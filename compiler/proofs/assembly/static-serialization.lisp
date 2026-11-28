(in-package "BOYMOO-PROOFS")

(include-book "bytes")

(logic)
(set-verify-guards-eagerness 0)

; The static writer pads each string to an eight-byte boundary. Every
; other chunk occupies one word, including a tagged immediate integer.
(defun assembly-static-chunk-size (chunk)
  (if (stringp chunk)
      (boymoo-compiler::aligned-size (length chunk) 3)
    8))

(defun assembly-static-chunks-size (chunks)
  (if (atom chunks)
      0
    (+ (assembly-static-chunk-size (car chunks))
       (assembly-static-chunks-size (cdr chunks)))))

(local (in-theory (disable char length ash floor boymoo-compiler::low-bits)))

(defthm assembly-eight-byte-padding-bounds
  (let ((padded (boymoo-compiler::aligned-size size 3)))
    (implies (natp size)
             (and (natp padded)
                  (<= size padded)
                  (< padded (+ size 8)))))
  :hints (("Goal"
           :use ((:instance assembly-floor-bounds (x (+ size 7)) (d 8)))
           :in-theory (enable assembly-high)))
  :rule-classes nil)

(local
 (defthm assembly-length-of-static-string
   (implies (stringp text)
            (equal (length text) (len (coerce text 'list))))
   :hints (("Goal" :in-theory (enable length)))))

(local
 (defthm assembly-length-of-static-word-prepend
   (equal (len (boymoo-compiler::prepend-word word count chars))
          (+ (nfix count) (len chars)))))

(local
 (defthm assembly-characters-of-static-word-prepend
   (implies (character-listp chars)
            (character-listp (boymoo-compiler::prepend-word word count chars)))))

(local
 (defthm assembly-length-of-static-string-prepend
   (equal (len (boymoo-compiler::prepend-string text count chars))
          (+ (nfix count) (len chars)))))

(local
 (defthm assembly-nth-of-static-characters
   (implies (and (character-listp chars) (natp index) (< index (len chars)))
            (characterp (nth index chars)))
   :hints (("Goal" :induct (nth index chars)))))

(local
 (defthm assembly-static-char-within-string
   (implies (and (stringp text) (natp index) (< index (length text)))
            (characterp (char text index)))
   :hints (("Goal" :in-theory (enable char)))))

(local
 (defthm assembly-characters-of-static-string-prepend
   (implies (and (stringp text) (<= count (length text)) (character-listp chars))
            (character-listp (boymoo-compiler::prepend-string text count chars)))))

(local
 (defthm assembly-static-word-and-string-lengths
   (implies (and (character-listp chars) (proof-fragments-p fragments))
            (and (proof-fragments-p (boymoo-compiler::image-flush chars fragments))
                 (equal (proof-fragments-size (boymoo-compiler::image-flush chars fragments))
                        (+ (len chars) (proof-fragments-size fragments)))))
   :hints (("Goal" :in-theory (enable length)))))

(local
 (defthm assembly-length-of-static-zeroes
   (implies (character-listp chars)
            (and (stringp (boymoo-compiler::image-zeroes count chars))
                 (equal (length (boymoo-compiler::image-zeroes count chars))
                        (+ (nfix count) (len chars)))))))

(local
 (defthm assembly-size-and-type-of-zero-padding
   (implies (and (natp count) (proof-fragments-p fragments))
            (and (proof-fragments-p (boymoo-compiler::image-padding count fragments))
                 (equal (proof-fragments-size (boymoo-compiler::image-padding count fragments))
                        (+ count (proof-fragments-size fragments)))))
   :hints (("Goal"
            :use ((:instance assembly-length-of-static-zeroes (chars nil)))
            :in-theory (enable length)))))

(local (in-theory (disable boymoo-compiler::aligned-size boymoo-compiler::prepend-word
                           boymoo-compiler::prepend-string boymoo-compiler::image-padding
                           boymoo-compiler::image-flush proof-fragments-size proof-fragments-p)))

(local
 (defthm assembly-add-static-string-fragment
   (implies (and (stringp text) (proof-fragments-p fragments))
            (and (proof-fragments-p (cons text fragments))
                 (equal (proof-fragments-size (cons text fragments))
                        (+ (length text) (proof-fragments-size fragments)))))
   :hints (("Goal" :in-theory (enable proof-fragments-p proof-fragments-size)))))

(local
 (defthm assembly-static-aligned-size-facts
   (implies (natp size)
            (and (integerp (boymoo-compiler::aligned-size size 3))
                 (<= size (boymoo-compiler::aligned-size size 3))))
   :hints (("Goal" :use (assembly-eight-byte-padding-bounds)))
   :rule-classes
   ((:rewrite
     :corollary (implies (natp size) (integerp (boymoo-compiler::aligned-size size 3))))
    (:linear
     :corollary (implies (natp size) (<= size (boymoo-compiler::aligned-size size 3)))))))

(local
 (defthm assembly-data-write-chunks-size
   (let ((out (boymoo-compiler::data-write-chunks reversed chars buffered fragments)))
     (implies (and (character-listp chars) (proof-fragments-p fragments))
              (and (proof-fragments-p out)
                   (equal (proof-fragments-size out)
                          (+ (assembly-static-chunks-size reversed)
                             (len chars) (proof-fragments-size fragments))))))
   :hints (("Goal" :induct (boymoo-compiler::data-write-chunks reversed chars buffered fragments)))))

(defthm assembly-data-write-size
  (let ((out (boymoo-compiler::data-write reversed fragments)))
    (implies (proof-fragments-p fragments)
             (and (proof-fragments-p out)
                  (equal (proof-fragments-size out)
                         (+ (assembly-static-chunks-size reversed)
                            (proof-fragments-size fragments))))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-write-chunks)
                  :use ((:instance assembly-data-write-chunks-size (chars nil) (buffered 0))))))

(defun assembly-static-block-p (block)
  (equal (car block) (+ 80 (assembly-static-chunks-size (cdr block)))))

(defthm assembly-static-chunks-size-is-natural
  (natp (assembly-static-chunks-size chunks))
  :hints (("Goal" :induct (assembly-static-chunks-size chunks))
          ("Subgoal *1/2"
           :use ((:instance assembly-eight-byte-padding-bounds (size (length (car chunks)))))))
  :rule-classes :type-prescription)

(defun assembly-static-image (prefix block)
  (cons (car block)
        (boymoo-compiler::data-write (boymoo-compiler::reverse-onto prefix nil)
                                      (boymoo-compiler::data-write (cdr block) nil))))

(defun assembly-static-words-p (words)
  (if (atom words)
      t
    (and (not (stringp (car words)))
         (assembly-static-words-p (cdr words)))))

(local
 (defthm assembly-static-words-size
   (implies (assembly-static-words-p words)
            (equal (assembly-static-chunks-size (boymoo-compiler::reverse-onto words rest))
                   (+ (* 8 (len words)) (assembly-static-chunks-size rest))))))

(defthm assembly-static-image-from-sized-block
  (implies (and (assembly-static-block-p block)
                (assembly-static-words-p prefix)
                (equal (len prefix) 10))
           (proof-image-p (assembly-static-image prefix block)))
  :hints (("Goal" :in-theory (e/d (proof-fragments-p proof-fragments-size)
                                  (boymoo-compiler::data-write boymoo-compiler::reverse-onto
                                   assembly-static-chunks-size assembly-static-chunk-size)))))
