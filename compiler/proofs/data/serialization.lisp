(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")
(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

; A fragment boundary has no effect on the sequence of stored bytes.
(defun data-fragment-characters (fragments)
  (if (atom fragments)
      nil
    (append (coerce (car fragments) 'list)
            (data-fragment-characters (cdr fragments)))))

(defun data-zero-characters (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (code-char 0) (data-zero-characters (1- count)))))

(defun data-chunk-characters (chunk)
  (cond ((stringp chunk)
         (let ((size (length chunk)))
           (append (coerce chunk 'list)
                   (data-zero-characters
                    (- (boymoo-compiler::aligned-size size 3) size)))))
        ((consp chunk) (boymoo-compiler::prepend-integer (cdr chunk) nil))
        (t (boymoo-compiler::prepend-word chunk 8 nil))))

(defun data-chunks-characters (reversed)
  (if (atom reversed)
      nil
    (append (data-chunks-characters (cdr reversed))
            (data-chunk-characters (car reversed)))))

(local
 (defthm prepend-word-onto
   (equal (boymoo-compiler::prepend-word word count (append chars tail))
          (append (boymoo-compiler::prepend-word word count chars) tail))
   :hints (("Goal" :induct (boymoo-compiler::prepend-word word count chars)))))

(local
 (defthm prepend-word-character-listp
   (implies (character-listp chars)
            (character-listp (boymoo-compiler::prepend-word word count chars)))
   :hints (("Goal" :induct (boymoo-compiler::prepend-word word count chars)))))

(local
 (defthm zero-times-number
   (equal (* 0 x) 0)))

(local
 (defthm ash-of-zero-value
   (equal (ash 0 count) 0)))

(local
 (defthm append-zero-after-zero-characters
   (equal (append (data-zero-characters count) (cons (code-char 0) chars))
          (cons (code-char 0) (append (data-zero-characters count) chars)))))

(local
 (defthm prepend-word-zero-onto
   (equal (boymoo-compiler::prepend-word 0 count chars)
          (append (data-zero-characters count) chars))
   :hints (("Goal" :induct (boymoo-compiler::prepend-word 0 count chars)))))

(local
 (defthm image-zeroes-onto
   (implies (character-listp chars)
            (equal (coerce (boymoo-compiler::image-zeroes count chars) 'list)
                   (append (data-zero-characters count) chars)))
   :hints (("Goal" :induct (boymoo-compiler::image-zeroes count chars)))))

(local
 (defthm take-with-next-element
   (implies (posp count)
            (equal (append (take (1- count) xs) (cons (nth (1- count) xs) tail))
                   (append (take count xs) tail)))
   :hints (("Goal" :induct (take count xs)))))

(local
 (defthm take-zero
   (equal (take 0 xs) nil)))

(local
 (defthm prepend-string-of-prefix
   (equal (boymoo-compiler::prepend-string text count chars)
          (append (take (nfix count) (coerce text 'list)) chars))
   :hints (("Goal" :induct (boymoo-compiler::prepend-string text count chars)
                   :in-theory (disable take)))))

(local
 (defthm take-len-of-true-list
   (implies (true-listp chars)
            (equal (take (len chars) chars) chars))))

(local
 (defthm prepend-full-string
   (implies (stringp text)
            (equal (boymoo-compiler::prepend-string text (length text) chars)
                   (append (coerce text 'list) chars)))))

(local
 (defthm prepend-integer-tail
   (implies (syntaxp (not (equal chars ''nil)))
            (equal (boymoo-compiler::prepend-integer n chars)
                   (append (boymoo-compiler::prepend-integer n nil) chars)))
   :hints (("Goal" :use ((:instance prepend-word-onto
                                    (word (ash n -7)) (count 7)
                                    (chars nil) (tail chars)))
                   :in-theory (disable prepend-word-onto
                                       boymoo-compiler::prepend-word)))))

(local
 (defthm prepend-word-tail
   (implies (syntaxp (not (equal chars ''nil)))
            (equal (boymoo-compiler::prepend-word n count chars)
                   (append (boymoo-compiler::prepend-word n count nil) chars)))
   :hints (("Goal" :use ((:instance prepend-word-onto (word n) (chars nil)
                                    (tail chars)))
                   :in-theory (disable prepend-word-onto
                                       boymoo-compiler::prepend-word)))))

(local
 (defthm fragment-characters-of-flush
   (implies (character-listp chars)
            (equal (data-fragment-characters (boymoo-compiler::image-flush chars chunks))
                   (append chars (data-fragment-characters chunks))))))

(local
 (defthm fragment-characters-of-padding
   (equal (data-fragment-characters (boymoo-compiler::image-padding count chunks))
          (append (data-zero-characters count) (data-fragment-characters chunks)))))

(local
 (defthm data-append-associative
   (equal (append (append first second) third)
          (append first second third))))

(local
 (defthm character-listp-of-append
   (implies (and (character-listp first) (character-listp second))
            (character-listp (append first second)))))

(local
 (defthm character-listp-of-zero-characters
   (character-listp (data-zero-characters count))))

(local
 (defthm character-listp-of-encoded-integer
   (character-listp (boymoo-compiler::prepend-integer n nil))
   :hints (("Goal" :in-theory (disable boymoo-compiler::prepend-word
                                       boymoo-compiler::low-bits ash)))))

(defthm data-write-chunks-characters
  (implies (character-listp chars)
           (equal (data-fragment-characters
                   (boymoo-compiler::data-write-chunks reversed chars buffered chunks))
                  (append (data-chunks-characters reversed) chars
                          (data-fragment-characters chunks))))
  :hints (("Goal" :induct (boymoo-compiler::data-write-chunks reversed chars buffered chunks)
                  :in-theory (disable boymoo-compiler::image-flush
                                      boymoo-compiler::image-padding
                                      boymoo-compiler::prepend-integer
                                      boymoo-compiler::prepend-word
                                      boymoo-compiler::prepend-string
                                      boymoo-compiler::aligned-size))))

(defthm data-write-characters
  (equal (data-fragment-characters (boymoo-compiler::data-write reversed tail))
         (append (data-chunks-characters reversed) (data-fragment-characters tail)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-write-chunks))))

(local
 (defthm fragments-p-of-flush
   (implies (proof-fragments-p tail)
            (proof-fragments-p (boymoo-compiler::image-flush chars tail)))))

(local
 (defthm fragments-p-of-padding
   (implies (proof-fragments-p tail)
            (proof-fragments-p (boymoo-compiler::image-padding count tail)))))

(local
 (defthm fragments-p-of-data-write-chunks
   (implies (proof-fragments-p tail)
            (proof-fragments-p
             (boymoo-compiler::data-write-chunks reversed chars buffered tail)))
   :hints (("Goal" :induct (boymoo-compiler::data-write-chunks reversed chars buffered tail)
                   :in-theory (disable boymoo-compiler::image-flush
                                       boymoo-compiler::image-padding
                                       boymoo-compiler::prepend-integer
                                       boymoo-compiler::prepend-word
                                       boymoo-compiler::prepend-string
                                       boymoo-compiler::aligned-size)))))

(defthm fragments-p-of-data-write
  (implies (proof-fragments-p tail)
           (proof-fragments-p (boymoo-compiler::data-write reversed tail)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-write-chunks))))

(defthm data-fragment-characters-size
  (implies (proof-fragments-p fragments)
           (equal (len (data-fragment-characters fragments))
                  (proof-fragments-size fragments))))

(defun data-chunk-size (chunk)
  (if (stringp chunk)
      (boymoo-compiler::aligned-size (length chunk) 3)
    8))

(defun data-chunks-size (chunks)
  (if (atom chunks)
      0
    (+ (data-chunk-size (car chunks)) (data-chunks-size (cdr chunks)))))

(local
 (defthm len-of-prepend-word
   (equal (len (boymoo-compiler::prepend-word word count chars))
          (+ (nfix count) (len chars)))
   :hints (("Goal" :induct (boymoo-compiler::prepend-word word count chars)
                   :in-theory (disable boymoo-compiler::low-bits ash)))))

(local
 (defthm len-of-prepend-integer
   (equal (len (boymoo-compiler::prepend-integer value chars))
          (+ 8 (len chars)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::prepend-word
                                       prepend-word-tail
                                       prepend-integer-tail
                                       boymoo-compiler::low-bits ash)))))

(local
 (defthm len-of-data-append
   (equal (len (append first second)) (+ (len first) (len second)))))

(local
 (defthm len-of-zero-characters
   (equal (len (data-zero-characters count)) (nfix count))))

(defthm data-chunk-characters-size
  (equal (len (data-chunk-characters chunk)) (data-chunk-size chunk))
  :hints (("Goal" :in-theory (disable boymoo-compiler::aligned-size
                                      boymoo-compiler::prepend-integer
                                      boymoo-compiler::prepend-word))))

(defthm data-chunks-characters-size
  (equal (len (data-chunks-characters reversed)) (data-chunks-size reversed))
  :hints (("Goal" :in-theory (disable data-chunk-characters data-chunk-size))))

(defthm data-write-size
  (implies (proof-fragments-p tail)
           (equal (proof-fragments-size (boymoo-compiler::data-write reversed tail))
                  (+ (data-chunks-size reversed) (proof-fragments-size tail))))
  :hints (("Goal" :use ((:instance data-fragment-characters-size
                                   (fragments (boymoo-compiler::data-write reversed tail)))
                       (:instance data-fragment-characters-size (fragments tail)))
                  :in-theory (disable data-fragment-characters-size
                                      boymoo-compiler::data-write
                                      proof-fragments-size proof-fragments-p
                                      data-fragment-characters data-chunks-characters
                                      data-chunks-size))))

(defun data-forward-chunk-characters (chunks)
  (if (atom chunks)
      nil
    (append (data-chunk-characters (car chunks))
            (data-forward-chunk-characters (cdr chunks)))))

(local
 (defthm true-listp-when-character-listp
   (implies (character-listp chars) (true-listp chars))
   :rule-classes :forward-chaining))

(defthm data-chunk-characters-are-characters
  (character-listp (data-chunk-characters chunk))
  :hints (("Goal" :in-theory (disable boymoo-compiler::prepend-word
                                      boymoo-compiler::prepend-integer
                                      boymoo-compiler::aligned-size))))

(defthm data-chunks-characters-are-characters
  (character-listp (data-chunks-characters reversed)))

(defthm data-forward-chunk-characters-are-characters
  (character-listp (data-forward-chunk-characters chunks)))

(local
 (defthm data-chunks-characters-are-a-list
   (true-listp (data-chunks-characters reversed))
   :hints (("Goal" :use data-chunks-characters-are-characters))))

(defthm data-chunks-characters-of-reverse-onto
  (equal (data-chunks-characters (boymoo-compiler::reverse-onto chunks tail))
         (append (data-chunks-characters tail) (data-forward-chunk-characters chunks)))
  :hints (("Goal" :induct (boymoo-compiler::reverse-onto chunks tail)
                  :in-theory (disable data-chunk-characters))))

(defun data-word-chunks-p (chunks)
  (if (atom chunks)
      t
    (and (not (stringp (car chunks))) (data-word-chunks-p (cdr chunks)))))

(defthm data-word-chunks-p-of-reverse-onto
  (equal (data-word-chunks-p (boymoo-compiler::reverse-onto xs tail))
         (and (data-word-chunks-p xs) (data-word-chunks-p tail)))
  :hints (("Goal" :induct (boymoo-compiler::reverse-onto xs tail))))

(defthm len-of-data-reverse-onto
  (equal (len (boymoo-compiler::reverse-onto xs tail)) (+ (len xs) (len tail)))
  :hints (("Goal" :induct (boymoo-compiler::reverse-onto xs tail))))

(local
 (defthm data-write-chunks-below-flush-size
   (implies (and (data-word-chunks-p reversed) (integerp buffered)
                 (< (+ buffered (* 8 (len reversed))) 512))
            (equal (boymoo-compiler::data-write-chunks reversed chars buffered tail)
                   (boymoo-compiler::image-flush
                    (append (data-chunks-characters reversed) chars) tail)))
   :hints (("Goal" :induct (boymoo-compiler::data-write-chunks reversed chars buffered tail)
                   :in-theory (disable boymoo-compiler::image-flush
                                       boymoo-compiler::prepend-integer
                                       boymoo-compiler::prepend-word
                                       boymoo-compiler::aligned-size)))))

(defthm data-write-short-word-chunks
  (implies (and (data-word-chunks-p reversed) (< (len reversed) 64))
           (equal (boymoo-compiler::data-write reversed tail)
                  (boymoo-compiler::image-flush (data-chunks-characters reversed) tail)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-write-chunks
                                      boymoo-compiler::image-flush data-chunks-characters))))

(defthm data-word-chunks-size
  (implies (data-word-chunks-p chunks)
           (equal (data-chunks-size chunks) (* 8 (len chunks)))))

(defthm data-forward-chunk-characters-size
  (equal (len (data-forward-chunk-characters chunks)) (data-chunks-size chunks))
  :hints (("Goal" :in-theory (disable data-chunk-characters data-chunk-size))))

(local
 (defthm len-of-nonempty-list-is-positive
   (implies (consp contents) (< 0 (len contents)))
   :rule-classes :linear))

(defthm data-header-stays-in-one-fragment
  (implies (and (data-word-chunks-p header) (consp header) (< (len header) 64))
           (equal (boymoo-compiler::data-write (boymoo-compiler::reverse-onto header nil) tail)
                  (cons (coerce (data-forward-chunk-characters header) 'string) tail)))
  :hints (("Goal" :cases ((consp (data-forward-chunk-characters header)))
                  :use ((:instance data-forward-chunk-characters-size (chunks header)))
                  :in-theory (disable boymoo-compiler::data-write boymoo-compiler::reverse-onto
                                      data-forward-chunk-characters data-forward-chunk-characters-size
                                      data-word-chunks-p))))
