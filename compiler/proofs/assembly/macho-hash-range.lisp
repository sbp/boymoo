(in-package "BOYMOO-PROOFS")

(include-book "bytes")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-sha256-message-range-p (text start data-end message-end)
  (and (stringp text) (natp start) (natp data-end) (natp message-end)
       (<= start data-end) (<= data-end message-end) (<= data-end (length text))))

(defun assembly-sha256-message (text start data-end message-end)
  (coerce (append (take (- data-end start) (nthcdr start (coerce text 'list)))
                  (assembly-zero-characters (- message-end data-end)))
          'string))

(local
 (defun assembly-sha256-index-induction (index count chars)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (cons count chars)
     (assembly-sha256-index-induction (1- index) (1- count) (cdr chars)))))

(local
 (defthm assembly-sha256-length-of-suffix
   (implies (and (natp start) (<= start (len chars)))
            (equal (len (nthcdr start chars)) (- (len chars) start)))
   :hints (("Goal" :induct (nthcdr start chars)))))

(local
 (defthm assembly-sha256-suffix-of-character-list
   (implies (character-listp chars)
            (character-listp (nthcdr start chars)))
   :hints (("Goal" :induct (nthcdr start chars)))))

(local
 (defthm assembly-sha256-take-of-character-list
   (implies (and (character-listp chars) (natp count) (<= count (len chars)))
            (character-listp (take count chars)))
   :hints (("Goal" :induct (take count chars)))))

(local
 (defthm assembly-sha256-length-of-take
   (equal (len (take count chars)) (nfix count))
   :hints (("Goal" :induct (take count chars)))))

(local
 (defthm assembly-sha256-length-of-append
   (equal (len (append prefix suffix)) (+ (len prefix) (len suffix)))))

(local
 (defthm assembly-sha256-append-of-character-lists
   (implies (and (character-listp prefix) (character-listp suffix))
            (character-listp (append prefix suffix)))))

(local
 (defthm assembly-sha256-zeroes-are-characters
   (character-listp (assembly-zero-characters count))))

(local
 (defthm assembly-sha256-zeroes-count
   (equal (len (assembly-zero-characters count)) (nfix count))))

(local
 (defthm assembly-sha256-index-of-take
   (implies (and (natp index) (natp count) (< index count))
            (equal (nth index (take count chars)) (nth index chars)))
   :hints (("Goal" :induct (assembly-sha256-index-induction index count chars)
                   :expand ((take count chars))))))

(local
 (defthm assembly-sha256-index-of-suffix
   (implies (and (natp start) (natp index))
            (equal (nth index (nthcdr start chars))
                   (nth (+ start index) chars)))
   :hints (("Goal" :induct (nthcdr start chars)))))

(local
 (defthm assembly-sha256-index-of-appended-prefix
   (implies (and (natp index) (< index (len prefix)))
            (equal (nth index (append prefix suffix)) (nth index prefix)))
   :hints (("Goal" :induct (nth index prefix)))))

(local
 (defthm assembly-sha256-index-of-appended-tail
   (implies (and (natp index) (<= (len prefix) index))
            (equal (nth index (append prefix suffix)) (nth (- index (len prefix)) suffix)))
   :hints (("Goal" :induct (nth index prefix)))))

(local
 (defthm assembly-sha256-index-of-zeroes
   (implies (and (natp index) (natp count) (< index count))
            (equal (nth index (assembly-zero-characters count)) (code-char 0)))
   :hints (("Goal" :induct (assembly-sha256-index-induction index count nil)))))

(local
 (defthm assembly-sha256-character-list-of-message
   (implies (assembly-sha256-message-range-p text start data-end message-end)
            (character-listp
             (append (take (- data-end start) (nthcdr start (coerce text 'list)))
                     (assembly-zero-characters (- message-end data-end)))))))

(defthm assembly-sha256-message-length
  (implies (assembly-sha256-message-range-p text start data-end message-end)
           (equal (length (assembly-sha256-message text start data-end message-end))
                  (- message-end start))))

(local
 (defthm assembly-sha256-character-of-message
   (implies (and (assembly-sha256-message-range-p text start data-end message-end)
                 (natp index) (< index (- message-end start)))
            (equal (char (assembly-sha256-message text start data-end message-end) index)
                   (if (< (+ start index) data-end)
                       (char text (+ start index))
                     (code-char 0))))))

(local (in-theory (disable assembly-sha256-message
                           assembly-sha256-message-range-p assembly-zero-characters)))

(local
 (defthm assembly-sha256-message-padded-byte
   (let ((message (assembly-sha256-message text start data-end message-end))
         (size (- message-end start)))
     (implies (and (assembly-sha256-message-range-p text start data-end message-end)
                   (natp index))
              (equal (boymoo-compiler::sha256-padded-byte message index size size)
                     (boymoo-compiler::sha256-padded-byte
                      text (+ start index) data-end message-end))))
   :hints (("Goal" :in-theory (e/d (assembly-sha256-message-range-p) (char))))))

(local
 (defthm assembly-sha256-message-last-word
   (let ((message (assembly-sha256-message text start data-end message-end))
         (size (- message-end start)))
     (implies (and (assembly-sha256-message-range-p text start data-end message-end)
                   (natp index))
              (equal (boymoo-compiler::sha256-last-word message index size size padded-end bits)
                     (boymoo-compiler::sha256-last-word
                      text (+ start index) data-end message-end (+ start padded-end) bits))))
   :hints (("Goal" :in-theory (e/d (assembly-sha256-message-range-p)
                                  (boymoo-compiler::sha256-padded-byte))))))

(local
 (defthm assembly-sha256-full-word-is-last-word
   (implies (and (<= (+ index 4) data-end)
                 (<= (+ data-end 9) padded-end))
            (equal (boymoo-compiler::sha256-message-word text index)
                   (boymoo-compiler::sha256-last-word text index data-end message-end padded-end bits)))
   :hints (("Goal" :in-theory (disable char)))
   :rule-classes nil))

(local (in-theory (disable boymoo-compiler::sha256-padded-byte
                           boymoo-compiler::sha256-last-word
                           boymoo-compiler::sha256-message-word)))

(local
 (defthm assembly-sha256-message-block-word
   (let* ((message (assembly-sha256-message text start data-end message-end))
          (size (- message-end start))
          (source-index (+ start index))
          (source-end (+ start padded-end)))
     (implies (and (assembly-sha256-message-range-p text start data-end message-end)
                   (natp index) (integerp padded-end) (<= (+ size 9) padded-end))
              (equal (if (<= (+ index 4) size)
                         (boymoo-compiler::sha256-message-word message index)
                       (boymoo-compiler::sha256-last-word message index size size padded-end bits))
                     (if (<= (+ source-index 4) data-end)
                         (boymoo-compiler::sha256-message-word text source-index)
                       (boymoo-compiler::sha256-last-word
                        text source-index data-end message-end source-end bits)))))
   :hints (("Goal"
            :use ((:instance assembly-sha256-full-word-is-last-word
                             (index (+ start index)) (padded-end (+ start padded-end)))
                  (:instance assembly-sha256-full-word-is-last-word
                             (text (assembly-sha256-message text start data-end message-end))
                             (data-end (- message-end start)) (message-end (- message-end start))))
            :in-theory (enable assembly-sha256-message-range-p)))
   :rule-classes nil))

(local
 (defthm assembly-sha256-message-block-words
   (let ((message (assembly-sha256-message text start data-end message-end))
         (size (- message-end start)))
     (implies (and (assembly-sha256-message-range-p text start data-end message-end)
                   (integerp padded-end) (<= (+ size 9) padded-end)
                   (implies (posp count)
                            (and (natp index) (<= (* 4 (1- count)) index))))
              (equal (boymoo-compiler::sha256-block-words message index count size size padded-end bits acc)
                     (boymoo-compiler::sha256-block-words
                      text (+ start index) count data-end message-end (+ start padded-end) bits acc))))
   :hints (("Goal"
            :induct (boymoo-compiler::sha256-block-words
                     (assembly-sha256-message text start data-end message-end)
                     index count (- message-end start) (- message-end start) padded-end bits acc))
           ("Subgoal *1/2" :use (assembly-sha256-message-block-word)))
   :rule-classes nil))

(local (in-theory (disable boymoo-compiler::sha256-block-words
                           boymoo-compiler::sha256-compress)))

(local
 (defthm assembly-sha256-message-blocks
   (let ((message (assembly-sha256-message text start data-end message-end))
         (size (- message-end start)))
     (implies (and (assembly-sha256-message-range-p text start data-end message-end)
                   (natp index) (integerp padded-end) (<= (+ size 9) padded-end))
              (equal (boymoo-compiler::sha256-blocks message index count size size padded-end bits digest)
                     (boymoo-compiler::sha256-blocks
                      text (+ start index) count data-end message-end (+ start padded-end) bits digest))))
   :hints (("Goal"
            :induct (boymoo-compiler::sha256-blocks
                     (assembly-sha256-message text start data-end message-end)
                     index count (- message-end start) (- message-end start) padded-end bits digest))
           ("Subgoal *1/2"
            :use ((:instance assembly-sha256-message-block-words
                             (index (+ index 60)) (count 16) (acc nil)))))
   :rule-classes nil))

(local (in-theory (disable boymoo-compiler::sha256-blocks ash floor assembly-power-of-two)))

(local
 (defthm assembly-sha256-padded-message-length
   (implies (natp size)
            (and (integerp (ash (ash (+ size 72) -6) 6))
                 (<= (+ 9 size) (ash (ash (+ size 72) -6) 6))))
   :hints (("Goal" :use ((:instance assembly-floor-bounds (x (+ size 72)) (d 64)))
                   :in-theory (enable assembly-high)))))

(defthm assembly-sha256-range-uses-explicit-message
  (let ((message (assembly-sha256-message text start data-end message-end))
        (size (- message-end start)))
    (implies (assembly-sha256-message-range-p text start data-end message-end)
             (equal (boymoo-compiler::sha256-range-words text start data-end message-end)
                    (boymoo-compiler::sha256-range-words message 0 size size))))
  :hints (("Goal"
           :use ((:instance assembly-sha256-message-blocks
                            (index 0) (count (ash (+ (- message-end start) 72) -6))
                            (padded-end (ash (ash (+ (- message-end start) 72) -6) 6))
                            (bits (ash (- message-end start) 3))
                            (digest boymoo-compiler::*sha256-initial*))
                 (:instance assembly-sha256-padded-message-length (size (- message-end start))))
           :in-theory (e/d (assembly-sha256-message-range-p)
                           (assembly-sha256-padded-message-length))))
  :rule-classes nil)
