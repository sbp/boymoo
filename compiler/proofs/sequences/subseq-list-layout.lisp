(in-package "BOYMOO-PROOFS")

(include-book "subseq-list-fill")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-cell-source-word (word base memory)
  (if (equal (proof-word-tag word) 0)
      (boymoo-model::a64-read-bytes 8 (proof-pointer-address word base) memory)
    *proof-nil*))

(defun sequence-subseq-cell-source-tail (word base memory)
  (if (equal (proof-word-tag word) 0)
      (boymoo-model::a64-read-bytes 8 (+ 8 (proof-pointer-address word base)) memory)
    word))

(defun sequence-subseq-copy-words (count word base memory)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (sequence-subseq-cell-source-word word base memory)
          (sequence-subseq-copy-words (1- count)
                                      (sequence-subseq-cell-source-tail word base memory)
                                      base memory))))

(defun sequence-subseq-cell-link (count cell base)
  (if (equal count 1) *proof-nil* (sequence-cell-word (+ 16 cell) base)))

(local
 (defthm sequence-subseq-field-words-fit
   (and (unsigned-byte-p 64 (sequence-subseq-cell-source-word word base memory))
        (unsigned-byte-p 64 (sequence-subseq-cell-link count cell base)))
   :hints (("Goal" :in-theory (disable proof-word-tag proof-pointer-address sequence-read-bytes-bits)
            :use ((:instance sequence-read-bytes-bits (count 8)
                             (address (proof-pointer-address word base))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-fill-memory-unroll
   (implies (posp count)
            (equal (sequence-subseq-list-fill-memory count word base cell memory)
                   (sequence-subseq-list-fill-memory
                    (1- count) (sequence-subseq-cell-source-tail word base memory)
                    base (+ cell 16)
                    (sequence-write-cell cell (sequence-subseq-cell-source-word word base memory)
                                         (sequence-subseq-cell-link count cell base) memory))))
   :hints (("Goal" :expand ((sequence-subseq-list-fill-memory count word base cell memory))))))

(local
 (defthm sequence-subseq-selected-words-survive-write
   (implies (and (sequence-subseq-readable-cells-p count word base lower upper memory)
                 (proof-subspan-p cell 16 lower upper))
            (equal (sequence-subseq-copy-words
                    count word base (sequence-write-cell cell first rest memory))
                   (sequence-subseq-copy-words count word base memory)))
   :hints
   (("Goal"
     :induct (sequence-subseq-readable-cells-p count word base lower upper memory)
     :in-theory (disable proof-word-tag proof-pointer-address
                         sequence-subseq-list-fill-memory sequence-subseq-fill-memory-unroll)
     :expand ((:free (state) (sequence-subseq-copy-words count word base state)))))
   :rule-classes nil))

(defthm sequence-subseq-fill-keeps-outside-reads
  (implies (and (natp count) (proof-span-p cell (* 16 count))
                (proof-span-p address width)
                (proof-disjoint-p address (+ address width) cell (+ cell (* 16 count))))
           (equal (boymoo-model::a64-read-bytes
                   width address (sequence-subseq-list-fill-memory count word base cell memory))
                  (boymoo-model::a64-read-bytes width address memory)))
  :hints
  (("Goal"
    :in-theory (e/d ((:induction sequence-subseq-list-fill-memory))
                    (sequence-subseq-fill-memory-unroll proof-word-tag proof-pointer-address
                     sequence-subseq-cell-link))
    :induct (sequence-subseq-list-fill-memory count word base cell memory)
    :expand ((sequence-subseq-list-fill-memory count word base cell memory)))
   ("Subgoal *1/2"
    :cases ((equal count 1))
    :expand ((:free (word base cell memory)
                    (sequence-subseq-list-fill-memory 0 word base cell memory)))))
  :rule-classes nil)

(local
 (defthm sequence-subseq-first-cell-after-copy
   (let* ((finished (sequence-subseq-list-fill-memory count word base cell memory))
          (first (sequence-subseq-cell-source-word word base memory))
          (rest (sequence-subseq-cell-link count cell base)))
     (implies (and (posp count) (proof-span-p cell (* 16 count)))
              (and (equal (boymoo-model::a64-read-bytes 8 cell finished) first)
                   (equal (boymoo-model::a64-read-bytes 8 (+ cell 8) finished) rest))))
   :hints
   (("Goal"
     :in-theory (disable (:definition sequence-subseq-list-fill-memory)
                         sequence-subseq-fill-memory-unroll sequence-subseq-cell-link
                         sequence-subseq-cell-source-word sequence-subseq-cell-source-tail)
     :cases ((equal count 1))
     :use (sequence-subseq-fill-memory-unroll sequence-subseq-field-words-fit
           (:instance sequence-cell-write-first-word
                      (address cell) (first (sequence-subseq-cell-source-word word base memory))
                      (rest (sequence-subseq-cell-link count cell base)))
           (:instance sequence-cell-write-rest-word
                      (address cell) (first (sequence-subseq-cell-source-word word base memory))
                      (rest (sequence-subseq-cell-link count cell base)))
           (:instance sequence-subseq-fill-keeps-outside-reads
                      (count (1- count)) (cell (+ cell 16)) (address cell) (width 8)
                      (word (sequence-subseq-cell-source-tail word base memory))
                      (memory (sequence-write-cell cell (sequence-subseq-cell-source-word word base memory)
                                                   (sequence-subseq-cell-link count cell base) memory)))
           (:instance sequence-subseq-fill-keeps-outside-reads
                      (count (1- count)) (cell (+ cell 16)) (address (+ cell 8)) (width 8)
                      (word (sequence-subseq-cell-source-tail word base memory))
                      (memory (sequence-write-cell cell (sequence-subseq-cell-source-word word base memory)
                                                   (sequence-subseq-cell-link count cell base) memory)))))
    ("Subgoal 1"
     :expand ((:free (word base cell memory)
                     (sequence-subseq-list-fill-memory 0 word base cell memory)))))
   :rule-classes nil))

(local
 (defun sequence-subseq-cell-layout-induction (count index word base cell memory)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (cons word memory)
     (sequence-subseq-cell-layout-induction
      (1- count) (1- index) (sequence-subseq-cell-source-tail word base memory)
      base (+ cell 16)
      (sequence-write-cell cell (sequence-subseq-cell-source-word word base memory)
                           (sequence-subseq-cell-link count cell base) memory)))))

(defthm sequence-subseq-result-cell-contents
  (let* ((address (+ cell (* 16 index)))
         (finished (sequence-subseq-list-fill-memory count word base cell memory)))
    (implies (and (natp index) (natp count) (< index count)
                  (proof-subspan-p cell (* 16 count) lower upper)
                  (sequence-subseq-readable-cells-p count word base lower upper memory))
             (and (equal (boymoo-model::a64-read-bytes 8 address finished)
                         (nth index (sequence-subseq-copy-words count word base memory)))
                  (equal (boymoo-model::a64-read-bytes 8 (+ address 8) finished)
                         (sequence-subseq-cell-link (- count index) address base)))))
  :hints
  (("Goal"
    :in-theory (disable (:definition sequence-subseq-list-fill-memory)
                        (:definition sequence-subseq-copy-words)
                        sequence-subseq-fill-memory-unroll sequence-subseq-cell-link
                        sequence-subseq-cell-source-word sequence-subseq-cell-source-tail
                        sequence-subseq-readable-cells-p sequence-subseq-readable-cells-survive-output-write)
    :induct (sequence-subseq-cell-layout-induction count index word base cell memory))
   ("Subgoal *1/1"
    :expand ((sequence-subseq-copy-words count word base memory))
    :use sequence-subseq-first-cell-after-copy)
   ("Subgoal *1/2"
    :expand ((sequence-subseq-copy-words count word base memory)
             (sequence-subseq-cell-source-tail word base memory))
    :use (sequence-subseq-fill-memory-unroll
          sequence-subseq-readable-tail
          (:instance sequence-subseq-readable-cells-survive-output-write
                     (count (1- count)) (word (sequence-subseq-cell-source-tail word base memory))
                     (first (sequence-subseq-cell-source-word word base memory))
                     (rest (sequence-subseq-cell-link count cell base)))
          (:instance sequence-subseq-selected-words-survive-write
                     (count (1- count)) (word (sequence-subseq-cell-source-tail word base memory))
                     (first (sequence-subseq-cell-source-word word base memory))
                     (rest (sequence-subseq-cell-link count cell base))))))
  :rule-classes nil)
