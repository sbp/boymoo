(in-package "BOYMOO-PROOFS")

(include-book "subseq-source-words")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-forward-copy-ranks-p (count cell first-rank objects)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (equal (assoc-equal cell objects)
                (proof-object cell :active :cons (+ first-rank (1- count))))
         (sequence-forward-copy-ranks-p (1- count) (+ 16 cell) first-rank objects))))

(defun sequence-forward-cell-fields-p (words cell base memory)
  (if (atom words)
      t
    (and (equal (boymoo-model::a64-read-bytes 8 cell memory) (car words))
         (equal (boymoo-model::a64-read-bytes 8 (+ 8 cell) memory)
                (if (atom (cdr words)) *proof-nil* (sequence-cell-word (+ 16 cell) base)))
         (sequence-forward-cell-fields-p (cdr words) (+ 16 cell) base memory))))

(local
 (defthm sequence-subseq-copy-words-length
   (equal (len (sequence-subseq-copy-words count word base memory)) (nfix count))
   :hints (("Goal" :induct (sequence-subseq-copy-words count word base memory)))))

(local
 (defthm sequence-subseq-copy-words-is-nonempty
   (equal (consp (sequence-subseq-copy-words count word base memory)) (posp count))
   :hints (("Goal" :expand ((sequence-subseq-copy-words count word base memory))))))

(local
 (defthm sequence-subseq-copy-words-is-a-list
   (true-listp (sequence-subseq-copy-words count word base memory))
   :hints (("Goal" :induct (sequence-subseq-copy-words count word base memory)))))

(local
 (defthm sequence-forward-drop-fields
   (implies (and (true-listp words) (natp index) (<= index (len words)))
            (and (equal (len (sequence-drop index words)) (- (len words) index))
                 (equal (car (sequence-drop index words)) (nth index words))
                 (equal (cdr (sequence-drop index words)) (sequence-drop (1+ index) words))))
   :hints (("Goal" :induct (sequence-drop index words)
            :expand ((sequence-drop (1+ index) words))))))

(local
 (defthm sequence-forward-drop-is-nonempty
   (implies (and (true-listp words) (natp index) (<= index (len words)))
            (equal (consp (sequence-drop index words)) (< index (len words))))
   :hints (("Goal" :use sequence-forward-drop-fields
            :in-theory (disable sequence-drop sequence-forward-drop-fields)
            :expand ((len (sequence-drop index words)))))))

(local
 (defun sequence-forward-fields-from-index-induction (index count)
   (declare (xargs :measure (nfix (- (nfix count) (nfix index)))))
   (if (and (natp index) (natp count) (< index count))
       (sequence-forward-fields-from-index-induction (1+ index) count)
     nil)))

(local
 (defthm sequence-forward-fields-at-cursor
   (implies (implies (consp words)
                     (and (equal (boymoo-model::a64-read-bytes 8 cell memory) (car words))
                          (equal (boymoo-model::a64-read-bytes 8 (+ 8 cell) memory)
                                 (if (consp (cdr words))
                                     (sequence-cell-word (+ 16 cell) base)
                                   *proof-nil*))
                          (sequence-forward-cell-fields-p (cdr words) (+ 16 cell) base memory)))
            (sequence-forward-cell-fields-p words cell base memory))
   :hints (("Goal" :expand ((sequence-forward-cell-fields-p words cell base memory))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-forward-fields-from-index
   (let* ((words (sequence-subseq-copy-words count word base memory))
          (finished (sequence-subseq-list-fill-memory count word base cell memory)))
     (implies
      (and (natp index) (natp count) (<= index count)
           (proof-span-p cell (* 16 count))
           (sequence-subseq-readable-cells-p count word base cell (+ cell (* 16 count)) memory))
      (sequence-forward-cell-fields-p
       (sequence-drop index words) (+ cell (* 16 index)) base finished)))
   :hints
   (("Goal"
     :in-theory (disable sequence-drop sequence-subseq-copy-words sequence-subseq-list-fill-memory
                         sequence-subseq-readable-cells-p sequence-cell-word
                         (:definition sequence-forward-cell-fields-p))
     :induct (sequence-forward-fields-from-index-induction index count))
    ("Subgoal *1/1"
     :expand ((sequence-subseq-cell-link (- count index) (+ cell (* 16 index)) base))
     :use ((:instance sequence-subseq-result-cell-contents
                      (lower cell) (upper (+ cell (* 16 count))))
           (:instance sequence-forward-fields-at-cursor
                      (words (sequence-drop index (sequence-subseq-copy-words count word base memory)))
                      (cell (+ cell (* 16 index)))
                      (memory (sequence-subseq-list-fill-memory count word base cell memory)))))
    ("Subgoal *1/2"
     :use ((:instance sequence-forward-fields-at-cursor
                      (words (sequence-drop index (sequence-subseq-copy-words count word base memory)))
                      (cell (+ cell (* 16 index)))
                      (memory (sequence-subseq-list-fill-memory count word base cell memory))))))
   :rule-classes nil))

(local
 (defthm sequence-forward-last-cell-has-no-datum-tail
   (implies (and (consp words)
                 (sequence-words-viewed-at-rank-p words datums depth base objects packages machine))
            (and (equal (equal (len words) 1) (atom (cdr words)))
                 (equal (null (cdr datums)) (atom (cdr words)))))
   :hints
   (("Goal" :in-theory (disable proof-view-step)
            :expand ((sequence-words-viewed-at-rank-p words datums depth base objects packages machine)
                     (sequence-words-viewed-at-rank-p (cdr words) (cdr datums) depth base objects packages machine)
                     (len words) (len (cdr words)))))
   :rule-classes nil))

(local
 (defthm sequence-forward-cell-alignment
   (implies (and (natp base) (natp cell) (equal (mod (- cell base) 8) 0))
            (equal (mod (- (+ 16 cell) base) 8) 0))
   :hints (("Goal" :in-theory (disable sequence-mod-add-multiple)
            :use ((:instance sequence-mod-add-multiple (divisor 8) (multiple 2) (value (- cell base))))))))

(local
 (defthm sequence-forward-record-at-head
   (implies (and (posp count) (sequence-forward-copy-ranks-p count cell first-rank objects))
            (and (equal (assoc-equal cell objects)
                        (proof-object cell :active :cons (+ first-rank (1- count))))
                 (sequence-forward-copy-ranks-p (1- count) (+ 16 cell) first-rank objects)))
   :hints (("Goal" :expand ((sequence-forward-copy-ranks-p count cell first-rank objects))))
   :rule-classes nil))

(local
 (defthm sequence-forward-cons-at-next-rank
   (let* ((next (+ 16 cell))
          (word (if (equal count 1) *proof-nil* (sequence-cell-word next base)))
          (rank (+ first-rank (1- count))))
     (implies
      (and (posp count) (natp first-rank) (natp base) (<= base cell)
           (proof-span-p cell (* 16 count)) (equal (mod (- cell base) 8) 0)
           (sequence-forward-copy-ranks-p count cell first-rank objects)
           (if (equal count 1)
               (and (null tail)
                    (equal (proof-view-step :word *proof-nil* 0 first-rank base objects packages machine)
                           (proof-value-view nil)))
             (proof-value-p word tail base objects packages machine)))
      (equal (proof-view-step :word word 0 rank base objects packages machine)
             (proof-value-view tail))))
   :hints
   (("Goal"
     :in-theory (disable proof-view-step proof-value-p proof-pointer-address proof-word-tag
                         sequence-cell-word sequence-forward-cell-alignment
                         sequence-forward-copy-ranks-p oddp)
     :cases ((equal count 1))
     :use (sequence-forward-cell-alignment sequence-forward-record-at-head
           (:instance sequence-forward-record-at-head (count (1- count)) (cell (+ 16 cell)))
           (:instance sequence-cell-word-is-relative-pointer (cell (+ 16 cell)))
           (:instance sequence-datum-view-at-sufficient-rank
                      (word (sequence-cell-word (+ 16 cell) base))
                      (datum tail) (depth (+ first-rank (1- count)))))))
   :rule-classes nil))

(local
 (defun sequence-forward-list-view-induction (words datums cell)
   (if (atom words)
       (cons datums cell)
     (sequence-forward-list-view-induction (cdr words) (cdr datums) (+ 16 cell)))))

(local
 (defthm sequence-forward-cells-represent-datums
   (let* ((count (len words))
          (memory (boymoo-model::a64-memory machine)))
     (implies
      (and (consp words) (true-listp words) (natp first-rank) (natp base) (<= base cell)
           (proof-span-p cell (* 16 count)) (equal (mod (- cell base) 8) 0)
           (sequence-forward-copy-ranks-p count cell first-rank objects)
           (sequence-forward-cell-fields-p words cell base memory)
           (sequence-words-viewed-at-rank-p words datums first-rank base objects packages machine)
           (equal (proof-view-step :word *proof-nil* 0 first-rank base objects packages machine)
                  (proof-value-view nil)))
      (proof-value-p (sequence-cell-word cell base) datums base objects packages machine)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-load-word)
                     (proof-value-p proof-view-step proof-pointer-address proof-word-tag
                      sequence-cell-word sequence-forward-cell-alignment))
     :do-not '(generalize)
     :induct (sequence-forward-list-view-induction words datums cell))
    ("Subgoal *1/2"
     :cases ((consp (cdr words)))
     :use (sequence-forward-cell-alignment
           (:instance sequence-forward-last-cell-has-no-datum-tail (depth first-rank))
           (:instance sequence-forward-record-at-head (count (len words)))
           (:instance sequence-cell-word-is-relative-pointer)
           (:instance sequence-value-view-at-greater-rank
                      (word (car words)) (datum (car datums))
                      (depth first-rank) (greater (+ first-rank (1- (len words)))))
           (:instance sequence-forward-cons-at-next-rank (count (len words)) (tail (cdr datums)))
           (:instance sequence-cons-value-from-ranked-fields
                      (word (sequence-cell-word cell base)) (first (car datums)) (rest (cdr datums))))))
   :rule-classes nil))

(local
 (defthm sequence-fill-register-word-is-natural
   (natp (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg)))
   :rule-classes :type-prescription))

(defthm sequence-subseq-list-fill-source-value
  (let* ((first (proof-world-machine before))
         (base (proof-heap-base before))
         (word (proof-world-reg 2 before))
         (cell (proof-world-reg 1 before))
         (path (sequence-subseq-list-fill-path count before))
         (after (sequence-execute path before))
         (last (proof-world-machine after))
         (cuts (list (+ 44 (proof-world-pc before)))))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers first))
          (equal (proof-world-reg 19 before) count)
          (equal (proof-world-reg 0 before) (sequence-cell-word cell base))
          (equal (proof-world-reg 5 before) *proof-nil*)
          (posp count) (natp first-rank) (natp base) (<= base cell)
          (proof-span-p cell (* 16 count)) (unsigned-byte-p 64 (+ cell (* 16 count)))
          (equal (mod (- cell base) 8) 0)
          (unsigned-byte-p 64 (+ 44 (proof-world-pc before)))
          (sequence-subseq-readable-cells-p count word base cell (+ cell (* 16 count))
                                            (boymoo-model::a64-memory first))
          (proof-value-p word datum base objects packages first)
          (proof-value-p *proof-nil* nil base objects packages first)
          (sequence-object-storage-agrees-p objects first last)
          (sequence-object-lookups-agree-p objects objects extended)
          (sequence-ranks-below-p objects first-rank)
          (sequence-forward-copy-ranks-p count cell first-rank extended)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-reg-value-p 0 (take count datum) after extended packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                    (proof-view-step proof-value-p proof-segment-p sequence-cell-word take
                     proof-world-reg proof-world-machine proof-world-pc proof-heap-base
                     sequence-execute sequence-subseq-list-fill-path sequence-subseq-list-fill-memory
                     sequence-forward-copy-ranks-p sequence-subseq-copy-words sequence-forward-cell-fields-p
                     sequence-subseq-readable-cells-p sequence-object-lookups-agree-p sequence-ranks-below-p))
    :use ((:instance sequence-subseq-list-fill-segment
                     (lower (proof-world-reg 1 before)) (upper (+ (proof-world-reg 1 before) (* 16 count))))
          (:instance sequence-subseq-list-fill-effects
                     (lower (proof-world-reg 1 before)) (upper (+ (proof-world-reg 1 before) (* 16 count))))
          (:instance sequence-subseq-forward-fields-from-index
                     (index 0) (cell (proof-world-reg 1 before)) (base (proof-heap-base before))
                     (word (proof-world-reg 2 before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before))))
          (:instance sequence-subseq-selected-words-represent-take
                     (depth first-rank) (base (proof-heap-base before)) (word (proof-world-reg 2 before))
                     (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute (sequence-subseq-list-fill-path count before) before))))
          (:instance sequence-old-value-at-rank-in-extended-map
                     (word *proof-nil*) (datum nil) (depth first-rank) (base (proof-heap-base before))
                     (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute (sequence-subseq-list-fill-path count before) before))))
          (:instance sequence-forward-cells-represent-datums
                     (objects extended) (datums (take count datum))
                     (cell (proof-world-reg 1 before)) (base (proof-heap-base before))
                     (words (sequence-subseq-copy-words count (proof-world-reg 2 before) (proof-heap-base before)
                                                        (boymoo-model::a64-memory (proof-world-machine before))))
                     (machine (proof-world-machine (sequence-execute (sequence-subseq-list-fill-path count before) before)))))))
  :rule-classes nil)
