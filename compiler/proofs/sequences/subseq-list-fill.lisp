(in-package "BOYMOO-PROOFS")

(include-book "coerce-list")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-list-cell-path (world)
  (if (equal (proof-word-tag (proof-world-reg 2 world)) 0)
      *sequence-subseq-list-copy-cell*
    *sequence-subseq-list-copy-nil*))

(defun sequence-subseq-list-fill-path (count world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let* ((step (sequence-subseq-list-cell-path world))
           (next (sequence-execute step world)))
      (append step (sequence-subseq-list-fill-path (1- count) next)))))

(defun sequence-subseq-list-fill-memory (count word base cell memory)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      memory
    (let* ((present (equal (proof-word-tag word) 0))
           (address (proof-pointer-address word base))
           (first (if present (boymoo-model::a64-read-bytes 8 address memory) *proof-nil*))
           (next-word (if present (boymoo-model::a64-read-bytes 8 (+ address 8) memory) word))
           (next-cell (+ 16 cell))
           (rest (if (equal count 1) *proof-nil* (sequence-cell-word next-cell base))))
      (sequence-subseq-list-fill-memory
       (1- count) next-word base next-cell
       (sequence-write-cell cell first rest memory)))))

(defun sequence-subseq-readable-cells-p (count word base lower upper memory)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (not (equal (proof-word-tag word) 0)))
      t
    (let ((address (proof-pointer-address word base)))
      (and (proof-span-p address 16)
           (proof-disjoint-p address (+ address 16) lower upper)
           (sequence-subseq-readable-cells-p
            (1- count) (boymoo-model::a64-read-bytes 8 (+ address 8) memory)
            base lower upper memory)))))

(defthm sequence-subseq-readable-cells-survive-output-write
  (implies (and (sequence-subseq-readable-cells-p count word base lower upper memory)
                (proof-subspan-p cell 16 lower upper))
           (sequence-subseq-readable-cells-p count word base lower upper
                                            (sequence-write-cell cell first rest memory)))
  :hints
  (("Goal"
    :induct (sequence-subseq-readable-cells-p count word base lower upper memory)
    :in-theory (disable proof-word-tag proof-pointer-address)
    :expand ((:free (state)
                    (sequence-subseq-readable-cells-p count word base lower upper state))))))

(local
 (defthm sequence-subseq-readable-head-span
   (implies (and (posp count)
                 (equal (proof-word-tag word) 0)
                 (sequence-subseq-readable-cells-p count word base lower upper memory))
            (proof-span-p (proof-pointer-address word base) 16))
   :hints (("Goal" :expand ((sequence-subseq-readable-cells-p count word base lower upper memory))))))

(defthm sequence-subseq-readable-tail
  (implies (and (posp count)
                (sequence-subseq-readable-cells-p count word base lower upper memory))
           (sequence-subseq-readable-cells-p
            (1- count)
            (if (equal (proof-word-tag word) 0)
                (boymoo-model::a64-read-bytes 8
                                             (+ 8 (proof-pointer-address word base)) memory)
              word)
            base lower upper memory))
  :hints
  (("Goal"
    :expand ((sequence-subseq-readable-cells-p count word base lower upper memory)
             (sequence-subseq-readable-cells-p (1- count) word base lower upper memory))))
  :rule-classes nil)

(local
 (defun sequence-list-fill-induction (count world)
   (declare (xargs :measure (nfix count)))
   (if (<= (nfix count) 1)
       world
     (sequence-list-fill-induction
      (1- count) (sequence-execute (sequence-subseq-list-cell-path world) world)))))

(local
 (defthm sequence-subseq-fill-execution-unroll
   (implies (posp count)
            (equal (sequence-execute (sequence-subseq-list-fill-path count before) before)
                   (let ((next (sequence-execute (sequence-subseq-list-cell-path before) before)))
                     (sequence-execute (sequence-subseq-list-fill-path (1- count) next) next))))
   :hints (("Goal" :in-theory (disable acl2::binary-append sequence-subseq-list-cell-path)
                   :expand ((sequence-subseq-list-fill-path count before))))))

(local
 (defthm sequence-subseq-fill-register-is-natural
   (natp (proof-world-reg register world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-subseq-fill-world-is-cons
   (implies (consp (boymoo-model::a64-registers (proof-world-machine world)))
            (consp world))
   :hints (("Goal" :in-theory (enable proof-world-machine boymoo-model::a64-registers)))
   :rule-classes :forward-chaining))

(local
 (defthm sequence-subseq-list-step-with-readable-tail
   (let* ((machine (proof-world-machine before))
          (memory (boymoo-model::a64-memory machine))
          (word (proof-world-reg 2 before))
          (cell (proof-world-reg 1 before))
          (base (proof-heap-base before))
          (count (proof-world-reg 19 before))
          (address (proof-pointer-address word base))
          (present (equal (proof-word-tag word) 0))
          (first (if present (boymoo-model::a64-read-bytes 8 address memory) *proof-nil*))
          (rest (if (equal count 1) *proof-nil* (sequence-cell-word (+ 16 cell) base)))
          (after (sequence-execute (sequence-subseq-list-cell-path before) before)))
     (implies (and (consp (boymoo-model::a64-registers machine))
                   (equal (proof-world-reg 5 before) *proof-nil*)
                   (posp count) (unsigned-byte-p 64 (+ cell 16))
                   (unsigned-byte-p 64 (+ 44 (proof-world-pc before)))
                   (proof-subspan-p cell 16 lower upper)
                   (sequence-subseq-readable-cells-p count word base lower upper memory))
              (and (equal (proof-world-pc after)
                          (if (equal count 1) (+ 44 (proof-world-pc before)) (proof-world-pc before)))
                   (equal (proof-world-reg 19 after) (1- count))
                   (equal (proof-world-reg 1 after) (+ 16 cell))
                   (equal (proof-world-reg 2 after)
                          (if present (boymoo-model::a64-read-bytes 8 (+ 8 address) memory) word))
                   (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                   (equal (proof-world-reg 5 after) *proof-nil*)
                   (equal (proof-heap-base after) base)
                   (consp (boymoo-model::a64-registers (proof-world-machine after)))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (sequence-write-cell cell first rest memory))
                   (sequence-subseq-readable-cells-p
                    (1- count) (proof-world-reg 2 after) base lower upper
                    (boymoo-model::a64-memory (proof-world-machine after))))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-write-cell proof-load-word)
                     (proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                      proof-heap-base proof-word-tag proof-pointer-address
                      sequence-subseq-readable-cells-p sequence-subseq-readable-cells-survive-output-write))
     :use (sequence-subseq-list-step-effects
           (:instance sequence-subseq-readable-head-span
                      (count (proof-world-reg 19 before))
                      (word (proof-world-reg 2 before)) (base (proof-heap-base before))
                      (memory (boymoo-model::a64-memory (proof-world-machine before))))
           (:instance sequence-subseq-readable-tail
                      (count (proof-world-reg 19 before))
                      (word (proof-world-reg 2 before)) (base (proof-heap-base before))
                      (memory (boymoo-model::a64-memory (proof-world-machine before))))
           (:instance sequence-subseq-readable-cells-survive-output-write
                      (count (1- (proof-world-reg 19 before)))
                      (word (proof-world-reg 2
                              (sequence-execute (sequence-subseq-list-cell-path before) before)))
                      (base (proof-heap-base before))
                      (cell (proof-world-reg 1 before))
                      (memory (boymoo-model::a64-memory (proof-world-machine before)))
                      (first (if (equal (proof-word-tag (proof-world-reg 2 before)) 0)
                                 (proof-load-word (proof-pointer-address (proof-world-reg 2 before)
                                                                        (proof-heap-base before))
                                                  (proof-world-machine before))
                               *proof-nil*))
                      (rest (if (equal (proof-world-reg 19 before) 1)
                                *proof-nil*
                              (sequence-cell-word (+ 16 (proof-world-reg 1 before))
                                                  (proof-heap-base before))))))))
   :rule-classes nil))

(defthm sequence-subseq-list-fill-effects
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (base (proof-heap-base before))
         (word (proof-world-reg 2 before))
         (cell (proof-world-reg 1 before))
         (path (sequence-subseq-list-fill-path count before))
         (after (sequence-execute path before)))
    (implies
     (and (equal (proof-world-reg 19 before) count)
          (equal (proof-world-reg 5 before) *proof-nil*)
          (posp count)
          (consp (boymoo-model::a64-registers machine))
          (proof-subspan-p cell (* 16 count) lower upper)
          (unsigned-byte-p 64 (+ cell (* 16 count)))
          (unsigned-byte-p 64 (+ 44 (proof-world-pc before)))
          (sequence-subseq-readable-cells-p count word base lower upper memory))
     (and (equal (proof-world-pc after) (+ 44 (proof-world-pc before)))
          (equal (proof-world-reg 19 after) 0)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-heap-base after) base)
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (sequence-subseq-list-fill-memory count word base cell memory)))))
  :hints
  (("Goal"
    :in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                        proof-heap-base proof-word-tag proof-pointer-address sequence-cell-word
                        sequence-subseq-readable-cells-p acl2::binary-append sequence-subseq-list-cell-path
                        (:definition sequence-subseq-list-fill-path)
                        (:definition sequence-subseq-list-fill-memory))
    :induct (sequence-list-fill-induction count before)
    :do-not '(eliminate-destructors fertilize generalize))
   ("Subgoal *1/1"
    :expand ((:free (world) (sequence-subseq-list-fill-path 0 world))
             (:free (world) (sequence-execute nil world))
             (:free (word base cell memory) (sequence-subseq-list-fill-memory 0 word base cell memory))
             (:free (word base cell memory) (sequence-subseq-list-fill-memory 1 word base cell memory)))
    :use sequence-subseq-list-step-with-readable-tail)
   ("Subgoal *1/2"
    :expand ((sequence-subseq-list-fill-memory count (proof-world-reg 2 before)
                                               (proof-heap-base before) (proof-world-reg 1 before)
                                               (boymoo-model::a64-memory (proof-world-machine before))))
    :use sequence-subseq-list-step-with-readable-tail))
  :rule-classes nil)

(defthm sequence-subseq-list-fill-segment
  (let* ((machine (proof-world-machine before))
         (path (sequence-subseq-list-fill-path count before))
         (cuts (list (+ 44 (proof-world-pc before))))
         (after (sequence-execute path before)))
    (implies
     (and (equal (proof-world-reg 19 before) count)
          (equal (proof-world-reg 5 before) *proof-nil*)
          (posp count)
          (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (proof-subspan-p (proof-world-reg 1 before) (* 16 count) lower upper)
          (unsigned-byte-p 64 (+ (proof-world-reg 1 before) (* 16 count)))
          (unsigned-byte-p 64 (+ 44 (proof-world-pc before)))
          (sequence-subseq-readable-cells-p count (proof-world-reg 2 before)
                                           (proof-heap-base before) lower upper
                                           (boymoo-model::a64-memory machine))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (sequence-subseq-list-fill-memory count (proof-world-reg 2 before)
                                                   (proof-heap-base before) (proof-world-reg 1 before)
                                                   (boymoo-model::a64-memory machine))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p sequence-subseq-list-fill-path sequence-subseq-list-fill-memory
                        sequence-subseq-readable-cells-p)
    :use (sequence-subseq-list-fill-effects
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-subseq-list-fill-path count before))
                     (cuts (list (+ 44 (proof-world-pc before))))
                     (after (sequence-execute (sequence-subseq-list-fill-path count before) before))))))
  :rule-classes nil)
