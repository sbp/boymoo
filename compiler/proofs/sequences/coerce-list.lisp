(in-package "BOYMOO-PROOFS")

(include-book "copy-loops")
(include-book "cell-memory")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-coerce-list-copy-path (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (append *sequence-coerce-list-step* (sequence-coerce-list-copy-path (1- count)))))

(defun sequence-cell-word (cell base)
  (boymoo-model::a64-unsigned 64 (- cell base)))

(defun sequence-coerce-list-copy-memory (count source cell tail base memory)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      memory
    (let* ((byte (boymoo-model::a64-byte (+ source (1- count)) memory))
           (word (+ 4 (* 8 byte))))
      (sequence-coerce-list-copy-memory
       (1- count) source (+ cell 16) (sequence-cell-word cell base) base
       (sequence-write-cell cell word tail memory)))))

(defthm sequence-coerce-list-copy-step-count
  (equal (len (sequence-coerce-list-copy-path count)) (* 8 (nfix count)))
  :hints (("Goal" :induct (sequence-coerce-list-copy-path count))))

(local
 (defthm sequence-coerce-copy-register-is-natural
   (natp (proof-world-reg register world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-register-bearing-world-is-a-cons
   (implies (consp (boymoo-model::a64-registers (proof-world-machine world)))
            (consp world))
   :hints (("Goal" :in-theory (enable proof-world-machine boymoo-model::a64-registers)))
   :rule-classes :forward-chaining))

(local
 (defun sequence-coerce-list-copy-induction (count before)
   (declare (xargs :measure (nfix count)))
   (if (<= (nfix count) 1)
       before
     (sequence-coerce-list-copy-induction
      (1- count) (sequence-execute *sequence-coerce-list-step* before)))))

(local
 (defthm sequence-coerce-list-path-unroll
   (implies (posp count)
            (equal (sequence-coerce-list-copy-path count)
                   (append *sequence-coerce-list-step* (sequence-coerce-list-copy-path (1- count)))))
   :hints (("Goal" :expand ((sequence-coerce-list-copy-path count))))))

(local
 (defthm sequence-coerce-list-memory-unroll
   (implies (posp count)
            (equal (sequence-coerce-list-copy-memory count source cell tail base memory)
                   (let* ((byte (boymoo-model::a64-byte (+ source (1- count)) memory))
                          (word (+ 4 (* 8 byte))))
                     (sequence-coerce-list-copy-memory
                      (1- count) source (+ cell 16) (sequence-cell-word cell base) base
                      (sequence-write-cell cell word tail memory)))))
   :hints (("Goal" :expand ((sequence-coerce-list-copy-memory count source cell tail base memory))))))

(local
 (defthm sequence-final-cons-address-telescope
   (equal (+ 16 cell (* 16 (+ -2 count))) (+ -16 cell (* 16 count)))))

(local
 (defthm sequence-coerce-copy-execution-unroll
   (implies (posp count)
            (equal (sequence-execute (sequence-coerce-list-copy-path count) before)
                   (sequence-execute (sequence-coerce-list-copy-path (1- count))
                                     (sequence-execute *sequence-coerce-list-step* before))))
   :hints (("Goal" :in-theory (disable acl2::binary-append)
                   :expand ((sequence-coerce-list-copy-path count))))))

(defthm sequence-coerce-list-copy-effects
  (let* ((machine (proof-world-machine before))
         (source (proof-world-reg 1 before))
         (cell (proof-world-reg 5 before))
         (base (proof-heap-base before))
         (tail (proof-world-reg 0 before))
         (path (sequence-coerce-list-copy-path count))
         (after (sequence-execute path before)))
    (implies (and (equal (proof-world-reg 2 before) count)
                  (posp count)
                  (consp (boymoo-model::a64-registers machine))
                  (proof-span-p source count)
                  (unsigned-byte-p 64 (+ cell (* 16 count)))
                  (unsigned-byte-p 64 (+ 32 (proof-world-pc before))))
             (and (equal (proof-world-pc after) (+ 32 (proof-world-pc before)))
                  (equal (proof-world-reg 2 after) 0)
                  (equal (proof-world-reg 0 after)
                         (sequence-cell-word (+ cell (* 16 (1- count))) base))
                  (equal (proof-heap-base after) base)
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (sequence-coerce-list-copy-memory
                          count source cell tail base (boymoo-model::a64-memory machine))))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-write-cell)
                    ((:definition sequence-coerce-list-copy-path)
                     (:definition sequence-coerce-list-copy-memory)
                     sequence-coerce-list-path-unroll sequence-coerce-list-memory-unroll
                     acl2::binary-append proof-world-machine proof-world-reg
                     proof-world-pc proof-world-stop proof-heap-base))
    :do-not '(eliminate-destructors fertilize generalize)
    :induct (sequence-coerce-list-copy-induction count before))
   ("Subgoal *1/2"
    :use (sequence-coerce-list-step-effects
          (:instance sequence-coerce-list-memory-unroll
                     (source (proof-world-reg 1 before)) (cell (proof-world-reg 5 before))
                     (tail (proof-world-reg 0 before)) (base (proof-heap-base before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before))))))
   ("Subgoal *1/1"
    :expand ((sequence-coerce-list-copy-path 0)
             (:free (source cell tail base memory)
                    (sequence-coerce-list-copy-memory 0 source cell tail base memory))
             (:free (world) (sequence-execute nil world)))
    :use (sequence-coerce-list-step-effects
          (:instance sequence-coerce-list-memory-unroll
                     (source (proof-world-reg 1 before)) (cell (proof-world-reg 5 before))
                     (tail (proof-world-reg 0 before)) (base (proof-heap-base before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before)))))))
  :rule-classes nil)

(defthm sequence-coerce-list-copy-segment
  (let* ((path (sequence-coerce-list-copy-path count))
         (cuts (list (+ 32 (proof-world-pc before))))
         (after (sequence-execute path before)))
    (implies (and (not (proof-world-stop before))
                  (equal (proof-world-reg 2 before) count)
                  (posp count)
                  (consp (boymoo-model::a64-registers (proof-world-machine before)))
                  (proof-span-p (proof-world-reg 1 before) count)
                  (unsigned-byte-p 64 (+ (proof-world-reg 5 before) (* 16 count)))
                  (unsigned-byte-p 64 (+ 32 (proof-world-pc before)))
                  (sequence-instruction-path path cuts before))
             (and (proof-segment-p (* 8 count) cuts before :cut after)
                  (equal (proof-world-reg 0 after)
                         (sequence-cell-word (+ (proof-world-reg 5 before) (* 16 (1- count)))
                                             (proof-heap-base before)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (sequence-coerce-list-copy-memory
                          count (proof-world-reg 1 before) (proof-world-reg 5 before)
                          (proof-world-reg 0 before) (proof-heap-base before)
                          (boymoo-model::a64-memory (proof-world-machine before)))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p sequence-coerce-list-copy-path sequence-coerce-list-copy-memory)
    :use (sequence-coerce-list-copy-effects
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-coerce-list-copy-path count))
                     (cuts (list (+ 32 (proof-world-pc before))))
                     (after (sequence-execute (sequence-coerce-list-copy-path count) before))))))
  :rule-classes nil)
