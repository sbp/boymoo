(in-package "BOYMOO-PROOFS")

(include-book "heap-views")
(include-book "frames")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-world-reg
                    proof-world-machine proof-world-pc proof-world-stop proof-world-regions
                    generated-load-word generated-store-word boymoo-model::a64-unsigned
                    boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-address
                    boymoo-model::a64-store boymoo-model::a64-write-bytes expt))

(defcong generated-memory-equiv generated-memory-equiv
  (boymoo-model::a64-store width address value machine) 4
  :hints (("Goal" :in-theory (enable generated-memory-equiv boymoo-model::a64-store
                                    boymoo-model::a64-memory))))

(defcong generated-heap-world-equiv equal (generated-load-word address world) 2
  :hints (("Goal" :in-theory (enable generated-load-word))))

(defcong generated-heap-world-equiv equal (generated-read-words count address world) 3
  :hints (("Goal" :induct (generated-read-words count address world)
                  :in-theory (enable generated-read-words))))

(defthm generated-machine-after-word-store
  (equal (proof-world-machine (generated-store-word address value world))
         (boymoo-model::a64-store 8 address value (proof-world-machine world)))
  :hints (("Goal" :in-theory (enable generated-store-word))))

(defcong generated-heap-world-equiv generated-heap-world-equiv
  (generated-store-word address value world) 3
  :hints (("Goal" :in-theory
           (enable generated-heap-world-equiv proof-machine-limit proof-stack-top
                   proof-stack-limit proof-heap-limit proof-box-top proof-heap-base))))

(local
 (defun generated-copy-congruence-induction (count source destination first second)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons first second)
     (generated-copy-congruence-induction
      (1- count) (+ 8 source) (+ 8 destination)
      (generated-store-word destination (generated-load-word source first) first)
      (generated-store-word destination (generated-load-word source second) second)))))

(defcong generated-heap-world-equiv generated-heap-world-equiv
  (generated-copy-words count source destination world) 4
  :hints (("Goal" :induct (generated-copy-congruence-induction count source destination world world-equiv)
                  :expand ((generated-copy-words count source destination world)
                           (generated-copy-words count source destination world-equiv))
                  :in-theory (enable generated-copy-words))))

(defund generated-copy-pair (offset)
  (list (list :single 1 8 10 9 :offset offset) (list :single 0 8 19 9 :offset offset)))

(defund generated-copy-immediate-path (count offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (append (generated-copy-pair offset) (generated-copy-immediate-path (1- count) (+ 8 offset)))))

(defund generated-copy-immediate-items (count offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (list* (list :ldr 9 10 offset) (list :str 9 19 offset)
           (generated-copy-immediate-items (1- count) (+ 8 offset)))))

(defthm generated-copy-immediate-emission
  (implies (and (natp offset) (natp count) (<= (+ offset (* 8 count)) 32768))
           (equal (boymoo-compiler::gen-copy-arguments count offset code)
                  (boymoo-compiler::reverse-onto (generated-copy-immediate-items count offset) code)))
  :hints (("Goal" :induct (boymoo-compiler::gen-copy-arguments count offset code)
                  :in-theory (enable boymoo-compiler::gen-copy-arguments generated-copy-immediate-items)))
  :rule-classes nil)

(defthm generated-copy-immediate-path-length
  (equal (len (generated-copy-immediate-path count offset)) (* 2 (nfix count)))
  :hints (("Goal" :induct (generated-copy-immediate-path count offset)
                  :in-theory (enable generated-copy-immediate-path generated-copy-pair))))

(defthm generated-copy-pair-effect
  (let* ((after (generated-path-after (generated-copy-pair offset) world))
         (source (+ (proof-world-reg 10 world) offset))
         (destination (+ (proof-world-reg 19 world) offset)))
    (implies (and (generated-ordinary-machine-p world) (natp offset))
             (and (generated-ordinary-machine-p after)
                  (equal (proof-world-reg 10 after) (proof-world-reg 10 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (generated-heap-world-equiv
                   after (generated-store-word destination (generated-load-word source world) world)))))
  :hints (("Goal" :in-theory (enable generated-copy-pair)))
  :rule-classes nil)

(local
 (defun generated-copy-path-induction (count offset world)
   (declare (xargs :measure (nfix count)))
   (if (zp count) world
     (generated-copy-path-induction (1- count) (+ 8 offset)
                                    (generated-path-after (generated-copy-pair offset) world)))))

(defthm generated-copy-immediate-path-effect
  (let ((source (+ (proof-world-reg 10 world) offset))
        (destination (+ (proof-world-reg 19 world) offset)))
    (implies (and (generated-ordinary-machine-p world) (natp offset))
             (generated-heap-world-equiv
              (generated-path-after (generated-copy-immediate-path count offset) world)
              (generated-copy-words count source destination world))))
  :hints (("Goal" :induct (generated-copy-path-induction count offset world)
                  :in-theory (enable generated-copy-immediate-path generated-copy-words))
          ("Subgoal *1/2" :use generated-copy-pair-effect)))

(defthm generated-copy-immediate-path-registers
  (let ((after (generated-path-after (generated-copy-immediate-path count offset) world)))
    (implies (and (generated-ordinary-machine-p world) (natp offset))
             (and (generated-ordinary-machine-p after)
                  (equal (generated-sp after) (generated-sp world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (implies (not (equal register 9))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :induct (generated-copy-path-induction count offset world)
                  :in-theory (enable generated-copy-immediate-path generated-copy-pair))))

(defthm generated-copy-immediate-path-pc
  (let ((after (generated-path-after (generated-copy-immediate-path count offset) world)))
    (implies (and (generated-ordinary-machine-p world) (natp offset) (natp count)
                  (< (+ (proof-world-pc world) (* 8 count)) (expt 2 64)))
             (equal (proof-world-pc after) (+ (proof-world-pc world) (* 8 count)))))
  :hints (("Goal" :induct (generated-copy-path-induction count offset world)
                  :in-theory (enable generated-copy-immediate-path generated-copy-pair))))

(defthm generated-read-words-of-updates
  (and (equal (generated-read-words count address (generated-set-pc pc world))
              (generated-read-words count address world))
       (equal (generated-read-words count address (generated-set-reg reg value world))
              (generated-read-words count address world))
       (equal (generated-read-words count address (generated-set-sp sp world))
              (generated-read-words count address world))
       (equal (generated-read-words count address (generated-set-flags flags world))
              (generated-read-words count address world)))
  :hints (("Goal" :induct (generated-read-words count address world)
                  :in-theory (enable generated-read-words))))

(defthm generated-copy-immediate-path-words
  (let* ((source (+ (proof-world-reg 10 before) offset))
         (destination (+ (proof-world-reg 19 before) offset))
         (path (generated-copy-immediate-path count offset))
         (after (generated-path-after path before)))
    (implies (and (generated-ordinary-machine-p before) (natp offset)
                  (generated-word-block-span-p source count)
                  (generated-word-block-span-p destination count) (<= destination source)
                  (generated-path-p path cuts before)
                  (member-equal (proof-world-pc after) cuts) (not (proof-world-stop after)))
             (and (proof-segment-p (* 2 count) cuts before :cut after)
                  (equal (generated-read-words count destination after)
                         (generated-read-words count source before)))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions (generated-copy-immediate-path count offset)))
                  :in-theory (disable generated-path-p generated-path-after)))
  :rule-classes nil)
