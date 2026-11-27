(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defun division-label-offset (label items)
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout items 0 nil nil)
    (declare (ignore end reversed))
    (boymoo-compiler::a64-offset label labels)))

(defun division-decode-instructions (count address machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-decode-at address machine)
          (division-decode-instructions (1- count) (+ address 4) machine))))

; The code contains the runtime and a generated identity function.
(defun division-linked-example-items ()
  (boymoo-compiler::compile-items "ACL2::IDENTITY"
   '(("ACL2::IDENTITY" ("ACL2::X") "ACL2::X"))
   (list nil nil nil) (cons 0 nil) (boymoo-compiler::linux-system-code)))

(defthm division-raw-model-clz-coverage
  (let ((word (boymoo-compiler::a64-word '(:clz 10 10) 0 nil)))
    (and (equal (boymoo-model::a64-decode word) '(:clz 10 10))
         (equal (proof-decode word) '(:clz 10 10))))
  :rule-classes nil)

(defun division-instruction-sequence (instructions world)
  (if (atom instructions)
      world
    (division-instruction-sequence (cdr instructions)
                                    (proof-instruction-effect (car instructions) world))))

(defun division-instruction-sequence-ready-p (instructions cuts world)
  (and (not (proof-world-stop world))
       (if (atom instructions)
           (and (null instructions) (member-equal (proof-world-pc world) cuts))
         (and (not (member-equal (proof-world-pc world) cuts))
              (proof-instruction-at-p (car instructions) (proof-world-pc world) world)
              (proof-instruction-access-p (car instructions) world)
              (division-instruction-sequence-ready-p
               (cdr instructions) cuts (proof-instruction-effect (car instructions) world))))))

(defthm division-instruction-sequence-finishes-at-ready-cut
  (implies (division-instruction-sequence-ready-p instructions cuts world)
           (let ((after (division-instruction-sequence instructions world)))
             (and (not (proof-world-stop after))
                  (member-equal (proof-world-pc after) cuts))))
  :hints (("Goal"
           :induct (division-instruction-sequence-ready-p instructions cuts world)
           :in-theory (disable proof-instruction-at-p proof-instruction-access-p
                               proof-instruction-effect proof-world-stop proof-world-pc)))
  :rule-classes nil)

(defthm division-instruction-sequence-runs-to-cut
  (implies (division-instruction-sequence-ready-p instructions cuts world)
           (proof-segment-p (len instructions) cuts world :cut
                            (division-instruction-sequence instructions world)))
  :hints (("Goal"
           :induct (division-instruction-sequence-ready-p instructions cuts world)
           :in-theory (disable proof-step proof-instruction-at-p proof-instruction-access-p
                               proof-instruction-effect proof-world-stop proof-world-pc)))
  :rule-classes nil)

(defthm division-instruction-sequence-advances
  (implies (division-instruction-sequence-ready-p instructions cuts world)
           (equal (proof-advance (len instructions) world)
                  (division-instruction-sequence instructions world)))
  :hints (("Goal"
           :induct (division-instruction-sequence-ready-p instructions cuts world)
           :in-theory (disable proof-step proof-instruction-at-p proof-instruction-access-p
                               proof-instruction-effect proof-world-stop proof-world-pc)))
  :rule-classes nil)

(local
 (defthm division-sequence-advance-once
   (equal (proof-advance 1 world) (proof-step world))
   :hints (("Goal" :expand ((proof-advance 1 world) (proof-advance 0 (proof-step world)))
                   :in-theory (disable proof-step)))))

(defthm division-instruction-sequence-then-one-step
  (let ((middle (division-instruction-sequence prefix world)))
    (implies (and (division-instruction-sequence-ready-p prefix cuts world)
                  (proof-instruction-at-p last (proof-world-pc middle) middle)
                  (proof-instruction-access-p last middle))
             (equal (proof-advance (1+ (len prefix)) world)
                    (proof-instruction-effect last middle))))
  :hints (("Goal"
           :use ((:instance division-instruction-sequence-finishes-at-ready-cut (instructions prefix))
                 (:instance division-instruction-sequence-advances (instructions prefix))
                 (:instance proof-step-from-instruction
                            (world (division-instruction-sequence prefix world)) (instruction last))
                 (:instance proof-advance-append (prefix (len prefix)) (suffix 1)))
           :in-theory (disable proof-step-from-instruction proof-step proof-advance proof-world-pc
                               proof-instruction-at-p proof-instruction-access-p proof-instruction-effect
                               division-instruction-sequence division-instruction-sequence-ready-p)))
  :rule-classes nil)

(defthm division-instruction-placement-preserved
  (implies (and (equal (proof-world-regions before) (proof-world-regions after))
                (equal (boymoo-model::a64-memory (proof-world-machine before))
                       (boymoo-model::a64-memory (proof-world-machine after))))
           (equal (proof-instruction-at-p instruction address after)
                  (proof-instruction-at-p instruction address before)))
  :hints (("Goal" :in-theory (disable proof-decode proof-covered-p boymoo-model::a64-read-bytes
                                      boymoo-model::a64-memory proof-world-machine proof-world-regions)))
  :rule-classes nil)

(defthm division-instructions-placement-preserved
  (implies (and (equal (proof-world-regions before) (proof-world-regions after))
                (equal (boymoo-model::a64-memory (proof-world-machine before))
                       (boymoo-model::a64-memory (proof-world-machine after))))
           (equal (proof-instructions-at-p instructions address after)
                  (proof-instructions-at-p instructions address before)))
  :hints (("Goal"
           :induct (proof-instructions-at-p instructions address before)
           :in-theory (disable proof-instruction-at-p boymoo-model::a64-memory
                               proof-world-machine proof-world-regions))
          ("Subgoal *1/2"
           :use (:instance division-instruction-placement-preserved (instruction (car instructions)))
           :expand ((proof-instructions-at-p instructions address after)))
          ("Subgoal *1/3"
           :use (:instance division-instruction-placement-preserved (instruction (car instructions)))
           :expand ((proof-instructions-at-p instructions address after))))
  :rule-classes nil)
