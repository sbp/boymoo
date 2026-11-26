(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-instruction-at-p proof-instruction-access-p
                    proof-instruction-effect proof-world-reg proof-world-pc
                    proof-world-stop proof-world-machine
                    boymoo-model::a64-execute boymoo-model::a64-store))

(defun generated-instruction-p (instruction world)
  (and (not (proof-world-stop world))
       (proof-instruction-at-p instruction (proof-world-pc world) world)
       (proof-instruction-access-p instruction world)))

(defthm generated-step-of-placed-instruction
  (implies (generated-instruction-p instruction world)
           (equal (proof-step world)
                  (proof-instruction-effect instruction world)))
  :hints (("Goal" :use proof-step-from-instruction))
  :rule-classes nil)

(defun generated-before-cuts-p (count cuts world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (not (proof-world-stop world))
         (not (member-equal (proof-world-pc world) cuts))
         (generated-before-cuts-p (1- count) cuts (proof-step world)))))

(defthm generated-before-cuts-append
  (equal (generated-before-cuts-p (+ (nfix prefix) (nfix suffix)) cuts world)
         (and (generated-before-cuts-p prefix cuts world)
              (generated-before-cuts-p suffix cuts (proof-advance prefix world))))
  :hints (("Goal" :induct (proof-advance prefix world))))

(defthm generated-run-of-clear-prefix
  (implies (generated-before-cuts-p prefix cuts world)
           (equal (proof-run (+ (nfix prefix) (nfix suffix)) cuts world)
                  (proof-run suffix cuts (proof-advance prefix world))))
  :hints (("Goal" :induct (proof-advance prefix world))))

(defthm generated-prefix-then-segment
  (implies (and (generated-before-cuts-p prefix cuts before)
                (equal middle (proof-advance prefix before))
                (proof-segment-p suffix cuts middle reason after))
           (proof-segment-p (+ (nfix prefix) (nfix suffix)) cuts before reason after))
  :hints (("Goal" :use (:instance generated-run-of-clear-prefix (world before))
                  :in-theory (e/d (proof-segment-p) (generated-run-of-clear-prefix))))
  :rule-classes nil)

(defun generated-cut-p (count cuts before after)
  (and (natp count)
       (generated-before-cuts-p count cuts before)
       (equal after (proof-advance count before))
       (not (proof-world-stop after))
       (member-equal (proof-world-pc after) cuts)))

(defthm generated-cut-is-segment
  (implies (generated-cut-p count cuts before after)
           (proof-segment-p count cuts before :cut after))
  :hints (("Goal" :use (:instance generated-run-of-clear-prefix
                                  (prefix count) (suffix 0) (world before))
                  :in-theory (disable generated-run-of-clear-prefix))))

(defthm generated-cut-compose
  (implies (and (generated-before-cuts-p prefix cuts before)
                (equal middle (proof-advance prefix before))
                (generated-cut-p suffix cuts middle after))
           (generated-cut-p (+ (nfix prefix) suffix) cuts before after))
  :rule-classes nil)

(defun generated-path-after (instructions world)
  (if (atom instructions)
      world
    (generated-path-after (cdr instructions)
                          (proof-instruction-effect (car instructions) world))))

(defun generated-path-p (instructions cuts world)
  (if (atom instructions)
      (null instructions)
    (and (not (member-equal (proof-world-pc world) cuts))
         (generated-instruction-p (car instructions) world)
         (generated-path-p (cdr instructions) cuts
                           (proof-instruction-effect (car instructions) world)))))

(defthm generated-advance-of-placed-path
  (implies (generated-path-p instructions cuts world)
           (and (generated-before-cuts-p (len instructions) cuts world)
                (equal (proof-advance (len instructions) world)
                       (generated-path-after instructions world))))
  :hints (("Goal" :induct (generated-path-p instructions cuts world))
          ("Subgoal *1/2" :use (:instance generated-step-of-placed-instruction
                                           (instruction (car instructions))))))

(defthm generated-placed-path-allows-fewer-cuts
  (implies (and (subsetp-equal cuts all-cuts)
                (generated-path-p path all-cuts before))
           (generated-path-p path cuts before))
  :hints (("Goal" :induct (generated-path-p path all-cuts before)))
  :rule-classes nil)

(defthm generated-placed-path-to-cut
  (let ((after (generated-path-after instructions before)))
    (implies (and (generated-path-p instructions cuts before)
                  (not (proof-world-stop after))
                  (member-equal (proof-world-pc after) cuts))
             (proof-segment-p (len instructions) cuts before :cut after)))
  :hints (("Goal" :use (:instance generated-cut-is-segment
                                  (count (len instructions))
                                  (after (generated-path-after instructions before)))
                  :in-theory (disable generated-cut-is-segment)))
  :rule-classes nil)

(defthm generated-path-after-append
  (equal (generated-path-after (append first second) world)
         (generated-path-after second (generated-path-after first world))))

(defthm generated-path-p-of-append
  (implies (true-listp first)
           (equal (generated-path-p (append first second) cuts world)
                  (and (generated-path-p first cuts world)
                       (generated-path-p second cuts (generated-path-after first world))))))

(defund generated-set-machine (machine world)
  (update-nth 0 machine world))

(defund generated-set-pc (pc world)
  (generated-set-machine
   (boymoo-model::a64-set-pc pc (proof-world-machine world)) world))

(defund generated-set-reg (register value world)
  (generated-set-machine
   (boymoo-model::a64-write-reg register 64 nil value (proof-world-machine world)) world))

(defund generated-set-sp (sp world)
  (generated-set-machine
   (boymoo-model::a64-write-reg 31 64 t sp (proof-world-machine world)) world))

(defund generated-set-flags (flags world)
  (generated-set-machine
   (boymoo-model::a64-set-nzcv flags (proof-world-machine world)) world))

(defund generated-store-word (address value world)
  (generated-set-machine
   (boymoo-model::a64-store 8 address value (proof-world-machine world)) world))

(defun generated-sp (world)
  (boymoo-model::a64-sp (proof-world-machine world)))

(defun generated-flags (world)
  (boymoo-model::a64-nzcv (proof-world-machine world)))

(defun generated-load-word (address world)
  (proof-load-word address (proof-world-machine world)))

(defthm generated-world-projections
  (and (equal (proof-world-machine (generated-set-machine machine world)) machine)
       (equal (proof-world-stop (generated-set-machine machine world))
              (proof-world-stop world))
       (equal (proof-world-reg register (generated-set-machine machine world))
              (proof-reg register machine))
       (equal (proof-world-pc (generated-set-machine machine world))
              (boymoo-model::a64-pc machine))
       (equal (proof-world-regions (generated-set-machine machine world))
              (proof-world-regions world))
       (equal (proof-world-replies (generated-set-machine machine world))
              (proof-world-replies world))
       (equal (proof-world-input (generated-set-machine machine world))
              (proof-world-input world))
       (equal (proof-world-stdout (generated-set-machine machine world))
              (proof-world-stdout world))
       (equal (proof-world-stderr (generated-set-machine machine world))
              (proof-world-stderr world))
       (equal (proof-world-page-size (generated-set-machine machine world))
              (proof-world-page-size world)))
  :hints (("Goal" :in-theory (enable generated-set-machine proof-world-reg
                                    proof-world-machine proof-world-stop proof-world-pc))))
