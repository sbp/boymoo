(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-step proof-world-stop proof-world-pc)))

(defun assembly-clear-prefix-p (count cuts world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (not (proof-world-stop world))
         (not (member-equal (proof-world-pc world) cuts))
         (assembly-clear-prefix-p (1- count) cuts (proof-step world)))))

(defthm assembly-run-after-clear-prefix
  (implies (assembly-clear-prefix-p prefix cuts world)
           (and (equal (mv-nth 0 (proof-run (+ (nfix prefix) (nfix suffix)) cuts world))
                       (mv-nth 0 (proof-run suffix cuts (proof-advance prefix world))))
                (equal (mv-nth 1 (proof-run (+ (nfix prefix) (nfix suffix)) cuts world))
                       (mv-nth 1 (proof-run suffix cuts (proof-advance prefix world))))))
  :hints (("Goal" :induct (proof-advance prefix world))))

(defthm assembly-segment-to-cutpoint
  (implies (and (natp count)
                (assembly-clear-prefix-p count cuts before)
                (equal after (proof-advance count before))
                (not (proof-world-stop after))
                (member-equal (proof-world-pc after) cuts))
           (proof-segment-p count cuts before :cut after))
  :hints (("Goal" :use ((:instance assembly-run-after-clear-prefix
                                   (prefix count) (suffix 0) (world before)))
                  :in-theory (disable assembly-run-after-clear-prefix))))

(defthm assembly-one-step-to-cutpoint
  (implies (and (not (proof-world-stop before))
                (not (member-equal (proof-world-pc before) cuts))
                (proof-instruction-at-p instruction (proof-world-pc before) before)
                (proof-instruction-access-p instruction before)
                (equal after (proof-instruction-effect instruction before))
                (not (proof-world-stop after))
                (member-equal (proof-world-pc after) cuts))
           (proof-segment-p 1 cuts before :cut after))
  :hints (("Goal"
           :expand ((proof-run 1 cuts before)
                    (proof-run 0 cuts (proof-instruction-effect instruction before)))
           :use ((:instance proof-step-from-instruction (world before)))
           :in-theory (disable proof-step-from-instruction proof-instruction-at-p
                                      proof-instruction-access-p
                                      proof-instruction-effect))))

(defun assembly-straight-line-effect (instructions world)
  (if (atom instructions)
      world
    (assembly-straight-line-effect
     (cdr instructions) (proof-instruction-effect (car instructions) world))))

(defun assembly-straight-line-p (instructions address cuts world)
  (and (not (proof-world-stop world))
       (equal (proof-world-pc world) address)
       (if (atom instructions)
           (and (null instructions) (member-equal address cuts))
         (and (not (member-equal address cuts))
              (proof-instruction-at-p (car instructions) address world)
              (proof-instruction-access-p (car instructions) world)
              (assembly-straight-line-p
               (cdr instructions) (+ 4 address) cuts
               (proof-instruction-effect (car instructions) world))))))

(local (in-theory (disable proof-instruction-at-p proof-instruction-access-p
                           proof-instruction-effect)))

(defthm assembly-straight-line-run
  (implies (assembly-straight-line-p instructions address cuts before)
           (proof-segment-p (len instructions) cuts before :cut
                            (assembly-straight-line-effect instructions before)))
  :hints (("Goal" :induct (assembly-straight-line-p instructions address cuts before))))

(defun assembly-branch-world (target link world)
  (let* ((machine (proof-world-machine world))
         (next (boymoo-model::a64-set-pc (+ (boymoo-model::a64-pc machine) 4) machine))
         (linked (if link
                     (boymoo-model::a64-write-reg 30 64 nil
                                                  (boymoo-model::a64-pc next)
                                                  next)
                   next)))
    (update-nth 0 (boymoo-model::a64-set-pc target linked) world)))

(local (in-theory (disable boymoo-model::a64-unsigned
                           boymoo-model::a64-read-reg
                           boymoo-model::a64-nzcv
                           boymoo-model::a64-condition
                           proof-linux-svc)))

(defun assembly-machine-registers-p (world)
  (alistp (boymoo-model::a64-registers (proof-world-machine world))))

(defthm assembly-car-of-update-nth
  (equal (car (update-nth n value list))
         (if (zp n) value (car list)))
  :hints (("Goal" :expand ((update-nth n value list)))))

(defthm assembly-update-same-index-twice
  (equal (update-nth n first (update-nth n second machine))
         (update-nth n first machine))
  :hints (("Goal" :induct (update-nth n first machine)
                  :expand ((update-nth n second machine)
                           (:free (record) (update-nth n first record))))))

(defthm assembly-effect-of-branch
  (implies (assembly-machine-registers-p world)
           (equal (proof-instruction-effect (list :branch delta link) world)
                  (assembly-branch-world (+ (proof-world-pc world) delta) link world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-world-pc
                                      boymoo-model::a64-unsigned))))

(defthm assembly-effect-of-branch-register
  (implies (assembly-machine-registers-p world)
           (equal (proof-instruction-effect (list :branch-reg register link) world)
                  (assembly-branch-world (proof-world-reg register world) link world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-world-pc
                                      boymoo-model::a64-unsigned))))

(defthm assembly-effect-of-branch-condition
  (implies (assembly-machine-registers-p world)
   (equal (proof-instruction-effect (list :branch-cond delta condition) world)
         (assembly-branch-world
          (+ (proof-world-pc world)
             (if (boymoo-model::a64-condition
                  condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                 delta
               4))
          nil world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-world-pc))))

(defthm assembly-effect-of-branch-zero
  (implies (assembly-machine-registers-p world)
   (equal (proof-instruction-effect (list :branch-zero delta 64 register nonzero) world)
         (assembly-branch-world
          (+ (proof-world-pc world)
             (if (if nonzero
                     (not (equal (proof-world-reg register world) 0))
                   (equal (proof-world-reg register world) 0))
                 delta
               4))
          nil world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-world-pc))))

(defthm assembly-branch-world-keeps-stop
  (equal (proof-world-stop (assembly-branch-world target link world))
         (proof-world-stop world))
  :hints (("Goal" :in-theory (enable proof-world-stop))))

(defun assembly-branch-condition-target (delta condition world)
  (+ (proof-world-pc world)
     (if (boymoo-model::a64-condition
          condition (boymoo-model::a64-nzcv (proof-world-machine world)))
         delta
       4)))

(defun assembly-branch-zero-target (delta register nonzero world)
  (+ (proof-world-pc world)
     (if (if nonzero
             (not (equal (proof-world-reg register world) 0))
           (equal (proof-world-reg register world) 0))
         delta
       4)))

(defmacro assembly-branch-run-rule (name instruction target link)
  `(defthm ,name
     (let ((after (assembly-branch-world ,target ,link before)))
       (implies (and (assembly-machine-registers-p before)
                     (not (proof-world-stop before))
                     (not (member-equal (proof-world-pc before) cuts))
                     (proof-instruction-at-p ,instruction (proof-world-pc before) before)
                     (member-equal (proof-world-pc after) cuts))
                (proof-segment-p 1 cuts before :cut after)))
     :hints (("Goal"
              :use ((:instance assembly-one-step-to-cutpoint
                               (instruction ,instruction)
                               (after (assembly-branch-world ,target ,link before))))
              :in-theory (e/d (proof-instruction-access-p)
                              (assembly-one-step-to-cutpoint assembly-branch-world
                               assembly-machine-registers-p proof-world-reg))))))

(assembly-branch-run-rule assembly-b-run
  (list :branch delta nil) (+ (proof-world-pc before) delta) nil)

(assembly-branch-run-rule assembly-bl-run
  (list :branch delta t) (+ (proof-world-pc before) delta) t)

(assembly-branch-run-rule assembly-br-run
  (list :branch-reg register nil) (proof-world-reg register before) nil)

(assembly-branch-run-rule assembly-blr-run
  (list :branch-reg register t) (proof-world-reg register before) t)

(assembly-branch-run-rule assembly-ret-run
  (list :branch-reg 30 nil) (proof-world-reg 30 before) nil)

(assembly-branch-run-rule assembly-b-cond-run
  (list :branch-cond delta condition)
  (assembly-branch-condition-target delta condition before) nil)

(assembly-branch-run-rule assembly-cbz-cbnz-run
  (list :branch-zero delta 64 register nonzero)
  (assembly-branch-zero-target delta register nonzero before) nil)

(defthm assembly-two-steps-to-cutpoint
  (implies (and (not (proof-world-stop before))
                (not (member-equal (proof-world-pc before) cuts))
                (proof-instruction-at-p first (proof-world-pc before) before)
                (proof-instruction-access-p first before)
                (equal between (proof-instruction-effect first before))
                (not (proof-world-stop between))
                (not (member-equal (proof-world-pc between) cuts))
                (proof-instruction-at-p second (proof-world-pc between) between)
                (proof-instruction-access-p second between)
                (equal after (proof-instruction-effect second between))
                (not (proof-world-stop after))
                (member-equal (proof-world-pc after) cuts))
           (proof-segment-p 2 cuts before :cut after))
  :hints (("Goal"
           :use ((:instance proof-step-from-instruction (world before) (instruction first))
                 (:instance proof-step-from-instruction (world between) (instruction second)))
           :expand ((:free (world) (proof-run 2 cuts world))
                    (:free (world) (proof-run 1 cuts world))
                    (:free (world) (proof-run 0 cuts world)))
           :in-theory (disable proof-step-from-instruction
                               assembly-one-step-to-cutpoint
                               assembly-segment-to-cutpoint assembly-straight-line-run))))
