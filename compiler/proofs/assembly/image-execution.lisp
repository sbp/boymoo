(in-package "BOYMOO-PROOFS")

(include-book "image-decoding")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-decode proof-decode-at proof-step
                           proof-execute proof-instruction-effect
                           proof-instruction-access-p proof-instruction-at-p
                           proof-world-machine proof-world-pc proof-world-stop
                           boymoo-model::a64-unsigned assembly-low
                           assembly-register-instruction-p assembly-register-instruction-world-effect)))

(defthm assembly-covered-span-p
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :hints (("Goal" :induct (proof-covered-p address size access regions)
                  :in-theory (disable proof-region-allows-p proof-span-p)))
  :rule-classes nil)

(defthm assembly-placed-instruction-span
  (implies (proof-instruction-at-p instruction address world)
           (proof-span-p address 4))
  :hints (("Goal"
           :use ((:instance assembly-covered-span-p
                            (size 4) (access :execute) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-instruction-at-p)
                           (proof-covered-p proof-span-p))))
  :rule-classes nil)

(local
 (defthm assembly-pair-advance
   (let ((between (proof-instruction-effect first before)))
     (implies (and (assembly-register-instruction-p first)
                   (assembly-register-instruction-p second)
                   (not (eq (car (proof-world-machine before)) :svc))
                   (proof-instructions-at-p (list first second) address before)
                   (equal (proof-world-pc before) address)
                   (not (proof-world-stop before)))
              (and (equal (proof-step before) between)
                   (not (proof-world-stop between))
                   (equal (proof-world-pc between) (+ address 4))
                   (equal (proof-step between) (proof-instruction-effect second between)))))
   :hints (("Goal"
            :use ((:instance assembly-placed-instruction-span (instruction second)
                             (address (+ address 4)) (world before))
                  (:instance assembly-register-instruction-world-fields
                             (instruction first) (world before))
                  (:instance assembly-register-effect-keeps-instructions-placed
                             (instruction first) (placed second)
                             (address (+ address 4)) (world before))
                  (:instance proof-step-from-instruction (instruction first) (world before))
                  (:instance proof-step-from-instruction (instruction second)
                             (world (proof-instruction-effect first before))))
            :in-theory (e/d (assembly-a64-unsigned-is-low)
                            (assembly-register-instruction-world-fields
                             assembly-register-effect-keeps-instructions-placed
                             proof-step-from-instruction
                             proof-covered-p))))
   :rule-classes nil))

(local
 (defthm assembly-one-or-two-instructions
   (implies (true-listp instructions)
            (and (implies (equal (len instructions) 1)
                          (equal instructions (list (car instructions))))
                 (implies (equal (len instructions) 2)
                          (equal instructions (list (car instructions) (cadr instructions))))))
   :hints (("Goal" :cases ((consp (cdr instructions)) (consp (cddr instructions)))))
   :rule-classes nil))

(local
 (defthm assembly-decoded-instructions-are-a-true-list
   (implies (assembly-decoded-list-p instructions)
            (true-listp instructions))))

(defun assembly-item-access-p (instructions world)
  (and (proof-instruction-access-p (car instructions) world)
       (or (atom (cdr instructions))
           (not (eq (car (proof-world-machine world)) :svc)))))

(local
 (defthm assembly-small-advance-counts
   (and (equal (proof-advance 1 world) (proof-step world))
        (equal (proof-advance 2 world) (proof-step (proof-step world))))
   :hints (("Goal" :expand ((:free (before) (proof-advance 0 before))
                            (:free (before) (proof-advance 1 before))
                            (proof-advance 2 world))))))

(local
 (defthm assembly-placed-item-steps
   (implies (and (assembly-decoded-list-p instructions)
                 (or (equal (len instructions) 1)
                     (and (equal (len instructions) 2)
                          (assembly-register-instruction-p (car instructions))
                          (assembly-register-instruction-p (cadr instructions))))
                 (assembly-item-access-p instructions before)
                 (proof-instructions-at-p instructions address before)
                 (equal (proof-world-pc before) address)
                 (not (proof-world-stop before)))
            (let ((between (proof-instruction-effect (car instructions) before)))
              (and (equal (proof-step before) between)
                   (implies (equal (len instructions) 2)
                            (and (not (proof-world-stop between))
                                 (equal (proof-world-pc between) (+ address 4))
                                 (equal (proof-step between)
                                        (proof-instruction-effect (cadr instructions) between))))
                   (equal (proof-advance (len instructions) before)
                          (assembly-straight-line-effect instructions before)))))
   :hints (("Goal"
            :use (assembly-one-or-two-instructions
                  (:instance assembly-pair-advance
                             (first (car instructions)) (second (cadr instructions)))
                  (:instance proof-step-from-instruction
                             (instruction (car instructions)) (world before)))
            :in-theory (disable proof-step-from-instruction assembly-decoded-list-p)))
   :rule-classes nil))

(local
 (defthm assembly-clear-prefix-of-one
   (equal (assembly-clear-prefix-p 1 cuts world)
          (and (not (proof-world-stop world))
               (not (member-equal (proof-world-pc world) cuts))))
   :hints (("Goal" :expand ((assembly-clear-prefix-p 1 cuts world)
                            (:free (before) (assembly-clear-prefix-p 0 cuts before)))))))

(defthm assembly-placed-item-to-cutpoint
  (let ((after (assembly-straight-line-effect instructions before)))
    (implies (and (assembly-decoded-list-p instructions)
                  (or (equal (len instructions) 1)
                      (and (equal (len instructions) 2)
                           (assembly-register-instruction-p (car instructions))
                           (assembly-register-instruction-p (cadr instructions))))
                  (assembly-item-access-p instructions before)
                  (proof-instructions-at-p instructions address before)
                  (equal (proof-world-pc before) address)
                  (not (proof-world-stop before))
                  (not (member-equal address cuts))
                  (implies (equal (len instructions) 2)
                           (not (member-equal (+ address 4) cuts)))
                  (not (proof-world-stop after))
                  (member-equal (proof-world-pc after) cuts))
             (proof-segment-p (len instructions) cuts before :cut after)))
  :hints (("Goal"
           :use (assembly-placed-item-steps
                 (:instance assembly-segment-to-cutpoint
                            (count (len instructions))
                            (after (assembly-straight-line-effect instructions before))))
           :in-theory (disable assembly-segment-to-cutpoint
                               assembly-straight-line-effect proof-segment-p proof-run
                               assembly-item-access-p proof-instructions-at-p
                               assembly-decoded-list-p member-equal)))
  :rule-classes nil)

(local (in-theory (disable assembly-image-layout-p proof-linked-image-p assembly-executable-item-p
                           assembly-labels assembly-labels-after-prefix assembly-size
                           assembly-specified-instructions assembly-decoded-list-p
                           assembly-item-access-p proof-instructions-at-p
                           assembly-straight-line-effect)))

(defthm assembly-linked-executable-item-advance
  (let* ((items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (offsets (assembly-labels items 0))
         (instructions (assembly-specified-instructions item offset offsets)))
    (implies (and (assembly-image-layout-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base before)
                  (assembly-executable-item-p item offset offsets)
                  (assembly-item-access-p instructions before)
                  (equal (proof-world-pc before) (+ base offset))
                  (not (proof-world-stop before)))
             (equal (proof-advance (len instructions) before)
                    (assembly-straight-line-effect instructions before))))
  :hints (("Goal"
           :use ((:instance assembly-linked-executable-item-instructions (world before))
                 (:instance assembly-specified-instruction-shape
                            (pc (assembly-size prefix))
                            (offsets (assembly-labels (append prefix (cons item suffix)) 0)))
                 (:instance assembly-placed-item-steps
                            (instructions (assembly-specified-instructions
                                           item (assembly-size prefix)
                                           (assembly-labels (append prefix (cons item suffix)) 0)))
                            (address (+ base (assembly-size prefix)))))))
  :rule-classes nil)

(defthm assembly-linked-executable-item-to-cutpoint
  (let* ((items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (address (+ base offset))
         (offsets (assembly-labels items 0))
         (instructions (assembly-specified-instructions item offset offsets))
         (after (assembly-straight-line-effect instructions before)))
    (implies (and (assembly-image-layout-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base before)
                  (assembly-executable-item-p item offset offsets)
                  (assembly-item-access-p instructions before)
                  (equal (proof-world-pc before) address)
                  (not (proof-world-stop before))
                  (not (member-equal address cuts))
                  (implies (equal (len instructions) 2)
                           (not (member-equal (+ address 4) cuts)))
                  (not (proof-world-stop after))
                  (member-equal (proof-world-pc after) cuts))
             (proof-segment-p (len instructions) cuts before :cut after)))
  :hints (("Goal"
           :use ((:instance assembly-linked-executable-item-instructions (world before))
                 (:instance assembly-specified-instruction-shape
                            (pc (assembly-size prefix))
                            (offsets (assembly-labels (append prefix (cons item suffix)) 0)))
                 (:instance assembly-placed-item-to-cutpoint
                            (instructions (assembly-specified-instructions
                                           item (assembly-size prefix)
                                           (assembly-labels (append prefix (cons item suffix)) 0)))
                            (address (+ base (assembly-size prefix)))))
           :in-theory (disable proof-segment-p)))
  :rule-classes nil)

; A discarded MOVZ on a machine whose register file is the atom :svc gives a
; machine whose first element is :svc. The step takes it as a machine, not
; as a system call, because it tests the instruction.
(defthm assembly-malformed-register-file-is-no-system-call
  (let* ((instruction '(:move-wide 2 64 31 0 0))
         (machine (boymoo-model::a64-state :svc 0 0 0 nil))
         (world (proof-world machine nil 4096 nil nil nil nil nil)))
    (and (equal (boymoo-model::a64-pc (proof-execute instruction machine)) 4)
         (equal (car (proof-execute instruction machine)) :svc)
         (equal (proof-world-stop (proof-instruction-effect instruction world)) nil)))
  :hints (("Goal" :in-theory (enable proof-execute proof-instruction-effect proof-world-stop)))
  :rule-classes nil)
