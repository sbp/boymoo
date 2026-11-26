(in-package "BOYMOO-PROOFS")

(include-book "image-execution")
(include-book "expanded-effects")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-decode proof-execute proof-instruction-effect proof-step
                           boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                           boymoo-model::a64-set-nzcv boymoo-model::a64-exec-arithmetic
                           boymoo-model::a64-pc boymoo-model::a64-unsigned
                           assembly-low assembly-high assembly-power-of-two ash floor mod)))

(local
 (defthm assembly-register-pair-world
   (implies (and (assembly-register-instruction-p first)
                 (assembly-register-instruction-p second)
                 (not (equal (car (proof-world-machine before)) :svc)))
            (equal (assembly-straight-line-effect (list first second) before)
                   (update-nth 0 (assembly-execute-two (list first second) (proof-world-machine before))
                               before)))
   :hints (("Goal"
            :use ((:instance assembly-register-instruction-world-fields (instruction first) (world before)))
            :in-theory (disable assembly-register-instruction-world-fields
                                assembly-register-instruction-p)))))

(local
 (defthm assembly-placed-two-instruction-list
   (implies (and (proof-instructions-at-p instructions address before)
                 (true-listp instructions)
                 (equal (len instructions) 2))
            (and (equal (list (car instructions) (cadr instructions)) instructions)
                 (proof-instruction-at-p (cadr instructions) (+ 4 address) before)))
   :hints (("Goal" :cases ((consp (cdr instructions)) (consp (cddr instructions)))
                   :in-theory (disable proof-instruction-at-p)))
   :rule-classes nil))

(local
 (defthm assembly-valid-instructions-form-a-list
   (implies (assembly-decoded-list-p instructions)
            (true-listp instructions))))

(local
 (defthm assembly-placed-register-pair-world
   (implies (and (proof-instructions-at-p instructions address before)
                 (assembly-decoded-list-p instructions)
                 (equal (len instructions) 2)
                 (assembly-register-instruction-p (car instructions))
                 (assembly-register-instruction-p (cadr instructions))
                 (not (equal (car (proof-world-machine before)) :svc)))
            (and (proof-span-p (+ address 4) 4)
                 (assembly-item-access-p instructions before)
                 (equal (assembly-straight-line-effect instructions before)
                        (update-nth 0 (assembly-execute-two instructions (proof-world-machine before))
                                    before))))
   :hints (("Goal"
            :use (assembly-placed-two-instruction-list
                  (:instance assembly-placed-instruction-span (instruction (cadr instructions))
                             (address (+ address 4)) (world before))
                  (:instance assembly-register-pair-world (first (car instructions)) (second (cadr instructions))))
            :in-theory (disable assembly-register-pair-world assembly-register-instruction-p
                                proof-instructions-at-p proof-instruction-at-p
                                proof-world-machine assembly-decoded-list-p proof-span-p
                                assembly-straight-line-effect assembly-execute-two)))))

(defthm assembly-linked-expansion-machine-effect
  (let* ((items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (offsets (assembly-labels items 0))
         (instructions (assembly-specified-instructions item offset offsets)))
    (implies (and (assembly-image-layout-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base before)
                  (assembly-executable-item-p item offset offsets)
                  (equal (len instructions) 2)
                  (not (equal (car (proof-world-machine before)) :svc))
                  (equal (proof-world-pc before) (+ base offset))
                  (not (proof-world-stop before)))
             (and (proof-span-p (+ base offset 4) 4)
                  (equal (proof-advance 2 before)
                         (update-nth 0 (assembly-execute-two instructions (proof-world-machine before))
                                     before)))))
  :hints (("Goal"
           :use ((:instance assembly-linked-executable-item-instructions (world before))
                 assembly-linked-executable-item-advance
                 (:instance assembly-specified-instruction-shape (pc (assembly-size prefix))
                            (offsets (assembly-labels (append prefix (cons item suffix)) 0)))
                 (:instance assembly-placed-register-pair-world
                            (instructions (assembly-specified-instructions
                                           item (assembly-size prefix)
                                           (assembly-labels (append prefix (cons item suffix)) 0)))
                            (address (+ base (assembly-size prefix)))))
           :in-theory (disable assembly-placed-register-pair-world assembly-image-layout-p
                               assembly-executable-item-p assembly-specified-instructions
                               assembly-label-offset assembly-size assembly-labels assembly-labels-after-prefix
                               proof-linked-image-p proof-advance proof-span-p
                               proof-world-pc proof-world-machine proof-world-stop
                               assembly-execute-two assembly-straight-line-effect assembly-item-access-p
                               proof-instructions-at-p assembly-register-instruction-p assembly-decoded-list-p)))
  :rule-classes nil)

(local
 (defthm assembly-linked-base-page-aligned
   (implies (proof-linked-image-p items entry base world)
            (and (natp base) (equal (mod base 4096) 0)))
   :hints (("Goal"
            :in-theory (disable boymoo-compiler::a64-assemble-image
                                proof-fragments-at-p proof-image-p proof-covered-p)))))

(local
 (defthm assembly-address-expansion-length
   (equal (len (assembly-far-address-instructions rd target offset)) 2)))

(defthm assembly-linked-far-address-effect
  (let* ((item (list :adr-far rd label))
         (items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (offsets (assembly-labels items 0))
         (target (assembly-label-offset label offsets))
         (machine (proof-world-machine before)))
    (implies (and (assembly-image-layout-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base before)
                  (assembly-executable-item-p item offset offsets)
                  (not (equal (car machine) :svc))
                  (equal (proof-world-pc before) (+ base offset))
                  (not (proof-world-stop before)))
             (equal (proof-advance 2 before)
                    (update-nth 0
                                (boymoo-model::a64-write-reg
                                 rd 64 nil (+ base target)
                                 (boymoo-model::a64-set-pc (+ base offset 8) machine))
                                before))))
  :hints (("Goal"
           :use ((:instance assembly-linked-expansion-machine-effect (item (list :adr-far rd label)))
                 (:instance assembly-linked-base-page-aligned
                            (items (append prefix (cons (list :adr-far rd label) suffix))) (world before))
                 (:instance assembly-far-address-effect
                            (machine (proof-world-machine before)) (offset (assembly-size prefix))
                            (target (assembly-label-offset
                                     label (assembly-labels (append prefix (cons (list :adr-far rd label) suffix)) 0)))))
           :in-theory (disable assembly-linked-base-page-aligned assembly-far-address-effect
                               assembly-image-layout-p proof-linked-image-p
                               assembly-far-address-instructions assembly-execute-two
                               assembly-label-offset assembly-labels assembly-size assembly-labels-after-prefix
                               proof-world-machine proof-world-stop proof-advance)))
  :rule-classes nil)

(defun assembly-zero-source-machine (subtract rd immediate machine)
  (let ((next (boymoo-model::a64-set-pc (+ 8 (boymoo-model::a64-pc machine)) machine)))
    (if (and subtract (not (equal rd 31)))
        (boymoo-model::a64-exec-arithmetic 3 64 rd 31 immediate nil next)
      (boymoo-model::a64-set-nzcv
       (assembly-zero-source-nzcv subtract immediate)
       (boymoo-model::a64-write-reg rd 64 nil immediate next)))))

(local
 (defthm assembly-write-to-zero-register
   (equal (boymoo-model::a64-write-reg 31 64 nil value machine) machine)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm assembly-zero-source-expand-and-execute
   (implies (and (booleanp subtract) (unsigned-byte-p 5 rd) (unsigned-byte-p 12 immediate)
                 (< (+ 4 (boymoo-model::a64-pc machine)) (expt 2 64)))
            (equal (assembly-execute-two (assembly-zero-source-instructions subtract rd immediate) machine)
                   (assembly-zero-source-machine subtract rd immediate machine)))
   :hints (("Goal"
            :cases ((equal rd 31) subtract)
            :use (assembly-zero-source-discard-effect assembly-zero-source-subtract-effect
                  (:instance assembly-zero-source-add-effect))
            :in-theory (disable assembly-zero-source-instructions assembly-execute-two
                                assembly-zero-source-discard-effect assembly-zero-source-subtract-effect
                                assembly-zero-source-add-effect)))))

(local
 (defthm assembly-zero-source-instructions-length
   (equal (len (assembly-zero-source-instructions subtract rd immediate)) 2)))

(defthm assembly-linked-zero-source-effect
  (let* ((op (car item))
         (compare (member-eq op '(:cmp :cmn)))
         (subtract (if (member-eq op '(:cmp :subs)) t nil))
         (rd (if compare 31 (cadr item)))
         (immediate (if compare (caddr item) (cadddr item)))
         (items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (offsets (assembly-labels items 0))
         (machine (proof-world-machine before)))
    (implies (and (member-eq op '(:adds :subs :cmp :cmn))
                  (boymoo-compiler::a64-zero-source-p item)
                  (assembly-image-layout-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base before)
                  (assembly-executable-item-p item offset offsets)
                  (not (equal (car machine) :svc))
                  (equal (proof-world-pc before) (+ base offset))
                  (not (proof-world-stop before)))
             (equal (proof-advance 2 before)
                    (update-nth 0 (assembly-zero-source-machine subtract rd immediate machine) before))))
  :hints (("Goal"
           :use (assembly-linked-expansion-machine-effect)
           :in-theory (disable assembly-image-layout-p proof-linked-image-p
                               assembly-zero-source-instructions assembly-execute-two assembly-zero-source-machine
                               assembly-label-offset assembly-labels assembly-size assembly-labels-after-prefix
                               proof-world-stop proof-world-machine proof-advance)))
  :rule-classes nil)
