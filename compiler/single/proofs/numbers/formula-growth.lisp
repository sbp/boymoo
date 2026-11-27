(in-package "BOYMOO-PROOFS")

(include-book "formula-heap")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-execute proof-instruction-effect
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-heap-frame-p
                     proof-stack-top proof-machine-limit proof-load-word
                     proof-grow-return-p proof-frame-return-p proof-fixed-heap-p
                     proof-number-formula-growth-trace-p proof-number-formula-grow-instructions
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(local
 (defthm memory-with-one-store
   (equal (boymoo-model::a64-memory (boymoo-model::a64-store bytes address datum machine))
          (boymoo-model::a64-write-bytes bytes address datum (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store boymoo-model::a64-memory)))))

(local
 (defthm formula-prologue-machine-effects
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (ready (proof-number-formula-grow-ready name grow world)))
     (implies (not (eq (car machine) :svc))
              (and (equal (boymoo-model::a64-memory (proof-world-machine ready))
                          (boymoo-model::a64-memory
                           (boymoo-model::a64-store
                            8 (- sp 8) (proof-world-reg 30 world)
                            (boymoo-model::a64-store 8 (- sp 16) (proof-world-reg 19 world) machine))))
                   (implies (not (member-equal register '(8 19 30)))
                            (equal (proof-world-reg register ready) (proof-world-reg register world)))
                   (equal (cdr ready) (cdr world)))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-formula-grow-ready proof-number-formula-grow-instructions
                             proof-number-execute-block proof-world-reg proof-stack-top)
                            (proof-reg boymoo-model::a64-store boymoo-model::a64-read-reg
                             boymoo-model::a64-write-reg boymoo-model::a64-unsigned
                             boymoo-model::a64-set-pc boymoo-model::a64-pc boymoo-model::a64-nzcv
                             boymoo-model::a64-write-bytes (:definition nth) (:definition update-nth)))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm formula-prologue-footprint
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (ready (proof-number-formula-grow-ready name grow world)))
     (implies (and (not (eq (car machine) :svc)) (proof-span-p (- sp 16) 16))
              (proof-number-memory-change-p (- sp 16) sp machine (proof-world-machine ready))))
   :hints (("Goal"
            :use ((:instance formula-prologue-machine-effects (register 23))
                  (:instance proof-number-pair-store-changes-only-footprint
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (machine (proof-world-machine world))
                             (left (proof-world-reg 19 world)) (right (proof-world-reg 30 world)))
                  (:instance proof-number-memory-change-with-same-final-memory
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (first (proof-world-machine world))
                             (last (proof-world-machine (proof-number-formula-grow-ready name grow world)))
                             (other (boymoo-model::a64-store
                                     8 (- (boymoo-model::a64-sp (proof-world-machine world)) 8)
                                     (proof-world-reg 30 world)
                                     (boymoo-model::a64-store
                                      8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      (proof-world-reg 19 world) (proof-world-machine world))))))
            :in-theory (disable proof-number-memory-change-p boymoo-model::a64-store memory-with-one-store)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm formula-prologue-register-frame
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (proof-register-frame-p limit '(8 19 30) world (proof-number-formula-grow-ready name grow world)))
   :hints (("Goal"
            :induct (proof-register-frame-p limit '(8 19 30)
                                            world (proof-number-formula-grow-ready name grow world)))
           ("Subgoal *1/3" :use ((:instance formula-prologue-machine-effects (register limit))))
           ("Subgoal *1/2" :use ((:instance formula-prologue-machine-effects (register limit))))
           ("Subgoal *1/1" :use ((:instance formula-prologue-machine-effects (register limit)))))
   :rule-classes nil))

(defthm proof-number-formula-prologue-preserves-heap
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (ready (proof-number-formula-grow-ready name grow world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-formula-growth-trace-p name grow steps world grown objects new-objects packages))
             (and (proof-preserved-heap-p nil world ready objects objects packages)
                  (equal (proof-machine-limit ready) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine ready)) (- sp 16))
                  (equal (proof-stack-top ready) (proof-stack-top world))
                  (equal (proof-world-reg 19 ready) (proof-stack-top world)))))
  :hints (("Goal"
           :use (proof-number-heap-machine-context formula-prologue-footprint
                 (:instance proof-number-formula-calls-growth (bytes (proof-number-formula-frame-bytes name)))
                 (:instance formula-prologue-machine-effects (register 23))
                 (:instance formula-prologue-machine-effects (register 24))
                 (:instance formula-prologue-machine-effects (register 25))
                 (:instance formula-prologue-machine-effects (register 26))
                 (:instance formula-prologue-machine-effects (register 27))
                 (:instance formula-prologue-machine-effects (register 28))
                 (:instance proof-number-mod-shift-by-multiple
                            (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times -1))
                 (:instance proof-number-machine-save-preserves-heap
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (before world) (after (proof-number-formula-grow-ready name grow world))))
           :in-theory (e/d (proof-number-formula-growth-trace-p proof-number-formula-grow-ready
                            proof-number-heap-registers-and-world-tail-agree-p proof-machine-limit)
                           (proof-span-p proof-number-save-interval-p proof-number-memory-change-p
                            proof-number-formula-grow-instructions boymoo-model::a64-store))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-growth-preserves-heap-and-register-frame
  (let* ((link (proof-world-reg 30 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (clobbers (list* 19 30 (proof-number-numeric-clobbers))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-formula-growth-trace-p name grow steps world grown objects new-objects packages))
             (and (proof-number-exact-prefix-p (+ 4 steps) (list link) world grown)
                  (proof-preserved-heap-p nil world grown objects new-objects packages)
                  (proof-heap-p grown new-objects packages)
                  (proof-number-world-byte-keys-p grown)
                  (proof-register-frame-p 30 clobbers world grown)
                  (equal (proof-machine-limit grown) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine grown)) (- sp 16))
                  (equal (proof-stack-top grown) (proof-stack-top world))
                  (equal (proof-world-reg 19 grown) (proof-stack-top world)))))
  :hints (("Goal"
           :use (proof-number-formula-growth-prefix proof-number-formula-prologue-preserves-heap
                 (:instance formula-prologue-register-frame (limit 30))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (+ 4 steps)) (cuts (list (proof-world-reg 30 world)))
                            (before world) (after grown))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle (proof-number-formula-grow-ready name grow world)) (after grown)
                            (old-objects objects) (middle-objects objects) (objects new-objects))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (after grown)
                            (old-objects objects) (objects new-objects))
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (clobbers (list* 19 30 (proof-number-numeric-clobbers)))
                            (first-clobbers '(8 19 30)) (last-clobbers '(9 10 11 12 24))
                            (before world) (middle (proof-number-formula-grow-ready name grow world))
                            (after grown))
                 (:instance proof-number-register-frame-keeps
                            (limit 30) (register 19) (clobbers '(9 10 11 12 24))
                            (before (proof-number-formula-grow-ready name grow world)) (after grown))
                 (:instance proof-number-register-frame-keeps
                            (limit 30) (register 23) (clobbers '(9 10 11 12 24))
                            (before (proof-number-formula-grow-ready name grow world)) (after grown))
                 (:instance proof-number-register-frame-keeps
                            (limit 30) (register 25) (clobbers '(9 10 11 12 24))
                            (before (proof-number-formula-grow-ready name grow world)) (after grown)))
           :in-theory (e/d (proof-number-formula-growth-trace-p proof-grow-return-p proof-frame-return-p
                            proof-number-numeric-clobbers proof-machine-limit proof-stack-top)
                           (proof-number-formula-grow-instructions proof-register-frame-p proof-span-p
                            proof-grow-limit proof-number-save-interval-p))
           :do-not-induct t))
  :rule-classes nil)
