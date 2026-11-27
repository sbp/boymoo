(in-package "BOYMOO-PROOFS")

(include-book "emission")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-quotient-by-one-instructions*
  '((:arithmetic-imm 3 64 31 1 3)
    (:branch-cond -2340 0)
    (:branch-reg 30 nil)))

(defthm division-quotient-by-one-instructions-are-emitted
  (let* ((items (division-linked-example-items))
         (entry (division-label-offset "rt:z-quotient" items))
         (return (division-label-offset "rt:num-type-return" items))
         (image (boymoo-compiler::a64-bytes items))
         (machine (proof-load-cleared-string image 0
                                             (boymoo-model::a64-state nil 0 0 0 nil))))
    (and (equal (division-decode-instructions 2 entry machine)
                (take 2 *division-quotient-by-one-instructions*))
         (equal (proof-decode-at return machine)
                (nth 2 *division-quotient-by-one-instructions*))))
  :rule-classes nil)

(local
 (in-theory (disable floor mod ash proof-step boymoo-model::a64-unsigned
                     division-a64-unsigned-is-remainder division-mask-is-remainder)))

(local
 (defthm division-return-car-after-update
   (implies (posp index)
            (equal (car (update-nth index datum old)) (car old)))
   :hints (("Goal" :expand ((update-nth index datum old))))))

(local (in-theory (disable proof-instruction-effect)))

(local
 (defthm division-by-one-compare-effect
   (implies (and (equal (proof-world-reg 1 world) (proof-integer-word 1))
                 (not (equal (car (proof-world-machine world)) :svc)))
            (equal (proof-instruction-effect '(:arithmetic-imm 3 64 31 1 3) world)
                   (let ((machine (proof-world-machine world)))
                     (update-nth 0 (boymoo-model::a64-set-nzcv
                                    6 (boymoo-model::a64-set-pc
                                       (+ 4 (boymoo-model::a64-pc machine)) machine))
                                 world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect) :do-not-induct t))))

(local
 (defthm division-by-one-branch-effect
   (implies (and (equal (boymoo-model::a64-nzcv (proof-world-machine world)) 6)
                 (not (equal (car (proof-world-machine world)) :svc)))
            (equal (proof-instruction-effect '(:branch-cond -2340 0) world)
                   (let* ((machine (proof-world-machine world))
                          (next (boymoo-model::a64-set-pc
                                 (+ 4 (boymoo-model::a64-pc machine)) machine)))
                     (update-nth 0 (boymoo-model::a64-set-pc
                                    (- (boymoo-model::a64-pc machine) 2340) next)
                                 world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect) :do-not-induct t))))

(local
 (defthm division-shared-ret-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:branch-reg 30 nil) world)
                   (let* ((machine (proof-world-machine world))
                          (next (boymoo-model::a64-set-pc
                                 (+ 4 (boymoo-model::a64-pc machine)) machine)))
                     (update-nth 0 (boymoo-model::a64-set-pc (proof-world-reg 30 world) next) world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect) :do-not-induct t))))

(local
 (defthm division-return-frame-after-pc
   (let ((after (boymoo-model::a64-set-pc pc machine)))
     (and (equal (car after) (car machine))
          (equal (boymoo-model::a64-registers after) (boymoo-model::a64-registers machine))
          (equal (boymoo-model::a64-sp after) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-pc after) (boymoo-model::a64-unsigned 64 pc))))
   :hints (("Goal" :cases ((consp machine))))))

(local
 (defthm division-return-frame-after-flags
   (let ((after (boymoo-model::a64-set-nzcv 6 machine)))
     (and (equal (car after) (car machine))
          (equal (boymoo-model::a64-registers after) (boymoo-model::a64-registers machine))
          (equal (boymoo-model::a64-sp after) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-nzcv after) 6)))
   :hints (("Goal" :cases ((consp machine))))))

(defthm division-quotient-by-one-effects
  (implies (and (equal (proof-world-reg 1 world) (proof-integer-word 1))
                (not (equal (car (proof-world-machine world)) :svc)))
           (let* ((after (division-instruction-sequence *division-quotient-by-one-instructions* world))
                  (initial (proof-world-machine world))
                  (final (proof-world-machine after)))
             (and (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp final) (boymoo-model::a64-sp initial))
                  (equal (boymoo-model::a64-registers final) (boymoo-model::a64-registers initial))
                  (equal (boymoo-model::a64-memory final) (boymoo-model::a64-memory initial))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                                      boymoo-model::a64-nzcv boymoo-model::a64-pc
                                      boymoo-model::a64-registers boymoo-model::a64-sp
                                      boymoo-model::a64-memory)))
  :rule-classes nil)

(defthm division-quotient-by-one-returns
  (let* ((cuts (list (proof-world-reg 30 world)))
         (after (division-instruction-sequence *division-quotient-by-one-instructions* world)))
    (implies (and (equal (proof-world-reg 1 world) (proof-integer-word 1))
                  (not (equal (car (proof-world-machine world)) :svc))
                  (division-instruction-sequence-ready-p *division-quotient-by-one-instructions*
                                                         cuts world))
             (and (proof-segment-p 3 cuts world :cut after)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world)))))
  :hints (("Goal"
           :use ((:instance division-quotient-by-one-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-quotient-by-one-instructions*)
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-instruction-sequence division-instruction-sequence-ready-p
                               proof-segment-p proof-world-reg)))
  :rule-classes nil)
