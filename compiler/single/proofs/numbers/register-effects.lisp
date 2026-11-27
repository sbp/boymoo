(in-package "BOYMOO-PROOFS")

(include-book "store-traces")

(logic)
(set-verify-guards-eagerness 0)

(defund proof-number-register-only-instruction-p (instruction clobbers)
  (let ((args (cdr instruction)))
    (case (car instruction)
      ((:branch :branch-reg) (or (not (cadr args)) (member-equal 30 clobbers)))
      ((:branch-cond :branch-zero) t)
      ((:multiply :signed-multiply-high)
       (or (equal (car args) 31) (member-equal (car args) clobbers)))
      (:single
       (and (equal (car args) 1)
            (equal (nth 4 args) :offset)
            (or (equal (nth 3 args) 31) (member-equal (nth 3 args) clobbers))))
      (:select
       (and (equal (car args) 64)
            (or (equal (cadr args) 31) (member-equal (cadr args) clobbers))))
      ((:arithmetic-reg :logical-reg :bitfield :move-wide)
       (and (equal (cadr args) 64)
            (or (equal (caddr args) 31) (member-equal (caddr args) clobbers))))
      (:arithmetic-imm
       (and (equal (cadr args) 64)
            (if (equal (caddr args) 31)
                (logbitp 0 (car args))
              (member-equal (caddr args) clobbers))))
      (:logical-imm
       (and (equal (cadr args) 64)
            (if (equal (caddr args) 31)
                (equal (car args) 3)
              (member-equal (caddr args) clobbers))))
      (otherwise nil))))

(defun proof-number-register-only-code-p (instructions clobbers)
  (if (endp instructions)
      t
    (and (proof-number-register-only-instruction-p (car instructions) clobbers)
         (proof-number-register-only-code-p (cdr instructions) clobbers))))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-stop proof-reg
                     proof-execute proof-instruction-effect
                     boymoo-model::a64-state boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-sp boymoo-model::a64-pc boymoo-model::a64-nzcv
                     boymoo-model::a64-memory boymoo-model::a64-shift
                     boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-ones boymoo-model::a64-condition boymoo-model::a64-ror
                     boymoo-model::a64-result-flags
                     (:definition nth) (:definition update-nth)
                     floor ash mod acl2::binary-logior acl2::binary-logand)))

(local
 (defthm car-of-set-pc
   (equal (car (boymoo-model::a64-set-pc pc machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm car-of-set-nzcv
   (equal (car (boymoo-model::a64-set-nzcv flags machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-nzcv)))))

(local
 (defthm put-assoc-is-cons
   (consp (put-assoc-equal key value entries))))

(local
 (defthm car-of-register-write
   (equal (car (boymoo-model::a64-write-reg dest width use-sp word machine))
          (if (and (natp dest) (< dest 31))
              (put-assoc-equal dest (boymoo-model::a64-unsigned width word)
                               (boymoo-model::a64-registers machine))
            (car machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm register-load-keeps-memory-and-sp
   (and (equal (boymoo-model::a64-memory (boymoo-model::a64-write-reg dest width nil value machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-sp (boymoo-model::a64-write-reg dest width nil value machine))
               (boymoo-model::a64-sp machine)))
   :hints (("Goal"
            :in-theory (enable boymoo-model::a64-write-reg boymoo-model::a64-memory boymoo-model::a64-sp)))))

(local
 (defthm register-load-keeps-other-register
   (implies (or (not (equal register dest)) (equal dest 31))
            (equal (proof-reg register (boymoo-model::a64-write-reg dest width nil value machine))
                   (proof-reg register machine)))
   :hints (("Goal"
            :in-theory (enable proof-reg boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                               boymoo-model::a64-registers)))))

(local
 (defthm distinct-register-membership
   (implies (and (member-equal dest clobbers)
                 (not (member-equal register clobbers)))
            (not (equal register dest)))
   :rule-classes nil))

(local
 (defthm register-only-cpu-effects
   (let ((after (proof-execute instruction machine)))
     (implies (and (not (eq (car machine) :svc))
                   (proof-number-register-only-instruction-p instruction clobbers))
              (and (not (eq after :undefined))
                   (not (eq (car after) :svc))
                   (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine))
                   (equal (boymoo-model::a64-sp after) (boymoo-model::a64-sp machine))
                   (implies (not (member-equal register clobbers))
                            (equal (proof-reg register after) (proof-reg register machine))))))
   :hints (("Goal"
            :use ((:instance distinct-register-membership (dest (nth 3 (cdr instruction)))))
            :in-theory (e/d (proof-number-register-only-instruction-p proof-execute
                            (:definition nth))
                           (logbitp))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-register-only-step-effects
  (let* ((machine (proof-world-machine world))
         (after (proof-instruction-effect instruction world))
         (last (proof-world-machine after)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-number-register-only-instruction-p instruction clobbers))
             (and (not (eq (car last) :svc))
                  (equal (cdr after) (cdr world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine))
                  (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp machine))
                  (implies (not (member-equal register clobbers))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance register-only-cpu-effects (machine (proof-world-machine world))))
           :in-theory (enable proof-world-reg)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-register-only-block-effects
  (let* ((machine (proof-world-machine world))
         (after (proof-number-execute-block instructions world))
         (last (proof-world-machine after)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-number-register-only-code-p instructions clobbers))
             (and (not (eq (car last) :svc))
                  (equal (cdr after) (cdr world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine))
                  (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp machine))
                  (implies (not (member-equal register clobbers))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :induct (proof-number-execute-block instructions world))
          ("Subgoal *1/2"
           :use ((:instance proof-number-register-only-step-effects (instruction (car instructions))))))
  :rule-classes nil)

(defthm proof-number-execute-appended-block
  (equal (proof-number-execute-block (append first second) world)
         (proof-number-execute-block second (proof-number-execute-block first world)))
  :hints (("Goal" :induct (proof-number-execute-block first world))))

(defthm proof-number-register-only-block-keeps-register-frame
  (implies (and (not (eq (car (proof-world-machine world)) :svc))
                (proof-number-register-only-code-p instructions clobbers))
           (proof-register-frame-p limit clobbers world (proof-number-execute-block instructions world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit clobbers world
                                           (proof-number-execute-block instructions world))
           :in-theory (disable proof-number-execute-block proof-number-register-only-code-p))
          ("Subgoal *1/3"
           :use ((:instance proof-number-register-only-block-effects (register limit))))
          ("Subgoal *1/2"
           :use ((:instance proof-number-register-only-block-effects (register limit))))
          ("Subgoal *1/1"
           :use ((:instance proof-number-register-only-block-effects (register limit))))))

(defthm proof-number-register-frame-keeps
  (implies (and (natp limit) (natp register) (<= register limit)
                (not (member-equal register clobbers))
                (proof-register-frame-p limit clobbers before after))
           (equal (proof-world-reg register before) (proof-world-reg register after)))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)))
  :rule-classes nil)

(local
 (defthm member-of-subset-is-member
   (implies (and (subsetp-equal left right) (member-equal key left))
            (member-equal key right))
   :hints (("Goal" :induct (subsetp-equal left right)))))

(defthm proof-number-register-frame-allows-more-clobbers
  (implies (and (subsetp-equal clobbers extended)
                (proof-register-frame-p limit clobbers before after))
           (proof-register-frame-p limit extended before after))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)
                  :in-theory (disable subsetp-equal)))
  :rule-classes nil)
