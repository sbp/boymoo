(in-package "BOYMOO-PROOFS")

(include-book "frame-composition")
(include-book "register-effects")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-run proof-step proof-segment-p proof-heap-p proof-preserved-heap-p
                     proof-number-execute-block
                     boymoo-model::a64-sp boymoo-model::a64-memory)))

(defthm proof-number-register-frames-compose
  (implies (and (proof-register-frame-p limit clobbers before middle)
                (proof-register-frame-p limit clobbers middle after))
           (proof-register-frame-p limit clobbers before after))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before middle)))
  :rule-classes nil)

(defthm proof-number-register-frame-can-keep-restored-register
  (implies (and (proof-register-frame-p limit (cons register clobbers) before after)
                (equal (proof-world-reg register before) (proof-world-reg register after)))
           (proof-register-frame-p limit clobbers before after))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)
                  :expand ((proof-register-frame-p limit (cons register clobbers) before after))))
  :rule-classes nil)

(local
 (defthm world-tail-keeps-streams-and-region-list
   (implies (equal (cdr before) (cdr after))
            (and (proof-streams-preserved-p before after)
                 (equal (proof-world-page-size before) (proof-world-page-size after))
                 (equal (proof-world-regions before) (proof-world-regions after))))
   :hints (("Goal" :cases ((consp before) (consp after))))
   :rule-classes nil))

(local
 (defthm protected-heap-registers
   (implies (and (not (member-equal 23 clobbers)) (not (member-equal 24 clobbers))
                 (not (member-equal 25 clobbers)) (not (member-equal 26 clobbers))
                 (not (member-equal 27 clobbers)) (not (member-equal 28 clobbers))
                 (proof-register-frame-p 30 clobbers before after))
            (and (equal (proof-world-reg 23 before) (proof-world-reg 23 after))
                 (equal (proof-world-reg 24 before) (proof-world-reg 24 after))
                 (equal (proof-world-reg 25 before) (proof-world-reg 25 after))
                 (equal (proof-world-reg 26 before) (proof-world-reg 26 after))
                 (equal (proof-world-reg 27 before) (proof-world-reg 27 after))
                 (equal (proof-world-reg 28 before) (proof-world-reg 28 after))))
   :hints (("Goal"
            :use ((:instance proof-number-register-frame-keeps (limit 30) (register 23))
                  (:instance proof-number-register-frame-keeps (limit 30) (register 24))
                  (:instance proof-number-register-frame-keeps (limit 30) (register 25))
                  (:instance proof-number-register-frame-keeps (limit 30) (register 26))
                  (:instance proof-number-register-frame-keeps (limit 30) (register 27))
                  (:instance proof-number-register-frame-keeps (limit 30) (register 28)))
            :in-theory (disable proof-register-frame-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-register-only-execution-preserves-heap
  (let ((after (proof-number-execute-block instructions world)))
    (implies (and (not (eq (car (proof-world-machine world)) :svc))
                  (proof-number-register-only-code-p instructions clobbers)
                  (not (member-equal 23 clobbers)) (not (member-equal 24 clobbers))
                  (not (member-equal 25 clobbers)) (not (member-equal 26 clobbers))
                  (not (member-equal 27 clobbers)) (not (member-equal 28 clobbers))
                  (proof-heap-p world objects packages))
             (and (proof-register-frame-p 30 clobbers world after)
                  (proof-preserved-heap-p nil world after objects objects packages)
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance proof-number-register-only-block-keeps-register-frame (limit 30))
                 (:instance proof-number-register-only-block-effects (register 23))
                 (:instance protected-heap-registers
                            (before world) (after (proof-number-execute-block instructions world)))
                 (:instance world-tail-keeps-streams-and-region-list
                            (before world) (after (proof-number-execute-block instructions world)))
                 (:instance proof-number-same-state-preserves-heap
                            (before world) (after (proof-number-execute-block instructions world))))
           :in-theory (e/d (proof-number-same-heap-state-p)
                           (proof-register-frame-p proof-number-register-only-block-keeps-register-frame
                            proof-streams-preserved-p proof-world-page-size proof-world-regions))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-segment-preserves-byte-keys
  (implies (and (proof-segment-p count cuts before reason after)
                (proof-number-world-byte-keys-p before))
           (proof-number-world-byte-keys-p after))
  :hints (("Goal"
           :use ((:instance proof-number-run-preserves-byte-keys (world before)))
           :in-theory (e/d (proof-segment-p) (proof-number-run-preserves-byte-keys))))
  :rule-classes nil)

(defthm proof-number-exact-prefix-preserves-byte-keys
  (implies (and (proof-number-exact-prefix-p count cuts before after)
                (proof-number-world-byte-keys-p before))
           (proof-number-world-byte-keys-p after))
  :hints (("Goal"
           :use ((:instance proof-number-advance-preserves-byte-keys (world before)))
           :in-theory (e/d (proof-number-exact-prefix-p)
                           (proof-number-advance-preserves-byte-keys proof-advance))))
  :rule-classes nil)
