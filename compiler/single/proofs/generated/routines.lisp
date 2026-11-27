(in-package "BOYMOO-PROOFS")

(include-book "calls")
(include-book "inlines")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-reg proof-world-pc proof-world-stop proof-world-machine
                    proof-step proof-segment-p proof-runtime-pre-p proof-runtime-entry
                    proof-runtime-return-p proof-datum-return-p proof-frame-return-p
                    proof-register-frame-p proof-heap-p proof-heap-frame-p proof-preserved-heap-p
                    proof-reg-value-p proof-machine-value-p proof-stack-top proof-prefix-preserved-p
                    proof-label-address generated-ordinary-machine-p boymoo-model::a64-unsigned expt))

(defthm generated-link-preserves-register-arguments
  (implies (and (natp register) (<= (+ register (len args)) 30))
           (equal (proof-register-arguments-p args register
                                              (generated-link-to target before) objects packages)
                  (proof-register-arguments-p args register before objects packages)))
  :hints (("Goal" :induct (proof-register-arguments-p args register before objects packages)
                  :in-theory (enable proof-reg-value-p generated-link-to))))

(defthm generated-routine-bl-establishes-entry
  (let* ((pc (proof-world-pc before))
         (entry (proof-runtime-entry name))
         (label (cddr entry))
         (target (proof-label-address label base labels))
         (after (generated-link-to target before)))
    (implies (and entry (true-listp args) (equal (len args) (cadr entry)) (<= (len args) 30)
                  (proof-program-packages-p program packages)
                  (proof-heap-p before objects packages)
                  (proof-register-arguments-p args 0 before objects packages)
                  (unsigned-byte-p 64 target) (< (+ 4 pc) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (not (equal pc target))
                  (generated-linked-item-p (list :bl label) (list :branch (- target pc) t)
                                           pc base labels before))
             (and (proof-segment-p 1 (list target) before :cut after)
                  (proof-runtime-pre-p name args program labels base after objects packages)
                  (equal (proof-world-reg 30 after) (+ 4 pc)))))
  :hints (("Goal"
           :use (:instance generated-branch-with-link-transfer
                           (target (proof-label-address (cddr (proof-runtime-entry name)) base labels))
                           (cuts (list (proof-label-address (cddr (proof-runtime-entry name)) base labels)))
                           (address 0))
           :in-theory (e/d (proof-runtime-pre-p) (proof-register-arguments-p)))))

(defthm generated-routine-returns-to-continuation
  (let* ((pc (proof-world-pc before))
         (entered (generated-link-to target before))
         (result (proof-runtime-value name args program)))
    (implies (and (< (+ 4 pc) (expt 2 64))
                  (proof-runtime-return-p name args program entered after
                                          old-objects new-objects packages))
             (and (equal (proof-world-pc after) (+ 4 pc))
                  (equal (generated-sp after) (generated-sp before))
                  (boymoo-model::core-value-p result)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after old-objects new-objects packages)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages))))
  :hints (("Goal" :in-theory (e/d (proof-runtime-return-p proof-datum-return-p
                                  proof-frame-return-p proof-preserved-heap-p proof-stack-top
                                  proof-prefix-preserved-p generated-link-to generated-heap-machine-sp)
                                 (proof-fixed-heap-p proof-dynamic-table-preserved-p
                                  proof-runtime-value proof-runtime-clobbers
                                  proof-runtime-allocates-p)))))
