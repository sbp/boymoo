(in-package "BOYMOO-PROOFS")

(include-book "argument-flow")
(include-book "routines")
(include-book "growth")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-runtime-pre-p proof-runtime-return-p proof-runtime-entry proof-runtime-value
                    proof-datum-return-p proof-frame-return-p proof-register-frame-p proof-heap-frame-p
                    proof-preserved-heap-p proof-register-arguments-p proof-heap-p proof-label-address
                    proof-stack-base proof-stack-top proof-prefix-preserved-p proof-reg-value-p
                    proof-world-machine proof-world-pc proof-world-stop proof-world-reg proof-segment-p
                    generated-link-to generated-path-after generated-sp boymoo-model::a64-unsigned expt))

(local
 (defthm generated-runtime-clobbers-exclude-frame-and-top
   (and (not (member-equal 19 (proof-runtime-clobbers name)))
        (not (member-equal 25 (proof-runtime-clobbers name))))
   :hints (("Goal" :in-theory (enable proof-runtime-clobbers)))))

(local
 (defthm generated-returning-runtime-keeps-argument-stack-frame
   (implies (proof-runtime-return-p name args program entry after old-objects new-objects packages)
            (and (generated-same-stack-frame-p entry after)
                 (equal (proof-stack-top after) (proof-stack-top entry))
                 (proof-heap-p after new-objects packages)))
   :hints (("Goal"
            :use ((:instance generated-register-in-preserved-frame (register 19) (last 30) (before entry)
                             (clobbers (proof-runtime-clobbers name)))
                  (:instance generated-register-in-preserved-frame (register 25) (last 30) (before entry)
                             (clobbers (proof-runtime-clobbers name))))
            :in-theory (e/d (proof-runtime-return-p proof-datum-return-p proof-frame-return-p
                                                    proof-heap-frame-p proof-preserved-heap-p
                                                    generated-same-stack-frame-p generated-heap-machine-sp proof-stack-top)
                            (proof-runtime-clobbers proof-fixed-heap-p proof-dynamic-table-preserved-p
                             proof-runtime-allocates-p))))
   :rule-classes nil))

(defthm generated-runtime-return-provides-nontail-value
  (let* ((entry (generated-link-to target before))
         (result (proof-runtime-value name args program))
         (continuation (+ (proof-world-pc before) 4)))
    (implies (and (< continuation (expt 2 64))
                  (proof-runtime-return-p name args program entry after old-objects new-objects packages))
             (and (boymoo-model::core-value-p result)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                     before after old-objects new-objects packages))))
  :hints (("Goal"
           :use (generated-routine-returns-to-continuation
                 (:instance generated-returning-runtime-keeps-argument-stack-frame
                            (entry (generated-link-to target before))))
           :in-theory (enable generated-nontail-value-result-p generated-same-stack-frame-p generated-link-to)))
  :rule-classes nil)

(defthm generated-linked-runtime-call-and-return-compose
  (let* ((pc (proof-world-pc before)) (definition (proof-runtime-entry name))
         (label (cddr definition)) (target (proof-label-address label base labels))
         (entered (generated-link-to target before))
         (result (proof-runtime-value name args program))
         (continuation (+ pc 4)))
    (implies (and definition (true-listp args) (equal (len args) (cadr definition)) (<= (len args) 30)
                  (proof-program-packages-p program packages)
                  (proof-heap-p before old-objects packages)
                  (proof-register-arguments-p args 0 before old-objects packages)
                  (unsigned-byte-p 64 target) (< continuation (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (not (equal pc target)) (not (member-equal pc cuts)) (member-equal continuation cuts)
                  (generated-linked-item-p (list :bl label) (list :branch (- target pc) t) pc base labels before)
                  (proof-segment-p routine-steps cuts entered :cut after)
                  (proof-runtime-return-p name args program entered after old-objects new-objects packages))
             (and (proof-segment-p (+ 1 (nfix routine-steps)) cuts before :cut after)
                  (proof-runtime-pre-p name args program labels base entered old-objects packages)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                     before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-routine-bl-establishes-entry (objects old-objects))
                 (:instance generated-runtime-return-provides-nontail-value
                            (target (proof-label-address (cddr (proof-runtime-entry name)) base labels)))
                 (:instance generated-branch-with-link-transfer (address 0)
                            (target (proof-label-address (cddr (proof-runtime-entry name)) base labels))
                            (cuts (cons (proof-label-address (cddr (proof-runtime-entry name)) base labels) cuts)))
                 (:instance generated-segment-composes-with-final-segment (prefix-steps 1) (suffix-steps routine-steps)
                            (prefix-cuts (cons (proof-label-address (cddr (proof-runtime-entry name)) base labels) cuts))
                            (middle (generated-link-to
                                     (proof-label-address (cddr (proof-runtime-entry name)) base labels) before))
                            (reason :cut)))
           :in-theory (disable generated-routine-bl-establishes-entry)))
  :rule-classes nil)
