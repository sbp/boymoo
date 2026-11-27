(in-package "BOYMOO-PROOFS")

(include-book "formula-contracts")
(include-book "stack-storage")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-stack-top proof-stack-limit proof-stack-end proof-stack-prefix
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-object-map-p
                     proof-reg-value-p proof-register-arguments-p proof-datum-return-p
                     proof-number-formula-call-trace-p proof-number-formula-call-return-p
                     proof-number-value-append-pre-p proof-number-formula-argument-trace-p
                     proof-number-formula-spill-trace-p proof-number-formula-result-p
                     proof-number-formula-contract-trace-p proof-number-formula-trace-after
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-formula-store-site-p (arity link world)
  (let* ((top (proof-stack-top world))
         (end (+ top (* 8 arity)))
         (pc (+ 8 (proof-world-pc world)))
         (code (proof-number-formula-argument-store-instructions arity)))
    (and (not (eq (car (proof-world-machine world)) :svc))
         (posp top) (unsigned-byte-p 64 end) (<= end (proof-stack-limit world))
         (unsigned-byte-p 64 pc)
         (proof-number-checked-block-p code (list pc) world)
         (proof-number-checked-block-p code (list link) world))))

(defun proof-number-formula-body-checked-trace-p (calls trace slots gcd start targets link world objects packages)
  (declare (xargs :measure (len calls)))
  (if (endp calls)
      (endp trace)
    (let* ((call (car calls))
           (entry (car trace))
           (returned (cadr entry))
           (new-objects (caddr entry))
           (value (proof-number-call-value (car call) (proof-number-slot-arguments (cdr call) slots) gcd)))
      (and (consp trace)
           (proof-number-formula-call-trace-p call slots gcd start targets link entry world objects packages)
           (if (endp (cdr calls))
               (endp (cdr trace))
             (and (proof-number-formula-store-site-p 1 link returned)
                  (proof-number-formula-body-checked-trace-p
                   (cdr calls) (cdr trace) (append slots (list value)) gcd start targets link
                   (proof-number-formula-spill-after returned) new-objects packages)))))))

(local
 (defthm value-stack-limit-is-within-reservation
   (implies (proof-heap-p world objects packages)
            (<= (proof-stack-limit world) (proof-stack-end world)))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
            :in-theory (disable proof-static-p proof-external-objects proof-dynamic-entries
                                proof-dynamic-view proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                                proof-string-accounting-p proof-align-up proof-runtime-word
                                proof-covered-p proof-regions-p proof-disjoint-p proof-page-size-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm formula-call-trace-gives-heap-and-result
   (let* ((value (proof-number-call-value (car call) (proof-number-slot-arguments (cdr call) slots) gcd))
          (returned (cadr entry))
          (new-objects (caddr entry)))
     (implies (proof-number-formula-call-trace-p call slots gcd start targets link entry world objects packages)
              (and (proof-heap-p returned new-objects packages)
                   (proof-reg-value-p 0 value returned new-objects packages))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-formula-call-trace-p proof-number-formula-call-return-p
                             proof-datum-return-p proof-preserved-heap-p)
                            (proof-number-formula-call-ready proof-number-formula-call-instructions
                             proof-number-call-value proof-number-call-domain-p proof-number-slot-arguments
                             proof-frame-return-p proof-heap-frame-p proof-prefix-preserved-p
                             proof-dynamic-table-preserved-p assoc-equal))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-checked-formula-body-trace-supplies-stores
  (implies (proof-number-formula-body-checked-trace-p calls trace slots gcd start targets link world objects packages)
           (and (proof-number-formula-body-trace-p calls trace slots gcd start targets link world objects packages)
                (proof-number-formula-spill-storage-p calls trace packages)
                (proof-number-formula-spills-in-value-stack-p calls trace)))
  :hints (("Goal"
           :induct (proof-number-formula-body-checked-trace-p calls trace slots gcd start targets link world objects packages)
           :in-theory (disable proof-number-call-value proof-number-slot-arguments proof-number-formula-spill-after))
          ("Subgoal *1/3"
           :use ((:instance formula-call-trace-gives-heap-and-result (call (car calls)) (entry (car trace)))
                 (:instance value-stack-limit-is-within-reservation (world (cadar trace)) (objects (caddar trace)))
                 (:instance proof-number-checked-spill-store-from-heap
                            (world (cadar trace)) (objects (caddar trace))
                            (value (proof-number-call-value (caar calls)
                                                           (proof-number-slot-arguments (cdar calls) slots) gcd))))
           :in-theory (enable proof-number-formula-store-site-p proof-number-formula-argument-store-instructions)))
  :rule-classes nil)

(defund proof-number-formula-checked-trace-p
    (name args gcd grow growth-steps targets trace world grown objects grown-objects packages)
  (let* ((link (proof-world-reg 30 world))
         (ready (proof-number-formula-grow-ready name grow world))
         (start (len (cdr (proof-stack-prefix (proof-stack-top grown) grown grown-objects packages))))
         (calls (proof-number-formula-calls name))
         (body (proof-number-formula-arguments-after args grown))
         (returned (cadar (last trace)))
         (machine (proof-world-machine returned)))
    (and (natp growth-steps)
         (consp calls)
         (proof-number-formula-growth-trace-p name grow growth-steps world grown objects grown-objects packages)
         (proof-number-machine-save-fits-p ready)
         (proof-number-argument-list-p args)
         (proof-register-arguments-p args 0 grown grown-objects packages)
         (proof-number-formula-store-site-p (len args) link grown)
         (proof-number-formula-body-checked-trace-p calls trace args gcd start targets link body grown-objects packages)
         (proof-number-checked-block-p *proof-number-formula-return-instructions* (list link) returned)
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp machine))))))

(defthm proof-number-checked-formula-trace-supplies-store-effects
  (implies (and (proof-heap-p world objects packages)
                (proof-number-world-byte-keys-p world)
                (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16) world objects)
                (proof-number-formula-checked-trace-p
                 name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
           (proof-number-formula-contract-trace-p
            name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
  :hints (("Goal"
           :use ((:instance proof-number-formula-growth-preserves-heap-and-register-frame
                            (steps growth-steps) (new-objects grown-objects))
                 (:instance value-stack-limit-is-within-reservation (world grown) (objects grown-objects))
                 (:instance proof-number-checked-argument-store-from-heap
                            (world grown) (objects grown-objects) (link (proof-world-reg 30 world)))
                 (:instance proof-number-checked-formula-body-trace-supplies-stores
                            (calls (proof-number-formula-calls name)) (slots args)
                            (start (len (cdr (proof-stack-prefix (proof-stack-top grown) grown grown-objects packages))))
                            (link (proof-world-reg 30 world)) (objects grown-objects)
                            (world (proof-number-formula-arguments-after args grown))))
           :in-theory (e/d (proof-number-formula-checked-trace-p proof-number-formula-contract-trace-p
                            proof-number-formula-return-trace-p proof-number-formula-store-site-p)
                           (proof-number-formula-body-checked-trace-p proof-number-formula-body-trace-p
                            proof-number-formula-spill-storage-p proof-number-formula-spills-in-value-stack-p
                            proof-number-formula-argument-store-instructions last))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-generated-formula-return-from-checked-stores
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (saved (- sp 16))
         (count (proof-number-formula-contract-steps name growth-steps trace))
         (after (proof-number-formula-trace-after trace))
         (new-objects (caddar (last trace))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (posp saved)
                  (<= (- (proof-machine-limit world) *proof-machine-margin*) saved)
                  (proof-span-p saved 16)
                  (proof-number-formula-result-p name args gcd result)
                  (proof-number-formula-checked-trace-p
                   name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
             (and (proof-segment-p count (list (proof-world-reg 30 world)) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-heap-gives-machine-save-locality
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16)))
                 proof-number-checked-formula-trace-supplies-store-effects
                 proof-number-generated-formula-datum-return)
           :in-theory (disable proof-machine-limit proof-span-p proof-number-save-interval-p last)
           :do-not-induct t))
  :rule-classes nil)
