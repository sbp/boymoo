(in-package "BOYMOO-PROOFS")

(include-book "formula-execution")
(include-book "returns")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-number-execute-block proof-segment-p
                     proof-number-checked-block-p proof-number-cut-free-prefix-p
                     proof-datum-return-p proof-world-machine proof-world-reg proof-world-pc
                     proof-stack-top proof-number-frame-address proof-number-frame-p
                     proof-prefix-preserved-p proof-reg-value-p proof-machine-value-p
                     proof-number-call-domain-p proof-number-call-value
                     proof-number-slot-arguments proof-number-exact-prefix-p)))

; TARGETS maps each callee label to its loaded address. One trace entry
; gives the steps in the callee, its return world and its object map.
(defund proof-number-formula-call-ready (call targets world)
  (let ((target (cdr (assoc-equal (car call) targets))))
    (proof-number-execute-block
     (proof-number-formula-call-instructions (cdr call) (proof-world-pc world) target)
     world)))

(defund proof-number-formula-call-return-p (call slots gcd ready returned objects new-objects packages)
  (let* ((target (car call))
         (args (proof-number-slot-arguments (cdr call) slots))
         (value (proof-number-call-value target args gcd)))
    (and (proof-number-call-domain-p target args gcd)
         (proof-datum-return-p value (append *proof-volatile-registers* '(24 26 27))
                               t t nil ready returned objects new-objects packages))))

(defund proof-number-formula-call-trace-p (call slots gcd start targets link entry world objects packages)
  (let* ((indices (cdr call))
         (target (cdr (assoc-equal (car call) targets)))
         (steps (car entry))
         (returned (cadr entry))
         (new-objects (caddr entry))
         (pc (proof-world-pc world))
         (count (1+ (len indices)))
         (continuation (+ pc (* 4 count)))
         (code (proof-number-formula-call-instructions indices pc target))
         (ready (proof-number-formula-call-ready call targets world)))
    (and (consp indices)
         (or (null (cdr indices))
             (and (consp (cdr indices)) (null (cddr indices))))
         (equal (proof-world-reg 19 world) (proof-number-frame-address start world))
         (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 continuation)
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p code (list target) world)
         (proof-number-checked-block-p code (list link) world)
         (natp steps)
         (proof-segment-p steps (list continuation) ready :cut returned)
         (proof-number-cut-free-prefix-p steps (list continuation link) ready)
         (proof-number-formula-call-return-p call slots gcd ready returned
                                             objects new-objects packages))))

(local
 (defthm length-with-one-more-element
   (equal (len (append elements (list element))) (1+ (len elements)))
   :hints (("Goal" :induct (len elements)))))

(local
 (defthm formula-load-count
   (equal (len (proof-number-formula-load-instructions indices reg)) (len indices))
   :hints (("Goal" :induct (proof-number-formula-load-instructions indices reg)))))

(local
 (defthm formula-linked-call-count
   (equal (len (proof-number-formula-call-instructions indices pc target)) (1+ (len indices)))
   :hints (("Goal" :in-theory (disable proof-number-formula-load-instructions)))))

(defthm proof-number-formula-call-keeps-slot-values
  (let* ((indices (cdr call))
         (args (proof-number-slot-arguments indices slots))
         (value (proof-number-call-value (car call) args gcd))
         (ready (proof-number-formula-call-ready call targets world))
         (returned (cadr entry))
         (new-objects (caddr entry))
         (count (1+ (len indices))))
    (implies (and (proof-number-slot-indices-p indices (len slots))
                  (proof-number-frame-p start slots world objects packages)
                  (proof-number-formula-call-trace-p call slots gcd start targets link
                                                     entry world objects packages))
             (and (proof-number-exact-prefix-p (+ count (car entry)) (list link) world returned)
                  (proof-register-arguments-p args 0 ready objects packages)
                  (proof-number-frame-p start slots returned new-objects packages)
                  (proof-reg-value-p 0 value returned new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-passes-slot-values
                            (indices (cdr call)) (target (cdr (assoc-equal (car call) targets))))
                 (:instance proof-number-frame-across-datum-return
                            (before (proof-number-formula-call-ready call targets world))
                            (after (cadr entry)) (old-objects objects) (new-objects (caddr entry))
                            (datum (proof-number-call-value
                                    (car call) (proof-number-slot-arguments (cdr call) slots) gcd))
                            (clobbers (append *proof-volatile-registers* '(24 26 27)))
                            (changes-flags t) (allocates t) (may-intern nil))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-formula-call-instructions
                                           (cdr call) (proof-world-pc world)
                                           (cdr (assoc-equal (car call) targets))))
                            (cuts (list link)))
                 (:instance proof-number-segment-exact-prefix
                            (count (car entry)) (cuts (list link)) (reason :cut)
                            (local-cuts (list (+ (proof-world-pc world) (* 4 (1+ (len (cdr call)))))))
                            (before (proof-number-formula-call-ready call targets world))
                            (after (cadr entry)))
                 (:instance proof-number-exact-prefix-append
                            (prefix (1+ (len (cdr call)))) (suffix (car entry))
                            (cuts (list link)) (before world)
                            (middle (proof-number-formula-call-ready call targets world))
                            (after (cadr entry))))
           :in-theory (e/d (proof-number-formula-call-trace-p proof-number-formula-call-return-p
                            proof-number-formula-call-ready proof-datum-return-p)
                           (proof-number-formula-call-instructions proof-frame-return-p
                            proof-preserved-heap-p proof-fixed-heap-p
                            proof-register-arguments-p proof-number-slot-indices-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-formula-spill-after (world)
  (proof-number-execute-block *proof-number-formula-spill-instructions* world))

(defund proof-number-formula-spill-trace-p (value link world objects packages)
  (let* ((machine (proof-world-machine world))
         (top (proof-stack-top world))
         (pc (+ 8 (proof-world-pc world)))
         (after (proof-number-formula-spill-after world)))
    (and (not (eq (car machine) :svc))
         (proof-span-p top 8)
         (unsigned-byte-p 64 (+ top 8))
         (unsigned-byte-p 64 pc)
         (proof-number-checked-block-p *proof-number-formula-spill-instructions* (list pc) world)
         (proof-number-checked-block-p *proof-number-formula-spill-instructions* (list link) world)
         (proof-prefix-preserved-p top world after objects objects packages)
         (proof-machine-value-p (proof-world-reg 0 world) value after objects packages))))

(defthm proof-number-formula-spill-keeps-slot-values
  (let ((after (proof-number-formula-spill-after world)))
    (implies (and (proof-number-formula-spill-trace-p value link world objects packages)
                  (proof-number-frame-p start slots world objects packages))
             (and (proof-number-exact-prefix-p 2 (list link) world after)
                  (proof-number-frame-p start (append slots (list value)) after objects packages))))
  :hints (("Goal"
           :use (proof-number-formula-spill-extends-frame
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions *proof-number-formula-spill-instructions*)
                            (cuts (list link))))
           :in-theory (enable proof-number-formula-spill-trace-p proof-number-formula-spill-after)
           :do-not-induct t))
  :rule-classes nil)

(defun proof-number-formula-body-trace-p (calls trace slots gcd start targets link world objects packages)
  (declare (xargs :measure (len calls)))
  (if (endp calls)
      (endp trace)
    (let* ((call (car calls))
           (entry (car trace))
           (returned (cadr entry))
           (new-objects (caddr entry))
           (value (proof-number-call-value (car call)
                                          (proof-number-slot-arguments (cdr call) slots) gcd)))
      (and (consp trace)
           (proof-number-formula-call-trace-p call slots gcd start targets link
                                              entry world objects packages)
           (if (endp (cdr calls))
               (endp (cdr trace))
             (and (proof-number-formula-spill-trace-p value link returned new-objects packages)
                  (proof-number-formula-body-trace-p
                   (cdr calls) (cdr trace) (append slots (list value)) gcd start targets link
                   (proof-number-formula-spill-after returned) new-objects packages)))))))

(defun proof-number-formula-trace-steps (calls trace)
  (if (endp calls)
      0
    (+ 1 (len (cdar calls)) (nfix (caar trace))
       (if (endp (cdr calls))
           0
         (+ 2 (proof-number-formula-trace-steps (cdr calls) (cdr trace)))))))

(local
 (defthm traced-step-count-is-natural
   (natp (proof-number-formula-trace-steps calls trace))
   :rule-classes :type-prescription))

(local
 (defthm call-and-spill-keep-slot-values
   (let* ((value (proof-number-call-value (car call)
                                          (proof-number-slot-arguments (cdr call) slots) gcd))
          (returned (cadr entry))
          (new-objects (caddr entry))
          (after (proof-number-formula-spill-after returned))
          (count (+ 1 (len (cdr call)) (car entry))))
     (implies (and (proof-number-slot-indices-p (cdr call) (len slots))
                   (proof-number-frame-p start slots world objects packages)
                   (proof-number-formula-call-trace-p call slots gcd start targets link
                                                      entry world objects packages)
                   (proof-number-formula-spill-trace-p value link returned new-objects packages))
              (and (proof-number-exact-prefix-p (+ count 2) (list link) world after)
                   (proof-number-frame-p start (append slots (list value)) after new-objects packages))))
   :hints (("Goal"
            :use (proof-number-formula-call-keeps-slot-values
                  (:instance proof-number-formula-spill-keeps-slot-values
                             (value (proof-number-call-value
                                     (car call) (proof-number-slot-arguments (cdr call) slots) gcd))
                             (world (cadr entry)) (objects (caddr entry)))
                  (:instance proof-number-exact-prefix-append
                             (prefix (+ 1 (len (cdr call)) (car entry))) (suffix 2)
                             (cuts (list link)) (before world) (middle (cadr entry))
                             (after (proof-number-formula-spill-after (cadr entry)))))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm traced-call-domain-and-count
   (implies (proof-number-formula-call-trace-p call slots gcd start targets link
                                              entry world objects packages)
            (and (natp (car entry))
                 (proof-number-call-domain-p
                  (car call) (proof-number-slot-arguments (cdr call) slots) gcd)))
   :hints (("Goal" :in-theory (enable proof-number-formula-call-trace-p
                                    proof-number-formula-call-return-p)))
   :rule-classes nil))

(local
 (defthm last-slot-after-append
   (equal (car (last (append slots (list value)))) value)
   :hints (("Goal" :induct (len slots)))))

(defthm proof-number-formula-body-follows-evaluation
  (implies (and (consp calls)
                (proof-number-call-slots-p calls (len slots))
                (proof-number-frame-p start slots world objects packages)
                (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                  world objects packages))
           (mv-let (valid final-slots)
             (proof-number-evaluate-calls calls slots gcd)
             (let* ((entry (car (last trace)))
                    (returned (cadr entry))
                    (new-objects (caddr entry)))
               (and valid
                    (proof-number-exact-prefix-p (proof-number-formula-trace-steps calls trace)
                                                 (list link) world returned)
                    (proof-reg-value-p 0 (car (last final-slots)) returned new-objects packages)))))
  :hints (("Goal"
           :induct (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                     world objects packages)
           :in-theory (disable proof-number-slot-indices-p proof-number-formula-call-instructions))
          ("Subgoal *1/3"
           :use ((:instance traced-call-domain-and-count (call (car calls)) (entry (car trace)))
                 (:instance call-and-spill-keep-slot-values (call (car calls)) (entry (car trace)))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 3 (len (cdar calls)) (caar trace)))
                            (suffix (proof-number-formula-trace-steps (cdr calls) (cdr trace)))
                            (cuts (list link)) (before world)
                            (middle (proof-number-formula-spill-after (cadar trace)))
                            (after (cadar (last trace))))))
          ("Subgoal *1/2"
           :use ((:instance traced-call-domain-and-count (call (car calls)) (entry (car trace)))
                 (:instance proof-number-formula-call-keeps-slot-values
                            (call (car calls)) (entry (car trace))))))
  :rule-classes nil)

(local
 (defthm formula-table-lookup
   (implies (and (proof-number-formula-table-p formulas)
                 (assoc-equal name formulas))
            (let ((row (assoc-equal name formulas)))
              (and (member-equal (cadr row) '(1 2))
                   (consp (caddr row))
                   (proof-number-call-slots-p (caddr row) (cadr row)))))
   :hints (("Goal" :induct (assoc-equal name formulas)
            :in-theory (disable proof-number-call-slots-p)))
   :rule-classes nil))

(local
 (defthm generated-formula-initialized-indices
   (implies (consp (proof-number-formula-calls name))
            (proof-number-call-slots-p (proof-number-formula-calls name)
                                       (proof-number-formula-arity name)))
   :hints (("Goal"
            :use (proof-number-generated-formulas-use-initialized-slots
                  (:instance formula-table-lookup (formulas *proof-number-formulas*)))
            :in-theory (disable proof-number-formula-table-p proof-number-call-slots-p
                                assoc-equal)))
   :rule-classes nil))

(defthm proof-number-formula-body-returns-result
  (let* ((calls (proof-number-formula-calls name))
         (entry (car (last trace)))
         (returned (cadr entry))
         (new-objects (caddr entry))
         (machine (proof-world-machine returned))
         (sp (boymoo-model::a64-sp machine))
         (after (proof-number-execute-block *proof-number-formula-return-instructions* returned)))
    (implies (and (proof-number-formula-result-p name args gcd result)
                  (proof-number-frame-p start args world objects packages)
                  (proof-number-formula-body-trace-p calls trace args gcd start targets link
                                                     world objects packages)
                  (proof-number-checked-block-p *proof-number-formula-return-instructions*
                                               (list link) returned)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 sp))
                  (equal (proof-load-word (+ 8 sp) machine) link))
             (and (proof-segment-p (+ (proof-number-formula-trace-steps calls trace) 3)
                                   (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-stack-top after) (proof-world-reg 19 returned))
                  (equal (proof-world-reg 19 after) (proof-load-word sp machine))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                  (proof-reg-value-p 0 result after new-objects packages))))
  :hints (("Goal"
           :use (generated-formula-initialized-indices
                 (:instance proof-number-formula-body-follows-evaluation
                            (calls (proof-number-formula-calls name)) (slots args))
                 (:instance proof-number-formula-restores-frame
                            (world (cadar (last trace))))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (proof-number-formula-trace-steps
                                     (proof-number-formula-calls name) trace))
                            (suffix 3) (cuts (list link)) (before world)
                            (middle (cadar (last trace))) (reason :cut)
                            (after (proof-number-execute-block
                                    *proof-number-formula-return-instructions* (cadar (last trace)))))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value result) (objects (caddar (last trace)))
                            (before (cadar (last trace))) (word (proof-world-reg 0 (cadar (last trace))))
                            (after (proof-number-execute-block
                                    *proof-number-formula-return-instructions* (cadar (last trace))))))
           :in-theory (e/d (proof-reg-value-p)
                           (proof-heap-base proof-number-formula-calls proof-number-formula-arity
                            proof-number-formula-body-trace-p proof-number-evaluate-calls
                            proof-number-call-slots-p proof-number-formula-trace-steps
                            proof-number-formula-table-p boymoo-model::a64-sp
                            boymoo-model::a64-memory proof-load-word last))
           :do-not-induct t))
  :rule-classes nil)
