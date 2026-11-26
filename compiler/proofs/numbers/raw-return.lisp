(in-package "BOYMOO-PROOFS")

(include-book "numeric-comparisons")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-reg-value-p
                     proof-machine-value-p proof-datum-return-p proof-number-order
                     proof-number-binary-types-p
                     boymoo-model::a64-memory
                     proof-number-integer-parity mod floor ash)))

(local
 (defthm datum-result-register
   (implies (proof-datum-return-p datum clobbers changes-flags allocates may-intern
                                  before after old-objects objects packages)
            (proof-reg-value-p 0 datum after objects packages))
   :hints (("Goal"
            :in-theory (e/d (proof-datum-return-p)
                            (proof-frame-return-p proof-preserved-heap-p proof-fixed-heap-p))))))

(defthm proof-number-positive-inversion-returns-through-box
  (let* ((path (proof-number-invert-path a zero negative box world))
         (ready (proof-number-execute-block path world))
         (link (proof-world-reg 30 world))
         (count (+ (len path) box-steps)))
    (implies (and (posp a) (proof-number-reduced-p a b)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-checked-block-p path (list box) world)
                  (proof-number-checked-block-p path (list link) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 56 (proof-world-pc world)))
                  (unsigned-byte-p 64 box)
                  (natp box-steps)
                  (proof-segment-p box-steps (list link) ready :cut after)
                  (proof-datum-return-p (/ b a) (proof-number-numeric-clobbers) t t nil
                                        ready after objects new-objects packages))
             (and (proof-number-reduced-p b a)
                  (proof-register-arguments-p (list b a) 0 ready objects packages)
                  (proof-segment-p count (list link) world :cut after)
                  (proof-reg-value-p 0 (/ (/ a b)) after new-objects packages))))
  :hints (("Goal"
           :use (proof-number-positive-inversion-passes-reduced-parts
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-invert-path a zero negative box world))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (len (proof-number-invert-path a zero negative box world)))
                            (suffix box-steps) (cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-execute-block
                                     (proof-number-invert-path a zero negative box world) world)))
                 (:instance datum-result-register
                            (datum (/ b a)) (clobbers (proof-number-numeric-clobbers))
                            (changes-flags t) (allocates t) (may-intern nil)
                            (before (proof-number-execute-block
                                     (proof-number-invert-path a zero negative box world) world))
                            (old-objects objects) (objects new-objects)))
           :in-theory (disable proof-number-reduced-p datum-result-register)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-rational-compare-path (addresses world)
  (let ((row (assoc-equal "rt:q-compare" *proof-number-dispatch-rows*)))
    (proof-number-dispatch-path (cadr row) (caddr row) (proof-world-pc world) addresses world)))

(defund proof-number-rational-compare-ready (addresses world)
  (proof-number-execute-block (proof-number-rational-compare-path addresses world) world))

(defund proof-number-rational-compare-target (a b)
  (if (and (integerp (fix a)) (integerp (fix b))) "rt:z-compare" "rt:q-compare-products"))

(defund proof-number-rational-compare-dispatch-trace-p (a b addresses cuts world)
  (let* ((machine (proof-world-machine world))
         (path (proof-number-rational-compare-path addresses world))
         (target (cdr (assoc-equal (proof-number-rational-compare-target a b) addresses))))
    (and (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p path (list target) world)
         (proof-number-checked-block-p path cuts world))))

(defthm proof-number-rational-comparison-passes-operands
  (let* ((path (proof-number-rational-compare-path addresses world))
         (ready (proof-number-rational-compare-ready addresses world))
         (target (cdr (assoc-equal (proof-number-rational-compare-target a b) addresses))))
    (implies (and (not (complex-rationalp a)) (not (complex-rationalp b))
                  (proof-number-binary-types-p a b world objects packages)
                  (proof-number-rational-compare-dispatch-trace-p a b addresses cuts world))
             (and (proof-number-exact-prefix-p (len path) cuts world ready)
                  (proof-segment-p (len path) (list target) world :cut ready)
                  (equal (proof-world-pc ready) target)
                  (equal (proof-world-reg 30 ready) (proof-world-reg 30 world))
                  (rationalp (fix a)) (rationalp (fix b))
                  (proof-register-arguments-p (list (fix a) (fix b)) 0 ready objects packages))))
  :hints (("Goal"
           :use (proof-number-rational-comparison-dispatch-by-value
                 (:instance proof-number-dispatch-reaches-selected-label (name "rt:q-compare") (register 28))
                 (:instance proof-number-dispatch-reaches-selected-label (name "rt:q-compare") (register 30))
                 (:instance proof-number-dispatch-reaches-selected-label (name "rt:q-compare") (register 0))
                 (:instance proof-number-dispatch-reaches-selected-label (name "rt:q-compare") (register 1))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-rational-compare-path addresses world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value (fix a)) (word (proof-world-reg 0 world))
                            (before world) (after (proof-number-rational-compare-ready addresses world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 1) (value (fix b)) (word (proof-world-reg 1 world))
                            (before world) (after (proof-number-rational-compare-ready addresses world))))
           :in-theory (enable proof-number-rational-compare-path proof-number-rational-compare-target
                              proof-number-rational-compare-ready proof-number-rational-compare-dispatch-trace-p
                              proof-number-binary-types-p proof-heap-base proof-reg-value-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-rational-comparison-returns-through-callee
  (let* ((link (proof-world-reg 30 world))
         (completed (proof-number-binary-types-call-after types classifier world))
         (dispatched (proof-number-pop-link-after completed))
         (ready (proof-number-rational-compare-ready addresses dispatched))
         (count (+ 3
                   (proof-number-types-completion-steps nil classifier (proof-number-types-first-ready types world))
                   (len (proof-number-rational-compare-path addresses dispatched))
                   callee-steps))
         (order (proof-number-order (fix a) (fix b))))
    (implies (and (not (complex-rationalp a)) (not (complex-rationalp b))
                  (proof-number-binary-types-call-trace-p types classifier (list link) a b
                                                         world objects packages)
                  (proof-number-pop-link-trace-p (list link) completed)
                  (proof-number-rational-compare-dispatch-trace-p a b addresses (list link) dispatched)
                  (natp callee-steps)
                  (proof-segment-p callee-steps (list link) ready :cut after)
                  (proof-datum-return-p order (proof-number-numeric-clobbers) t t nil
                                        ready after objects new-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-reg-value-p 0 order after new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-binary-wrapper-reaches-dispatch
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-rational-comparison-passes-operands
                            (cuts (list (proof-world-reg 30 world)))
                            (world (proof-number-pop-link-after
                                    (proof-number-binary-types-call-after types classifier world))))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 3 (proof-number-types-completion-steps
                                          nil classifier (proof-number-types-first-ready types world))))
                            (suffix (len (proof-number-rational-compare-path
                                          addresses (proof-number-pop-link-after
                                                     (proof-number-binary-types-call-after types classifier world)))))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-pop-link-after
                                     (proof-number-binary-types-call-after types classifier world)))
                            (after (proof-number-rational-compare-ready addresses
                                    (proof-number-pop-link-after
                                     (proof-number-binary-types-call-after types classifier world)))))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (+ 3 (proof-number-types-completion-steps
                                          nil classifier (proof-number-types-first-ready types world))
                                       (len (proof-number-rational-compare-path
                                             addresses (proof-number-pop-link-after
                                                        (proof-number-binary-types-call-after types classifier world))))))
                            (suffix callee-steps) (before world)
                            (middle (proof-number-rational-compare-ready addresses
                                     (proof-number-pop-link-after
                                      (proof-number-binary-types-call-after types classifier world))))
                            (cuts (list (proof-world-reg 30 world))) (reason :cut))
                 (:instance datum-result-register
                            (datum (proof-number-order (fix a) (fix b)))
                            (clobbers (proof-number-numeric-clobbers))
                            (changes-flags t) (allocates t) (may-intern nil)
                            (before (proof-number-rational-compare-ready addresses
                                     (proof-number-pop-link-after
                                      (proof-number-binary-types-call-after types classifier world))))
                            (old-objects objects) (objects new-objects)))
           :in-theory (disable datum-result-register fix proof-register-arguments-p)
           :do-not-induct t))
  :rule-classes nil)
