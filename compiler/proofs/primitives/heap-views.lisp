(in-package "BOYMOO-PROOFS")

(include-book "contracts")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-object-view proof-object-size proof-static-p
                           proof-object-map-p proof-object-disjoint-p proof-static-spans-p
                           proof-view-value proof-external-objects proof-heap-layout-p
                           proof-heap-object-spans-p proof-string-accounting-p
                           proof-dynamic-symbol-objects-p proof-stack-prefix
                           proof-dynamic-entries proof-dynamic-view)))

(local
 (defthm p6-object-size-is-positive
   (posp (proof-object-size object machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-object-size proof-align-up)))))

(local
 (defthm p6-disjoint-objects-do-not-repeat-address
   (implies (and (integerp address) (posp size)
                 (proof-object-disjoint-p address (+ address size) objects machine))
            (not (assoc-equal address objects)))
   :hints (("Goal" :induct (assoc-equal address objects)
                   :in-theory (enable proof-object-disjoint-p proof-disjoint-p proof-object-address)))))

(defun p6-object-addresses-unique-p (objects)
  (or (atom objects)
      (and (not (assoc-equal (caar objects) (cdr objects)))
           (p6-object-addresses-unique-p (cdr objects)))))

(defthm p6-object-map-has-unique-addresses
  (implies (proof-object-map-p pending objects symbols base packages machine)
           (p6-object-addresses-unique-p pending))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                  :expand ((:free (seen) (proof-object-map-p pending objects seen base packages machine)))
                  :in-theory (e/d ((:induction proof-object-map-p) proof-object-address)
                                  (proof-symbol-object-p p6-disjoint-objects-do-not-repeat-address)))
          ("Subgoal *1/2"
           :use ((:instance p6-disjoint-objects-do-not-repeat-address
                            (address (caar pending)) (size (proof-object-size (car pending) machine))
                            (objects (cdr pending)))))))

(local
 (defthm p6-static-lookup-has-address
   (implies (and (integerp address) (assoc-equal address (proof-static-objects objects)))
            (assoc-equal address objects))
   :hints (("Goal" :induct (proof-static-objects objects)))))

(local
 (defthm p6-static-lookup-agrees-with-full-map
   (implies (and (integerp address) (p6-object-addresses-unique-p objects)
                 (assoc-equal address (proof-static-objects objects)))
            (equal (assoc-equal address (proof-static-objects objects))
                   (assoc-equal address objects)))
   :hints (("Goal" :induct (proof-static-objects objects)))))

(local
 (defthm p6-header-fields-require-both-views
   (and (equal (proof-cons-value nil other) nil)
        (equal (proof-cons-value other nil) nil)
        (equal (proof-symbol-value nil other packages) nil)
        (equal (proof-symbol-value other nil packages) nil)
        (equal (proof-rational-value nil other) nil)
        (equal (proof-rational-value other nil) nil)
        (equal (proof-complex-value nil other) nil)
        (equal (proof-complex-value other nil) nil))))

(local
 (defthm p6-successful-static-view-step-agrees-with-full-map
   (implies (and (p6-object-addresses-unique-p objects)
                 (proof-view-step kind input count depth base (proof-static-objects objects) packages machine))
            (equal (proof-view-step kind input count depth base objects packages machine)
                   (proof-view-step kind input count depth base (proof-static-objects objects) packages machine)))
   :hints (("Goal"
            :induct (proof-view-step kind input count depth base (proof-static-objects objects) packages machine)
            :expand ((:free (mode map) (proof-view-step mode input count depth base map packages machine)))
            :in-theory (e/d ((:induction proof-view-step))
                            (proof-static-objects proof-integer-view proof-cons-value
                             proof-symbol-value proof-rational-value proof-complex-value
                             p6-even-as-mod))))))

(defthm p6-successful-static-view-agrees-with-full-map
  (implies (and (proof-object-map-p objects objects nil base packages machine)
                (proof-view word base (proof-static-objects objects) packages machine))
           (equal (proof-view word base objects packages machine)
                  (proof-view word base (proof-static-objects objects) packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance p6-object-map-has-unique-addresses (pending objects) (symbols nil))
                 (:instance p6-rank-independent-word-view
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base)
                                                           (proof-static-objects objects))))))))
           :expand ((proof-view word base (proof-static-objects objects) packages machine))
           :in-theory (disable proof-static-objects))))

(defthm p6-heap-has-boolean-views
  (implies (proof-heap-p world objects packages)
           (p6-boolean-views-p world objects packages))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-heap-p proof-static-p p6-boolean-views-p
                              proof-machine-value-p proof-value-p)
           :use ((:instance p6-successful-static-view-agrees-with-full-map
                            (word *proof-nil*) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance p6-successful-static-view-agrees-with-full-map
                            (word *proof-t*) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))))))
