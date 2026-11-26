(in-package "BOYMOO-PROOFS")

(include-book "published-writes")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-object-map-p proof-object-disjoint-p proof-object-view proof-object-size
                    proof-object-record-p proof-symbol-object-p proof-span-p proof-subspan-p
                    proof-disjoint-p proof-view proof-load-word proof-static-objects
                    proof-static-spans-p proof-dynamic-symbol-objects-p proof-home-bindings-p
                    proof-static-size proof-static-p proof-dynamic-entries proof-align-up
                    proof-word-tag proof-pointer-address proof-object-word ash mod floor expt
                    generated-ash-down-by-three boymoo-model::a64-unsigned))

(local
 (defthm generated-aligned-size-is-nonnegative
   (<= 0 (proof-align-up size 8))
   :hints (("Goal" :in-theory (enable proof-align-up ceiling floor)))
   :rule-classes :linear))

(defthm generated-object-size-at-least-a-word
  (<= 8 (proof-object-size object machine))
  :hints (("Goal" :in-theory (enable proof-object-size)))
  :rule-classes :linear)

(defthm generated-published-object-has-span-and-view
  (implies (and (proof-object-map-p pending objects symbols base packages machine)
                (member-equal object pending))
           (and (proof-object-record-p object)
                (proof-span-p (proof-object-address object) (proof-object-size object machine))
                (proof-object-view object base objects packages machine)))
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                  :in-theory (enable proof-object-map-p)))
  :rule-classes nil)

(defthm generated-disjoint-object-has-disjoint-span
  (let ((address (proof-object-address object)))
    (implies (and (proof-object-disjoint-p start end objects machine)
                  (member-equal object objects))
             (proof-disjoint-p address (+ address (proof-object-size object machine)) start end)))
  :hints (("Goal" :induct (proof-object-disjoint-p start end objects machine)
                  :in-theory (enable proof-object-disjoint-p proof-disjoint-p)))
  :rule-classes nil)

(defthm generated-object-header-outside-written-span
  (let ((address (proof-object-address object)) (size (proof-object-size object first)))
    (implies (and (proof-span-p address size)
                  (proof-disjoint-p address (+ address size) start end)
                  (generated-memory-outside-p start end first last))
             (and (equal (proof-load-word address last) (proof-load-word address first))
                  (equal (proof-object-size object last) size)
                  (equal (proof-symbol-object-p object last) (proof-symbol-object-p object first)))))
  :hints (("Goal"
           :use (:instance generated-word-outside-written-span
                           (address (proof-object-address object)) (before first) (after last))
           :in-theory (enable proof-span-p proof-disjoint-p proof-object-size proof-symbol-object-p)))
  :rule-classes nil)

(defthm generated-published-object-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (proof-object-map-p objects objects nil base packages first)
                (proof-object-disjoint-p start end objects first)
                (member-equal object objects))
           (and (equal (proof-object-size object last) (proof-object-size object first))
                (equal (proof-symbol-object-p object last) (proof-symbol-object-p object first))
                (equal (proof-object-view object base objects packages last)
                       (proof-object-view object base objects packages first))))
  :hints (("Goal"
           :use ((:instance generated-published-object-has-span-and-view (pending objects) (symbols nil)
                            (machine first))
                 (:instance generated-disjoint-object-has-disjoint-span (machine first))
                 generated-object-header-outside-written-span
                 (:instance generated-published-view-outside-written-span
                            (word (proof-object-word object base))))
           :in-theory (enable proof-object-view)))
  :rule-classes nil)

(defund generated-object-observations-agree-p (pending objects base packages first last)
  (if (atom pending)
      t
    (let ((object (car pending)))
      (and (equal (proof-object-size object last) (proof-object-size object first))
           (equal (proof-symbol-object-p object last) (proof-symbol-object-p object first))
           (equal (proof-object-view object base objects packages last)
                  (proof-object-view object base objects packages first))
           (generated-object-observations-agree-p (cdr pending) objects base packages first last)))))

(defthm generated-object-observations-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (proof-object-map-p objects objects nil base packages first)
                (proof-object-disjoint-p start end objects first)
                (subsetp-equal pending objects))
           (generated-object-observations-agree-p pending objects base packages first last))
  :hints (("Goal" :induct (len pending)
                  :in-theory (enable generated-object-observations-agree-p subsetp-equal))
          ("Subgoal *1/1" :use (:instance generated-published-object-outside-written-span
                                          (object (car pending)))))
  :rule-classes nil)

(local
 (defthm generated-object-observations-preserve-disjointness
   (implies (generated-object-observations-agree-p pending objects base packages first last)
            (equal (proof-object-disjoint-p address end pending last)
                   (proof-object-disjoint-p address end pending first)))
   :hints (("Goal" :induct (len pending)
                   :in-theory (enable generated-object-observations-agree-p proof-object-disjoint-p)))
   :rule-classes nil))

(local
 (defun generated-object-map-induction (pending objects symbols base packages first)
   (if (atom pending)
       symbols
     (generated-object-map-induction
      (cdr pending) objects
      (if (proof-symbol-object-p (car pending) first)
          (cons (proof-view-value (proof-object-view (car pending) base objects packages first)) symbols)
        symbols)
      base packages first))))

(local
 (defthm generated-object-observations-preserve-map
   (implies (generated-object-observations-agree-p pending objects base packages first last)
            (equal (proof-object-map-p pending objects symbols base packages last)
                   (proof-object-map-p pending objects symbols base packages first)))
   :hints (("Goal"
            :induct (generated-object-map-induction pending objects symbols base packages first)
            :in-theory (enable generated-object-observations-agree-p))
           ("Subgoal *1/2"
            :use (:instance generated-object-observations-preserve-disjointness
                            (pending (cdr pending)) (address (proof-object-address (car pending)))
                            (end (+ (proof-object-address (car pending))
                                    (proof-object-size (car pending) first))))
            :expand ((proof-object-map-p pending objects symbols base packages first)
                     (proof-object-map-p pending objects symbols base packages last)))
           ("Subgoal *1/1" :in-theory (enable proof-object-map-p)))
   :rule-classes nil))

(local
 (defthm generated-subsetp-cons-superset
   (implies (subsetp-equal left right)
            (subsetp-equal left (cons entry right)))
   :hints (("Goal" :induct (len left) :in-theory (enable subsetp-equal)))))

(defthm generated-subsetp-equal-reflexive
  (subsetp-equal objects objects)
  :hints (("Goal" :induct (len objects) :in-theory (enable subsetp-equal))))

(defthm generated-object-map-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (proof-object-map-p objects objects nil base packages first)
                (proof-object-disjoint-p start end objects first))
           (proof-object-map-p objects objects nil base packages last))
  :hints (("Goal"
           :use ((:instance generated-object-observations-outside-written-span (pending objects))
                 (:instance generated-object-observations-preserve-map (pending objects) (symbols nil)))))
  :rule-classes nil)

(defthm generated-object-disjointness-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (proof-object-map-p objects objects nil base packages first)
                (proof-object-disjoint-p start end objects first))
           (proof-object-disjoint-p start end objects last))
  :hints (("Goal"
           :use ((:instance generated-object-observations-outside-written-span (pending objects))
                 (:instance generated-object-observations-preserve-disjointness
                            (pending objects) (address start)))))
  :rule-classes nil)

(defthm generated-published-view-unchanged-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (proof-object-map-p objects objects nil base packages first)
                (proof-object-disjoint-p start end objects first))
           (equal (proof-view word base objects packages last)
                  (proof-view word base objects packages first)))
  :hints (("Goal"
           :use (generated-published-view-outside-written-span
                 generated-object-map-outside-written-span
                 generated-object-disjointness-outside-written-span
                 generated-memory-outside-symmetric
                 (:instance generated-published-view-outside-written-span (first last) (last first)))))
  :rule-classes nil)

(defthm generated-object-observations-preserve-dynamic-symbols
  (implies (generated-object-observations-agree-p pending objects base packages first last)
           (equal (proof-dynamic-symbol-objects-p pending objects entries base packages last)
                  (proof-dynamic-symbol-objects-p pending objects entries base packages first)))
  :hints (("Goal" :induct (len pending)
                  :in-theory (enable generated-object-observations-agree-p proof-dynamic-symbol-objects-p)))
  :rule-classes nil)

(defthm generated-object-observations-preserve-static-spans
  (implies (generated-object-observations-agree-p pending objects base packages first last)
           (equal (proof-static-spans-p pending base size last)
                  (proof-static-spans-p pending base size first)))
  :hints (("Goal" :induct (len pending)
                  :in-theory (enable generated-object-observations-agree-p proof-static-spans-p)))
  :rule-classes nil)
