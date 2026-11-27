(in-package "BOYMOO-PROOFS")

(include-book "steps")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-run proof-step proof-advance proof-segment-p proof-world-stop
                    proof-world-pc generated-before-cuts-p generated-run-of-clear-prefix))

(defun generated-run-step-count (fuel cuts world)
  (declare (xargs :measure (nfix fuel)))
  (if (or (proof-world-stop world) (member-equal (proof-world-pc world) cuts) (zp fuel))
      0
    (1+ (generated-run-step-count (1- fuel) cuts (proof-step world)))))

(defthm generated-run-step-count-describes-prefix
  (let ((count (generated-run-step-count fuel cuts world)))
    (and (natp count) (<= count (nfix fuel))
         (generated-before-cuts-p count cuts world)
         (equal (proof-advance count world) (mv-nth 1 (proof-run fuel cuts world)))))
  :hints (("Goal" :induct (generated-run-step-count fuel cuts world)
                  :in-theory (enable proof-run proof-advance generated-before-cuts-p))))

(local
 (defthm generated-member-of-cut-subset
   (implies (and (subsetp-equal smaller larger) (member-equal pc smaller))
            (member-equal pc larger))
   :hints (("Goal" :induct (len smaller) :in-theory (enable subsetp-equal)))
   :rule-classes nil))

(defthm generated-clear-prefix-allows-fewer-cuts
  (implies (and (subsetp-equal cuts all-cuts) (generated-before-cuts-p count all-cuts before))
           (generated-before-cuts-p count cuts before))
  :hints (("Goal" :induct (generated-before-cuts-p count all-cuts before)
                  :in-theory (enable generated-before-cuts-p))
          ("Subgoal *1/2" :use (:instance generated-member-of-cut-subset
                                           (smaller cuts) (larger all-cuts) (pc (proof-world-pc before)))))
  :rule-classes nil)

(local
 (defthm generated-terminated-run-agrees-with-extra-fuel
   (implies (and (natp fuel) (natp extra)
                 (not (equal (mv-nth 0 (proof-run fuel cuts before)) :limit)))
            (equal (proof-run (+ fuel extra) cuts before) (proof-run fuel cuts before)))
   :hints (("Goal" :induct (generated-run-step-count fuel cuts before)
                   :in-theory (enable proof-run)))))

(local
 (defthm generated-instruction-budget-with-difference
   (implies (and (natp fuel) (natp more))
            (equal (+ fuel (- fuel) more) more))
   :hints (("Goal" :use (:instance associativity-of-+ (acl2::x fuel) (acl2::y (- fuel)) (acl2::z more))
                   :in-theory (disable associativity-of-+)))))

(local
 (defthm generated-terminated-run-agrees-with-more-fuel
   (implies (and (natp fuel) (natp more) (<= fuel more)
                 (not (equal (mv-nth 0 (proof-run fuel cuts before)) :limit)))
            (equal (proof-run more cuts before) (proof-run fuel cuts before)))
   :hints (("Goal" :use (:instance generated-terminated-run-agrees-with-extra-fuel (extra (- more fuel)))
                   :in-theory (disable generated-terminated-run-agrees-with-extra-fuel)))))

(defthm generated-segment-composes-with-final-segment
  (implies (and (subsetp-equal cuts prefix-cuts)
                (proof-segment-p prefix-steps prefix-cuts before :cut middle)
                (proof-segment-p suffix-steps cuts middle reason after) (not (eq reason :limit)))
           (proof-segment-p (+ (nfix prefix-steps) (nfix suffix-steps)) cuts before reason after))
  :hints (("Goal"
           :use ((:instance generated-run-step-count-describes-prefix
                            (fuel prefix-steps) (cuts prefix-cuts) (world before))
                 (:instance generated-clear-prefix-allows-fewer-cuts
                            (count (generated-run-step-count prefix-steps prefix-cuts before)) (all-cuts prefix-cuts))
                 (:instance generated-prefix-then-segment
                            (prefix (generated-run-step-count prefix-steps prefix-cuts before)) (suffix suffix-steps))
                 (:instance generated-terminated-run-agrees-with-more-fuel
                            (fuel (+ (generated-run-step-count prefix-steps prefix-cuts before) (nfix suffix-steps)))
                            (more (+ (nfix prefix-steps) (nfix suffix-steps)))))
           :in-theory (e/d (proof-segment-p) (generated-terminated-run-agrees-with-more-fuel
                                             generated-run-step-count-describes-prefix))))
  :rule-classes nil)
