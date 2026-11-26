(in-package "BOYMOO-PROOFS")

(include-book "segments")
(include-book "registers")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-stop proof-step proof-run proof-segment-p generated-sp
                    generated-before-cuts-p proof-advance))

(defun generated-frame-key (world)
  (cons (proof-world-pc world) (generated-sp world)))

(defund generated-frame-run (fuel cuts world)
  (declare (xargs :measure (nfix fuel)))
  (cond ((proof-world-stop world) (mv (proof-world-stop world) world))
        ((member-equal (generated-frame-key world) cuts) (mv :cut world))
        ((zp fuel) (mv :limit world))
        (t (generated-frame-run (1- fuel) cuts (proof-step world)))))

(defund generated-frame-segment-p (fuel cuts before reason after)
  (mv-let (why reached)
    (generated-frame-run fuel cuts before)
    (and (equal why reason) (equal reached after))))

(defun generated-before-frame-cuts-p (count cuts world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (not (proof-world-stop world))
         (not (member-equal (generated-frame-key world) cuts))
         (generated-before-frame-cuts-p (1- count) cuts (proof-step world)))))

(defthm generated-frame-run-reaches-after-clear-prefix
  (implies (generated-before-frame-cuts-p prefix cuts before)
           (equal (generated-frame-run (+ (nfix prefix) (nfix suffix)) cuts before)
                  (generated-frame-run suffix cuts (proof-advance prefix before))))
  :hints (("Goal" :induct (generated-before-frame-cuts-p prefix cuts before)
                  :in-theory (enable generated-frame-run proof-advance))))

(defthm generated-frame-prefix-and-segment-compose
  (implies (and (generated-before-frame-cuts-p prefix cuts before)
                (equal middle (proof-advance prefix before))
                (generated-frame-segment-p suffix cuts middle reason after))
           (generated-frame-segment-p (+ (nfix prefix) (nfix suffix)) cuts before reason after))
  :hints (("Goal" :use generated-frame-run-reaches-after-clear-prefix
                  :in-theory (e/d (generated-frame-segment-p) (generated-frame-run-reaches-after-clear-prefix))))
  :rule-classes nil)

(defthm generated-frame-cut-at-exact-instruction-count
  (let ((after (proof-advance count before)))
    (implies (and (generated-before-frame-cuts-p count cuts before)
                  (not (proof-world-stop after)) (member-equal (generated-frame-key after) cuts))
             (generated-frame-segment-p count cuts before :cut after)))
  :hints (("Goal" :use (:instance generated-frame-run-reaches-after-clear-prefix (prefix count) (suffix 0))
                  :in-theory (e/d (generated-frame-segment-p generated-frame-run)
                                  (generated-frame-run-reaches-after-clear-prefix))))
  :rule-classes nil)

(local
 (defthm generated-member-frame-key-has-pc-in-cuts
   (implies (member-equal (cons pc sp) frames) (member-equal pc (strip-cars frames)))
   :hints (("Goal" :induct (len frames)))))

(local
 (defthm generated-member-of-address-cut-superset
   (implies (and (subsetp-equal small large) (member-equal pc small)) (member-equal pc large))
   :hints (("Goal" :induct (len small)))))

(defthm generated-clear-address-prefix-is-clear-of-frame-cuts
  (implies (and (subsetp-equal (strip-cars frames) cuts) (generated-before-cuts-p count cuts before))
           (generated-before-frame-cuts-p count frames before))
  :hints (("Goal" :induct (generated-before-cuts-p count cuts before)
                  :in-theory (enable generated-before-cuts-p))
          ("Subgoal *1/2"
           :use (:instance generated-member-of-address-cut-superset
                           (small (strip-cars frames)) (large cuts) (pc (proof-world-pc before)))))
  :rule-classes nil)

(defthm generated-address-segment-gives-correct-frame-cut
  (implies (and (proof-segment-p fuel cuts before :cut after) (not (proof-world-stop after))
                (subsetp-equal (strip-cars frames) cuts) (member-equal (generated-frame-key after) frames))
           (generated-frame-segment-p (generated-run-step-count fuel cuts before) frames before :cut after))
  :hints (("Goal"
           :use ((:instance generated-run-step-count-describes-prefix (world before))
                 (:instance generated-clear-address-prefix-is-clear-of-frame-cuts (count (generated-run-step-count fuel cuts before)))
                 (:instance generated-frame-cut-at-exact-instruction-count
                            (count (generated-run-step-count fuel cuts before)) (cuts frames)))
           :in-theory (e/d (proof-segment-p) (generated-run-step-count-describes-prefix))))
  :rule-classes nil)

(defthm generated-address-prefix-composes-with-frame-segment
  (let ((count (generated-run-step-count prefix-steps address-cuts before)))
    (implies (and (proof-segment-p prefix-steps address-cuts before :cut middle)
                  (subsetp-equal (strip-cars frames) address-cuts)
                  (generated-frame-segment-p frame-steps frames middle reason after))
             (generated-frame-segment-p (+ count (nfix frame-steps)) frames before reason after)))
  :hints (("Goal"
           :use ((:instance generated-run-step-count-describes-prefix (fuel prefix-steps) (cuts address-cuts) (world before))
                 (:instance generated-clear-address-prefix-is-clear-of-frame-cuts
                            (count (generated-run-step-count prefix-steps address-cuts before)) (cuts address-cuts))
                 (:instance generated-frame-prefix-and-segment-compose
                            (prefix (generated-run-step-count prefix-steps address-cuts before)) (suffix frame-steps) (cuts frames)))
           :in-theory (e/d (proof-segment-p) (generated-run-step-count-describes-prefix))))
  :rule-classes nil)

(defun generated-frame-run-step-count (fuel cuts world)
  (declare (xargs :measure (nfix fuel)))
  (if (or (proof-world-stop world) (member-equal (generated-frame-key world) cuts) (zp fuel))
      0
    (1+ (generated-frame-run-step-count (1- fuel) cuts (proof-step world)))))

(defthm generated-frame-step-count-describes-prefix
  (let ((count (generated-frame-run-step-count fuel cuts world)))
    (and (natp count) (<= count (nfix fuel))
         (generated-before-frame-cuts-p count cuts world)
         (equal (proof-advance count world) (mv-nth 1 (generated-frame-run fuel cuts world)))))
  :hints (("Goal" :induct (generated-frame-run-step-count fuel cuts world)
                  :in-theory (enable generated-frame-run proof-advance))))

(local
 (defthm generated-frame-prefix-allows-fewer-frame-cuts
   (implies (and (subsetp-equal cuts all-cuts) (generated-before-frame-cuts-p count all-cuts before))
            (generated-before-frame-cuts-p count cuts before))
   :hints (("Goal" :induct (generated-before-frame-cuts-p count all-cuts before))
           ("Subgoal *1/2" :use (:instance generated-member-of-address-cut-superset
                                           (small cuts) (large all-cuts) (pc (generated-frame-key before)))))
   :rule-classes nil))

(local
 (defthm generated-frame-completed-run-allows-extra-steps
   (implies (and (natp fuel) (natp extra) (not (equal (mv-nth 0 (generated-frame-run fuel cuts before)) :limit)))
            (equal (generated-frame-run (+ fuel extra) cuts before) (generated-frame-run fuel cuts before)))
   :hints (("Goal" :induct (generated-frame-run-step-count fuel cuts before) :in-theory (enable generated-frame-run)))))

(defthm generated-frame-segments-compose-under-step-budgets
  (implies (and (subsetp-equal cuts prefix-cuts)
                (generated-frame-segment-p prefix-steps prefix-cuts before :cut middle)
                (generated-frame-segment-p suffix-steps cuts middle reason after) (not (eq reason :limit)))
           (generated-frame-segment-p (+ (nfix prefix-steps) (nfix suffix-steps)) cuts before reason after))
  :hints (("Goal"
           :use ((:instance generated-frame-step-count-describes-prefix (fuel prefix-steps) (cuts prefix-cuts) (world before))
                 (:instance generated-frame-prefix-allows-fewer-frame-cuts
                            (count (generated-frame-run-step-count prefix-steps prefix-cuts before)) (all-cuts prefix-cuts))
                 (:instance generated-frame-prefix-and-segment-compose
                            (prefix (generated-frame-run-step-count prefix-steps prefix-cuts before)) (suffix suffix-steps))
                 (:instance generated-frame-completed-run-allows-extra-steps
                            (fuel (+ (generated-frame-run-step-count prefix-steps prefix-cuts before) (nfix suffix-steps)))
                            (extra (- (nfix prefix-steps) (generated-frame-run-step-count prefix-steps prefix-cuts before)))))
           :in-theory (e/d (generated-frame-segment-p) (generated-frame-step-count-describes-prefix
                                                       generated-frame-completed-run-allows-extra-steps))))
  :rule-classes nil)
