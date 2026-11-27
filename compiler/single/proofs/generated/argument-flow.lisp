(in-package "BOYMOO-PROOFS")

(include-book "stack-write")
(include-book "prefix-suffix")
(include-book "segments")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-stack-base proof-stack-top proof-stack-limit proof-heap-base proof-stack-prefix
                    proof-stack-views proof-prefix-preserved-p proof-reg-value-p proof-segment-p
                    generated-stack-views-are-word-views generated-stack-views-of-one-slot
                    generated-sp generated-path-after generated-path-p expt))

(defund generated-same-stack-frame-p (before after)
  (and (equal (proof-stack-base after) (proof-stack-base before))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
       (equal (generated-sp after) (generated-sp before))))

(defthm generated-prepending-a-cut-keeps-the-subset
  (implies (subsetp-equal cuts all-cuts)
           (subsetp-equal cuts (cons cut all-cuts)))
  :hints (("Goal" :induct (len cuts) :in-theory (enable subsetp-equal))))

(defund generated-nontail-value-result-p (datum continuation before after old-objects new-objects packages)
  (and (equal (proof-world-pc after) continuation)
       (proof-heap-p after new-objects packages)
       (generated-same-stack-frame-p before after)
       (equal (proof-stack-top after) (proof-stack-top before))
       (proof-prefix-preserved-p (proof-stack-top before) before after old-objects new-objects packages)
       (proof-reg-value-p 0 datum after new-objects packages)))

(defund generated-arguments-result-p (args before after old-objects new-objects packages)
  (let ((start (proof-stack-top before)))
    (and (true-listp args)
         (proof-heap-p after new-objects packages)
         (generated-same-stack-frame-p before after)
         (equal (proof-stack-top after) (+ start (* 8 (len args))))
         (proof-prefix-preserved-p start before after old-objects new-objects packages)
         (equal (proof-stack-views (len args) start (proof-heap-base after) new-objects packages
                                  (proof-world-machine after))
                (cons :slots (proof-argument-views args))))))

(defthm generated-no-arguments-preserve-the-frame
  (implies (proof-heap-p world objects packages)
           (generated-arguments-result-p nil world world objects objects packages))
  :hints (("Goal"
           :use generated-heap-has-layout-and-roots
           :expand (:free (start base machine) (proof-stack-views 0 start base objects packages machine))
           :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-argument-views-of-appended-values
  (equal (proof-argument-views (append first rest))
         (append (proof-argument-views first) (proof-argument-views rest)))
  :hints (("Goal" :induct (len first) :in-theory (enable proof-argument-views))))

(defthm generated-argument-stages-compose
  (implies (and (generated-arguments-result-p first-args before middle old-objects middle-objects packages)
                (generated-arguments-result-p rest-args middle after middle-objects new-objects packages))
           (generated-arguments-result-p (append first-args rest-args)
                                         before after old-objects new-objects packages))
  :hints (("Goal"
           :use ((:instance generated-stack-prefix-has-aligned-slot-count
                            (top (proof-stack-top before)) (world before) (objects old-objects))
                 (:instance generated-preserved-prefix-preserves-aligned-suffix
                            (before middle) (old-objects middle-objects)
                            (start (proof-stack-top before)) (top (proof-stack-top middle))
                            (left (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (count (len first-args)))
                 (:instance generated-stack-views-split
                            (first (len first-args)) (rest (len rest-args))
                            (address (proof-stack-top before)) (base (proof-heap-base after))
                            (objects new-objects) (machine (proof-world-machine after)))
                 (:instance generated-prefix-preserved-at-smaller-top
                            (before middle) (old-objects middle-objects)
                            (top (proof-stack-top before)) (retained (proof-stack-top middle))
                            (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3)))
                 (:instance generated-prefix-preserved-transitive (top (proof-stack-top before))
                            (first before) (last after) (first-objects old-objects) (last-objects new-objects)))
           :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p
                              proof-prefix-preserved-p generated-ash-down-by-three)))
  :rule-classes nil)

(defthm generated-push-provides-argument-stage
  (let* ((after (generated-path-after *generated-push-path* before))
         (end (+ (proof-world-pc before) 8)))
    (implies (and (proof-heap-p before objects packages) (proof-reg-value-p 0 datum before objects packages)
                  (<= (+ (proof-stack-top before) 8) (proof-stack-limit before)) (< end (expt 2 64))
                  (generated-ordinary-machine-p before)
                  (member-equal end cuts) (generated-path-p *generated-push-path* cuts before))
             (and (proof-segment-p 2 cuts before :cut after)
                  (equal (proof-world-pc after) end)
                  (generated-arguments-result-p (list datum) before after objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-stack-prefix-has-aligned-slot-count
                            (world before) (top (proof-stack-top before)))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path *generated-push-path*) (all-cuts cuts) (cuts (list (+ (proof-world-pc before) 8))))
                 (:instance generated-push-preserves-heap-and-appends-value
                            (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3)))
                 (:instance generated-heap-has-layout-and-roots
                            (world (generated-path-after *generated-push-path* before)))
                 (:instance generated-heap-layout-value-stack-bounds
                            (world (generated-path-after *generated-push-path* before)))
                 (:instance generated-placed-path-to-cut (instructions *generated-push-path*)))
           :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p
                              generated-ash-down-by-three)))
  :rule-classes nil)

(defthm generated-evaluated-operand-and-push-compose
  (let* ((push-end (+ operand-end 8))
         (after (generated-path-after *generated-push-path* evaluated)))
    (implies (and (generated-nontail-value-result-p datum operand-end before evaluated old-objects objects packages)
                  (proof-segment-p operand-steps (cons operand-end cuts) before :cut evaluated)
                  (<= (+ (proof-stack-top evaluated) 8) (proof-stack-limit evaluated))
                  (< push-end (expt 2 64)) (generated-ordinary-machine-p evaluated)
                  (member-equal push-end cuts) (generated-path-p *generated-push-path* cuts evaluated))
             (and (proof-segment-p (+ (nfix operand-steps) 2) cuts before :cut after)
                  (equal (proof-world-pc after) push-end)
                  (generated-arguments-result-p (list datum) before after old-objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-push-provides-argument-stage (before evaluated))
                 (:instance generated-segment-composes-with-final-segment
                            (prefix-steps operand-steps) (suffix-steps 2) (prefix-cuts (cons operand-end cuts))
                            (middle evaluated) (reason :cut)
                            (after (generated-path-after *generated-push-path* evaluated)))
                 (:instance generated-prefix-preserved-transitive (top (proof-stack-top before))
                            (first before) (middle evaluated) (last (generated-path-after *generated-push-path* evaluated))
                            (first-objects old-objects) (middle-objects objects) (last-objects objects)))
           :in-theory (enable generated-nontail-value-result-p generated-arguments-result-p
                              generated-same-stack-frame-p proof-reg-value-p)))
  :rule-classes nil)
