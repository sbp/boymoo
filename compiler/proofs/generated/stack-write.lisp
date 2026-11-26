(in-package "BOYMOO-PROOFS")

(include-book "heap-disjoint")
(include-book "stack-prefix")
(include-book "operand-stack")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-world-machine proof-world-stop proof-world-reg
                    proof-heap-base proof-stack-base proof-stack-top proof-stack-limit proof-stack-end
                    proof-stack-prefix proof-stack-views proof-prefix-preserved-p proof-reg-value-p
                    proof-machine-value-p proof-load-word proof-view proof-span-p proof-subspan-p proof-disjoint-p
                    proof-object-map-p proof-object-disjoint-p proof-segment-p proof-instruction-effect
                    generated-load-word generated-store-word generated-path-after generated-path-p
                    generated-stack-views-are-word-views boymoo-model::a64-unsigned expt mod))

(defthm generated-stack-views-outside-written-span
  (implies (and (generated-word-block-span-p address count)
                (proof-disjoint-p address (+ address (* 8 count)) start end)
                (generated-memory-outside-p start end first last)
                (proof-object-map-p objects objects nil base packages first)
                (proof-object-disjoint-p start end objects first))
           (equal (proof-stack-views count address base objects packages last)
                  (proof-stack-views count address base objects packages first)))
  :hints (("Goal" :induct (generated-read-words count address first)
                  :in-theory (enable proof-stack-views (:induction generated-read-words)))
          ("Subgoal *1/2"
           :use ((:instance generated-word-outside-written-span (before first) (after last))
                 (:instance generated-published-view-unchanged-outside-written-span
                            (word (proof-load-word address first))))
           :in-theory (enable proof-stack-views proof-span-p proof-disjoint-p)))
  :rule-classes nil)

(defthm generated-heap-has-layout-and-roots
  (implies (proof-heap-p world objects packages)
           (and (proof-heap-layout-p world)
                (proof-stack-prefix (proof-stack-top world) world objects packages)
                (proof-object-map-p objects objects nil (proof-heap-base world) packages
                                    (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable proof-heap-p)))
  :rule-classes nil)

(defthm generated-heap-layout-value-stack-bounds
  (let ((lower (proof-stack-base world)) (top (proof-stack-top world))
        (limit (proof-stack-limit world)) (upper (proof-stack-end world)))
    (implies (proof-heap-layout-p world)
             (and (not (proof-world-stop world))
                  (<= lower top) (<= top limit) (<= limit upper)
                  (equal (mod lower 8) 0) (equal (mod top 8) 0) (equal (mod limit 8) 0)
                  (proof-span-p lower (- upper lower)))))
  :hints (("Goal"
           :use (:instance generated-covered-memory-has-bounded-span
                           (address (proof-stack-base world)) (size *proof-value-reservation*)
                           (regions (proof-world-regions world)) (access :write))
           :in-theory (enable proof-heap-layout-p)))
  :rule-classes nil)

(defthm generated-heap-layout-machine-stack-bounds
  (let ((lower (generated-machine-stack-base world)) (upper (generated-machine-stack-end world))
        (sp (generated-sp world)))
    (implies (proof-heap-layout-p world)
             (and (<= lower sp) (<= sp upper) (equal (mod sp 16) 0)
                  (proof-span-p lower (- upper lower)))))
  :hints (("Goal"
           :use (:instance generated-covered-memory-has-bounded-span
                           (address (generated-machine-stack-base world)) (size *proof-machine-reservation*)
                           (regions (proof-world-regions world)) (access :write))
           :in-theory (enable proof-heap-layout-p generated-heap-machine-sp
                              generated-machine-stack-base generated-machine-stack-end)))
  :rule-classes nil)

(local
 (defthm generated-stack-limit-is-bounded-word
   (unsigned-byte-p 64 (proof-stack-limit world))
   :hints (("Goal" :in-theory (enable proof-stack-limit)))
   :rule-classes nil))

(local
 (defthm generated-push-word-outcome
   (let* ((top (proof-stack-top before)) (pc (proof-world-pc before))
          (stored (generated-store-word top (proof-world-reg 0 before) (generated-set-pc (+ 4 pc) before))))
     (implies (and (< (+ top 8) (expt 2 64)) (< (+ pc 8) (expt 2 64))
                   (generated-ordinary-machine-p before))
              (equal (generated-path-after *generated-push-path* before)
                     (generated-set-reg 25 (+ top 8) (generated-set-pc (+ pc 8) stored)))))
   :hints (("Goal" :in-theory (enable generated-path-after proof-stack-top)))))

(local
 (defthm generated-push-observes-written-word
   (let* ((top (proof-stack-top before))
          (after (generated-path-after *generated-push-path* before)))
     (implies (and (proof-span-p top 8) (< (+ top 8) (expt 2 64))
                   (< (+ (proof-world-pc before) 8) (expt 2 64))
                   (generated-ordinary-machine-p before))
              (and (equal (proof-load-word top (proof-world-machine after)) (proof-world-reg 0 before))
                   (equal (proof-world-pc after) (+ (proof-world-pc before) 8))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (generated-sp after) (generated-sp before))
                   (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                   (equal (proof-stack-top after) (+ top 8))
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (generated-memory-outside-p top (+ top 8) (proof-world-machine before)
                                              (proof-world-machine after)))))
   :hints (("Goal"
            :use ((:instance generated-load-after-word-store-same
                             (address (proof-stack-top before)) (value (proof-world-reg 0 before)) (world before))
                  (:instance generated-word-store-writes-only-inside-span
                             (address (proof-stack-top before)) (value (proof-world-reg 0 before)) (world before)
                             (start (proof-stack-top before)) (end (+ (proof-stack-top before) 8))))
            :in-theory (e/d (proof-stack-top proof-heap-base generated-load-word)
                            (generated-load-after-word-store-same generated-word-store-writes-only-inside-span))))
   :rule-classes nil))

(defthm generated-add-slots-keeps-stack-alignment
  (implies (and (integerp base) (integerp count))
           (equal (mod (+ base (* 8 count)) 8) (mod base 8)))
  :hints (("Goal" :use (:instance generated-floor-add-multiple (x base) (q count) (divisor 8))
                  :in-theory (enable mod)))
  :rule-classes nil)

(local
 (defthm generated-push-is-stack-update
   (let* ((top (proof-stack-top before))
          (after (generated-path-after *generated-push-path* before)))
     (implies (and (proof-heap-layout-p before) (<= (+ top 8) (proof-stack-limit before))
                   (< (+ (proof-world-pc before) 8) (expt 2 64))
                   (generated-ordinary-machine-p before))
              (generated-stack-update-p top (+ top 8) before after)))
   :hints (("Goal"
            :use ((:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-heap-layout-machine-stack-bounds (world before))
                  (:instance generated-stack-limit-is-bounded-word (world before))
                  (:instance generated-add-slots-keeps-stack-alignment (base (proof-stack-top before)) (count 1))
                  generated-push-observes-written-word)
            :in-theory (enable generated-stack-update-p generated-runtime-stack-span-p proof-span-p
                               proof-subspan-p proof-stack-top proof-stack-limit proof-machine-limit
                               proof-box-top proof-heap-limit proof-heap-base)))
   :rule-classes nil))

(defthm generated-stack-update-preserves-untouched-prefix
  (let* ((lower (proof-stack-base before))
         (retained (+ lower (* 8 keep))))
    (implies (and (proof-heap-p before objects packages)
                  (generated-stack-update-p start end before after)
                  (proof-object-disjoint-p start end objects (proof-world-machine before))
                  (natp keep) (<= retained (proof-stack-top before))
                  (<= retained (proof-stack-top after))
                  (proof-disjoint-p lower retained start end))
             (proof-prefix-preserved-p retained before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-layout-value-stack-bounds (world before))
                 generated-stack-update-preserves-runtime-fields
                 (:instance generated-lower-stack-prefix-is-valid
                            (count keep) (top (+ (proof-stack-base before) (* 8 keep))))
                 (:instance generated-stack-views-outside-written-span
                            (address (proof-stack-base before)) (count keep) (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance generated-stack-prefix-at-slot-count
                            (world before) (count keep) (top (+ (proof-stack-base before) (* 8 keep))))
                 (:instance generated-stack-prefix-at-slot-count
                            (world after) (count keep) (top (+ (proof-stack-base before) (* 8 keep)))))
           :in-theory (e/d (generated-stack-update-p proof-prefix-preserved-p proof-span-p)
                           (generated-lower-stack-prefix-is-valid generated-stack-prefix-at-slot-count))))
  :rule-classes nil)

(defthm generated-stack-prefix-with-argument-suffix
  (let* ((lower (proof-stack-base after))
         (retained (+ lower (* 8 keep)))
         (prefix (proof-stack-prefix retained after objects packages))
         (count (len args))
         (views (proof-argument-views args)))
    (implies (and (natp keep) (equal (proof-stack-top after) (+ retained (* 8 count)))
                  prefix
                  (equal (proof-stack-views count retained (proof-heap-base after) objects packages
                                           (proof-world-machine after))
                         (cons :slots views)))
             (equal (proof-stack-prefix (proof-stack-top after) after objects packages)
                    (cons :slots (append (cdr prefix) views)))))
  :hints (("Goal"
           :use ((:instance generated-stack-prefix-at-slot-count (count keep) (world after)
                            (top (+ (proof-stack-base after) (* 8 keep))))
                 (:instance generated-stack-prefix-at-slot-count (count (+ keep (len args))) (world after)
                            (top (proof-stack-top after)))
                 (:instance generated-stack-views-split (first keep) (rest (len args))
                            (address (proof-stack-base after)) (base (proof-heap-base after))
                            (machine (proof-world-machine after))))
           :in-theory (disable generated-stack-prefix-at-slot-count proof-argument-views)))
  :rule-classes nil)

(defthm generated-stack-views-of-one-slot
  (let ((view (proof-view (proof-load-word address machine) base objects packages machine)))
    (equal (proof-stack-views 1 address base objects packages machine)
           (and view (list :slots view))))
  :hints (("Goal" :expand ((proof-stack-views 1 address base objects packages machine)
                           (proof-stack-views 0 (+ 8 address) base objects packages machine)))))

(defthm generated-argument-views-of-singleton
  (equal (proof-argument-views (list datum)) (list (proof-value-view datum)))
  :hints (("Goal" :expand ((proof-argument-views (list datum)) (proof-argument-views nil)))))

(local
 (defthm generated-pushed-operand-has-source-view
   (let* ((top (proof-stack-top before))
          (pc (proof-world-pc before))
          (after (generated-path-after *generated-push-path* before)))
     (implies (and (proof-heap-p before objects packages)
                   (<= (+ top 8) (proof-stack-limit before)) (< (+ pc 8) (expt 2 64))
                   (generated-ordinary-machine-p before)
                   (proof-object-disjoint-p top (+ top 8) objects (proof-world-machine before))
                   (proof-reg-value-p 0 datum before objects packages))
              (and (generated-stack-update-p top (+ top 8) before after)
                   (equal (proof-world-pc after) (+ pc 8))
                   (not (proof-world-stop after))
                   (equal (generated-sp after) (generated-sp before))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                   (equal (proof-stack-top after) (+ top 8))
                   (equal (proof-stack-views 1 top (proof-heap-base after) objects packages
                                            (proof-world-machine after))
                          (list :slots (proof-value-view datum))))))
   :hints (("Goal"
            :use ((:instance generated-heap-has-layout-and-roots (world before))
                  (:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-stack-limit-is-bounded-word (world before))
                  generated-push-observes-written-word generated-push-is-stack-update
                  (:instance generated-published-view-unchanged-outside-written-span
                             (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                             (start (proof-stack-top before)) (end (+ (proof-stack-top before) 8))
                             (first (proof-world-machine before))
                             (last (proof-world-machine (generated-path-after *generated-push-path* before)))))
            :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-span-p proof-value-p proof-stack-top)
                            (generated-push-word-outcome))))
   :rule-classes nil))

(defthm generated-push-preserves-heap-and-appends-value
  (let* ((top (proof-stack-top before))
         (next (+ top 8))
         (end (+ (proof-world-pc before) 8))
         (after (generated-path-after *generated-push-path* before))
         (prefix (proof-stack-prefix top before objects packages)))
    (implies (and (proof-heap-p before objects packages)
                  (natp count) (equal top (+ (proof-stack-base before) (* 8 count)))
                  (<= next (proof-stack-limit before)) (< end (expt 2 64))
                  (generated-ordinary-machine-p before)
                  (generated-path-p *generated-push-path* (list end) before)
                  (proof-reg-value-p 0 datum before objects packages))
             (and (proof-segment-p 2 (list end) before :cut after)
                  (proof-heap-p after objects packages)
                  (equal (proof-world-pc after) end)
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (equal (proof-stack-top after) next)
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (equal (proof-stack-views 1 top (proof-heap-base after) objects packages
                                           (proof-world-machine after))
                         (list :slots (proof-value-view datum)))
                  (equal (proof-stack-prefix next after objects packages)
                         (cons :slots (append (cdr prefix) (list (proof-value-view datum))))))))
  :hints (("Goal"
           :use (generated-push-is-stack-update generated-pushed-operand-has-source-view
                 (:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-stack-update-is-disjoint-from-published-objects
                            (start (proof-stack-top before)) (end (+ (proof-stack-top before) 8))
                            (after (generated-path-after *generated-push-path* before)))
                 (:instance generated-stack-update-preserves-runtime-fields
                            (start (proof-stack-top before)) (end (+ (proof-stack-top before) 8))
                            (after (generated-path-after *generated-push-path* before)))
                 (:instance generated-stack-update-preserves-heap
                            (start (proof-stack-top before)) (end (+ (proof-stack-top before) 8))
                            (after (generated-path-after *generated-push-path* before)))
                 (:instance generated-stack-update-preserves-untouched-prefix
                            (start (proof-stack-top before)) (end (+ (proof-stack-top before) 8))
                            (keep count) (after (generated-path-after *generated-push-path* before)))
                 (:instance generated-stack-prefix-with-argument-suffix
                            (keep count) (args (list datum)) (after (generated-path-after *generated-push-path* before)))
                 (:instance generated-placed-path-to-cut (instructions *generated-push-path*)
                            (cuts (list (+ (proof-world-pc before) 8)))))
           :in-theory (e/d (proof-prefix-preserved-p proof-disjoint-p)
                           (generated-stack-views-of-one-slot))))
  :rule-classes nil)
