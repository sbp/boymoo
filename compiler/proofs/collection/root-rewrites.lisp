(in-package "BOYMOO-PROOFS")

(include-book "scan-fields")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable collection-read-word proof-load-word proof-world-machine
                     proof-stack-base proof-stack-top proof-heap-base proof-dynamic-root
                     proof-inactive-floor proof-inactive-end collection-trace-effect
                     collection-trace-ready-p proof-segment-p
                     collection-slot-rewrite-entry-p collection-slot-rewrite-round-input-p
                     collection-slot-rewrite-input-p collection-slot-rewrite-trace
                     collection-relocate-datum collection-discover collection-unseen collection-forwarding
                     collection-reference-fields collection-work collection-rewrite-slots
                     collection-graph-record-p collection-published-object-graph
                     proof-pointer-address proof-word-tag boymoo-model::a64-unsigned (:definition ash))))

(local
 (defun collection-word-list-first-difference (left right)
   (if (and (consp left) (consp right) (equal (car left) (car right)))
       (1+ (collection-word-list-first-difference (cdr left) (cdr right)))
     0)))

(local
 (defthm collection-differing-word-lists-disagree-at-a-valid-index
   (let ((index (collection-word-list-first-difference left right)))
     (implies (and (true-listp left) (true-listp right)
                   (equal (len left) (len right)) (not (equal left right)))
              (and (natp index)
                   (< index (len left))
                   (not (equal (nth index left) (nth index right))))))
   :hints (("Goal" :induct (collection-word-list-first-difference left right)))))

(local
 (defthm collection-slot-word-list-has-count
   (equal (len (collection-slot-words count base world)) (nfix count))
   :hints (("Goal" :induct (collection-slot-words count base world)))))

(local
 (defthm collection-slot-word-list-is-true-list
   (true-listp (collection-slot-words count base world))))

(local
 (defthm collection-slot-plan-word-list-has-one-entry-per-call
   (equal (len (strip-cars plans)) (len plans))))

(local
 (in-theory (disable collection-word-list-first-difference collection-slot-words)))

(defthm collection-admitted-slot-loop-installs-entire-plan
  (let* ((count (len plans))
         (after (collection-trace-effect (collection-slot-rewrite-trace roots plans origin) world)))
    (implies (and (collection-slot-rewrite-input-p roots plans 0 base origin world)
                  (integerp base))
             (equal (collection-slot-words count base after) (strip-cars plans))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-differing-word-lists-disagree-at-a-valid-index
                            (left (collection-slot-words
                                   (len plans) base
                                   (collection-trace-effect (collection-slot-rewrite-trace roots plans origin) world)))
                            (right (strip-cars plans)))
                 (:instance collection-slot-rewrite-traversal-commits-all-returned-words
                            (position 0)
                            (index (collection-word-list-first-difference
                                    (collection-slot-words
                                     (len plans) base
                                     (collection-trace-effect (collection-slot-rewrite-trace roots plans origin) world))
                                    (strip-cars plans))))))))

(defthm collection-checked-slot-loop-establishes-committed-fields
  (let* ((count (len plans))
         (machine (proof-world-machine original))
         (trace (collection-slot-rewrite-trace roots plans origin))
         (cut (list (+ origin (collection-linux-offset "rt:scan"))))
         (after (collection-trace-effect trace world)))
    (mv-let (words next)
      (collection-rewrite-slots count source data-base objects machine work)
      (implies (and (collection-slot-rewrite-input-p roots plans 0 base origin world)
                    (integerp base)
                    (collection-trace-ready-p trace cut world)
                    (collection-slot-sources-known-p count source data-base objects machine work)
                    (equal (strip-cars plans) words))
               (and (proof-segment-p (len trace) cut world :cut after)
                    (collection-scanned-fields-p count source base data-base objects original after next)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-admitted-slot-loop-installs-entire-plan)
                 (:instance collection-ready-trace-reaches-cut
                            (trace (collection-slot-rewrite-trace roots plans origin))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan")))))
                 (:instance collection-writing-the-abstract-rewrites-commits-all-fields
                            (count (len plans)) (target base) (base data-base)
                            (current (collection-trace-effect
                                      (collection-slot-rewrite-trace roots plans origin) world))))
           :in-theory (disable collection-scanned-fields-p collection-slot-sources-known-p
                               collection-slot-rewrites-discover-exactly-the-graph-edges))))

(defthm collection-dynamic-and-stack-rewrites-start-published-traversal
  (let* ((base (proof-heap-base original))
         (machine (proof-world-machine original))
         (graph (collection-published-object-graph objects base objects machine))
         (lower (proof-inactive-floor original))
         (upper (proof-inactive-end original))
         (empty (collection-work graph nil nil nil lower upper))
         (dynamic (proof-dynamic-root base machine))
         (bottom (proof-stack-base original))
         (count (ash (- (proof-stack-top original) bottom) -3))
         (started (mv-nth 1 (collection-rewrite-slots
                             count bottom base objects machine
                             (collection-discover-datum dynamic base objects empty)))))
    (equal started (collection-discover-fields (collection-published-roots original objects) empty)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (collection-published-roots collection-discover-datum collection-discover-fields)
                            (collection-movable-reference)))))
