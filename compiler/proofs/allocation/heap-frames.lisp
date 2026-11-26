(in-package "BOYMOO-PROOFS")

(include-book "segments")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-same-memory-p (first last)
  (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last)))

(defequiv allocation-same-memory-p)

(in-theory (disable allocation-same-memory-p))

(defcong allocation-same-memory-p equal (proof-load-word address machine) 2
  :hints (("Goal" :in-theory (enable allocation-same-memory-p proof-load-word))))

(defcong allocation-same-memory-p equal (proof-byte-list count address machine) 3
  :hints (("Goal" :induct (proof-byte-list count address machine)
           :in-theory (enable allocation-same-memory-p))))

(defcong allocation-same-memory-p equal (proof-load-string count address machine) 3)

(defcong allocation-same-memory-p equal (proof-limb-magnitude count address machine) 3
  :hints (("Goal" :induct (proof-limb-magnitude count address machine))))

(defcong allocation-same-memory-p equal (proof-limbs-p count address machine) 3
  :hints (("Goal" :induct (proof-limbs-p count address machine))))

(defcong allocation-same-memory-p equal (proof-integer-view address machine) 2)

(defcong allocation-same-memory-p equal
  (proof-view-step kind input count depth base objects packages machine) 8
  :hints (("Goal" :induct (proof-view-step kind input count depth base objects packages machine)
           :expand ((:free (mode mem)
                           (proof-view-step mode input count depth base objects packages mem)))
           :in-theory (disable (:definition proof-view-step) mod oddp
                               proof-cons-value proof-rational-value proof-complex-value
                               proof-symbol-value proof-pointer-address proof-integer-view
                               proof-load-string proof-header-type proof-header-size))))

(defcong allocation-same-memory-p equal (proof-view word base objects packages machine) 5)

(defcong allocation-same-memory-p equal (proof-object-size object machine) 2)

(defcong allocation-same-memory-p equal (proof-object-disjoint-p address end objects machine) 4
  :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine))))

(defcong allocation-same-memory-p equal
  (proof-object-view object base objects packages machine) 5)

(defcong allocation-same-memory-p equal (proof-symbol-object-p object machine) 2)

(defcong allocation-same-memory-p equal
  (proof-object-map-p pending objects symbols base packages machine) 6
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-view proof-symbol-object-p proof-object-size
                               proof-object-disjoint-p proof-object-record-p))))

(defcong allocation-same-memory-p equal (proof-static-spans-p objects base size machine) 4
  :hints (("Goal" :induct (proof-static-spans-p objects base size machine)
           :in-theory (disable proof-object-size))))

(defcong allocation-same-memory-p equal
  (proof-home-bindings-p pending base objects packages machine buckets) 5
  :hints (("Goal" :induct (proof-home-bindings-p pending base objects packages machine buckets)
           :in-theory (disable proof-object-view proof-symbol-object-p proof-view))))

(defcong allocation-same-memory-p equal (proof-static-p base objects packages machine) 4
  :hints (("Goal" :in-theory (disable proof-static-objects proof-object-map-p
                                     proof-static-spans-p proof-home-bindings-p proof-view))))

(defcong allocation-same-memory-p equal
  (proof-dynamic-symbol-objects-p pending objects entries base packages machine) 6
  :hints (("Goal" :induct (proof-dynamic-symbol-objects-p pending objects entries
                                                       base packages machine)
           :in-theory (disable proof-object-view proof-symbol-object-p))))

(defcong allocation-same-memory-p equal
  (proof-stack-views count address base objects packages machine) 6
  :hints (("Goal" :induct (proof-stack-views count address base objects packages machine)
           :in-theory (disable proof-view))))

(defcong allocation-same-memory-p equal (proof-external-bytes headers machine) 2
  :hints (("Goal" :induct (proof-external-bytes headers machine))))

(defthm allocation-memory-agrees-with-itself
  (proof-byte-entries-agree-p entries start end memory memory))

(defthm allocation-equal-memory-agrees-on-span
  (implies (equal (allocation-memory before) (allocation-memory after))
           (proof-memory-span-agrees-p start end before after))
  :hints (("Goal" :in-theory (disable proof-byte-entries-agree-p))))

(defthm allocation-equal-memory-is-model-equivalence
  (equal (allocation-same-memory-p (proof-world-machine first) (proof-world-machine last))
         (equal (allocation-memory first) (allocation-memory last)))
  :hints (("Goal" :in-theory (enable allocation-same-memory-p))))

; The committed limits are independent of the registers and memory
; observed by the static tables, root views, and external mappings.
(defun allocation-same-heap-context-p (first last)
  (and (allocation-same-memory-p (proof-world-machine first) (proof-world-machine last))
       (equal (proof-heap-base first) (proof-heap-base last))
       (equal (proof-stack-top first) (proof-stack-top last))
       (equal (proof-machine-limit first) (proof-machine-limit last))
       (equal (allocation-sp first) (allocation-sp last))
       (equal (proof-world-regions first) (proof-world-regions last))
       (equal (proof-world-replies first) (proof-world-replies last))
       (equal (proof-world-stop first) (proof-world-stop last))
       (proof-streams-preserved-p first last)))

(defequiv allocation-same-heap-context-p)

(in-theory (disable allocation-same-heap-context-p))

(defmacro allocation-heap-context-congruence (accessor)
  `(defcong allocation-same-heap-context-p equal (,accessor world) 1
     :hints (("Goal" :in-theory (enable allocation-same-heap-context-p)))))

(allocation-heap-context-congruence proof-heap-base)
(allocation-heap-context-congruence proof-stack-top)
(allocation-heap-context-congruence proof-machine-limit)
(allocation-heap-context-congruence allocation-sp)
(allocation-heap-context-congruence proof-world-regions)
(allocation-heap-context-congruence proof-world-replies)
(allocation-heap-context-congruence proof-world-page-size)
(allocation-heap-context-congruence proof-world-stop)
(allocation-heap-context-congruence proof-world-input)
(allocation-heap-context-congruence proof-world-stdout)
(allocation-heap-context-congruence proof-world-stderr)

(defcong allocation-same-heap-context-p allocation-same-memory-p (proof-world-machine world) 1
  :hints (("Goal" :in-theory (enable allocation-same-heap-context-p))))

(defcong allocation-same-heap-context-p equal (proof-runtime-word offset world) 2
  :hints (("Goal" :in-theory (e/d (proof-runtime-word)
                                (allocation-runtime-word-as-load proof-heap-base)))))

(local (in-theory (disable allocation-runtime-word-as-load)))

(defcong allocation-same-heap-context-p equal (proof-external-objects head fuel world objects) 3
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :expand ((:free (h w) (proof-external-objects h fuel w objects)))
           :in-theory (disable (:definition proof-external-objects)
                               proof-disjoint-p proof-heap-base proof-machine-limit
                               proof-string-accounting-p proof-header-type proof-header-size
                               proof-align-up))))

(defcong allocation-same-heap-context-p equal (proof-string-accounting-p headers world) 2)

(defcong allocation-same-heap-context-p equal (proof-stack-prefix top world objects packages) 2
  :hints (("Goal" :in-theory (disable proof-stack-views proof-heap-base proof-stack-top))))

(defcong allocation-same-heap-context-p equal (proof-dynamic-view world objects packages) 1
  :hints (("Goal" :in-theory (disable proof-view proof-heap-base))))

(defthm allocation-extend-layout-tops
  (implies (and (allocation-same-heap-context-p before after)
                (proof-heap-layout-p before)
                (<= (proof-stack-limit before) (proof-stack-limit after))
                (<= (proof-stack-limit after) (proof-stack-end before))
                (equal (mod (proof-stack-limit after) 8) 0)
                (<= (proof-box-top before) (proof-box-top after))
                (<= (proof-box-top after) (proof-heap-limit after))
                (<= (proof-heap-limit after) (proof-cons-floor before))
                (equal (mod (proof-box-top after) 8) 0)
                (equal (mod (proof-heap-limit after) 8) 0))
           (proof-heap-layout-p after))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-covered-p proof-disjoint-p proof-regions-p
                                     proof-align-up proof-heap-base
                                     proof-machine-limit proof-stack-top mod))))

(defthm allocation-existing-spans-with-raised-box-top
  (implies (and (allocation-same-heap-context-p before after)
                (proof-heap-object-spans-p objects external before)
                (<= (proof-box-top before) (proof-box-top after)))
           (proof-heap-object-spans-p objects external after))
  :rule-classes nil
  :hints (("Goal" :induct (proof-heap-object-spans-p objects external before)
           :in-theory (disable proof-object-size mod))))

(defthm allocation-heap-with-raised-box-top
  (implies (and (allocation-same-heap-context-p before after)
                (proof-heap-p before objects packages)
                (proof-heap-layout-p after)
                (<= (proof-box-top before) (proof-box-top after)))
           (proof-heap-p after objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-existing-spans-with-raised-box-top
                  (external (cdr (proof-external-objects
                                  (proof-external-head before) (len objects) before objects)))))
           :in-theory (disable proof-heap-layout-p proof-heap-object-spans-p proof-static-p
                               proof-object-map-p proof-stack-top proof-stack-prefix
                               proof-dynamic-view proof-dynamic-entries
                               proof-dynamic-symbol-objects-p proof-string-accounting-p
                               proof-external-objects proof-heap-base))))

(defthm allocation-fixed-external-under-equal-memory
  (implies (equal (allocation-memory before) (allocation-memory after))
           (proof-fixed-external-p headers before after))
  :hints (("Goal" :induct (proof-fixed-external-p headers before after)
           :in-theory (disable proof-memory-span-agrees-p))))

(defthm allocation-memory-and-streams-of-same-context
  (implies (allocation-same-heap-context-p before after)
           (and (equal (allocation-memory before) (allocation-memory after))
                (proof-streams-preserved-p before after)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable allocation-same-heap-context-p))))

(defthm allocation-heap-frame-under-same-context
  (implies (allocation-same-heap-context-p before after)
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal" :use allocation-memory-and-streams-of-same-context
           :in-theory (disable proof-streams-preserved-p proof-memory-span-agrees-p
                               proof-heap-base proof-machine-limit))))

(defthm allocation-fixed-heap-under-same-context
  (implies (and (allocation-same-heap-context-p before after)
                (equal (proof-box-top before) (proof-box-top after))
                (equal (proof-heap-limit before) (proof-heap-limit after))
                (proof-heap-p before objects packages))
           (proof-fixed-heap-p before after objects))
  :rule-classes nil
  :hints (("Goal" :use allocation-memory-and-streams-of-same-context
           :in-theory (disable proof-static-p proof-heap-layout-p proof-dynamic-view
                                 proof-external-objects proof-object-map-p
                                 proof-heap-object-spans-p proof-string-accounting-p
                                 proof-stack-prefix proof-dynamic-symbol-objects-p
                                 proof-memory-span-agrees-p proof-fixed-external-p
                                 proof-heap-base))))

(defthm allocation-heap-stack-prefix-exists
  (implies (proof-heap-p world objects packages)
           (proof-stack-prefix (proof-stack-top world) world objects packages))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-static-p proof-heap-layout-p proof-dynamic-view
                                     proof-external-objects proof-object-map-p
                                     proof-heap-object-spans-p proof-string-accounting-p
                                     proof-stack-prefix proof-dynamic-symbol-objects-p))))

(defthm allocation-layout-of-heap
  (implies (proof-heap-p world objects packages)
           (proof-heap-layout-p world))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-dynamic-view
                                     proof-external-objects proof-object-map-p
                                     proof-heap-object-spans-p proof-string-accounting-p
                                     proof-stack-prefix proof-dynamic-symbol-objects-p))))

(defthm allocation-preserved-heap-under-same-context
  (implies (and (allocation-same-heap-context-p before after)
                (proof-heap-p before objects packages)
                (proof-heap-p after objects packages))
           (proof-preserved-heap-p nil before after objects objects packages))
  :rule-classes nil
  :hints (("Goal" :use (allocation-heap-frame-under-same-context
                        (:instance allocation-heap-stack-prefix-exists (world before)))
           :in-theory (disable proof-heap-frame-p proof-dynamic-view
                               proof-stack-prefix proof-stack-top proof-heap-p))))

(defthm allocation-context-from-register-frame
  (implies (and (proof-register-frame-p 30 clobbers before after)
                (not (member-equal 23 clobbers))
                (not (member-equal 25 clobbers))
                (not (member-equal 28 clobbers))
                (equal (allocation-sp before) (allocation-sp after))
                (equal (allocation-memory before) (allocation-memory after))
                (equal (proof-world-regions before) (proof-world-regions after))
                (equal (proof-world-replies before) (proof-world-replies after))
                (equal (proof-world-stop before) (proof-world-stop after))
                (proof-streams-preserved-p before after))
           (allocation-same-heap-context-p before after))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-register-frame-member (register 23) (upper 30))
                        (:instance allocation-register-frame-member (register 25) (upper 30))
                        (:instance allocation-register-frame-member (register 28) (upper 30)))
           :in-theory (enable allocation-same-heap-context-p))))

(defcong allocation-same-heap-context-p equal (allocation-memory world) 1
  :hints (("Goal" :in-theory (enable allocation-same-heap-context-p))))

(defcong allocation-same-heap-context-p equal (proof-heap-frame-p before after) 1
  :hints (("Goal" :in-theory (disable proof-heap-base proof-machine-limit))))

(defcong allocation-same-heap-context-p equal
  (proof-preserved-heap-p may-intern before after old-objects new-objects packages) 2
  :hints (("Goal" :in-theory (disable proof-heap-p proof-heap-frame-p proof-stack-top
                                     proof-stack-prefix proof-dynamic-entries proof-dynamic-view))))
