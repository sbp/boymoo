(in-package "BOYMOO-PROOFS")

(include-book "large-heap")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable allocation-runtime-word-as-load proof-runtime-word)))

(local
 (defthm allocation-large-runtime-word-range
   (unsigned-byte-p 64 (proof-runtime-word offset world))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use allocation-runtime-word-as-load))))

(local
 (defthm allocation-large-runtime-word-upper-bound
   (< (proof-runtime-word offset world) *allocation-word-modulus*)
   :rule-classes :linear
   :hints (("Goal" :use allocation-large-runtime-word-range
            :in-theory (disable allocation-large-runtime-word-range)))))

(defund allocation-large-layout-frame-p (before after)
  (and (allocation-same-external-bounds-p before after)
       (not (proof-world-stop after))
       (equal (proof-world-page-size after) (proof-world-page-size before))
       (equal (allocation-sp after) (+ 32 (allocation-sp before)))
       (equal (proof-stack-top after) (proof-stack-top before))
       (equal (proof-stack-limit after) (proof-stack-limit before))
       (equal (proof-box-top after) (proof-box-top before))
       (equal (proof-heap-limit after) (proof-heap-limit before))
       (equal (proof-active-floor after) (proof-active-floor before))
       (equal (proof-active-end after) (proof-active-end before))
       (equal (proof-inactive-floor after) (proof-inactive-floor before))
       (equal (proof-inactive-end after) (proof-inactive-end before))
       (equal (proof-cons-floor after) (proof-cons-floor before))))

(local
 (defthm allocation-large-layout-frame-keeps-base
   (implies (allocation-large-layout-frame-p before after)
            (equal (proof-heap-base after) (proof-heap-base before)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable allocation-large-layout-frame-p allocation-same-external-bounds-p)))))

(defthm allocation-large-checked-suffix-layout-frame
  (implies (and (allocation-large-mapped-entry-p origin before)
                (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                (equal after (allocation-path-end *allocation-large-restore-path* initialized))
                (allocation-large-postmap-result-p before after))
           (allocation-large-layout-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialized-machine-stages allocation-large-postmap-keeps-heap-registers
                 allocation-large-postmap-restore-keeps-initialization allocation-large-initialization-write-footprint
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 0))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 8))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 16))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 24))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 32))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 40))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 48))
                 (:instance allocation-large-initialization-keeps-runtime-word (offset 64)))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (allocation-large-mapped-entry-p allocation-path-end
                            allocation-large-insertion-p allocation-large-header-p
                            allocation-large-initialization-writes allocation-write-words
                            proof-object-word allocation-string-header proof-load-word)))))

(defthm allocation-large-initialization-keeps-static-area
  (let ((writes (allocation-large-initialization-writes before))
        (base (proof-heap-base before)))
    (implies (and (allocation-large-layout-frame-p before after)
                  (equal (allocation-memory after) (allocation-memory (allocation-write-words writes before)))
                  (proof-static-p base objects packages (proof-world-machine before))
                  (allocation-word-writes-avoid-span-p
                   writes base (+ base (proof-static-size base (proof-world-machine before)))))
             (and (proof-static-p (proof-heap-base after) objects packages (proof-world-machine after))
                  (equal (proof-static-size base (proof-world-machine after))
                         (proof-static-size base (proof-world-machine before))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-writes-keep-static-area
                  (writes (allocation-large-initialization-writes before)) (base (proof-heap-base before)) (world before))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first after) (last (allocation-write-words (allocation-large-initialization-writes before) before))))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (allocation-large-initialization-writes allocation-write-words
                            allocation-word-writes-avoid-span-p proof-static-p proof-load-word proof-heap-base
                            allocation-equal-memory-is-model-equivalence)))))

(defthm allocation-large-layout-after-initialization
  (let* ((base (proof-heap-base before))
         (machine-end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-large-layout-frame-p before after)
                  (equal (proof-static-size base (proof-world-machine after))
                         (proof-static-size base (proof-world-machine before)))
                  (<= (+ (allocation-sp before) 32) machine-end)
                  (equal (mod (+ (allocation-sp before) 32) 16) 0))
             (proof-heap-layout-p after)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (proof-align-up proof-covered-p proof-regions-p proof-page-size-p
                            proof-disjoint-p proof-static-size proof-load-word
                            proof-machine-limit proof-heap-base mod)))))

(local
 (defthm allocation-prefix-view-bytes-fit-stack-span
   (let* ((address (proof-stack-base world))
          (count (ash (- top address) -3)))
     (implies (and (proof-heap-layout-p world)
                   (natp top) (<= address top) (<= top (proof-stack-top world)))
              (and (proof-subspan-p address (* 8 count) address (proof-stack-end world))
                   (<= (proof-stack-end world) *allocation-word-modulus*))))
   :rule-classes nil
   :hints (("Goal"
            :use (allocation-layout-storage-spans
                  (:instance allocation-slot-bytes-fit (size (- top (proof-stack-base world)))))
            :in-theory (disable proof-heap-layout-p proof-stack-top proof-heap-base ash)))))

(defthm allocation-large-initialization-keeps-stack-prefix
  (let* ((lower (proof-stack-base before))
         (upper (proof-stack-end before))
         (writes (allocation-large-initialization-writes before)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-large-layout-frame-p before after)
                  (equal (allocation-memory after) (allocation-memory (allocation-write-words writes before)))
                  (allocation-word-writes-outside-objects-p writes objects (proof-world-machine before))
                  (allocation-word-writes-avoid-span-p writes lower upper))
             (equal (proof-stack-prefix top after objects packages)
                    (proof-stack-prefix top before objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-prefix-view-bytes-fit-stack-span (world before))
                 (:instance allocation-word-writes-avoid-subspan
                  (writes (allocation-large-initialization-writes before))
                  (lower (proof-stack-base before)) (upper (proof-stack-end before))
                  (start (proof-stack-base before))
                  (end (+ (proof-stack-base before) (* 8 (ash (- top (proof-stack-base before)) -3)))))
                 (:instance allocation-word-writes-keep-stack-views
                  (writes (allocation-large-initialization-writes before)) (world before)
                  (base (proof-heap-base before)) (address (proof-stack-base before))
                  (count (ash (- top (proof-stack-base before)) -3)))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first after) (last (allocation-write-words (allocation-large-initialization-writes before) before))))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-stack-views proof-heap-base proof-stack-base proof-stack-end
                            proof-stack-top proof-view proof-load-word allocation-equal-memory-is-model-equivalence
                            allocation-word-writes-outside-objects-p allocation-word-writes-avoid-span-p
                            allocation-large-initialization-writes allocation-write-words mod ash)))))

(defthm allocation-large-initialization-keeps-dynamic
  (let* ((base (proof-heap-base before))
         (machine (proof-world-machine before))
         (end (+ base (proof-static-size base machine)))
         (writes (allocation-large-initialization-writes before)))
    (implies (and (allocation-large-layout-frame-p before after)
                  (equal (allocation-memory after) (allocation-memory (allocation-write-words writes before)))
                  (proof-subspan-p (+ base 24) 8 base end)
                  (<= end *allocation-word-modulus*)
                  (allocation-word-writes-outside-objects-p writes objects machine)
                  (allocation-word-writes-avoid-span-p writes base end))
             (and (equal (proof-dynamic-view after objects packages) (proof-dynamic-view before objects packages))
                  (equal (proof-dynamic-symbol-objects-p objects objects entries base packages (proof-world-machine after))
                         (proof-dynamic-symbol-objects-p objects objects entries base packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-writes-keep-word-in-avoided-span
                  (writes (allocation-large-initialization-writes before)) (world before)
                  (address (+ 24 (proof-heap-base before))) (lower (proof-heap-base before))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-word-writes-keep-views
                  (writes (allocation-large-initialization-writes before)) (world before) (base (proof-heap-base before))
                  (word (proof-dynamic-root (proof-heap-base before) (proof-world-machine before))))
                 (:instance allocation-word-writes-keep-dynamic-symbols
                  (writes (allocation-large-initialization-writes before)) (world before) (base (proof-heap-base before)))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first after) (last (allocation-write-words (allocation-large-initialization-writes before) before))))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (proof-view proof-load-word proof-static-size proof-heap-base proof-subspan-p
                            proof-dynamic-symbol-objects-p allocation-equal-memory-is-model-equivalence
                            allocation-word-writes-outside-objects-p allocation-word-writes-avoid-span-p
                            allocation-large-initialization-writes allocation-write-words)))))

(defund allocation-large-mapping-outside-reservations-p (before)
  (let* ((mapping (proof-world-reg 0 before))
         (end (+ mapping (proof-world-reg 20 before)))
         (base (proof-heap-base before))
         (machine-start (- (proof-machine-limit before) *proof-machine-margin*)))
    (and (proof-disjoint-p mapping end (- base *proof-heap-prefix*) (proof-spaces-end before))
         (proof-disjoint-p mapping end (proof-stack-base before) (proof-stack-end before))
         (proof-disjoint-p mapping end machine-start (+ machine-start *proof-machine-reservation*)))))

(defthm allocation-large-writes-avoid-heap-frame
  (let* ((base (proof-heap-base before))
         (static-end (+ base (proof-static-size base (proof-world-machine before))))
         (sp (allocation-sp before))
         (limit (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
         (writes (allocation-large-initialization-writes before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (proof-heap-layout-p before)
                  (allocation-large-mapping-outside-reservations-p before))
             (and (natp base) (<= (+ base 24) *allocation-word-modulus*)
                  (natp static-end) (<= static-end *allocation-word-modulus*)
                  (natp sp) (natp limit) (<= limit *allocation-word-modulus*)
                  (allocation-word-writes-avoid-span-p writes base (+ base 24))
                  (allocation-word-writes-avoid-span-p writes (+ base 32) static-end)
                  (allocation-word-writes-avoid-span-p writes sp limit))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-large-writes-avoid-disjoint-span
                  (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before))))
                 (:instance allocation-large-writes-avoid-disjoint-span
                  (lower (+ 32 (proof-heap-base before)))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-large-writes-avoid-disjoint-span
                  (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
                 (:instance allocation-word-register-range (register 28) (world before)))
           :in-theory (e/d (allocation-large-mapping-outside-reservations-p)
                           (allocation-large-mapped-entry-p allocation-large-initialization-writes
                            proof-heap-layout-p allocation-word-writes-avoid-span-p
                            proof-machine-limit proof-static-size mod)))))

(defthm allocation-large-initialization-preserves-heap-frame
  (implies (and (allocation-large-mapped-entry-p origin before)
                (allocation-large-layout-frame-p before after)
                (proof-heap-layout-p before)
                (allocation-large-mapping-outside-reservations-p before)
                (equal (allocation-memory after)
                       (allocation-memory (allocation-write-words (allocation-large-initialization-writes before) before)))
                (proof-streams-preserved-p before after))
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-writes-avoid-heap-frame
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-large-initialization-writes before)) (world before)
                  (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before))))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-large-initialization-writes before)) (world before)
                  (lower (+ 32 (proof-heap-base before)))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-large-initialization-writes before)) (world before)
                  (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (allocation-large-mapped-entry-p allocation-large-initialization-writes
                            allocation-word-writes-avoid-span-p allocation-write-words
                            proof-heap-layout-p proof-memory-span-agrees-p proof-streams-preserved-p proof-static-size mod)))))

(local
 (defthm allocation-heap-object-subset-extension
   (implies (subsetp-equal pending objects)
            (subsetp-equal pending (cons object objects)))
   :hints (("Goal" :induct (subsetp-equal pending objects)))))

(local
 (defthm allocation-heap-object-subset-reflexive
   (subsetp-equal objects objects)))

(local
 (defthm allocation-large-dynamic-root-fits-static-area
   (let* ((base (proof-heap-base world))
          (end (+ base (proof-static-size base (proof-world-machine world)))))
     (implies (proof-heap-layout-p world)
              (and (proof-subspan-p (+ base 24) 8 base end)
                   (<= end *allocation-word-modulus*))))
   :rule-classes nil
   :hints (("Goal" :use allocation-layout-storage-spans
            :in-theory (disable proof-heap-layout-p proof-static-size proof-heap-base)))))

(defthm allocation-large-initialization-keeps-old-heap-components
  (let* ((base (proof-heap-base before))
         (machine (proof-world-machine before))
         (writes (allocation-large-initialization-writes before))
         (external (proof-external-objects (proof-external-head before) (len objects) before objects))
         (dynamic (proof-dynamic-entries (proof-dynamic-view before objects packages) packages))
         (top (proof-stack-top before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-large-mapped-entry-p origin before)
                  (allocation-large-layout-frame-p before after)
                  (allocation-large-mapping-outside-reservations-p before)
                  (equal (allocation-memory after) (allocation-memory (allocation-write-words writes before)))
                  (allocation-word-writes-outside-objects-p writes objects machine)
                  (<= (+ (allocation-sp before) 32)
                      (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
                  (equal (mod (+ (allocation-sp before) 32) 16) 0))
             (and (proof-heap-layout-p after)
                  (proof-static-p (proof-heap-base after) objects packages (proof-world-machine after))
                  (proof-heap-object-spans-p objects (cdr external) after)
                  (equal (proof-stack-prefix top after objects packages) (proof-stack-prefix top before objects packages))
                  (equal (proof-dynamic-view after objects packages) (proof-dynamic-view before objects packages))
                  (proof-dynamic-symbol-objects-p objects objects (cdr dynamic) base packages
                                                 (proof-world-machine after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-dynamic-root-fits-static-area (world before))
                 allocation-large-static-and-stack-footprint
                 allocation-large-initialization-keeps-static-area
                 allocation-large-layout-after-initialization
                 (:instance allocation-large-initialization-keeps-stack-prefix (top (proof-stack-top before)))
                 (:instance allocation-large-initialization-keeps-dynamic
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages))))
                 (:instance allocation-word-writes-keep-heap-object-spans
                  (pending objects) (base (proof-heap-base before))
                  (writes (allocation-large-initialization-writes before))
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first after) (last (allocation-write-words (allocation-large-initialization-writes before) before))))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p
                           allocation-large-mapping-outside-reservations-p)
                           (allocation-large-mapped-entry-p allocation-large-initialization-writes allocation-write-words
                            allocation-word-writes-outside-objects-p allocation-word-writes-avoid-span-p
                            proof-heap-layout-p proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-external-objects proof-string-accounting-p proof-dynamic-entries proof-dynamic-view
                            proof-dynamic-symbol-objects-p proof-stack-prefix proof-disjoint-p proof-load-word
                            proof-subspan-p proof-span-p allocation-equal-memory-is-model-equivalence mod)))))

(local
 (defthm allocation-extra-external-address-keeps-spans
   (implies (proof-heap-object-spans-p objects headers world)
            (proof-heap-object-spans-p objects (cons address headers) world))
   :hints (("Goal" :induct (proof-heap-object-spans-p objects headers world)
            :in-theory (disable proof-subspan-p proof-object-size mod)))))

(defthm allocation-external-record-extends-heap-spans
  (implies (proof-heap-object-spans-p objects headers world)
           (proof-heap-object-spans-p (cons (proof-object address :external :header 0) objects)
                                      (cons address headers) world))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-object-size))))

(defthm allocation-nonsymbol-record-adds-no-dynamic-symbol
  (implies (not (proof-symbol-object-p record machine))
           (equal (proof-dynamic-symbol-objects-p (cons record pending) objects entries base packages machine)
                  (proof-dynamic-symbol-objects-p pending objects entries base packages machine)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-object-view proof-symbol-object-p))))

(defthm allocation-large-header-is-nonsymbol
  (let ((record (proof-object (+ 24 (proof-world-reg 0 before)) :external :header 0)))
    (implies (allocation-large-postmap-result-p before after)
             (not (proof-symbol-object-p record (proof-world-machine after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-string-header-fields (length (proof-world-reg 19 before))))
           :in-theory (e/d (allocation-load-word)
                           (proof-load-word proof-header-type allocation-string-header proof-object-word
                            proof-streams-preserved-p)))))

(defthm allocation-large-runtime-prefix-avoids-published-objects
  (implies (proof-heap-p before objects packages)
           (allocation-objects-outside-write-p
            (- (proof-heap-base before) 128) (proof-heap-base before) objects (proof-world-machine before)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-heap-published-map (world before))
                 (:instance allocation-prefix-span-disjoint-from-published-objects
                  (start (- (proof-heap-base before) 128)) (end (proof-heap-base before)))
                 (:instance allocation-object-map-with-disjoint-spans
                  (start (- (proof-heap-base before) 128)) (end (proof-heap-base before))
                  (pending objects) (symbols nil) (base (proof-heap-base before)) (machine (proof-world-machine before))))
           :in-theory (disable proof-heap-p proof-object-map-p proof-object-disjoint-p
                               allocation-objects-outside-write-p proof-heap-base))))

(defthm allocation-large-mapping-has-fresh-header
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (length (proof-world-reg 19 before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal size (allocation-large-mapping-size length))
                  (allocation-objects-outside-write-p mapping (+ mapping size) objects (proof-world-machine before)))
             (not (assoc-equal (+ 24 mapping) objects))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-extents-within-request
                  (mapping (proof-world-reg 0 before)) (size (proof-world-reg 20 before)) (length (proof-world-reg 19 before)))
                 (:instance allocation-objects-outside-subspan
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower (+ 24 (proof-world-reg 0 before))) (upper (+ 40 (proof-world-reg 0 before)))
                  (machine (proof-world-machine before)))
                 (:instance allocation-cell-span-excludes-existing-address
                  (address (+ 24 (proof-world-reg 0 before))) (machine (proof-world-machine before))))
           :in-theory (disable allocation-large-mapping-size allocation-objects-outside-write-p
                               allocation-code-origin-p allocation-large-string-address proof-disjoint-p mod))))

(defthm allocation-published-external-record-admits-heap
  (let* ((base (proof-heap-base after))
         (machine (proof-world-machine after))
         (record (proof-object address :external :header 0))
         (published (cons record objects))
         (dynamic (proof-dynamic-entries (proof-dynamic-view before objects packages) packages))
         (top (proof-stack-top before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-large-layout-frame-p before after)
                  (proof-heap-layout-p after)
                  (proof-static-p base objects packages machine)
                  (proof-heap-object-spans-p objects headers after)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-object-map-p published published nil base packages machine)
                  (equal (proof-external-objects (proof-external-head after) (len published) after published)
                         (list* :mappings address headers))
                  (proof-string-accounting-p (cons address headers) after)
                  (equal (proof-stack-prefix top after objects packages) (proof-stack-prefix top before objects packages))
                  (equal (proof-dynamic-view after objects packages) (proof-dynamic-view before objects packages))
                  (proof-dynamic-symbol-objects-p objects objects (cdr dynamic) base packages machine)
                  (not (assoc-equal address objects))
                  (not (proof-symbol-object-p record machine)))
             (and (proof-heap-p after published packages)
                  (proof-prefix-preserved-p top before after objects published packages)
                  (proof-dynamic-table-preserved-p nil before after objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-external-record-extends-heap-spans (world after))
                 (:instance allocation-old-dynamic-symbols-after-publication
                  (pending objects) (object (proof-object address :external :header 0)) (symbols nil)
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                  (base (proof-heap-base after)) (machine (proof-world-machine after)))
                 (:instance allocation-nonsymbol-record-adds-no-dynamic-symbol
                  (record (proof-object address :external :header 0)) (pending objects)
                  (objects (cons (proof-object address :external :header 0) objects))
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                  (base (proof-heap-base after)) (machine (proof-world-machine after))))
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-external-objects proof-external-head proof-string-accounting-p
                            proof-dynamic-entries proof-dynamic-view proof-dynamic-symbol-objects-p
                            proof-symbol-object-p proof-stack-top proof-stack-prefix proof-heap-base)))))

(defthm allocation-large-checked-suffix-effects
  (let* ((path (allocation-large-postmap-path))
         (cuts (list (allocation-load-word (+ (allocation-sp before) 8) before))))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized))
                  (allocation-path-ready-p path cuts before))
             (and (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (allocation-large-postmap-result-p before after)
                  (allocation-large-layout-frame-p before after)
                  (proof-streams-preserved-p before after)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (equal (allocation-memory after)
                         (allocation-memory (allocation-write-words (allocation-large-initialization-writes before) before)))
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-postmap-checked-return allocation-large-initialized-machine-stages
                 allocation-large-postmap-restore-keeps-initialization allocation-large-initialization-write-footprint
                 allocation-large-checked-suffix-layout-frame)
           :in-theory (disable allocation-large-mapped-entry-p allocation-large-insertion-p allocation-large-header-p
                               allocation-large-layout-frame-p allocation-path-end allocation-path-ready-p
                               allocation-large-initialization-writes allocation-write-words proof-segment-p
                               proof-object-word allocation-string-header))))

(local
 (defthm allocation-large-heap-entry-components
   (let* ((base (proof-heap-base before))
          (machine (proof-world-machine before))
          (head (proof-external-head before))
          (external (proof-external-objects head (len objects) before objects)))
     (implies (proof-heap-p before objects packages)
              (and (proof-heap-layout-p before)
                   (proof-object-map-p objects objects nil base packages machine)
                   external
                   (proof-string-accounting-p (cdr external) before))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                                      proof-string-accounting-p proof-heap-object-spans-p proof-dynamic-view
                                      proof-dynamic-entries proof-dynamic-symbol-objects-p proof-stack-prefix)))))

(local
 (defthm allocation-large-mapped-region-spans
   (implies (allocation-large-mapped-entry-p origin before)
            (and (proof-span-p (proof-world-reg 0 before) (proof-world-reg 20 before))
                 (<= 32 (proof-world-reg 20 before))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable allocation-code-origin-p allocation-large-string-address proof-span-p)))))

(local
 (defthm allocation-region-at-head-is-present
   (implies (equal regions (cons region rest))
            (member-equal region regions))
   :rule-classes nil))

(defthm allocation-large-checked-external-list-and-accounting
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (address (+ mapping 24))
         (external (proof-external-objects (proof-external-head before) (len objects) before objects))
         (old-total (proof-external-bytes (cdr external) (proof-world-machine before)))
         (published (cons (proof-object address :external :header 0) objects)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (allocation-large-postmap-result-p before after)
                  (allocation-large-layout-frame-p before after)
                  (allocation-large-mapping-outside-reservations-p before)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (proof-heap-p before objects packages)
                  (equal size (allocation-large-mapping-size length))
                  (equal (proof-world-regions before) (cons (proof-region mapping (+ mapping size) :rw) old-regions))
                  (equal (allocation-memory before) (proof-clear-memory mapping (+ mapping size) memory))
                  (not (assoc-equal address objects))
                  (< (+ old-total size) (expt 2 63)))
             (and (equal (proof-external-objects (proof-external-head after) (len published) after published)
                         (list* :mappings address (cdr external)))
                  (proof-string-accounting-p (cons address (cdr external)) after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-heap-entry-components
                 allocation-large-mapped-region-spans
                 (:instance allocation-layout-storage-spans (world before))
                 allocation-large-cleared-header-is-zero allocation-large-mark-is-zero-on-cleared-mapping
                 (:instance allocation-large-fresh-region-writes-avoid-existing-external-spans
                  (head (proof-external-head before)) (fuel (len objects)))
                 (:instance allocation-region-at-head-is-present
                  (regions (proof-world-regions after)) (rest old-regions)
                  (region (proof-region (proof-world-reg 0 before)
                                        (+ (proof-world-reg 0 before) (proof-world-reg 20 before)) :rw)))
                 allocation-large-keeps-old-external-list allocation-large-publishes-external-list
                 allocation-large-accounting-after-publication)
           :in-theory (e/d (allocation-large-layout-frame-p allocation-same-external-bounds-p
                           allocation-large-mapping-outside-reservations-p)
                           (allocation-large-mapped-entry-p allocation-large-insertion-p allocation-large-header-p
                            allocation-large-postmap-result-p proof-heap-p proof-heap-layout-p proof-external-objects
                            proof-external-head proof-external-bytes proof-string-accounting-p proof-disjoint-p proof-span-p
                            proof-clear-memory proof-regions-p proof-heap-base proof-machine-limit member-equal
                            allocation-large-mapping-size)))))

(defthm allocation-large-checked-heap-return-from-mapping
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before))
         (machine (proof-world-machine before))
         (external (proof-external-objects (proof-external-head before) (len objects) before objects))
         (old-total (proof-external-bytes (cdr external) machine))
         (published (cons (proof-object (+ mapping 24) :external :header 0) objects))
         (path (allocation-large-postmap-path))
         (cuts (list (allocation-load-word (+ (allocation-sp before) 8) before))))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized))
                  (allocation-path-ready-p path cuts before)
                  (proof-heap-p before objects packages)
                  (equal size (allocation-large-mapping-size length))
                  (equal (mod mapping 8) 0) (equal (mod base 8) 0)
                  (allocation-large-mapping-outside-reservations-p before)
                  (equal (proof-world-regions before) (cons (proof-region mapping (+ mapping size) :rw) old-regions))
                  (equal (allocation-memory before) (proof-clear-memory mapping (+ mapping size) memory))
                  (allocation-objects-outside-write-p mapping (+ mapping size) objects machine)
                  (< (+ old-total size) (expt 2 63))
                  (<= (+ (allocation-sp before) 32)
                      (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
                  (equal (mod (+ (allocation-sp before) 32) 16) 0))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (proof-preserved-heap-p nil before after objects published packages)
                  (proof-string-result-p length after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-checked-suffix-effects allocation-large-heap-entry-components
                 allocation-large-layout-frame-keeps-base
                 allocation-large-runtime-prefix-avoids-published-objects
                 allocation-large-initialization-writes-outside-objects
                 allocation-large-mapping-has-fresh-header
                 (:instance allocation-region-at-head-is-present
                  (regions (proof-world-regions before)) (rest old-regions)
                  (region (proof-region (proof-world-reg 0 before)
                                        (+ (proof-world-reg 0 before) (proof-world-reg 20 before)) :rw)))
                 allocation-large-checked-initialization-and-publication
                 (:instance allocation-large-write-preserves-published-objects (word 0) (lower 0) (upper 0))
                 allocation-large-initialization-keeps-old-heap-components
                 allocation-large-checked-external-list-and-accounting
                 allocation-large-initialization-preserves-heap-frame allocation-large-header-is-nonsymbol
                 (:instance allocation-published-external-record-admits-heap
                  (address (+ 24 (proof-world-reg 0 before)))
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))))
           :in-theory (disable allocation-large-layout-frame-p
                            allocation-large-mapped-entry-p allocation-large-postmap-result-p allocation-large-insertion-p
                            allocation-large-header-p allocation-large-mapping-outside-reservations-p
                            allocation-large-initialization-writes allocation-large-mapping-size allocation-write-words
                            allocation-path-end allocation-path-ready-p proof-segment-p proof-heap-p proof-heap-layout-p
                            proof-static-p proof-external-objects proof-external-head proof-external-bytes
                            proof-object-map-p proof-object-disjoint-p proof-heap-object-spans-p proof-string-accounting-p
                            proof-string-result-p proof-symbol-object-p proof-clear-memory proof-heap-base
                            proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p proof-stack-prefix
                            proof-heap-frame-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                            proof-span-p proof-subspan-p proof-view proof-view-step proof-streams-preserved-p
                            allocation-objects-outside-write-p allocation-word-writes-outside-objects-p member-equal mod))))
