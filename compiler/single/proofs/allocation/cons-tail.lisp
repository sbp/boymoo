(in-package "BOYMOO-PROOFS")

(include-book "cons-heap")
(include-book "stack-pop")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-resumed-cons-world (world)
  (let* ((top (allocation-cons-reload-address world))
         (cell (proof-world-reg 0 world))
         (first (allocation-load-word top world))
         (second (allocation-load-word (+ top 8) world))
         (initialized (allocation-initialized-cell-world cell first second world)))
    (allocation-world-with-stack-pointers top (+ 16 (allocation-sp world)) initialized)))

(defthm allocation-resumed-cons-world-agrees-with-runtime
  (let ((expected (allocation-resumed-cons-world before)))
    (implies (and (not (proof-world-stop before))
                  (allocation-cons-resumed-return-p before after))
             (and (allocation-same-heap-context-p expected after)
                  (equal (proof-stack-limit expected) (proof-stack-limit after))
                  (equal (proof-box-top expected) (proof-box-top after))
                  (equal (proof-heap-limit expected) (proof-heap-limit after)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-resumed-memory-after-initialization
                 (:instance allocation-word-register-range (register 25) (world after))
                 (:instance allocation-register-frame-member (register 23) (upper 30) (clobbers '(0 1 2 25 29 30)))
                 (:instance allocation-register-frame-member (register 24) (upper 30) (clobbers '(0 1 2 25 29 30)))
                 (:instance allocation-register-frame-member (register 26) (upper 30) (clobbers '(0 1 2 25 29 30)))
                 (:instance allocation-register-frame-member (register 27) (upper 30) (clobbers '(0 1 2 25 29 30))))
           :in-theory (e/d (allocation-same-heap-context-p)
                           (proof-register-frame-p allocation-cons-fields-p
                            allocation-word-register-range
                            allocation-store-word-changes-machine-memory
                            allocation-initialized-cell-world-machine
                            boymoo-model::a64-write-bytes)))))

(local
 (defthm allocation-live-layout-is-running
   (implies (proof-heap-layout-p world) (not (proof-world-stop world)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p mod)))))

(local
 (defthm allocation-cons-reload-address-from-root-count
   (implies (equal (proof-stack-top before) (+ (proof-stack-base before) (* 8 index) 16))
            (equal (allocation-cons-reload-address before) (+ (proof-stack-base before) (* 8 index))))
   :rule-classes nil))

(local
 (defthm allocation-cons-restored-pointers-are-valid
   (let* ((top (allocation-cons-reload-address before))
          (sp (+ 16 (allocation-sp before)))
          (machine-start (- (proof-machine-limit before) *proof-machine-margin*))
          (machine-end (+ machine-start *proof-machine-reservation*)))
     (implies (and (proof-heap-layout-p before)
                   (natp index)
                   (equal (proof-stack-top before) (+ (proof-stack-base before) (* 8 index) 16))
                   (<= sp machine-end) (< sp *allocation-word-modulus*))
              (and (unsigned-byte-p 64 top) (equal (mod top 8) 0)
                   (<= (proof-stack-base before) top) (<= top (proof-stack-top before))
                   (unsigned-byte-p 64 sp) (equal (mod sp 16) 0)
                   (<= machine-start sp))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-word-register-range (register 25) (world before))
                  (:instance allocation-aligned-eight-sum (first (proof-stack-top before)) (second -16)))
            :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                                proof-static-size proof-page-size-p allocation-word-register-range mod)))))

(defthm allocation-resumed-cell-heap-with-shorter-stack
  (let* ((top (allocation-cons-reload-address before))
         (sp (+ 16 (allocation-sp before)))
         (limit (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
         (cell (proof-world-reg 0 before))
         (full (proof-stack-prefix (proof-stack-top before) before objects packages))
         (expected (allocation-resumed-cons-world before)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-reserved-span-p :cons cell 16 before objects)
                  (natp index) (equal (proof-stack-top before) (+ (proof-stack-base before) (* 8 index) 16))
                  (<= sp limit) (< sp *allocation-word-modulus*))
             (and (proof-heap-p expected objects packages)
                  (equal (proof-stack-prefix top expected objects packages)
                         (cons :slots (take index (cdr full))))
                  (equal (proof-dynamic-view expected objects packages) (proof-dynamic-view before objects packages))
                  (equal (proof-cons-floor expected) (proof-cons-floor before))
                  (equal (proof-active-end expected) (proof-active-end before)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-restored-pointers-are-valid
                 allocation-cons-reload-address-from-root-count
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-heap-stack-prefix-exists (world before))
                 (:instance allocation-stack-prefix-without-two-roots (world before))
                 (:instance allocation-initializing-cell-keeps-old-heap
                  (world before) (address (proof-world-reg 0 before))
                  (first (allocation-load-word (allocation-cons-reload-address before) before))
                  (second (allocation-load-word (+ 8 (allocation-cons-reload-address before)) before))
                  (top (allocation-cons-reload-address before)))
                 (:instance allocation-heap-after-stack-pointer-update
                  (world (allocation-initialized-cell-world
                          (proof-world-reg 0 before)
                          (allocation-load-word (allocation-cons-reload-address before) before)
                          (allocation-load-word (+ 8 (allocation-cons-reload-address before)) before)
                          before))
                  (top (allocation-cons-reload-address before)) (sp (+ 16 (allocation-sp before)))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-p proof-heap-layout-p proof-reserved-span-p proof-stack-prefix
                            proof-dynamic-view proof-view proof-load-word allocation-cons-reload-address
                            allocation-world-with-stack-pointers mod ash)))))

(defthm allocation-resumed-cons-initialized-heap
  (let* ((top (allocation-cons-reload-address before))
         (sp (+ 16 (allocation-sp before)))
         (limit (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
         (cell (proof-world-reg 0 before))
         (full (proof-stack-prefix (proof-stack-top before) before objects packages)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-reserved-span-p :cons cell 16 before objects)
                  (natp index) (equal (proof-stack-top before) (+ (proof-stack-base before) (* 8 index) 16))
                  (<= sp limit) (< sp *allocation-word-modulus*)
                  (allocation-cons-resumed-return-p before after))
             (and (proof-heap-p after objects packages)
                  (equal (proof-stack-prefix top after objects packages)
                         (cons :slots (take index (cdr full))))
                  (equal (proof-dynamic-view after objects packages) (proof-dynamic-view before objects packages))
                  (proof-subspan-p cell 16 (proof-cons-floor after) (proof-active-end after))
                  (equal (mod cell 16) 0)
                  (not (assoc-equal cell objects)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-resumed-cons-world-agrees-with-runtime allocation-resumed-cell-heap-with-shorter-stack
                 (:instance allocation-heap-under-same-context-and-frontiers (before (allocation-resumed-cons-world before)))
                 (:instance allocation-reserved-cell-write-addresses (world before) (address (proof-world-reg 0 before)))
                 (:instance allocation-reserved-cell-avoids-published-objects (world before) (address (proof-world-reg 0 before)))
                 (:instance allocation-layout-of-heap (world before)))
           :in-theory (disable allocation-resumed-cons-world proof-heap-p proof-heap-layout-p proof-reserved-span-p
                               allocation-cons-resumed-return-p proof-stack-prefix proof-dynamic-view
                               proof-subspan-p allocation-runtime-word-as-load proof-runtime-word
                               proof-span-p allocation-objects-outside-write-p mod))))

(local
 (defthm allocation-live-heap-has-dynamic-view
   (implies (proof-heap-p world objects packages) (proof-dynamic-view world objects packages))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p
                                      proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                                      proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                                      proof-stack-prefix)))))

(defthm allocation-resumed-cons-admits-published-heap
  (let* ((top (allocation-cons-reload-address before))
         (sp (+ 16 (allocation-sp before)))
         (limit (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
         (cell (proof-world-reg 0 before))
         (full (proof-stack-prefix (proof-stack-top before) before objects packages))
         (published (cons (proof-object cell :active :cons rank) objects)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-reserved-span-p :cons cell 16 before objects)
                  (natp index) (equal (proof-stack-top before) (+ (proof-stack-base before) (* 8 index) 16))
                  (<= sp limit) (< sp *allocation-word-modulus*)
                  (allocation-cons-resumed-return-p before after)
                  (proof-object-map-p published published nil (proof-heap-base after)
                                      packages (proof-world-machine after)))
             (and (proof-heap-p after published packages)
                  (equal (proof-stack-prefix top after published packages)
                         (cons :slots (take index (cdr full))))
                  (proof-dynamic-table-preserved-p nil before after objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-resumed-cons-initialized-heap
                 (:instance allocation-live-heap-has-dynamic-view (world after))
                 (:instance allocation-published-cons-admits-heap (world after) (address (proof-world-reg 0 before))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-map-p proof-stack-prefix
                               proof-stack-base proof-stack-top proof-dynamic-view proof-reserved-span-p
                               allocation-cons-resumed-return-p proof-cons-floor proof-active-end
                               proof-subspan-p allocation-cons-reload-address mod))))

(local
 (defthm allocation-cons-allocator-heap-and-spans
   (implies (proof-allocator-return-p :cons 16 rooted reserved old-objects objects packages)
            (and (proof-heap-p reserved objects packages)
                 (proof-reserved-span-p :cons (proof-world-reg 0 reserved) 16 reserved objects)
                 (proof-span-p (proof-world-reg 0 reserved) 16)
                 (equal (proof-machine-limit reserved) (proof-machine-limit rooted))
                 (not (proof-world-stop reserved))
                 (proof-dynamic-table-preserved-p nil rooted reserved old-objects objects packages)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-register-frame-member
                   (before rooted) (after reserved) (register 23) (upper 30)
                   (clobbers (append *proof-volatile-registers* '(26 27)))))
            :in-theory (disable proof-heap-p proof-span-p proof-heap-frame-p proof-register-frame-p
                                proof-prefix-preserved-p proof-dynamic-table-preserved-p
                                proof-object-disjoint-p proof-active-end proof-cons-floor)))))

(local
 (defthm allocation-cons-resumed-return-keeps-heap-base
   (implies (allocation-cons-resumed-return-p before after)
            (equal (proof-heap-base after) (proof-heap-base before)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable allocation-cons-fields-p proof-register-frame-p proof-streams-preserved-p)))))

(defthm allocation-cons-checked-heap-continuation
  (let* ((save (allocation-sp rooted))
         (top (proof-stack-top rooted))
         (slot (- top 16))
         (link (allocation-load-word (+ 8 save) rooted))
         (cuts (list link))
         (cell (proof-world-reg 0 reserved))
         (base (proof-heap-base reserved))
         (machine-end (+ (- (proof-machine-limit rooted) *proof-machine-margin*) *proof-machine-reservation*))
         (published (cons (proof-object cell :active :cons rank) objects)))
    (implies (and (natp index) (equal top (+ (proof-stack-base rooted) (* 8 index) 16))
                  (proof-machine-value-p (allocation-load-word slot rooted) left rooted old-objects packages)
                  (proof-machine-value-p (allocation-load-word (+ slot 8) rooted) right rooted old-objects packages)
                  (proof-allocator-return-p :cons 16 rooted reserved old-objects objects packages)
                  (proof-subspan-p save 16 save machine-end) (< (+ save 16) *allocation-word-modulus*)
                  (proof-disjoint-p cell (+ cell 16) save (+ save 16))
                  (allocation-machine-state-p reserved)
                  (equal (mod cell 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth (allocation-load-word slot reserved) base objects) rank)
                  (<= (allocation-word-depth (allocation-load-word (+ slot 8) reserved) base objects) rank)
                  (allocation-path-ready-p *allocation-cons-return-path* cuts reserved)
                  (equal after (allocation-path-end *allocation-cons-return-path* reserved)))
             (and (proof-segment-p (len *allocation-cons-return-path*) cuts reserved :cut after)
                  (proof-heap-p after published packages)
                  (proof-reg-value-p 0 (cons left right) after published packages)
                  (equal (proof-stack-prefix slot after published packages)
                         (cons :slots (take index (cdr (proof-stack-prefix top rooted old-objects packages)))))
                  (proof-dynamic-table-preserved-p nil rooted after old-objects published packages)
                  (equal (proof-world-reg 29 after) (allocation-load-word save rooted))
                  (equal (proof-world-reg 30 after) link))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-checked-publication-after-allocator allocation-cons-save-record-survives-allocator
                 allocation-cons-allocator-heap-and-spans
                 (:instance allocation-allocator-stack-prefix
                  (kind :cons) (bytes 16) (before rooted) (after reserved) (new-objects objects))
                 (:instance allocation-cons-checked-resumed-return (before reserved))
                 (:instance allocation-cons-resumed-return-keeps-heap-base (before reserved))
                 (:instance allocation-resumed-cons-admits-published-heap (before reserved)))
           :in-theory (disable allocation-path-end allocation-path-ready-p proof-segment-p proof-heap-p
                               proof-allocator-return-p allocation-cons-resumed-return-p proof-reserved-span-p
                               proof-span-p proof-heap-base
                               proof-stack-base proof-stack-top proof-stack-prefix proof-object-map-p
                               proof-reg-value-p proof-machine-value-p proof-dynamic-view
                               allocation-word-depth proof-disjoint-p mod))))
