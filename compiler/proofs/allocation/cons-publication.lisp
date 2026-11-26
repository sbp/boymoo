(in-package "BOYMOO-PROOFS")

(include-book "cons-contracts")
(include-book "fast-contracts")
(include-book "saved-words")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-objects-outside-subspan
  (implies (and (allocation-objects-outside-write-p start end objects machine)
                (<= start lower) (<= upper end))
           (allocation-objects-outside-write-p lower upper objects machine))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-objects-outside-write-p start end objects machine)
           :in-theory (disable proof-object-size proof-span-p))))

(defthm allocation-other-object-spans-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine))
           (equal (allocation-objects-outside-write-p lower upper objects
                                                     (boymoo-model::a64-store bytes start value machine))
                  (allocation-objects-outside-write-p lower upper objects machine)))
  :hints (("Goal" :induct (allocation-objects-outside-write-p start (+ start bytes) objects machine)
           :in-theory (disable boymoo-model::a64-store proof-object-size proof-span-p proof-disjoint-p))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write (object (car objects)))))))

(defthm allocation-objects-outside-pair-write
  (let ((middle (boymoo-model::a64-store 8 start first machine)))
    (implies (and (proof-span-p start 16)
                  (allocation-objects-outside-write-p start (+ start 16) objects machine))
             (and (proof-span-p start 8)
                  (proof-span-p (+ start 8) 8)
                  (allocation-objects-outside-write-p start (+ start 8) objects machine)
                  (allocation-objects-outside-write-p (+ start 8) (+ start 16) objects middle)
                  (allocation-objects-outside-write-p start (+ start 16) objects middle))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-objects-outside-subspan
                         (end (+ start 16)) (lower start) (upper (+ start 8)))
                        (:instance allocation-objects-outside-subspan
                         (end (+ start 16)) (lower (+ start 8)) (upper (+ start 16))))
           :in-theory (disable boymoo-model::a64-store allocation-objects-outside-write-p))))

(defun allocation-store-cell (address first second machine)
  (boymoo-model::a64-store 8 (+ address 8) second
                           (boymoo-model::a64-store 8 address first machine)))

(defthm allocation-cell-store-keeps-object-map
  (implies (and (proof-span-p start 16)
                (allocation-objects-outside-write-p start (+ start 16) objects machine)
                (proof-object-map-p objects objects nil base packages machine))
           (proof-object-map-p objects objects nil base packages
                               (allocation-store-cell start first second machine)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-objects-outside-pair-write
                 (:instance allocation-object-map-after-disjoint-write
                  (bytes 8) (value first) (pending objects) (symbols nil))
                 (:instance allocation-object-map-after-disjoint-write
                  (start (+ start 8)) (bytes 8) (value second) (pending objects) (symbols nil)
                  (machine (boymoo-model::a64-store 8 start first machine))))
           :in-theory (disable proof-object-map-p allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))))

(defthm allocation-cell-store-keeps-old-views
  (implies (and (proof-span-p start 16)
                (allocation-objects-outside-write-p start (+ start 16) objects machine))
           (equal (proof-view word base objects packages (allocation-store-cell start first second machine))
                  (proof-view word base objects packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-objects-outside-pair-write
                 (:instance allocation-view-after-disjoint-write (bytes 8) (value first))
                 (:instance allocation-view-after-disjoint-write
                  (start (+ start 8)) (bytes 8) (value second)
                  (machine (boymoo-model::a64-store 8 start first machine))))
           :in-theory (disable proof-view allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))))

(defthm allocation-object-spans-outside-write-are-disjoint
  (implies (allocation-objects-outside-write-p start end objects machine)
           (proof-object-disjoint-p start end objects machine))
  :hints (("Goal" :induct (allocation-objects-outside-write-p start end objects machine)
           :in-theory (disable proof-object-size proof-span-p proof-disjoint-p))))

(defthm allocation-cell-store-keeps-span-disjoint
  (implies (and (proof-span-p start 16)
                (allocation-objects-outside-write-p start (+ start 16) objects machine))
           (proof-object-disjoint-p start (+ start 16) objects (allocation-store-cell start first second machine)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-objects-outside-pair-write
                 (:instance allocation-object-disjointness-after-write
                  (address start) (end (+ start 16)) (bytes 8) (value first))
                 (:instance allocation-object-disjointness-after-write
                  (address start) (end (+ start 16)) (start (+ start 8)) (bytes 8) (value second)
                  (machine (boymoo-model::a64-store 8 start first machine))))
           :in-theory (disable allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))))

(local
 (defthm allocation-object-size-positive
   (posp (proof-object-size object machine))
   :rule-classes :type-prescription
   :hints (("Goal"
            :use ((:instance allocation-align-up-bounds (alignment 8)
                   (size (proof-header-size (proof-load-word (proof-object-address object) machine)))))
            :in-theory (disable proof-load-word proof-header-size proof-align-up)))))

(defthm allocation-cell-span-excludes-existing-address
  (implies (allocation-objects-outside-write-p address (+ address 16) objects machine)
           (not (assoc-equal address objects)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-lookup-object-outside-write (start address) (end (+ address 16))))
           :in-theory (disable allocation-objects-outside-write-p proof-object-size))))

(defthm allocation-cell-store-reads-fields
  (let ((updated (allocation-store-cell address first second machine)))
    (implies (and (proof-span-p address 16)
                  (unsigned-byte-p 64 first) (unsigned-byte-p 64 second))
             (and (equal (proof-load-word address updated) first)
                  (equal (proof-load-word (+ 8 address) updated) second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-load-word-after-disjoint-write
                  (start (+ 8 address)) (bytes 8) (value second) (machine (boymoo-model::a64-store 8 address first machine))))
           :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                           (allocation-load-word-after-disjoint-write boymoo-model::a64-read-bytes
                            boymoo-model::a64-write-bytes)))))

(defthm allocation-initialize-and-publish-cell
  (let* ((updated (allocation-store-cell start first second machine))
         (record (proof-object start :active :cons rank))
         (published (cons record objects)))
    (implies (and (proof-span-p start 16) (unsigned-byte-p 64 base)
                  (unsigned-byte-p 64 first) (unsigned-byte-p 64 second)
                  (equal (mod start 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth first base objects) rank)
                  (<= (allocation-word-depth second base objects) rank)
                  (allocation-objects-outside-write-p start (+ start 16) objects machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-value-p first left base objects packages machine)
                  (proof-value-p second right base objects packages machine))
             (and (proof-object-map-p published published nil base packages updated)
                  (proof-value-p (proof-object-word record base) (cons left right)
                                 base published packages updated))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cell-store-keeps-object-map allocation-cell-store-keeps-span-disjoint
                 (:instance allocation-cell-span-excludes-existing-address (address start))
                 (:instance allocation-cell-store-reads-fields (address start))
                 (:instance allocation-cell-store-keeps-old-views (word first))
                 (:instance allocation-cell-store-keeps-old-views (word second))
                 (:instance allocation-publish-initialized-cons
                  (address start) (machine (allocation-store-cell start first second machine))))
           :in-theory (disable allocation-store-cell allocation-objects-outside-write-p proof-object-map-p
                               proof-object-disjoint-p proof-span-p proof-load-word proof-view
                               proof-object-word allocation-word-depth mod))))

(defthm allocation-cons-resumed-memory-after-initialization
  (let* ((start (proof-world-reg 0 before))
         (root (allocation-cons-reload-address before))
         (first (allocation-load-word root before))
         (second (allocation-load-word (+ root 8) before)))
    (implies (allocation-cons-resumed-return-p before after)
             (allocation-same-memory-p (proof-world-machine after)
                                       (allocation-store-cell start first second (proof-world-machine before)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (allocation-same-memory-p)
                                  (proof-streams-preserved-p allocation-cons-fields-p proof-register-frame-p
                                   proof-world-reg boymoo-model::a64-write-bytes)))))

(local
 (defthm allocation-cons-heap-base-range
   (unsigned-byte-p 64 (proof-heap-base world))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use ((:instance allocation-word-register-range (register 28)))
            :in-theory (disable allocation-word-register-range)))))

(local
 (defthm allocation-cons-root-stack-base-natural
   (natp (proof-stack-base world))
   :rule-classes :type-prescription))

(defthm allocation-cons-resumed-publishes-cell
  (let* ((start (proof-world-reg 0 before))
         (root (allocation-cons-reload-address before))
         (first (allocation-load-word root before))
         (second (allocation-load-word (+ root 8) before))
         (base (proof-heap-base before))
         (published (cons (proof-object start :active :cons rank) objects)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-reserved-span-p :cons start 16 before objects)
                  (allocation-cons-resumed-return-p before after)
                  (equal (mod start 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth first base objects) rank)
                  (<= (allocation-word-depth second base objects) rank)
                  (proof-machine-value-p first left before objects packages)
                  (proof-machine-value-p second right before objects packages))
             (and (proof-object-map-p published published nil base packages (proof-world-machine after))
                  (proof-reg-value-p 0 (cons left right) after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-resumed-memory-after-initialization
                 (:instance allocation-heap-published-map (world before))
                 (:instance allocation-object-map-with-disjoint-spans
                  (pending objects) (symbols nil) (base (proof-heap-base before)) (machine (proof-world-machine before))
                  (start (proof-world-reg 0 before)) (end (+ 16 (proof-world-reg 0 before))))
                 (:instance allocation-initialize-and-publish-cell
                  (start (proof-world-reg 0 before)) (base (proof-heap-base before)) (machine (proof-world-machine before))
                  (first (allocation-load-word (allocation-cons-reload-address before) before))
                  (second (allocation-load-word (+ 8 (allocation-cons-reload-address before)) before))))
           :in-theory (disable proof-heap-p proof-object-map-p allocation-objects-outside-write-p
                               proof-object-disjoint-p proof-span-p proof-world-machine proof-heap-base
                               proof-cons-floor proof-active-end proof-view allocation-word-depth
                               allocation-store-cell proof-streams-preserved-p
                               proof-register-frame-p allocation-cons-fields-p boymoo-model::a64-unsigned
                               allocation-unsigned-64-of-difference mod))))

(defthm allocation-cons-save-record-survives-allocator
  (let* ((save (allocation-sp rooted))
         (machine-end (+ (- (proof-machine-limit rooted) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (proof-allocator-return-p :cons 16 rooted reserved old-objects objects packages)
                  (proof-subspan-p save 16 save machine-end))
             (and (equal (allocation-sp reserved) save)
                  (equal (allocation-load-word save reserved) (allocation-load-word save rooted))
                  (equal (allocation-load-word (+ save 8) reserved) (allocation-load-word (+ save 8) rooted)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-allocator-preserves-saved-word
                  (kind :cons) (bytes 16) (before rooted) (after reserved) (new-objects objects)
                  (address (allocation-sp rooted)))
                 (:instance allocation-allocator-preserves-saved-word
                  (kind :cons) (bytes 16) (before rooted) (after reserved) (new-objects objects)
                  (address (+ 8 (allocation-sp rooted)))))
           :in-theory (disable proof-heap-p proof-heap-frame-p proof-reserved-span-p
                               proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-machine-limit))))

(local
 (defthm allocation-cons-allocator-output-facts
   (implies (proof-allocator-return-p :cons 16 rooted reserved old-objects objects packages)
            (and (proof-heap-p reserved objects packages)
                 (proof-reserved-span-p :cons (proof-world-reg 0 reserved) 16 reserved objects)
                 (proof-span-p (proof-world-reg 0 reserved) 16)
                 (not (proof-world-stop reserved))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-heap-p proof-span-p proof-heap-frame-p
                                      proof-register-frame-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                                      proof-object-disjoint-p proof-active-end proof-cons-floor)))))

(local
 (defthm allocation-cons-resumed-pop-and-restore
   (implies (allocation-cons-resumed-return-p before after)
            (and (equal (proof-stack-top after) (allocation-cons-reload-address before))
                 (equal (allocation-sp after) (+ (allocation-sp before) 16))
                 (equal (proof-world-reg 29 after) (allocation-load-word (allocation-sp before) before))
                 (equal (proof-world-reg 30 after) (allocation-load-word (+ (allocation-sp before) 8) before))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable allocation-cons-fields-p proof-register-frame-p proof-streams-preserved-p)))))

(defthm allocation-cons-checked-publication-after-allocator
  (let* ((save (allocation-sp rooted))
         (top (proof-stack-top rooted))
         (slot (- top 16))
         (link (allocation-load-word (+ save 8) rooted))
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
                  (proof-object-map-p published published nil base packages (proof-world-machine after))
                  (proof-reg-value-p 0 (cons left right) after published packages)
                  (equal (proof-stack-top after) slot)
                  (equal (allocation-sp after) (+ save 16))
                  (equal (proof-world-reg 29 after) (allocation-load-word save rooted))
                  (equal (proof-world-reg 30 after) link))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-save-record-survives-allocator allocation-cons-allocator-output-facts
                 (:instance allocation-allocator-stack-prefix
                  (kind :cons) (bytes 16) (before rooted) (after reserved) (new-objects objects))
                 (:instance allocation-cons-two-roots-after-allocator
                  (before rooted) (after reserved) (new-objects objects))
                 (:instance allocation-cons-checked-resumed-return (before reserved))
                 (:instance allocation-cons-resumed-pop-and-restore (before reserved))
                 (:instance allocation-cons-resumed-publishes-cell (before reserved)))
           :in-theory (disable allocation-path-end allocation-path-ready-p proof-segment-p proof-heap-p
                               allocation-cons-resumed-return-p proof-allocator-return-p
                               proof-heap-frame-p proof-prefix-preserved-p
                               proof-dynamic-table-preserved-p proof-reserved-span-p proof-disjoint-p
                               proof-view proof-value-p proof-reg-value-p proof-machine-value-p proof-object-map-p
                               proof-stack-base proof-stack-top proof-heap-base proof-machine-limit proof-span-p
                               allocation-word-depth allocation-cons-reload-address allocation-cons-fields-p
                               proof-streams-preserved-p proof-register-frame-p boymoo-model::a64-unsigned mod))))
