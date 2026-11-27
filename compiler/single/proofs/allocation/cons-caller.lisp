(in-package "BOYMOO-PROOFS")

(include-book "cons-tail")
(include-book "frame-composition")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-cons-resumed-writes (before)
  (let ((cell (proof-world-reg 0 before))
        (root (allocation-cons-reload-address before)))
    (list (cons cell (allocation-load-word root before))
          (cons (+ 8 cell) (allocation-load-word (+ 8 root) before)))))

(defthm allocation-cons-resumed-write-footprint
  (implies (allocation-cons-resumed-return-p before after)
           (equal (allocation-memory after)
                  (allocation-memory (allocation-write-words (allocation-cons-resumed-writes before) before))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-cons-fields-p proof-register-frame-p
                                     proof-streams-preserved-p boymoo-model::a64-write-bytes))))

(defthm allocation-cons-resumed-writes-avoid-frame
  (let* ((cell (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (static-end (+ base (proof-static-size base (proof-world-machine before))))
         (sp (allocation-sp before))
         (machine-end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
         (writes (allocation-cons-resumed-writes before)))
    (implies (and (proof-heap-layout-p before)
                  (proof-reserved-span-p :cons cell 16 before objects))
             (and (natp base) (<= (+ base 24) *allocation-word-modulus*)
                  (natp static-end) (<= static-end *allocation-word-modulus*)
                  (natp sp) (natp machine-end) (<= machine-end *allocation-word-modulus*)
                  (allocation-word-writes-avoid-span-p writes base (+ 24 base))
                  (allocation-word-writes-avoid-span-p writes (+ 32 base) static-end)
                  (allocation-word-writes-avoid-span-p writes sp machine-end))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-reserved-cell-write-addresses (world before) (address (proof-world-reg 0 before)))
                 (:instance allocation-active-word-store-bounds (world before) (address (proof-world-reg 0 before)))
                 (:instance allocation-active-word-store-bounds (world before) (address (+ 8 (proof-world-reg 0 before))))
                 (:instance allocation-word-register-range (register 28) (world before)))
           :in-theory (disable proof-heap-layout-p proof-reserved-span-p proof-static-size proof-machine-limit
                               proof-heap-base allocation-word-register-range mod))))

(local
 (defthm allocation-heap-layout-requires-running-world
   (implies (proof-heap-layout-p world) (not (proof-world-stop world)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p mod)))))

(local
 (defthm allocation-external-bounds-of-same-heap-context
   (implies (allocation-same-heap-context-p before after)
            (allocation-same-external-bounds-p before after))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-same-external-bounds-p)
                                   (proof-runtime-word allocation-runtime-word-as-load
                                    proof-heap-base proof-machine-limit))))))

(local
 (defthm allocation-stack-pointer-update-keeps-external-bounds
   (allocation-same-external-bounds-p world (allocation-world-with-stack-pointers top sp world))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable allocation-same-external-bounds-p)))))

(local
 (defthm allocation-external-bounds-transitive
   (implies (and (allocation-same-external-bounds-p before middle)
                 (allocation-same-external-bounds-p middle after))
            (allocation-same-external-bounds-p before after))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-same-external-bounds-p)
                                   (proof-heap-base proof-spaces-end proof-stack-base
                                    proof-stack-end proof-machine-limit))))))

(defthm allocation-cons-resumed-keeps-heap-bounds
  (let ((cell (proof-world-reg 0 before)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-reserved-span-p :cons cell 16 before objects)
                  (allocation-cons-resumed-return-p before after))
             (allocation-same-external-bounds-p before after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-resumed-cons-world-agrees-with-runtime
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-external-bounds-of-same-heap-context
                  (before (allocation-resumed-cons-world before)))
                 (:instance allocation-stack-pointer-update-keeps-external-bounds
                  (top (allocation-cons-reload-address before)) (sp (+ 16 (allocation-sp before)))
                  (world (allocation-initialized-cell-world
                          (proof-world-reg 0 before)
                          (allocation-load-word (allocation-cons-reload-address before) before)
                          (allocation-load-word (+ 8 (allocation-cons-reload-address before)) before)
                          before)))
                 (:instance allocation-initializing-cell-keeps-old-heap
                  (world before) (address (proof-world-reg 0 before)) (top (proof-stack-top before))
                  (first (allocation-load-word (allocation-cons-reload-address before) before))
                  (second (allocation-load-word (+ 8 (allocation-cons-reload-address before)) before)))
                 (:instance allocation-external-bounds-transitive
                  (middle (allocation-initialized-cell-world
                           (proof-world-reg 0 before)
                           (allocation-load-word (allocation-cons-reload-address before) before)
                           (allocation-load-word (+ 8 (allocation-cons-reload-address before)) before)
                           before))
                  (after (allocation-resumed-cons-world before)))
                 (:instance allocation-external-bounds-transitive
                  (middle (allocation-resumed-cons-world before))))
           :in-theory (disable proof-heap-layout-p proof-heap-p proof-reserved-span-p allocation-cons-resumed-return-p
                               proof-stack-top proof-stack-prefix proof-dynamic-view allocation-cons-reload-address
                               allocation-initialized-cell-world allocation-world-with-stack-pointers))))

(defthm allocation-cons-resumed-keeps-heap-frame
  (implies (and (proof-heap-p before objects packages)
                (proof-reserved-span-p :cons (proof-world-reg 0 before) 16 before objects)
                (allocation-cons-resumed-return-p before after))
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-resumed-write-footprint allocation-cons-resumed-keeps-heap-bounds
                 allocation-cons-resumed-writes-avoid-frame
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-cons-resumed-writes before)) (world before)
                  (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before))))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-cons-resumed-writes before)) (world before)
                  (lower (+ 32 (proof-heap-base before)))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-cons-resumed-writes before)) (world before)
                  (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-p proof-heap-layout-p proof-reserved-span-p proof-heap-base proof-static-size
                            proof-memory-span-agrees-p proof-streams-preserved-p proof-cons-floor
                            proof-register-frame-p allocation-cons-fields-p allocation-cons-resumed-writes
                            allocation-write-words allocation-word-writes-avoid-span-p boymoo-model::a64-write-bytes)))))

(defconst *allocation-cons-restored-registers* '(25 29 30))

(defconst *allocation-cons-clobbers-through-saves*
  (append *allocation-cons-restored-registers* (proof-runtime-clobbers 'cons)))

(defund allocation-cons-rooted-caller-frame-p (caller rooted)
  (let ((save (allocation-sp rooted)))
    (and (not (proof-world-stop caller))
         (equal (allocation-sp caller) (+ 16 save))
         (equal (proof-stack-top rooted) (+ 16 (proof-stack-top caller)))
         (equal (proof-machine-limit rooted) (proof-machine-limit caller))
         (equal (allocation-load-word save rooted) (proof-world-reg 29 caller))
         (equal (allocation-load-word (+ 8 save) rooted) (proof-world-reg 30 caller))
         (proof-register-frame-p 30 *allocation-cons-clobbers-through-saves* caller rooted))))

(local
 (defthm allocation-cons-allocator-frame-facts
   (implies (proof-allocator-return-p :cons 16 rooted reserved root-objects objects packages)
            (and (proof-heap-p reserved objects packages)
                 (proof-reserved-span-p :cons (proof-world-reg 0 reserved) 16 reserved objects)
                 (proof-span-p (proof-world-reg 0 reserved) 16)
                 (proof-heap-frame-p rooted reserved)
                 (proof-register-frame-p 30 (append *proof-volatile-registers* '(26 27)) rooted reserved)
                 (equal (proof-machine-limit reserved) (proof-machine-limit rooted))
                 (equal (allocation-sp reserved) (allocation-sp rooted))
                 (not (proof-world-stop reserved))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-register-frame-member
                   (before rooted) (after reserved) (register 23) (upper 30)
                   (clobbers (append *proof-volatile-registers* '(26 27)))))
            :in-theory (disable proof-heap-p proof-span-p proof-heap-frame-p proof-register-frame-p
                                proof-prefix-preserved-p proof-dynamic-table-preserved-p
                                proof-object-disjoint-p proof-active-end proof-cons-floor)))))

(defthm allocation-cons-epilogue-restores-original-registers
  (implies (and (allocation-cons-rooted-caller-frame-p caller rooted)
                (proof-allocator-return-p :cons 16 rooted reserved root-objects objects packages)
                (proof-subspan-p (allocation-sp rooted) 16 (allocation-sp rooted)
                                 (+ (- (proof-machine-limit rooted) *proof-machine-margin*) *proof-machine-reservation*))
                (allocation-cons-resumed-return-p reserved after))
           (proof-frame-return-p (proof-runtime-clobbers 'cons) t caller after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-allocator-frame-facts
                 (:instance allocation-cons-save-record-survives-allocator (old-objects root-objects))
                 (:instance allocation-allocator-stack-prefix
                  (kind :cons) (bytes 16) (before rooted) (after reserved) (old-objects root-objects) (new-objects objects))
                 (:instance allocation-register-frame-under-more-clobbers
                  (before rooted) (after reserved) (register 30)
                  (small (append *proof-volatile-registers* '(26 27))) (large *allocation-cons-clobbers-through-saves*))
                 (:instance allocation-register-frame-under-more-clobbers
                  (before reserved) (register 30) (small '(0 1 2 25 29 30))
                  (large *allocation-cons-clobbers-through-saves*))
                 (:instance allocation-register-frame-transitive
                  (before caller) (middle rooted) (after reserved) (register 30) (clobbers *allocation-cons-clobbers-through-saves*))
                 (:instance allocation-register-frame-transitive
                  (before caller) (middle reserved) (register 30) (clobbers *allocation-cons-clobbers-through-saves*))
                 (:instance allocation-register-frame-after-restoration
                  (before caller) (upper 30) (restored *allocation-cons-restored-registers*)
                  (clobbers (proof-runtime-clobbers 'cons))))
           :in-theory (e/d (allocation-cons-rooted-caller-frame-p)
                           (proof-allocator-return-p proof-heap-p proof-heap-frame-p proof-reserved-span-p proof-span-p
                            proof-prefix-preserved-p proof-register-frame-p proof-subspan-p allocation-cons-fields-p
                            proof-streams-preserved-p proof-dynamic-table-preserved-p boymoo-model::a64-write-bytes)))))

(defthm allocation-cons-epilogue-preserves-original-heap-frame
  (implies (and (allocation-cons-rooted-caller-frame-p caller rooted)
                (proof-heap-frame-p caller rooted)
                (proof-allocator-return-p :cons 16 rooted reserved root-objects objects packages)
                (allocation-cons-resumed-return-p reserved after)
                (proof-span-p (proof-heap-base caller) 8)
                (allocation-memory-addresses-are-words-p (allocation-memory caller))
                (allocation-memory-addresses-are-words-p (allocation-memory reserved))
                (allocation-memory-addresses-are-words-p (allocation-memory after)))
           (proof-heap-frame-p caller after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-allocator-frame-facts
                 (:instance allocation-cons-resumed-keeps-heap-frame (before reserved))
                 (:instance allocation-heap-frame-compose (before caller) (middle rooted) (after reserved))
                 (:instance allocation-heap-frame-compose (before caller) (middle reserved)))
           :in-theory (e/d (allocation-cons-rooted-caller-frame-p)
                           (proof-allocator-return-p allocation-cons-resumed-return-p proof-heap-p
                            proof-heap-frame-p proof-reserved-span-p proof-span-p proof-register-frame-p
                            allocation-memory-addresses-are-words-p proof-machine-limit proof-heap-base)))))

(local
 (defthm allocation-cons-caller-prefix-after-pop
   (let* ((top (proof-stack-top caller))
          (root-top (proof-stack-top rooted))
          (full (proof-stack-prefix root-top rooted root-objects packages)))
     (implies (and (natp index)
                   (equal root-top (+ (proof-stack-base rooted) (* 8 index) 16))
                   (equal root-top (+ top 16))
                   full
                   (proof-prefix-preserved-p top caller rooted old-objects root-objects packages)
                   (equal (proof-stack-prefix top after new-objects packages)
                          (cons :slots (take index (cdr full)))))
              (proof-prefix-preserved-p top caller after old-objects new-objects packages)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-stack-prefix-without-two-roots (world rooted) (objects root-objects)))
            :in-theory (disable proof-stack-base proof-stack-top proof-stack-prefix take)))))

(local
 (defthm allocation-stack-prefix-at-top-before-pair
   (implies (and (integerp top) (equal root-top (+ top 16)))
            (equal (proof-stack-prefix (- root-top 16) world objects packages)
                   (proof-stack-prefix top world objects packages)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-stack-prefix)))))

(defthm allocation-cons-runtime-return-after-publication
  (let* ((save (allocation-sp rooted))
         (top (proof-stack-top caller))
         (root-top (proof-stack-top rooted))
         (machine-end (+ (- (proof-machine-limit rooted) *proof-machine-margin*) *proof-machine-reservation*))
         (full (proof-stack-prefix root-top rooted root-objects packages)))
    (implies (and (allocation-cons-rooted-caller-frame-p caller rooted)
                  (proof-heap-frame-p caller rooted)
                  (proof-prefix-preserved-p top caller rooted old-objects root-objects packages)
                  (proof-dynamic-table-preserved-p nil caller rooted old-objects root-objects packages)
                  (proof-allocator-return-p :cons 16 rooted reserved root-objects objects packages)
                  (proof-subspan-p save 16 save machine-end)
                  (allocation-cons-resumed-return-p reserved after)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (allocation-memory-addresses-are-words-p (allocation-memory reserved))
                  (allocation-memory-addresses-are-words-p (allocation-memory after))
                  (natp index)
                  (equal root-top (+ (proof-stack-base rooted) (* 8 index) 16))
                  (proof-heap-p after new-objects packages)
                  (proof-reg-value-p 0 (cons left right) after new-objects packages)
                  (equal (proof-stack-prefix (- root-top 16) after new-objects packages)
                         (cons :slots (take index (cdr full))))
                  (proof-dynamic-table-preserved-p nil rooted after root-objects new-objects packages))
             (proof-runtime-return-p 'cons (list left right) program caller after old-objects new-objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-epilogue-restores-original-registers
                 allocation-cons-epilogue-preserves-original-heap-frame allocation-cons-caller-prefix-after-pop
                 (:instance allocation-stack-prefix-at-top-before-pair
                  (top (proof-stack-top caller)) (root-top (proof-stack-top rooted))
                  (world after) (objects new-objects))
                 (:instance allocation-allocator-stack-prefix (kind :cons) (bytes 16) (before rooted) (after reserved)
                            (old-objects root-objects) (new-objects objects)))
           :in-theory (e/d (boymoo-model::core-primitive allocation-cons-rooted-caller-frame-p)
                           (proof-allocator-return-p allocation-cons-resumed-return-p proof-heap-p
                            proof-heap-frame-p proof-frame-return-p proof-stack-top proof-stack-base
                            proof-stack-prefix proof-reg-value-p proof-register-frame-p proof-span-p
                            proof-subspan-p proof-dynamic-view allocation-memory-addresses-are-words-p)))))

(defthm allocation-cons-checked-runtime-return-from-roots
  (let* ((save (allocation-sp rooted))
         (top (proof-stack-top rooted))
         (slot (- top 16))
         (cuts (list (proof-world-reg 30 caller)))
         (cell (proof-world-reg 0 reserved))
         (base (proof-heap-base reserved))
         (machine-end (+ (- (proof-machine-limit rooted) *proof-machine-margin*) *proof-machine-reservation*))
         (published (cons (proof-object cell :active :cons rank) objects)))
    (implies (and (allocation-cons-rooted-caller-frame-p caller rooted)
                  (proof-heap-frame-p caller rooted)
                  (proof-prefix-preserved-p (proof-stack-top caller) caller rooted old-objects root-objects packages)
                  (proof-dynamic-table-preserved-p nil caller rooted old-objects root-objects packages)
                  (natp prefix-steps)
                  (allocation-prefix-p prefix-steps cuts caller reserved)
                  (natp index) (equal top (+ (proof-stack-base rooted) (* 8 index) 16))
                  (proof-machine-value-p (allocation-load-word slot rooted) left rooted root-objects packages)
                  (proof-machine-value-p (allocation-load-word (+ slot 8) rooted) right rooted root-objects packages)
                  (proof-allocator-return-p :cons 16 rooted reserved root-objects objects packages)
                  (proof-subspan-p save 16 save machine-end) (< (+ save 16) *allocation-word-modulus*)
                  (proof-disjoint-p cell (+ cell 16) save (+ save 16))
                  (allocation-machine-state-p reserved)
                  (equal (mod cell 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth (allocation-load-word slot reserved) base objects) rank)
                  (<= (allocation-word-depth (allocation-load-word (+ slot 8) reserved) base objects) rank)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (allocation-memory-addresses-are-words-p (allocation-memory reserved))
                  (allocation-memory-addresses-are-words-p (allocation-memory after))
                  (allocation-path-ready-p *allocation-cons-return-path* cuts reserved)
                  (equal after (allocation-path-end *allocation-cons-return-path* reserved)))
             (and (proof-segment-p (+ prefix-steps (len *allocation-cons-return-path*)) cuts caller :cut after)
                  (proof-runtime-return-p 'cons (list left right) program caller after old-objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-cons-checked-heap-continuation (old-objects root-objects))
                 allocation-cons-allocator-frame-facts
                 (:instance allocation-cons-save-record-survives-allocator (old-objects root-objects))
                 (:instance allocation-allocator-stack-prefix
                  (kind :cons) (bytes 16) (before rooted) (after reserved) (old-objects root-objects) (new-objects objects))
                 (:instance allocation-cons-checked-resumed-return (before reserved))
                 (:instance allocation-cons-runtime-return-after-publication
                  (new-objects (cons (proof-object (proof-world-reg 0 reserved) :active :cons rank) objects)))
                 (:instance allocation-segment-after-prefix
                  (count prefix-steps) (remaining (len *allocation-cons-return-path*)) (before caller) (middle reserved)
                  (cuts (list (proof-world-reg 30 caller))) (reason :cut)))
           :in-theory (e/d (allocation-cons-rooted-caller-frame-p)
                           (allocation-prefix-p allocation-path-end allocation-path-ready-p proof-segment-p
                            allocation-cons-resumed-return-p proof-runtime-return-p proof-allocator-return-p
                            proof-heap-p proof-heap-frame-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                            proof-stack-prefix proof-reg-value-p proof-machine-value-p proof-register-frame-p
                            proof-stack-top proof-stack-base proof-span-p proof-subspan-p
                            allocation-word-depth allocation-memory-addresses-are-words-p mod)))))
