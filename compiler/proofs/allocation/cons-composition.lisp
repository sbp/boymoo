(in-package "BOYMOO-PROOFS")

(include-book "cons-growth-boundary")
(include-book "memory-keys")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-cons-room-and-caller-frame-place-saves
   (let* ((save (- (allocation-sp caller) 16))
          (machine-end (+ (- (proof-machine-limit rooted) *proof-machine-margin*) *proof-machine-reservation*)))
     (implies (and (allocation-cons-prologue-room-p caller)
                   (allocation-cons-rooted-caller-frame-p caller rooted))
              (and (equal (allocation-sp rooted) save)
                   (proof-span-p save 16)
                   (proof-subspan-p save 16 save machine-end)
                   (< (+ save 16) *allocation-word-modulus*)
                   (< (+ (proof-stack-top caller) 16) *allocation-word-modulus*)
                   (equal (proof-stack-top rooted) (+ (proof-stack-top caller) 16))
                   (equal (- (proof-stack-top rooted) 16) (proof-stack-top caller)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-word-register-range (world caller) (register 0)))
            :in-theory (e/d (allocation-cons-prologue-room-p allocation-cons-rooted-caller-frame-p
                             unsigned-byte-p acl2::integer-range-p)
                            (proof-register-frame-p proof-stack-end allocation-word-register-range))))))

(local
 (defthm allocation-cons-heap-frame-keeps-old-stack-base
   (implies (proof-heap-frame-p caller rooted)
            (equal (proof-stack-base rooted) (proof-stack-base caller)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-memory-span-agrees-p proof-streams-preserved-p
                                      proof-stack-end proof-spaces-end proof-heap-base)))))

(defthm allocation-cons-prologue-sets-up-caller-heap-frame
  (let* ((top (proof-stack-top caller))
         (required (+ 16 top))
         (grow-path (allocation-growth-path "rt:ensure-stack" required cut))
         (stack (proof-stack-base caller))
         (save (- (allocation-sp caller) 16))
         (machine-start (- (proof-machine-limit rooted) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (proof-heap-p caller objects packages)
                  (allocation-cons-prologue-room-p caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (proof-reg-value-p 0 left caller objects packages)
                  (proof-reg-value-p 1 right caller objects packages)
                  (natp index) (equal top (+ stack (* 8 index)))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (allocation-growth-machine-pre-p "rt:ensure-stack" required origin cut)
                  (<= required (proof-stack-end cut))
                  (or (<= required (proof-stack-limit cut)) (allocation-growth-doubling-fits-p cut))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown)))
             (and (allocation-cons-rooted-caller-frame-p caller rooted)
                  (proof-heap-frame-p caller rooted)
                  (proof-prefix-preserved-p top caller rooted objects objects packages)
                  (proof-dynamic-table-preserved-p nil caller rooted objects objects packages)
                  (equal (proof-stack-top rooted) (+ 16 (proof-stack-base rooted) (* 8 index)))
                  (equal (- (proof-stack-top rooted) 16) top)
                  (proof-machine-value-p (allocation-load-word top rooted) left rooted objects packages)
                  (proof-machine-value-p (allocation-load-word (+ 8 top) rooted) right rooted objects packages)
                  (equal (allocation-sp rooted) save)
                  (proof-subspan-p save 16 save machine-end)
                  (< (+ save 16) *allocation-word-modulus*))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-effects allocation-cons-prologue-memory-footprint
                 allocation-cons-prologue-writes-in-unused-stack
                 allocation-cons-prologue-preserves-shared-heap-frame allocation-cons-prologue-preserves-live-stack
                 allocation-cons-prologue-preserves-dynamic-table allocation-cons-prologue-roots-represent-arguments
                 allocation-cons-room-and-caller-frame-place-saves allocation-cons-heap-frame-keeps-old-stack-base
                 (:instance allocation-layout-of-heap (world caller)))
           :in-theory (e/d (allocation-cons-prologue-room-p)
                           (allocation-path-end allocation-growth-path allocation-growth-machine-pre-p
                            allocation-cons-machine-entry-p proof-allocation-fits-p
                            allocation-growth-doubling-fits-p proof-heap-p proof-heap-layout-p proof-reg-value-p
                            proof-machine-value-p proof-stack-base proof-stack-end proof-stack-limit proof-register-frame-p
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p allocation-cons-fields-p
                            allocation-cons-prologue-writes allocation-write-words proof-heap-frame-p proof-memory-span-agrees-p
                            proof-streams-preserved-p proof-disjoint-p proof-span-p proof-subspan-p)))))

(defthm allocation-cons-executed-prologue-with-allocator
  (let* ((grow-path (allocation-growth-path "rt:ensure-stack" (+ 16 (proof-stack-top caller)) cut))
         (path (allocation-cons-prologue-path caller cut))
         (cuts (list (proof-world-reg 30 caller))))
    (implies (and (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown))
                  (allocation-path-ready-p path cuts caller)
                  (natp allocator-steps)
                  (allocation-prefix-p allocator-steps cuts rooted reserved))
             (allocation-prefix-p (+ (len path) allocator-steps) cuts caller reserved)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-path-end-of-append
                  (first *allocation-cons-growth-path*)
                  (last (append (allocation-growth-path "rt:ensure-stack" (+ 16 (proof-stack-top caller)) cut)
                                *allocation-cons-root-path*))
                  (world caller))
                 (:instance allocation-path-end-of-append
                  (first (allocation-growth-path "rt:ensure-stack" (+ 16 (proof-stack-top caller)) cut))
                  (last *allocation-cons-root-path*) (world cut))
                 (:instance allocation-prefix-from-path
                  (path (allocation-cons-prologue-path caller cut)) (before caller) (cuts (list (proof-world-reg 30 caller))))
                 (:instance allocation-prefix-after-prefix
                  (first-steps (len (allocation-cons-prologue-path caller cut))) (last-steps allocator-steps)
                  (cuts (list (proof-world-reg 30 caller))) (before caller) (middle rooted) (after reserved)))
           :in-theory (disable allocation-prefix-p allocation-prefix-from-path allocation-path-ready-p
                               allocation-path-end allocation-path-end-of-append allocation-growth-path))))

(defthm allocation-cons-checked-runtime-return-through-allocator
  (let* ((top (proof-stack-top caller))
         (required (+ 16 top))
         (save (- (allocation-sp caller) 16))
         (grow-path (allocation-growth-path "rt:ensure-stack" required cut))
         (path (allocation-cons-prologue-path caller cut))
         (cell (proof-world-reg 0 reserved))
         (base (proof-heap-base reserved))
         (cuts (list (proof-world-reg 30 caller)))
         (published (cons (proof-object cell :active :cons rank) reserved-objects)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (proof-heap-p caller objects packages)
                  (allocation-cons-prologue-room-p caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (proof-reg-value-p 0 left caller objects packages)
                  (proof-reg-value-p 1 right caller objects packages)
                  (natp index) (equal top (+ (proof-stack-base caller) (* 8 index)))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (<= (proof-stack-end caller) (expt 2 63))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown))
                  (allocation-path-ready-p path cuts caller)
                  (natp allocator-steps)
                  (allocation-prefix-p allocator-steps cuts rooted reserved)
                  (proof-allocator-return-p :cons 16 rooted reserved objects reserved-objects packages)
                  (allocation-machine-state-p reserved)
                  (proof-disjoint-p cell (+ 16 cell) save (+ 16 save))
                  (equal (mod cell 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth (allocation-load-word top reserved) base reserved-objects) rank)
                  (<= (allocation-word-depth (allocation-load-word (+ 8 top) reserved) base reserved-objects) rank)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (allocation-path-ready-p *allocation-cons-return-path* cuts reserved)
                  (equal after (allocation-path-end *allocation-cons-return-path* reserved)))
             (and (proof-segment-p (+ (len path) allocator-steps (len *allocation-cons-return-path*))
                                   cuts caller :cut after)
                  (proof-runtime-return-p 'cons (list left right) program caller after objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 allocation-cons-growth-premises-from-linux-layout
                 allocation-cons-prologue-sets-up-caller-heap-frame allocation-cons-executed-prologue-with-allocator
                 (:instance allocation-executed-prefix-preserves-word-address-keys
                  (before caller) (after reserved) (cuts (list (proof-world-reg 30 caller)))
                  (steps (+ (len (allocation-cons-prologue-path caller cut)) allocator-steps)))
                 (:instance allocation-checked-path-preserves-word-address-keys
                  (before reserved) (path *allocation-cons-return-path*) (cuts (list (proof-world-reg 30 caller))))
                 (:instance allocation-cons-checked-runtime-return-from-roots
                  (old-objects objects) (root-objects objects) (objects reserved-objects)
                  (prefix-steps (+ (len (allocation-cons-prologue-path caller cut)) allocator-steps))))
           :in-theory (disable allocation-cons-rooted-caller-frame-p allocation-cons-prologue-path
                               allocation-path-end allocation-path-ready-p allocation-growth-path
                               allocation-prefix-p proof-segment-p proof-runtime-return-p proof-heap-p proof-heap-frame-p
                               proof-heap-layout-p allocation-growth-machine-pre-p allocation-growth-doubling-fits-p
                               proof-allocator-return-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                               proof-machine-value-p proof-reg-value-p proof-register-frame-p proof-span-p proof-subspan-p
                               proof-heap-base proof-stack-base proof-stack-top proof-disjoint-p allocation-word-depth
                               allocation-memory-addresses-are-words-p mod))))
