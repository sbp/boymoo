(in-package "BOYMOO-PROOFS")

(include-book "cons-composition")
(include-book "stack-writes")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-cons-layout-stack-base-before-top
   (implies (proof-heap-layout-p caller)
            (<= (proof-stack-base caller) (proof-stack-top caller)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-align-up proof-regions-p proof-covered-p
                                      proof-disjoint-p proof-runtime-word mod)))))

(defthm allocation-cons-prologue-words-in-stacks
  (implies (and (proof-heap-layout-p caller)
                (allocation-cons-prologue-room-p caller))
           (allocation-stack-word-writes-p (allocation-cons-prologue-writes caller) caller))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-layout-stack-base-before-top
                 (:instance allocation-layout-storage-spans (world caller)))
           :in-theory (e/d (allocation-cons-prologue-room-p)
                           (proof-heap-layout-p proof-heap-base proof-static-size proof-spaces-end
                            proof-stack-base proof-stack-end proof-stack-top proof-machine-limit
                            proof-runtime-word allocation-runtime-word-as-load)))))

(local
 (defthm allocation-same-stack-limits-determine-growth
   (implies (and (equal (proof-stack-base caller) (proof-stack-base cut))
                 (equal (proof-stack-limit caller) (proof-stack-limit cut))
                 (equal (proof-stack-end caller) (proof-stack-end cut)))
            (equal (proof-grow-limit required caller) (proof-grow-limit required cut)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-stack-base proof-stack-end proof-stack-limit)))))

(local
 (defthm allocation-cons-growth-edge-keeps-top-and-link
   (implies (allocation-cons-growth-edge-p origin caller cut)
            (and (allocation-machine-state-p cut)
                 (equal (proof-world-reg 30 cut) (allocation-cons-address origin 14))
                 (equal (proof-stack-top cut) (proof-stack-top caller))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable allocation-cons-fields-p allocation-cons-address
                                      allocation-code-address proof-stack-top)))))

(defthm allocation-cons-prologue-sets-committed-stack-limit
  (let* ((top (proof-stack-top caller))
         (required (+ 16 top))
         (grow-path (allocation-growth-path "rt:ensure-stack" required cut)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (<= (proof-stack-end caller) (expt 2 63))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown)))
             (equal (proof-stack-limit rooted) (proof-grow-limit required caller))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-growth-cut-keeps-limits allocation-cons-growth-premises-from-linux-layout
                 allocation-cons-growth-edge-keeps-top-and-link
                 (:instance allocation-cons-ensure-stack-return-effects (required (+ 16 (proof-stack-top caller))))
                 (:instance allocation-same-stack-limits-determine-growth (required (+ 16 (proof-stack-top caller))))
                 (:instance allocation-cons-root-cut-effects (before grown) (cut rooted))
                 (:instance allocation-register-frame-member
                  (register 24) (upper 30) (clobbers '(0 25 30)) (before grown) (after rooted)))
           :in-theory (e/d (allocation-cons-prologue-room-p allocation-cons-machine-entry-p)
                           (allocation-growth-machine-pre-p allocation-growth-doubling-fits-p
                            allocation-growth-path allocation-path-end proof-allocation-fits-p proof-heap-layout-p
                            allocation-cons-growth-edge-p allocation-cons-root-edge-p
                            proof-register-frame-p proof-frame-return-p proof-subspan-p proof-streams-preserved-p
                            proof-stack-end proof-stack-base proof-stack-top proof-grow-limit
                            allocation-code-address allocation-cons-address mod)))))

(local
 (defthm allocation-cons-stack-pointer-shifts-keep-alignment
   (and (implies (and (integerp sp) (equal (mod sp 16) 0))
                 (equal (mod (- sp 16) 16) 0))
        (implies (and (integerp top) (equal (mod top 8) 0))
                 (equal (mod (+ 16 top) 8) 0)))))

(local
 (defthm allocation-cons-pushed-machine-frame-keeps-alignment
   (implies (and (integerp save) (equal sp (+ 16 save)) (equal (mod sp 16) 0))
            (equal (mod save 16) 0))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-cons-stack-pointer-shifts-keep-alignment (top 0)))
            :in-theory (disable allocation-cons-stack-pointer-shifts-keep-alignment mod)))))

(local
 (defthm allocation-cons-layout-allows-pair-push
   (implies (proof-heap-layout-p caller)
            (and (equal (mod (proof-stack-top caller) 8) 0)
                 (equal (mod (allocation-sp caller) 16) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-align-up proof-regions-p proof-covered-p
                                      proof-disjoint-p proof-runtime-word mod)))))

(defthm allocation-cons-rooted-stack-pointers-valid
  (let ((required (+ 16 (proof-stack-top caller))))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (allocation-cons-rooted-caller-frame-p caller rooted)
                  (equal (proof-stack-limit rooted) (proof-grow-limit required caller)))
             (allocation-stack-pointers-in-original-reservations-p caller rooted)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-layout-stack-base-before-top allocation-cons-layout-allows-pair-push
                 (:instance allocation-growth-layout-facts (before caller))
                 (:instance allocation-growth-aligned-limit (before caller) (required (+ 16 (proof-stack-top caller))))
                 (:instance allocation-growth-limit-in-reservation (world caller) (required (+ 16 (proof-stack-top caller))))
                 (:instance allocation-word-register-range (world caller) (register 25))
                 (:instance allocation-word-register-range (world rooted) (register 25))
                 (:instance allocation-cons-pushed-machine-frame-keeps-alignment
                  (save (allocation-sp rooted)) (sp (allocation-sp caller))))
           :in-theory (e/d (allocation-cons-prologue-room-p allocation-cons-rooted-caller-frame-p
                            allocation-stack-pointers-in-original-reservations-p unsigned-byte-p acl2::integer-range-p)
                           (proof-heap-layout-p proof-grow-limit proof-register-frame-p proof-stack-base
                            proof-stack-end proof-stack-top proof-stack-limit proof-machine-limit
                            allocation-word-register-range mod)))))

(defthm allocation-cons-rooted-stack-write-state
  (let ((writes (allocation-cons-prologue-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (proof-register-frame-p 30 *allocation-cons-prologue-clobbers* caller rooted)
                  (equal (allocation-memory rooted) (allocation-memory (allocation-write-words writes caller)))
                  (equal (proof-world-regions rooted) (proof-world-regions caller))
                  (proof-streams-preserved-p caller rooted)
                  (not (proof-world-stop rooted)))
             (allocation-stack-write-state-p writes caller rooted)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-words-in-stacks
                 (:instance allocation-register-frame-member
                  (before caller) (after rooted) (register 23) (upper 30) (clobbers *allocation-cons-prologue-clobbers*))
                 (:instance allocation-register-frame-member
                  (before caller) (after rooted) (register 26) (upper 30) (clobbers *allocation-cons-prologue-clobbers*))
                 (:instance allocation-register-frame-member
                  (before caller) (after rooted) (register 27) (upper 30) (clobbers *allocation-cons-prologue-clobbers*))
                 (:instance allocation-register-frame-member
                  (before caller) (after rooted) (register 28) (upper 30) (clobbers *allocation-cons-prologue-clobbers*)))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-layout-p proof-register-frame-p proof-streams-preserved-p
                            allocation-cons-prologue-writes allocation-write-words allocation-stack-word-writes-p)))))

(local
 (defthm allocation-cons-root-index-slot-is-old-top
   (implies (and (equal root-top (+ 16 base (* 8 index)))
                 (equal (- root-top 16) top)
                 (integerp top) (integerp base) (natp index))
            (equal (+ base (* 8 index)) top))
   :rule-classes nil))

(local
 (defthm allocation-cons-prologue-room-fits-words
   (implies (allocation-cons-prologue-room-p caller)
            (and (<= 16 (allocation-sp caller))
                 (< (+ 16 (proof-stack-top caller)) *allocation-word-modulus*)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-cons-prologue-room-p) (proof-subspan-p proof-stack-end))))))

(local
 (defthm allocation-cons-rooted-heap-with-argument-views
   (let* ((top (proof-stack-top caller))
          (old (proof-stack-prefix top caller objects packages)))
     (implies (and (proof-heap-p caller objects packages)
                   (allocation-stack-write-state-p (allocation-cons-prologue-writes caller) caller rooted)
                   (allocation-stack-pointers-in-original-reservations-p caller rooted)
                   (natp index)
                   (equal (proof-stack-top rooted) (+ 16 (proof-stack-base rooted) (* 8 index)))
                   (equal (- (proof-stack-top rooted) 16) top)
                   (proof-prefix-preserved-p top caller rooted objects objects packages)
                   (proof-machine-value-p (allocation-load-word top rooted) left rooted objects packages)
                   (proof-machine-value-p (allocation-load-word (+ 8 top) rooted) right rooted objects packages))
              (and (proof-heap-p rooted objects packages)
                   (equal (proof-stack-prefix (proof-stack-top rooted) rooted objects packages)
                          (cons :slots (append (cdr old) (list (proof-value-view left) (proof-value-view right))))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-cons-root-index-slot-is-old-top
                   (root-top (proof-stack-top rooted)) (base (proof-stack-base rooted)) (top (proof-stack-top caller)))
                  (:instance allocation-stack-prefix-extended-with-argument-pair (world rooted))
                  (:instance allocation-stack-write-state-keeps-heap-with-new-stack-prefix
                   (writes (allocation-cons-prologue-writes caller)) (before caller) (after rooted)))
            :in-theory (disable proof-heap-p proof-stack-top proof-stack-base proof-stack-prefix
                                proof-machine-value-p allocation-cons-prologue-writes mod)))))

(local
 (defthm allocation-cons-decoded-prefix-stack-state
   (let* ((needed (+ 16 (proof-stack-top caller)))
          (path (allocation-growth-path "rt:ensure-stack" needed cut)))
     (implies (and (allocation-cons-machine-entry-p origin caller)
                   (proof-heap-layout-p caller)
                   (allocation-cons-prologue-room-p caller)
                   (not (proof-allocation-fits-p :cons 16 caller))
                   (<= (proof-stack-end caller) (expt 2 63))
                   (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                   (equal grown (allocation-path-end path cut))
                   (equal rooted (allocation-path-end *allocation-cons-root-path* grown)))
              (and (allocation-stack-write-state-p (allocation-cons-prologue-writes caller) caller rooted)
                   (allocation-stack-pointers-in-original-reservations-p caller rooted))))
   :rule-classes nil
   :hints (("Goal"
            :use (allocation-cons-growth-premises-from-linux-layout allocation-cons-prologue-room-fits-words
                  allocation-cons-prologue-writes-in-unused-stack allocation-cons-prologue-effects
                  allocation-cons-prologue-memory-footprint allocation-cons-prologue-sets-committed-stack-limit
                  allocation-cons-rooted-stack-pointers-valid allocation-cons-rooted-stack-write-state)
            :in-theory (disable allocation-cons-machine-entry-p proof-heap-layout-p proof-allocation-fits-p
                                allocation-growth-path allocation-path-end allocation-growth-machine-pre-p
                                allocation-growth-doubling-fits-p allocation-cons-rooted-caller-frame-p
                                proof-stack-base proof-stack-end proof-stack-top proof-stack-limit proof-grow-limit
                                allocation-cons-fields-p proof-register-frame-p proof-streams-preserved-p
                                allocation-cons-prologue-writes allocation-write-words proof-span-p proof-disjoint-p)))))

(defthm allocation-cons-checked-allocator-entry-has-heap
  (let* ((top (proof-stack-top caller))
         (required (+ 16 top))
         (path (allocation-cons-prologue-path caller cut))
         (growth (allocation-growth-path "rt:ensure-stack" required cut))
         (target (allocation-code-address "rt:alloc-cells" origin))
         (cuts (list target))
         (old (proof-stack-prefix top caller objects packages)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (proof-heap-p caller objects packages)
                  (allocation-cons-prologue-room-p caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (<= (proof-stack-end caller) (expt 2 63))
                  (proof-reg-value-p 0 left caller objects packages)
                  (proof-reg-value-p 1 right caller objects packages)
                  (natp index) (equal top (+ (proof-stack-base caller) (* 8 index)))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (equal grown (allocation-path-end growth cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown))
                  (allocation-path-ready-p path cuts caller))
             (and (proof-segment-p (len path) cuts caller :cut rooted)
                  (proof-heap-p rooted objects packages)
                  (equal (proof-world-reg 0 rooted) 16)
                  (equal (proof-stack-prefix (proof-stack-top rooted) rooted objects packages)
                         (cons :slots (append (cdr old) (list (proof-value-view left) (proof-value-view right))))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 allocation-cons-growth-premises-from-linux-layout allocation-cons-prologue-writes-in-unused-stack
                 allocation-cons-prologue-room-fits-words
                 allocation-cons-prologue-sets-up-caller-heap-frame allocation-cons-checked-prologue-to-roots
                 allocation-cons-decoded-prefix-stack-state allocation-cons-rooted-heap-with-argument-views)
           :in-theory (disable allocation-cons-machine-entry-p allocation-cons-prologue-room-p
                               proof-allocation-fits-p allocation-path-end allocation-growth-path
                               allocation-growth-machine-pre-p allocation-growth-doubling-fits-p
                               allocation-path-ready-p proof-segment-p proof-heap-p proof-heap-layout-p proof-grow-limit
                               proof-stack-top proof-stack-limit proof-stack-end proof-stack-base proof-stack-prefix
                               proof-reg-value-p proof-machine-value-p proof-register-frame-p proof-heap-frame-p
                               proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-streams-preserved-p allocation-cons-fields-p
                               allocation-write-words allocation-cons-prologue-writes allocation-cons-rooted-caller-frame-p
                               proof-span-p proof-subspan-p proof-disjoint-p mod))))
