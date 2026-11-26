(in-package "BOYMOO-PROOFS")

(include-book "prologue-flow")
(include-book "protected-frame")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-layout-p proof-heap-p proof-compiled-entry-p proof-world-machine
                    proof-world-reg proof-world-pc proof-world-stop proof-world-regions proof-world-page-size
                    proof-stack-base proof-stack-top proof-stack-limit proof-stack-end proof-machine-limit
                    proof-heap-base proof-heap-limit proof-box-top proof-span-p proof-subspan-p proof-disjoint-p
                    proof-stack-prefix proof-prefix-preserved-p proof-segment-p proof-instruction-effect
                    proof-object-map-p generated-sp generated-load-word generated-store-word generated-path-p
                    generated-path-after boymoo-model::a64-memory boymoo-model::a64-unsigned mod expt))

(local
 (defthm generated-unchanged-entries-compose
   (implies (and (generated-memory-outside-p start end first middle)
                 (generated-memory-outside-p start end middle last))
            (generated-outside-entries-p entries start end (boymoo-model::a64-memory first)
                                         (boymoo-model::a64-memory last)))
   :hints (("Goal" :induct (len entries))
           ("Subgoal *1/1"
            :use ((:instance generated-byte-outside-written-span
                             (address (caar entries)) (before first) (after middle))
                  (:instance generated-byte-outside-written-span
                             (address (caar entries)) (before middle) (after last)))))
   :rule-classes nil))

(defthm generated-memory-outside-transitive
  (implies (and (generated-memory-outside-p start end first middle)
                (generated-memory-outside-p start end middle last))
           (generated-memory-outside-p start end first last))
  :hints (("Goal"
           :use ((:instance generated-unchanged-entries-compose (entries (boymoo-model::a64-memory first)))
                 (:instance generated-unchanged-entries-compose (entries (boymoo-model::a64-memory last))))
           :in-theory (enable generated-memory-outside-p)))
  :rule-classes nil)

(local
 (defthm generated-save-frame-stores-are-confined
   (let* ((middle (generated-store-word address first-value before))
          (last (generated-store-word (+ address 8) second-value middle)))
     (implies (proof-span-p address 16)
              (generated-memory-outside-p address (+ address 16)
                                           (proof-world-machine before) (proof-world-machine last))))
   :hints (("Goal"
            :use ((:instance generated-word-store-writes-only-inside-span (start address) (end (+ address 16))
                             (world before) (value first-value))
                  (:instance generated-word-store-writes-only-inside-span (start address) (end (+ address 16))
                             (address (+ address 8)) (world (generated-store-word address first-value before))
                             (value second-value))
                  (:instance generated-memory-outside-transitive (start address) (end (+ address 16))
                             (first (proof-world-machine before))
                             (middle (proof-world-machine (generated-store-word address first-value before)))
                             (last (proof-world-machine (generated-store-word (+ address 8) second-value
                                                                              (generated-store-word address first-value before))))))
            :in-theory (e/d (proof-span-p) (generated-word-store-writes-only-inside-span))))
   :rule-classes nil))

(defthm generated-incoming-machine-bound-prevents-subtraction-wrap
  (implies (and (proof-heap-layout-p before) (<= (proof-machine-limit before) (generated-sp before)))
           (and (<= 16 (proof-machine-limit before)) (<= 16 (generated-sp before))))
  :hints (("Goal"
           :use (:instance generated-heap-layout-machine-stack-bounds (world before))
           :in-theory (enable proof-span-p generated-machine-stack-base)))
  :rule-classes nil)

(local
 (defthm generated-frame-save-within-machine-stack
   (let ((start (- (generated-sp before) 16)))
     (implies (and (proof-heap-layout-p before) (<= (proof-machine-limit before) start))
              (and (proof-subspan-p start 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                   (proof-span-p start 16) (equal (mod start 16) 0)
                   (<= (generated-machine-stack-base before) start)
                   (<= start (generated-machine-stack-end before)))))
   :hints (("Goal"
            :use ((:instance generated-heap-layout-machine-stack-bounds (world before))
                  (:instance generated-floor-add-multiple (x (generated-sp before)) (divisor 16) (q -1)))
            :in-theory (enable generated-machine-stack-base generated-machine-stack-end proof-subspan-p
                               proof-machine-limit proof-span-p mod)))
   :rule-classes nil))

(local
 (defthm generated-frame-save-keeps-page-size
   (equal (proof-world-page-size (generated-set-sp sp world)) (proof-world-page-size world))
   :hints (("Goal" :in-theory (enable generated-set-sp)))))

(local
 (defthm generated-save-frame-is-stack-update
   (let* ((sp (generated-sp before)) (start (- sp 16))
          (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))
     (implies (and (proof-heap-layout-p before) (<= (proof-machine-limit before) start)
                   (generated-ordinary-machine-p before))
              (and (generated-stack-update-p start sp before after)
                   (equal (proof-stack-top after) (proof-stack-top before))
                   (equal (generated-sp after) start))))
   :hints (("Goal"
            :use (generated-frame-save-within-machine-stack
                  (:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-save-frame-stores-are-confined
                             (address (- (generated-sp before) 16))
                             (first-value (proof-world-reg 19 before)) (second-value (proof-world-reg 30 before))))
            :in-theory (e/d (generated-stack-update-p generated-runtime-stack-span-p proof-stack-top proof-stack-limit
                                              proof-machine-limit proof-heap-base proof-box-top proof-heap-limit proof-span-p)
                            (generated-word-store-writes-only-inside-span))))
   :rule-classes nil))

(local
 (defthm generated-frame-save-keeps-streams
   (implies (generated-ordinary-machine-p before)
            (proof-streams-preserved-p before (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))
   :hints (("Goal" :in-theory (enable proof-streams-preserved-p generated-set-machine generated-set-pc
                                      generated-set-sp generated-store-word proof-world-input proof-world-stdout
                                      proof-world-stderr proof-world-page-size)))
   :rule-classes nil))

(defthm generated-frame-save-preserves-caller-heap-frame
  (let* ((sp (generated-sp before)) (start (- sp 16))
         (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))
    (implies (and (proof-heap-layout-p before) (<= (proof-machine-limit before) start)
                  (generated-ordinary-machine-p before))
             (proof-heap-frame-p before after)))
  :hints (("Goal"
           :use (generated-save-frame-is-stack-update generated-frame-save-keeps-streams
                 generated-incoming-machine-bound-prevents-subtraction-wrap
                 (:instance generated-stack-update-preserves-protected-heap-frame
                            (start (- (generated-sp before) 16)) (end (generated-sp before))
                            (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before))))
           :in-theory (e/d (proof-disjoint-p) (generated-effect-of-save-frame))))
  :rule-classes nil)

(local
 (defthm generated-value-prefix-disjoint-from-saved-frame
   (let* ((sp (generated-sp before)) (start (- sp 16)))
     (implies (and (proof-heap-layout-p before) (<= (proof-machine-limit before) start))
              (proof-disjoint-p (proof-stack-base before) (proof-stack-top before) start sp)))
   :hints (("Goal"
            :use (generated-frame-save-within-machine-stack
                  (:instance generated-heap-layout-value-stack-bounds (world before)))
            :in-theory (enable proof-heap-layout-p generated-machine-stack-base generated-machine-stack-end
                               proof-disjoint-p proof-subspan-p)))
   :rule-classes nil))

(local
 (defthm generated-occupied-prefix-has-slot-count
   (let* ((base (proof-stack-base before)) (top (proof-stack-top before))
          (count (ash (- top base) -3)))
     (implies (proof-stack-prefix top before objects packages)
              (and (natp count) (equal top (+ base (* 8 count))))))
   :hints (("Goal"
            :use (:instance generated-byte-count-of-aligned-slots (size (- (proof-stack-top before) (proof-stack-base before))))
            :in-theory (e/d (proof-stack-prefix generated-ash-down-by-three)
                            (generated-byte-count-of-aligned-slots))))
   :rule-classes nil))

(defthm generated-prologue-frame-save-keeps-valid-heap
  (let* ((sp (generated-sp before)) (start (- sp 16))
         (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before))
         (top (proof-stack-top before)))
    (implies (and (proof-heap-p before objects packages) (<= (proof-machine-limit before) start)
                  (generated-ordinary-machine-p before))
             (and (proof-heap-p after objects packages)
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-stack-top after) top)
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (equal (generated-sp after) start))))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 generated-save-frame-is-stack-update generated-occupied-prefix-has-slot-count
                 generated-value-prefix-disjoint-from-saved-frame
                 (:instance generated-stack-update-is-disjoint-from-published-objects
                            (start (- (generated-sp before) 16)) (end (generated-sp before))
                            (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))
                 (:instance generated-stack-update-preserves-runtime-fields
                            (start (- (generated-sp before) 16)) (end (generated-sp before))
                            (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))
                 (:instance generated-stack-update-preserves-untouched-prefix
                            (start (- (generated-sp before) 16)) (end (generated-sp before))
                            (keep (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))
                 (:instance generated-stack-update-preserves-heap-with-valid-roots
                            (start (- (generated-sp before) 16)) (end (generated-sp before))
                            (after (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before))))
           :in-theory (e/d (proof-prefix-preserved-p) (generated-effect-of-save-frame))))
  :rule-classes nil)
