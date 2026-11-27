(in-package "BOYMOO-PROOFS")

(include-book "memory-frame")
(include-book "object-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine generated-copy-words generated-store-word
                    generated-load-word proof-load-word proof-load-string proof-byte-list
                    proof-limbs-p proof-limb-magnitude proof-integer-view
                    proof-view-step proof-view proof-object-map-p proof-align-up
                    proof-object-disjoint-p proof-object-size proof-span-p proof-disjoint-p
                    proof-word-tag proof-pointer-address proof-immediate-integer-p
                    proof-cons-value proof-complex-value proof-rational-value proof-symbol-value
                    boymoo-model::a64-load boymoo-model::a64-store boymoo-model::a64-unsigned expt))

(defthmd generated-byte-list-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (proof-span-p address byte-count)
                (proof-disjoint-p address (+ address byte-count) start end))
           (equal (proof-byte-list byte-count address last)
                  (proof-byte-list byte-count address first)))
  :hints (("Goal" :induct (proof-byte-list byte-count address first)
                  :in-theory (enable proof-byte-list proof-span-p proof-disjoint-p))
          ("Subgoal *1/2"
           :use (:instance generated-load-outside-written-span
                           (count 1) (before first) (after last)))))

(defthmd generated-string-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (or (zp byte-count)
                    (and (proof-span-p address byte-count)
                         (proof-disjoint-p address (+ address byte-count) start end))))
           (equal (proof-load-string byte-count address last)
                  (proof-load-string byte-count address first)))
  :hints (("Goal" :use generated-byte-list-outside-written-span
                  :in-theory (enable proof-load-string proof-byte-list))))

(defthmd generated-limb-reads-outside-written-span
  (implies (and (generated-memory-outside-p start end first last)
                (or (zp count)
                    (and (proof-span-p address (* 8 count))
                         (proof-disjoint-p address (+ address (* 8 count)) start end))))
           (and (equal (proof-limb-magnitude count address last)
                       (proof-limb-magnitude count address first))
                (equal (proof-limbs-p count address last)
                       (proof-limbs-p count address first))))
  :hints (("Goal" :induct (proof-limb-magnitude count address first)
                  :in-theory (enable proof-limb-magnitude proof-limbs-p proof-span-p proof-disjoint-p))
          ("Subgoal *1/2"
           :use (:instance generated-word-outside-written-span (before first) (after last)))))

(defthm generated-ash-down-by-three
  (implies (integerp value) (equal (ash value -3) (floor value 8)))
  :hints (("Goal" :in-theory (enable ash floor))))

(local
 (defthm generated-integer-length-after-limb-count
   (implies (and (integerp size) (<= 8 size) (equal (mod size 8) 0))
            (and (natp (1- (ash size -3)))
                 (equal (* 8 (1- (ash size -3))) (- size 8))))
   :hints (("Goal" :use (:instance generated-floor-bounds (x size) (y 8))
                   :in-theory (enable mod)))))

(defthmd generated-integer-view-outside-written-span
  (let ((size (proof-header-size (proof-load-word address first))))
    (implies (and (generated-memory-outside-p start end first last)
                  (proof-integer-view address first)
                  (proof-disjoint-p address (+ address 8 size) start end))
             (equal (proof-integer-view address last) (proof-integer-view address first))))
  :hints (("Goal"
           :use ((:instance generated-integer-length-after-limb-count
                            (size (proof-header-size (proof-load-word address first))))
                 (:instance generated-word-outside-written-span (before first) (after last))
                 (:instance generated-word-outside-written-span (before first) (after last)
                            (address (+ 8 address)))
                 (:instance generated-limb-reads-outside-written-span
                            (address (+ 16 address))
                            (count (1- (ash (proof-header-size (proof-load-word address first)) -3)))))
           :in-theory (e/d (proof-integer-view proof-span-p proof-disjoint-p)
                           (generated-integer-length-after-limb-count)))))

(local
 (defthm generated-declared-object-span-is-copy-disjoint
   (let ((record (assoc-equal address objects)))
     (implies (and record (proof-object-disjoint-p start end objects machine))
              (proof-disjoint-p address (+ address (proof-object-size record machine)) start end)))
   :hints (("Goal" :induct (proof-object-disjoint-p start end objects machine)
                   :in-theory (enable proof-object-disjoint-p proof-disjoint-p)))
   :rule-classes nil))

(local
 (defthm generated-declared-object-span-fits
   (let ((record (assoc-equal address pending)))
     (implies (and record (proof-object-map-p pending objects seen base packages machine))
              (proof-span-p address (proof-object-size record machine))))
   :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine)
                   :in-theory (enable proof-object-map-p)))
   :rule-classes nil))

(local
 (defthm generated-eight-byte-rounding-covers-integer-length
   (implies (integerp address)
            (<= address (proof-align-up address 8)))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x (* 1/8 address)) (y 1))
                  (:instance rational-implies1 (acl2::x (* 1/8 address)))
                  (:instance rational-implies2 (acl2::x (* 1/8 address))))
            :in-theory (e/d (proof-align-up ceiling floor) (rational-implies2))))
   :rule-classes :linear))

(local
 (defthm generated-object-view-extent-is-copy-disjoint
   (let* ((record (assoc-equal address objects))
          (size (proof-header-size (proof-load-word address machine)))
          (bytes (if (eq (proof-object-kind record) :cons) 16 (+ 8 size))))
     (implies (and record (proof-object-disjoint-p start end objects machine))
              (proof-disjoint-p address (+ address bytes) start end)))
   :hints (("Goal"
            :use (generated-declared-object-span-is-copy-disjoint generated-lookup-record-is-published)
            :in-theory (e/d (proof-object-size proof-disjoint-p)
                            (proof-header-size proof-object-kind))))
   :rule-classes nil))

(local
 (defthm generated-eight-byte-rounding-is-nonnegative
   (<= 0 (proof-align-up address 8))
   :hints (("Goal"
            :use ((:instance rational-implies1 (acl2::x (* 1/8 (nfix address))))
                  (:instance rational-implies2 (acl2::x (* 1/8 (nfix address)))))
            :in-theory (e/d (proof-align-up ceiling) (rational-implies2))))
   :rule-classes :linear))

(local
 (defthm generated-readable-word-outside-written-span
   (implies (and (generated-memory-outside-p start end first last)
                 (proof-span-p address 8)
                 (proof-disjoint-p address (+ address 8) start end))
            (equal (proof-load-word address last) (proof-load-word address first)))
   :hints (("Goal" :use (:instance generated-word-outside-written-span (before first) (after last))))))

(local
 (defthm generated-published-header-read-outside-written-span
   (let ((record (assoc-equal address objects)))
     (implies (and (generated-memory-outside-p start end first last)
                   (proof-object-map-p objects objects nil base packages first)
                   (proof-object-disjoint-p start end objects first)
                   record (eq (proof-object-kind record) :header))
              (equal (proof-load-word address last) (proof-load-word address first))))
   :hints (("Goal"
            :use (generated-lookup-record-is-published
                  (:instance generated-declared-object-span-fits (pending objects) (seen nil)
                             (machine first))
                  (:instance generated-declared-object-span-is-copy-disjoint (machine first))
                  (:instance generated-word-outside-written-span (before first) (after last)))
            :in-theory (e/d (proof-object-size proof-span-p proof-disjoint-p)
                            (proof-object-kind proof-header-size generated-readable-word-outside-written-span))))))

(defthm generated-byte-count-of-aligned-slots
  (implies (and (integerp size) (equal (mod size 8) 0))
           (equal (* 8 (floor size 8)) size))
  :hints (("Goal" :in-theory (enable mod))))

(local
 (defthm generated-header-size-is-integer
   (integerp (proof-header-size header))
   :hints (("Goal" :in-theory (enable proof-header-size)))
   :rule-classes :type-prescription))

(local
 (defthm generated-byte-load-is-natural
   (natp (boymoo-model::a64-load byte-count address machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load)))
   :rule-classes :type-prescription))

(defthm generated-proof-load-word-natural
  (natp (proof-load-word address machine))
  :hints (("Goal" :in-theory (enable proof-load-word)))
  :rule-classes :type-prescription)

(local
 (defthm generated-header-size-of-natural-word
   (implies (natp header) (natp (proof-header-size header)))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x (* 1/256 header)) (y 1))
                  (:instance generated-integer-step (x (floor (* 1/256 header) 1)) (y 0)))
            :in-theory (enable proof-header-size generated-ash-as-floor)))
   :rule-classes :type-prescription))

(defthm generated-published-view-step-outside-written-span
  (let ((view (proof-view-step kind input count depth base objects packages first)))
    (implies (and (generated-memory-outside-p start end first last)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p start end objects first)
                  (implies (and (eq kind :slots) (posp count))
                           (and (proof-span-p input (* 8 count))
                                (proof-disjoint-p input (+ input (* 8 count)) start end)))
                  view)
             (equal (proof-view-step kind input count depth base objects packages last) view)))
  :hints (("Goal"
           :induct (proof-view-step kind input count depth base objects packages first)
           :in-theory (e/d (proof-view-step proof-span-p proof-disjoint-p
                           generated-integer-view-outside-written-span
                           proof-cons-value proof-complex-value proof-rational-value proof-symbol-value)
                          (proof-object-kind proof-header-size proof-header-type)))
          ("Subgoal *1/20"
           :use (:instance generated-object-view-extent-is-copy-disjoint
                           (address (proof-pointer-address input base)) (machine first)))
          ("Subgoal *1/18"
           :use (:instance generated-object-view-extent-is-copy-disjoint
                           (address (proof-pointer-address input base)) (machine first)))
          ("Subgoal *1/17"
           :use (:instance generated-object-view-extent-is-copy-disjoint
                           (address (proof-pointer-address input base)) (machine first)))
          ("Subgoal *1/16"
           :use (:instance generated-object-view-extent-is-copy-disjoint
                           (address (proof-pointer-address input base)) (machine first)))
          ("Subgoal *1/13"
           :use (:instance generated-object-view-extent-is-copy-disjoint
                           (address (proof-pointer-address input base)) (machine first)))
          ("Subgoal *1/12"
           :use ((:instance generated-object-view-extent-is-copy-disjoint
                            (address (proof-pointer-address input base)) (machine first))
                 (:instance generated-string-outside-written-span
                            (address (+ 8 (proof-pointer-address input base)))
                            (byte-count (proof-header-size
                                         (proof-load-word (proof-pointer-address input base) first))))))
          ("Subgoal *1/9"
           :use (:instance generated-object-view-extent-is-copy-disjoint
                           (address (proof-pointer-address input base)) (machine first))))
  :rule-classes nil)

(defthm generated-published-view-outside-written-span
  (let ((view (proof-view word base objects packages first)))
    (implies (and (generated-memory-outside-p start end first last)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p start end objects first)
                  view)
             (equal (proof-view word base objects packages last) view)))
  :hints (("Goal"
           :use (:instance generated-published-view-step-outside-written-span
                           (kind :word) (input word) (count 0)
                           (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base) objects))))))
           :in-theory (enable proof-view)))
  :rule-classes nil)

(defthm generated-published-view-step-outside-copied-destination
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine (generated-copy-words copies source destination before)))
         (end (+ destination (* 8 copies)))
         (view (proof-view-step kind input count depth base objects packages first)))
    (implies (and (generated-word-block-span-p destination copies)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p destination end objects first)
                  (implies (and (eq kind :slots) (posp count))
                           (and (proof-span-p input (* 8 count))
                                (proof-disjoint-p input (+ input (* 8 count)) destination end)))
                  view)
             (equal (proof-view-step kind input count depth base objects packages last) view)))
  :hints (("Goal"
           :use (:instance generated-published-view-step-outside-written-span
                           (start destination) (end (+ destination (* 8 copies)))
                           (first (proof-world-machine before))
                           (last (proof-world-machine
                                  (generated-copy-words copies source destination before)))))))

(defthm generated-published-view-outside-copied-destination
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine (generated-copy-words copies source destination before)))
         (view (proof-view word base objects packages first)))
    (implies (and (generated-word-block-span-p destination copies)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p destination (+ destination (* 8 copies)) objects first)
                  view)
             (equal (proof-view word base objects packages last) view)))
  :hints (("Goal"
           :use (:instance generated-published-view-outside-written-span
                           (start destination) (end (+ destination (* 8 copies)))
                           (first (proof-world-machine before))
                           (last (proof-world-machine
                                  (generated-copy-words copies source destination before)))))))
