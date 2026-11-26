(in-package "BOYMOO-PROOFS")

(include-book "heap-layout-frame")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-external-objects proof-external-bytes proof-heap-layout-p
                    proof-stack-base proof-stack-end proof-world-machine proof-world-regions
                    proof-load-word proof-header-size proof-header-type proof-object-zone proof-object-kind
                    proof-region proof-regions-p proof-region-p proof-align-up proof-span-p proof-subspan-p
                    proof-disjoint-p ash floor mod expt))

(defthm generated-mapped-region-is-valid
  (implies (and (proof-regions-p regions) (member-equal region regions))
           (proof-region-p region))
  :hints (("Goal" :induct (len regions) :in-theory (enable proof-regions-p)))
  :rule-classes nil)

(defthm generated-write-in-stack-is-disjoint-from-mapping
  (implies (and (generated-runtime-stack-span-p start end world)
                (proof-disjoint-p head limit (proof-stack-base world) (proof-stack-end world))
                (proof-disjoint-p head limit (generated-machine-stack-base world)
                                  (generated-machine-stack-end world)))
           (proof-disjoint-p head limit start end))
  :hints (("Goal" :in-theory (enable generated-runtime-stack-span-p proof-subspan-p proof-disjoint-p)))
  :rule-classes nil)

(local
 (defthm generated-external-header-words-outside-written-span
   (implies (and (proof-regions-p regions) (member-equal (proof-region head (+ head size) :rw) regions)
                 (<= 32 size) (proof-disjoint-p head (+ head size) start end)
                 (generated-memory-outside-p start end first last))
            (and (equal (proof-load-word head last) (proof-load-word head first))
                 (equal (proof-load-word (+ head 8) last) (proof-load-word (+ head 8) first))
                 (equal (proof-load-word (+ head 16) last) (proof-load-word (+ head 16) first))
                 (equal (proof-load-word (+ head 24) last) (proof-load-word (+ head 24) first))))
   :hints (("Goal"
            :use ((:instance generated-mapped-region-is-valid (region (proof-region head (+ head size) :rw)))
                  (:instance generated-word-outside-written-span (address head) (before first) (after last))
                  (:instance generated-word-outside-written-span (address (+ head 8)) (before first) (after last))
                  (:instance generated-word-outside-written-span (address (+ head 16)) (before first) (after last))
                  (:instance generated-word-outside-written-span (address (+ head 24)) (before first) (after last)))
            :in-theory (enable proof-span-p proof-disjoint-p proof-region proof-region-p)))
   :rule-classes nil))

(local
 (defthm generated-external-header-size-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x (* 1/256 (proof-load-word address machine))) (y 1))
                  (:instance generated-integer-step (y 0)
                             (x (floor (* 1/256 (proof-load-word address machine)) 1))))
            :in-theory (enable proof-header-size)))
   :rule-classes :type-prescription))

(local
 (defthm generated-external-mapping-size-at-least-header
   (<= 32 (proof-align-up (+ 32 (proof-header-size (proof-load-word address machine))) *proof-runtime-page*))
   :hints (("Goal"
            :use (:instance generated-rounding-up-covers-address
                            (address (+ 32 (proof-header-size (proof-load-word address machine))))
                            (alignment *proof-runtime-page*))))
   :rule-classes (:linear)))

(local
 (defun generated-external-chain-induction (head fuel world)
   (declare (xargs :measure (nfix fuel)))
   (if (and (not (equal head 0)) (posp fuel))
       (generated-external-chain-induction (proof-load-word head (proof-world-machine world)) (1- fuel) world)
     head)))

(local
 (defthm generated-external-layout-regions-valid
   (implies (proof-heap-layout-p world) (proof-regions-p (proof-world-regions world)))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p)))))

(local
 (defthm generated-external-bytes-of-cons
   (equal (proof-external-bytes (cons address rest) machine)
          (+ (proof-load-word (- address 16) machine) (proof-external-bytes rest machine)))
   :hints (("Goal" :in-theory (enable proof-external-bytes)))))

(defthm generated-external-mappings-outside-written-span
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after))
        (mappings (proof-external-objects head fuel before objects)))
    (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after) mappings)
             (and (equal (proof-external-objects head fuel after objects) mappings)
                  (equal (proof-external-bytes (cdr mappings) last)
                         (proof-external-bytes (cdr mappings) first)))))
  :hints (("Goal" :induct (generated-external-chain-induction head fuel before))
          ("Subgoal *1/1"
           :expand ((proof-external-objects head fuel before objects)
                    (proof-external-objects head fuel after objects))
           :use (generated-stack-update-preserves-runtime-fields
                 (:instance generated-write-in-stack-is-disjoint-from-mapping
                            (world before)
                            (limit (+ head (proof-load-word (+ head 8) (proof-world-machine before)))))
                 (:instance generated-external-header-words-outside-written-span
                            (regions (proof-world-regions before))
                            (first (proof-world-machine before)) (last (proof-world-machine after))
                            (size (proof-load-word (+ head 8) (proof-world-machine before)))))
           :in-theory (enable generated-stack-update-p
                              generated-machine-stack-base generated-machine-stack-end))
          ("Subgoal *1/2" :in-theory (enable proof-external-objects proof-external-bytes)))
  :rule-classes nil)

(local
 (defthm generated-nonnegative-rational-ceiling-bound
   (implies (and (rationalp value) (<= 0 value) (integerp units) (<= value units))
            (<= (ceiling value 1) units))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x value) (y 1))
                  (:instance generated-integer-step (x (floor value 1)) (y units))
                  (:instance rational-implies2 (acl2::x value)))
            :cases ((equal value units))
            :in-theory (e/d (ceiling floor) (rational-implies2))))
   :rule-classes nil))

(local
 (defthm generated-eight-byte-ceiling-bound
   (implies (and (natp value) (integerp units) (<= value (* 8 units)))
            (<= (ceiling value 8) units))
   :hints (("Goal"
            :use (:instance generated-nonnegative-rational-ceiling-bound (value (* 1/8 value)))
            :in-theory (enable ceiling)))
   :rule-classes nil))

(local
 (defthm generated-external-rounded-object-fits-in-mapping
   (implies (natp payload)
            (<= (+ 32 (proof-align-up payload 8))
                (proof-align-up (+ 32 payload) *proof-runtime-page*)))
   :hints (("Goal"
            :use ((:instance generated-rounding-up-covers-address
                             (address (+ 32 payload)) (alignment *proof-runtime-page*))
                  (:instance generated-eight-byte-ceiling-bound
                             (value payload)
                             (units (- (* 8192 (ceiling (+ 32 payload) *proof-runtime-page*)) 4))))
            :in-theory (enable proof-align-up)))
   :rule-classes nil))

(local
 (defthm generated-external-record-at-mapping-head-is-disjoint
   (let* ((machine (proof-world-machine world))
          (address (+ head 24))
          (record (assoc-equal address objects))
          (end-of-mapping (+ head (proof-load-word (+ head 8) machine)))
          (payload (proof-header-size (proof-load-word address machine))))
     (implies (and record (eq (proof-object-kind record) :header)
                   (equal (proof-load-word (+ head 8) machine)
                          (proof-align-up (+ 32 payload) *proof-runtime-page*))
                   (proof-disjoint-p head end-of-mapping start end))
              (proof-disjoint-p address (+ address (proof-object-size record machine)) start end)))
   :hints (("Goal"
            :use ((:instance generated-lookup-record-is-published (address (+ head 24)))
                  (:instance generated-external-rounded-object-fits-in-mapping
                             (payload (proof-header-size (proof-load-word (+ head 24)
                                                                         (proof-world-machine world))))))
            :in-theory (enable proof-disjoint-p proof-object-size)))
   :rule-classes nil))

(defthm generated-external-record-disjoint-from-stack-write
  (let* ((addresses (cdr (proof-external-objects head fuel world objects)))
         (record (assoc-equal address objects)))
    (implies (and (generated-runtime-stack-span-p start end world)
                  (member-equal address addresses))
             (and record
                  (proof-disjoint-p address (+ address (proof-object-size record (proof-world-machine world)))
                                    start end))))
  :hints (("Goal" :induct (generated-external-chain-induction head fuel world))
          ("Subgoal *1/2" :in-theory (enable proof-external-objects))
          ("Subgoal *1/1"
           :expand (proof-external-objects head fuel world objects)
           :use (generated-external-record-at-mapping-head-is-disjoint
                 (:instance generated-write-in-stack-is-disjoint-from-mapping
                            (limit (+ head (proof-load-word (+ head 8) (proof-world-machine world))))))
           :in-theory (enable generated-machine-stack-base generated-machine-stack-end)))
  :rule-classes nil)
