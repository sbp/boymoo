(in-package "BOYMOO-PROOFS")

(include-book "tail-roots")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine proof-world-reg proof-world-stop proof-world-pc
                    proof-world-regions proof-world-page-size proof-segment-p proof-instruction-effect
                    proof-heap-p proof-heap-layout-p proof-stack-views proof-stack-prefix
                    proof-static-p proof-object-map-p proof-external-objects proof-heap-object-spans-p
                    proof-string-accounting-p proof-dynamic-symbol-objects-p proof-dynamic-entries
                    proof-dynamic-view proof-stack-base proof-stack-end proof-runtime-word
                    proof-load-word proof-heap-base proof-box-top proof-heap-limit proof-stack-top
                    proof-stack-limit proof-machine-limit proof-spaces-end proof-active-floor
                    proof-active-end proof-inactive-floor proof-inactive-end proof-cons-floor
                    proof-string-bytes-since-collection proof-string-budget proof-external-head
                    generated-address-path generated-sp boymoo-model::a64-unsigned mod ash expt))

(local
 (defun generated-stack-prefix-induction (small large address)
   (declare (xargs :measure (nfix small)))
   (if (zp small)
       (cons large address)
     (generated-stack-prefix-induction (1- small) (1- large) (+ 8 address)))))

(defthm generated-stack-views-have-valid-prefix
  (implies (and (natp small) (natp large) (<= small large)
                (proof-stack-views large address base objects packages machine))
           (equal (proof-stack-views small address base objects packages machine)
                  (cons :slots (take small (cdr (proof-stack-views
                                               large address base objects packages machine))))))
  :hints (("Goal" :induct (generated-stack-prefix-induction small large address)
                  :in-theory (enable proof-stack-views take))))

(local
 (defthm generated-stack-aligned-addition
   (implies (and (integerp base) (integerp count))
            (equal (mod (+ base (* 8 count)) 8) (mod base 8)))
   :hints (("Goal" :use (:instance generated-floor-add-multiple
                                   (x base) (q count) (divisor 8))
                   :in-theory (e/d (mod) (generated-floor-add-multiple))))))

(local
 (defthm generated-runtime-word-ignores-stack-top-update
   (equal (proof-runtime-word offset (generated-set-reg 25 top world))
          (proof-runtime-word offset world))
   :hints (("Goal" :in-theory (enable proof-runtime-word proof-heap-base)))))

(local
 (defthm generated-stack-top-fields-unchanged
   (let ((after (generated-set-reg 25 top world)))
     (and (equal (proof-heap-base after) (proof-heap-base world))
          (equal (proof-box-top after) (proof-box-top world))
          (equal (proof-heap-limit after) (proof-heap-limit world))
          (equal (proof-stack-limit after) (proof-stack-limit world))
          (equal (proof-machine-limit after) (proof-machine-limit world))
          (equal (proof-stack-base after) (proof-stack-base world))
          (equal (proof-stack-end after) (proof-stack-end world))
          (equal (proof-spaces-end after) (proof-spaces-end world))
          (equal (proof-active-floor after) (proof-active-floor world))
          (equal (proof-active-end after) (proof-active-end world))
          (equal (proof-inactive-floor after) (proof-inactive-floor world))
          (equal (proof-inactive-end after) (proof-inactive-end world))
          (equal (proof-cons-floor after) (proof-cons-floor world))
          (equal (proof-external-head after) (proof-external-head world))
          (equal (proof-string-bytes-since-collection after) (proof-string-bytes-since-collection world))
          (equal (proof-string-budget after) (proof-string-budget world))
          (equal (proof-dynamic-view after objects packages) (proof-dynamic-view world objects packages))
          (equal (proof-stack-top after) (boymoo-model::a64-unsigned 64 top))))
   :hints (("Goal"
            :in-theory (enable proof-heap-base proof-box-top proof-heap-limit proof-stack-limit
                               proof-machine-limit proof-stack-base proof-stack-end proof-spaces-end
                               proof-active-floor proof-active-end proof-inactive-floor proof-inactive-end
                               proof-cons-floor proof-external-head proof-string-bytes-since-collection
                               proof-string-budget proof-dynamic-view proof-stack-top)))))

(local
 (defthm generated-stack-top-ignores-external-mappings
   (equal (proof-external-objects head fuel (generated-set-reg 25 top world) objects)
          (proof-external-objects head fuel world objects))
   :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                   :expand (proof-external-objects head fuel (generated-set-reg 25 top world) objects)
                   :in-theory (enable proof-external-objects)))))

(local
 (defthm generated-stack-top-ignores-object-spans
   (equal (proof-heap-object-spans-p objects external (generated-set-reg 25 top world))
          (proof-heap-object-spans-p objects external world))
   :hints (("Goal" :induct (proof-heap-object-spans-p objects external world)
                   :expand (proof-heap-object-spans-p objects external (generated-set-reg 25 top world))
                   :in-theory (enable proof-heap-object-spans-p)))))

(local
 (defthm generated-stack-top-ignores-string-accounting
   (equal (proof-string-accounting-p headers (generated-set-reg 25 top world))
          (proof-string-accounting-p headers world))
   :hints (("Goal" :in-theory (enable proof-string-accounting-p)))))

(local
 (defcong generated-memory-equiv equal (proof-static-size base machine) 2
   :hints (("Goal" :in-theory (enable proof-static-size)))))

(local
 (defthm generated-stack-base-is-natural
   (natp (proof-stack-base world))
   :hints (("Goal"
            :use (:instance generated-word-load-bounds (address (- (proof-heap-base world) 88)))
            :in-theory (enable proof-stack-base proof-runtime-word generated-load-word)))
   :rule-classes :type-prescription))

(local
 (defthm generated-stack-top-is-a-word
   (unsigned-byte-p 64 (proof-stack-top world))
   :hints (("Goal" :in-theory (enable proof-stack-top)))
   :rule-classes ((:type-prescription :corollary (natp (proof-stack-top world)))
                  (:linear :corollary (< (proof-stack-top world) (expt 2 64))))))

(local
 (defthm generated-lowered-stack-top-keeps-heap-layout
   (let ((base (proof-stack-base before)))
     (implies (and (proof-heap-layout-p before) (natp count)
                   (equal top (+ base (* 8 count))) (<= top (proof-stack-top before)))
              (proof-heap-layout-p (generated-set-reg 25 top before))))
   :hints (("Goal"
            :in-theory (e/d (proof-heap-layout-p generated-heap-machine-sp)
                            (proof-covered-p proof-regions-p proof-disjoint-p
                             proof-align-up proof-static-size proof-page-size-p))))))

(defthm generated-lowered-stack-top-preserves-heap
  (let ((after (generated-set-reg 25 top before)))
    (implies (and (proof-heap-p before objects packages)
                  (natp count) (equal top (+ (proof-stack-base before) (* 8 count)))
                  (proof-stack-prefix top before objects packages))
             (and (proof-heap-p after objects packages)
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (equal (proof-stack-top after) top))))
  :hints (("Goal"
           :use generated-lowered-stack-top-keeps-heap-layout
           :in-theory (e/d (proof-heap-p proof-stack-prefix proof-prefix-preserved-p)
                           (proof-stack-views proof-static-size
                            generated-lowered-stack-top-keeps-heap-layout)))))

(local
 (defthm generated-stack-slot-alignment
   (implies (natp count)
            (and (equal (mod (* 8 count) 8) 0)
                 (equal (floor (* 8 count) 8) count)))
   :hints (("Goal"
            :use (:instance generated-floor-of-multiple-and-remainder (divisor 8) (q count) (r 0))
            :in-theory (enable mod)))))

(local
 (defthm generated-stack-slot-difference
   (implies (and (integerp base) (integerp count))
            (equal (+ base (- base) (* 8 count)) (* 8 count)))
   :hints (("Goal" :use (:instance associativity-of-*
                                   (acl2::x 1) (acl2::y 8) (acl2::z count))))))

(defthm generated-lower-stack-prefix-is-valid
  (let ((base (proof-stack-base before)))
    (implies (and (proof-heap-p before objects packages) (natp count)
                  (equal top (+ base (* 8 count))) (<= top (proof-stack-top before)))
             (proof-stack-prefix top before objects packages)))
  :hints (("Goal"
           :use ((:instance generated-stack-views-have-valid-prefix
                            (small count) (large (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (machine (proof-world-machine before)))
                 (:instance generated-byte-count-of-aligned-slots
                            (size (- (proof-stack-top before) (proof-stack-base before)))))
           :in-theory (e/d (proof-heap-p proof-stack-prefix)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-stack-views
                            generated-stack-views-have-valid-prefix)))))

(defthm generated-drop-emission
  (equal (boymoo-compiler::gen-drop count code)
         (boymoo-compiler::reverse-onto (generated-address-items 25 25 (* 8 count) t) code))
  :hints (("Goal" :use (:instance generated-address-accumulator
                                  (register 25) (base 25) (bytes (* 8 count)) (subtract t))
                  :in-theory (enable boymoo-compiler::gen-drop))))

(local
 (defthm generated-drop-changes-only-top-and-scratch
   (let* ((path (generated-address-path 25 25 bytes t))
          (after (generated-path-after path before))
          (top (- (proof-stack-top before) bytes)))
     (implies (unsigned-byte-p 64 bytes)
              (and (generated-heap-world-equiv after (generated-set-reg 25 top before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                   (equal (proof-world-reg 0 after) (proof-world-reg 0 before)))))
   :hints (("Goal"
            :use (:instance generated-wide-word-loads-value (rd 17) (word bytes))
            :in-theory (enable generated-address-path generated-path-after generated-heap-world-equiv
                               proof-stack-top proof-heap-base proof-box-top proof-heap-limit
                               proof-stack-limit proof-machine-limit)))))

(defthm generated-drop-keeps-valid-stack-prefix
  (let* ((bytes (* 8 drop))
         (top (- (proof-stack-top before) bytes))
         (path (generated-address-path 25 25 bytes t))
         (end (+ (proof-world-pc before) (* 4 (len path))))
         (after (generated-path-after path before)))
    (implies (and (natp drop) (natp keep) (unsigned-byte-p 64 bytes)
                  (equal top (+ (proof-stack-base before) (* 8 keep)))
                  (< end (expt 2 64)) (not (proof-world-stop before))
                  (proof-heap-p before objects packages)
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (proof-stack-top after) top)
                  (proof-heap-p after objects packages)
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (generated-heap-world-equiv after (generated-set-reg 25 top before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before)))))
  :hints (("Goal"
           :use ((:instance generated-address-reaches-continuation
                            (rd 25) (rn 25) (bytes (* 8 drop)) (subtract t))
                 (:instance generated-lowered-stack-top-preserves-heap
                            (count keep) (top (- (proof-stack-top before) (* 8 drop))))
                 (:instance generated-lower-stack-prefix-is-valid
                            (count keep) (top (- (proof-stack-top before) (* 8 drop)))))
           :in-theory (disable generated-path-p generated-lower-stack-prefix-is-valid
                               generated-lowered-stack-top-preserves-heap)))
  :rule-classes nil)
