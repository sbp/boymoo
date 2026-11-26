(in-package "BOYMOO-PROOFS")

(include-book "static-frame")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-layout-p proof-heap-p proof-world-machine proof-world-page-size
                    proof-world-regions proof-world-stop proof-runtime-word proof-covered-p
                    proof-page-size-p proof-regions-p
                    proof-stack-base proof-stack-end proof-stack-top proof-stack-limit proof-machine-limit
                    proof-active-floor proof-active-end proof-inactive-floor proof-inactive-end
                    proof-cons-floor proof-spaces-end proof-heap-base proof-box-top proof-heap-limit
                    proof-external-head proof-static-size proof-string-bytes-since-collection proof-string-budget
                    proof-span-p proof-subspan-p proof-disjoint-p proof-align-up
                    generated-sp mod floor expt))

(defund generated-machine-stack-base (world)
  (- (proof-machine-limit world) *proof-machine-margin*))

(defund generated-machine-stack-end (world)
  (+ (generated-machine-stack-base world) *proof-machine-reservation*))

(defund generated-runtime-stack-span-p (start end world)
  (or (proof-subspan-p start (- end start) (proof-stack-base world) (proof-stack-end world))
      (proof-subspan-p start (- end start) (generated-machine-stack-base world)
                       (generated-machine-stack-end world))))

(defund generated-stack-update-p (start end before after)
  (and (generated-runtime-stack-span-p start end before)
       (generated-memory-outside-p start end (proof-world-machine before) (proof-world-machine after))
       (equal (proof-heap-base after) (proof-heap-base before))
       (equal (proof-box-top after) (proof-box-top before))
       (equal (proof-heap-limit after) (proof-heap-limit before))
       (equal (proof-stack-limit after) (proof-stack-limit before))
       (equal (proof-machine-limit after) (proof-machine-limit before))
       (equal (proof-world-regions after) (proof-world-regions before))
       (equal (proof-world-page-size after) (proof-world-page-size before))
       (equal (proof-world-stop after) (proof-world-stop before))
       (<= (proof-stack-base before) (proof-stack-top after))
       (<= (proof-stack-top after) (proof-stack-limit before))
       (equal (mod (proof-stack-top after) 8) 0)
       (<= (generated-machine-stack-base before) (generated-sp after))
       (<= (generated-sp after) (generated-machine-stack-end before))
       (equal (mod (generated-sp after) 16) 0)))

(defthm generated-covered-memory-has-bounded-span
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :hints (("Goal" :induct (proof-covered-p address size access regions)
                  :in-theory (enable proof-covered-p proof-subspan-p)))
  :rule-classes nil)

(local
 (defthm generated-alignment-multiply-reciprocal
   (implies (and (integerp alignment) (< 0 alignment) (integerp address))
            (equal (* alignment (* (/ alignment) address)) address))
   :hints (("Goal"
            :use (:instance associativity-of-* (acl2::x alignment) (acl2::y (/ alignment)) (acl2::z address))
            :in-theory (disable associativity-of-* commutativity-of-*)))
   :rule-classes nil))

(defthm generated-rounding-up-covers-address
  (implies (and (natp address) (posp alignment))
           (<= address (proof-align-up address alignment)))
  :hints (("Goal"
           :use (:instance generated-floor-bounds (x (- address)) (y alignment))
           :in-theory (enable proof-align-up ceiling))
          ("Subgoal 2"
           :use ((:instance rational-implies2 (acl2::x (* address (/ alignment))))
                 generated-alignment-multiply-reciprocal)
           :in-theory (disable rational-implies2))
          ("Subgoal 1"
           :use (:instance generated-floor-bounds (x address) (y alignment))
           :in-theory (enable floor)))
  :rule-classes :linear)

(local
 (defthm generated-heap-base-natural
   (natp (proof-heap-base world))
   :hints (("Goal" :in-theory (enable proof-heap-base)))
   :rule-classes :type-prescription))

(local
 (defthm generated-static-size-natural
   (natp (proof-static-size base machine))
   :hints (("Goal" :in-theory (enable proof-static-size)))
   :rule-classes :type-prescription))

(defthm generated-stack-write-disjoint-from-main-heap
  (let* ((base (proof-heap-base before))
         (upper (proof-spaces-end before))
         (static (proof-static-size base (proof-world-machine before))))
    (implies (and (proof-heap-layout-p before)
                  (generated-runtime-stack-span-p start end before))
             (and (proof-span-p (- base *proof-heap-prefix*) (+ *proof-heap-prefix* (- upper base)))
                  (<= (+ base static 16) upper)
                  (proof-span-p base (+ static 16))
                  (proof-disjoint-p (- base *proof-heap-prefix*) upper start end)
                  (proof-disjoint-p base (+ base static 16) start end))))
  :hints (("Goal"
           :use (:instance generated-covered-memory-has-bounded-span
                           (address (- (proof-heap-base before) *proof-heap-prefix*))
                           (size (+ *proof-heap-prefix* (- (proof-spaces-end before) (proof-heap-base before))))
                           (access :write) (regions (proof-world-regions before)))
           :in-theory (enable proof-heap-layout-p generated-runtime-stack-span-p
                              generated-machine-stack-base generated-machine-stack-end
                              proof-disjoint-p proof-subspan-p proof-span-p generated-heap-machine-sp)))
  :rule-classes nil)

(defthm generated-runtime-word-outside-stack-write
  (implies (and (natp offset) (<= offset 80) (proof-heap-layout-p before)
                (generated-stack-update-p start end before after))
           (equal (proof-runtime-word offset after) (proof-runtime-word offset before)))
  :hints (("Goal"
           :use (generated-stack-write-disjoint-from-main-heap
                 (:instance generated-word-outside-written-span
                            (address (+ (- (proof-heap-base before) 128) offset))
                            (before (proof-world-machine before)) (after (proof-world-machine after))))
           :in-theory (enable generated-stack-update-p proof-runtime-word proof-span-p proof-disjoint-p)))
  :rule-classes nil)

(defthm generated-static-header-outside-stack-write
  (let ((base (proof-heap-base before)))
    (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after))
             (and (equal (proof-static-size base (proof-world-machine after))
                         (proof-static-size base (proof-world-machine before)))
                  (equal (proof-dynamic-root base (proof-world-machine after))
                         (proof-dynamic-root base (proof-world-machine before))))))
  :hints (("Goal"
           :use (generated-stack-write-disjoint-from-main-heap
                 (:instance generated-static-header-outside-written-span
                            (base (proof-heap-base before))
                            (size (+ 16 (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (enable proof-heap-layout-p generated-stack-update-p)))
  :rule-classes nil)

(defthm generated-stack-update-preserves-runtime-fields
  (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after))
           (and (equal (proof-stack-base after) (proof-stack-base before))
                (equal (proof-stack-end after) (proof-stack-end before))
                (equal (proof-spaces-end after) (proof-spaces-end before))
                (equal (proof-active-floor after) (proof-active-floor before))
                (equal (proof-active-end after) (proof-active-end before))
                (equal (proof-inactive-floor after) (proof-inactive-floor before))
                (equal (proof-inactive-end after) (proof-inactive-end before))
                (equal (proof-cons-floor after) (proof-cons-floor before))
                (equal (proof-external-head after) (proof-external-head before))
                (equal (proof-string-bytes-since-collection after) (proof-string-bytes-since-collection before))
                (equal (proof-string-budget after) (proof-string-budget before))))
  :hints (("Goal"
           :use ((:instance generated-runtime-word-outside-stack-write (offset 0))
                 (:instance generated-runtime-word-outside-stack-write (offset 8))
                 (:instance generated-runtime-word-outside-stack-write (offset 16))
                 (:instance generated-runtime-word-outside-stack-write (offset 24))
                 (:instance generated-runtime-word-outside-stack-write (offset 32))
                 (:instance generated-runtime-word-outside-stack-write (offset 40))
                 (:instance generated-runtime-word-outside-stack-write (offset 48))
                 (:instance generated-runtime-word-outside-stack-write (offset 56))
                 (:instance generated-runtime-word-outside-stack-write (offset 64))
                 (:instance generated-runtime-word-outside-stack-write (offset 72))
                 (:instance generated-runtime-word-outside-stack-write (offset 80)))
           :in-theory (enable proof-stack-base proof-stack-end proof-spaces-end proof-active-floor
                              proof-active-end proof-inactive-floor proof-inactive-end proof-cons-floor
                              proof-external-head proof-string-bytes-since-collection proof-string-budget)))
  :rule-classes nil)

(defthm generated-stack-update-preserves-heap-layout
  (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after))
           (proof-heap-layout-p after))
  :hints (("Goal"
           :use (generated-stack-update-preserves-runtime-fields generated-static-header-outside-stack-write)
           :in-theory (enable proof-heap-layout-p generated-stack-update-p generated-machine-stack-end
                              generated-machine-stack-base generated-heap-machine-sp)))
  :rule-classes nil)
