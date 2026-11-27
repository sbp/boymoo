(in-package "BOYMOO-PROOFS")

(include-book "heap-frame")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-stop proof-world-page-size
                     proof-world-regions proof-load-word proof-view proof-heap-p
                     proof-covered-p proof-heap-layout-p proof-align-up proof-regions-p
                     proof-static-size proof-dynamic-root
                     proof-number-machine-span-agrees-p boymoo-model::a64-sp
                     boymoo-model::a64-unsigned boymoo-model::a64-memory mod floor ash)))

(defun proof-number-runtime-words (offsets world)
  (if (atom offsets)
      nil
    (cons (proof-runtime-word (car offsets) world)
          (proof-number-runtime-words (cdr offsets) world))))

(defconst *proof-number-runtime-word-offsets*
  '(0 8 16 24 32 40 48 56 64 72 80))

(defund proof-number-heap-coordinates (world)
  (let ((base (proof-heap-base world))
        (machine (proof-world-machine world)))
    (list base
          (proof-machine-limit world)
          (proof-stack-limit world)
          (proof-heap-limit world)
          (proof-box-top world)
          (proof-world-page-size world)
          (proof-world-regions world)
          (proof-static-size base machine)
          (proof-dynamic-root base machine)
          (proof-number-runtime-words *proof-number-runtime-word-offsets* world))))

(local
 (defun runtime-offsets-p (offsets)
   (if (atom offsets)
       t
     (and (natp (car offsets)) (<= (car offsets) 80) (runtime-offsets-p (cdr offsets))))))

(local
 (defthm runtime-words-in-metadata-span-agree
   (let* ((base (proof-heap-base before))
          (first (proof-world-machine before))
          (last (proof-world-machine after)))
     (implies (and (runtime-offsets-p offsets)
                   (equal (proof-heap-base after) base)
                   (natp base) (<= 128 base) (<= (+ base 32) (expt 2 64))
                   (proof-number-machine-span-agrees-p (- base 128) (+ base 32) first last))
              (equal (proof-number-runtime-words offsets after)
                     (proof-number-runtime-words offsets before))))
   :hints (("Goal"
            :induct (proof-number-runtime-words offsets before)
            :in-theory (disable proof-heap-base proof-runtime-word))
           ("Subgoal *1/2"
            :use ((:instance proof-number-word-agrees-in-machine-span
                             (address (+ (- (proof-heap-base before) 128) (car offsets)))
                             (lower (- (proof-heap-base before) 128))
                             (upper (+ (proof-heap-base before) 32))
                             (first (proof-world-machine before))
                             (last (proof-world-machine after))))
            :in-theory (enable proof-runtime-word)))
   :rule-classes nil))

(defthm proof-number-metadata-span-keeps-heap-coordinates
  (let* ((base (proof-heap-base before))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and (equal (proof-heap-base after) base)
                  (equal (proof-machine-limit after) (proof-machine-limit before))
                  (equal (proof-stack-limit after) (proof-stack-limit before))
                  (equal (proof-heap-limit after) (proof-heap-limit before))
                  (equal (proof-box-top after) (proof-box-top before))
                  (equal (proof-world-page-size after) (proof-world-page-size before))
                  (equal (proof-world-regions after) (proof-world-regions before))
                  (natp base) (<= 128 base) (<= (+ base 32) (expt 2 64))
                  (proof-number-machine-span-agrees-p (- base 128) (+ base 32) first last))
             (equal (proof-number-heap-coordinates after) (proof-number-heap-coordinates before))))
  :hints (("Goal"
           :use ((:instance runtime-words-in-metadata-span-agree
                            (offsets *proof-number-runtime-word-offsets*))
                 (:instance proof-number-word-agrees-in-machine-span
                            (address (proof-heap-base before))
                            (lower (- (proof-heap-base before) 128))
                            (upper (+ (proof-heap-base before) 32))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-word-agrees-in-machine-span
                            (address (+ 24 (proof-heap-base before)))
                            (lower (- (proof-heap-base before) 128))
                            (upper (+ (proof-heap-base before) 32))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (e/d (proof-number-heap-coordinates proof-static-size proof-dynamic-root)
                           (proof-number-runtime-words proof-heap-base proof-runtime-word))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-covered-range-is-a-span
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :hints (("Goal" :induct (proof-covered-p address size access regions)
                  :in-theory (e/d (proof-covered-p) (proof-span-p))))
  :rule-classes nil)

(defthm proof-number-heap-layout-range-bounds
  (let ((base (proof-heap-base world))
        (machine (proof-world-machine world)))
    (implies (proof-heap-layout-p world)
             (and (<= *proof-heap-prefix* base)
                  (<= (+ base (proof-static-size base machine)) (proof-spaces-end world))
                  (<= (proof-spaces-end world) (expt 2 64))
                  (<= (proof-stack-end world) (expt 2 64))
                  (<= (+ (- (proof-machine-limit world) *proof-machine-margin*)
                         *proof-machine-reservation*)
                      (expt 2 64)))))
  :hints (("Goal"
           :use ((:instance proof-number-covered-range-is-a-span
                            (address (- (proof-heap-base world) *proof-heap-prefix*))
                            (size (+ *proof-heap-prefix*
                                     (- (proof-spaces-end world) (proof-heap-base world))))
                            (access :write) (regions (proof-world-regions world)))
                 (:instance proof-number-covered-range-is-a-span
                            (address (proof-stack-base world)) (size *proof-value-reservation*)
                            (access :write) (regions (proof-world-regions world)))
                 (:instance proof-number-covered-range-is-a-span
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (size *proof-machine-reservation*)
                            (access :write) (regions (proof-world-regions world)))
                 (:instance proof-number-alignment-does-not-shrink
                            (size (+ (proof-heap-base world)
                                     (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                            (alignment *proof-runtime-page*))
                 (:instance proof-number-reg-range
                            (register 28) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-heap-layout-p proof-heap-base)
                           (proof-runtime-word proof-disjoint-p proof-reg proof-stack-base
                            proof-stack-end proof-spaces-end))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-equal-heap-coordinates-preserve-fields
  (implies (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
           (and (equal (proof-heap-base before) (proof-heap-base after))
                (equal (proof-static-size (proof-heap-base before) (proof-world-machine before))
                       (proof-static-size (proof-heap-base after) (proof-world-machine after)))
                (equal (proof-dynamic-root (proof-heap-base before) (proof-world-machine before))
                       (proof-dynamic-root (proof-heap-base after) (proof-world-machine after)))
                (equal (proof-machine-limit before) (proof-machine-limit after))
                (equal (proof-stack-limit before) (proof-stack-limit after))
                (equal (proof-heap-limit before) (proof-heap-limit after))
                (equal (proof-box-top before) (proof-box-top after))
                (equal (proof-world-regions before) (proof-world-regions after))
                (equal (proof-world-page-size before) (proof-world-page-size after))
                (equal (proof-active-floor before) (proof-active-floor after))
                (equal (proof-active-end before) (proof-active-end after))
                (equal (proof-cons-floor before) (proof-cons-floor after))
                (equal (proof-inactive-floor before) (proof-inactive-floor after))
                (equal (proof-inactive-end before) (proof-inactive-end after))
                (equal (proof-stack-base before) (proof-stack-base after))
                (equal (proof-stack-end before) (proof-stack-end after))
                (equal (proof-external-head before) (proof-external-head after))
                (equal (proof-spaces-end before) (proof-spaces-end after))
                (equal (proof-string-bytes-since-collection before) (proof-string-bytes-since-collection after))
                (equal (proof-string-budget before) (proof-string-budget after))))
  :hints (("Goal"
           :in-theory (e/d (proof-number-heap-coordinates)
                           (proof-runtime-word proof-heap-base))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-coordinate-equality-keeps-layout
  (let* ((floor (- (proof-machine-limit before) *proof-machine-margin*))
         (sp (boymoo-model::a64-sp (proof-world-machine after)))
         (top (proof-stack-top after)))
    (implies (and (proof-heap-layout-p before)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (not (proof-world-stop after))
                  (<= floor sp) (<= sp (+ floor *proof-machine-reservation*))
                  (equal (mod sp 16) 0)
                  (<= (proof-stack-base before) top) (<= top (proof-stack-limit before))
                  (equal (mod top 8) 0))
             (proof-heap-layout-p after)))
  :hints (("Goal"
           :use proof-number-equal-heap-coordinates-preserve-fields
           :in-theory (e/d (proof-heap-layout-p)
                           (proof-runtime-word proof-disjoint-p proof-heap-base proof-stack-base
                            proof-stack-end proof-stack-limit proof-heap-limit proof-box-top
                            proof-machine-limit proof-active-floor proof-active-end proof-cons-floor
                            proof-inactive-floor proof-inactive-end proof-spaces-end proof-page-size-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-heap-layout-separates-reservations
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (static (proof-static-size base machine))
         (heap-start (- base *proof-heap-prefix*))
         (heap-end (proof-spaces-end world))
         (stack-start (proof-stack-base world))
         (stack-end (proof-stack-end world))
         (sp (boymoo-model::a64-sp machine))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (proof-heap-layout-p world)
             (and (natp base) (<= *proof-heap-prefix* base)
                  (<= 80 static)
                  (<= (+ base static) (proof-active-floor world))
                  (<= (proof-box-top world) heap-end)
                  (natp heap-end)
                  (natp stack-start) (natp stack-end)
                  (natp machine-start) (natp machine-end)
                  (<= (proof-stack-top world) stack-end)
                  (<= machine-start sp) (<= sp machine-end)
                  (proof-disjoint-p heap-start heap-end stack-start stack-end)
                  (proof-disjoint-p heap-start heap-end machine-start machine-end)
                  (proof-disjoint-p stack-start stack-end machine-start machine-end))))
  :hints (("Goal"
           :use ((:instance proof-number-alignment-does-not-shrink
                            (size (+ (proof-heap-base world)
                                     (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                            (alignment *proof-runtime-page*))
                 (:instance proof-number-reg-range
                            (register 28) (machine (proof-world-machine world)))
                 (:instance proof-number-covered-range-is-a-span
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (size *proof-machine-reservation*)
                            (access :write) (regions (proof-world-regions world))))
           :expand ((proof-heap-layout-p world))
           :in-theory (e/d (proof-heap-base)
                           (proof-align-up proof-disjoint-p proof-runtime-word proof-reg
                            proof-heap-limit proof-box-top proof-stack-limit proof-machine-limit
                            proof-stack-base proof-stack-top proof-stack-end proof-spaces-end
                            proof-active-floor proof-active-end proof-inactive-floor proof-inactive-end
                            proof-cons-floor))
           :do-not-induct t))
  :rule-classes nil)
