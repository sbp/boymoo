(in-package "BOYMOO-PROOFS")

(include-book "value-stack")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-stop proof-world-regions
                     proof-heap-base proof-stack-base proof-stack-end proof-stack-top proof-stack-limit
                     proof-box-top proof-heap-limit proof-machine-limit proof-static-size proof-load-word
                     proof-active-floor proof-active-end proof-cons-floor proof-spaces-end
                     proof-inactive-floor proof-inactive-end proof-runtime-word
                     proof-heap-p proof-heap-layout-p proof-static-p proof-object-map-p
                     proof-object-size proof-object-address proof-object-kind proof-object-zone
                     proof-region-p proof-regions-p proof-covered-p proof-align-up proof-header-type proof-header-size
                     proof-external-objects proof-disjoint-p proof-span-p proof-subspan-p
                     proof-number-append-storage-p proof-number-value-append-pre-p proof-number-save-interval-p
                     boymoo-model::a64-sp boymoo-model::a64-memory floor mod ash)))

(defund proof-number-stack-footprint-p (start end world)
  (let ((floor (- (proof-machine-limit world) *proof-machine-margin*))
        (bytes (- end start)))
    (or (proof-subspan-p start bytes (proof-stack-base world) (proof-stack-end world))
        (proof-subspan-p start bytes floor (+ floor *proof-machine-reservation*)))))

(local
 (defthm stack-footprint-avoids-heap-interval
   (implies (and (proof-heap-layout-p world)
                 (proof-number-stack-footprint-p start end world)
                 (<= (- (proof-heap-base world) *proof-heap-prefix*) lower)
                 (<= upper (proof-spaces-end world)))
            (proof-disjoint-p start end lower upper))
   :hints (("Goal"
            :use proof-number-heap-layout-separates-reservations
            :in-theory (enable proof-number-stack-footprint-p proof-subspan-p proof-disjoint-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm static-member-fits-static-interval
   (implies (and (member-equal object pending)
                 (eq (proof-object-zone object) :static)
                 (proof-static-spans-p (proof-static-objects pending) base size machine))
            (proof-subspan-p (proof-object-address object) (proof-object-size object machine)
                             (+ 32 base) (+ base size)))
   :hints (("Goal" :induct (proof-static-objects pending)))
   :rule-classes nil))

(local
 (defthm active-member-fits-active-interval
   (implies (and (member-equal object pending)
                 (eq (proof-object-zone object) :active)
                 (proof-heap-object-spans-p pending external world))
            (if (eq (proof-object-kind object) :cons)
                (proof-subspan-p (proof-object-address object)
                                 (proof-object-size object (proof-world-machine world))
                                 (proof-cons-floor world) (proof-active-end world))
              (proof-subspan-p (proof-object-address object)
                               (proof-object-size object (proof-world-machine world))
                               (proof-active-floor world) (proof-box-top world))))
   :hints (("Goal" :induct (proof-heap-object-spans-p pending external world)))
   :rule-classes nil))

(local
 (defthm external-member-is-listed
   (implies (and (member-equal object pending)
                 (eq (proof-object-zone object) :external)
                 (proof-heap-object-spans-p pending external world))
            (member-equal (proof-object-address object) external))
   :hints (("Goal" :induct (proof-heap-object-spans-p pending external world)))
   :rule-classes nil))

(local
 (defthm active-bounds-fit-heap
   (implies (proof-heap-layout-p world)
            (and (<= (- (proof-heap-base world) *proof-heap-prefix*) (proof-active-floor world))
                 (<= (proof-active-floor world) (proof-cons-floor world))
                 (<= (proof-box-top world) (proof-active-end world))
                 (<= (proof-active-end world) (proof-spaces-end world))))
   :hints (("Goal"
            :use proof-number-heap-layout-separates-reservations
            :expand ((proof-heap-layout-p world))
            :in-theory (disable proof-page-size-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm exact-word-count-has-unit-denominator
   (implies (and (integerp words) (equal bytes (* 8 words)))
            (equal (denominator (* 1/8 bytes)) 1))
   :hints (("Goal"
            :use ((:instance proof-number-exact-quotient-value (a bytes) (b 8) (q words)))
            :in-theory (enable proof-exact-quotient-p)))
   :rule-classes nil))

(local
 (defthm strict-integer-gap
   (implies (and (integerp x) (integerp y) (< x y))
            (<= (1+ x) y))
   :hints (("Goal"
            :use ((:instance proof-number-floor-with-remainder (a y) (b 1) (q x)))
            :expand ((floor y 1))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm aligned-to-word-fits-bounded-word-count
   (implies (and (natp bytes) (natp words) (<= bytes (* 8 words)))
            (<= (proof-align-up bytes 8) (* 8 words)))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds (a bytes) (b 8))
                  (:instance proof-number-quotient-of-parts (x (* 1/8 bytes)))
                  (:instance strict-integer-gap (x (floor bytes 8)) (y words))
                  (:instance exact-word-count-has-unit-denominator (words (floor bytes 8))))
            :expand ((floor bytes 8))
            :in-theory (e/d (proof-align-up ceiling)
                            (floor acl2::nonnegative-integer-quotient proof-number-quotient-of-parts
                             acl2::rational-implies2))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm word-alignment-fits-external-mapping
   (implies (natp bytes)
            (<= (+ 32 (proof-align-up bytes 8))
                (proof-align-up (+ 32 bytes) *proof-runtime-page*)))
   :hints (("Goal"
            :use ((:instance proof-number-alignment-does-not-shrink (size (+ 32 bytes)) (alignment *proof-runtime-page*))
                  (:instance aligned-to-word-fits-bounded-word-count
                             (words (- (* 8192 (ceiling (+ 32 bytes) *proof-runtime-page*)) 4))))
            :expand ((proof-align-up (+ 32 bytes) *proof-runtime-page*))
            :in-theory (disable ceiling)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm external-lookup-address
   (implies (assoc-equal address objects)
            (equal (proof-object-address (assoc-equal address objects)) address))
   :hints (("Goal"
            :induct (assoc-equal address objects)
            :in-theory (enable proof-object-address assoc-equal)))))

(local
 (defthm external-mapping-covers-record
   (let* ((address (+ head 24))
          (object (assoc-equal address objects))
          (machine (proof-world-machine world)))
     (implies (and (not (equal head 0))
                   (proof-external-objects head fuel world objects))
              (and (<= head address)
                   (<= (+ address (proof-object-size object machine))
                       (+ head (proof-load-word (+ head 8) machine))))))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds
                             (a (proof-load-word (+ head 24) (proof-world-machine world))) (b 256))
                  (:instance word-alignment-fits-external-mapping
                             (bytes (proof-header-size (proof-load-word (+ head 24) (proof-world-machine world))))))
            :expand ((proof-external-objects head fuel world objects))
            :in-theory (e/d (proof-object-size proof-header-size) (assoc-equal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm external-current-record-avoids-stack-footprint
   (let* ((address (+ head 24))
          (object (assoc-equal address objects))
          (machine (proof-world-machine world)))
     (implies (and (not (equal head 0))
                   (proof-external-objects head fuel world objects)
                   (proof-number-stack-footprint-p start end world))
              (proof-disjoint-p start end address (+ address (proof-object-size object machine)))))
   :hints (("Goal"
            :use external-mapping-covers-record
            :expand ((proof-external-objects head fuel world objects))
            :in-theory (e/d (proof-number-stack-footprint-p proof-subspan-p proof-disjoint-p)
                            (assoc-equal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm external-chain-step
   (let ((next (proof-external-objects (proof-load-word head (proof-world-machine world)) (1- fuel) world objects)))
     (implies (and (not (equal head 0)) (proof-external-objects head fuel world objects))
              (and next
                   (equal (cdr (proof-external-objects head fuel world objects))
                          (cons (+ 24 head) (cdr next))))))
   :hints (("Goal"
            :expand ((proof-external-objects head fuel world objects))
            :in-theory (disable assoc-equal)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defun external-chain-induction (head fuel world)
   (declare (xargs :measure (nfix fuel)))
   (if (or (equal head 0) (zp fuel))
       nil
     (external-chain-induction (proof-load-word head (proof-world-machine world)) (1- fuel) world))))

(local
 (defthm external-list-record-avoids-stack-footprint
   (let* ((external (proof-external-objects head fuel world objects))
          (object (assoc-equal address objects))
          (machine (proof-world-machine world)))
     (implies (and external (member-equal address (cdr external))
                   (proof-number-stack-footprint-p start end world))
              (proof-disjoint-p start end address (+ address (proof-object-size object machine)))))
   :hints (("Goal"
            :induct (external-chain-induction head fuel world)
            :in-theory (disable assoc-equal))
           ("Subgoal *1/2"
            :use (external-chain-step external-current-record-avoids-stack-footprint)
            :do-not-induct t)
           ("Subgoal *1/1"
            :expand ((proof-external-objects head fuel world objects)
                     (proof-external-objects 0 fuel world objects))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm map-member-avoids-stack-footprint
   (let* ((machine (proof-world-machine world))
          (address (proof-object-address object))
          (limit (+ address (proof-object-size object machine))))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-stack-footprint-p start end world)
                   (member-equal object objects))
              (proof-disjoint-p start end address limit)))
   :hints (("Goal"
            :use ((:instance proof-number-object-map-member-record-and-lookup
                             (pending objects) (symbols nil) (base (proof-heap-base world))
                             (machine (proof-world-machine world)))
                  (:instance static-member-fits-static-interval
                             (pending objects) (base (proof-heap-base world)) (machine (proof-world-machine world))
                             (size (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                  (:instance active-member-fits-active-interval
                             (pending objects) (external (cdr (proof-external-objects
                                                               (proof-external-head world) (len objects) world objects))))
                  (:instance external-member-is-listed
                             (pending objects) (external (cdr (proof-external-objects
                                                               (proof-external-head world) (len objects) world objects))))
                  (:instance external-list-record-avoids-stack-footprint
                             (address (proof-object-address object)) (head (proof-external-head world))
                             (fuel (len objects)))
                  proof-number-heap-layout-range-bounds active-bounds-fit-heap
                  (:instance stack-footprint-avoids-heap-interval
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object)
                                       (proof-object-size object (proof-world-machine world))))))
            :in-theory (e/d (proof-heap-p proof-static-p proof-subspan-p)
                            (proof-external-head proof-static-objects proof-static-spans-p proof-heap-object-spans-p
                             proof-stack-prefix proof-object-record-p proof-packages-p proof-dynamic-entries
                             proof-dynamic-view proof-string-accounting-p assoc-equal))
            :expand ((proof-object-record-p object))
            :cases ((eq (proof-object-zone object) :static) (eq (proof-object-zone object) :active))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm object-subset-survives-cons
   (implies (subsetp-equal pending objects)
            (subsetp-equal pending (cons object objects)))
   :hints (("Goal" :induct (len pending)))
   :rule-classes nil))

(local
 (defthm object-list-is-own-subset
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (len objects))
           ("Subgoal *1/1"
            :use ((:instance object-subset-survives-cons
                             (pending (cdr objects)) (objects (cdr objects)) (object (car objects))))))))

(local
 (defthm map-subset-avoids-stack-footprint
   (implies (and (proof-heap-p world objects packages)
                 (proof-number-stack-footprint-p start end world)
                 (subsetp-equal pending objects))
            (proof-object-disjoint-p start end pending (proof-world-machine world)))
   :hints (("Goal" :induct (len pending))
           ("Subgoal *1/1"
            :use ((:instance map-member-avoids-stack-footprint (object (car pending))))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-stack-footprint-avoids-objects
  (implies (and (proof-heap-p world objects packages)
                (proof-number-stack-footprint-p start end world))
           (proof-object-disjoint-p start end objects (proof-world-machine world)))
  :hints (("Goal"
           :use ((:instance map-subset-avoids-stack-footprint (pending objects)))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-heap-gives-machine-save-locality
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (floor (- (proof-machine-limit world) *proof-machine-margin*)))
    (implies (and (proof-heap-p world objects packages)
                  (posp start) (<= floor start) (proof-span-p start (- sp start)))
             (proof-number-save-interval-p start world objects)))
  :hints (("Goal"
           :use (proof-number-heap-layout-separates-reservations
                 (:instance proof-number-stack-footprint-avoids-objects
                            (end (boymoo-model::a64-sp (proof-world-machine world)))))
           :in-theory (e/d (proof-number-save-interval-p proof-number-stack-footprint-p proof-subspan-p)
                           (proof-object-disjoint-p))
           :expand ((proof-heap-p world objects packages))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm value-append-footprint-and-metadata-bounds
   (let* ((top (proof-stack-top world))
          (base (proof-heap-base world))
          (end (+ top size)))
     (implies (and (proof-heap-layout-p world) (natp size)
                   (posp top) (unsigned-byte-p 64 end) (<= end (proof-stack-limit world)))
              (and (proof-number-stack-footprint-p top end world)
                   (proof-span-p top size)
                   (proof-span-p (- base 88) 8)
                   (<= (- base 80) (proof-spaces-end world)))))
   :hints (("Goal"
            :use (proof-number-heap-layout-separates-reservations proof-number-heap-layout-range-bounds)
            :expand ((proof-heap-layout-p world))
            :in-theory (e/d (proof-number-stack-footprint-p proof-subspan-p proof-span-p)
                            (proof-page-size-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-heap-gives-value-append-locality
  (let* ((top (proof-stack-top world))
         (size (* 8 arity))
         (end (+ top size)))
    (implies (and (proof-heap-p world objects packages)
                  (member-equal arity '(1 2))
                  (not (eq (car (proof-world-machine world)) :svc))
                  (posp top) (unsigned-byte-p 64 end)
                  (<= end (proof-stack-limit world)))
             (proof-number-value-append-pre-p arity world objects packages)))
  :hints (("Goal"
           :use (proof-number-heap-machine-context
                 (:instance value-append-footprint-and-metadata-bounds (size (* 8 arity)))
                 (:instance proof-number-stack-footprint-avoids-objects
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity))))
                 (:instance stack-footprint-avoids-heap-interval
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (lower (- (proof-heap-base world) 88)) (upper (- (proof-heap-base world) 80))))
           :expand ((proof-heap-p world objects packages))
           :in-theory (e/d (proof-number-value-append-pre-p proof-number-append-storage-p proof-disjoint-p)
                           (proof-stack-prefix proof-object-disjoint-p proof-heap-object-spans-p proof-external-head
                            proof-dynamic-entries proof-dynamic-view proof-dynamic-symbol-objects-p
                            proof-string-accounting-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-checked-argument-store-from-heap
  (let* ((arity (len args))
         (top (proof-stack-top world))
         (end (+ top (* 8 arity)))
         (pc (+ 8 (proof-world-pc world)))
         (code (proof-number-formula-argument-store-instructions arity)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-argument-list-p args)
                  (proof-register-arguments-p args 0 world objects packages)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (posp top) (unsigned-byte-p 64 end) (<= end (proof-stack-limit world))
                  (unsigned-byte-p 64 pc)
                  (equal (proof-world-reg 19 world) top)
                  (proof-number-checked-block-p code (list pc) world)
                  (proof-number-checked-block-p code (list link) world))
             (and (proof-number-value-append-pre-p arity world objects packages)
                  (proof-number-formula-argument-trace-p args link world objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-heap-gives-value-append-locality (arity (len args)))
                 proof-number-argument-trace-from-disjoint-store)
           :in-theory (e/d (proof-number-value-append-pre-p proof-number-argument-list-p)
                           (proof-number-formula-argument-store-instructions proof-register-arguments-p
                            proof-number-formula-argument-trace-p proof-number-checked-block-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-checked-spill-store-from-heap
  (let* ((top (proof-stack-top world))
         (end (+ top 8))
         (pc (+ 8 (proof-world-pc world))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-reg-value-p 0 value world objects packages)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (posp top) (unsigned-byte-p 64 end) (<= end (proof-stack-limit world))
                  (unsigned-byte-p 64 pc)
                  (proof-number-checked-block-p *proof-number-formula-spill-instructions* (list pc) world)
                  (proof-number-checked-block-p *proof-number-formula-spill-instructions* (list link) world))
             (and (proof-number-value-append-pre-p 1 world objects packages)
                  (proof-number-formula-spill-trace-p value link world objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-heap-gives-value-append-locality (arity 1))
                 proof-number-spill-trace-from-disjoint-store)
           :in-theory (e/d (proof-number-value-append-pre-p)
                           (proof-reg-value-p proof-number-checked-block-p proof-number-formula-spill-trace-p))
           :do-not-induct t))
  :rule-classes nil)
