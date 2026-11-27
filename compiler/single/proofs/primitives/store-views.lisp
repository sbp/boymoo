(in-package "BOYMOO-PROOFS")

(include-book "machine-stack")
(include-book "mapped-data")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-stack-store-p (address world)
  (let ((machine-start (p6-machine-reservation-start world)))
    (or (proof-subspan-p address 16 (proof-stack-base world) (proof-stack-end world))
        (proof-subspan-p address 16 machine-start (+ machine-start *proof-machine-reservation*)))))

(defund p6-span-avoids-pair-p (start size address)
  (or (zp size)
      (and (proof-span-p start size)
           (proof-disjoint-p start (+ start size) address (+ address 16)))))

(defun p6-object-spans-avoid-pair-p (objects address machine)
  (if (atom objects)
      t
    (let* ((object (car objects))
           (start (proof-object-address object)))
      (and (p6-span-avoids-pair-p start (p6-object-content-size start object machine) address)
           (p6-object-spans-avoid-pair-p (cdr objects) address machine)))))

(local (in-theory (disable proof-heap-p proof-object-map-p proof-load-word proof-load-string
                           proof-integer-view proof-view proof-object-kind
                           proof-header-size proof-header-type p6-loaded-header-fields
                           p6-load-equality-is-byte-list-equality)))

(defthm p6-pair-store-has-valid-span
  (implies (p6-stack-store-p address world)
           (proof-span-p address 16))
  :hints (("Goal" :in-theory (enable p6-stack-store-p proof-subspan-p))))

(local
 (defthm p6-small-positive-subspan-avoids-pair
   (implies (and (p6-span-avoids-pair-p start length address)
                 (integerp length) (integerp offset) (<= 0 offset)
                 (posp width) (<= (+ offset width) length))
            (p6-span-avoids-pair-p (+ offset start) width address))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-span-avoids-pair-p proof-span-p proof-disjoint-p)))))

(local
 (defthm p6-store-in-reservation-avoids-disjoint-span
   (implies (and (p6-stack-store-p address world)
                 (proof-span-p start size)
                 (p6-reservations-disjoint-p start (+ start size) world))
            (p6-span-avoids-pair-p start size address))
   :hints (("Goal" :in-theory (enable p6-stack-store-p p6-span-avoids-pair-p
                                      p6-reservations-disjoint-p proof-subspan-p proof-disjoint-p)))))

(local
 (defthm p6-record-lookup-of-member
   (implies (and (consp object) (member-equal object objects) (p6-object-addresses-unique-p objects))
            (equal (assoc-equal (proof-object-address object) objects) object))
   :hints (("Goal" :induct (member-equal object objects)
                   :in-theory (enable proof-object-address)))))

(local
 (defthm p6-member-of-object-map-is-record
   (implies (and (member-equal object pending)
                 (proof-object-map-p pending objects symbols base packages machine))
            (consp object))
   :rule-classes nil
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                   :in-theory (e/d ((:induction proof-object-map-p))
                                   (proof-object-size proof-object-view
                                    proof-object-disjoint-p proof-symbol-object-p))
                   :expand ((:free (seen) (proof-object-map-p pending objects seen base packages machine)))))))

(local
 (defthm p6-heap-object-is-its-lookup
   (implies (and (proof-heap-p world objects packages) (member-equal object objects))
            (and (consp object)
                 (equal (assoc-equal (proof-object-address object) objects) object)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-heap-p)
                            (proof-heap-layout-p proof-static-p proof-external-objects
                             proof-heap-object-spans-p proof-dynamic-view proof-dynamic-entries
                             proof-dynamic-symbol-objects-p proof-string-accounting-p proof-stack-prefix))
            :use (p6-record-lookup-of-member
                  (:instance p6-member-of-object-map-is-record
                             (pending objects) (symbols nil) (base (proof-heap-base world))
                             (machine (proof-world-machine world)))
                  (:instance p6-object-map-has-unique-addresses
                             (pending objects) (symbols nil) (base (proof-heap-base world))
                             (machine (proof-world-machine world))))
            :do-not-induct t))))

(local
 (defthm p6-heap-record-avoids-stack-store
   (let ((start (proof-object-address object))
         (machine (proof-world-machine world)))
     (implies (and (proof-heap-p world objects packages)
                   (member-equal object objects) (p6-stack-store-p address world))
              (p6-span-avoids-pair-p start (p6-object-content-size start object machine) address)))
   :rule-classes nil
   :hints (("Goal"
            :use (p6-heap-object-is-its-lookup
                  (:instance p6-published-object-contents-avoid-stacks
                             (address (proof-object-address object))))))))

(local
 (defthm p6-stack-store-avoids-subset-of-objects
   (implies (and (proof-heap-p world objects packages) (subsetp-equal pending objects)
                 (p6-stack-store-p address world))
            (p6-object-spans-avoid-pair-p pending address (proof-world-machine world)))
   :rule-classes nil
   :hints (("Goal" :induct (len pending))
           ("Subgoal *1/1" :use ((:instance p6-heap-record-avoids-stack-store (object (car pending))))))))

(local
 (defthm p6-subset-of-cons
   (implies (subsetp-equal first second)
            (subsetp-equal first (cons object second)))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm p6-subset-of-itself
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (len objects)))))

(defthm p6-stack-store-avoids-published-objects
  (implies (and (proof-heap-p world objects packages) (p6-stack-store-p address world))
           (p6-object-spans-avoid-pair-p objects address (proof-world-machine world)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance p6-stack-store-avoids-subset-of-objects (pending objects))))))

(defthm p6-static-object-spans-avoid-pair
  (implies (p6-object-spans-avoid-pair-p objects address machine)
           (p6-object-spans-avoid-pair-p (proof-static-objects objects) address machine))
  :hints (("Goal" :induct (proof-static-objects objects))))

(local
 (defthm p6-assoc-record-is-a-cons
   (implies start (iff (consp (assoc-equal start objects)) (assoc-equal start objects)))
   :hints (("Goal" :induct (assoc-equal start objects)))))

(local
 (defthm p6-lookup-object-span-avoids-pair
   (let* ((record (assoc-equal start objects))
          (size (p6-object-content-size start record machine)))
     (implies (and (consp record) (p6-object-spans-avoid-pair-p objects address machine))
              (p6-span-avoids-pair-p start size address)))
   :rule-classes nil
   :hints (("Goal" :induct (assoc-equal start objects)
                   :in-theory (enable proof-object-address)))))

(defthm p6-proof-load-word-after-disjoint-pair-store
  (implies (and (proof-span-p address 16) (p6-span-avoids-pair-p start 8 address))
           (equal (proof-load-word start (proof-world-machine (p6-store-register-pair first second address world)))
                  (proof-load-word start (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable p6-span-avoids-pair-p proof-load-word p6-world-load)
                  :use ((:instance p6-load-outside-stored-register-pair (width 8) (source start))))))

(defthm p6-byte-list-after-disjoint-pair-store
  (implies (and (proof-span-p address 16) (p6-span-avoids-pair-p start count address))
           (equal (proof-byte-list count start (proof-world-machine (p6-store-register-pair first second address world)))
                  (proof-byte-list count start (proof-world-machine world))))
  :hints (("Goal"
           :in-theory (enable p6-span-avoids-pair-p p6-world-load
                              p6-load-equality-is-byte-list-equality)
           :use ((:instance p6-load-outside-stored-register-pair (width count) (source start))))))

(local
 (defthm p6-load-string-after-disjoint-pair-store
   (implies (and (proof-span-p address 16) (p6-span-avoids-pair-p start count address))
            (equal (proof-load-string count start (proof-world-machine (p6-store-register-pair first second address world)))
                   (proof-load-string count start (proof-world-machine world))))
   :hints (("Goal" :in-theory (enable proof-load-string)))))

(local
 (defthm p6-first-word-of-span-avoids-pair
   (implies (and (posp count) (p6-span-avoids-pair-p start (* 8 count) address))
            (p6-span-avoids-pair-p start 8 address))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-span-avoids-pair-p proof-span-p proof-disjoint-p)))))

(local
 (defthm p6-remaining-words-of-span-avoid-pair
   (implies (and (posp count) (p6-span-avoids-pair-p start (* 8 count) address))
            (p6-span-avoids-pair-p (+ 8 start) (* 8 (1- count)) address))
   :rule-classes nil
   :hints (("Goal"
            :cases ((equal count 1))
            :in-theory (enable p6-span-avoids-pair-p)
            :use ((:instance p6-small-positive-subspan-avoids-pair
                             (length (* 8 count)) (offset 8) (width (* 8 (1- count)))))))))

(local
 (defun p6-word-span-induction (count start)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       start
     (p6-word-span-induction (1- count) (+ 8 start)))))

(local
 (defthm p6-limbs-after-disjoint-pair-store
   (implies (and (proof-span-p address 16) (p6-span-avoids-pair-p start (* 8 (nfix count)) address))
            (let ((after (proof-world-machine (p6-store-register-pair first second address world))))
              (and (equal (proof-limb-magnitude count start after)
                          (proof-limb-magnitude count start (proof-world-machine world)))
                   (equal (proof-limbs-p count start after)
                          (proof-limbs-p count start (proof-world-machine world))))))
   :rule-classes nil
   :hints (("Goal" :induct (p6-word-span-induction count start)
                   :expand ((:free (memory) (proof-limbs-p count start memory))))
           ("Subgoal *1/2"
            :use ((:instance p6-first-word-of-span-avoids-pair)
                  (:instance p6-remaining-words-of-span-avoid-pair))))))

(local
 (defthm p6-header-size-is-natural
   (natp (proof-header-size (proof-load-word start machine)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load)
                   :use ((:instance p6-loaded-header-fields (address start)))))))

(local
 (defthm p6-parts-of-header-span-avoid-pair
   (implies (and (natp size) (p6-span-avoids-pair-p start (+ 8 size) address))
            (and (p6-span-avoids-pair-p start 8 address)
                 (p6-span-avoids-pair-p (+ 8 start) size address)
                 (implies (<= 8 size) (p6-span-avoids-pair-p (+ 8 start) 8 address))
                 (implies (<= 16 size) (p6-span-avoids-pair-p (+ 16 start) 8 address))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-span-avoids-pair-p proof-span-p proof-disjoint-p)))))

(local
 (defthm p6-two-word-span-avoids-pair
   (implies (p6-span-avoids-pair-p start 16 address)
            (and (p6-span-avoids-pair-p start 8 address)
                 (p6-span-avoids-pair-p (+ 8 start) 8 address)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-span-avoids-pair-p proof-span-p proof-disjoint-p)))))

(local
 (defthm p6-payload-word-count-avoids-pair
   (implies (and (natp size) (p6-span-avoids-pair-p start (+ 8 size) address))
            (p6-span-avoids-pair-p (+ 8 start) (* 8 (nfix (ash size -3))) address))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable p6-span-avoids-pair-p proof-span-p)
            :use ((:instance p6-floor-bounds (x size) (d 8)))))))

(local
 (defthm p6-integer-limb-span-avoids-pair
   (implies (and (natp size) (<= 8 size) (p6-span-avoids-pair-p start (+ 8 size) address))
            (p6-span-avoids-pair-p (+ 16 start) (* 8 (nfix (1- (ash size -3)))) address))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable p6-span-avoids-pair-p proof-span-p)
            :use ((:instance p6-floor-bounds (x size) (d 8)))))))

(local
 (defthm p6-integer-view-after-disjoint-pair-store
   (let* ((machine (proof-world-machine world))
          (size (proof-header-size (proof-load-word start machine)))
          (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-span-p address 16)
                   (p6-span-avoids-pair-p start (+ 8 size) address))
              (equal (proof-integer-view start after) (proof-integer-view start machine))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable proof-integer-view)
            :use ((:instance p6-parts-of-header-span-avoid-pair
                             (size (proof-header-size (proof-load-word start (proof-world-machine world)))))
                  (:instance p6-integer-limb-span-avoids-pair
                             (size (proof-header-size (proof-load-word start (proof-world-machine world)))))
                  (:instance p6-limbs-after-disjoint-pair-store
                             (start (+ 16 start))
                             (count (1- (ash (proof-header-size
                                              (proof-load-word start (proof-world-machine world))) -3)))))))))

(local
 (defthm p6-record-reads-after-disjoint-pair-store
   (let* ((record (assoc-equal start objects))
          (machine (proof-world-machine world))
          (after (proof-world-machine (p6-store-register-pair first second address world)))
          (size (proof-header-size (proof-load-word start machine))))
     (implies (and (consp record) (proof-span-p address 16)
                   (p6-object-spans-avoid-pair-p objects address machine))
              (and (equal (proof-load-word start after) (proof-load-word start machine))
                   (implies (eq (proof-object-kind record) :cons)
                            (equal (proof-load-word (+ 8 start) after) (proof-load-word (+ 8 start) machine)))
                   (implies (not (eq (proof-object-kind record) :cons))
                            (and (equal (proof-load-string size (+ 8 start) after)
                                        (proof-load-string size (+ 8 start) machine))
                                 (equal (proof-integer-view start after) (proof-integer-view start machine))
                                 (p6-span-avoids-pair-p (+ 8 start) (* 8 (nfix (ash size -3))) address)
                                 (implies (<= 8 size)
                                          (equal (proof-load-word (+ 8 start) after)
                                                 (proof-load-word (+ 8 start) machine)))
                                 (implies (<= 16 size)
                                          (equal (proof-load-word (+ 16 start) after)
                                                 (proof-load-word (+ 16 start) machine))))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable p6-object-content-size)
            :use ((:instance p6-lookup-object-span-avoids-pair (machine (proof-world-machine world)))
                  p6-two-word-span-avoids-pair
                  (:instance p6-parts-of-header-span-avoid-pair
                             (size (proof-header-size (proof-load-word start (proof-world-machine world)))))
                  (:instance p6-payload-word-count-avoids-pair
                             (size (proof-header-size (proof-load-word start (proof-world-machine world)))))
                  p6-integer-view-after-disjoint-pair-store)))))

(local
 (defun p6-view-store-induction (kind input count depth base objects world)
   (declare (xargs :measure (make-ord 1 (1+ (nfix depth))
                                       (if (eq kind :slots) (1+ (nfix count)) 0))))
   (let ((machine (proof-world-machine world)))
     (if (eq kind :slots)
         (if (zp count)
             nil
           (list (p6-view-store-induction :word (proof-load-word input machine) 0 depth base objects world)
                 (p6-view-store-induction :slots (+ 8 input) (1- count) depth base objects world)))
       (let* ((start (proof-pointer-address input base))
              (record (assoc-equal start objects))
              (rank (proof-object-rank record)))
         (and record (natp rank) (< rank (nfix depth))
              (list (p6-view-store-induction :word (proof-load-word start machine) 0 rank base objects world)
                    (p6-view-store-induction :word (proof-load-word (+ 8 start) machine) 0 rank base objects world)
                    (p6-view-store-induction :word (proof-load-word (+ 16 start) machine) 0 rank base objects world)
                    (p6-view-store-induction :slots (+ 8 start)
                                             (ash (proof-header-size (proof-load-word start machine)) -3)
                                             rank base objects world))))))))

(local
 (defthm p6-view-step-after-disjoint-pair-store
   (let ((machine (proof-world-machine world))
         (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-span-p address 16)
                   (p6-object-spans-avoid-pair-p objects address machine)
                   (implies (eq kind :slots)
                            (p6-span-avoids-pair-p input (* 8 (nfix count)) address)))
              (equal (proof-view-step kind input count depth base objects packages after)
                     (proof-view-step kind input count depth base objects packages machine))))
   :rule-classes nil
   :hints (("Goal"
            :induct (p6-view-store-induction kind input count depth base objects world)
            :in-theory (disable proof-pointer-address proof-cons-value
                                proof-rational-value proof-complex-value proof-symbol-value
                                p6-even-as-mod proof-word-tag)
            :do-not '(generalize eliminate-destructors fertilize)
            :expand ((:free (access memory) (proof-view-step access input count depth base objects packages memory))))
           ("Subgoal *1/3"
            :use ((:instance p6-record-reads-after-disjoint-pair-store (start (proof-pointer-address input base)))))
           ("Subgoal *1/2"
            :use ((:instance p6-first-word-of-span-avoids-pair (start input))
                  (:instance p6-remaining-words-of-span-avoid-pair (start input)))))))

(defthm p6-published-view-after-disjoint-pair-store
  (let ((machine (proof-world-machine world))
        (after (proof-world-machine (p6-store-register-pair first second address world))))
    (implies (and (proof-span-p address 16)
                  (p6-object-spans-avoid-pair-p objects address machine))
             (equal (proof-view word base objects packages after)
                    (proof-view word base objects packages machine))))
  :hints (("Goal"
           :in-theory (enable proof-view)
           :use ((:instance p6-view-step-after-disjoint-pair-store
                            (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base) objects))))))))))

(defthm p6-stack-store-preserves-published-views
  (implies (and (proof-heap-p world objects packages) (p6-stack-store-p address world))
           (equal (proof-view word (proof-heap-base world) objects packages
                              (proof-world-machine (p6-store-register-pair first second address world)))
                  (proof-view word (proof-heap-base world) objects packages (proof-world-machine world))))
  :rule-classes nil
  :hints (("Goal" :use p6-stack-store-avoids-published-objects)))

(defthm p6-stack-views-after-disjoint-pair-store
  (let ((machine (proof-world-machine world))
        (after (proof-world-machine (p6-store-register-pair first second address world))))
    (implies (and (proof-span-p address 16)
                  (p6-object-spans-avoid-pair-p objects address machine)
                  (p6-span-avoids-pair-p start (* 8 (nfix count)) address))
             (equal (proof-stack-views count start base objects packages after)
                    (proof-stack-views count start base objects packages machine))))
  :rule-classes nil
  :hints (("Goal"
           :induct (p6-word-span-induction count start)
           :expand ((:free (memory) (proof-stack-views count start base objects packages memory))))
          ("Subgoal *1/2"
           :use (p6-first-word-of-span-avoids-pair p6-remaining-words-of-span-avoid-pair))))

(defthm p6-object-descriptors-after-disjoint-pair-store
  (let* ((start (proof-object-address object))
         (machine (proof-world-machine world))
         (after (proof-world-machine (p6-store-register-pair first second address world))))
    (implies (and (proof-span-p address 16)
                  (p6-span-avoids-pair-p start (p6-object-content-size start object machine) address))
             (and (equal (proof-object-size object after) (proof-object-size object machine))
                  (equal (proof-symbol-object-p object after) (proof-symbol-object-p object machine)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-object-content-size proof-object-size proof-symbol-object-p)
           :use ((:instance p6-parts-of-header-span-avoid-pair
                            (start (proof-object-address object))
                            (size (proof-header-size (proof-load-word (proof-object-address object)
                                                                      (proof-world-machine world)))))))))
