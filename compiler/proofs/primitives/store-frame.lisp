(in-package "BOYMOO-PROOFS")

(include-book "scratch-frame")
(include-book "store-views")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-heap-p proof-heap-layout-p proof-object-map-p
                           proof-object-size proof-symbol-object-p proof-object-view
                           proof-static-size proof-view proof-value-p proof-load-word
                           proof-external-objects proof-fixed-external-p
                           proof-string-accounting-p proof-dynamic-view proof-static-p
                           proof-heap-object-spans-p proof-static-spans-p
                           proof-home-bindings-p proof-dynamic-symbol-objects-p
                           proof-stack-prefix proof-runtime-word proof-object-address
                           proof-load-string proof-integer-view proof-header-size)))

(local
 (defthm p6-store-frame-load-word-natural
   (natp (proof-load-word address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load)))))

(local
 (defthm p6-store-frame-static-size-natural
   (natp (proof-static-size base machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-static-size)))))

(defthm p6-pair-store-preserves-register
  (equal (proof-world-reg register (p6-store-register-pair first second address world))
         (proof-world-reg register world))
  :hints (("Goal" :in-theory (enable p6-store-register-pair))))

(defthm p6-pair-store-preserves-sp-and-environment
  (let ((saved (p6-store-register-pair first second address world)))
    (and (equal (p6-sp saved) (p6-sp world))
         (equal (cdr saved) (cdr world))
         (equal (proof-world-stop saved) (proof-world-stop world))
         (equal (proof-world-page-size saved) (proof-world-page-size world))
         (equal (proof-world-regions saved) (proof-world-regions world))
         (equal (proof-world-replies saved) (proof-world-replies world))
         (proof-streams-preserved-p world saved)))
  :hints (("Goal"
           :in-theory (enable p6-store-register-pair p6-store-word proof-world-stop
                              proof-world-machine boymoo-model::a64-sp
                              proof-world-page-size proof-world-regions proof-world-replies
                              proof-world-input proof-world-stdout proof-world-stderr))))

(local
 (defthm p6-heap-mapping-bounds
   (let ((start (- (proof-heap-base world) *proof-heap-prefix*))
         (end (proof-spaces-end world)))
     (implies (proof-heap-layout-p world)
              (and (natp start) (natp end) (<= end (expt 2 64)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-heap-layout-p proof-span-p)
                            (proof-align-up proof-page-size-p proof-regions-p proof-disjoint-p))
            :use ((:instance p6-covered-span-is-valid
                             (address (- (proof-heap-base world) *proof-heap-prefix*))
                             (size (- (proof-spaces-end world) (- (proof-heap-base world) *proof-heap-prefix*)))
                             (access :write) (regions (proof-world-regions world))))))))

(local
 (defthm p6-heap-subspan-avoids-stack-store
   (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                 (natp start) (natp end) (<= (- (proof-heap-base world) *proof-heap-prefix*) start)
                 (<= end (proof-spaces-end world)) (<= start end))
            (and (p6-span-avoids-pair-p start (- end start) address)
                 (proof-disjoint-p start end address (+ address 16))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable p6-stack-store-p p6-span-avoids-pair-p
                               p6-reservations-disjoint-p proof-subspan-p proof-disjoint-p proof-span-p)
            :use (p6-heap-mapping-bounds p6-heap-area-is-outside-stack-reservations)))))

(local
 (defthm p6-heap-word-after-stack-store
   (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                 (integerp start) (<= (- (proof-heap-base world) *proof-heap-prefix*) start)
                 (<= (+ 8 start) (proof-spaces-end world)))
            (equal (proof-load-word start (proof-world-machine (p6-store-register-pair first second address world)))
                   (proof-load-word start (proof-world-machine world))))
   :hints (("Goal"
            :use (p6-heap-mapping-bounds
                  (:instance p6-heap-subspan-avoids-stack-store (end (+ 8 start))))))))

(local
 (defthm p6-heap-span-after-stack-store
   (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                 (posp address) (integerp start) (integerp end)
                 (<= (- (proof-heap-base world) *proof-heap-prefix*) start)
                 (<= start end) (<= end (proof-spaces-end world)))
            (proof-memory-span-agrees-p start end world (p6-store-register-pair first second address world)))
   :rule-classes nil
   :hints (("Goal"
            :use (p6-heap-mapping-bounds p6-heap-subspan-avoids-stack-store
                  (:instance p6-pair-store-preserves-disjoint-memory-span (scratch address)))))))

(local
 (defthm p6-word-address-after-stack-store
   (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                 (integerp offset) (<= -128 offset)
                 (<= (+ 8 offset)
                     (+ 32 (proof-static-size (proof-heap-base world) (proof-world-machine world)))))
            (equal (proof-load-word (+ offset (proof-heap-base world))
                                   (proof-world-machine (p6-store-register-pair first second address world)))
                   (proof-load-word (+ offset (proof-heap-base world)) (proof-world-machine world))))
   :hints (("Goal"
            :use (p6-static-fits-heap-range
                  (:instance p6-heap-word-after-stack-store (start (+ offset (proof-heap-base world)))))
            :in-theory (disable p6-heap-word-after-stack-store)))))

(local
 (defthm p6-runtime-word-after-stack-store
   (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                 (integerp offset) (<= 0 offset) (<= offset 80))
            (equal (proof-runtime-word offset (p6-store-register-pair first second address world))
                   (proof-runtime-word offset world)))
   :hints (("Goal"
            :in-theory (e/d (proof-runtime-word)
                            (p6-heap-word-after-stack-store))
            :use (p6-static-fits-heap-range
                  (:instance p6-heap-word-after-stack-store
                             (start (+ (proof-heap-base world) (- offset 128)))))))))

(local
 (defthm p6-static-prefix-words-after-stack-store
   (let* ((base (proof-heap-base world)) (machine (proof-world-machine world))
          (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world))
              (and (equal (proof-static-size base after) (proof-static-size base machine))
                   (equal (proof-load-word (+ 8 base) after) (proof-load-word (+ 8 base) machine))
                   (equal (proof-load-word (+ 16 base) after) (proof-load-word (+ 16 base) machine))
                   (equal (proof-dynamic-root base after) (proof-dynamic-root base machine)))))
   :hints (("Goal"
            :in-theory (enable proof-static-size proof-dynamic-root)
            :use ((:instance p6-word-address-after-stack-store (offset 0))
                  (:instance p6-word-address-after-stack-store (offset 8))
                  (:instance p6-word-address-after-stack-store (offset 16))
                  (:instance p6-word-address-after-stack-store (offset 24))
                  p6-static-fits-heap-range)
            :expand ((proof-heap-layout-p world))))))

(local
 (defthm p6-covered-span-of-equal-size
   (implies (and (proof-covered-p address size access regions)
                 (equal size other))
            (proof-covered-p address other access regions))
   :rule-classes nil))

(defthm p6-pair-store-preserves-layout
  (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world))
           (proof-heap-layout-p (p6-store-register-pair first second address world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-page-size-p proof-regions-p proof-align-up proof-disjoint-p)
           :expand ((:free (state) (proof-heap-layout-p state)))
           :use (p6-static-prefix-words-after-stack-store))
          (and stable-under-simplificationp
               (let ((start (list 'binary-+ (- *proof-heap-prefix*) '(proof-world-reg '28 world)))
                     (size (list 'binary-+ *proof-heap-prefix*
                                 '(binary-+ (unary-- (proof-world-reg '28 world))
                                            (proof-runtime-word '32 world)))))
                 (list :use
                       (list (list :instance 'p6-covered-span-of-equal-size
                                   (list 'address start) (list 'size size)
                                   (list 'other (list 'binary-+ (+ *proof-heap-prefix* *proof-space-size*)
                                                      '(binary-+ (proof-runtime-word '8 world)
                                                                 (unary-- (proof-world-reg '28 world)))))
                                   '(access :write) '(regions (proof-world-regions world)))
                             (list :instance 'p6-covered-span-of-equal-size
                                   (list 'address start) (list 'size size)
                                   (list 'other (list 'binary-+ (+ *proof-heap-prefix* *proof-space-size*)
                                                      '(binary-+ (proof-runtime-word '0 world)
                                                                 (unary-- (proof-world-reg '28 world)))))
                                   '(access :write) '(regions (proof-world-regions world)))))))))

(local
 (defthm p6-object-disjointness-after-pair-store
   (let ((machine (proof-world-machine world))
         (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-span-p address 16)
                   (p6-object-spans-avoid-pair-p pending address machine))
              (equal (proof-object-disjoint-p start end pending after)
                     (proof-object-disjoint-p start end pending machine))))
   :hints (("Goal"
            :induct (len pending)
            :in-theory (disable proof-disjoint-p)
            :expand ((:free (memory) (proof-object-disjoint-p start end pending memory))))
           ("Subgoal *1/1"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending))))))))

(local
 (defun p6-object-map-store-induction (pending objects symbols base packages world)
   (if (atom pending)
       symbols
     (let* ((machine (proof-world-machine world))
            (symbol (proof-symbol-object-p (car pending) machine))
            (seen (if symbol
                      (cons (proof-view-value (proof-object-view (car pending) base objects packages machine)) symbols)
                    symbols)))
       (p6-object-map-store-induction (cdr pending) objects seen base packages world)))))

(local
 (defthm p6-object-map-after-pair-store
   (let ((machine (proof-world-machine world))
         (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-span-p address 16)
                   (p6-object-spans-avoid-pair-p pending address machine)
                   (p6-object-spans-avoid-pair-p objects address machine))
              (equal (proof-object-map-p pending objects symbols base packages after)
                     (proof-object-map-p pending objects symbols base packages machine))))
   :hints (("Goal"
            :induct (p6-object-map-store-induction pending objects symbols base packages world)
            :in-theory (enable proof-object-view)
            :expand ((:free (seen memory) (proof-object-map-p pending objects seen base packages memory))))
           ("Subgoal *1/2"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending)))))
           ("Subgoal *1/3"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending))))))))

(local
 (defthm p6-static-spans-after-pair-store
   (let ((machine (proof-world-machine world))
         (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-span-p address 16)
                   (p6-object-spans-avoid-pair-p pending address machine))
              (equal (proof-static-spans-p pending base size after)
                     (proof-static-spans-p pending base size machine))))
   :hints (("Goal"
            :induct (len pending)
            :expand ((:free (memory) (proof-static-spans-p pending base size memory))))
           ("Subgoal *1/1"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending))))))))

(local
 (defthm p6-static-record-package-word-after-pair-store
   (let* ((base (proof-heap-base world))
          (machine (proof-world-machine world)) (size (proof-static-size base machine))
          (after (proof-world-machine (p6-store-register-pair first second address world)))
          (start (proof-object-address object)))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                   (proof-static-spans-p (cons object rest) base size machine))
              (equal (proof-load-word (+ 16 start) after) (proof-load-word (+ 16 start) machine))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable proof-subspan-p proof-span-p)
            :expand ((:free (base size) (proof-static-spans-p (cons object rest) base size (proof-world-machine world))))
            :use ((:instance p6-word-address-after-stack-store
                             (offset (+ 16 (- (proof-object-address object) (proof-heap-base world))))))))))

(local
 (defthm p6-home-bindings-after-pair-store
   (let* ((base (proof-heap-base world)) (machine (proof-world-machine world))
          (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                   (proof-static-spans-p pending base (proof-static-size base machine) machine)
                   (p6-object-spans-avoid-pair-p pending address machine)
                   (p6-object-spans-avoid-pair-p objects address machine))
              (equal (proof-home-bindings-p pending base objects packages after buckets)
                     (proof-home-bindings-p pending base objects packages machine buckets))))
   :hints (("Goal"
            :induct (len pending) :in-theory (enable proof-object-view)
            :expand ((:free (base memory) (proof-home-bindings-p pending base objects packages memory buckets))
                     (:free (base size) (proof-static-spans-p pending base size (proof-world-machine world)))))
           ("Subgoal *1/1"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending)))
                  (:instance p6-static-record-package-word-after-pair-store
                             (object (car pending)) (rest (cdr pending))))))))

(local
 (defthm p6-static-heap-after-pair-store
   (let* ((base (proof-heap-base world)) (machine (proof-world-machine world))
          (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                   (p6-object-spans-avoid-pair-p objects address machine)
                   (proof-static-p base objects packages machine))
              (proof-static-p base objects packages after)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-value-p)
                            (proof-static-objects proof-packages-p proof-package-row-views
                             proof-static-buckets-p proof-package-bindings-p))
            :expand ((:free (base memory) (proof-static-p base objects packages memory)))
            :use (p6-static-prefix-words-after-stack-store
                  (:instance p6-home-bindings-after-pair-store
                             (pending (proof-static-objects objects))
                             (objects (proof-static-objects objects))
                             (buckets (cdr (proof-view (proof-load-word (+ 16 (proof-heap-base world))
                                                                        (proof-world-machine world))
                                                       (proof-heap-base world)
                                                       (proof-static-objects objects) packages
                                                       (proof-world-machine world))))))))))

(local
 (defthm p6-object-spans-after-pair-store
   (let* ((machine (proof-world-machine world))
          (after (p6-store-register-pair first second address world)))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                   (p6-object-spans-avoid-pair-p pending address machine))
              (equal (proof-heap-object-spans-p pending external after)
                     (proof-heap-object-spans-p pending external world))))
   :hints (("Goal"
            :induct (len pending)
            :expand ((:free (state) (proof-heap-object-spans-p pending external state))))
           ("Subgoal *1/1"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending))))))))

(local
 (defthm p6-dynamic-object-views-after-pair-store
   (let ((machine (proof-world-machine world))
         (after (proof-world-machine (p6-store-register-pair first second address world))))
     (implies (and (proof-span-p address 16)
                   (p6-object-spans-avoid-pair-p pending address machine)
                   (p6-object-spans-avoid-pair-p objects address machine))
              (equal (proof-dynamic-symbol-objects-p pending objects entries base packages after)
                     (proof-dynamic-symbol-objects-p pending objects entries base packages machine))))
   :hints (("Goal"
            :induct (len pending) :in-theory (enable proof-object-view)
            :expand ((:free (memory) (proof-dynamic-symbol-objects-p pending objects entries
                                                                  base packages memory))))
           ("Subgoal *1/1"
            :use ((:instance p6-object-descriptors-after-disjoint-pair-store (object (car pending))))))))

(local
 (defthm p6-external-metadata-avoids-stack-store
   (implies (and (proof-regions-p (proof-world-regions world))
                 (member-equal (proof-region head end :rw) (proof-world-regions world))
                 (p6-reservations-disjoint-p head end world)
                 (p6-stack-store-p address world)
                 (natp offset) (<= (+ head offset 8) end))
            (p6-span-avoids-pair-p (+ head offset) 8 address))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable p6-span-avoids-pair-p p6-stack-store-p
                               proof-subspan-p proof-span-p proof-disjoint-p
                               p6-reservations-disjoint-p proof-region-p)
            :use ((:instance p6-listed-region-is-valid
                             (region (proof-region head end :rw))
                             (regions (proof-world-regions world))))))))

(local
 (defthm p6-rounded-external-size-covers-metadata
   (implies (natp size)
            (<= 32 (proof-align-up (+ 32 size) *proof-runtime-page*)))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (enable proof-align-up ceiling)
            :use ((:instance p6-floor-bounds (x (- (+ 32 size))) (d *proof-runtime-page*)))))))

(local
 (defthm p6-store-frame-header-size-natural
   (natp (proof-header-size (proof-load-word start machine)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load)
                   :use ((:instance p6-loaded-header-fields (address start)))))))

(local
 (defthm p6-layout-has-valid-regions
   (implies (proof-heap-layout-p world)
            (proof-regions-p (proof-world-regions world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-heap-layout-p)
                                   (proof-regions-p proof-align-up proof-disjoint-p
                                    proof-page-size-p proof-covered-p))))))

(local
 (defthm p6-external-head-facts
   (let* ((machine (proof-world-machine world))
          (end (+ head (proof-load-word (+ head 8) machine))))
     (implies (and (proof-heap-layout-p world)
                   (proof-external-objects head fuel world objects)
                   (not (equal head 0)))
              (and (natp head) (natp end) (<= end (expt 2 64)) (<= (+ head 32) end)
                   (proof-regions-p (proof-world-regions world))
                   (member-equal (proof-region head end :rw) (proof-world-regions world))
                   (p6-reservations-disjoint-p head end world))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-reservations-disjoint-p p6-machine-reservation-start)
                            (proof-align-up proof-disjoint-p p6-loaded-header-fields))
            :expand ((proof-external-objects head fuel world objects))
            :use (p6-layout-has-valid-regions
                  (:instance p6-listed-region-is-valid
                             (region (proof-region head (+ head (proof-load-word (+ head 8)
                                                        (proof-world-machine world))) :rw))
                             (regions (proof-world-regions world)))
                  (:instance p6-rounded-external-size-covers-metadata
                             (size (proof-header-size (proof-load-word (+ head 24)
                                                                       (proof-world-machine world))))))))))

(local
 (defthm p6-external-header-and-prefix-after-pair-store
   (let* ((machine (proof-world-machine world))
          (saved (proof-world-machine (p6-store-register-pair first second address world)))
          (end (+ head (proof-load-word (+ head 8) machine))))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                   (proof-external-objects head fuel world objects)
                   (not (equal head 0)))
              (and (equal (proof-load-word head saved) (proof-load-word head machine))
                   (equal (proof-load-word (+ 8 head) saved) (proof-load-word (+ 8 head) machine))
                   (equal (proof-load-word (+ 16 head) saved) (proof-load-word (+ 16 head) machine))
                   (equal (proof-load-word (+ 24 head) saved) (proof-load-word (+ 24 head) machine))
                   (implies (posp address)
                            (proof-memory-span-agrees-p
                             head end world (p6-store-register-pair first second address world))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-reservations-disjoint-p p6-machine-reservation-start
                             p6-stack-store-p proof-subspan-p proof-span-p proof-disjoint-p
                             p6-span-avoids-pair-p)
                            (proof-align-up proof-region-p proof-memory-span-agrees-p
                             proof-external-objects proof-regions-p))
            :use (p6-external-head-facts
                  p6-pair-store-has-valid-span
                  (:instance p6-proof-load-word-after-disjoint-pair-store (start head))
                  (:instance p6-proof-load-word-after-disjoint-pair-store (start (+ 8 head)))
                  (:instance p6-proof-load-word-after-disjoint-pair-store (start (+ 16 head)))
                  (:instance p6-proof-load-word-after-disjoint-pair-store (start (+ 24 head)))
                  (:instance p6-pair-store-preserves-disjoint-memory-span
                             (start head) (end (+ head (proof-load-word (+ head 8) (proof-world-machine world))))
                             (scratch address)))))))

(local
 (defthm p6-external-objects-at-zero
   (equal (proof-external-objects 0 fuel world objects) (list :mappings))
   :hints (("Goal" :expand ((proof-external-objects 0 fuel world objects))))))

(local
 (defthm p6-external-chain-after-pair-store
   (let* ((saved (p6-store-register-pair first second address world))
          (external (proof-external-objects head fuel world objects)))
     (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world) external)
              (and (equal (proof-external-objects head fuel saved objects) external)
                   (equal (proof-external-bytes (cdr external) (proof-world-machine saved))
                          (proof-external-bytes (cdr external) (proof-world-machine world)))
                   (implies (posp address) (proof-fixed-external-p (cdr external) world saved)))))
   :hints (("Goal"
            :induct (proof-external-objects head fuel world objects)
            :in-theory (e/d ((:induction proof-external-objects) proof-fixed-external-p)
                            (proof-disjoint-p proof-regions-p proof-align-up p6-loaded-header-fields
                             proof-memory-span-agrees-p proof-external-bytes))
            :expand ((:free (state) (proof-external-objects head fuel state objects)))
            :do-not '(generalize eliminate-destructors))
           (and stable-under-simplificationp
                '(:use (p6-external-header-and-prefix-after-pair-store p6-external-head-facts)
                  :in-theory (e/d ((:induction proof-external-objects) proof-fixed-external-p
                                   proof-external-bytes)
                                  (proof-disjoint-p proof-regions-p proof-align-up
                                   p6-loaded-header-fields proof-memory-span-agrees-p)))))))

(local
 (defthm p6-value-reservation-bounds
   (implies (proof-heap-layout-p world)
            (and (natp (proof-stack-base world))
                 (natp (proof-stack-end world))
                 (<= (proof-stack-end world) (expt 2 64))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-span-p)
                            (proof-align-up proof-region-p proof-regions-p proof-disjoint-p))
            :expand ((proof-heap-layout-p world))
            :use ((:instance p6-covered-span-is-valid
                             (address (proof-stack-base world)) (size *proof-value-reservation*)
                             (access :write) (regions (proof-world-regions world))))))))

(local
 (defthm p6-prefix-span-avoids-stack-store
   (let ((base (proof-stack-base world)))
     (implies (and (proof-heap-layout-p world) (natp top)
                   (<= base top) (<= top (proof-stack-top world))
                   (proof-disjoint-p base top address (+ address 16)))
              (p6-span-avoids-pair-p base (* 8 (nfix (ash (- top base) -3))) address)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-span-avoids-pair-p proof-span-p proof-disjoint-p)
                            (proof-align-up proof-regions-p p6-ash-right))
            :expand ((proof-heap-layout-p world))
            :use (p6-value-reservation-bounds
                  (:instance p6-ash-right (x (- top (proof-stack-base world))))
                  (:instance p6-floor-bounds (x (- top (proof-stack-base world))) (d 8)))))))

(defthm p6-stack-store-preserves-prefix
  (let ((saved (p6-store-register-pair first second address world))
        (base (proof-stack-base world)))
    (implies (and (proof-heap-p world objects packages) (p6-stack-store-p address world)
                  (proof-disjoint-p base top address (+ address 16)))
             (equal (proof-stack-prefix top saved objects packages)
                    (proof-stack-prefix top world objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-heap-p proof-stack-prefix)
                           (proof-static-p proof-object-map-p proof-external-objects
                            proof-heap-object-spans-p proof-dynamic-view proof-dynamic-entries
                            proof-dynamic-symbol-objects-p proof-string-accounting-p))
           :use (p6-prefix-span-avoids-stack-store p6-stack-store-avoids-published-objects
                 (:instance p6-stack-views-after-disjoint-pair-store
                            (count (ash (- top (proof-stack-base world)) -3))
                            (start (proof-stack-base world)) (base (proof-heap-base world)))))))

(defthm p6-stack-store-preserves-heap
  (let ((saved (p6-store-register-pair first second address world))
        (base (proof-stack-base world)) (top (proof-stack-top world)))
    (implies (and (proof-heap-p world objects packages) (p6-stack-store-p address world)
                  (proof-disjoint-p base top address (+ address 16)))
             (proof-heap-p saved objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-string-accounting-p proof-dynamic-view)
                           (proof-dynamic-entries proof-fixed-external-p
                            proof-external-bytes proof-prefix-preserved-p))
           :expand ((:free (state) (proof-heap-p state objects packages)))
           :use (p6-stack-store-avoids-published-objects p6-pair-store-preserves-layout
                 p6-static-prefix-words-after-stack-store p6-static-heap-after-pair-store
                 (:instance p6-stack-store-preserves-prefix (top (proof-stack-top world)))
                 (:instance p6-external-chain-after-pair-store (head (proof-external-head world))
                            (fuel (len objects)))))))

(defthm p6-stack-store-preserves-fixed-heap
  (let ((saved (p6-store-register-pair first second address world)))
    (implies (and (proof-heap-p world objects packages) (p6-stack-store-p address world)
                  (posp address))
             (proof-fixed-heap-p world saved objects)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-fixed-heap-p proof-heap-p)
                           (proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                            proof-string-accounting-p proof-fixed-external-p proof-external-bytes
                            proof-memory-span-agrees-p))
           :use (p6-heap-mapping-bounds p6-static-fits-heap-range
                 (:instance p6-heap-span-after-stack-store
                            (start (- (proof-heap-base world) *proof-heap-prefix*))
                            (end (proof-spaces-end world)))
                 (:instance p6-external-chain-after-pair-store
                            (head (proof-external-head world)) (fuel (len objects)))))))

(defthm p6-stack-store-keeps-heap-words
  (let ((after (p6-store-register-pair first second address world)))
    (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world))
             (and (equal (proof-stack-base after) (proof-stack-base world))
                  (equal (proof-stack-end after) (proof-stack-end world))
                  (equal (proof-spaces-end after) (proof-spaces-end world))
                  (equal (proof-dynamic-root (proof-heap-base world) (proof-world-machine after))
                         (proof-dynamic-root (proof-heap-base world) (proof-world-machine world))))))
  :rule-classes nil
  :hints (("Goal" :use p6-static-prefix-words-after-stack-store)))

(defthm p6-stack-store-keeps-heap-span
  (implies (and (proof-heap-layout-p world) (p6-stack-store-p address world)
                (posp address) (integerp start) (integerp end)
                (<= (- (proof-heap-base world) *proof-heap-prefix*) start)
                (<= start end) (<= end (proof-spaces-end world)))
           (proof-memory-span-agrees-p start end world (p6-store-register-pair first second address world)))
  :rule-classes nil
  :hints (("Goal" :use p6-heap-span-after-stack-store)))
