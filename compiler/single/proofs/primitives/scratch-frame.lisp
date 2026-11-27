(in-package "BOYMOO-PROOFS")

(include-book "machine-stack")
(include-book "mapped-data")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-model::a64-write-bytes proof-load-word proof-region-p
                           proof-heap-layout-p proof-external-objects proof-fixed-external-p
                           proof-memory-span-agrees-p proof-byte-entries-agree-p)))

(defthm p6-pair-store-preserves-outside-byte
  (implies (and (proof-span-p scratch 16) (unsigned-byte-p 64 address)
                (or (< address scratch) (<= (+ scratch 16) address)))
           (let ((saved (p6-store-register-pair first second scratch world)))
             (equal (boymoo-model::a64-byte address (boymoo-model::a64-memory (proof-world-machine saved)))
                    (boymoo-model::a64-byte address (boymoo-model::a64-memory (proof-world-machine world))))))
  :hints (("Goal" :in-theory (enable p6-store-register-pair proof-span-p))))

(local
 (defthm p6-byte-at-noninteger-address
   (implies (not (integerp address))
            (equal (boymoo-model::a64-byte address memory) (boymoo-model::a64-byte 0 memory)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte p6-unsigned-as-mod)))))

(local
 (defthm p6-pair-store-preserves-byte-in-disjoint-span
   (implies (and (natp start) (natp end) (<= start address) (< address end) (<= end (expt 2 64))
                 (natp scratch) (< 0 scratch) (proof-span-p scratch 16)
                 (proof-disjoint-p start end scratch (+ scratch 16)))
            (let ((saved (p6-store-register-pair first second scratch world)))
              (equal (boymoo-model::a64-byte address (boymoo-model::a64-memory (proof-world-machine saved)))
                     (boymoo-model::a64-byte address (boymoo-model::a64-memory (proof-world-machine world))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-disjoint-p) (p6-pair-store-preserves-outside-byte))
            :cases ((integerp address))
            :use (p6-pair-store-preserves-outside-byte
                  (:instance p6-pair-store-preserves-outside-byte (address 0)))))))

(local
 (defthm p6-pair-store-preserves-listed-bytes-in-disjoint-span
   (implies (and (natp start) (natp end) (<= end (expt 2 64))
                 (natp scratch) (< 0 scratch) (proof-span-p scratch 16)
                 (proof-disjoint-p start end scratch (+ scratch 16)))
            (let ((saved (p6-store-register-pair first second scratch world)))
              (proof-byte-entries-agree-p entries start end
                                          (boymoo-model::a64-memory (proof-world-machine world))
                                          (boymoo-model::a64-memory (proof-world-machine saved)))))
   :rule-classes nil
   :hints (("Goal" :induct (len entries)
                   :in-theory (enable proof-byte-entries-agree-p))
           ("Subgoal *1/1"
            :use ((:instance p6-pair-store-preserves-byte-in-disjoint-span (address (caar entries))))))))

(defthm p6-pair-store-preserves-disjoint-memory-span
  (implies (and (natp start) (natp end) (<= end (expt 2 64))
                (natp scratch) (< 0 scratch) (proof-span-p scratch 16)
                (proof-disjoint-p start end scratch (+ scratch 16)))
           (proof-memory-span-agrees-p start end world (p6-store-register-pair first second scratch world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-memory-span-agrees-p)
           :use ((:instance p6-pair-store-preserves-listed-bytes-in-disjoint-span
                            (entries (boymoo-model::a64-memory (proof-world-machine world))))
                 (:instance p6-pair-store-preserves-listed-bytes-in-disjoint-span
                            (entries (boymoo-model::a64-memory
                                      (proof-world-machine (p6-store-register-pair first second scratch world)))))))))

(defund p6-machine-save-room-p (world)
  (let* ((floor (- (proof-machine-limit world) *proof-machine-margin*))
         (scratch (- (p6-sp world) 16)))
    (and (< 0 scratch) (<= floor scratch))))

(defthm p6-machine-save-room-is-mapped
  (let ((scratch (- (p6-sp world) 16)))
    (implies (and (proof-heap-layout-p world) (p6-machine-save-room-p world))
             (and (proof-span-p scratch 16)
                  (equal (mod (p6-sp world) 16) 0)
                  (proof-covered-p scratch 16 :write (proof-world-regions world)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-heap-layout-p p6-machine-save-room-p proof-span-p proof-subspan-p)
                           (proof-align-up proof-regions-p proof-disjoint-p proof-page-size-p p6-sp-is-a-word))
           :use (p6-sp-is-a-word
                 (:instance p6-covered-span-is-valid
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (size *proof-machine-reservation*) (access :write) (regions (proof-world-regions world)))
                 (:instance p6-covered-subspan
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (size *proof-machine-reservation*) (part (- (p6-sp world) 16))
                            (width 16) (access :write) (regions (proof-world-regions world)))))))

(defund p6-machine-reservation-floor (world)
  (- (proof-machine-limit world) *proof-machine-margin*))

(local
 (defthm p6-disjoint-from-reservation-is-disjoint-from-save
   (implies (and (p6-machine-save-room-p world)
                 (<= (p6-sp world) (+ *proof-machine-reservation* (p6-machine-reservation-floor world)))
                 (proof-disjoint-p start end (p6-machine-reservation-floor world)
                                   (+ *proof-machine-reservation* (p6-machine-reservation-floor world))))
            (proof-disjoint-p start end (- (p6-sp world) 16) (p6-sp world)))
   :hints (("Goal" :in-theory (enable p6-machine-save-room-p p6-machine-reservation-floor proof-disjoint-p)))))

(local
 (defthm p6-heap-layout-bounds-machine-save
   (let ((start (- (proof-heap-base world) *proof-heap-prefix*)) (end (proof-spaces-end world))
         (floor (p6-machine-reservation-floor world)))
     (implies (proof-heap-layout-p world)
              (and (natp start) (natp end) (<= end (expt 2 64))
                   (proof-regions-p (proof-world-regions world))
                   (<= (p6-sp world) (+ *proof-machine-reservation* floor))
                   (proof-disjoint-p start end floor (+ *proof-machine-reservation* floor)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-heap-layout-p p6-machine-reservation-floor proof-span-p)
                            (proof-align-up proof-regions-p proof-disjoint-p proof-page-size-p))
            :use ((:instance p6-covered-span-is-valid
                             (address (- (proof-heap-base world) *proof-heap-prefix*))
                             (size (+ *proof-heap-prefix* (- (proof-spaces-end world) (proof-heap-base world))))
                             (access :write) (regions (proof-world-regions world))))))))

(local
 (defthm p6-load-word-natural-for-external-chain
   (natp (proof-load-word address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load)))))

(local
 (defthm p6-mapping-bytes-survive-save
   (let* ((floor (p6-machine-reservation-floor world)) (scratch (- (p6-sp world) 16))
          (saved (p6-store-register-pair first second scratch world)))
     (implies (and (proof-regions-p (proof-world-regions world))
                   (member-equal (proof-region head end :rw) (proof-world-regions world))
                   (proof-disjoint-p head end floor (+ *proof-machine-reservation* floor))
                   (<= (p6-sp world) (+ *proof-machine-reservation* floor))
                   (p6-machine-save-room-p world) (proof-span-p scratch 16))
              (proof-memory-span-agrees-p head end world saved)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable proof-region-p p6-machine-save-room-p)
            :use ((:instance p6-listed-region-is-valid
                             (region (proof-region head end :rw)) (regions (proof-world-regions world)))
                  (:instance p6-disjoint-from-reservation-is-disjoint-from-save (start head))
                  (:instance p6-pair-store-preserves-disjoint-memory-span
                             (start head) (scratch (- (p6-sp world) 16))))))))

(local
 (defthm p6-external-chain-survives-register-save
   (let* ((mappings (proof-external-objects head fuel world objects))
          (floor (p6-machine-reservation-floor world)) (scratch (- (p6-sp world) 16)))
     (implies (and (natp head) mappings (proof-regions-p (proof-world-regions world))
                   (<= (p6-sp world) (+ *proof-machine-reservation* floor))
                   (p6-machine-save-room-p world) (proof-span-p scratch 16))
              (proof-fixed-external-p (cdr mappings) world (p6-store-register-pair first second scratch world))))
   :rule-classes nil
   :hints (("Goal"
            :induct (proof-external-objects head fuel world objects)
            :in-theory (e/d (proof-external-objects proof-fixed-external-p p6-machine-reservation-floor)
                            (proof-disjoint-p proof-regions-p proof-align-up))
            :do-not '(generalize eliminate-destructors))
           ("Subgoal *1/2"
            :use ((:instance p6-mapping-bytes-survive-save
                             (end (+ head (proof-load-word (+ head 8) (proof-world-machine world))))))))))

(defthm p6-machine-save-pair-leaves-heap-fixed
  (let* ((scratch (- (p6-sp world) 16))
         (saved (p6-store-register-pair first second scratch world)))
    (implies (and (proof-heap-p world objects packages) (p6-machine-save-room-p world))
             (proof-fixed-heap-p world saved objects)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-heap-p proof-fixed-heap-p p6-machine-save-room-p
                                         p6-store-register-pair proof-world-replies)
                           (proof-static-p proof-object-map-p proof-heap-object-spans-p proof-string-accounting-p
                            proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p proof-stack-prefix))
           :use (p6-machine-save-room-is-mapped p6-heap-layout-bounds-machine-save
                 (:instance p6-disjoint-from-reservation-is-disjoint-from-save
                            (start (- (proof-heap-base world) *proof-heap-prefix*)) (end (proof-spaces-end world)))
                 (:instance p6-pair-store-preserves-disjoint-memory-span
                            (start (- (proof-heap-base world) *proof-heap-prefix*)) (end (proof-spaces-end world))
                            (scratch (- (p6-sp world) 16)))
                 (:instance p6-external-chain-survives-register-save
                            (head (proof-external-head world)) (fuel (len objects)))))))

(local
 (defthm p6-layout-places-value-stack-away-from-saves
   (let* ((start (proof-stack-base world)) (end (proof-stack-end world))
          (floor (p6-machine-reservation-floor world)))
     (implies (proof-heap-layout-p world)
              (and (natp start) (natp end) (<= end (expt 2 64))
                   (<= (p6-sp world) (+ floor *proof-machine-reservation*))
                   (proof-disjoint-p start end floor (+ floor *proof-machine-reservation*)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-heap-layout-p p6-machine-reservation-floor proof-span-p)
                            (proof-align-up proof-regions-p proof-disjoint-p proof-page-size-p))
            :use ((:instance p6-covered-span-is-valid
                             (address (proof-stack-base world)) (size *proof-value-reservation*) (access :write)
                             (regions (proof-world-regions world))))))))

(defthm p6-machine-save-keeps-value-stack-storage
  (let* ((scratch (- (p6-sp world) 16))
         (saved (p6-store-register-pair first second scratch world)))
    (implies (and (proof-heap-layout-p world) (p6-machine-save-room-p world))
             (proof-memory-span-agrees-p (proof-stack-base world) (proof-stack-end world) world saved)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-machine-save-room-p) (p6-disjoint-from-reservation-is-disjoint-from-save))
           :use (p6-layout-places-value-stack-away-from-saves p6-machine-save-room-is-mapped
                 (:instance p6-disjoint-from-reservation-is-disjoint-from-save
                            (start (proof-stack-base world)) (end (proof-stack-end world)))
                 (:instance p6-pair-store-preserves-disjoint-memory-span
                            (start (proof-stack-base world)) (end (proof-stack-end world))
                            (scratch (- (p6-sp world) 16)))))))
