(in-package "BOYMOO-PROOFS")

(include-book "boxed-numeric")
(include-book "store-frame")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-heap-p proof-heap-layout-p proof-memory-span-agrees-p
                           proof-view proof-stack-prefix proof-static-size proof-dynamic-root)))

(local
 (defthm p6-boxed-scratch-load-word-natural
   (natp (proof-load-word address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load)))))

(local
 (defthm p6-boxed-scratch-static-size-natural
   (natp (proof-static-size base machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-static-size)))))

(local
 (defthm p6-layout-static-size-bound
   (implies (proof-heap-layout-p world)
            (<= 80 (proof-static-size (proof-heap-base world) (proof-world-machine world))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-heap-layout-p)
                                   (proof-align-up proof-covered-p proof-regions-p
                                    proof-page-size-p proof-disjoint-p))))))

(local
 (defthm p6-heap-gives-layout-and-prefix
   (implies (proof-heap-p world objects packages)
            (and (proof-heap-layout-p world)
                 (proof-stack-prefix (proof-stack-top world) world objects packages)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable proof-heap-p)))))

(defthm p6-machine-save-is-stack-store
  (let ((scratch (- (p6-sp world) 16)))
    (implies (and (proof-heap-layout-p world) (p6-machine-save-room-p world))
             (and (p6-stack-store-p scratch world)
                  (posp scratch)
                  (proof-disjoint-p (proof-stack-base world) (proof-stack-top world)
                                    scratch (p6-sp world))
                  (natp (+ (p6-machine-reservation-start world) *proof-machine-reservation*))
                  (<= (+ (p6-machine-reservation-start world) *proof-machine-reservation*)
                      (expt 2 64))
                  (<= (p6-sp world)
                      (+ (p6-machine-reservation-start world) *proof-machine-reservation*)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-stack-store-p proof-subspan-p proof-span-p proof-disjoint-p
                            p6-machine-save-room-p p6-machine-reservation-start)
                           (proof-align-up proof-covered-p proof-regions-p proof-page-size-p))
           :expand ((proof-heap-layout-p world))
           :use (p6-machine-save-room-is-mapped
                 (:instance p6-covered-span-is-valid
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (size *proof-machine-reservation*) (access :write)
                            (regions (proof-world-regions world)))))))

(defthm p6-numeric-save-preserves-heap
  (implies (and (proof-heap-p world objects packages) (p6-machine-save-room-p world))
           (proof-preserved-heap-p nil world (p6-numeric-save-world world) objects objects packages))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-numeric-save-world proof-preserved-heap-p proof-heap-frame-p
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p
                            proof-dynamic-view)
                           (proof-dynamic-entries p6-machine-reservation-start))
           :use (p6-heap-gives-layout-and-prefix
                 p6-machine-save-is-stack-store
                 p6-static-fits-heap-range
                 p6-layout-static-size-bound
                 (:instance p6-stack-store-preserves-heap
                            (first 29) (second 30) (address (- (p6-sp world) 16)))
                 (:instance p6-stack-store-preserves-prefix
                            (first 29) (second 30) (address (- (p6-sp world) 16))
                            (top (proof-stack-top world)))
                 (:instance p6-stack-store-keeps-heap-words
                            (first 29) (second 30) (address (- (p6-sp world) 16)))
                 (:instance p6-stack-store-keeps-heap-span
                            (first 29) (second 30) (address (- (p6-sp world) 16))
                            (start (proof-heap-base world)) (end (+ 24 (proof-heap-base world))))
                 (:instance p6-stack-store-keeps-heap-span
                            (first 29) (second 30) (address (- (p6-sp world) 16))
                            (start (+ 32 (proof-heap-base world)))
                            (end (+ (proof-heap-base world)
                                    (proof-static-size (proof-heap-base world)
                                                       (proof-world-machine world)))))
                 (:instance p6-pair-store-preserves-disjoint-memory-span
                            (first 29) (second 30) (scratch (- (p6-sp world) 16))
                            (start (p6-sp world))
                            (end (+ (p6-machine-reservation-start world) *proof-machine-reservation*)))
                 (:instance p6-stack-store-preserves-published-views
                            (first 29) (second 30) (address (- (p6-sp world) 16))
                            (word (proof-dynamic-root (proof-heap-base world)
                                                      (proof-world-machine world))))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (p6-numeric-save-world proof-preserved-heap-p proof-heap-frame-p
                                  proof-prefix-preserved-p proof-dynamic-table-preserved-p
                                  proof-dynamic-view p6-machine-reservation-start)
                                 (proof-dynamic-entries))))))

(defthm p6-numeric-save-preserves-argument-view
  (implies (and (proof-heap-p world objects packages) (p6-machine-save-room-p world)
                (proof-reg-value-p 0 value world objects packages))
           (proof-reg-value-p 0 value (p6-numeric-save-world world) objects packages))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-numeric-save-world proof-reg-value-p proof-machine-value-p
                              proof-value-p)
           :use (p6-heap-gives-layout-and-prefix
                 p6-machine-save-is-stack-store
                 (:instance p6-stack-store-preserves-published-views
                            (first 29) (second 30) (address (- (p6-sp world) 16))
                            (word (proof-world-reg 0 world)))))))

(defthm p6-boxed-numeric-projections-runtime-contract-with-room
  (let* ((sites (p6-boxed-numeric-sites name world))
         (after (p6-path-end sites world))
         (args (list value)))
    (implies (and (p6-boxed-numeric-pre-p name runtime-base world)
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-machine-save-room-p world))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-segment-p proof-runtime-return-p proof-runtime-pre-p
                               proof-preserved-heap-p proof-reg-value-p)
           :use (p6-boxed-numeric-projections-with-machine-save-room
                 (:instance p6-runtime-pre-has-heap-and-first-arg (args (list value)))
                 p6-numeric-save-preserves-heap
                 p6-numeric-save-preserves-argument-view))))
