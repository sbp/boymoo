(in-package "BOYMOO-PROOFS")

(include-book "agreements")
(include-book "placement")
(include-book "runtime-layout")

(logic)
(set-verify-guards-eagerness 0)

(defconst *collection-allocation-clobbers*
  (append *proof-volatile-registers* '(26 27)))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     boymoo-model::a64-sp proof-heap-base proof-stack-top proof-machine-limit
                     proof-memory-span-agrees-p proof-static-size proof-dynamic-view
                     proof-stack-prefix proof-stack-base proof-stack-end proof-spaces-end
                     proof-active-floor proof-inactive-floor proof-external-objects
                     proof-object-map-p proof-runtime-word proof-heap-layout-p proof-static-p
                     proof-load-word proof-value-p proof-view proof-static-objects
                     proof-static-spans-p proof-packages-p proof-package-row-views
                     proof-home-bindings-p proof-static-buckets-p proof-package-bindings-p
                     proof-dynamic-entries proof-dynamic-symbol-objects-p
                     proof-string-accounting-p proof-heap-object-spans-p mod
                     boymoo-model::a64-unsigned)))

(defthm collection-register-frame-through-intermediate
  (implies (and (proof-register-frame-p bound clobbers before middle)
                (proof-register-frame-p bound clobbers middle after))
           (proof-register-frame-p bound clobbers before after))
  :hints (("Goal" :induct (proof-register-frame-p bound clobbers before middle))))

(defthm collection-register-frame-preserves-unclobbered-register
  (implies (and (natp register) (natp bound) (<= register bound)
                (not (member-equal register clobbers))
                (proof-register-frame-p bound clobbers before after))
           (equal (proof-world-reg register before) (proof-world-reg register after)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-register-frame-p bound clobbers before after)
                  :do-not '(generalize))))

(local
 (defthm collection-static-span-bounds
   (let* ((base (proof-heap-base world))
          (machine (proof-world-machine world))
          (size (proof-static-size base machine)))
     (implies (proof-static-p base objects packages machine)
              (and (natp base)
                   (<= (+ base 24) (expt 2 64))
                   (<= (+ base size) (expt 2 64)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable proof-static-p)))))

(local
 (defthm collection-static-size-kept-by-heap-frame
   (let ((base (proof-heap-base before)))
     (implies (and (proof-heap-frame-p before after)
                   (natp base) (<= (+ base 24) (expt 2 64)))
              (equal (proof-static-size base (proof-world-machine before))
                     (proof-static-size base (proof-world-machine after)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-span-agreement-preserves-word
                             (start (proof-heap-base before))
                             (end (+ (proof-heap-base before) 24))
                             (address (proof-heap-base before))))
            :in-theory (enable proof-static-size collection-read-word)))))

(defthm collection-heap-frame-through-intermediate
  (implies (and (proof-heap-p before objects packages)
                (collection-memory-keys-p
                 (boymoo-model::a64-memory (proof-world-machine before)))
                (collection-memory-keys-p
                 (boymoo-model::a64-memory (proof-world-machine after)))
                (proof-heap-frame-p before middle) (proof-heap-frame-p middle after)
                (equal (proof-machine-limit before) (proof-machine-limit middle))
                (equal (boymoo-model::a64-sp (proof-world-machine before))
                       (boymoo-model::a64-sp (proof-world-machine middle))))
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-static-span-bounds (world before))
                 (:instance collection-static-size-kept-by-heap-frame (after middle))
                 (:instance collection-memory-span-agrees-transitively
                            (start (proof-heap-base before))
                            (end (+ (proof-heap-base before) 24)))
                 (:instance collection-memory-span-agrees-transitively
                            (start (+ (proof-heap-base before) 32))
                            (end (+ (proof-heap-base before)
                                    (proof-static-size (proof-heap-base before)
                                                       (proof-world-machine before)))))
                 (:instance collection-memory-span-agrees-transitively
                            (start (boymoo-model::a64-sp (proof-world-machine before)))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*))))
           :in-theory (disable proof-dynamic-entries proof-dynamic-symbol-objects-p
                               proof-string-accounting-p proof-heap-object-spans-p))))

(defun collection-allocator-handoff-p (kind bytes origin before middle
                                            old-objects moved-objects packages)
  (and (not (proof-world-stop before))
       (not (proof-world-stop middle))
       (equal (proof-world-pc middle)
              (+ origin (collection-linux-offset
                         (if (eq kind :cons) "rt:alloc-cells" "rt:alloc"))))
       (equal (proof-world-reg 0 middle) bytes)
       (proof-allocation-fits-p kind bytes middle)
       (proof-register-frame-p 30 *collection-allocation-clobbers* before middle)
       (equal (boymoo-model::a64-sp (proof-world-machine before))
              (boymoo-model::a64-sp (proof-world-machine middle)))
       (proof-preserved-heap-p nil before middle old-objects moved-objects packages)
       (equal (proof-active-floor middle) (proof-inactive-floor before))
       (equal (proof-inactive-floor middle) (proof-active-floor before))))

(defthm collection-fast-allocation-finishes-collector-contract
  (implies (and (proof-heap-p before old-objects packages)
                (collection-memory-keys-p
                 (boymoo-model::a64-memory (proof-world-machine before)))
                (collection-memory-keys-p
                 (boymoo-model::a64-memory (proof-world-machine after)))
                (collection-allocator-handoff-p
                 kind bytes origin before middle old-objects moved-objects packages)
                (proof-fast-allocation-return-p
                 kind bytes middle after moved-objects new-objects packages))
           (proof-collector-return-p kind bytes before after old-objects new-objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-heap-frame-through-intermediate
                            (objects old-objects))
                 (:instance collection-register-frame-preserves-unclobbered-register
                            (bound 30) (register 23) (clobbers *collection-allocation-clobbers*)
                            (after middle))
                 (:instance collection-register-frame-preserves-unclobbered-register
                            (bound 30) (register 25) (clobbers *collection-allocation-clobbers*)
                            (after middle))
                 (:instance collection-register-frame-preserves-unclobbered-register
                            (bound 30) (register 30) (clobbers *collection-allocation-clobbers*)
                            (after middle)))
           :in-theory (e/d (proof-machine-limit proof-stack-top)
                           (proof-register-frame-p proof-heap-frame-p proof-heap-p
                            proof-allocation-fits-p proof-reserved-span-p proof-box-top
                            proof-cons-floor proof-heap-limit collection-linux-offset)))))

(local
 (defthm collection-collector-contract-identifies-return-cut
   (implies (proof-collector-return-p kind bytes before after old-objects new-objects packages)
            (and (not (proof-world-stop after))
                 (equal (proof-world-pc after) (proof-world-reg 30 before))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-preserved-heap-p proof-reserved-span-p
                                       proof-register-frame-p)))))

(defthm collection-checked-handoff-and-fast-allocation-return
  (let* ((link (proof-world-reg 30 before))
         (cuts (list link))
         (middle (proof-advance body-count before))
         (after (proof-advance allocation-count middle)))
    (implies (and (natp body-count) (natp allocation-count)
                  (collection-prefix-p body-count cuts before)
                  (collection-prefix-p allocation-count cuts middle)
                  (proof-heap-p before old-objects packages)
                  (collection-memory-keys-p
                   (boymoo-model::a64-memory (proof-world-machine before)))
                  (collection-memory-keys-p
                   (boymoo-model::a64-memory (proof-world-machine after)))
                  (collection-allocator-handoff-p
                   kind bytes origin before middle old-objects moved-objects packages)
                  (proof-fast-allocation-return-p
                   kind bytes middle after moved-objects new-objects packages))
             (and (proof-segment-p (+ body-count allocation-count) cuts before :cut after)
                  (proof-collector-return-p kind bytes before after
                                            old-objects new-objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-fast-allocation-finishes-collector-contract
                            (middle (proof-advance body-count before))
                            (after (proof-advance allocation-count
                                                  (proof-advance body-count before))))
                 (:instance collection-collector-contract-identifies-return-cut
                            (after (proof-advance allocation-count
                                                  (proof-advance body-count before))))
                 (:instance proof-advance-append
                            (prefix body-count) (suffix allocation-count)
                            (world before))
                 (:instance collection-prefix-append
                            (first body-count) (second allocation-count)
                            (cuts (list (proof-world-reg 30 before))) (world before))
                 (:instance collection-prefix-ending-at-cut-is-segment
                            (count (+ body-count allocation-count))
                            (cuts (list (proof-world-reg 30 before)))))
           :in-theory (disable collection-allocator-handoff-p proof-allocator-return-p
                               proof-fast-allocation-return-p proof-collector-return-p
                               proof-run proof-advance proof-segment-p proof-heap-p
                               proof-advance-append collection-prefix-append
                               collection-prefix-p))))
