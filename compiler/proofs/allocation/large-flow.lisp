(in-package "BOYMOO-PROOFS")

(include-book "large-contracts")
(include-book "saved-words")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-large-map-label-is-continuation
  (equal (allocation-large-string-address origin 19)
         (allocation-code-address "rt:map-string" origin)))

(defthm allocation-large-budget-checked-edge
  (let* ((path (allocation-large-budget-path before))
         (target (allocation-large-budget-target before origin))
         (cuts (list target)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-large-string-address origin 12))
                  (< (+ (proof-world-reg 1 before) (proof-world-reg 20 before)) *allocation-word-modulus*)
                  (allocation-path-ready-p path cuts before)
                  (equal cut (allocation-path-end path before)))
             (proof-segment-p (len path) cuts before :cut cut)))
  :rule-classes nil
  :hints (("Goal" :use (allocation-large-budget-machine-edge
                        (:instance allocation-checked-cut
                         (instructions (allocation-large-budget-path before)) (world before) (after cut)
                         (cuts (list (allocation-large-budget-target before origin)))))
           :in-theory (disable allocation-large-budget-path allocation-large-budget-target
                               allocation-checked-cut allocation-path-ready-p allocation-path-end proof-segment-p))))

(defthm allocation-large-collector-return-keeps-map-arguments
  (implies (proof-collector-return-p :header 0 before after old-objects new-objects packages)
           (and (proof-heap-p after new-objects packages)
                (equal (proof-world-pc after) (proof-world-reg 30 before))
                (equal (allocation-sp after) (allocation-sp before))
                (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                (equal (proof-world-reg 21 after) (proof-world-reg 21 before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-member
                  (register 19) (upper 30) (clobbers (append *proof-volatile-registers* '(26 27))))
                 (:instance allocation-register-frame-member
                  (register 20) (upper 30) (clobbers (append *proof-volatile-registers* '(26 27))))
                 (:instance allocation-register-frame-member
                  (register 21) (upper 30) (clobbers (append *proof-volatile-registers* '(26 27)))))
           :in-theory (disable proof-heap-p proof-heap-frame-p proof-preserved-heap-p proof-reserved-span-p
                               proof-register-frame-p proof-active-floor proof-inactive-floor)
           :expand ((proof-preserved-heap-p nil before after old-objects new-objects packages)))))

(defthm allocation-large-collection-continuation
  (let* ((path (allocation-large-budget-path before))
         (cuts (list (allocation-code-address "rt:map-string" origin))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-large-string-address origin 12))
                  (allocation-large-collect-p (proof-world-reg 1 before) (proof-world-reg 20 before)
                                              (proof-world-reg 2 before))
                  (< (+ (proof-world-reg 1 before) (proof-world-reg 20 before)) *allocation-word-modulus*)
                  (allocation-path-ready-p path cuts before)
                  (equal cut (allocation-path-end path before))
                  (natp steps)
                  (proof-segment-p steps cuts cut :cut after)
                  (proof-collector-return-p :header 0 cut after old-objects new-objects packages))
             (and (equal (proof-world-pc cut) (allocation-code-address "rt:collect" origin))
                  (equal (proof-world-reg 0 cut) 0)
                  (equal (proof-world-reg 1 cut) 0)
                  (equal (proof-world-pc after) (allocation-code-address "rt:map-string" origin))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
                  (equal (allocation-sp after) (allocation-sp before))
                  (proof-heap-p after new-objects packages)
                  (proof-segment-p (+ (len path) steps) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-budget-machine-edge
                 (:instance allocation-large-collector-return-keeps-map-arguments (before cut))
                 (:instance allocation-prefix-from-path
                  (path (allocation-large-budget-path before))
                  (cuts (list (allocation-code-address "rt:map-string" origin))))
                 (:instance allocation-segment-after-prefix
                  (count (len (allocation-large-budget-path before))) (remaining steps) (middle cut) (reason :cut)
                  (cuts (list (allocation-code-address "rt:map-string" origin)))))
           :in-theory (disable allocation-large-budget-path allocation-path-end allocation-path-ready-p
                               allocation-prefix-p proof-segment-p proof-collector-return-p proof-heap-p
                               allocation-prefix-from-path allocation-code-address allocation-large-string-address))))

(defthm allocation-large-collector-keeps-save-record
  (let* ((sp (allocation-sp before))
         (limit (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (proof-collector-return-p :header 0 before after old-objects new-objects packages)
                  (proof-subspan-p sp 32 sp limit)
                  (member-equal offset '(0 8 16 24)))
             (equal (allocation-load-word (+ sp offset) after) (allocation-load-word (+ sp offset) before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-allocator-preserves-saved-word
                  (kind :header) (bytes 0) (address (+ (allocation-sp before) offset))))
           :in-theory (disable proof-allocator-return-p proof-active-floor proof-inactive-floor proof-machine-limit))))

(defthm allocation-large-refused-request-exits
  (let* ((path (list *allocation-large-map-test*))
         (cuts (list (allocation-code-address (proof-resource-label :mapping) origin))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-large-string-address origin 21))
                  (equal (proof-world-reg 0 before) 0)
                  (allocation-path-ready-p path cuts before)
                  (equal cut (allocation-path-end path before))
                  (natp stop-steps)
                  (proof-segment-p stop-steps nil cut '(:exit . 3) after)
                  (null (proof-world-stdout after)))
             (and (proof-segment-p (+ 1 stop-steps) nil before '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-refused-mapping-edge
                 (:instance allocation-path-then-resource-exit
                  (path (list *allocation-large-map-test*))
                  (cuts (list (allocation-code-address (proof-resource-label :mapping) origin)))))
           :in-theory (disable allocation-path-ready-p allocation-path-end proof-segment-p proof-resource-observation-p))))
