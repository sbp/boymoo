(in-package "BOYMOO-PROOFS")

(include-book "object-memory")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-machine-stack-base (world)
  (- (proof-machine-limit world) *proof-machine-margin*))

(defun sequence-machine-stack-end (world)
  (+ (sequence-machine-stack-base world) *proof-machine-reservation*))

(defun sequence-heap-registers-agree-p (before after)
  (and (equal (proof-heap-base after) (proof-heap-base before))
       (equal (proof-box-top after) (proof-box-top before))
       (equal (proof-heap-limit after) (proof-heap-limit before))
       (equal (proof-stack-top after) (proof-stack-top before))
       (equal (proof-stack-limit after) (proof-stack-limit before))
       (equal (proof-machine-limit after) (proof-machine-limit before))))

(defun sequence-stack-write-p (start end before after)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after)))
    (and (proof-subspan-p start (- end start)
                          (sequence-machine-stack-base before)
                          (sequence-machine-stack-end before))
         (<= end (boymoo-model::a64-sp first))
         (proof-subspan-p (boymoo-model::a64-sp last) 0
                          (sequence-machine-stack-base before)
                          (sequence-machine-stack-end before))
         (equal (mod (boymoo-model::a64-sp last) 16) 0)
         (sequence-heap-registers-agree-p before after)
         (equal (cdr before) (cdr after))
         (sequence-machine-write-confined-p start end first last))))

(in-theory (disable proof-heap-base proof-box-top proof-heap-limit
                    proof-stack-top proof-stack-limit proof-machine-limit
                    proof-static-size proof-runtime-word proof-stack-base proof-stack-end
                    proof-active-floor proof-active-end proof-inactive-floor proof-inactive-end
                    proof-cons-floor proof-external-head proof-spaces-end proof-covered-p
                    proof-string-bytes-since-collection proof-string-budget
                    proof-world-machine proof-world-regions))

(defthm sequence-covered-span
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :hints (("Goal" :in-theory (enable proof-covered-p)
                  :induct (proof-covered-p address size access regions)))
  :rule-classes nil)

(defthm sequence-heap-layout-bounds
  (let* ((base (proof-heap-base world))
         (static (proof-static-size base (proof-world-machine world)))
         (floor (- base *proof-heap-prefix*))
         (end (proof-spaces-end world))
         (stack (proof-stack-base world))
         (stack-end (proof-stack-end world))
         (machine-base (sequence-machine-stack-base world))
         (machine-end (sequence-machine-stack-end world)))
    (implies (proof-heap-layout-p world)
             (and (<= 80 static)
                  (proof-subspan-p base static floor end)
                  (proof-span-p floor (- end floor))
                  (proof-span-p stack (- stack-end stack))
                  (proof-span-p machine-base (- machine-end machine-base))
                  (<= floor (proof-active-floor world))
                  (<= (proof-active-end world) end)
                  (proof-disjoint-p floor end machine-base machine-end)
                  (proof-disjoint-p stack stack-end machine-base machine-end)
                  (<= machine-base (boymoo-model::a64-sp (proof-world-machine world)))
                  (<= (boymoo-model::a64-sp (proof-world-machine world)) machine-end)
                  (not (proof-world-stop world))
                  (proof-regions-p (proof-world-regions world)))))
  :hints
  (("Goal" :in-theory (disable proof-align-up proof-regions-p)
           :use ((:instance sequence-covered-span
                            (address (- (proof-heap-base world) *proof-heap-prefix*))
                            (size (- (proof-spaces-end world)
                                     (- (proof-heap-base world) *proof-heap-prefix*)))
                            (access :write) (regions (proof-world-regions world)))
                 (:instance sequence-covered-span
                            (address (proof-stack-base world))
                            (size *proof-value-reservation*)
                            (access :write) (regions (proof-world-regions world)))
                 (:instance sequence-covered-span
                            (address (sequence-machine-stack-base world))
                            (size *proof-machine-reservation*)
                            (access :write) (regions (proof-world-regions world)))
                 (:instance sequence-align-up-covers-address
                            (address (+ (proof-heap-base world)
                                        (proof-static-size (proof-heap-base world)
                                                           (proof-world-machine world))))
                            (alignment *proof-runtime-page*)))))
  :rule-classes nil)

(defthm sequence-stack-write-keeps-heap-spans
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before))
         (sp (boymoo-model::a64-sp first))
         (end-of-stack (sequence-machine-stack-end before)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-stack-write-p start end before after))
             (and (sequence-machine-span-agrees-p (- base *proof-heap-prefix*)
                                                  (proof-spaces-end before) first last)
                  (sequence-machine-span-agrees-p (proof-stack-base before)
                                                  (proof-stack-end before) first last)
                  (sequence-machine-span-agrees-p sp end-of-stack first last))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-layout-p proof-regions-p
                        sequence-machine-stack-base sequence-machine-stack-end
                        sequence-heap-registers-agree-p)
    :use ((:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-agreement-outside-confined-write
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (- (proof-heap-base before) *proof-heap-prefix*))
                     (upper (proof-spaces-end before)))
          (:instance sequence-agreement-outside-confined-write
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (proof-stack-base before)) (upper (proof-stack-end before)))
          (:instance sequence-agreement-outside-confined-write
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (boymoo-model::a64-sp (proof-world-machine before)))
                     (upper (sequence-machine-stack-end before))))))
  :rule-classes nil)

(defthm sequence-runtime-words-after-stack-write
  (implies (and (proof-heap-layout-p before)
                (sequence-stack-write-p start end before after)
                (natp offset) (<= offset 120))
           (equal (proof-runtime-word offset after) (proof-runtime-word offset before)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-word proof-load-word)
                    (proof-heap-layout-p proof-regions-p
                     sequence-machine-stack-base sequence-machine-stack-end))
    :use ((:instance sequence-heap-layout-bounds (world before))
          sequence-stack-write-keeps-heap-spans
          (:instance sequence-read-in-agreed-machine-span
                     (start (- (proof-heap-base before) *proof-heap-prefix*))
                     (end (proof-spaces-end before))
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (address (+ (- (proof-heap-base before) 128) offset)) (count 8)))))
  :rule-classes nil)

(defthm sequence-static-header-after-stack-write
  (implies (and (proof-heap-layout-p before)
                (sequence-stack-write-p start end before after)
                (natp offset) (<= offset 72))
           (equal (proof-load-word (+ (proof-heap-base before) offset)
                                   (proof-world-machine after))
                  (proof-load-word (+ (proof-heap-base before) offset)
                                   (proof-world-machine before))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-load-word)
                    (proof-heap-layout-p proof-regions-p
                     sequence-machine-stack-base sequence-machine-stack-end))
    :use ((:instance sequence-heap-layout-bounds (world before))
          sequence-stack-write-keeps-heap-spans
          (:instance sequence-read-in-agreed-machine-span
                     (start (- (proof-heap-base before) *proof-heap-prefix*))
                     (end (proof-spaces-end before))
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (address (+ (proof-heap-base before) offset)) (count 8)))))
  :rule-classes nil)

(in-theory (disable sequence-machine-stack-base sequence-machine-stack-end
                    sequence-heap-registers-agree-p sequence-stack-write-p))
