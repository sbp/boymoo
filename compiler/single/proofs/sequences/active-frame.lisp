(in-package "BOYMOO-PROOFS")

(include-book "stack-invariant")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-active-write-p (start end before after)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after)))
    (and (natp end)
         (proof-subspan-p start (- end start) (proof-active-floor before) (proof-active-end before))
         (sequence-machine-write-confined-p start end first last)
         (sequence-heap-registers-agree-p before after)
         (equal (cdr after) (cdr before))
         (proof-subspan-p (boymoo-model::a64-sp last) 0
                          (sequence-machine-stack-base before) (sequence-machine-stack-end before))
         (equal (mod (boymoo-model::a64-sp last) 16) 0))))

(local
 (defthm sequence-active-static-address-fields-are-natural
   (and (natp (proof-heap-base before))
        (natp (proof-static-size (proof-heap-base before) (proof-world-machine before))))
   :hints (("Goal" :in-theory (enable proof-heap-base proof-world-reg proof-reg proof-static-size proof-load-word)))
   :rule-classes nil))

(local
 (defthm sequence-active-write-disjointness
   (let* ((base (proof-heap-base before))
          (static (proof-static-size base (proof-world-machine before)))
          (static-end (+ base static))
          (stack (proof-stack-base before))
          (stack-end (proof-stack-end before))
          (machine-base (sequence-machine-stack-base before))
          (machine-end (sequence-machine-stack-end before)))
     (implies
      (and (proof-heap-layout-p before)
           (natp end)
           (proof-subspan-p start (- end start) (proof-active-floor before) (proof-active-end before)))
      (and (<= 80 static)
           (proof-span-p (- base 128) (+ 128 static))
           (proof-span-p stack (- stack-end stack))
           (proof-span-p machine-base (- machine-end machine-base))
           (proof-disjoint-p (- base 128) static-end start end)
           (proof-disjoint-p stack stack-end start end)
           (proof-disjoint-p machine-base machine-end start end))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-disjoint-p proof-span-p proof-subspan-p
                      sequence-machine-stack-base sequence-machine-stack-end)
                     (proof-regions-p proof-align-up proof-heap-layout-p))
     :expand ((proof-heap-layout-p before))
     :use (sequence-active-static-address-fields-are-natural
           (:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-align-up-covers-address
                      (address (+ (proof-heap-base before)
                                  (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                      (alignment *proof-runtime-page*)))))
   :rule-classes nil))

(defthm sequence-active-write-keeps-surrounding-spans
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-active-write-p start end before after))
             (and (sequence-machine-span-agrees-p (- base 128) (+ base (proof-static-size base first)) first last)
                  (sequence-machine-span-agrees-p (proof-stack-base before) (proof-stack-end before) first last)
                  (sequence-machine-span-agrees-p (sequence-machine-stack-base before)
                                                  (sequence-machine-stack-end before) first last))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-active-write-p proof-span-p)
                    (proof-heap-layout-p proof-subspan-p proof-disjoint-p sequence-machine-span-agrees-p
                     sequence-machine-write-confined-p sequence-machine-stack-base sequence-machine-stack-end))
    :use (sequence-active-write-disjointness
          (:instance sequence-agreement-outside-confined-write
                     (lower (- (proof-heap-base before) 128))
                     (upper (+ (proof-heap-base before)
                               (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                     (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-agreement-outside-confined-write
                     (lower (proof-stack-base before)) (upper (proof-stack-end before))
                     (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-agreement-outside-confined-write
                     (lower (sequence-machine-stack-base before)) (upper (sequence-machine-stack-end before))
                     (first (proof-world-machine before)) (last (proof-world-machine after))))))
  :rule-classes nil)

(local
 (defthm sequence-active-write-keeps-header-words
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (base (proof-heap-base before))
          (address (+ (- base 128) offset)))
     (implies (and (proof-heap-layout-p before)
                   (sequence-active-write-p start end before after)
                   (natp offset) (<= offset 152))
              (equal (proof-load-word address last) (proof-load-word address first))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-load-word proof-span-p proof-subspan-p sequence-active-write-p)
                     (sequence-machine-span-agrees-p sequence-machine-write-confined-p
                      sequence-heap-registers-agree-p proof-heap-layout-p))
     :use (sequence-active-write-keeps-surrounding-spans
           sequence-active-write-disjointness
           sequence-active-static-address-fields-are-natural
           (:instance sequence-read-in-agreed-machine-span
                      (start (- (proof-heap-base before) 128))
                      (end (+ (proof-heap-base before)
                              (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                      (address (+ (- (proof-heap-base before) 128) offset)) (count 8)
                      (first (proof-world-machine before)) (last (proof-world-machine after))))))
   :rule-classes nil))

(defthm sequence-active-write-keeps-heap-metadata
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-active-write-p start end before after))
             (and (sequence-heap-metadata-agrees-p before after)
                  (equal (proof-dynamic-root base last) (proof-dynamic-root base first)))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-active-write-p sequence-heap-registers-agree-p sequence-heap-metadata-agrees-p
                     proof-static-size proof-dynamic-root proof-active-floor proof-active-end proof-cons-floor
                     proof-inactive-floor proof-inactive-end proof-stack-base proof-stack-end proof-external-head
                     proof-spaces-end proof-string-bytes-since-collection proof-string-budget proof-runtime-word)
                    (proof-heap-layout-p proof-span-p proof-subspan-p proof-load-word
                     sequence-machine-write-confined-p))
    :use ((:instance sequence-active-write-keeps-header-words (offset 0))
          (:instance sequence-active-write-keeps-header-words (offset 8))
          (:instance sequence-active-write-keeps-header-words (offset 16))
          (:instance sequence-active-write-keeps-header-words (offset 24))
          (:instance sequence-active-write-keeps-header-words (offset 32))
          (:instance sequence-active-write-keeps-header-words (offset 40))
          (:instance sequence-active-write-keeps-header-words (offset 48))
          (:instance sequence-active-write-keeps-header-words (offset 56))
          (:instance sequence-active-write-keeps-header-words (offset 64))
          (:instance sequence-active-write-keeps-header-words (offset 72))
          (:instance sequence-active-write-keeps-header-words (offset 80))
          (:instance sequence-active-write-keeps-header-words (offset 128))
          (:instance sequence-active-write-keeps-header-words (offset 152)))))
  :rule-classes nil)

(defthm sequence-active-write-keeps-heap-layout
  (implies (and (proof-heap-layout-p before)
                (sequence-active-write-p start end before after))
           (proof-heap-layout-p after))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-active-write-p sequence-heap-registers-agree-p
                     sequence-heap-metadata-agrees-p sequence-machine-stack-base
                     sequence-machine-stack-end proof-subspan-p)
                    (proof-heap-layout-p proof-regions-p proof-align-up proof-disjoint-p
                     proof-span-p proof-streams-preserved-p proof-world-stop proof-world-regions
                     proof-world-replies proof-world-page-size sequence-machine-write-confined-p))
    :expand ((proof-heap-layout-p before) (proof-heap-layout-p after))
    :use (sequence-active-write-keeps-heap-metadata sequence-world-tail-fields)))
  :rule-classes nil)

(defthm sequence-active-write-keeps-caller-heap-frame
  (implies (and (proof-heap-layout-p before)
                (sequence-active-write-p start end before after))
           (proof-heap-frame-p before after))
  :hints
  (("Goal"
    :in-theory (e/d (proof-heap-frame-p sequence-active-write-p sequence-heap-registers-agree-p
                     sequence-heap-metadata-agrees-p sequence-machine-stack-base sequence-machine-stack-end)
                    (proof-heap-layout-p proof-span-p proof-subspan-p sequence-machine-span-agrees-p
                     sequence-machine-write-confined-p proof-streams-preserved-p proof-world-stop
                     proof-world-replies proof-world-page-size proof-world-regions))
    :use (sequence-active-write-keeps-heap-metadata
          sequence-active-write-keeps-surrounding-spans sequence-world-tail-fields
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-machine-agreement-on-subinterval
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (- (proof-heap-base before) 128))
                     (upper (+ (proof-heap-base before)
                               (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                     (start (proof-heap-base before)) (end (+ (proof-heap-base before) 24)))
          (:instance sequence-machine-agreement-on-subinterval
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (- (proof-heap-base before) 128))
                     (upper (+ (proof-heap-base before)
                               (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                     (start (+ (proof-heap-base before) 32))
                     (end (+ (proof-heap-base before)
                             (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
          (:instance sequence-machine-agreement-on-subinterval
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (sequence-machine-stack-base before)) (upper (sequence-machine-stack-end before))
                     (start (boymoo-model::a64-sp (proof-world-machine before))) (end (sequence-machine-stack-end before))))))
  :rule-classes nil)
