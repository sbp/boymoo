(in-package "BOYMOO-PROOFS")

(include-book "stack-storage")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-world-tail-fields
  (implies (equal (cdr before) (cdr after))
           (and (equal (proof-world-regions after) (proof-world-regions before))
                (equal (proof-world-page-size after) (proof-world-page-size before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (equal (proof-world-stop after) (proof-world-stop before))
                (proof-streams-preserved-p before after)))
  :hints (("Goal" :in-theory (enable proof-world-regions)))
  :rule-classes nil)

(defun sequence-heap-metadata-agrees-p (before after)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after))
        (base (proof-heap-base before)))
    (and (equal (proof-static-size base last) (proof-static-size base first))
         (equal (proof-active-floor after) (proof-active-floor before))
         (equal (proof-active-end after) (proof-active-end before))
         (equal (proof-cons-floor after) (proof-cons-floor before))
         (equal (proof-inactive-floor after) (proof-inactive-floor before))
         (equal (proof-inactive-end after) (proof-inactive-end before))
         (equal (proof-stack-base after) (proof-stack-base before))
         (equal (proof-stack-end after) (proof-stack-end before))
         (equal (proof-external-head after) (proof-external-head before))
         (equal (proof-spaces-end after) (proof-spaces-end before))
         (equal (proof-string-bytes-since-collection after)
                (proof-string-bytes-since-collection before))
         (equal (proof-string-budget after) (proof-string-budget before)))))

(defthm sequence-stack-write-keeps-heap-metadata
  (implies (and (proof-heap-layout-p before)
                (sequence-stack-write-p start end before after))
           (sequence-heap-metadata-agrees-p before after))
  :hints
  (("Goal"
    :in-theory (e/d (proof-stack-base proof-stack-end proof-active-floor proof-active-end
                     proof-inactive-floor proof-inactive-end proof-cons-floor proof-external-head
                     proof-spaces-end proof-string-bytes-since-collection proof-string-budget
                     proof-static-size)
                    (proof-heap-layout-p proof-regions-p))
    :use ((:instance sequence-static-header-after-stack-write (offset 0))
          (:instance sequence-runtime-words-after-stack-write (offset 0))
          (:instance sequence-runtime-words-after-stack-write (offset 8))
          (:instance sequence-runtime-words-after-stack-write (offset 16))
          (:instance sequence-runtime-words-after-stack-write (offset 24))
          (:instance sequence-runtime-words-after-stack-write (offset 32))
          (:instance sequence-runtime-words-after-stack-write (offset 40))
          (:instance sequence-runtime-words-after-stack-write (offset 48))
          (:instance sequence-runtime-words-after-stack-write (offset 56))
          (:instance sequence-runtime-words-after-stack-write (offset 64))
          (:instance sequence-runtime-words-after-stack-write (offset 72))
          (:instance sequence-runtime-words-after-stack-write (offset 80)))))
  :rule-classes nil)

(local
 (defthm sequence-layout-uses-heap-fields
   (let ((last (proof-world-machine after)))
     (implies (and (sequence-heap-registers-agree-p before after)
                   (sequence-heap-metadata-agrees-p before after)
                   (equal (proof-world-regions after) (proof-world-regions before))
                   (equal (proof-world-page-size after) (proof-world-page-size before))
                   (not (proof-world-stop after))
                   (<= (sequence-machine-stack-base before) (boymoo-model::a64-sp last))
                   (<= (boymoo-model::a64-sp last) (sequence-machine-stack-end before))
                   (equal (mod (boymoo-model::a64-sp last) 16) 0)
                   (proof-heap-layout-p before))
              (proof-heap-layout-p after)))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-heap-registers-agree-p
                      sequence-machine-stack-base sequence-machine-stack-end)
                     (proof-align-up proof-regions-p proof-disjoint-p
                      proof-page-size-p proof-world-page-size proof-world-stop))))
   :rule-classes nil))

(defthm sequence-stack-write-keeps-heap-layout
  (implies (and (proof-heap-layout-p before)
                (sequence-stack-write-p start end before after))
           (proof-heap-layout-p after))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p sequence-machine-stack-end)
                    (proof-heap-layout-p sequence-heap-registers-agree-p
                     sequence-heap-metadata-agrees-p proof-streams-preserved-p
                     proof-world-stdout proof-world-stderr proof-world-stop
                     proof-world-page-size proof-world-replies proof-regions-p))
    :use (sequence-layout-uses-heap-fields
          sequence-stack-write-keeps-heap-metadata sequence-world-tail-fields
          (:instance sequence-heap-layout-bounds (world before)))))
  :rule-classes nil)

(defthm sequence-stack-write-keeps-caller-heap-frame
  (implies (and (proof-heap-layout-p before)
                (sequence-stack-write-p start end before after))
           (proof-heap-frame-p before after))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p sequence-heap-registers-agree-p
                     sequence-machine-stack-base sequence-machine-stack-end)
                    (proof-heap-layout-p proof-streams-preserved-p
                     proof-world-stop proof-world-page-size proof-world-replies proof-regions-p))
    :use (sequence-stack-write-keeps-heap-metadata
          sequence-stack-write-keeps-heap-spans sequence-world-tail-fields
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-machine-agreement-on-subinterval
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (- (proof-heap-base before) *proof-heap-prefix*))
                     (upper (proof-spaces-end before))
                     (start (proof-heap-base before)) (end (+ (proof-heap-base before) 24)))
          (:instance sequence-machine-agreement-on-subinterval
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (- (proof-heap-base before) *proof-heap-prefix*))
                     (upper (proof-spaces-end before))
                     (start (+ (proof-heap-base before) 32))
                     (end (+ (proof-heap-base before)
                             (proof-static-size (proof-heap-base before)
                                                (proof-world-machine before))))))))
  :rule-classes nil)

(local
 (defthm sequence-region-record-of-member
   (implies (and (proof-regions-p regions) (member-equal region regions))
            (proof-region-p region))
   :hints (("Goal" :induct (proof-regions-p regions)
                   :in-theory (disable proof-region-p proof-region-disjoint-p)))
   :rule-classes nil))

(local
 (defthm sequence-external-string-header-size
   (implies (equal (proof-header-type (proof-load-word address machine)) 1)
            (natp (proof-header-size (proof-load-word address machine))))
   :hints (("Goal" :in-theory (enable proof-load-word)
                   :use ((:instance sequence-floor-of-unsigned
                                    (dropped 8) (kept 56)
                                    (value (proof-load-word address machine))))))
   :rule-classes nil))

(defthm sequence-external-mapping-bounds
  (let* ((machine (proof-world-machine world))
         (size (proof-load-word (+ head 8) machine))
         (payload-size (proof-header-size (proof-load-word (+ head 24) machine))))
    (implies (and (proof-regions-p (proof-world-regions world))
                  (not (equal head 0))
                  (proof-external-objects head fuel world objects))
             (and (proof-span-p head size)
                  (natp payload-size)
                  (<= 32 size)
                  (<= (+ 32 payload-size) size)
                  (proof-disjoint-p head (+ head size)
                                    (sequence-machine-stack-base world)
                                    (sequence-machine-stack-end world)))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-machine-stack-base sequence-machine-stack-end)
                    (proof-external-objects proof-align-up proof-header-size
                     proof-regions-p proof-spaces-end proof-disjoint-p))
    :expand ((proof-external-objects head fuel world objects))
    :use ((:instance sequence-region-record-of-member
                     (regions (proof-world-regions world))
                     (region (proof-region head (+ head (proof-load-word
                                                         (+ head 8) (proof-world-machine world)))
                                            :rw)))
          (:instance sequence-external-string-header-size
                     (machine (proof-world-machine world)) (address (+ head 24)))
          (:instance sequence-align-up-covers-address
                     (address (+ 32 (proof-header-size
                                     (proof-load-word (+ head 24) (proof-world-machine world)))))
                     (alignment *proof-runtime-page*)))))
  :rule-classes nil)

(defthm sequence-mapping-bytes-unchanged-by-stack-write
  (let* ((machine (proof-world-machine before))
         (size (proof-load-word (+ head 8) machine)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-stack-write-p start end before after)
                  (not (equal head 0))
                  (proof-external-objects head fuel before objects))
             (sequence-machine-span-agrees-p head (+ head size)
                                             machine (proof-world-machine after))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p)
                    (proof-heap-layout-p proof-external-objects
                     sequence-heap-registers-agree-p proof-regions-p))
    :use ((:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-external-mapping-bounds (world before))
          (:instance sequence-agreement-outside-confined-write
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower head)
                     (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))))))
  :rule-classes nil)

(in-theory (disable sequence-heap-metadata-agrees-p))
