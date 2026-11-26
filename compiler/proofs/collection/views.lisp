(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-load-word proof-pointer-address proof-word-tag)))

(defun collection-same-limb-words-p (count source copy before after)
  (declare (xargs :measure (nfix count)))
  (or (zp count)
      (and (equal (proof-load-word source before) (proof-load-word copy after))
           (collection-same-limb-words-p (1- count) (+ source 8) (+ copy 8)
                                         before after))))

(local
 (defthm collection-same-limbs-have-same-value
   (implies (collection-same-limb-words-p count source copy before after)
            (and (equal (proof-limbs-p count source before)
                        (proof-limbs-p count copy after))
                 (equal (proof-limb-magnitude count source before)
                        (proof-limb-magnitude count copy after))))
   :hints (("Goal" :induct (collection-same-limb-words-p count source copy before after)
                   :expand ((proof-limbs-p count source before)
                            (proof-limbs-p count copy after)
                            (proof-limb-magnitude count source before)
                            (proof-limb-magnitude count copy after))
                   :in-theory (disable proof-limbs-p proof-limb-magnitude
                                       unsigned-byte-p posp)))))

; A correspondence relates words and fields of equal rank, with equal
; headers and unchanged non-reference payloads. The two object maps
; and the two memories may place their objects at different addresses.
(defun collection-view-transport-p (kind source copy count depth base
                                         old-objects new-objects before after)
  (declare (xargs :measure
                  (make-ord 1 (1+ (nfix depth))
                            (if (eq kind :slots) (1+ (nfix count)) 0))))
  (if (eq kind :slots)
      (or (zp count)
          (and (collection-view-transport-p
                :word (proof-load-word source before) (proof-load-word copy after)
                0 depth base old-objects new-objects before after)
               (collection-view-transport-p
                :slots (+ source 8) (+ copy 8) (1- count) depth base
                old-objects new-objects before after)))
    (let ((tag (proof-word-tag source)))
      (if (not (member-equal tag '(0 2)))
          (equal source copy)
        (let* ((old-address (proof-pointer-address source base))
               (new-address (proof-pointer-address copy base))
               (old (assoc-equal old-address old-objects))
               (new (assoc-equal new-address new-objects))
               (rank (proof-object-rank old)))
          (and (unsigned-byte-p 64 source) (unsigned-byte-p 64 copy)
               (not (oddp source)) (not (oddp copy))
               (equal (proof-word-tag copy) tag)
               old new (natp rank) (< rank (nfix depth))
               (equal (proof-object-rank new) rank)
               (if (equal tag 0)
                   (and (eq (proof-object-kind old) :cons)
                        (eq (proof-object-kind new) :cons)
                        (proof-span-p old-address 16) (proof-span-p new-address 16)
                        (collection-view-transport-p
                         :word (proof-load-word old-address before)
                         (proof-load-word new-address after)
                         0 rank base old-objects new-objects before after)
                        (collection-view-transport-p
                         :word (proof-load-word (+ old-address 8) before)
                         (proof-load-word (+ new-address 8) after)
                         0 rank base old-objects new-objects before after))
                 (let* ((header (proof-load-word old-address before))
                        (size (proof-header-size header))
                        (old-fields (+ old-address 8))
                        (new-fields (+ new-address 8)))
                   (and (eq (proof-object-kind old) :header)
                        (eq (proof-object-kind new) :header)
                        (equal (proof-load-word new-address after) header)
                        (proof-span-p old-address (+ 8 size))
                        (proof-span-p new-address (+ 8 size))
                        (case (proof-header-type header)
                          (1 (equal (proof-byte-list size old-fields before)
                                    (proof-byte-list size new-fields after)))
                          (3 (and (equal (proof-load-word old-fields before)
                                         (proof-load-word new-fields after))
                                  (collection-same-limb-words-p
                                   (1- (ash size -3)) (+ old-fields 8) (+ new-fields 8)
                                   before after)))
                          ((2 4 5)
                           (and (equal size 16)
                                (collection-view-transport-p
                                 :word (proof-load-word old-fields before)
                                 (proof-load-word new-fields after)
                                 0 rank base old-objects new-objects before after)
                                (collection-view-transport-p
                                 :word (proof-load-word (+ old-fields 8) before)
                                 (proof-load-word (+ new-fields 8) after)
                                 0 rank base old-objects new-objects before after)))
                          (6 (and (equal (mod size 8) 0)
                                  (collection-view-transport-p
                                   :slots old-fields new-fields (ash size -3) rank base
                                   old-objects new-objects before after)))
                          (otherwise nil)))))))))))

(defthm collection-transport-preserves-view-step
  (implies (collection-view-transport-p kind source copy count depth base
                                        old-objects new-objects before after)
           (equal (proof-view-step kind source count depth base old-objects packages before)
                  (proof-view-step kind copy count depth base new-objects packages after)))
  :hints (("Goal"
           :induct (collection-view-transport-p kind source copy count depth base
                                               old-objects new-objects before after)
           :in-theory (disable proof-byte-list proof-limbs-p proof-limb-magnitude
                               proof-symbol-value proof-rational-value proof-complex-value
                               proof-cons-value proof-header-type proof-header-size
                               (:definition ash) (:definition oddp) assoc-equal))))

(defthm collection-transport-preserves-view
  (let* ((old (assoc-equal (proof-pointer-address source base) old-objects))
         (new (assoc-equal (proof-pointer-address copy base) new-objects))
         (depth (1+ (nfix (proof-object-rank old)))))
    (implies (and (equal (proof-object-rank old) (proof-object-rank new))
                  (collection-view-transport-p :word source copy 0 depth base
                                               old-objects new-objects before after))
             (equal (proof-view source base old-objects packages before)
                    (proof-view copy base new-objects packages after))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable collection-view-transport-p proof-view-step assoc-equal))))
