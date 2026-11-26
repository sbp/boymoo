(in-package "BOYMOO-PROOFS")

(include-book "inlines")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-view-step proof-view proof-value-p proof-cons-value
                    proof-word-tag proof-pointer-address proof-object-rank proof-load-word))

(defthm generated-valid-word-view-at-full-depth
  (implies (proof-view-step :word word 0 depth base objects packages machine)
           (equal (proof-view word base objects packages machine)
                  (proof-view-step :word word 0 depth base objects packages machine)))
  :hints (("Goal" :in-theory (enable proof-view)
                  :expand ((:free (limit)
                                  (proof-view-step :word word 0 limit base objects packages machine)))))
  :rule-classes nil)

(local
 (defthm generated-cons-field-views-at-rank
   (let* ((address (proof-pointer-address word base))
          (rank (proof-object-rank (assoc-equal address objects))))
     (implies (and (proof-value-p word value base objects packages machine) (consp value))
              (and (equal (proof-view-step :word (proof-load-word address machine)
                                            0 rank base objects packages machine)
                          (proof-value-view (car value)))
                   (equal (proof-view-step :word (proof-load-word (+ 8 address) machine)
                                            0 rank base objects packages machine)
                          (proof-value-view (cdr value))))))
   :hints (("Goal" :use generated-cons-tag-in-value-view
                   :in-theory (e/d (proof-value-p proof-view proof-cons-value)
                                   (generated-cons-tag-in-value-view))
                   :expand ((:free (limit)
                                   (proof-view-step :word word 0 limit base objects packages machine)))))
   :rule-classes nil))

(defthm generated-cons-word-points-to-two-datums
  (let ((address (proof-pointer-address word base)))
    (implies (and (consp value) (proof-value-p word value base objects packages machine))
             (and (proof-value-p (proof-load-word address machine) (car value)
                                  base objects packages machine)
                  (proof-value-p (proof-load-word (+ 8 address) machine) (cdr value)
                                  base objects packages machine))))
  :hints (("Goal"
           :use (generated-cons-field-views-at-rank
                 (:instance generated-valid-word-view-at-full-depth
                            (word (proof-load-word (proof-pointer-address word base) machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance generated-valid-word-view-at-full-depth
                            (word (proof-load-word (+ 8 (proof-pointer-address word base)) machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects)))))
           :in-theory (enable proof-value-p)))
  :rule-classes nil)
