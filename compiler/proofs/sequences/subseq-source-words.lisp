(in-package "BOYMOO-PROOFS")

(include-book "subseq-list-layout")
(include-book "publication-views")
(include-book "cons-views")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-words-viewed-at-rank-p (words datums depth base objects packages machine)
  (if (atom words)
      (null datums)
    (and (consp datums)
         (equal (proof-view-step :word (car words) 0 depth base objects packages machine)
                (proof-value-view (car datums)))
         (sequence-words-viewed-at-rank-p (cdr words) (cdr datums) depth base objects packages machine))))

(local
 (defthm sequence-pointer-datum-has-an-object
   (implies (and (proof-value-p word datum base objects packages machine)
                 (not (oddp word)) (not (equal (proof-word-tag word) 4)))
            (assoc-equal (proof-pointer-address word base) objects))
   :hints
   (("Goal"
     :in-theory (e/d (proof-value-p proof-view)
                     (proof-view-step proof-pointer-address proof-word-tag
                      proof-load-word oddp evenp))
     :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))))
   :rule-classes nil))

(defthm sequence-old-value-at-rank-in-extended-map
  (implies (and (proof-value-p word datum base objects packages first)
                (sequence-object-storage-agrees-p objects first last)
                (sequence-object-lookups-agree-p objects objects extended)
                (sequence-ranks-below-p objects depth)
                (natp depth))
           (equal (proof-view-step :word word 0 depth base extended packages last)
                  (proof-value-view datum)))
  :hints
  (("Goal"
    :in-theory (disable proof-value-p proof-view-step proof-word-tag proof-pointer-address
                        proof-object-rank sequence-ranks-below-p sequence-object-lookups-agree-p
                        oddp evenp)
    :use (sequence-old-value-after-publication
          (:instance sequence-pointer-datum-has-an-object (machine first))
          (:instance sequence-existing-object-rank-below-limit (records objects) (limit depth)
                     (address (proof-pointer-address word base)))
          (:instance sequence-existing-object-lookup-in-extension (pending objects)
                     (address (proof-pointer-address word base)))
          (:instance sequence-datum-view-at-sufficient-rank (objects extended) (machine last)))))
  :rule-classes nil)

(defthm sequence-value-view-at-greater-rank
  (implies (and (natp depth) (natp greater) (<= depth greater)
                (equal (proof-view-step :word word 0 depth base objects packages machine)
                       (proof-value-view datum)))
           (equal (proof-view-step :word word 0 greater base objects packages machine)
                  (proof-value-view datum)))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-word-tag proof-pointer-address proof-object-rank
                        proof-load-word oddp evenp)
    :expand ((proof-view-step :word word 0 depth base objects packages machine)
             (proof-view-step :word word 0 greater base objects packages machine))))
  :rule-classes nil)

(local
 (defthm sequence-subseq-source-field-values
   (let* ((memory (boymoo-model::a64-memory machine))
          (first (sequence-subseq-cell-source-word word base memory))
          (tail (sequence-subseq-cell-source-tail word base memory)))
     (implies
      (and (proof-value-p word datum base objects packages machine)
           (proof-value-p *proof-nil* nil base objects packages machine))
      (and (proof-value-p first (car datum) base objects packages machine)
           (proof-value-p tail (if (consp datum) (cdr datum) datum) base objects packages machine))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-value-p proof-view proof-load-word)
                     (proof-view-step proof-pointer-address proof-word-tag proof-object-rank
                      sequence-even-tags-mark-even-words oddp evenp
                      sequence-unsigned-word-of-value))
     :use ((:instance sequence-word-cons-tag
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address word base) objects))))))
           (:instance sequence-unsigned-word-of-value
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address word base) objects))))))
           sequence-even-tags-mark-even-words
           (:instance sequence-cons-fields-of-represented-value
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address word base) objects))))))
           (:instance sequence-value-view-at-its-own-rank (datum (car datum))
                      (word (proof-load-word (proof-pointer-address word base) machine))
                      (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
           (:instance sequence-value-view-at-its-own-rank (datum (cdr datum))
                      (word (proof-load-word (+ 8 (proof-pointer-address word base)) machine))
                      (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))))
   :rule-classes nil))

(local
 (defun sequence-subseq-words-and-values-induction (count word datum base memory)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons word datum)
     (sequence-subseq-words-and-values-induction
      (1- count) (sequence-subseq-cell-source-tail word base memory)
      (if (consp datum) (cdr datum) datum) base memory))))

(defthm sequence-subseq-selected-words-represent-take
  (let* ((memory (boymoo-model::a64-memory first))
         (words (sequence-subseq-copy-words count word base memory)))
    (implies
     (and (natp count) (natp depth)
          (proof-value-p word datum base objects packages first)
          (proof-value-p *proof-nil* nil base objects packages first)
          (sequence-object-storage-agrees-p objects first last)
          (sequence-object-lookups-agree-p objects objects extended)
          (sequence-ranks-below-p objects depth))
     (sequence-words-viewed-at-rank-p words (take count datum) depth base extended packages last)))
  :hints
  (("Goal"
    :in-theory (disable proof-value-p proof-view-step proof-load-word proof-pointer-address
                        proof-word-tag sequence-subseq-cell-source-word sequence-subseq-cell-source-tail
                        sequence-object-lookups-agree-p sequence-ranks-below-p)
    :induct (sequence-subseq-words-and-values-induction count word datum base (boymoo-model::a64-memory first))
    :expand ((sequence-subseq-copy-words count word base (boymoo-model::a64-memory first))
             (:free (car-word cdr-words datums)
                    (sequence-words-viewed-at-rank-p (cons car-word cdr-words) datums
                                                     depth base extended packages last))
             (take count datum)))
   ("Subgoal *1/2"
    :use ((:instance sequence-subseq-source-field-values (machine first))
          (:instance sequence-old-value-at-rank-in-extended-map
                     (word (sequence-subseq-cell-source-word word base (boymoo-model::a64-memory first)))
                     (datum (car datum))))))
  :rule-classes nil)
