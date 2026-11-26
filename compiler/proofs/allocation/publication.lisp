(in-package "BOYMOO-PROOFS")

(include-book "representation")

(local (include-book "arithmetic/top" :dir :system))


(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-view-at-greater-depth
  (implies (and (natp depth) (natp greater) (<= depth greater)
                (proof-view-step kind input count depth base objects packages machine))
           (equal (proof-view-step kind input count greater base objects packages machine)
                  (proof-view-step kind input count depth base objects packages machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-view-step kind input count depth base objects packages machine)
           :in-theory (disable proof-cons-value proof-symbol-value proof-rational-value
                               proof-complex-value proof-integer-view proof-load-string
                               proof-pointer-address proof-word-tag proof-header-type
                               proof-header-size proof-load-word proof-span-p))))

(local
 (defthm allocation-old-lookup-after-publication
   (implies (and (not (assoc-equal (car object) objects))
                 (assoc-equal address objects))
            (equal (assoc-equal address (cons object objects))
                   (assoc-equal address objects)))
   :hints (("Goal" :cases ((equal address (car object)))))))

(local
 (defthm allocation-value-views-require-both-fields
   (and (not (proof-cons-value nil view))
        (not (proof-cons-value view nil))
        (not (proof-symbol-value nil view packages))
        (not (proof-symbol-value view nil packages))
        (not (proof-rational-value nil view))
        (not (proof-rational-value view nil))
        (not (proof-complex-value nil view))
        (not (proof-complex-value view nil)))))

(defthm allocation-successful-view-step-after-publication
  (implies (and (not (assoc-equal (car object) objects))
                (proof-view-step kind input count depth base objects packages machine))
           (equal (proof-view-step kind input count depth base
                                   (cons object objects) packages machine)
                  (proof-view-step kind input count depth base objects packages machine)))
  :hints (("Goal" :induct (proof-view-step kind input count depth base objects packages machine)
           :expand ((:free (mode table)
                           (proof-view-step mode input count depth base table packages machine)))
           :in-theory (disable (:definition proof-view-step) mod oddp
                               proof-cons-value proof-symbol-value proof-rational-value
                               proof-complex-value proof-integer-view proof-load-string
                               proof-pointer-address proof-word-tag proof-header-type
                               proof-header-size proof-load-word proof-span-p))))

(defthm allocation-successful-view-after-publication
  (implies (and (not (assoc-equal (car object) objects))
                (proof-view word base objects packages machine))
           (equal (proof-view word base (cons object objects) packages machine)
                  (proof-view word base objects packages machine)))
  :hints (("Goal" :in-theory (disable proof-pointer-address proof-word-tag))))

(defthm allocation-old-records-after-publication
  (implies (and (not (assoc-equal (car object) objects))
                (proof-object-map-p pending objects symbols base packages machine))
           (proof-object-map-p pending (cons object objects) symbols base packages machine))
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-size proof-object-disjoint-p
                               proof-symbol-object-p proof-object-record-p proof-view))))

(defthm allocation-stack-views-after-publication
  (implies (and (not (assoc-equal (car object) objects))
                (proof-stack-views count address base objects packages machine))
           (equal (proof-stack-views count address base (cons object objects) packages machine)
                  (proof-stack-views count address base objects packages machine)))
  :hints (("Goal" :induct (proof-stack-views count address base objects packages machine)
           :in-theory (disable proof-view proof-load-word))))

(defthm allocation-old-dynamic-symbols-after-publication
  (implies (and (not (assoc-equal (car object) objects))
                (proof-object-map-p pending objects symbols base packages machine))
           (equal (proof-dynamic-symbol-objects-p pending (cons object objects) entries base packages machine)
                  (proof-dynamic-symbol-objects-p pending objects entries base packages machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-size proof-object-disjoint-p proof-object-record-p
                               proof-symbol-object-p proof-view))))

(defthm allocation-publish-object
  (let ((address (proof-object-address object))
        (size (proof-object-size object machine)))
    (implies (and (proof-object-map-p objects objects nil base packages machine)
                  (proof-object-record-p object)
                  (not (assoc-equal address objects))
                  (proof-span-p address size)
                  (proof-object-disjoint-p address (+ address size) objects machine)
                  (not (proof-symbol-object-p object machine))
                  (proof-object-view object base (cons object objects) packages machine))
             (proof-object-map-p (cons object objects) (cons object objects)
                                 nil base packages machine)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-object-size proof-object-disjoint-p
                                     proof-symbol-object-p proof-object-record-p
                                     proof-object-view))))

(defun allocation-word-depth (word base objects)
  (1+ (nfix (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))

(defthm allocation-word-view-at-greater-depth
  (implies (and (natp rank) (<= (allocation-word-depth word base objects) rank)
                (proof-view word base objects packages machine))
           (equal (proof-view-step :word word 0 rank base objects packages machine)
                  (proof-view word base objects packages machine)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-view-at-greater-depth
                         (kind :word) (input word) (count 0)
                         (depth (allocation-word-depth word base objects)) (greater rank)))
           :in-theory (disable proof-view-step proof-pointer-address))))

(defthm allocation-initialized-cons-view
  (let* ((object (proof-object address :active :cons rank))
         (word (proof-object-word object base))
         (first (proof-load-word address machine))
         (second (proof-load-word (+ address 8) machine)))
    (implies (and (proof-span-p address 16) (unsigned-byte-p 64 base)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (not (assoc-equal address objects))
                  (natp rank)
                  (<= (allocation-word-depth first base objects) rank)
                  (<= (allocation-word-depth second base objects) rank)
                  (proof-value-p first left base objects packages machine)
                  (proof-value-p second right base objects packages machine))
             (proof-value-p word (cons left right) base (cons object objects) packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-tagged-offset-round-trip (tag 0))
                 (:instance allocation-word-view-at-greater-depth (word (proof-load-word address machine)))
                 (:instance allocation-word-view-at-greater-depth (word (proof-load-word (+ address 8) machine))))
           :expand ((:free (datum object)
                           (proof-view-step :word datum 0 (+ 1 rank) base
                                            (cons object objects)
                                            packages machine)))
           :in-theory (disable (:definition proof-view-step) allocation-word-depth
                               proof-pointer-address proof-word-tag proof-load-word))))

(defthm allocation-initialized-external-string-view
  (let* ((object (proof-object address :external :header 0))
         (word (proof-object-word object base)))
    (implies (and (natp length) (unsigned-byte-p 64 base)
                  (proof-span-p address (+ 8 length))
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (equal (proof-load-word address machine) (allocation-string-header length))
                  (not (assoc-equal address objects)))
             (proof-value-p word (proof-load-string length (+ address 8) machine)
                            base (cons object objects) packages machine)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-tagged-offset-round-trip (tag 2)))
           :expand ((:free (datum object)
                           (proof-view-step :word datum 0 1 base (cons object objects) packages machine)))
           :in-theory (disable (:definition proof-view-step) allocation-string-header
                               proof-pointer-address proof-word-tag proof-header-type
                               proof-header-size proof-load-word
                               proof-load-string))))

(defthm allocation-publish-initialized-cons
  (let* ((object (proof-object address :active :cons rank))
         (first (proof-load-word address machine))
         (second (proof-load-word (+ address 8) machine)))
    (implies (and (proof-span-p address 16) (unsigned-byte-p 64 base)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (not (assoc-equal address objects))
                  (natp rank)
                  (<= (allocation-word-depth first base objects) rank)
                  (<= (allocation-word-depth second base objects) rank)
                  (proof-value-p first left base objects packages machine)
                  (proof-value-p second right base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-object-disjoint-p address (+ address 16) objects machine))
             (and (proof-object-map-p (cons object objects) (cons object objects)
                                      nil base packages machine)
                  (proof-value-p (proof-object-word object base) (cons left right)
                                 base (cons object objects) packages machine))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-initialized-cons-view
                        (:instance allocation-publish-object (object (proof-object address :active :cons rank))))
           :in-theory (disable proof-view proof-object-map-p allocation-word-depth
                               proof-load-word proof-object-disjoint-p mod
                               boymoo-model::a64-unsigned allocation-unsigned-64-of-difference))))

(defthm allocation-publish-initialized-external-string
  (let* ((object (proof-object address :external :header 0))
         (size (+ 8 (proof-align-up length 8))))
    (implies (and (natp length) (unsigned-byte-p 64 base)
                  (proof-span-p address (+ 8 length)) (proof-span-p address size)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (equal (proof-load-word address machine) (allocation-string-header length))
                  (not (assoc-equal address objects))
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-object-disjoint-p address (+ address size) objects machine))
             (and (proof-object-map-p (cons object objects) (cons object objects)
                                      nil base packages machine)
                  (proof-value-p (proof-object-word object base)
                                 (proof-load-string length (+ address 8) machine)
                                 base (cons object objects) packages machine))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-initialized-external-string-view
                        (:instance allocation-publish-object (object (proof-object address :external :header 0))))
           :in-theory (disable proof-view proof-object-map-p proof-align-up proof-load-string
                               proof-load-word proof-object-disjoint-p mod allocation-string-header
                               proof-header-type proof-header-size boymoo-model::a64-unsigned
                               allocation-unsigned-64-of-difference))))
