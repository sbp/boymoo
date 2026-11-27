(in-package "BOYMOO-PROOFS")

(include-book "source")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-integer-view proof-symbol-value
                     proof-rational-value proof-complex-value proof-load-word
                     proof-word-tag proof-pointer-address proof-header-type
                     proof-header-size proof-load-string
                     boymoo-model::a64-signed boymoo-model::a64-unsigned)))

(defthm sequence-symbol-view-type
  (implies (equal (proof-symbol-value name number packages) (cons :value datum))
           (symbolp datum))
  :hints (("Goal" :in-theory (enable proof-symbol-value)))
  :rule-classes :forward-chaining)

(defthm sequence-rational-view-type
  (implies (equal (proof-rational-value left right) (cons :value datum))
           (and (rationalp datum) (not (integerp datum))))
  :hints (("Goal" :in-theory (enable proof-rational-value)))
  :rule-classes :forward-chaining)

(defthm sequence-complex-view-type
  (implies (equal (proof-complex-value left right) (cons :value datum))
           (complex-rationalp datum))
  :hints (("Goal" :in-theory (enable proof-complex-value)))
  :rule-classes :forward-chaining)

(defthm sequence-unsigned-word-of-value
  (implies (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view datum))
           (unsigned-byte-p 64 word))
  :hints (("Goal" :expand ((proof-view-step :word word 0 depth
                                                          base objects packages machine))))
  :rule-classes :forward-chaining)

(defthm sequence-cons-value-fields
  (implies
   (equal (proof-cons-value first second) (cons :value datum))
   (and (consp datum)
        (equal first (proof-value-view (car datum)))
        (equal second (proof-value-view (cdr datum)))))
  :rule-classes :forward-chaining)

(defthm sequence-cons-view-of-represented-value
  (implies
   (and (equal (proof-view-step :word word 0 depth base objects packages machine)
               (proof-value-view datum))
        (not (oddp word)))
   (equal (consp datum) (equal (proof-word-tag word) 0)))
  :hints (("Goal"
           :expand ((proof-view-step :word word 0 depth base objects packages machine))
           :in-theory (enable proof-integer-view)))
  :rule-classes nil)

(defthm sequence-cons-fields-of-represented-value
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object)))
    (implies
     (and (equal (proof-view-step :word word 0 depth base objects packages machine)
                 (proof-value-view datum))
          (not (oddp word))
          (equal (proof-word-tag word) 0))
     (and object (natp rank) (< rank depth)
          (eq (proof-object-kind object) :cons)
          (proof-span-p address 16)
          (equal (proof-view-step :word (proof-load-word address machine)
                                  0 rank base objects packages machine)
                 (proof-value-view (car datum)))
          (equal (proof-view-step :word (proof-load-word (+ address 8) machine)
                                  0 rank base objects packages machine)
                 (proof-value-view (cdr datum))))))
  :hints (("Goal"
           :expand ((proof-view-step :word word 0 depth base objects packages machine))
           :in-theory (disable proof-span-p proof-object-rank proof-object-kind)))
  :rule-classes nil)

(defthm sequence-string-view-of-represented-value
  (let* ((address (proof-pointer-address word base))
         (header (proof-load-word address machine))
         (size (proof-header-size header)))
    (implies
     (equal (proof-view-step :word word 0 depth base objects packages machine)
            (proof-value-view datum))
     (and
      (equal (stringp datum)
             (and (not (oddp word))
                  (equal (proof-word-tag word) 2)
                  (equal (proof-header-type header) 1)))
      (implies (stringp datum)
               (and (proof-span-p address (+ 8 size))
                    (equal datum (proof-load-string size (+ address 8) machine)))))))
  :hints (("Goal"
           :expand ((proof-view-step :word word 0 depth base objects packages machine))
           :in-theory (enable proof-integer-view)))
  :rule-classes nil)

(local
 (defun sequence-stack-index-induction (index count address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count address)
     (sequence-stack-index-induction (1- index) (1- count) (+ 8 address)))))

(defthm sequence-view-of-stack-slot
  (implies
   (and (natp index) (natp count) (< index count) (integerp address)
        (proof-stack-views count address base objects packages machine))
   (equal (nth index (cdr (proof-stack-views count address base objects packages machine)))
          (proof-view (proof-load-word (+ address (* 8 index)) machine)
                      base objects packages machine)))
  :hints (("Goal"
           :induct (sequence-stack-index-induction index count address)
           :expand ((proof-stack-views count address base objects packages machine))
           :in-theory (disable proof-view))))

(defthm sequence-selected-root-view-preserved
  (let* ((m (proof-world-machine before))
         (n (proof-world-machine after))
         (base (proof-heap-base before))
         (start (proof-stack-base before))
         (address (+ start (* 8 index))))
    (implies
     (and (natp index) (natp count) (< index count) (integerp start)
          (equal (proof-heap-base after) base)
          (proof-stack-views count start base old-objects packages m)
          (equal (proof-stack-views count start base old-objects packages m)
                 (proof-stack-views count start base new-objects packages n)))
     (equal (proof-view (proof-load-word address n) base new-objects packages n)
            (proof-view (proof-load-word address m) base old-objects packages m))))
  :hints (("Goal"
           :use ((:instance sequence-view-of-stack-slot
                            (address (proof-stack-base before))
                            (base (proof-heap-base before))
                            (objects old-objects)
                            (machine (proof-world-machine before)))
                 (:instance sequence-view-of-stack-slot
                            (address (proof-stack-base before))
                            (base (proof-heap-base before))
                            (objects new-objects)
                            (machine (proof-world-machine after))))
           :in-theory (disable sequence-view-of-stack-slot proof-heap-base
                               proof-stack-base proof-world-machine proof-view
                               proof-stack-views)))
  :rule-classes nil)
