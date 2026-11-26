(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-load-word proof-load-string proof-pointer-address
                    proof-header-type proof-header-size proof-word-tag
                    proof-view-step proof-view proof-limbs-p
                    proof-immediate-integer-p proof-integer-word proof-character-word
                    proof-object-rank proof-object-kind proof-span-p))

(defthm p6-integer-parts
  (implies (integerp x)
           (and (equal (numerator x) x)
                (equal (denominator x) 1)))
  :hints (("Goal"
           :use (p6-numerator-product
                 (:instance acl2::lowest-terms
                            (acl2::n (denominator x)) (acl2::x x)
                            (acl2::r x) (acl2::q 1))
                 (:instance acl2::rational-implies1 (acl2::x x))))))

(defthm p6-rational-parts
  (implies (rationalp x)
           (and (equal (realpart x) x) (equal (imagpart x) 0)))
  :hints (("Goal"
           :use ((:instance acl2::complex-definition (acl2::x x) (acl2::y 0))
                 (:instance acl2::realpart-complex (acl2::x x) (acl2::y 0))
                 (:instance acl2::imagpart-complex (acl2::x x) (acl2::y 0)))
           :in-theory (disable acl2::realpart-complex acl2::imagpart-complex))))

(local
 (defthm p6-complex-type
   (implies (and (rationalp x) (rationalp y) (not (equal y 0)))
            (complex-rationalp (complex x y)))
   :hints (("Goal" :use ((:instance acl2::imagpart-complex (acl2::x x) (acl2::y y)))
                   :in-theory (disable acl2::imagpart-complex)))))

(local
 (defthm p6-loaded-word-integer
   (integerp (proof-load-word address machine))
   :hints (("Goal" :in-theory (enable proof-load-word)))
   :rule-classes :type-prescription))

(local
 (defthm p6-limb-magnitude-integer
   (integerp (proof-limb-magnitude count address machine))
   :rule-classes :type-prescription))

(local
 (defthm p6-integer-view-type
   (implies (proof-integer-view address machine)
            (integerp (proof-view-value (proof-integer-view address machine))))))

(defund p6-datum-class (value)
  (cond ((consp value) :cons)
        ((characterp value) :character)
        ((stringp value) :string)
        ((symbolp value) :symbol)
        ((integerp value)
         (if (proof-immediate-integer-p value) :immediate :bignum))
        ((rationalp value) :fraction)
        ((complex-rationalp value) :complex)
        (t :other)))

(defund p6-word-class (word base machine)
  (let ((tag (proof-word-tag word)))
    (cond ((oddp word) :immediate)
          ((equal tag 0) :cons)
          ((equal tag 4) :character)
          ((equal tag 2)
           (case (proof-header-type (proof-load-word (proof-pointer-address word base)
                                                     machine))
             (1 :string) (2 :symbol) (3 :bignum) (4 :fraction) (5 :complex)
             (6 :vector) (otherwise :other)))
          (t :other))))

(defthm p6-word-class-of-view
  (implies (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view value))
           (equal (p6-word-class word base machine) (p6-datum-class value)))
  :rule-classes nil
  :hints (("Goal" :expand ((proof-view-step :word word 0 depth base objects packages machine))
                  :use (p6-odd-word-decodes-to-immediate
                        (:instance p6-integer-view-type
                                   (address (proof-pointer-address word base))))
                  :in-theory (e/d (p6-word-class p6-datum-class)
                                  (proof-integer-view p6-integer-view-type)))))

(defthm p6-word-class-of-value
  (implies (proof-value-p word value base objects packages machine)
           (equal (p6-word-class word base machine) (p6-datum-class value)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-view)
                  :use ((:instance p6-word-class-of-view
                                   (depth (1+ (nfix (proof-object-rank
                                                     (assoc-equal (proof-pointer-address word base)
                                                                  objects))))))))))

; A successful word lookup at a bounded depth has the same view at the
; depth supplied by the word's own object record.
(defthm p6-rank-independent-word-view
  (implies (proof-view-step :word word 0 depth base objects packages machine)
           (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-view word base objects packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-view)
                           (proof-integer-view proof-symbol-value proof-rational-value
                            proof-complex-value proof-cons-value))
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine))))))

(defund p6-field-word (offset word base machine)
  (proof-load-word (+ offset (proof-pointer-address word base)) machine))

(local
 (defthm p6-source-view-eta
   (implies (equal (car view) :value)
            (equal (cons :value (cdr view)) view))))

(defthm p6-cons-field-views
  (implies (and (proof-value-p word value base objects packages machine)
                (consp value))
           (and (proof-value-p (p6-field-word 0 word base machine) (car value)
                               base objects packages machine)
                (proof-value-p (p6-field-word 8 word base machine) (cdr value)
                               base objects packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-field-word proof-view p6-datum-class p6-word-class)
                           (proof-integer-view proof-symbol-value proof-rational-value
                            proof-complex-value))
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine)))
           :use (p6-word-class-of-value
                 (:instance p6-rank-independent-word-view
                            (word (p6-field-word 0 word base machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance p6-rank-independent-word-view
                            (word (p6-field-word 8 word base machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))))))

(defthm p6-rational-field-views
  (implies (and (proof-value-p word value base objects packages machine)
                (rationalp value) (not (integerp value)))
           (and (proof-value-p (p6-field-word 8 word base machine) (numerator value)
                               base objects packages machine)
                (proof-value-p (p6-field-word 16 word base machine) (denominator value)
                               base objects packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-field-word proof-view p6-datum-class p6-word-class)
                           (proof-integer-view proof-symbol-value proof-complex-value
                            proof-cons-value))
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine)))
           :use (p6-word-class-of-value
                 (:instance p6-rank-independent-word-view
                            (word (p6-field-word 8 word base machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance p6-rank-independent-word-view
                            (word (p6-field-word 16 word base machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))))))

(defthm p6-complex-field-views
  (implies (and (proof-value-p word value base objects packages machine)
                (complex-rationalp value))
           (and (proof-value-p (p6-field-word 8 word base machine) (realpart value)
                               base objects packages machine)
                (proof-value-p (p6-field-word 16 word base machine) (imagpart value)
                               base objects packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-field-word proof-view p6-datum-class p6-word-class)
                           (proof-integer-view proof-symbol-value proof-rational-value
                            proof-cons-value))
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine)))
           :use (p6-word-class-of-value
                 (:instance p6-rank-independent-word-view
                            (word (p6-field-word 8 word base machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance p6-rank-independent-word-view
                            (word (p6-field-word 16 word base machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))))))
