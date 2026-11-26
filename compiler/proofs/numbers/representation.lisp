(in-package "BOYMOO-PROOFS")

(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash oddp evenp
                     boymoo-model::a64-signed boymoo-model::a64-unsigned
                     acl2::binary-logand acl2::binary-logior
                     boymoo-model::a64-load boymoo-model::a64-read-bytes
                     proof-load-word proof-word-tag proof-header-type proof-header-size
                     proof-pointer-address)))

(defthm proof-number-immediate-word-bits
  (implies (proof-immediate-integer-p value)
           (equal (proof-integer-word value)
                  (if (< value 0)
                      (+ (expt 2 64) 1 (* 2 value))
                    (+ 1 (* 2 value)))))
  :hints (("Goal"
           :use ((:instance proof-number-a64-unsigned-is-modulo (width 64)
                            (a (+ 1 (* 2 value))))
                 (:instance proof-number-mod-with-remainder
                            (a (+ 1 (* 2 value))) (b (expt 2 64))
                            (q -1) (r (+ (expt 2 64) 1 (* 2 value))))))))

(defthm proof-number-signed-immediate-word
  (implies (proof-immediate-integer-p value)
           (equal (boymoo-model::a64-signed 64 (proof-integer-word value))
                  (+ 1 (* 2 value))))
  :hints (("Goal"
           :in-theory (disable proof-number-immediate-word-bits)
           :use ((:instance proof-number-a64-signed-after-unsigned (width 64)
                            (a (+ 1 (* 2 value))))))))

(local
 (defthm odd-linear-value
   (implies (integerp value)
            (oddp (+ 1 (* 2 value))))
   :hints (("Goal"
            :use ((:instance proof-number-mod-with-remainder
                             (a (+ 1 (* 2 value))) (b 2) (q value) (r 1)))))))

(defthm proof-number-immediate-word-is-odd
  (implies (proof-immediate-integer-p value)
           (oddp (proof-integer-word value)))
  :hints (("Goal"
           :in-theory (disable proof-integer-word oddp proof-number-integer-parity)
           :use ((:instance odd-linear-value (value (+ (expt 2 63) value)))))))

(defthm proof-number-integer-word-range
  (unsigned-byte-p 64 (proof-integer-word value)))

(local
 (defthm signed-word-is-odd
   (implies (and (unsigned-byte-p 64 word) (oddp word))
            (equal (mod (boymoo-model::a64-signed 64 word) 2) 1))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-value (width 64) (a word))
                  (:instance proof-number-mod-shift-by-multiple
                             (a word) (b 2) (times (- (expt 2 63)))))))))

(defthm proof-number-odd-word-round-trip
  (implies (and (unsigned-byte-p 64 word) (oddp word))
           (let ((value (ash (boymoo-model::a64-signed 64 word) -1)))
             (and (proof-immediate-integer-p value)
                  (equal (proof-integer-word value) word))))
  :hints (("Goal"
           :use (signed-word-is-odd
                 (:instance proof-number-a64-signed-value (width 64) (a word))
                 (:instance proof-number-quotient-and-remainder
                            (a (boymoo-model::a64-signed 64 word)) (b 2))
                 (:instance proof-number-positive-divisor-floor-bounds
                            (a (boymoo-model::a64-signed 64 word)) (b 2))
                 (:instance proof-number-immediate-word-bits
                            (value (floor (boymoo-model::a64-signed 64 word) 2))))
           :in-theory (disable proof-integer-word
                               proof-number-immediate-word-bits signed-word-is-odd)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-odd-word-view
  (implies (and (unsigned-byte-p 64 word) (oddp word))
           (equal (proof-view word base objects packages machine)
                  (proof-value-view (ash (boymoo-model::a64-signed 64 word) -1))))
  :hints (("Goal"
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (disable proof-view-step proof-number-ash-half oddp))))

(defthm proof-number-immediate-word-view
  (implies (proof-immediate-integer-p value)
           (proof-value-p (proof-integer-word value) value base objects packages machine))
  :hints (("Goal"
           :use ((:instance proof-number-floor-with-remainder
                            (a (+ 1 (* 2 value))) (b 2) (q value)))
           :in-theory (disable proof-integer-word proof-view
                               proof-number-immediate-word-bits oddp))))

(defund proof-number-datum-class (value)
  (cond ((integerp value) 3)
        ((rationalp value) 4)
        ((complex-rationalp value) 5)
        (t 0)))

(defund proof-number-word-class (word base machine)
  (cond ((oddp word) 3)
        ((equal (proof-word-tag word) 2)
         (let ((kind (proof-header-type
                      (proof-load-word (proof-pointer-address word base) machine))))
           (if (member-equal kind '(3 4 5)) kind 0)))
        (t 0)))

(defthm proof-number-limb-magnitude-is-natural
  (natp (proof-limb-magnitude count address machine))
  :hints (("Goal" :induct (proof-limb-magnitude count address machine)))
  :rule-classes :type-prescription)

(defthm proof-number-view-class
  (implies (proof-value-p word value base objects packages machine)
           (and (unsigned-byte-p 64 word)
                (equal (proof-number-word-class word base machine)
                       (proof-number-datum-class value))))
  :hints (("Goal"
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (e/d (proof-number-word-class proof-number-datum-class)
                           (proof-view-step proof-limb-magnitude proof-limbs-p
                            proof-load-string oddp proof-number-odd-word-view
                            proof-number-integer-parity)))))

(defthm proof-number-value-has-immediate-word
  (implies (proof-value-p word value base objects packages machine)
           (and (equal (oddp word) (proof-immediate-integer-p value))
                (implies (oddp word) (equal word (proof-integer-word value)))))
  :hints (("Goal"
           :use proof-number-odd-word-round-trip
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (disable proof-view-step proof-limbs-p proof-limb-magnitude
                               proof-load-string proof-integer-word oddp
                               proof-number-integer-parity proof-number-immediate-word-bits
                               proof-number-odd-word-view)))
  :rule-classes nil)

(defthm proof-number-tagged-zero-and-one
  (implies (proof-value-p word value base objects packages machine)
           (and (equal (equal word 1) (equal value 0))
                (equal (equal word 3) (equal value 1))))
  :hints (("Goal"
           :use (proof-number-value-has-immediate-word
                 (:instance proof-number-immediate-word-view (value 0))
                 (:instance proof-number-immediate-word-view (value 1)))
           :in-theory (disable proof-view proof-number-immediate-word-view)))
  :rule-classes nil)

(defthm proof-number-boxed-integer-sign
  (implies (and (proof-value-p word value base objects packages machine)
                (integerp value) (not (oddp word)))
           (let* ((address (proof-pointer-address word base))
                  (sign (proof-load-word (+ 8 address) machine)))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type (proof-load-word address machine)) 3)
                  (equal sign (if (< value 0) 1 0)))))
  :hints (("Goal"
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (disable proof-view-step proof-limbs-p proof-limb-magnitude
                               proof-load-string proof-number-integer-parity)))
  :rule-classes nil)

(defthm proof-number-ranked-and-outer-views-agree
  (implies (proof-view-step :word word 0 depth base objects packages machine)
           (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-view word base objects packages machine)))
  :hints (("Goal"
           :expand ((:free (limit)
                     (proof-view-step :word word 0 limit base objects packages machine)))
           :in-theory (disable proof-view-step proof-integer-view proof-limbs-p
                               proof-limb-magnitude proof-load-string proof-number-integer-parity
                               proof-rational-value proof-complex-value proof-symbol-value
                               proof-cons-value proof-number-odd-word-view)))
  :rule-classes nil)

(defun proof-number-field-word (word base field machine)
  (proof-load-word (+ (proof-pointer-address word base) (* 8 field)) machine))

(local
 (defthm recover-value-view
   (implies (equal (car view) :value)
            (equal (cons :value (cdr view)) view))))

(defthm proof-number-fraction-fields
  (implies (and (proof-value-p word value base objects packages machine)
                (rationalp value) (not (integerp value)))
           (and (equal (proof-word-tag word) 2)
                (proof-value-p (proof-number-field-word word base 1 machine)
                               (numerator value) base objects packages machine)
                (proof-value-p (proof-number-field-word word base 2 machine)
                               (denominator value) base objects packages machine)))
  :hints (("Goal"
           :use ((:instance proof-number-ranked-and-outer-views-agree
                            (word (proof-number-field-word word base 1 machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance proof-number-ranked-and-outer-views-agree
                            (word (proof-number-field-word word base 2 machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects)))))
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (disable proof-view-step proof-limb-magnitude proof-limbs-p
                               proof-load-string proof-number-integer-parity
                               proof-number-odd-word-view)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-complex-fields
  (implies (and (proof-value-p word value base objects packages machine)
                (complex-rationalp value))
           (and (equal (proof-word-tag word) 2)
                (proof-value-p (proof-number-field-word word base 1 machine)
                               (realpart value) base objects packages machine)
                (proof-value-p (proof-number-field-word word base 2 machine)
                               (imagpart value) base objects packages machine)))
  :hints (("Goal"
           :use ((:instance proof-number-ranked-and-outer-views-agree
                            (word (proof-number-field-word word base 1 machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance proof-number-ranked-and-outer-views-agree
                            (word (proof-number-field-word word base 2 machine))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects)))))
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (disable proof-view-step proof-limb-magnitude proof-limbs-p
                               proof-load-string proof-number-integer-parity
                               proof-number-odd-word-view)
           :do-not-induct t))
  :rule-classes nil)

; A published numeric box has a 16-byte payload and a rank greater
; than the ranks of its two fields.
(defund proof-number-box-fields-p (kind word a b base objects packages machine)
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object))
         (header (proof-load-word address machine)))
    (and (member-equal kind '(4 5))
         (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
         (proof-span-p address 24)
         object (eq (proof-object-kind object) :header) (natp rank)
         (equal header (+ 4096 kind))
         (equal (proof-view-step :word (proof-number-field-word word base 1 machine)
                                 0 rank base objects packages machine)
                (proof-value-view a))
         (equal (proof-view-step :word (proof-number-field-word word base 2 machine)
                                 0 rank base objects packages machine)
                (proof-value-view b)))))

(defthm proof-number-published-fraction
  (implies (and (proof-number-reduced-p a b) (< 1 b)
                (proof-number-box-fields-p 4 word a b base objects packages machine))
           (and (proof-value-p word (/ a b) base objects packages machine)
                (not (integerp (/ a b)))))
  :hints (("Goal"
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (e/d (proof-number-reduced-p proof-number-box-fields-p)
                           (proof-view-step proof-number-integer-parity
                            proof-number-odd-word-view)))))

(defthm proof-number-published-complex
  (implies (and (rationalp a) (rationalp b) (not (equal b 0))
                (proof-number-box-fields-p 5 word a b base objects packages machine))
           (and (proof-value-p word (complex a b) base objects packages machine)
                (complex-rationalp (complex a b))))
  :hints (("Goal"
           :expand ((:free (depth)
                     (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (e/d (proof-number-box-fields-p)
                           (proof-view-step proof-number-integer-parity
                            proof-number-odd-word-view)))))
