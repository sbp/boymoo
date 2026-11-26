(in-package "BOYMOO-PROOFS")

(include-book "equality-dispatch")
(include-book "equality-byte-call")
(include-book "bignum-equality")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm p6-header-load-is-integer
   (integerp (proof-load-word address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load)))))

(defthm p6-datum-header-layout
  (let* ((address (proof-pointer-address word base))
         (header (proof-load-word address machine)) (type (proof-header-type header)))
    (implies (and (proof-value-p word value base objects packages machine) (equal (proof-word-tag word) 2))
             (and (member-equal type '(1 2 3 4 5))
                  (implies (equal type 3) (equal (proof-integer-view address machine) (proof-value-view value)))
                  (implies (member-equal type '(4 5)) (equal (proof-header-size header) 16)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-view proof-value-p)
                           (proof-integer-view proof-load-word proof-load-string proof-symbol-value
                            proof-cons-value proof-rational-value proof-complex-value p6-loaded-header-fields))
           :expand ((:free (depth) (proof-view-step :word word 0 depth base objects packages machine)))
           :use p6-even-tag-is-not-an-immediate-integer)))

(local
 (defthm p6-equal-datums-have-equal-header-types
   (let* ((left-header (proof-load-word (proof-pointer-address left base) machine))
          (right-header (proof-load-word (proof-pointer-address right base) machine)))
     (implies (and (integerp left) (integerp right)
                   (proof-value-p left value base objects packages machine)
                   (proof-value-p right value base objects packages machine)
                   (equal (proof-word-tag left) 2) (equal (proof-word-tag right) 2))
              (equal (proof-header-type left-header) (proof-header-type right-header))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-word-class) (p6-loaded-header-fields proof-load-word p6-even-as-mod))
            :use ((:instance p6-word-class-of-value (word left))
                  (:instance p6-word-class-of-value (word right))
                  (:instance p6-datum-header-layout (word left))
                  (:instance p6-datum-header-layout (word right))
                  (:instance p6-even-tag-is-not-an-immediate-integer (word left))
                  (:instance p6-even-tag-is-not-an-immediate-integer (word right)))))))

(defthm p6-equal-published-datums-have-equal-headers
  (let* ((left-address (proof-pointer-address left base)) (right-address (proof-pointer-address right base))
         (left-header (proof-load-word left-address machine)) (right-header (proof-load-word right-address machine)))
    (implies (and (integerp base) (integerp left) (integerp right)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-value-p left value base objects packages machine)
                  (proof-value-p right value base objects packages machine)
                  (equal (proof-word-tag left) 2) (equal (proof-word-tag right) 2))
             (equal left-header right-header)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-word-class p6-datum-class)
                           (proof-load-word proof-object-map-p proof-integer-view proof-header-size
                            proof-header-type p6-loaded-header-fields p6-even-as-mod))
           :use (p6-equal-datums-have-equal-header-types
                 (:instance p6-datum-header-layout (word left))
                 (:instance p6-datum-header-layout (word right))
                 (:instance p6-word-class-of-value (word left))
                 (:instance p6-even-tag-is-not-an-immediate-integer (word left))
                 (:instance p6-published-symbols-equal-exactly-by-word (first value) (second value))
                 (:instance p6-string-equality-by-header-and-payload (first value) (second value))
                 (:instance p6-boxed-integer-equality-by-header-and-payload
                            (left (proof-pointer-address left base)) (right (proof-pointer-address right base))
                            (first machine) (second machine))
                 (:instance p6-header-word-from-type-and-size (header (proof-load-word (proof-pointer-address left base) machine)))
                 (:instance p6-header-word-from-type-and-size (header (proof-load-word (proof-pointer-address right base) machine)))))))

(defthm p6-equal-header-rejection-agrees-with-core
  (implies (and (eq (p6-equal-dispatch-case world) :different-headers)
                (proof-heap-p world objects packages)
                (proof-reg-value-p 0 first world objects packages)
                (proof-reg-value-p 1 second world objects packages))
           (not (equal first second)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-heap-p proof-reg-value-p p6-equal-dispatch-case p6-equal-operand-address
                                         p6-equal-operand-header p6-world-load proof-load-word)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                            proof-heap-object-spans-p proof-string-accounting-p proof-dynamic-symbol-objects-p
                            proof-dynamic-view proof-dynamic-entries proof-stack-prefix))
           :use ((:instance p6-equal-published-datums-have-equal-headers
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world)) (value first)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))))))

(defthm p6-equal-byte-case-agrees-with-core
  (let* ((left (p6-equal-operand-address 0 world)) (right (p6-equal-operand-address 1 world))
         (size (proof-header-size (p6-equal-operand-header 0 world)))
         (machine (proof-world-machine world)))
    (implies (and (eq (p6-equal-dispatch-case world) :bytes)
                  (proof-reg-value-p 0 first world objects packages)
                  (proof-reg-value-p 1 second world objects packages))
             (equal (equal first second)
                    (equal (proof-byte-list size (+ 8 left) machine)
                           (proof-byte-list size (+ 8 right) machine)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-reg-value-p p6-equal-dispatch-case p6-equal-operand-address
                                             p6-equal-operand-header p6-world-load proof-load-word
                                             p6-word-class p6-datum-class)
                           (proof-integer-view proof-header-size proof-header-type p6-loaded-header-fields
                            proof-immediate-integer-p p6-even-as-mod p6-load-equality-is-byte-list-equality))
           :use ((:instance p6-datum-header-layout (word (proof-world-reg 0 world)) (value first)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-datum-header-layout (word (proof-world-reg 1 world)) (value second)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-word-class-of-value (word (proof-world-reg 0 world)) (value first)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-word-class-of-value (word (proof-world-reg 1 world)) (value second)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-even-tag-is-not-an-immediate-integer (word (proof-world-reg 0 world)))
                 (:instance p6-even-tag-is-not-an-immediate-integer (word (proof-world-reg 1 world)))
                 (:instance p6-string-equality-by-header-and-payload
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-boxed-integer-equality-by-header-and-payload
                            (left (p6-equal-operand-address 0 world)) (right (p6-equal-operand-address 1 world))
                            (first (proof-world-machine world)) (second (proof-world-machine world)))))))
