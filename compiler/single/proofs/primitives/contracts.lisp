(in-package "BOYMOO-PROOFS")

(include-book "state-invariants")
(include-book "data-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-runtime-pre-p proof-value-p proof-reg-value-p
                    proof-datum-return-p proof-segment-p p6-path-end))

(defthm p6-even-tag-is-not-an-immediate-integer
  (implies (and (integerp word) (member-equal (proof-word-tag word) '(0 2 4)))
           (not (oddp word)))
  :hints (("Goal" :use p6-odd-from-tag
                  :in-theory (disable proof-word-tag p6-even-as-mod))))

(defthm p6-immediate-word-has-no-even-datum-tag
  (implies (and (integerp word) (oddp word))
           (and (not (equal (proof-word-tag word) 0))
                (not (equal (proof-word-tag word) 2))
                (not (equal (proof-word-tag word) 4))))
  :hints (("Goal" :in-theory (disable p6-even-as-mod)
                  :use p6-even-tag-is-not-an-immediate-integer)))

(defthm p6-tag-tests-agree-with-core
  (implies (and (proof-value-p word value base objects packages machine)
                (integerp word) (member-equal name '(consp characterp)))
           (equal (equal (proof-word-tag word) (if (eq name 'consp) 0 4))
                  (boymoo-model::core-datum
                   (boymoo-model::core-primitive name (list value) program))))
  :rule-classes nil
  :hints (("Goal" :use p6-word-class-of-value
                  :in-theory (e/d (p6-word-class p6-datum-class boymoo-model::core-primitive)
                                  (p6-even-as-mod)))))

(defconst *p6-public-type-tests*
  '(stringp symbolp complex-rationalp integerp rationalp acl2-numberp))

(defthm p6-type-tests-agree-with-core
  (implies (and (proof-value-p word value base objects packages machine)
                (integerp word) (member-equal name *p6-public-type-tests*))
           (equal (p6-type-test-value
                   name word (proof-header-type (proof-load-word (proof-pointer-address word base) machine))
                   limit)
                  (boymoo-model::core-datum
                   (boymoo-model::core-primitive name (list value) program))))
  :rule-classes nil
  :hints (("Goal" :use p6-word-class-of-value
                  :in-theory (e/d (p6-word-class p6-datum-class p6-type-test-value
                                   boymoo-model::core-primitive)
                                  (proof-word-tag proof-pointer-address proof-immediate-integer-p
                                   proof-header-type proof-load-word p6-loaded-header-fields
                                   p6-even-as-mod)))))

(defthm p6-header-byte-is-header-type
  (implies (equal (proof-word-tag (proof-world-reg 0 world)) 2)
           (equal (p6-header-byte world)
                  (proof-header-type
                   (proof-load-word (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world))
                                    (proof-world-machine world)))))
  :hints (("Goal" :in-theory (enable p6-header-byte p6-header-address p6-world-load proof-pointer-address))))

(defthm p6-cons-load-is-field-word
  (implies (equal (proof-word-tag (proof-world-reg 0 world)) 0)
           (equal (p6-world-load 8 (p6-projection-address name (proof-world-reg 0 world)
                                                         (proof-heap-base world)) world)
                  (p6-field-word (if (eq name 'car) 0 8) (proof-world-reg 0 world)
                                 (proof-heap-base world) (proof-world-machine world))))
  :hints (("Goal"
           :use ((:instance p6-world-load-add-wraps
                            (count 8) (address (+ (proof-world-reg 0 world) (proof-heap-base world)))
                            (delta (if (eq name 'car) 0 8))))
           :in-theory (e/d (p6-field-word p6-projection-address p6-world-load
                                          proof-pointer-address proof-load-word)
                           (p6-world-load-add-wraps p6-load-equality-is-byte-list-equality)))))

(defund p6-leaf-primitive-p (name)
  (or (member-equal name '(acl2::bad-atom<= car cdr consp characterp))
      (member-equal name *p6-public-type-tests*)))

(defund p6-leaf-primitive-sites (name world)
  (case name
    (acl2::bad-atom<= (p6-literal-sites "rt:nil"))
    ((car cdr) (p6-projection-sites name (proof-world-reg 0 world)))
    ((consp characterp) (p6-tag-test-sites name))
    (otherwise (p6-type-test-sites name (proof-world-reg 0 world)
                                   (p6-header-byte world) (proof-world-reg 1 world)))))

(defund p6-leaf-primitive-word (name world)
  (let* ((word (proof-world-reg 0 world)) (tag (proof-word-tag word)))
    (case name
      (acl2::bad-atom<= *proof-nil*)
      ((car cdr) (if (equal tag 0)
                     (p6-world-load 8 (p6-projection-address name word (proof-heap-base world)) world)
                   *proof-nil*))
      (consp (p6-boolean-word (equal tag 0)))
      (characterp (p6-boolean-word (equal tag 4)))
      (otherwise (p6-boolean-word (p6-type-test-value name word (p6-header-byte world)
                                                      (proof-world-reg 1 world)))))))

(defund p6-leaf-primitive-loads-p (name world)
  (let ((word (proof-world-reg 0 world)) (regions (proof-world-regions world)))
    (cond ((and (member-equal name '(car cdr)) (equal (proof-word-tag word) 0))
           (proof-covered-p (p6-projection-address name word (proof-heap-base world)) 8 :read regions))
          ((and (member-equal name *p6-public-type-tests*) (equal (proof-word-tag word) 2))
           (proof-covered-p (p6-header-address world) 1 :read regions))
          (t t))))

(defun p6-leaf-primitive-flags-p (name)
  (not (eq name 'acl2::bad-atom<=)))

(defthm p6-leaf-primitive-machine-return
  (let ((sites (p6-leaf-primitive-sites name world)))
    (implies (and (p6-leaf-primitive-p name) (p6-leaf-primitive-loads-p name world)
                  (p6-path-entry-p sites base world))
             (p6-read-only-return-p (p6-leaf-primitive-word name world)
                                    (proof-runtime-clobbers name) (p6-leaf-primitive-flags-p name)
                                    sites world)))
  :rule-classes nil
  :hints (("Goal"
           :use (p6-tag-test-returns p6-cons-projection-returns
                 (:instance p6-literal-entry-returns (entry "rt:nil"))
                 p6-stringp-returns p6-symbolp-returns p6-complex-rationalp-returns
                 p6-integerp-returns p6-rationalp-returns p6-acl2-numberp-returns)
           :in-theory (enable p6-leaf-primitive-p p6-leaf-primitive-loads-p p6-type-test-contract-p
                              p6-leaf-primitive-sites p6-leaf-primitive-word p6-literal-word))))

(defund p6-boolean-views-p (world objects packages)
  (and (proof-machine-value-p *proof-t* t world objects packages)
       (proof-machine-value-p *proof-nil* nil world objects packages)))

(defthm p6-leaf-primitive-specification
  (let* ((word (proof-world-reg 0 world))
         (base (proof-heap-base world))
         (machine (proof-world-machine world))
         (result (boymoo-model::core-primitive name args program)))
    (implies (and (p6-leaf-primitive-p name)
                  (proof-value-p word (car args) base objects packages machine)
                  (p6-boolean-views-p world objects packages))
             (proof-value-p (p6-leaf-primitive-word name world) (boymoo-model::core-datum result)
                            base objects packages machine)))
  :rule-classes nil
  :hints (("Goal"
           :use (p6-cons-load-is-field-word
                 (:instance p6-tag-tests-agree-with-core
                            (word (proof-world-reg 0 world)) (value (car args))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-type-tests-agree-with-core
                            (word (proof-world-reg 0 world)) (value (car args))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (limit (proof-world-reg 1 world)))
                 (:instance p6-cons-field-views
                            (word (proof-world-reg 0 world)) (value (car args))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-tag-tests-agree-with-core
                            (name 'consp) (word (proof-world-reg 0 world)) (value (car args))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (p6-leaf-primitive-p p6-leaf-primitive-word p6-boolean-views-p
                                           p6-boolean-word p6-type-test-value boymoo-model::core-primitive)
                           (p6-cons-load-is-field-word p6-loaded-header-fields proof-header-type proof-load-word
                            proof-pointer-address proof-word-tag)))))

(defthm p6-runtime-pre-has-heap-and-first-arg
  (implies (proof-runtime-pre-p name args program labels code-base world objects packages)
           (and (proof-heap-p world objects packages)
                (implies (consp args) (proof-reg-value-p 0 (car args) world objects packages))))
  :hints (("Goal" :in-theory (e/d (proof-runtime-pre-p)
                                  (proof-runtime-entry proof-program-packages-p)))))

(defthm p6-leaf-primitive-runtime-contract
  (let* ((sites (p6-leaf-primitive-sites name world))
         (after (p6-path-end sites world)))
    (implies (and (p6-leaf-primitive-p name) (consp args)
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-path-entry-p sites runtime-base world)
                  (p6-leaf-primitive-loads-p name world)
                  (p6-boolean-views-p world objects packages))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (p6-runtime-pre-has-heap-and-first-arg
                 p6-leaf-primitive-specification
                 (:instance p6-leaf-primitive-machine-return (base runtime-base))
                 (:instance p6-read-only-datum-return
                            (before world) (sites (p6-leaf-primitive-sites name world))
                            (word (p6-leaf-primitive-word name world))
                            (value (boymoo-model::core-datum (boymoo-model::core-primitive name args program)))
                            (clobbers (proof-runtime-clobbers name)) (flags (p6-leaf-primitive-flags-p name))))
           :in-theory (enable p6-leaf-primitive-p p6-read-only-return-p proof-reg-value-p
                              boymoo-model::core-primitive))))
