(in-package "BOYMOO-PROOFS")

(include-book "contracts")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-numeric-class (word type)
  (cond ((oddp word) 3)
        ((and (equal (proof-word-tag word) 2) (member-equal type '(3 4 5))) type)
        (t 0)))

(defund p6-number-class-sites (word type)
  (cond ((oddp word)
         (append (p6-sites "rt:num-type" 3) (p6-sites "rt:num-type-return" 1)))
        ((not (equal (proof-word-tag word) 2))
         (append (p6-sites "rt:num-type" 6) (p6-sites "rt:num-type-other" 2)))
        ((member-equal type '(3 4 5))
         (append (p6-sites "rt:num-type" 12) (p6-sites "rt:num-type-return" 1)))
        (t (p6-sites "rt:num-type" 14))))

(local
 (defthm p6-byte-minus-three-test
   (implies (unsigned-byte-p 8 type)
            (equal (<= (boymoo-model::a64-unsigned 64 (- type 3)) 2)
                   (if (member-equal type '(3 4 5)) t nil)))
   :hints (("Goal" :use ((:instance p6-unsigned-between-wraps (x (- type 3)) (width 64)))))))

(defthm p6-numeric-type-entry-returns
  (let* ((word (proof-world-reg 0 world))
         (type (p6-header-byte world))
         (sites (p6-number-class-sites word type))
         (after (p6-path-end sites world)))
    (implies (and (p6-path-entry-p sites base world)
                  (or (oddp word) (not (equal (proof-word-tag word) 2))
                      (proof-covered-p (p6-header-address world) 1 :read (proof-world-regions world))))
             (and (p6-read-only-return-p word '(3 4 5) t sites world)
                  (equal (proof-world-reg 3 after) (p6-numeric-class word type))
                  (implies (and (not (oddp word)) (equal (proof-word-tag word) 2))
                           (equal (proof-world-reg 4 after) (p6-header-address world))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-number-class-sites p6-numeric-class p6-read-only-return-p
                                                  p6-path-entry-p p6-path-end proof-word-tag
                                                  p6-same-mapped-memory-p p6-header-address p6-header-byte)
                           (proof-segment-p p6-sites-placed-p p6-header-byte-is-header-type))
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-number-class-sites (proof-world-reg 0 world) (p6-header-byte world)))
                            (cuts (list (proof-world-reg 30 world))))))))

(defconst *p6-numeric-projections* '(numerator denominator realpart imagpart))

(defund p6-numeric-class-of-datum (value)
  (cond ((integerp value) 3)
        ((rationalp value) 4)
        ((complex-rationalp value) 5)
        (t 0)))

(defthm p6-numeric-class-agrees-with-datum
  (implies (and (integerp word) (proof-value-p word value base objects packages machine))
           (let* ((header (proof-load-word (proof-pointer-address word base) machine))
                  (type (proof-header-type header)))
             (equal (p6-numeric-class word type) (p6-numeric-class-of-datum value))))
  :rule-classes nil
  :hints (("Goal" :use p6-word-class-of-value
                  :in-theory (enable p6-word-class p6-datum-class p6-numeric-class
                                     p6-numeric-class-of-datum))))

(defund p6-projected-numeric-word (name word base machine)
  (let* ((header (proof-load-word (proof-pointer-address word base) machine))
         (type (p6-numeric-class word (proof-header-type header))))
    (case name
      (numerator (cond ((equal type 3) word)
                       ((equal type 4) (p6-field-word 8 word base machine))
                       (t 1)))
      (denominator (if (equal type 4) (p6-field-word 16 word base machine) 3))
      (realpart (cond ((equal type 5) (p6-field-word 8 word base machine))
                      ((equal type 0) 1)
                      (t word)))
      (imagpart (if (equal type 5) (p6-field-word 16 word base machine) 1)))))

(local
 (defthm p6-zero-and-one-views
   (and (proof-value-p 1 0 base objects packages machine)
        (proof-value-p 3 1 base objects packages machine))
   :hints (("Goal" :in-theory (enable proof-value-p proof-view)
                   :expand ((:free (word cap) (proof-view-step :word word 0 cap base objects packages machine)))))))

(defthm p6-numeric-projection-word-agrees-with-core
  (implies (and (member-equal name *p6-numeric-projections*)
                (integerp word) (proof-value-p word value base objects packages machine))
           (proof-value-p
            (p6-projected-numeric-word name word base machine)
            (boymoo-model::core-datum (boymoo-model::core-primitive name (list value) program))
            base objects packages machine))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable p6-projected-numeric-word p6-numeric-class-of-datum
                                     boymoo-model::core-primitive)
                  :use (p6-numeric-class-agrees-with-datum p6-rational-field-views p6-complex-field-views))))

(defund p6-immediate-numeric-sites (name)
  (case name
    (numerator (append (p6-sites "prim:COMMON-LISP::NUMERATOR" 2) (p6-sites "rt:num-type-return" 1)))
    (denominator (append (p6-sites "prim:COMMON-LISP::DENOMINATOR" 2) (p6-literal-sites "rt:one")))
    (realpart (append (p6-sites "prim:COMMON-LISP::REALPART" 2) (p6-sites "rt:num-type-return" 1)))
    (imagpart (append (p6-sites "prim:COMMON-LISP::IMAGPART" 2) (p6-literal-sites "rt:zero")))))

(defthm p6-immediate-numeric-projections-return
  (let* ((word (proof-world-reg 0 world))
         (sites (p6-immediate-numeric-sites name)))
    (implies (and (oddp word) (member-equal name *p6-numeric-projections*)
                  (p6-path-entry-p sites base world))
             (p6-read-only-return-p
              (p6-projected-numeric-word name word (proof-heap-base world) (proof-world-machine world))
              (proof-runtime-clobbers name) t sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-immediate-numeric-sites p6-projected-numeric-word p6-numeric-class
                                                      p6-literal-sites p6-path-entry-p p6-path-end
                                                      p6-read-only-return-p p6-same-mapped-memory-p)
                           (p6-sites-placed-p proof-segment-p))
           :use ((:instance p6-read-only-path-to-cut (sites (p6-immediate-numeric-sites name))
                            (cuts (list (proof-world-reg 30 world))))))))

(defthm p6-immediate-numeric-projections-runtime-contract
  (let* ((word (proof-world-reg 0 world))
         (sites (p6-immediate-numeric-sites name))
         (after (p6-path-end sites world))
         (args (list value)))
    (implies (and (member-equal name *p6-numeric-projections*) (oddp word)
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-path-entry-p sites runtime-base world))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-read-only-return-p proof-reg-value-p boymoo-model::core-primitive)
           :use ((:instance p6-runtime-pre-has-heap-and-first-arg (args (list value)))
                 (:instance p6-numeric-projection-word-agrees-with-core
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance p6-immediate-numeric-projections-return (base runtime-base))
                 (:instance p6-read-only-datum-return
                            (before world) (sites (p6-immediate-numeric-sites name))
                            (word (p6-projected-numeric-word name (proof-world-reg 0 world)
                                                            (proof-heap-base world) (proof-world-machine world)))
                            (value (boymoo-model::core-datum (boymoo-model::core-primitive name (list value) program)))
                            (clobbers (proof-runtime-clobbers name)) (flags t))))))

; These continuations start immediately after the load that restores
; the caller's link. The numeric class and header address are in X3 and X4.
(defund p6-numeric-suffix-fragment (name count)
  (nthcdr 5 (p6-sites (proof-runtime-label name) (+ 5 count))))

(defund p6-numeric-projection-field-offset (name type)
  (case name
    (numerator (and (equal type 4) 8))
    (denominator (and (equal type 4) 16))
    (realpart (and (equal type 5) 8))
    (imagpart (and (equal type 5) 16))))

(defund p6-numeric-suffix-sites (name type)
  (case name
    (numerator (cond ((equal type 3)
                      (append (p6-numeric-suffix-fragment name 2) (p6-sites "rt:num-type-return" 1)))
                     ((equal type 4) (p6-numeric-suffix-fragment name 6))
                     (t (append (p6-numeric-suffix-fragment name 4) (p6-literal-sites "rt:zero")))))
    (denominator (if (equal type 4) (p6-numeric-suffix-fragment name 4)
                   (append (p6-numeric-suffix-fragment name 2) (p6-literal-sites "rt:one"))))
    (realpart (cond ((equal type 0)
                     (append (p6-numeric-suffix-fragment name 1) (p6-literal-sites "rt:zero")))
                    ((equal type 5) (p6-numeric-suffix-fragment name 5))
                    (t (append (p6-numeric-suffix-fragment name 3) (p6-sites "rt:num-type-return" 1)))))
    (imagpart (if (equal type 5) (p6-numeric-suffix-fragment name 4)
                (append (p6-numeric-suffix-fragment name 2) (p6-literal-sites "rt:zero"))))))

(defund p6-numeric-suffix-word (name type world)
  (let ((offset (p6-numeric-projection-field-offset name type)))
    (cond (offset (p6-world-load 8 (+ (proof-world-reg 4 world) offset) world))
          ((or (and (eq name 'numerator) (equal type 3))
               (and (eq name 'realpart) (not (equal type 0))))
           (proof-world-reg 0 world))
          ((eq name 'denominator) 3)
          (t 1))))

(defthm p6-numeric-projection-continuations-return
  (let* ((type (proof-world-reg 3 world))
         (offset (p6-numeric-projection-field-offset name type))
         (sites (p6-numeric-suffix-sites name type)))
    (implies (and (member-equal name *p6-numeric-projections*)
                  (p6-path-entry-p sites base world)
                  (or (not offset)
                      (proof-covered-p (boymoo-model::a64-unsigned 64 (+ (proof-world-reg 4 world) offset))
                                       8 :read (proof-world-regions world))))
             (p6-read-only-return-p (p6-numeric-suffix-word name type world) '(0) t sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-numeric-projection-field-offset p6-numeric-suffix-fragment
                                                             p6-numeric-suffix-sites p6-numeric-suffix-word
                                                             p6-literal-sites p6-path-entry-p p6-path-end
                                                             p6-read-only-return-p p6-same-mapped-memory-p)
                           (p6-sites-placed-p proof-segment-p))
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-numeric-suffix-sites name (proof-world-reg 3 world)))
                            (cuts (list (proof-world-reg 30 world))))))))
