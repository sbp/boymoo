(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(defun proof-number-code-at-label (name code)
  (cond ((endp code) nil)
        ((equal (car code) (list :label name)) code)
        (t (proof-number-code-at-label name (cdr code)))))

; The formula prologue uses STR for one argument and STP for two.
; Each subsequent BL consumes the fields of the LDR items before it.
(defun proof-number-read-calls (body reverse-slots)
  (if (endp body)
      nil
    (case (caar body)
      (:ldr (proof-number-read-calls
             (cdr body) (cons (/ (cadddr (car body)) 8) reverse-slots)))
      (:bl (cons (cons (cadar body) (reverse reverse-slots))
                 (proof-number-read-calls (cdr body) nil)))
      (otherwise (proof-number-read-calls (cdr body) reverse-slots)))))

(defun proof-number-read-formula (name body)
  (list name (if (eq (car (nth 4 body)) :str) 1 2)
        (proof-number-read-calls (nthcdr 6 body) nil)))

(defun proof-number-read-formulas (code name reverse-body)
  (cond ((endp code)
         (if name (list (proof-number-read-formula name (reverse reverse-body))) nil))
        ((eq (caar code) :label)
         (let ((tail (proof-number-read-formulas (cdr code) (cadar code) nil)))
           (if name
               (cons (proof-number-read-formula name (reverse reverse-body)) tail)
             tail)))
        (t (proof-number-read-formulas (cdr code) name (cons (car code) reverse-body)))))

(defconst *proof-number-formula-code*
  (proof-number-code-at-label "rt:q-reduce" (boymoo-compiler::runtime-rational-code)))

(defconst *proof-number-formulas*
  (proof-number-read-formulas *proof-number-formula-code* nil nil))

(defthm proof-number-formulas-describe-runtime-code
  (equal (boymoo-compiler::runtime-number-formulas *proof-number-formulas*)
         *proof-number-formula-code*)
  :rule-classes nil)

(defun proof-number-formula-arity (name)
  (cadr (assoc-equal name *proof-number-formulas*)))

(defun proof-number-formula-calls (name)
  (caddr (assoc-equal name *proof-number-formulas*)))

(defun proof-number-slot-indices-p (indices size)
  (if (atom indices)
      (null indices)
    (and (natp (car indices))
         (< (car indices) size)
         (proof-number-slot-indices-p (cdr indices) size))))

(defun proof-number-call-slots-p (calls size)
  (if (atom calls)
      (null calls)
    (and (consp (car calls))
         (stringp (caar calls))
         (proof-number-slot-indices-p (cdar calls) size)
         (proof-number-call-slots-p (cdr calls) (1+ size)))))

(defun proof-number-formula-table-p (formulas)
  (if (atom formulas)
      (null formulas)
    (let ((arity (cadar formulas))
          (calls (caddar formulas)))
      (and (member-equal arity '(1 2))
           (consp calls)
           (proof-number-call-slots-p calls arity)
           (proof-number-formula-table-p (cdr formulas))))))

(defthm proof-number-generated-formulas-use-initialized-slots
  (proof-number-formula-table-p *proof-number-formulas*)
  :rule-classes nil)

(defun proof-number-slot-arguments (indices slots)
  (if (endp indices)
      nil
    (cons (nth (car indices) slots)
          (proof-number-slot-arguments (cdr indices) slots))))

(defconst *proof-number-formula-primitives*
  (list (cons (proof-runtime-label 'numerator) 'numerator)
        (cons (proof-runtime-label 'denominator) 'denominator)
        (cons (proof-runtime-label 'realpart) 'realpart)
        (cons (proof-runtime-label 'imagpart) 'imagpart)
        (cons (proof-runtime-label 'acl2::binary-+) 'acl2::binary-+)
        (cons (proof-runtime-label 'acl2::binary-*) 'acl2::binary-*)
        (cons (proof-runtime-label 'acl2::unary--) 'acl2::unary--)
        (cons (proof-runtime-label 'acl2::unary-/) 'acl2::unary-/)))

(defund proof-number-call-domain-p (target args gcd)
  (let ((a (car args))
        (b (cadr args))
        (primitive (cdr (assoc-equal target *proof-number-formula-primitives*))))
    (cond ((member-eq primitive '(numerator denominator)) (rationalp a))
          ((member-eq primitive '(realpart imagpart acl2::unary-- acl2::unary-/))
           (acl2-numberp a))
          ((member-eq primitive '(acl2::binary-+ acl2::binary-*))
           (and (acl2-numberp a) (acl2-numberp b)))
          ((equal target "rt:z-gcd") (and (posp b) (proof-gcd-p a b gcd)))
          ((equal target "rt:z-quotient") (proof-exact-quotient-p a b (/ a b)))
          ((equal target "rt:q-normalize") (and (integerp a) (posp b)))
          ((member-equal target '("rt:q-box" "rt:q-invert-parts"))
           (proof-number-reduced-p a b))
          ((member-equal target '("rt:c-box" "rt:q-compare"))
           (and (rationalp a) (rationalp b)))
          ((equal target "rt:z-compare") (and (integerp a) (integerp b)))
          ((equal target "rt:num-first-order")
           (and (member-equal a '(-1 0 1)) (member-equal b '(-1 0 1))))
          (t nil))))

(defund proof-number-call-value (target args gcd)
  (let ((a (car args))
        (b (cadr args))
        (primitive (cdr (assoc-equal target *proof-number-formula-primitives*))))
    (cond (primitive
           (boymoo-model::core-datum (boymoo-model::core-primitive primitive args nil)))
          ((equal target "rt:z-gcd") gcd)
          ((member-equal target '("rt:z-quotient" "rt:q-normalize" "rt:q-box")) (/ a b))
          ((equal target "rt:q-invert-parts") (/ (/ a b)))
          ((member-equal target '("rt:z-compare" "rt:q-compare")) (proof-number-order a b))
          ((equal target "rt:c-box") (complex a b))
          ((equal target "rt:num-first-order") (proof-number-first-order a b))
          (t nil))))

; Values are added at the end, so the index of each earlier value is fixed.
(defun proof-number-evaluate-calls (calls slots gcd)
  (if (endp calls)
      (mv t slots)
    (let* ((target (caar calls))
           (args (proof-number-slot-arguments (cdar calls) slots))
           (value (proof-number-call-value target args gcd)))
      (mv-let (valid final-slots)
        (proof-number-evaluate-calls (cdr calls) (append slots (list value)) gcd)
        (mv (and (proof-number-call-domain-p target args gcd) valid)
            final-slots)))))

(defun proof-number-formula-result-p (name args gcd result)
  (and (true-listp args)
       (equal (len args) (proof-number-formula-arity name))
       (let ((calls (proof-number-formula-calls name)))
         (and (consp calls)
              (mv-let (valid slots)
                (proof-number-evaluate-calls calls args gcd)
                (and valid (equal (car (last slots)) result)))))))

(local (in-theory (enable proof-number-call-domain-p proof-number-call-value
                          boymoo-model::core-primitive)))

(defthm proof-number-q-reduce-formula
  (implies (and (posp b) (proof-gcd-p a b gcd))
           (proof-number-formula-result-p "rt:q-reduce" (list a b) gcd (/ a b)))
  :hints (("Goal"
           :use ((:instance proof-number-gcd-of-positive-denominator (g gcd))
                 (:instance proof-number-gcd-numerator (g gcd))
                 (:instance proof-number-exact-quotient-value
                            (b gcd) (q (numerator (/ a b))))
                 (:instance proof-number-exact-quotient-value
                            (a b) (b gcd) (q (denominator (/ a b))))
                 (:instance proof-number-reduction (g gcd) (n (/ a gcd)) (d (/ b gcd))))))
  :rule-classes nil)

(defthm proof-number-q-add-formula
  (implies (and (rationalp x) (rationalp y))
           (proof-number-formula-result-p "rt:q-add" (list x y) gcd (+ x y)))
  :hints (("Goal"
           :use ((:instance proof-number-rational-sum
                            (a (numerator x)) (b (denominator x))
                            (c (numerator y)) (d (denominator y)))
                 (:instance acl2::positive
                            (acl2::x (denominator x)) (acl2::y (denominator y))))))
  :rule-classes nil)

(defthm proof-number-q-multiply-formula
  (implies (and (rationalp x) (rationalp y))
           (proof-number-formula-result-p "rt:q-multiply" (list x y) gcd (* x y)))
  :hints (("Goal"
           :use ((:instance proof-number-rational-product
                            (a (numerator x)) (b (denominator x))
                            (c (numerator y)) (d (denominator y)))
                 (:instance acl2::positive
                            (acl2::x (denominator x)) (acl2::y (denominator y))))
           :in-theory (disable acl2::associativity-of-*)))
  :rule-classes nil)

(defthm proof-number-q-negate-formula
  (implies (rationalp x)
           (proof-number-formula-result-p "rt:q-negate" (list x) gcd (- x)))
  :hints (("Goal"
           :use ((:instance proof-number-negated-parts-are-reduced
                            (a (numerator x)) (b (denominator x)))
                 (:instance proof-number-quotient-of-negated-numerator
                            (a (numerator x)) (b (denominator x))))))
  :rule-classes nil)

(defthm proof-number-q-reciprocal-formula
  (implies (rationalp x)
           (proof-number-formula-result-p "rt:q-reciprocal" (list x) gcd (/ x)))
  :rule-classes nil)

(defthm proof-number-q-invert-negative-formula
  (implies (and (proof-number-reduced-p a b) (< a 0))
           (proof-number-formula-result-p "rt:q-invert-negative"
                                          (list a b) gcd (/ (/ a b))))
  :hints (("Goal"
           :use (proof-number-inverted-parts-are-reduced
                 proof-number-reciprocal-from-negative-parts)
           :in-theory (enable proof-number-reduced-p)))
  :rule-classes nil)

(defthm proof-number-q-compare-products-formula
  (implies (and (rationalp x) (rationalp y))
           (proof-number-formula-result-p "rt:q-compare-products" (list x y)
                                          gcd (proof-number-order x y)))
  :hints (("Goal" :use proof-number-rational-cross-order))
  :rule-classes nil)

(defthm proof-number-c-add-formula
  (implies (and (acl2-numberp x) (acl2-numberp y))
           (proof-number-formula-result-p "rt:c-add" (list x y) gcd (+ x y)))
  :hints (("Goal" :use ((:instance acl2::add-def-complex (acl2::x x) (acl2::y y)))))
  :rule-classes nil)

(defthm proof-number-c-multiply-formula
  (implies (and (acl2-numberp x) (acl2-numberp y))
           (proof-number-formula-result-p "rt:c-multiply" (list x y) gcd (* x y)))
  :hints (("Goal" :use proof-number-complex-product))
  :rule-classes nil)

(defthm proof-number-c-negate-formula
  (implies (acl2-numberp x)
           (proof-number-formula-result-p "rt:c-negate" (list x) gcd (- x)))
  :hints (("Goal" :use proof-number-complex-negation))
  :rule-classes nil)

(defthm proof-number-c-reciprocal-formula
  (implies (acl2-numberp x)
           (proof-number-formula-result-p "rt:c-reciprocal" (list x) gcd (/ x)))
  :hints (("Goal" :use proof-number-complex-reciprocal))
  :rule-classes nil)

(defthm proof-number-c-compare-formula
  (implies (and (acl2-numberp x) (acl2-numberp y))
           (proof-number-formula-result-p "rt:c-compare" (list x y)
                                          gcd (proof-number-order x y)))
  :hints (("Goal" :use proof-number-order-lexicographic
                  :in-theory (enable proof-number-order proof-number-first-order)))
  :rule-classes nil)
