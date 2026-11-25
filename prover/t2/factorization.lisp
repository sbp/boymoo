(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)
(logic)

(defun t2-factorization-first (step)
  (if step
      (proof-step-first step)
    '(:failure "failure" "")))

(defun t2-factorization-residual (factorization)
  (proof-with-checked-results
      ((literal (t2-factorization-first factorization))
       (product (proof-term-at literal 2)))
    (proof-term-at product 1)))

(defun t2-factorization-factor-product-proof (lib step part factor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((outer (t2-factorization-residual step))
         (step (proof-proof-rewrite proof step part '(1 2 2)))
         (residual (t2-factorization-residual part))
         (association (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                             (list outer residual factor)))
         (reverse (proof-proof-symmetric proof association))
         (step (proof-proof-chain proof step (list reverse))))
      (cons step lib))))

(defun t2-factorization-factor-summand (lib step part residual factor index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list residual factor)))
         (part (proof-proof-chain proof part (list commuted))))
      (proof-proof-rewrite proof step part (list 1 2 index)))))

(defun t2-factorization-factor-sum-proof (lib expression left right factor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proof-proof-reflexive proof expression))
         (left-residual (t2-factorization-residual left))
         (step (t2-factorization-factor-summand lib step left left-residual factor 1))
         (right-residual (t2-factorization-residual right))
         (step (t2-factorization-factor-summand lib step right right-residual factor 2))
         (distributed (library-library-axiom lib "DISTRIBUTIVITY"
                                              (list factor left-residual right-residual)))
         (reverse (proof-proof-symmetric proof distributed))
         (step (proof-proof-chain proof step (list reverse)))
         (product (proof-rewritten-term step))
         (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (cdr product)))
         (step (proof-proof-chain proof step (list commuted))))
      (cons step lib))))

(defun t2-factorization-factor-right (lib expression factor)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((equal expression *proof-zero*)
    (proof-with-checked-results
        ((zero (t2-products-product-zero lib factor))
         (step (proof-proof-symmetric (library-library-proof (cdr zero)) (car zero))))
      (cons step (cdr zero))))
   ((and (consp expression) (proof-is-call expression *proof-times*))
    (proof-with-checked-results ((args (proof-list-of-length (cdr expression) 2)))
      (let ((left (car args))
            (right (cadr args)))
        (cond
         ((equal right factor)
          (proof-with-checked-results
              ((step (proof-proof-reflexive (library-library-proof lib) expression)))
            (cons step lib)))
         ((equal left factor)
          (proof-with-checked-results
              ((step (library-library-axiom lib "COMMUTATIVITY-OF-*" args)))
            (cons step lib)))
         (t
          (proof-with-checked-results
              ((part (t2-factorization-factor-right lib (caddr expression) factor))
               (lib (cdr part))
               (step (proof-proof-reflexive (library-library-proof lib) expression)))
            (if (car part)
                (t2-factorization-factor-product-proof lib step (car part) factor)
              (proof-with-checked-results
                  ((part (t2-factorization-factor-right lib (cadr expression) factor))
                   (lib (cdr part)))
                (if (car part)
                    (proof-with-checked-results
                        ((step (library-library-axiom lib "COMMUTATIVITY-OF-*" args)))
                      (t2-factorization-factor-product-proof lib step (car part) factor))
                  (cons nil lib))))))))))
   ((and (consp expression) (proof-is-call expression *proof-plus*))
    (cond
     ((endp (cdr expression)) (proof-list-of-length (cdr expression) 2))
     (t
      (proof-with-checked-results
          ((left (t2-factorization-factor-right lib (cadr expression) factor)))
        (if (endp (cddr expression))
            (proof-list-of-length (cdr expression) 2)
          (proof-with-checked-results
              ((right (t2-factorization-factor-right (cdr left) (caddr expression) factor)))
            (cond
             ((consp (cdddr expression))
              (let ((extra (t2-factorization-factor-right
                            (cdr right) (cadddr expression) factor)))
                (if (failure-p extra)
                    extra
                  (proof-list-of-length (cdr expression) 2))))
             ((and (car left) (car right))
              (t2-factorization-factor-sum-proof (cdr right) expression
                                                 (car left) (car right) factor))
             (t (cons nil (cdr right))))))))))
   (t (cons nil lib))))

(mutual-recursion
 (defun t2-factorization-align (lib actual expected)
   (declare (xargs :measure (1+ (* 2 (acl2-count actual)))))
   (let ((proof (library-library-proof lib)))
     (if (equal actual expected)
         (proof-proof-reflexive proof actual)
       (let ((operator (t2-book-logic-head actual)))
         (cond
          ((or (not (equal operator (t2-book-logic-head expected)))
               (equal operator *proof-quote*))
           nil)
          ((member-equal operator (list *proof-plus* *proof-times*))
           (t2-book-logic-ac-equal lib actual expected))
          ((member-equal operator (list *proof-equal* *proof-less* *proof-if*))
           (proof-with-checked-results ((step (proof-proof-reflexive proof actual)))
             (t2-factorization-align-arguments lib (cdr actual) (cdr expected) 1 step)))
          (t nil))))))

 (defun t2-factorization-align-arguments (lib actuals expecteds position step)
   (declare (xargs :measure (* 2 (acl2-count actuals))))
   (cond
    ((or (endp actuals) (endp expecteds)) step)
    ((equal (car actuals) (car expecteds))
     (t2-factorization-align-arguments lib (cdr actuals) (cdr expecteds)
                                       (1+ position) step))
    (t
     (proof-with-checked-results
         ((alignment (t2-factorization-align lib (car actuals) (car expecteds))))
       (if alignment
           (proof-with-checked-results
               ((step (proof-proof-rewrite (library-library-proof lib) step alignment
                                           (list 1 2 position))))
             (t2-factorization-align-arguments lib (cdr actuals) (cdr expecteds)
                                               (1+ position) step))
         nil))))))

(defun t2-factorization-candidate (premise facts comparison)
  (proof-with-checked-results ((literal (t2-factorization-first premise)))
    (if (not (proof-is-call literal *proof-not*))
        (cons nil facts)
      (proof-with-checked-results ((equality (proof-term-at literal 1)))
        (if (not (proof-is-call equality *proof-equal*))
            (cons nil facts)
          (proof-with-checked-results ((args (proof-list-of-length (cdr equality) 2)))
            (let* ((swapped (equal (car args) *proof-zero*))
                   (left (if swapped (cadr args) (car args)))
                   (right (if swapped (car args) (cadr args))))
              (cond
               ((not (equal right *proof-zero*)) (cons nil facts))
               ((equal comparison *proof-less*)
                (proof-with-checked-results
                    ((query (t2-tactics-ruler-facts-find facts (list *library-rationalp* left)))
                     (facts (cdr query)))
                  (if (not (car query))
                      (cons nil facts)
                    (proof-with-checked-results
                        ((different
                          (if (equal literal (proof-neg (proof-eq left *proof-zero*)))
                              premise
                            (t2-products-flip-neq
                             (library-library-init
                              (descent-proof (t2-tactics-ruler-facts-proof facts)))
                             premise))))
                      (cons (list left different) facts)))))
               ((and (equal comparison *proof-equal*) (proof-is-call left *t2-book-logic-fix*))
                (proof-with-checked-results ((factor (proof-term-at left 1)))
                  (cons (list factor premise) facts)))
               (t (cons nil facts))))))))))

(defun t2-factorization-coefficients (parts)
  (if (endp parts)
      nil
    (proof-with-checked-results
        ((first (t2-factorization-residual (car parts)))
         (rest (t2-factorization-coefficients (cdr parts))))
      (cons first rest))))

(defmacro t2-factorization-shorter-tail-p (items)
  `(and (consp ,items)
        (o< (len (cdr ,items)) (len ,items))))

(defun t2-factorization-commute-parts (lib pairs factor)
  (declare (xargs :measure (len pairs)))
  (if (not (t2-factorization-shorter-tail-p pairs))
      nil
    (proof-with-checked-results
        ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-*"
                                          (list (cadar pairs) factor)))
         (part (proof-proof-chain (library-library-proof lib) (caar pairs) (list commuted)))
         (rest (t2-factorization-commute-parts lib (cdr pairs) factor)))
      (cons part rest))))

(defun t2-factorization-rewrite-parts (proof equation parts position)
  (declare (xargs :measure (len parts)))
  (if (not (t2-factorization-shorter-tail-p parts))
      equation
    (proof-with-checked-results
        ((reverse (proof-proof-symmetric proof (car parts)))
         (equation (proof-proof-rewrite proof equation reverse (list 1 1 position))))
      (t2-factorization-rewrite-parts proof equation (cdr parts) (1+ position)))))

(defun t2-factorization-fix-coefficients (lib equation coefficients position)
  (declare (xargs :measure (len coefficients)))
  (if (not (t2-factorization-shorter-tail-p coefficients))
      equation
    (let ((coefficient (car coefficients)))
      (proof-with-checked-results
          ((equation
            (if (member-equal (t2-book-logic-head coefficient)
                              (list *proof-plus* *proof-times*))
                (proof-with-checked-results
                    ((numeric (t2-field-number lib coefficient))
                     (fix (t2-field-numeric-fix lib coefficient numeric)))
                  (proof-proof-rewrite (library-library-proof lib) equation fix
                                       (list 1 2 position)))
              equation)))
        (t2-factorization-fix-coefficients lib equation (cdr coefficients) (1+ position))))))

(defun t2-factorization-signed-order (lib arguments rational different)
  (let ((evidence (cond ((not rational) nil)
                        ((not different) (list rational))
                        (t (list rational different)))))
    (proof-with-checked-results
        ((equation (library-library-cite lib "RATIONAL-SIGNED-ORDER" arguments evidence)))
      (if (and rational different)
          equation
        (t2-factorization-first nil)))))

(defun t2-factorization-comparison-equation (lib comparison factor parts different facts)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((coefficients (t2-factorization-coefficients parts)))
      (let ((arguments (append coefficients (list factor))))
        (if (equal comparison *proof-equal*)
            (proof-with-checked-results
                ((equation (library-library-cite lib "FIELD-RIGHT-CANCELLATION" arguments nil))
                 (body (proof-rewritten-term equation))
                 (test (proof-term-at body 1))
                 (literal (t2-factorization-first different))
                 (different (if (equal literal (proof-neg test))
                                different
                              (t2-products-flip-neq lib different)))
                 (selected (proof-proof-select proof body different))
                 (equation (proof-proof-chain proof equation (list selected)))
                 (equation (t2-factorization-fix-coefficients lib equation coefficients 1))
                 (equation (t2-factorization-rewrite-parts proof equation parts 1)))
              (cons equation facts))
          (proof-with-checked-results
              ((rational (t2-tactics-ruler-facts-find facts (list *library-rationalp* factor)))
               (equation (t2-factorization-signed-order lib arguments (car rational) different))
               (parts (t2-factorization-commute-parts lib (seq-zip parts coefficients) factor))
               (equation (t2-factorization-rewrite-parts proof equation parts 1)))
            (cons equation (cdr rational))))))))

(defun t2-factorization-arithmetic-operand-p (operands)
  (and (consp operands)
       (or (member-equal (t2-book-logic-head (car operands)) (list *proof-plus* *proof-times*))
           (t2-factorization-arithmetic-operand-p (cdr operands)))))

(defun t2-factorization-factor-operands (lib operands factor)
  (declare (xargs :measure (len operands)))
  (if (not (t2-factorization-shorter-tail-p operands))
      (cons nil lib)
    (proof-with-checked-results
        ((first (t2-factorization-factor-right lib (car operands) factor))
         (rest (t2-factorization-factor-operands (cdr first) (cdr operands) factor)))
      (cons (cons (car first) (car rest)) (cdr rest)))))

(defun t2-factorization-try-candidate (lib candidate operator operands expected facts condition)
  (let ((factor (car candidate))
        (different (cadr candidate)))
    (proof-with-checked-results
        ((parts (t2-factorization-factor-operands lib operands factor))
         (lib (cdr parts))
         (facts (t2-tactics-ruler-facts-with-proof facts lib)))
      (if (member-equal nil (car parts))
          (list nil lib facts)
        (proof-with-checked-results
            ((equation (t2-factorization-comparison-equation
                        lib operator factor (car parts) different facts))
             (facts (cdr equation))
             (equation (car equation))
             (body (proof-rewritten-term equation))
             (aligned (t2-factorization-align lib body expected)))
          (if (not aligned)
              (list nil lib facts)
            (proof-with-checked-results
                ((step (proof-proof-chain (library-library-proof lib) equation (list aligned)))
                 (step (t2-power-implication lib condition step)))
              (list step lib facts))))))))

(defun t2-factorization-prove-candidates (lib premises operator operands expected facts condition)
  (declare (xargs :measure (len premises)))
  (if (not (t2-factorization-shorter-tail-p premises))
      (cons nil lib)
    (proof-with-checked-results ((candidate (t2-factorization-candidate (car premises) facts operator)))
      (if (not (car candidate))
          (t2-factorization-prove-candidates lib (cdr premises) operator operands expected
                                             (cdr candidate) condition)
        (proof-with-checked-results
            ((result (t2-factorization-try-candidate lib (car candidate) operator operands expected
                                                     (cdr candidate) condition)))
          (if (car result)
              (cons (car result) (cadr result))
            (t2-factorization-prove-candidates (cadr result) (cdr premises) operator operands
                                               expected (caddr result) condition)))))))

(defun t2-factorization-prove (lib formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil lib)
    (proof-with-checked-results ((claim (proof-term-at formula 2)))
      (if (not (proof-is-call claim *proof-equal*))
          (cons nil lib)
        (proof-with-checked-results
            ((args (proof-list-of-length (cdr formula) 2))
             (equality (proof-list-of-length (cdr claim) 2)))
          (let* ((condition (car args))
                 (comparison (car equality))
                 (expected (cadr equality))
                 (operator (t2-book-logic-head comparison)))
            (if (and (member-equal operator (list *proof-equal* *proof-less*))
                     (member-equal (t2-book-logic-head expected) (list *proof-equal* *proof-if*))
                     (t2-factorization-arithmetic-operand-p (cdr comparison)))
                (proof-with-checked-results
                    ((facts (t2-tactics-ruler-facts-init lib (list (list condition t)) nil))
                     (premises (t2-tactics-ruler-facts-premises facts)))
                  (t2-factorization-prove-candidates lib (car premises) operator (cdr comparison)
                                                     expected (cdr premises) condition))
              (cons nil lib))))))))
