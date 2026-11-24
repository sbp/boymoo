(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-witnesses-synp* (proof-sym "SYNP" "ACL2"))

(defun b2-witnesses-non-interpretation (name formulas)
  (proof-with-checked-results ((formula (proof-term-at (car formulas) 1)))
    (if (not (proof-is-call formula *b2-tactics-iff*)) nil
      (proof-with-checked-results ((left (proof-term-at formula 1)))
        (if (equal left (list name *library-x*))
            (proof-with-checked-results ((right (proof-term-at formula 2)))
              (list (list *library-x*) right))
          nil)))))

(defun b2-witnesses-interpretation (name index formulas)
  (proof-with-checked-results ((stem (proof-term-at name 2)))
    (if (text-ends-with stem "-FINAL-CDR-P")
        (list (list *library-x*) (proof-eq *library-x* *proof-false*))
      (proof-with-checked-results
          ((non-interpretation (and (equal (len formulas) 1) (text-starts-with stem "NON-")
                                    (b2-witnesses-non-interpretation name formulas))))
        (cond
         (non-interpretation non-interpretation)
         ((equal name (proof-sym "ELEMENT-FIX" "ACL2"))
          (list (list *library-x*)
                (proof-ite (list (proof-sym "ELEMENT-P" "ACL2") *library-x*)
                           *library-x* (list (proof-sym "ELEMENT-EXAMPLE" "ACL2")))))
         ((equal name (proof-sym "OUTELEMENT-P" "ACL2"))
          (list (list *library-x*) *proof-true*))
         ((and (equal name (proof-sym "COMPARE<" "ACL2")) (equal index 1))
          (list (list *library-x* *library-y*) *proof-false*))
         ((equal name (proof-sym "ELEMENT-XFORMER" "ACL2"))
          (list (list *library-x*) (list (proof-sym "OUTELEMENT-EXAMPLE" "ACL2"))))
         (t (list :none *proof-false*)))))))

(defun b2-witnesses-default-formals (indices)
  (if (endp indices) nil
    (cons (proof-sym (concatenate 'string "ARG-" (decimal-text (car indices))) "ACL2")
          (b2-witnesses-default-formals (cdr indices)))))

(defun b2-witnesses-witness-name (name)
  (proof-with-checked-results
      ((package (proof-term-at name 1))
       (suffix (if (equal package "ACL2") (proof-term-at name 2) (text-join "-" (cdr name)))))
    (proof-sym (concatenate 'string "B2-WITNESS-" suffix) "ACL2")))

(defun b2-witnesses-witness-formals (formals arity)
  (if (eq formals :none)
      (if (not (integerp arity))
          '(:failure "failure" "")
        (b2-witnesses-default-formals (seq-range 1 (1+ arity) 1)))
    formals))

(defun b2-witnesses-define (functions lib index formulas names)
  (if (endp functions) (cons (reverse names) lib)
    (proof-with-checked-results
        ((declaration (proof-list-of-length (car functions) 2))
         (name (car declaration))
         (arity (cadr declaration))
         (witness (b2-witnesses-witness-name name))
         (interpretation (b2-witnesses-interpretation name index formulas))
         (formals (b2-witnesses-witness-formals (car interpretation) arity)))
      (if (not (equal (len formals) arity))
          (b2-tactics-unproved)
        (proof-with-checked-results
            ((lib (library-library-definition lib witness (or formals *proof-nil*) (cadr interpretation))))
          (b2-witnesses-define (cdr functions) lib (1+ index) formulas (cons witness names)))))))

(defun b2-witnesses-renaming (functions names renamed)
  (if (endp functions) renamed
    (b2-witnesses-renaming (cdr functions) (cdr names)
                           (table-put renamed (caar functions) (car names)))))

(defun b2-witnesses-goals (formulas renamed)
  (if (endp formulas) nil
    (proof-with-checked-results
        ((parts (proof-list-of-length (car formulas) 2))
         (goal (b2-tactics-rename-calls (cadr parts) renamed))
         (rest (b2-witnesses-goals (cdr formulas) renamed)))
      (cons goal rest))))

(defun b2-witnesses-find-witnesses-solve (goal evidence lib names)
  (let ((unfold (append names (list *b2-witnesses-synp*))))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize lib goal evidence unfold nil 1500 t))
         (target (if equation
                     (proof-with-checked-results ((first (proof-step-first equation)))
                       (proof-term-at first 2))
                   goal))
         (search (b2-search-search-init lib 25 nil))
         (step (car (b2-search-search-prove search target evidence 2 3))))
      (if equation (proof-proof-transport (library-library-proof lib) step equation) step))))

(defun b2-witnesses-prove-implication (lib goal names)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (premise (cadr parts))
       (claim (caddr parts))
       (request (b2-tactics-tactics-implication lib premise claim nil))
       (callback (car request))
       (callback-lib (caddr callback))
       (step (b2-witnesses-find-witnesses-solve claim (list (cadddr callback)) callback-lib names))
       (result (b2-tactics-tactics-implication lib premise claim (cons step callback-lib))))
    (car result)))

(defun b2-witnesses-find-witnesses-prove (goal lib names)
  (let* ((unfold (append names (list *b2-witnesses-synp*)))
         (step (b2-tactics-tactics-solve lib goal nil unfold nil 0 t)))
    (if (b2-tactics-unproved-p step)
        (if (proof-is-call goal *library-implies*)
            (b2-witnesses-prove-implication lib goal names)
          (b2-witnesses-find-witnesses-solve goal nil lib names))
      step)))

(defun b2-witnesses-prove-goals (goals lib names)
  (if (endp goals) nil
    (proof-with-checked-results
        ((step (b2-witnesses-find-witnesses-prove (car goals) lib names))
         (rest (b2-witnesses-prove-goals (cdr goals) lib names)))
      (cons step rest))))

(defun b2-witnesses-find-witnesses (lib functions formulas)
  (proof-with-checked-results
      ((result (b2-witnesses-define functions lib 0 formulas nil))
       (names (car result))
       (lib (cdr result))
       (renamed (b2-witnesses-renaming functions names nil))
       (goals (b2-witnesses-goals formulas renamed))
       (proofs (b2-witnesses-prove-goals goals lib names))
       (declaration (proof-term-at functions 0))
       (name (proof-term-at declaration 0))
       (entry (proof-proof-entry "witness" name (cons name names) proofs)))
    (cons entry lib)))
