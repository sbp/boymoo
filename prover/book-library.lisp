(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *book-library-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(defconst *book-library-boolean-axioms*
  (list (cons (proof-cl "CONSP") "booleanp-consp")
        (cons (proof-cl "INTEGERP") "booleanp-integerp")
        (cons (proof-cl "RATIONALP") "booleanp-rationalp")
        (cons (proof-cl "STRINGP") "booleanp-stringp")
        (cons (proof-cl "SYMBOLP") "booleanp-symbolp")
        (cons (proof-cl "<") "booleanp-<")
        (cons (proof-cl "CHARACTERP") (proof-sym "BOOLEANP-CHARACTERP" "ACL2"))
        (cons (proof-sym "ACL2-NUMBERP" "ACL2") "booleanp-acl2-numberp")
        (cons (proof-sym "COMPLEX-RATIONALP" "ACL2") "booleanp-complex-rationalp")))

(defun book-library-cons-value (head tail)
  (proof-constant-cons-value head tail))

(defun book-library-book-library-init (proof)
  (library-library-init (proof-proof-with-kind proof :book)))

(defun book-library-book-library-constant (lib term)
  (proof-proof-constant (proof-proof-with-kind (library-library-proof lib) :book) term))

(defun book-library-book-library-boolean-constant (lib value)
  (proof-proof-prove (library-library-proof lib) (list *book-library-booleanp* value)
                     nil (list *book-library-booleanp* (proof-cl "EQ"))))

(defun book-library-boolean-task (lib term)
  (let ((proof (library-library-proof lib))
        (head (car term)))
    (cond
     ((member-equal term (list *proof-true* *proof-false*))
      (list :return (book-library-book-library-boolean-constant lib term)))
     ((not (proof-compound term)) (list :return nil))
     ((endp term) '(:failure "failure" ""))
     ((assoc-equal head *book-library-boolean-axioms*)
      (list :return
            (proof-proof-fact proof (cdr (assoc-equal head *book-library-boolean-axioms*))
                              (seq-zip (list *library-x* *library-y*) (cdr term)))))
     ((proof-is-call term *proof-equal*)
      (list :return (library-library-cite lib "BOOLEAN-EQUALITY" (cdr term) nil)))
     ((proof-is-call term *proof-if*)
      (list :if term))
     ((member-equal head (list *proof-not* *book-library-booleanp* (proof-cl "EQ") (proof-cl "EQL")
                              (proof-sym "IFF" "ACL2") (proof-sym "IMPLIES" "ACL2")))
      (proof-with-checked-results
       ((opened (proof-proof-unfold proof term))
        (first (proof-step-first opened))
        (value (proof-term-at first 2)))
       (list :unfolded opened value)))
     (t (list :return nil)))))

(defun book-library-boolean-if (lib term yes no)
  (if (not (and yes no))
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
       ((if-true (proof-proof-if-true proof term))
        (yes-proof (library-library-transport-argument lib yes if-true 1))
        (if-false (proof-proof-if-false proof term))
        (no-proof (library-library-transport-argument lib no if-false 1)))
       (proof-proof-cases proof (cadr term) yes-proof no-proof)))))

(mutual-recursion
 (defun book-library-book-library-boolean-loop (n lib term)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "book-library-book-library-boolean-loop")
     (book-library-boolean-run (1- n) lib (book-library-boolean-task lib term))))

 (defun book-library-boolean-run (n lib task)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "book-library-boolean-run"))
    ((failure-p task) task)
    ((eq (car task) :return) (cadr task))
    ((eq (car task) :if)
     (let ((term (cadr task)))
       (proof-with-checked-results
        ((yes (if (consp (cddr term)) (book-library-book-library-boolean-loop (1- n) lib (caddr term)) nil))
         (no (if (consp (cdddr term)) (book-library-book-library-boolean-loop (1- n) lib (cadddr term)) nil)))
        (cond
         ((< (len term) 4)
          *terms-invalid-proof-arity*)
         ((consp (cddddr term))
          (proof-with-checked-results
           ((third (book-library-book-library-boolean-loop (1- n) lib (car (cddddr term)))))
           *terms-invalid-proof-arity*))
         (t (book-library-boolean-if lib term yes no))))))
    (t
     (proof-with-checked-results
      ((boolean (book-library-book-library-boolean-loop (1- n) lib (caddr task))))
      (if boolean
          (library-library-transport-argument lib boolean (cadr task) 1)
        '(:failure "failure" "")))))))

(defun book-library-book-library-boolean (lib term)
  (book-library-book-library-boolean-loop 1000000 lib term))

(defun book-library-book-library-false-value (lib term premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((either (proof-proof-nil-or-true proof term))
      (true (proof-proof-front proof either term)))
     (proof-proof-cut proof true premise))))

(defun book-library-boolean-equality-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (equal-term (proof-eq *library-x* *library-y*)))
    (proof-with-checked-results
     ((truth (proof-proof-assume proof equal-term t))
      (same (proof-proof-fact proof "equal-same" nil))
      (same (proof-proof-rewrite proof same truth '(1 1 2)))
      (different (proof-proof-fact proof "equal-different" nil))
      (different (proof-proof-front proof different (proof-eq equal-term *proof-false*)))
      (true (book-library-book-library-boolean-constant lib *proof-true*))
      (yes (library-library-transport-argument lib true same 1))
      (false (book-library-book-library-boolean-constant lib *proof-false*))
      (no (library-library-transport-argument lib false different 1))
      (cases (proof-proof-cases proof equal-term yes no)))
     (library-library-lemma lib "BOOLEAN-EQUALITY" (list *book-library-booleanp* equal-term) cases nil))))

(defun book-library-boolean-true-value-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (predicate (list *book-library-booleanp* *library-x*))
         (test (proof-eq *library-x* *proof-true*)))
    (proof-with-checked-results
     ((boolean (proof-proof-assume proof predicate t))
      (unfolded (proof-proof-simplify proof predicate nil (list *book-library-booleanp* (proof-cl "EQ"))))
      (is-nil (proof-proof-rewrite proof boolean unfolded '(1)))
      (unfolded-first (proof-step-first unfolded))
      (if-false (proof-proof-if-false proof (caddr unfolded-first)))
      (is-nil (proof-proof-rewrite proof is-nil if-false '(1)))
      (is-nil (proof-proof-tidy proof is-nil))
      (is-nil-first (proof-step-first is-nil))
      (open-nil (proof-proof-unfold proof is-nil-first))
      (is-nil (proof-proof-rewrite proof is-nil open-nil '(1)))
      (is-nil (proof-proof-tidy proof is-nil))
      (not-nil (proof-proof-not-nil proof))
      (symmetric (proof-proof-symmetric proof is-nil))
      (not-x (proof-proof-rewrite proof not-nil symmetric '(1 1)))
      (not-x (proof-proof-tidy proof not-x))
      (assume-x (proof-proof-assume proof *library-x* t))
      (true (proof-proof-cut proof assume-x not-x))
      (step (proof-proof-front proof true test)))
     (library-library-lemma lib "BOOLEAN-TRUE-VALUE" test step
                            (list (proof-neg predicate) (proof-neg *library-x*))))))

(defun book-library-book-library-build (lib)
  (proof-with-checked-results ((lib (library-library-with-proof lib (proof-proof-with-kind (library-library-proof lib) :book)))
                (lib (lemmas-slice-library-build lib))
                (lib (book-library-boolean-equality-lemma lib)))
   (book-library-boolean-true-value-lemma lib)))
