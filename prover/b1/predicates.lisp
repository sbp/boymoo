(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-predicates-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(defun b1-predicates-at (term index)
  (let* ((index (if (eq index t) 1 index))
         (offset (if (and (integerp index) (< index 0))
                     (+ (len term) index)
                   index)))
    (cond ((not (integerp index))
           '(:failure "failure" ""))
          ((< offset 0) '(:failure "failure" ""))
          (t (proof-term-at term offset)))))

(defun b1-predicates-boolean-definition-variable (formals slot)
  (cond ((eq slot t) (b1-predicates-at formals 0))
        ((rationalp slot) (b1-predicates-at formals (1- slot)))
        (t '(:failure "failure" ""))))

(mutual-recursion
 (defun b1-predicates-boolean-definition-boolean-leaves (term head slot variable)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (equal term *proof-true*) (equal term *proof-false*)) t)
         ((proof-is-call term *proof-if*)
          (b1-predicates-boolean-definition-boolean-branches
           (cddr term) head slot variable))
         ((proof-is-call term head)
          (proof-with-checked-results
              ((argument (b1-predicates-at term slot)))
            (equal argument (list *library-cdr* variable))))
         (t nil)))
 (defun b1-predicates-boolean-definition-boolean-branches (branches head slot variable)
   (declare (xargs :measure (acl2-count branches)))
   (if (endp branches)
       t
     (proof-with-checked-results
         ((first (b1-predicates-boolean-definition-boolean-leaves
                  (car branches) head slot variable)))
       (and first
            (b1-predicates-boolean-definition-boolean-branches
             (cdr branches) head slot variable))))))

(defun b1-predicates-boolean-definition-bindings (pairs bindings)
  (if (endp pairs)
      bindings
    (b1-predicates-boolean-definition-bindings
     (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun b1-predicates-boolean-definition-leaf (value tests lib formals induction)
  (if (or (equal value *proof-true*) (equal value *proof-false*))
      (proof-with-checked-results
          ((step (b1-logic-bookproof-normalize-proof
                  lib (list *b1-predicates-booleanp* value) nil
                  (list *b1-predicates-booleanp* *proof-not* (proof-cl "EQ"))
                  nil nil)))
        (cons step induction))
    (b1-induction-tree-induction-hypothesis
     induction
     (b1-predicates-boolean-definition-bindings
      (seq-zip formals (cdr value)) nil)
     tests)))

(defun b1-predicates-boolean-definition-by-value (n lib value template tests formals induction)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "Fuel" "b1-predicates-boolean-definition-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b1-predicates-boolean-definition-by-value
                 (1- n) lib (cadr branches) template
                 (append tests (list (list (car branches) t))) formals induction))
           (no (b1-predicates-boolean-definition-by-value
                (1- n) lib (caddr branches) template
                (append tests (list (list (car branches) nil))) formals (cdr yes)))
           (yes-equality (proof-proof-if-true proof value))
           (yes-reversed (proof-proof-symmetric proof yes-equality))
           (yes-step (proof-proof-rewrite-result
                      proof (car yes) yes-reversed template *proof-result*))
           (no-equality (proof-proof-if-false proof value))
           (no-reversed (proof-proof-symmetric proof no-equality))
           (no-step (proof-proof-rewrite-result
                     proof (car no) no-reversed template *proof-result*))
           (step (proof-proof-cases proof (car branches) yes-step no-step)))
        (cons step (cdr no))))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (first (proof-step-first equality))
           (opened (proof-term-at first 2))
           (result (b1-predicates-boolean-definition-by-value
                    (1- n) lib opened template tests formals induction))
           (reversed (proof-proof-symmetric proof equality))
           (step (proof-proof-rewrite-result
                  proof (car result) reversed template *proof-result*)))
        (cons step (cdr result))))
     (t
      (proof-with-checked-results
          ((result (b1-predicates-boolean-definition-leaf
                    value tests lib formals induction))
           (literal (proof-step-first (car result)))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target)
            result
          '(:failure "failure" "")))))))

(defun b1-predicates-boolean-definition-lemma (lib head tag formals body slot variable)
  (proof-with-checked-results
      ((boolean (b1-predicates-boolean-definition-boolean-leaves
                 body head slot variable)))
    (if (not boolean)
        '(:failure "Unproved" "")
      (let* ((proof (library-library-proof lib))
             (formal-call (cons head formals))
             (template (list *b1-predicates-booleanp* *proof-result*))
             (claim (list *b1-predicates-booleanp* formal-call))
             (induction (b1-induction-tree-induction-init lib claim variable)))
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof formal-call))
             (first (proof-step-first opened))
             (expression (proof-term-at first 2))
             (result (b1-predicates-boolean-definition-by-value
                      1000000 lib expression template nil formals induction))
             (reversed (proof-proof-symmetric proof opened))
             (step (proof-proof-rewrite-result
                    proof (car result) reversed template *proof-result*))
             (finished (if (b1-induction-tree-induction-substitutions (cdr result))
                           (b1-induction-tree-induction-finish (cdr result) step)
                         step)))
          (library-library-lemma lib tag claim finished nil))))))

(defun b1-predicates-boolean-definition (lib call slot)
  (proof-with-checked-results
      ((head (proof-term-at call 0))
       (text (proof-write head)))
    (let* ((tag (concatenate 'string "BOOLEAN-"
                             (text-upper (seq-slice (siphash-hexdigest text) 0 16))))
           (name (proof-sym (concatenate 'string "SELF-" tag) "ACL2"))
           (proof (library-library-proof lib))
           (entry (assoc-equal head (proof-proof-definitions proof))))
      (if (not entry)
          '(:failure "failure" "")
        (proof-with-checked-results
            ((definition (proof-list-of-length (cdr entry) 2))
             (formals (car definition))
             (variable (b1-predicates-boolean-definition-variable formals slot))
             (updated (if (assoc-equal name (proof-proof-facts proof))
                          lib
                        (b1-predicates-boolean-definition-lemma
                         lib head tag formals (cadr definition) slot variable)))
             (step (proof-proof-fact (library-library-proof updated)
                                     name (seq-zip formals (cdr call)))))
          (cons step updated))))))
