(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-induction-tree-induction-init (lib formula variable)
  (list :b1-tree-induction lib formula variable (list *library-count* variable) nil))

(defun b1-induction-tree-induction-substitutions (induction)
  (nth 5 induction))

(defun b1-induction-tree-induction-with-lib (induction lib)
  (list* :b1-tree-induction lib (cddr induction)))

(defun b1-induction-changed-bindings (bindings)
  (if (endp bindings)
      nil
    (let ((variable (caar bindings))
          (term (cdar bindings))
          (rest (b1-induction-changed-bindings (cdr bindings))))
      (if (equal variable term)
          rest
        (cons (list variable term) rest)))))

(defun b1-induction-tree-induction-hypothesis (induction bindings tests)
  (let* ((pairs (b1-induction-changed-bindings bindings))
         (substitutions (b1-induction-tree-induction-substitutions induction))
         (lib (cadr induction))
         (proof (library-library-proof lib))
         (formula (caddr induction))
         (variable (cadddr induction))
         (measure (nth 4 induction))
         (substitutions (if (member-equal pairs substitutions)
                            substitutions
                          (append substitutions (list pairs)))))
    (proof-with-checked-results
        ((child (proof-subst measure bindings)))
      (let ((goal (list *proof-ordinal-less* child measure)))
        (proof-with-checked-results
            ((rulers (b1-measures-rulers-init lib tests nil))
             (descent (b1-measures-count-descent lib goal rulers))
             (claim (proof-subst formula bindings))
             (assumed (proof-proof-assume proof (proof-ite goal claim *proof-true*) t))
             (step (proof-proof-prove-if proof assumed descent)))
          (cons step (list :b1-tree-induction lib formula variable measure substitutions)))))))

(defun b1-induction-tree-induction-finish (induction proof)
  (let ((lib (cadr induction))
        (variable (cadddr induction)))
    (proof-with-checked-results
        ((ordinal (library-library-builtin lib 1 variable)))
      (proof-proof-induct (library-library-proof lib) ordinal proof
                         (caddr induction) (nth 4 induction)
                         (b1-induction-tree-induction-substitutions induction)))))
