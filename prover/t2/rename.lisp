(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun t2-rename-rename-calls (term names)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) term)
         ((endp term) '(:failure "failure" ""))
         ((equal (car term) *proof-quote*) term)
         (t (let ((head (car term)))
              (proof-with-checked-results
               ((operator
                 (if (proof-compound head)
                     (if (equal (len head) 3)
                         (proof-with-checked-results
                          ((body (t2-rename-rename-calls (caddr head) names)))
                          (list (car head) (cadr head) body))
                       (proof-list-of-length head 3))
                   (table-get names head head)))
                (arguments (t2-rename-rename-arguments (cdr term) names)))
               (cons operator arguments))))))
 (defun t2-rename-rename-arguments (arguments names)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
      ((first (t2-rename-rename-calls (car arguments) names))
       (rest (t2-rename-rename-arguments (cdr arguments) names)))
      (cons first rest)))))

