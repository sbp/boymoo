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

(defun t2-rename-fresh-definition-names (definitions names)
  (if (endp definitions)
      names
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3))
      (stem (proof-term-at (car definition) 2)))
     (if (stringp stem)
         (let ((name (proof-sym (concatenate 'string "T2-RECURSION-" stem) "ACL2")))
           (t2-rename-fresh-definition-names
            (cdr definitions) (table-put names (car definition) name)))
       '(:failure "failure" "")))))

(defun t2-rename-fresh-definition-rulers (rulers names)
  (if (endp rulers)
      nil
    (cons (table-get names (car rulers) (car rulers))
          (t2-rename-fresh-definition-rulers (cdr rulers) names))))

(defun t2-rename-fresh-definition-bodies (definitions names)
  (if (endp definitions)
      nil
    (let ((definition (car definitions)))
      (proof-with-checked-results
       ((body (t2-rename-rename-calls (caddr definition) names))
        (rest (t2-rename-fresh-definition-bodies (cdr definitions) names)))
       (cons (list (table-get names (car definition) nil) (cadr definition) body)
             rest)))))

(defun t2-rename-fresh-definition (rulers definitions)
  (proof-with-checked-results
   ((names (t2-rename-fresh-definition-names definitions nil))
    (rulers (if (proof-compound rulers)
                (t2-rename-fresh-definition-rulers rulers names)
              rulers))
    (definitions (t2-rename-fresh-definition-bodies definitions names)))
   (list rulers definitions names)))
