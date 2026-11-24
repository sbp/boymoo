(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-book-choice-values (bound index call)
  (if (endp bound)
      nil
    (cons (list (proof-sym "MV-NTH" "ACL2") (proof-quote index) call)
          (h4-book-choice-values (cdr bound) (1+ index) call))))

(defun h4-book-choice-bind (variables values bindings)
  (if (or (endp variables) (endp values))
      bindings
    (h4-book-choice-bind
     (cdr variables) (cdr values)
     (table-put bindings (car variables) (car values)))))

(defun h4-book-choice-choice-formula-chosen (variables name bound)
  (let* ((call (cons name variables))
         (values (if (equal (len bound) 1)
                     (list call)
                   (h4-book-choice-values bound 0 call))))
    (list call (h4-book-choice-bind bound values nil))))

(defun h4-book-choice-choice-formula (fields)
  (proof-with-checked-results ((fields (proof-list-of-length fields 5)))
    (let* ((name (car fields))
           (bound (cadr fields))
           (free (if (equal (caddr fields) *proof-nil*) nil (caddr fields)))
           (body (cadddr fields))
           (alternate (nth 4 fields))
           (chosen (h4-book-choice-choice-formula-chosen free name bound))
           (call (car chosen))
           (bindings (cadr chosen)))
      (proof-with-checked-results
       ((body-at-choice (proof-subst body bindings))
        (basic (list *library-implies* body body-at-choice))
        (basic (if (< 1 (len bound))
                   (proof-ite (list (proof-sym "TRUE-LISTP" "ACL2") call) basic *proof-false*)
                 basic)))
       (if (equal alternate *proof-nil*)
           basic
         (let* ((other-choice (h4-book-choice-choice-formula-chosen alternate name bound))
                (other (car other-choice))
                (alternatives (cadr other-choice)))
           (proof-with-checked-results
            ((other-body (proof-subst body (h4-book-choice-bind free alternate nil)))
             (same (proof-eq call other))
             (first-body (proof-subst body bindings))
             (first-alternate (proof-subst other-body bindings))
             (first-only (proof-ite first-body (proof-neg first-alternate) *proof-false*))
             (second-alternate (proof-subst other-body alternatives))
             (second-body (proof-subst body alternatives))
             (second-only (proof-ite second-alternate (proof-neg second-body) *proof-false*)))
            (proof-ite basic
                       (proof-ite same same (proof-ite first-only first-only second-only))
                       *proof-false*))))))))

(defun h4-book-choice-choice-fact (p name bindings choices)
  (let ((fields (assoc-equal name choices)))
    (if (not fields)
        '(:failure "failure" "")
      (proof-with-checked-results
       ((formula (h4-book-choice-choice-formula (cdr fields))))
       (proof-proof-instantiate (library-library-proof p)
                                (proof-make-step "fact" (list name) (list formula))
                                bindings)))))
