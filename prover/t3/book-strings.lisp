(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t3-book-strings-string-results-init (lib earlier)
  (list :t3-string-results lib earlier))

(defun t3-book-strings-string-results-lib (results)
  (cadr results))

(defun t3-book-strings-string-results-earlier (results)
  (caddr results))

(defun t3-book-strings-earlier-request-p (result)
  (eq (car result) :t3-book-strings-earlier))

(defmacro t3-book-strings-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name)
                 (t3-book-strings-earlier-request-p ,name))
             ,name
           (t3-book-strings-with-results ,(cdr bindings) ,result))))))

(defun t3-book-strings-string-template ()
  (list *t3-list-bounds-stringp* *proof-result*))

(defund t3-book-strings-call-action (results value formula trail)
  (let* ((lib (t3-book-strings-string-results-lib results))
         (proof (library-library-proof lib))
         (earlier (assoc-equal formula
                               (t3-book-strings-string-results-earlier results))))
    (cond
     ((not earlier) (list :t3-book-strings-earlier formula))
     ((cdr earlier) (cdr earlier))
     (t
      (proof-with-checked-results
          ((function (proof-term-at value 0))
           (index (if (equal function *t3-book-projections-mv-nth*)
                      (proof-term-at value 1)
                    nil))
           (number (if (proof-is-call index *proof-quote*)
                       (proof-term-at index 1)
                     nil)))
        (cond
         ((integerp number) (list :project))
         ((or (proof-compound function)
              (equal function *proof-if*)
              (member-equal function *t3-logic-wrappers*))
          (list :cases value trail nil))
         ((or (member-equal function trail)
              (not (assoc-equal function (proof-proof-definitions proof))))
          '(:failure "unsupported" ""))
         (t
          (proof-with-checked-results
              ((opened (proof-proof-unfold proof value))
               (body (proof-rewritten-term opened)))
            (list :cases body (append trail (list function)) opened)))))))))

(defund t3-book-strings-string-action (results value tests trail)
  (let* ((lib (t3-book-strings-string-results-lib results))
         (formula (list *t3-list-bounds-stringp* value)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (known (t3-logic-evidence-find evidence formula)))
      (cond
       ((car known) (car known))
       ((proof-is-call value *proof-quote*)
        (t3-logic-libraryproofs-prove-formula lib formula nil nil))
       ((and (proof-is-call value *t3-list-bounds-coerce*)
             (endp (cddr value)))
        (proof-term-at value 2))
       ((and (proof-is-call value *t3-list-bounds-coerce*)
             (equal (caddr value) *t3-list-bounds-string-type*))
        (t3-list-bounds-string-assertion lib (cadr value)))
       ((or (not (proof-compound value)) (< 10 (len trail)))
        '(:failure "unsupported" ""))
       (t (t3-book-strings-call-action results value formula trail))))))

(defund t3-book-strings-projection (results value trail)
  (let ((proof (library-library-proof
                (t3-book-strings-string-results-lib results))))
    (proof-with-checked-results
        ((parts (proof-list-of-length value 3))
         (index (cadr parts))
         (number (proof-term-at index 1))
         (producer (caddr parts)))
      (if (or (not (integerp number)) (< number 0) (< 8 number)
              (not (proof-compound producer)))
          '(:failure "unsupported" "")
        (proof-with-checked-results ((function (proof-term-at producer 0)))
          (if (or (member-equal function trail)
                  (not (assoc-equal function (proof-proof-definitions proof))))
              '(:failure "unsupported" "")
            (proof-with-checked-results
                ((template (list *t3-list-bounds-stringp*
                                 (list *t3-book-projections-mv-nth* index *proof-result*)))
                 (opened (proof-proof-unfold proof producer))
                 (body (proof-rewritten-term opened)))
              (list body template (append trail (list function)) number opened))))))))

(defund t3-book-strings-projected-leaf-selection (results index term)
  (let ((lib (t3-book-strings-string-results-lib results)))
    (proof-with-checked-results
        ((selected (t3-book-projections-project lib index term))
         (value (proof-rewritten-term selected)))
      (cons value selected))))

(defund t3-book-strings-branch (proof value)
  (if (proof-is-call value *proof-if*)
      (proof-with-checked-results ((parts (proof-list-of-length (cdr value) 3)))
        (cons :if parts))
    (proof-with-checked-results ((opened (t3-logic-by-value-unfold proof value)))
      (if opened
          (proof-with-checked-results ((body (proof-rewritten-term opened)))
            (list :opened body opened))
        '(:leaf)))))

(defun t3-book-strings-rewrite-branch (proof step opened template)
  (proof-with-checked-results ((reverse (proof-proof-symmetric proof opened)))
    (proof-proof-rewrite-result proof step reverse template *proof-result*)))

(mutual-recursion
 (defun t3-book-strings-string-results-string-run (n results value tests trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "t3-book-strings-string-results-string-run")
     (let ((action (t3-book-strings-string-action results value tests trail)))
       (case (car action)
         (:project
          (t3-book-strings-string-results-projected-run (1- n) results value tests trail))
         (:cases
          (t3-book-strings-with-results
              ((step (t3-book-strings-visit
                      (1- n) results (cadr action) (t3-book-strings-string-template)
                      tests (caddr action) nil)))
            (if (cadddr action)
                (library-library-transport-argument
                 (t3-book-strings-string-results-lib results) step (cadddr action) 1)
              step)))
         (otherwise action)))))

 (defun t3-book-strings-string-results-projected-run (n results value tests trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "t3-book-strings-string-results-projected-run")
     (t3-book-strings-with-results
         ((projection (t3-book-strings-projection results value trail))
          (template (cadr projection))
          (result (t3-book-strings-visit
                   (1- n) results (car projection) template tests
                   (caddr projection) (cadddr projection))))
       (t3-book-strings-rewrite-branch
        (library-library-proof (t3-book-strings-string-results-lib results))
        result (nth 4 projection) template))))

 (defun t3-book-strings-string-results-projected-leaf
     (n term signed results trail index)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "t3-book-strings-string-results-projected-leaf")
     (t3-book-strings-with-results
         ((selection (t3-book-strings-projected-leaf-selection results index term))
          (result (t3-book-strings-string-results-string-run
                   (1- n) results (car selection) signed trail)))
       (library-library-transport-argument
        (t3-book-strings-string-results-lib results) result (cdr selection) 1))))

 (defun t3-book-strings-visit (n results value template tests trail index)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "t3-book-strings-visit")
     (let* ((proof (library-library-proof (t3-book-strings-string-results-lib results)))
            (branch (t3-book-strings-branch proof value)))
       (case (car branch)
         (:if
          (let ((test (cadr branch)))
            (t3-book-strings-with-results
                ((yes (t3-book-strings-visit
                       (1- n) results (caddr branch) template
                       (append tests (list (list test t))) trail index))
                 (no (t3-book-strings-visit
                      (1- n) results (cadddr branch) template
                      (append tests (list (list test nil))) trail index)))
              (proof-by-value-join proof value template yes no))))
         (:opened
          (t3-book-strings-with-results
              ((step (t3-book-strings-visit
                      (1- n) results (cadr branch) template tests trail index)))
            (t3-book-strings-rewrite-branch proof step (caddr branch) template)))
         (:leaf
          (t3-book-strings-with-results
              ((step (if (integerp index)
                         (t3-book-strings-string-results-projected-leaf
                          (1- n) value tests results trail index)
                       (t3-book-strings-string-results-string-run
                        (1- n) results value tests trail))))
            (t3-logic-by-value-check-leaf step value template)))
         (otherwise branch))))))

