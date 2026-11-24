(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t3-book-values-symbolp* *t3-book-spines-symbolp*)
(defconst *t3-book-values-symbol-name* *t3-book-spines-symbol-name*)
(defconst *t3-book-values-char-code* *t3-book-spines-char-code*)
(defconst *t3-book-values-code-char* *t3-book-spines-code-char*)
(defconst *t3-book-values-coerce* *t3-book-spines-coerce*)
(defconst *t3-book-values-numberp* *t3-book-spines-numberp*)
(defconst *t3-book-values-package-name* *t3-book-spines-package-name*)
(defconst *t3-book-values-imports* *t3-book-spines-imports*)
(defconst *t3-book-values-witness* *t3-book-spines-witness*)
(defconst *t3-book-values-intern* *t3-book-spines-intern*)
(defconst *t3-book-values-bad-atom* *t3-book-spines-bad-atom*)

(defun t3-book-values-tagged (value tag)
  (t3-book-spines-tagged value tag))

(defun t3-book-values-make-book-proofs (library packages visible)
  (t3-book-spines-make-book-proofs library packages visible))

(defun t3-book-values-book-proofs-library (book-proofs)
  (t3-book-spines-library book-proofs))

(defun t3-book-values-book-proofs-packages (book-proofs)
  (t3-book-spines-book-packages book-proofs))

(defun t3-book-values-book-proofs-visible (book-proofs)
  (t3-book-spines-book-visible book-proofs))

(defun t3-book-values-book-proofs-with-library (book-proofs library)
  (t3-book-values-make-book-proofs library
                                 (t3-book-values-book-proofs-packages book-proofs)
                                 (t3-book-values-book-proofs-visible book-proofs)))

(defun t3-book-values-declaration-imports (symbols imports)
  (cond
   ((integerp symbols) '(:failure "failure" ""))
   ((endp symbols) imports)
   (t
    (proof-with-checked-results ((name (proof-term-at (car symbols) 2)))
      (t3-book-values-declaration-imports (cdr symbols)
                                         (table-put imports name (car symbols)))))))

(defun t3-book-values-book-proofs-declaration (book-proofs kind data)
  (if (member-equal kind '("package" "hidden-package"))
      (proof-with-checked-results
       ((fields (proof-list-of-length data 2))
        (imports (if (equal (cadr fields) *proof-nil*)
                     nil
                   (t3-book-values-declaration-imports (cadr fields) nil)))
        (name (proof-term-at (car fields) 1)))
       (let ((packages (t3-book-values-book-proofs-packages book-proofs))
             (visible (t3-book-values-book-proofs-visible book-proofs)))
         (t3-book-values-make-book-proofs
          (t3-book-values-book-proofs-library book-proofs)
          (table-put packages name imports)
          (if (and (equal kind "package") (not (member-equal name visible)))
              (append visible (list name))
            visible))))
    book-proofs))

(defun t3-book-values-init-declarations (book-proofs ground)
  (declare (xargs :measure (acl2-count ground)))
  (if (endp ground)
      book-proofs
    (proof-with-checked-results
     ((record (proof-list-of-length (car ground) 2))
      (book-proofs (t3-book-values-book-proofs-declaration book-proofs (car record) (cadr record))))
     (t3-book-values-init-declarations book-proofs (cdr ground)))))

(defun t3-book-values-book-proofs-init (ground)
  (t3-book-values-init-declarations
   (t3-book-values-make-book-proofs
    (t3-logic-libraryproofs-for-book (library-library-init (proof-proof-init))) nil nil)
   ground))

(defun t3-book-values-book-proofs-package-value (book-proofs function datum)
  (t3-book-spines-book-package-value book-proofs function datum))

(defun t3-book-values-book-proofs-coerce (datum kind)
  (t3-book-spines-book-coerce datum kind))

(defun t3-book-values-book-proofs-constant (book-proofs term)
  (t3-book-spines-book-constant book-proofs term))

(defun t3-book-values-book-proofs-simplify (book-proofs term evidence definitions)
  (t3-book-spines-book-simplify book-proofs term evidence definitions))

(defun t3-book-values-book-proofs-normalize (book-proofs term evidence definitions)
  (t3-book-values-book-proofs-simplify book-proofs term evidence
                                      (append *t3-logic-wrappers* definitions)))

(defund t3-book-values-prove-step (book-proofs term evidence definitions)
  (let ((proof (library-library-proof (t3-book-values-book-proofs-library book-proofs))))
    (cond
     ((equal term *proof-true*) (proof-proof-prove proof term nil nil))
     (t
      (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
        (if premise
            premise
          (proof-with-checked-results
           ((equation (t3-book-values-book-proofs-simplify book-proofs term evidence definitions))
            (right (and equation (proof-rewritten-term equation))))
           (cond ((or (not equation) (equal right term)) (proof-prove-unproved-term term))
                 ((equal right *proof-true*) (proof-proof-true-from-eq proof equation))
                 (t (list :transport right equation))))))))))

(defun t3-book-values-prove-visit (n book-proofs term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-values-book-proofs-prove")
    (let ((next (t3-book-values-prove-step book-proofs term evidence definitions)))
      (if (eq (car next) :transport)
          (proof-with-checked-results
           ((step (t3-book-values-prove-visit (1- n) book-proofs (cadr next)
                                             evidence definitions)))
           (proof-proof-transport
            (library-library-proof (t3-book-values-book-proofs-library book-proofs))
            step (caddr next)))
        next))))

(defun t3-book-values-book-proofs-prove (book-proofs term evidence definitions)
  (t3-book-values-prove-visit 1000000 book-proofs term evidence definitions))

(defun t3-book-values-natural-default (book-proofs term)
  (t3-book-values-book-proofs-prove book-proofs (list *library-natp* term) nil
                                   (list *library-natp* *proof-not*)))

(defund t3-book-values-natural-step (book-proofs term)
  (let ((lib (t3-book-values-book-proofs-library book-proofs)))
    (cond
     ((proof-is-call term *library-nfix*)
      (library-library-cite lib "NFIX-NATURAL" (cdr term) nil))
     ((proof-is-call term *t3-book-lemmas-exported-nfix*)
      (proof-with-checked-results
       ((value (library-library-cite lib "NFIX-NATURAL" (cdr term) nil))
        (exported (library-library-cite lib "T3-EXPORTED-NFIX" (cdr term) nil)))
       (library-library-transport-argument lib value exported 1)))
     ((or (proof-is-call term *t3-logic-length*)
          (proof-is-call term *library-gap*)
          (proof-is-call term *library-count*)
          (proof-is-call term *library-len*))
      (t3-logic-libraryproofs-natural lib term))
     ((proof-is-call term *proof-if*) '(:by-value))
     ((proof-is-call term *proof-times*)
      (proof-with-checked-results ((factor (proof-term-at term 1)))
        (if (equal factor (proof-quote 2))
            (proof-with-checked-results ((arg (proof-term-at term 2)))
              (list :double arg))
          (t3-book-values-natural-default book-proofs term))))
     ((proof-is-call term *proof-plus*) '(:sum))
     (t (t3-book-values-natural-default book-proofs term)))))

(defund t3-book-values-value-step (proof value)
  (if (proof-is-call value *proof-if*)
      (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
        (cons :branches branches))
    (proof-with-checked-results ((equation (t3-logic-by-value-unfold proof value)))
      (if equation
          (proof-with-checked-results ((opened (proof-rewritten-term equation)))
            (list :opened opened equation))
        '(:leaf)))))

(mutual-recursion
 (defun t3-book-values-natural-visit (n book-proofs term)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-book-values-book-proofs-natural")
     (let ((lib (t3-book-values-book-proofs-library book-proofs))
           (next (t3-book-values-natural-step book-proofs term)))
       (case (car next)
         (:by-value (t3-book-values-natural-by-value (1- n) book-proofs term))
         (:double
          (proof-with-checked-results
           ((fact (t3-book-values-natural-visit (1- n) book-proofs (cadr next))))
           (library-library-cite lib "T3-NATURAL-DOUBLE" (cddr term) (list fact))))
         (:sum
          (proof-with-checked-results
           ((steps (t3-book-values-natural-arguments (1- n) book-proofs (cdr term))))
           (library-library-cite lib "NATURAL-SUM" (cdr term) steps)))
         (otherwise next)))))

 (defun t3-book-values-natural-arguments (n book-proofs terms)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t3-book-values-book-proofs-natural"))
    ((endp terms) nil)
    (t
     (proof-with-checked-results
      ((first (t3-book-values-natural-visit (1- n) book-proofs (car terms)))
       (rest (t3-book-values-natural-arguments (1- n) book-proofs (cdr terms))))
      (cons first rest)))))

 (defun t3-book-values-natural-by-value (n book-proofs value)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-book-values-book-proofs-natural")
     (let* ((proof (library-library-proof (t3-book-values-book-proofs-library book-proofs)))
            (template (list *library-natp* *proof-result*))
            (next (t3-book-values-value-step proof value)))
       (case (car next)
         (:branches
          (proof-with-checked-results
           ((yes (t3-book-values-natural-by-value (1- n) book-proofs (caddr next)))
            (no (t3-book-values-natural-by-value (1- n) book-proofs (cadddr next))))
           (proof-by-value-join proof value template yes no)))
         (:opened
          (proof-with-checked-results
           ((step (t3-book-values-natural-by-value (1- n) book-proofs (cadr next)))
            (back (proof-proof-symmetric proof (caddr next))))
           (proof-proof-rewrite-result proof step back template *proof-result*)))
         (:leaf
          (proof-with-checked-results
           ((step (t3-book-values-natural-visit (1- n) book-proofs value)))
           (t3-logic-by-value-check-leaf step value template)))
         (otherwise next))))))

(defun t3-book-values-book-proofs-natural (book-proofs term)
  (t3-book-values-natural-visit 1000000 book-proofs term))

(defund t3-book-values-type-step (book-proofs term evidence)
  (let* ((lib (t3-book-values-book-proofs-library book-proofs))
         (literal (library-integer term)))
    (if (or (proof-is-call term *library-nfix*)
            (proof-is-call term *t3-book-lemmas-exported-nfix*)
            (proof-is-call term *t3-logic-length*)
            (proof-is-call term *library-gap*)
            (proof-is-call term *proof-if*))
        (proof-with-checked-results ((natural (t3-book-values-book-proofs-natural book-proofs term)))
          (library-library-cite lib "NATURAL-INTEGER" (list term) (list natural)))
      (proof-with-checked-results ((premise (proof-find-evidence evidence (list literal))))
        (cond
         (premise premise)
         ((and (proof-is-call term *proof-quote*)
               (or (integerp (cadr term)) (eq (cadr term) t)))
          (t3-book-values-book-proofs-prove book-proofs literal nil nil))
         ((proof-is-call term *proof-plus*) '(:args "INTEGER-SUM"))
         ((proof-is-call term *proof-times*) '(:args "INTEGER-PRODUCT"))
         ((proof-is-call term *proof-minus*) '(:negate))
         (t (t3-logic-libraryproofs-type-of lib term evidence)))))))

(mutual-recursion
 (defun t3-book-values-book-proofs-type-of (book-proofs term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let ((lib (t3-book-values-book-proofs-library book-proofs))
         (next (t3-book-values-type-step book-proofs term evidence)))
     (if (not (consp term))
         next
       (case (car next)
         (:args
          (proof-with-checked-results
           ((steps (t3-book-values-type-arguments book-proofs (cdr term) evidence)))
           (library-library-cite lib (cadr next) (cdr term) steps)))
         (:negate
          (if (consp (cdr term))
              (proof-with-checked-results
               ((step (t3-book-values-book-proofs-type-of book-proofs (cadr term) evidence)))
               (library-library-cite lib "INTEGER-NEGATION" (cdr term) (list step)))
            (proof-term-at term 1)))
         (otherwise next)))))

 (defun t3-book-values-type-arguments (book-proofs terms evidence)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (t3-book-values-book-proofs-type-of book-proofs (car terms) evidence))
       (rest (t3-book-values-type-arguments book-proofs (cdr terms) evidence)))
      (cons first rest)))))
