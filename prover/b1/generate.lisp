(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-generate-admit-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (let ((fields (car definitions)))
      (if (and (true-listp fields) (= (len fields) 3) (true-listp (cadr fields)))
        (proof-with-checked-results
         ((next (proof-proof-add-definition proof (car fields) (cadr fields) (caddr fields))))
         (b1-generate-admit-definitions next (cdr definitions)))
        '(:failure "failure" "")))))

(defun b1-generate-admit-fact (lib name formula formulas)
  (let* ((proof (library-library-proof lib))
         (facts (table-put (proof-proof-facts proof) name (list formula)))
         (lib (library-library-with-proof lib (proof-proof-with-facts proof facts))))
    (cons lib (if (assoc-equal formula formulas)
                  formulas
                (table-put formulas formula name)))))

(defun b1-generate-admit-constraints (lib constraints formulas)
  (declare (xargs :measure (acl2-count constraints)))
  (cond
   ((null constraints) (cons lib formulas))
   ((atom constraints)
    '(:failure "failure" ""))
   (t
    (proof-with-checked-results
     ((fields (proof-list-of-length (car constraints) 2)))
     (let ((admitted (b1-generate-admit-fact lib (car fields) (cadr fields) formulas)))
       (b1-generate-admit-constraints (car admitted) (cdr constraints) (cdr admitted)))))))

(defun b1-generate-admit (lib word data formulas)
  (cond
   ((equal word "define")
    (proof-with-checked-results
     ((proof (b1-generate-admit-definitions (library-library-proof lib) (cdr data))))
     (cons (library-library-with-proof lib proof) formulas)))
   ((or (equal word "theorem") (equal word "axiom"))
    (proof-with-checked-results ((fields (proof-list-of-length data 2)))
      (b1-generate-admit-fact lib (car fields) (cadr fields) formulas)))
   ((equal word "constrain")
    (proof-with-checked-results ((constraints (proof-term-at data 1)))
      (if (equal constraints *proof-nil*)
          (cons lib formulas)
        (b1-generate-admit-constraints lib constraints formulas))))
   (t (cons lib formulas))))

(defun b1-generate-obligations (word data)
  (cond
   ((equal word "theorem")
    (proof-with-checked-results ((name (proof-term-at data 0))) (list name nil)))
   ((equal word "define")
    (proof-with-checked-results
     ((rulers (proof-term-at data 0))
      (calls (termination-recursive-calls rulers (cdr data))))
     (if (endp calls)
         (list nil nil)
       (proof-with-checked-results ((name (proof-term-at (cadr data) 0)))
         (list name calls)))))
   ((equal word "constrain")
    (proof-with-checked-results ((constraints (proof-term-at data 1)))
      (if (equal constraints *proof-nil*)
          (list nil nil)
        (proof-with-checked-results
         ((definitions (proof-term-at data 0))
          (first (proof-term-at definitions 0))
          (name (proof-term-at first 0)))
         (list name nil)))))
   (t (list nil nil))))

(defun b1-generate-label (name)
  (proof-with-checked-results ((label (proof-term-at name 2)))
    (if (and (stringp label) (b1-logic-ascii-characters-p (coerce label 'list)))
        label
      '(:failure "failure" ""))))

(defun b1-generate-with-library (result lib)
  (if (failure-p result) (cons result lib) result))

(defun b1-generate-other-literal-p (clause formula)
  (declare (xargs :measure (acl2-count clause)))
  (and (consp clause)
       (or (not (equal (car clause) formula))
           (b1-generate-other-literal-p (cdr clause) formula))))

(defun b1-generate-theorem-proof (lib label formula formulas facts)
  (let ((known (assoc-equal formula formulas))
        (unproved (member-equal label *b1-theorems-unproved*)))
    (cond
     (known (cons (proof-proof-fact (library-library-proof lib) (cdr known) nil) lib))
     ((assoc-equal label *b1-theorems-recipes*)
      (b1-generate-with-library (b1-theorems-apply-recipe label lib formula) lib))
     (unproved (cons '(:failure "unproved" "") lib))
     (t
      (let ((wrapper (b1-xdoc-types-tree-tag-wrapper lib formula)))
        (if wrapper
            (cons wrapper lib)
          (let* ((attempt (b1-generate-with-library (b1-search-automatic lib facts formula) lib))
                 (proof (car attempt)))
            (if (and (not (failure-p proof))
                     (b1-generate-other-literal-p (proof-step-clause proof) formula))
                (cons '(:failure "unproved" "")
                      (cdr attempt))
              attempt))))))))

(defun b1-generate-prove-theorem (lib label name data formulas facts)
  (let ((formula (proof-term-at data 1)))
    (if (failure-p formula)
        (cons formula lib)
      (let* ((result (b1-generate-theorem-proof lib label formula formulas facts))
             (step (car result))
             (lib (cdr result)))
        (if (failure-p step)
            result
          (cons (proof-with-checked-results
                 ((step (proof-proof-subsume (library-library-proof lib) step (list formula))))
                 (proof-proof-entry "theorem" name (list name) (list step)))
                lib))))))

(defun b1-generate-functions (declarations)
  (declare (xargs :measure (acl2-count declarations)))
  (if (endp declarations)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car declarations) 0))
      (rest (b1-generate-functions (cdr declarations))))
     (cons name rest))))

(defun b1-generate-named-witness (recipe lib names formulas)
  (case recipe
    (b1-witnesses-identity-witness (b1-witnesses-identity-witness lib names formulas))
    (b1-witnesses-successor-witness (b1-witnesses-successor-witness-with-library lib names formulas))
    (b1-witnesses-alist-type-witness (b1-witnesses-alist-type-witness-with-library lib names formulas))
    (b1-witnesses-list-type-witness (b1-witnesses-list-type-witness-with-library lib names formulas))
    (b1-witnesses-evaluator-witness (b1-witnesses-evaluator-witness-with-library lib names formulas))
    (otherwise '(:failure "unproved" ""))))

(defun b1-generate-witness-proof (lib label data facts)
  (let ((recipe (assoc-equal label *b1-witnesses-witnesses*)))
    (proof-with-checked-results ((declarations (proof-term-at data 0)))
      (if recipe
          (proof-with-checked-results
           ((names (b1-generate-functions declarations))
            (formulas (proof-term-at data 1)))
           (b1-generate-named-witness (cdr recipe) lib names formulas))
        (proof-with-checked-results ((formulas (proof-term-at data 1)))
          (b1-witnesses-small-witnesses lib declarations formulas facts))))))

(defun b1-generate-prove-with-library (lib word data name calls aids formulas facts)
  (let ((label (b1-generate-label name)))
    (cond
     ((failure-p label) (cons label lib))
     ((equal word "define")
      (let ((unproved (member-equal label *b1-theorems-unproved*)))
        (if unproved
            (cons '(:failure "unproved" "") lib)
          (let* ((result (b1-measures-termination-with-library lib (cdr data) calls aids))
                 (proofs (car result)))
            (if (failure-p proofs)
                result
              (cons (proof-proof-entry "measure" name (cons name (car proofs)) (cadr proofs))
                    (cdr result)))))))
     ((equal word "theorem") (b1-generate-prove-theorem lib label name data formulas facts))
     ((equal word "constrain")
      (let* ((result (b1-generate-with-library (b1-generate-witness-proof lib label data facts) lib))
             (proofs (car result)))
        (if (failure-p proofs)
            result
          (cons (proof-proof-entry "witness" name (cons name (car proofs)) (cadr proofs))
                (cdr result)))))
     (t (cons '(:failure "unproved" "") lib)))))

(defun b1-generate-prove (lib word data name calls aids formulas facts)
  (let ((result (b1-generate-prove-with-library lib word data name calls aids formulas facts)))
    (if (failure-p (car result)) (car result) result)))

