(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)
(logic)

(mutual-recursion
 (defun t2-equational-witness-available (term lib)
   (declare (xargs :measure (acl2-count term)))
   (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
       t
     (let ((operator (t2-book-logic-head term))
           (proof (library-library-proof lib)))
       (and (or (equal operator *proof-if*)
                (assoc-equal operator (proof-proof-definitions proof))
                (member-equal operator (proof-proof-primitives proof)))
            (or (not (consp term))
                (t2-equational-witness-available-arguments (cdr term) lib))))))

 (defun t2-equational-witness-available-arguments (arguments lib)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       t
     (and (t2-equational-witness-available (car arguments) lib)
          (t2-equational-witness-available-arguments (cdr arguments) lib)))))

(defun t2-equational-witness-symbol-parameters-p (parameters)
  (if (endp parameters)
      t
    (let ((parameter (car parameters)))
      (and (consp parameter)
           (equal (car parameter) "sym")
           (not (equal parameter *proof-nil*))
           (not (equal parameter *proof-t*))
           (t2-equational-witness-symbol-parameters-p (cdr parameters))))))

(defun t2-equational-witness-orientation (lib name arity left right)
  (and (proof-is-call left name)
       (let ((parameters (cdr left)))
         (and (equal (len left) (1+ arity))
              (t2-equational-witness-symbol-parameters-p parameters)
              (no-duplicatesp-equal parameters)
              (subsetp-equal (t2-book-logic-variables right) parameters)
              (t2-equational-witness-available right lib)
              (list parameters right)))))

(defun t2-equational-witness-defining-equation (lib name arity formulas)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      '(:failure "Unproved" "")
    (let ((formula (car formulas)))
      (if (not (proof-is-call formula *proof-equal*))
          (t2-equational-witness-defining-equation lib name arity (cdr formulas))
        (proof-with-checked-results
            ((sides (proof-list-of-length (cdr formula) 2))
             (written (t2-equational-witness-orientation
                       lib name arity (car sides) (cadr sides)))
             (reversed (or written (t2-equational-witness-orientation
                                    lib name arity (cadr sides) (car sides)))))
          (or reversed
              (t2-equational-witness-defining-equation lib name arity (cdr formulas))))))))

(defun t2-equational-witness-pair (row)
  (if (stringp row)
      (if (equal (length row) 2)
          (list (subseq row 0 1) (subseq row 1 2))
        '(:failure "RecipeMismatch" ""))
    (proof-list-of-length row 2)))

(defun t2-equational-witness-formulas (claims)
  (if (endp claims)
      nil
    (proof-with-checked-results
        ((claim (t2-equational-witness-pair (car claims)))
         (rest (t2-equational-witness-formulas (cdr claims))))
      (cons (cadr claim) rest))))

(defun t2-equational-witness-choose (declarations lib formulas index chosen definitions)
  (declare (xargs :measure (acl2-count declarations)))
  (if (endp declarations)
      (list chosen (reverse definitions))
    (proof-with-checked-results
        ((declaration (t2-equational-witness-pair (car declarations)))
         (equation (t2-equational-witness-defining-equation
                    lib (car declaration) (cadr declaration) formulas)))
      (let ((name (proof-sym (concatenate 'string "SELF-EQUATIONAL-WITNESS-" (decimal-text index))
                             "ACL2")))
        (t2-equational-witness-choose
         (cdr declarations) lib formulas (1+ index)
         (table-put chosen (car declaration) name)
         (cons (list name (or (car equation) *proof-nil*) (cadr equation)) definitions))))))

(defun t2-equational-witness-install (definitions lib)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      lib
    (let ((definition (car definitions)))
      (proof-with-checked-results
          ((lib (library-library-definition lib (car definition)
                                             (cadr definition) (caddr definition))))
        (t2-equational-witness-install (cdr definitions) lib)))))

(defun t2-equational-witness-proofs (formulas lib rules chosen names proofs)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      (cons (reverse proofs) lib)
    (proof-with-checked-results
        ((target (t2-evaluator-rename (car formulas) chosen))
         (search (t2-book-logic-search-init lib rules names 3600 nil))
         (result (t2-book-logic-search-proof search target nil 5))
         (step (car result))
         (next-search (cdr result))
         (lib (t2-book-logic-search-lib next-search))
         (subsumed (proof-proof-subsume (library-library-proof lib) step (list target))))
      (t2-equational-witness-proofs (cdr formulas) lib
                                    (t2-book-logic-search-rules next-search)
                                    chosen names (cons subsumed proofs)))))

(defun t2-equational-witness-with-prepared-rules (lib data prepared)
  (proof-with-checked-results
      ((claims (proof-term-at data 1))
       (formulas (t2-equational-witness-formulas claims))
       (declarations (proof-term-at data 0))
       (choices (t2-equational-witness-choose declarations lib formulas 0 nil nil))
       (lib (t2-equational-witness-install (cadr choices) lib))
       (rules (if prepared
                  (t2-book-logic-rules-from-prepared prepared lib)
                (t2-book-logic-rules-init lib)))
       (chosen (car choices))
       (names (table-values chosen))
       (proved (t2-equational-witness-proofs formulas lib rules chosen names nil))
       (declaration (proof-term-at declarations 0))
       (name (proof-term-at declaration 0))
       (entry (proof-proof-entry "witness" name (cons name names) (car proved))))
    (cons entry (cdr proved))))

(defun t2-equational-witness-witness (lib data)
  (t2-equational-witness-with-prepared-rules lib data nil))
