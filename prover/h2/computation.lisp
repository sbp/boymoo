(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h2-computation-tag (value)
  (and (consp value) (stringp (car value)) (car value)))

(defun h2-computation-integer-or-true-p (value)
  (or (integerp value) (eq value t)))

(defun h2-computation-true-p (value)
  (cond ((or (null value) (eq value :none)) nil)
        ((acl2-numberp value) (not (equal value 0)))
        ((stringp value) (not (equal value "")))
        (t t)))

(defun h2-computation-ratio-value (fields)
  (let ((size (len fields))
        (num (car fields))
        (den (cadr fields)))
    (cond ((equal size 0) 0)
          ((equal size 1)
           (cond ((rationalp num) num)
                 ((eq num t) 1)
                 (t '(:failure "tactic-inapplicable" ""))))
          ((equal size 2)
           (cond ((not (and (h2-computation-integer-or-true-p num)
                            (h2-computation-integer-or-true-p den)))
                  '(:failure "tactic-inapplicable" ""))
                 ((equal den 0) '(:failure "failure" ""))
                 (t (/ (if (eq num t) 1 num) (if (eq den t) 1 den)))))
          (t '(:failure "tactic-inapplicable" "")))))

(defun h2-computation-rational (value)
  (cond ((integerp value) value)
        ((eq value t) 1)
        ((equal (h2-computation-tag value) "ratio")
         (h2-computation-ratio-value (cdr value)))
        (t nil)))

(defun h2-computation-rational-list (values)
  (if (endp values)
      nil
    (proof-with-checked-results
        ((first (h2-computation-rational (car values)))
         (rest (h2-computation-rational-list (cdr values))))
      (cons first rest))))

(defun h2-computation-components (value)
  (if (equal (h2-computation-tag value) "complex")
      (h2-computation-rational-list (cdr value))
    (proof-with-checked-results ((real (h2-computation-rational value)))
      (list (or real 0) 0))))

(defun h2-computation-encode (value)
  (cond ((integerp value) value)
        ((eq value t) 1)
        ((rationalp value)
         (list "ratio" (numerator value) (denominator value)))
        (t '(:failure "failure" ""))))

(defun h2-computation-number (real imag)
  (if (h2-computation-true-p imag)
      (proof-with-checked-results
          ((real-datum (h2-computation-encode real))
           (imag-datum (h2-computation-encode imag)))
        (list "complex" real-datum imag-datum))
    (h2-computation-encode real)))

(defun h2-computation-boolean (value)
  (if (h2-computation-true-p value) *proof-t* *proof-nil*))

(defun h2-computation-contents (value)
  (cond ((not (proof-compound value)) nil)
        ((equal (h2-computation-tag (car (last value))) "dot")
         (seq-slice value 0 -1))
        (t value)))

(defun h2-computation-index (value index)
  (cond ((stringp value)
         (if (< index (length value))
             (char-code (char value index))
           '(:failure "tactic-inapplicable" "")))
        ((eq value t)
         '(:failure "tactic-inapplicable" ""))
        (t (proof-term-at value index))))

(defun h2-computation-bytes-to-chars (bytes)
  (if (endp bytes)
      nil
    (cons (list "char" (char-code (car bytes)))
          (h2-computation-bytes-to-chars (cdr bytes)))))

(defun h2-computation-byte-codes (bytes)
  (if (endp bytes)
      nil
    (cons (char-code (car bytes)) (h2-computation-byte-codes (cdr bytes)))))

(defun h2-computation-chars-to-bytes (items)
  (if (endp items)
      nil
    (proof-with-checked-results
        ((value (if (equal (h2-computation-tag (car items)) "char")
                    (h2-computation-index (car items) 1)
                  0)))
      (let ((code (if (eq value t) 1 value)))
        (cond ((not (integerp code))
               '(:failure "tactic-inapplicable" ""))
              ((or (< code 0) (< 255 code))
               '(:failure "tactic-inapplicable" ""))
              (t
               (proof-with-checked-results
                   ((rest (h2-computation-chars-to-bytes (cdr items))))
                 (cons (code-char code) rest))))))))

(defun h2-computation-coerce-to-list (x kind)
  (if (equal kind "str")
      (proof-with-checked-results ((bytes (h2-computation-index x 1)))
        (if (stringp bytes)
            (or (h2-computation-bytes-to-chars (coerce bytes 'list)) *proof-nil*)
          '(:failure "tactic-inapplicable" "")))
    *proof-nil*))

(defun h2-computation-numeric-primitive (name x y)
  (proof-with-checked-results
      ((left (h2-computation-components x))
       (left (proof-list-of-length left 2))
       (right (h2-computation-components y))
       (right (proof-list-of-length right 2)))
    (let ((xr (car left)) (xi (cadr left))
          (yr (car right)) (yi (cadr right)))
      (cond ((equal name "BINARY-+")
             (if (and (rationalp xr) (rationalp xi) (rationalp yr) (rationalp yi))
                 (h2-computation-number (+ xr yr) (+ xi yi))
               '(:failure "tactic-inapplicable" "")))
            ((equal name "BINARY-*")
             (if (and (rationalp xr) (rationalp xi) (rationalp yr) (rationalp yi))
                 (h2-computation-number (- (* xr yr) (* xi yi)) (+ (* xr yi) (* xi yr)))
               '(:failure "tactic-inapplicable" "")))
            ((equal name "UNARY--")
             (if (and (rationalp xr) (rationalp xi))
                 (h2-computation-number (- xr) (- xi))
               '(:failure "tactic-inapplicable" "")))
            ((equal name "UNARY-/")
             (if (and (rationalp xr) (rationalp xi))
                 (let ((square (+ (* xr xr) (* xi xi))))
                   (if (equal square 0)
                       0
                     (h2-computation-number (/ xr square) (/ (- xi) square))))
               '(:failure "tactic-inapplicable" "")))
            ((equal xr yr)
             (if (equal xi yi)
                 *proof-nil*
               (if (and (rationalp xi) (rationalp yi))
                   (h2-computation-boolean (< xi yi))
                 '(:failure "tactic-inapplicable" ""))))
            ((and (rationalp xr) (rationalp yr))
             (h2-computation-boolean (< xr yr)))
            (t '(:failure "tactic-inapplicable" ""))))))

(defun h2-computation-package-get (name packages)
  (let ((entry (assoc-equal name packages)))
    (if entry
        (cdr entry)
      '(:failure "tactic-inapplicable" ""))))

(defun h2-computation-intern-import (name imports default)
  (if (endp imports)
      default
    (proof-with-checked-results
        ((symbol-name (h2-computation-index (car imports) 2)))
      (if (equal symbol-name name)
          (car imports)
        (h2-computation-intern-import name (cdr imports) default)))))

(defun h2-computation-intern (x y packages)
  (proof-with-checked-results
      ((package (h2-computation-index y 1))
       (info (h2-computation-package-get package packages))
       (info (proof-list-of-length info 2))
       (name (h2-computation-index x 1)))
    (h2-computation-intern-import name (car info) (list "sym" package name))))

(defun h2-computation-package-primitive (name x kind packages)
  (let ((imports-p (equal name "PKG-IMPORTS")))
    (if (not (equal kind "str"))
        (if imports-p *proof-nil* (proof-sym "ACL2-PKG-WITNESS" "ACL2"))
      (proof-with-checked-results ((package (h2-computation-index x 1)))
        (let ((entry (assoc-equal package packages)))
          (if (not entry)
              '(:failure "unproved" "")
            (proof-with-checked-results ((hidden (h2-computation-index (cdr entry) 1)))
              (cond ((h2-computation-true-p hidden)
                     '(:failure "unproved" ""))
                    (imports-p (or (cadr entry) *proof-nil*))
                    (t (list "sym" package "ACL2-PKG-WITNESS"))))))))))

(defun h2-computation-symbol-package (x kind packages)
  (if (not (equal kind "sym"))
      (list "str" "")
    (proof-with-checked-results
        ((package (h2-computation-index x 1))
         (info (h2-computation-package-get package packages))
         (hidden (h2-computation-index info 1)))
      (if (h2-computation-true-p hidden)
          '(:failure "unproved" "")
        (list "str" package)))))

(defun h2-computation-primitive-name (name args packages)
  (proof-with-checked-results ((x (h2-computation-index args 0)))
    (let ((y (if (consp (cdr args)) (cadr args) *proof-nil*))
          (kind (h2-computation-tag x)))
      (cond
       ((equal name "ACL2-NUMBERP")
        (proof-with-checked-results ((rational (h2-computation-rational x)))
          (h2-computation-boolean (or (not (null rational)) (equal kind "complex")))))
       ((equal name "BAD-ATOM<=") *proof-nil*)
       ((member-equal name '("BINARY-+" "BINARY-*" "UNARY--" "UNARY-/" "<"))
        (h2-computation-numeric-primitive name x y))
       ((equal name "CAR")
        (if (and (proof-compound x) (consp x)) (car x) *proof-nil*))
       ((equal name "CDR")
        (cond ((or (not (proof-compound x)) (endp x)) *proof-nil*)
              ((and (equal (len x) 2) (equal (h2-computation-tag (cadr x)) "dot"))
               (h2-computation-index (cadr x) 1))
              (t (or (cdr x) *proof-nil*))))
       ((equal name "CHAR-CODE")
        (if (equal kind "char") (h2-computation-index x 1) 0))
       ((equal name "CHARACTERP") (h2-computation-boolean (equal kind "char")))
       ((equal name "CODE-CHAR")
        (list "char" (cond ((eq x t) t)
                           ((and (integerp x) (<= 0 x) (<= x 255)) x)
                           (t 0))))
       ((equal name "COMPLEX")
        (proof-with-checked-results
            ((real (h2-computation-rational x))
             (imag (h2-computation-rational y)))
          (h2-computation-number (or real 0) (or imag 0))))
       ((equal name "COMPLEX-RATIONALP") (h2-computation-boolean (equal kind "complex")))
       ((equal name "COERCE")
        (if (equal y (proof-cl "LIST"))
            (h2-computation-coerce-to-list x kind)
          (proof-with-checked-results
              ((bytes (h2-computation-chars-to-bytes (h2-computation-contents x))))
            (list "str" (coerce bytes 'string)))))
       ((equal name "CONS")
        (cons x (cond ((equal y *proof-nil*) nil)
                      ((proof-compound y) y)
                      (t (list (list "dot" y))))))
       ((equal name "CONSP") (h2-computation-boolean (and (proof-compound x) (consp x))))
       ((equal name "DENOMINATOR")
        (proof-with-checked-results ((rational (h2-computation-rational x)))
          (denominator (or rational 0))))
       ((equal name "EQUAL") (h2-computation-boolean (equal x y)))
       ((equal name "IF")
        (if (equal x *proof-nil*) (h2-computation-index args 2) y))
       ((equal name "IMAGPART")
        (proof-with-checked-results
            ((parts (h2-computation-components x))
             (imag (h2-computation-index parts 1)))
          (h2-computation-encode imag)))
       ((equal name "INTEGERP") (h2-computation-boolean (h2-computation-integer-or-true-p x)))
       ((equal name "INTERN-IN-PACKAGE-OF-SYMBOL")
        (if (and (equal kind "str") (equal (h2-computation-tag y) "sym"))
            (h2-computation-intern x y packages)
          *proof-nil*))
       ((equal name "NUMERATOR")
        (proof-with-checked-results ((rational (h2-computation-rational x)))
          (numerator (or rational 0))))
       ((member-equal name '("PKG-IMPORTS" "PKG-WITNESS"))
        (h2-computation-package-primitive name x kind packages))
       ((equal name "RATIONALP")
        (proof-with-checked-results ((rational (h2-computation-rational x)))
          (h2-computation-boolean (not (null rational)))))
       ((equal name "REALPART")
        (proof-with-checked-results
            ((parts (h2-computation-components x))
             (real (h2-computation-index parts 0)))
          (h2-computation-encode real)))
       ((equal name "STRINGP") (h2-computation-boolean (equal kind "str")))
       ((equal name "SYMBOL-NAME")
        (proof-with-checked-results
            ((symbol-name (if (equal kind "sym") (h2-computation-index x 2) "")))
          (list "str" symbol-name)))
       ((equal name "SYMBOL-PACKAGE-NAME") (h2-computation-symbol-package x kind packages))
       ((equal name "SYMBOLP") (h2-computation-boolean (equal kind "sym")))
       (t '(:failure "unproved" ""))))))

(defun h2-computation-ascii-chars-p (chars)
  (or (endp chars)
      (and (< (char-code (car chars)) 128)
           (h2-computation-ascii-chars-p (cdr chars)))))

(defun h2-computation-primitive-value (function args packages)
  (proof-with-checked-results ((name (h2-computation-index function 2)))
    (cond ((not (stringp name)) '(:failure "failure" ""))
          ((h2-computation-ascii-chars-p (coerce name 'list))
           (h2-computation-primitive-name name args packages))
          (t '(:failure "tactic-inapplicable" "")))))

(defun h2-computation-evaluation-stop-p (value)
  (or (failure-p value) (h2-search-request-p value)))

(defun h2-computation-evaluate-memoize (root result)
  (if (h2-computation-evaluation-stop-p (car result))
      result
    (list (car result) (cadr result)
          (table-put (caddr result) root (car result)))))

(defun h2-computation-evaluate-primitive-args (args)
  (if (endp args)
      nil
    (proof-with-checked-results
        ((value (h2-computation-index (car args) 1))
         (rest (h2-computation-evaluate-primitive-args (cdr args))))
      (cons value rest))))

(defun h2-computation-evaluate-compute (proof fn call packages)
  (proof-with-checked-results
      ((args (h2-computation-evaluate-primitive-args (cdr call)))
       (datum (h2-computation-primitive-value fn args packages)))
    (proof-proof-compute proof call datum)))

(defun h2-computation-evaluate-error (fuel memo)
  (list '(:failure "fuel" "h2-computation-evaluate-error") fuel memo))

(defun h2-computation-evaluate-rewrite (proof root current child index)
  (if (not child)
      current
    (proof-with-checked-results
        ((step (or current (proof-proof-reflexive proof root))))
      (proof-proof-rewrite proof step child (list 1 2 index)))))

(defun h2-computation-evaluate-select (search root first)
  (let* ((proof (h2-book-logic-proof search))
         (current (h2-computation-evaluate-rewrite proof root nil first 1)))
    (proof-with-checked-results
        ((current current)
         (conditional (if current (h2-book-logic-first-at current 2) root))
         (test (h2-computation-index conditional 1)))
      (let ((truth (h2-search-search-truth search test (h2-search-context-init) nil)))
        (cond ((h2-computation-evaluation-stop-p truth) truth)
              ((not (car truth)) '(:failure "failure" ""))
              (t
               (proof-with-checked-results
                   ((selected (proof-proof-select proof conditional (car truth))))
                 (if current
                     (proof-proof-chain proof current (list selected))
                   selected))))))))

(mutual-recursion
 (defun h2-computation-evaluate-value (n search root packages fuel memo)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (h2-computation-evaluate-error fuel memo))
    ((proof-is-call root *proof-quote*) (list nil fuel memo))
    (t
     (let ((previous (assoc-equal root memo)))
       (if previous
           (list (cdr previous) fuel memo)
         (let ((fuel (if (and fuel (not (eq fuel :none))) (1- fuel) fuel)))
           (if (and (integerp fuel) (< fuel 0))
               (list '(:failure "unproved" "") fuel memo)
             (let* ((proof (h2-book-logic-proof search))
                    (fn (h2-computation-index root 0))
                    (result
                     (cond
                      ((failure-p fn) (list fn fuel memo))
                      ((or (proof-compound fn) (equal fn (proof-sym "RETURN-LAST" "ACL2")))
                       (h2-computation-evaluate-opened
                        (1- n) search
                        (if (proof-compound fn)
                            (proof-proof-beta proof root)
                          (proof-proof-unfold proof root))
                        packages fuel memo))
                      ((equal fn *proof-if*)
                       (let ((test (h2-computation-index root 1)))
                         (if (failure-p test)
                             (list test fuel memo)
                           (let ((first (h2-computation-evaluate-value
                                         (1- n) search test packages fuel memo)))
                             (if (h2-computation-evaluation-stop-p (car first))
                                 first
                               (h2-computation-evaluate-opened
                                (1- n) search
                                (h2-computation-evaluate-select search root (car first))
                                packages (cadr first) (caddr first)))))))
                      (t
                       (h2-computation-evaluate-call (1- n) search root fn packages fuel memo)))))
               (h2-computation-evaluate-memoize root result)))))))))

 (defun h2-computation-evaluate-opened (n search opening packages fuel memo)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (h2-computation-evaluate-error fuel memo))
    ((h2-computation-evaluation-stop-p opening) (list opening fuel memo))
    (t
     (let ((right (h2-book-logic-first-at opening 2)))
       (if (failure-p right)
           (list right fuel memo)
         (let* ((child (h2-computation-evaluate-value (1- n) search right packages fuel memo))
                (step (car child)))
           (if (h2-computation-evaluation-stop-p step)
               child
             (list (proof-proof-chain (h2-book-logic-proof search) opening (list step))
                   (cadr child) (caddr child)))))))))

 (defun h2-computation-evaluate-arguments (n search root arguments index current packages fuel memo)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (h2-computation-evaluate-error fuel memo))
    ((endp arguments) (list current fuel memo))
    (t
     (let ((child (h2-computation-evaluate-value (1- n) search (car arguments) packages fuel memo)))
       (if (h2-computation-evaluation-stop-p (car child))
           child
         (let ((rewritten (h2-computation-evaluate-rewrite
                           (h2-book-logic-proof search) root current (car child) index)))
           (if (failure-p rewritten)
               (list rewritten (cadr child) (caddr child))
             (h2-computation-evaluate-arguments
              (1- n) search root (cdr arguments) (1+ index) rewritten packages
              (cadr child) (caddr child)))))))))

 (defun h2-computation-evaluate-call (n search root fn packages fuel memo)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (h2-computation-evaluate-error fuel memo)
     (let* ((proof (h2-book-logic-proof search))
            (arguments (if (stringp root)
                           (h2-computation-byte-codes (coerce (subseq root 1 nil) 'list))
                         (cdr root)))
            (children (h2-computation-evaluate-arguments
                       (1- n) search root arguments 1 nil packages fuel memo))
            (current (car children))
            (fuel (cadr children))
            (memo (caddr children)))
       (if (h2-computation-evaluation-stop-p current)
           children
         (let* ((call (if current (h2-book-logic-first-at current 2) root))
                (opened
                 (cond
                  ((failure-p call) (list call fuel memo))
                  ((member-equal fn (proof-proof-primitives proof))
                   (list (h2-computation-evaluate-compute proof fn call packages) fuel memo))
                  ((assoc-equal fn (proof-proof-definitions proof))
                   (h2-computation-evaluate-opened
                    (1- n) search (proof-proof-unfold proof call) packages fuel memo))
                  (t (list '(:failure "unproved" "")
                           fuel memo)))))
           (if (or (not current) (h2-computation-evaluation-stop-p (car opened)))
               opened
             (list (proof-proof-chain proof current (list (car opened)))
                   (cadr opened) (caddr opened)))))))))

(defun h2-computation-evaluate (search term packages fuel)
  (let ((result (h2-computation-evaluate-value 1000000 search term packages fuel nil)))
    (cons (or (car result) (proof-proof-reflexive (h2-book-logic-proof search) term))
          (cadr result))))
