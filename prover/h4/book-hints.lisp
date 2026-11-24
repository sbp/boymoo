(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h4-book-hints-use* (proof-sym "USE" "KEYWORD"))
(defconst *h4-book-hints-instance* (proof-sym "INSTANCE" "KEYWORD"))
(defconst *h4-book-hints-divide* (proof-sym "UNARY-/" "ACL2"))

(mutual-recursion
 (defun h4-book-hints-applications (item)
   (declare (xargs :measure (1+ (* 2 (acl2-count item)))))
   (cond ((or (not (proof-compound item))
              (proof-is-call item *h4-book-hints-instance*))
          (list item))
         ((and (consp item) (consp (car item))
               (not (proof-compound (car item))))
          (proof-with-checked-results ((package (proof-term-at (car item) 1)))
            (if (equal package "KEYWORD")
                nil
              (h4-book-hints-applications-list item))))
         (t (h4-book-hints-applications-list item))))

 (defun h4-book-hints-applications-list (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (proof-with-checked-results
      ((first (h4-book-hints-applications (car items)))
       (rest (h4-book-hints-applications-list (cdr items))))
      (append first rest)))))

(defun h4-book-hints-name-uses (name uses)
  (if (endp uses)
      nil
    (cons (list name (car uses))
          (h4-book-hints-name-uses name (cdr uses)))))

(defun h4-book-hints-hint-items (name items)
  (declare (xargs :measure (acl2-count items)))
  (if (or (endp items) (endp (cdr items)))
      nil
    (proof-with-checked-results
     ((uses (if (equal (car items) *h4-book-hints-use*)
                (h4-book-hints-applications (cadr items))
              nil))
      (rest (h4-book-hints-hint-items name (cdr items))))
     (append (h4-book-hints-name-uses name uses) rest))))

(defun h4-book-hints-hint-list (name hints)
  (if (endp hints)
      nil
    (proof-with-checked-results
     ((uses (if (proof-compound (car hints))
                (h4-book-hints-hint-items name (car hints))
              nil))
      (rest (h4-book-hints-hint-list name (cdr hints))))
     (append uses rest))))

(defun h4-book-hints-line-uses (raw)
  (if (and (text-starts-with raw "(hints ")
           (<= 0 (text-find raw "KEYWORD::USE ")))
      (proof-with-checked-results
       ((parsed (reader-reader-line
                 (reader-reader (text-strip-right raw (coerce '(#\Newline) 'string)))))
        (fields (proof-list-of-length (cadar parsed) 2)))
       (if (proof-compound (cadr fields))
           (h4-book-hints-hint-list (car fields) (cadr fields))
         nil))
    nil))

(defun h4-book-hints-hint-uses (lines)
  (if (endp lines)
      nil
    (proof-with-checked-results
     ((first (h4-book-hints-line-uses (car lines)))
      (rest (h4-book-hints-hint-uses (cdr lines))))
     (append first rest))))

(defun h4-book-hints-source-atom (term)
  (if (and (consp term) (equal (car term) "sym")
           (not (equal term *proof-nil*))
           (not (equal term *proof-t*)))
      (proof-with-checked-results ((package (proof-term-at term 1)))
        (if (equal package "KEYWORD")
            (proof-quote term)
          (proof-with-checked-results ((name (proof-term-at term 2)))
            (if (text-starts-with name "*")
                '(:failure "UnusableHint" "")
              term))))
    (proof-quote term)))

(defun h4-book-hints-source-list (arguments)
  (if (endp arguments)
      *proof-false*
    (list *proof-cons* (car arguments)
          (h4-book-hints-source-list (cdr arguments)))))

(defun h4-book-hints-source-logic (arguments and-p)
  (cond ((endp arguments) (if and-p *proof-true* *proof-false*))
        ((endp (cdr arguments)) (car arguments))
        (t (let ((test (car arguments))
                 (rest (h4-book-hints-source-logic (cdr arguments) and-p)))
             (if and-p
                 (proof-ite test rest *proof-false*)
               (proof-ite test test rest))))))

(defun h4-book-hints-source-right (arguments binary identity)
  (cond ((endp arguments) identity)
        ((endp (cdr arguments)) (car arguments))
        (t (list binary (car arguments)
                 (h4-book-hints-source-right (cdr arguments) binary identity)))))

(defun h4-book-hints-source-left (left rest unary binary)
  (if (endp rest)
      left
    (h4-book-hints-source-left
     (list binary left (list unary (car rest)))
     (cdr rest) unary binary)))

(defun h4-book-hints-source-call (head arguments functions)
  (cond
   ((equal head (proof-cl "LIST"))
    (h4-book-hints-source-list arguments))
   ((equal head (proof-cl "AND"))
    (h4-book-hints-source-logic arguments t))
   ((equal head (proof-cl "OR"))
    (h4-book-hints-source-logic arguments nil))
   ((equal head (proof-cl "+"))
    (h4-book-hints-source-right arguments *proof-plus* *proof-zero*))
   ((equal head (proof-cl "*"))
    (h4-book-hints-source-right arguments *proof-times* *proof-one*))
   ((and (consp arguments)
         (or (equal head (proof-cl "-")) (equal head (proof-cl "/"))))
    (let* ((subtract (equal head (proof-cl "-")))
           (unary (if subtract *proof-minus* *h4-book-hints-divide*))
           (binary (if subtract *proof-plus* *proof-times*)))
      (if (endp (cdr arguments))
          (list unary (car arguments))
        (h4-book-hints-source-left (car arguments) (cdr arguments) unary binary))))
   ((and (equal (len arguments) 1)
         (or (equal head (proof-cl "1+")) (equal head (proof-cl "1-"))))
    (list *proof-plus*
          (if (equal head (proof-cl "1+")) *proof-one* *proof-neg-one*)
          (car arguments)))
   ((and (equal (len arguments) 2)
         (member-equal head (list (proof-cl "<=") (proof-cl ">=") (proof-cl ">"))))
    (let ((a (car arguments))
          (b (cadr arguments)))
      (cond ((equal head (proof-cl ">")) (list *proof-less* b a))
            ((equal head (proof-cl "<=")) (proof-neg (list *proof-less* b a)))
            (t (proof-neg (list *proof-less* a b))))))
   ((member-equal head functions) (cons head arguments))
   (t '(:failure "UnusableHint" ""))))

(mutual-recursion
 (defun h4-book-hints-source-term (term functions)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (h4-book-hints-source-atom term))
         ((proof-is-call term *proof-quote*) term)
         ((endp term)
          '(:failure "UnusableHint" ""))
         (t (proof-with-checked-results
             ((arguments (h4-book-hints-source-arguments (cdr term) functions)))
             (h4-book-hints-source-call (car term) arguments functions)))))

 (defun h4-book-hints-source-arguments (arguments functions)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
      ((first (h4-book-hints-source-term (car arguments) functions))
       (rest (h4-book-hints-source-arguments (cdr arguments) functions)))
      (cons first rest)))))

(defun h4-book-hints-instance-bindings (bindings functions)
  (if (endp bindings)
      nil
    (proof-with-checked-results
     ((pair (proof-list-of-length (car bindings) 2))
      (value (h4-book-hints-source-term (cadr pair) functions))
      (rest (h4-book-hints-instance-bindings (cdr bindings) functions)))
     (cons (list (car pair) value) rest))))

(defun h4-book-hints-fact-for-use (proof item functions)
  (cond ((assoc-equal item (proof-proof-facts proof))
         (proof-proof-fact proof item nil))
        ((and (proof-is-call item *h4-book-hints-instance*)
              (consp (cdr item))
              (assoc-equal (cadr item) (proof-proof-facts proof)))
         (let ((bindings (h4-book-hints-instance-bindings (cddr item) functions)))
           (cond ((failure-p bindings)
                  (if (member-equal (cadr bindings) '("UnusableHint" "value")) nil bindings))
                 ((no-duplicatesp-equal (strip-cars bindings))
                  (proof-proof-fact proof (cadr item) bindings))
                 (t nil))))
        (t nil)))

(defun h4-book-hints-facts-for-uses (proof uses functions)
  (if (endp uses)
      nil
    (proof-with-checked-results
     ((step (h4-book-hints-fact-for-use proof (car uses) functions))
      (rest (h4-book-hints-facts-for-uses proof (cdr uses) functions)))
     (if step (cons step rest) rest))))

(defun h4-book-hints-hint-facts (p uses book-functions)
  (let* ((proof (library-library-proof p))
         (functions (append (table-keys (proof-proof-definitions proof))
                            (proof-proof-primitives proof)
                            book-functions)))
    (h4-book-hints-facts-for-uses proof uses functions)))
