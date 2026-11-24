(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-witness-iff* (proof-sym "IFF" "ACL2"))

(mutual-recursion
 (defun h3-book-witness-replace-functions (term names)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond
    ((not (proof-compound term)) term)
    ((proof-is-call term *proof-quote*) term)
    ((endp term) '(:failure "failure" ""))
    ((proof-compound (car term))
     (if (endp (cddar term))
         '(:failure "failure" "")
       (proof-with-checked-results
        ((body (h3-book-witness-replace-functions (caddar term) names))
         (args (h3-book-witness-replace-arguments (cdr term) names)))
        (cons (list (caar term) (cadar term) body) args))))
    (t
     (proof-with-checked-results ((args (h3-book-witness-replace-arguments (cdr term) names)))
       (cons (table-get names (car term) (car term)) args)))))

 (defun h3-book-witness-replace-arguments (terms names)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (h3-book-witness-replace-functions (car terms) names))
       (rest (h3-book-witness-replace-arguments (cdr terms) names)))
      (cons first rest)))))

(mutual-recursion
 (defun h3-book-witness-mentions (term names)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
    ((endp term) '(:failure "failure" ""))
    ((member-equal (car term) names) t)
    ((proof-compound (car term))
     (if (endp (cddar term))
         '(:failure "failure" "")
       (let ((in-body (h3-book-witness-mentions (caddar term) names)))
         (or in-body (h3-book-witness-mentions-arguments (cdr term) names)))))
    (t (h3-book-witness-mentions-arguments (cdr term) names))))

 (defun h3-book-witness-mentions-arguments (terms names)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (and (consp terms)
        (or (h3-book-witness-mentions (car terms) names)
            (h3-book-witness-mentions-arguments (cdr terms) names)))))

(mutual-recursion
 (defun h3-book-witness-collect-variables (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((not (proof-compound term)) (list term))
         ((or (endp term) (proof-is-call term *proof-quote*)) nil)
         (t (h3-book-witness-collect-arguments (cdr term)))))

 (defun h3-book-witness-collect-arguments (terms)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       nil
     (append (h3-book-witness-collect-variables (car terms))
             (h3-book-witness-collect-arguments (cdr terms))))))

(defun h3-book-witness-escape-string (chars)
  (if (endp chars)
      nil
    (let ((char (car chars))
          (rest (h3-book-witness-escape-string (cdr chars))))
      (if (or (eql char #\") (eql char #\\))
          (cons #\\ (cons char rest))
        (cons char rest)))))

; Variable sets follow the lexical order of their written ACL2 objects.
(mutual-recursion
 (defun h3-book-witness-variable-key (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond ((stringp value)
          (coerce (cons #\" (append (h3-book-witness-escape-string (coerce value 'list))
                                     (list #\")))
                  'string))
         ((integerp value) (decimal-text value))
         ((rationalp value)
          (concatenate 'string (decimal-text (numerator value)) "/" (decimal-text (denominator value))))
         ((eq value t) "t")
         ((consp value)
          (concatenate 'string "(" (text-join " " (h3-book-witness-variable-keys value)) ")"))
         (t "()")))

 (defun h3-book-witness-variable-keys (values)
   (declare (xargs :measure (* 2 (acl2-count values))))
   (if (endp values)
       nil
     (cons (h3-book-witness-variable-key (car values))
           (h3-book-witness-variable-keys (cdr values))))))

(defun h3-book-witness-variable-pairs (variables)
  (if (endp variables)
      nil
    (cons (list (h3-book-witness-variable-key (car variables)) (car variables))
          (h3-book-witness-variable-pairs (cdr variables)))))

(defun h3-book-witness-pair-variables (pairs)
  (if (endp pairs)
      nil
    (cons (cadar pairs) (h3-book-witness-pair-variables (cdr pairs)))))

(defun h3-book-witness-variables (term)
  (h3-book-witness-pair-variables
   (seq-sorted (h3-book-witness-variable-pairs
               (proof-unique (h3-book-witness-collect-variables term))))))

(defun h3-book-witness-define (lib formals body)
  (let ((key (proof-write (list formals body))))
    (if (failure-p key)
        (cons key lib)
      (let* ((suffix (text-upper (seq-slice (siphash-hexdigest key) 0 16)))
             (name (proof-sym (string-append "H3-BOOK-WITNESS-" suffix) "ACL2"))
             (proof (library-library-proof lib)))
        (if (assoc-equal name (proof-proof-definitions proof))
            (cons name lib)
          (let ((updated (library-library-definition lib name formals body)))
            (if (failure-p updated) (cons updated lib) (cons name updated))))))))

(defun h3-book-witness-pair (value)
  (if (stringp value)
      (if (equal (length value) 2)
          (list (seq-slice value 0 1) (seq-slice value 1 2))
        '(:failure "failure" ""))
    (proof-list-of-length value 2)))

(defun h3-book-witness-atomic-arguments-p (args)
  (or (endp args)
      (and (not (proof-compound (car args)))
           (h3-book-witness-atomic-arguments-p (cdr args)))))

(defun h3-book-witness-equation-option (call body function arity constrained)
  (let ((args (cdr call)))
    (and (proof-is-call call function)
         (equal (len call) (+ arity 1))
         (h3-book-witness-atomic-arguments-p args)
         (equal (len (proof-unique args)) arity)
         (proof-with-checked-results ((mentioned (h3-book-witness-mentions body constrained)))
           (and (not mentioned) (list args body))))))

(defun h3-book-witness-equation-options (function arity formulas constrained)
  (if (endp formulas)
      nil
    (proof-with-checked-results
     ((named (h3-book-witness-pair (car formulas)))
      (term (cadr named))
      (conclusion (if (proof-is-call term *library-implies*) (proof-term-at term 2) term))
      (options
       (and (or (proof-is-call conclusion *proof-equal*)
                (proof-is-call conclusion *h3-book-witness-iff*))
         (proof-with-checked-results
          ((sides (h3-book-witness-pair (cdr conclusion)))
           (left (h3-book-witness-equation-option
                  (car sides) (cadr sides) function arity constrained))
           (right (h3-book-witness-equation-option
                   (cadr sides) (car sides) function arity constrained)))
          (append (and left (list left)) (and right (list right))))))
      (rest (h3-book-witness-equation-options function arity (cdr formulas) constrained)))
     (append options rest))))

(defun h3-book-witness-test-option (function term constrained)
  (and (proof-is-call term *library-implies*)
       (proof-with-checked-results ((parts (h3-book-witness-pair (cdr term))))
         (let ((given (car parts)) (conclusion (cadr parts)))
           (and (proof-compound given)
                (equal (len given) 2)
                (proof-is-call conclusion (car given))
                (proof-with-checked-results ((call (proof-term-at conclusion 1)))
                  (and (proof-is-call call function)
                       (proof-with-checked-results ((variable (proof-term-at call 1)))
                         (and (not (proof-compound variable))
                              (proof-with-checked-results
                               ((mentioned (h3-book-witness-mentions given constrained)))
                               (and (not mentioned)
                                    (list (list variable)
                                          (proof-ite (list (car given) variable)
                                                     variable (cadr given))))))))))))))

(defun h3-book-witness-test-options (function formulas constrained)
  (if (endp formulas)
      nil
    (proof-with-checked-results
     ((named (h3-book-witness-pair (car formulas)))
      (option (h3-book-witness-test-option function (cadr named) constrained))
      (rest (h3-book-witness-test-options function (cdr formulas) constrained)))
     (if option (cons option rest) rest))))

(defun h3-book-witness-equations-for (function arity formulas constrained)
  (proof-with-checked-results
   ((equations (h3-book-witness-equation-options function arity formulas constrained)))
   (if (equal arity 1)
       (proof-with-checked-results ((tests (h3-book-witness-test-options function formulas constrained)))
         (append equations tests))
     equations)))

(defun h3-book-witness-formals (indices)
  (if (endp indices)
      nil
    (cons (proof-sym (string-append "H3-ARG-" (decimal-text (car indices))) "ACL2")
          (h3-book-witness-formals (cdr indices)))))

(defun h3-book-witness-bodies (formals bodies)
  (if (endp bodies)
      nil
    (cons (list formals (car bodies))
          (h3-book-witness-bodies formals (cdr bodies)))))

(defun h3-book-witness-available (lib options)
  (declare (xargs :measure (acl2-count options)))
  (if (endp options)
      (cons nil lib)
    (let* ((formals (caar options))
           (body (cadar options)))
      (if (not (subsetp-equal (h3-book-witness-variables body) formals))
          (h3-book-witness-available lib (cdr options))
        (let ((defined (h3-book-witness-define lib formals body)))
          (if (failure-p (car defined))
              defined
            (let ((rest (h3-book-witness-available (cdr defined) (cdr options))))
              (if (failure-p (car rest))
                  rest
                (cons (cons (car defined) (car rest)) (cdr rest))))))))))

(defun h3-book-witness-options (lib functions formulas constrained)
  (declare (xargs :measure (acl2-count functions)))
  (if (endp functions)
      (cons nil lib)
    (let ((function (h3-book-witness-pair (car functions))))
      (cond
       ((failure-p function) (cons function lib))
       ((> (cadr function) 3)
        (cons *h3-rewrite-unproved* lib))
       (t
        (let* ((arity (cadr function))
               (formals (h3-book-witness-formals (seq-range 0 arity 1)))
               (inferred (h3-book-witness-equations-for (car function) arity formulas constrained)))
          (if (failure-p inferred)
              (cons inferred lib)
            (let ((available (h3-book-witness-available
                              lib (append inferred (h3-book-witness-bodies
                                                    formals (list* *proof-true* *proof-false* formals))))))
              (if (failure-p (car available))
                  available
                (let* ((choices (if (equal arity 2)
                                    (append (car available) (list *proof-equal*))
                                  (car available)))
                       (rest (h3-book-witness-options (cdr available) (cdr functions)
                                                      formulas constrained)))
                  (if (failure-p (car rest))
                      rest
                    (cons (cons (proof-unique choices) (car rest)) (cdr rest)))))))))))))

(defun h3-book-witness-function-names (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
     ((item (h3-book-witness-pair (car functions)))
      (rest (h3-book-witness-function-names (cdr functions))))
     (cons (car item) rest))))

(defun h3-book-witness-product-prepend (choice tails limit)
  (if (or (zp limit) (endp tails))
      nil
    (cons (cons choice (car tails))
          (h3-book-witness-product-prepend choice (cdr tails) (1- limit)))))

(defun h3-book-witness-product-heads (choices tails limit)
  (if (or (zp limit) (endp choices) (endp tails))
      nil
    (let ((first (h3-book-witness-product-prepend (car choices) tails limit)))
      (append first
              (h3-book-witness-product-heads (cdr choices) tails (- limit (len first)))))))

(defun h3-book-witness-product (options limit)
  (cond ((zp limit) nil)
        ((endp options) (list nil))
        (t (h3-book-witness-product-heads
            (car options) (h3-book-witness-product (cdr options) limit) limit))))

(defun h3-book-witness-selected-names (functions selected names)
  (if (or (endp functions) (endp selected))
      names
    (h3-book-witness-selected-names (cdr functions) (cdr selected)
                                    (table-put names (car functions) (car selected)))))

(defun h3-book-witness-try-formulas (lib formulas names selected replies proofs)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      (list (reverse proofs) lib replies)
    (let* ((named (h3-book-witness-pair (car formulas)))
           (instance (if (failure-p named)
                         named
                       (h3-book-witness-replace-functions (cadr named) names))))
      (cond
       ((failure-p instance) (list instance lib replies))
       ((endp replies) (list (list :request instance selected) lib nil))
       (t
        (let* ((reply (car replies))
               (result (car reply))
               (lib (cdr reply))
               (replies (cdr replies)))
          (cond
           ((or (h3-rewrite-unproved-p result)
                (and (failure-p result) (equal (cadr result) "assertion")))
            (list :none lib replies))
           ((failure-p result) (list result lib replies))
           ((not (proof-step-p result))
            (list '(:failure "failure" "")
                  lib replies))
           ((not (equal (proof-step-clause result) (list instance)))
            (list :none lib replies))
           (t (h3-book-witness-try-formulas
               lib (cdr formulas) names selected replies (cons result proofs))))))))))

(defun h3-book-witness-try-options (lib function-names formulas candidates replies)
  (declare (xargs :measure (acl2-count candidates)))
  (if (endp candidates)
      (cons *h3-rewrite-unproved* lib)
    (let* ((selected (car candidates))
           (names (h3-book-witness-selected-names function-names selected nil))
           (tried (h3-book-witness-try-formulas lib formulas names selected replies nil))
           (result (car tried))
           (lib (cadr tried)))
      (cond
       ((eq result :none)
        (h3-book-witness-try-options lib function-names formulas (cdr candidates) (caddr tried)))
       ((or (failure-p result) (and (consp result) (eq (car result) :request)))
        (cons result lib))
       ((endp function-names) (cons '(:failure "failure" "") lib))
       (t
        (let ((head (car function-names)))
          (cons (proof-proof-entry "witness" head (cons head selected) result) lib)))))))

(defun h3-book-witness-prepare (lib fields)
  (let ((fields (h3-book-witness-pair fields)))
    (if (failure-p fields)
        (cons fields lib)
      (let ((functions (car fields)) (formulas (cadr fields)))
        (if (or (> (len formulas) 5) (> (len functions) 3))
            (cons *h3-rewrite-unproved* lib)
          (let ((names (h3-book-witness-function-names functions)))
            (if (failure-p names)
                (cons names lib)
              (let ((options (h3-book-witness-options lib functions formulas (proof-unique names))))
                (if (failure-p (car options))
                    options
                  (cons (list names formulas (h3-book-witness-product (car options) 28))
                        (cdr options)))))))))))

(defun h3-book-witness-witness-proof (lib fields prove)
  (let ((prepared (h3-book-witness-prepare lib fields)))
    (if (failure-p (car prepared))
        prepared
      (h3-book-witness-try-options (cdr prepared) (caar prepared) (cadar prepared)
                                  (caddar prepared) prove))))
