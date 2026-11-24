(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b2-bounds-comparison (term)
  (cond ((proof-is-call term *proof-less*)
         (proof-with-checked-results ((lower (proof-term-at term 1))
                                      (upper (proof-term-at term 2)))
           (list lower upper t)))
        ((proof-is-call term *proof-not*)
         (proof-with-checked-results ((inner (proof-term-at term 1)))
           (and (proof-is-call inner *proof-less*)
                (proof-with-checked-results ((lower (proof-term-at inner 2))
                                             (upper (proof-term-at inner 1)))
                  (list lower upper nil)))))
        (t nil)))

(defun b2-bounds-increment (counts term increment)
  (table-put counts term (+ (table-get counts term 0) increment)))

(mutual-recursion
 (defun b2-bounds-coefficients-collect (node sign counts)
   (declare (xargs :measure (1+ (* 2 (acl2-count node)))))
   (cond ((proof-is-call node *proof-plus*)
          (b2-bounds-coefficients-collect-arguments (cdr node) sign counts))
         ((proof-is-call node *proof-minus*)
          (if (consp (cdr node))
              (b2-bounds-coefficients-collect (cadr node) (- sign) counts)
            '(:failure "tactic-rejected" "")))
         ((proof-is-call node *proof-quote*)
          (proof-with-checked-results ((datum (proof-term-at node 1)))
            (cond ((integerp datum)
                   (b2-bounds-increment counts :none (* sign datum)))
                  ((eq datum t) (b2-bounds-increment counts :none sign))
                  (t (b2-bounds-increment counts node sign)))))
         (t (b2-bounds-increment counts node sign))))
 (defun b2-bounds-coefficients-collect-arguments (args sign counts)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       counts
     (proof-with-checked-results
         ((counts (b2-bounds-coefficients-collect (car args) sign counts)))
       (b2-bounds-coefficients-collect-arguments (cdr args) sign counts)))))

(defun b2-bounds-coefficient-counts (term)
  (b2-bounds-coefficients-collect term 1 nil))

(defun b2-bounds-coefficients-data (counts)
  (if (endp counts)
      nil
    (cons (if (eq (caar counts) :none) (cons nil (cdar counts)) (car counts))
          (b2-bounds-coefficients-data (cdr counts)))))

(defun b2-bounds-coefficients (term)
  (proof-with-checked-results ((counts (b2-bounds-coefficient-counts term)))
    (b2-bounds-coefficients-data counts)))

(defun b2-bounds-add-signs (lib first second evidence)
  (declare (xargs :measure (if (caddr first) 1 0)))
  (proof-with-checked-results
      ((first-parts (proof-list-of-length first 3))
       (second-parts (proof-list-of-length second 3)))
    (let ((a (car first-parts))
          (p (cadr first-parts))
          (b (car second-parts))
          (q (cadr second-parts)))
      (cond ((and (caddr first) (caddr second))
             (proof-with-checked-results
                 ((step (library-library-cite lib "POSITIVE-SUM"
                                              (list a b) (list p q))))
               (list (library-plus a b) step t)))
            ((caddr first) (b2-bounds-add-signs lib second first evidence))
            (t (proof-with-checked-results
                   ((a-integer (library-library-type-of lib a evidence))
                    (b-integer (library-library-type-of lib b evidence))
                    (step (library-library-cite
                           lib (if (caddr second)
                                   "POSITIVE-PLUS-NONNEGATIVE"
                                 "NONNEGATIVE-SUM")
                           (list a b)
                           (if (caddr second)
                               (list a-integer b-integer q p)
                             (list a-integer b-integer p q)))))
                 (list (library-plus b a) step (caddr second))))))))

(defun b2-bounds-unusable-bound-p (result)
  (and (failure-p result)
       (member-equal (cadr result) '("value" "Unproved"))))

(defun b2-bounds-type-bounds (lib lower upper evidence)
  (let ((lower-type (library-library-type-of lib lower evidence)))
    (if (failure-p lower-type)
        lower-type
      (library-library-type-of lib upper evidence))))

(defun b2-bounds-bound-source (lib item step evidence)
  (let* ((proof (library-library-proof lib))
         (low (car item))
         (high (cadr item))
         (strong (caddr item))
         (typed (b2-bounds-type-bounds lib low high evidence)))
    (cond ((b2-bounds-unusable-bound-p typed) nil)
          ((failure-p typed) typed)
          (t (proof-with-checked-results
                 ((equation (if strong
                                (library-library-comparison lib low high evidence)
                              (library-library-axiom lib "<-ON-OTHERS" (list high low))))
                  (rewritten (proof-proof-rewrite proof step equation
                                                  (if strong '(1) '(1 1))))
                  (bound (proof-proof-tidy proof rewritten)))
               (list (library-diff high low) bound strong))))))

(defun b2-bounds-sources (lib pending evidence count)
  (if (endp pending)
      nil
    (proof-with-checked-results
        ((literal (proof-step-first (car pending)))
         (item (b2-bounds-comparison literal))
         (source (and item (< count 8)
                      (b2-bounds-bound-source lib item (car pending) evidence)))
         (rest (b2-bounds-sources lib (cdr pending) evidence
                                 (if source (1+ count) count))))
      (if source (cons source rest) rest))))

(defun b2-bounds-subtract-coefficients (counts parts)
  (if (endp parts)
      counts
    (b2-bounds-subtract-coefficients
     (b2-bounds-increment counts (caar parts) (- (cdar parts)))
     (cdr parts))))

(defun b2-bounds-remaining-coefficients (parts counts)
  (if (endp parts)
      counts
    (proof-with-checked-results ((part (b2-bounds-coefficient-counts (caar parts))))
      (b2-bounds-remaining-coefficients
       (cdr parts) (b2-bounds-subtract-coefficients counts part)))))

(defun b2-bounds-nonconstant-p (counts)
  (and (consp counts)
       (or (and (not (eq (caar counts) :none)) (not (equal (cdar counts) 0)))
           (b2-bounds-nonconstant-p (cdr counts)))))

(defun b2-bounds-strong-part-p (parts)
  (and (consp parts)
       (or (caddar parts) (b2-bounds-strong-part-p (cdr parts)))))

(defun b2-bounds-prove-integer-bound-combine (parts constant a b strict lib evidence)
  (proof-with-checked-results
      ((result (if (equal (len parts) 2)
                   (b2-bounds-add-signs lib (car parts) (cadr parts) evidence)
                 (proof-term-at parts 0)))
       (result (if (equal constant 0)
                   result
                 (let ((term (proof-quote constant)))
                   (proof-with-checked-results
                       ((positive (b2-tactics-tactics-solve lib (library-positive term)
                                                           nil nil nil 0 nil)))
                     (b2-bounds-add-signs lib result (list term positive t) evidence)))))
       (bound (if (and (caddr result) (not strict))
                  (proof-with-checked-results
                      ((typed (library-library-type-of lib (car result) evidence)))
                    (library-library-cite lib "POSITIVE-NONNEGATIVE" (list (car result))
                                          (list typed (cadr result))))
                (cadr result))))
    (if strict
        (b2-tactics-tactics-less-from-difference lib a b bound evidence)
      (b2-tactics-tactics-weak-from-difference lib a b bound evidence))))

(defun b2-bounds-prove-integer-bound-attempt (parts want a b strict lib evidence)
  (proof-with-checked-results
      ((remaining (b2-bounds-remaining-coefficients parts want)))
    (let ((constant (table-get remaining :none 0)))
      (cond ((or (b2-bounds-nonconstant-p remaining) (< constant 0)) nil)
            ((and strict (equal constant 0) (not (b2-bounds-strong-part-p parts))) nil)
            (t (let ((result (b2-bounds-prove-integer-bound-combine
                             parts constant a b strict lib evidence)))
                 (if (b2-bounds-unusable-bound-p result) nil result)))))))

(defun b2-bounds-try-singles (sources want a b strict lib evidence)
  (if (endp sources)
      nil
    (let ((result (b2-bounds-prove-integer-bound-attempt
                   (list (car sources)) want a b strict lib evidence)))
      (or result (b2-bounds-try-singles (cdr sources) want a b strict lib evidence)))))

(defun b2-bounds-try-pairs-with (first sources want a b strict lib evidence)
  (if (endp sources)
      nil
    (let ((result (b2-bounds-prove-integer-bound-attempt
                   (list first (car sources)) want a b strict lib evidence)))
      (or result (b2-bounds-try-pairs-with first (cdr sources)
                                          want a b strict lib evidence)))))

(defun b2-bounds-try-pairs (sources want a b strict lib evidence)
  (if (endp sources)
      nil
    (or (b2-bounds-try-pairs-with (car sources) sources want a b strict lib evidence)
        (b2-bounds-try-pairs (cdr sources) want a b strict lib evidence))))

(defun b2-bounds-prove-integer-bound (lib target evidence)
  (proof-with-checked-results ((decoded (b2-bounds-comparison target)))
    (if (not decoded)
        '(:failure "Unproved" "")
      (let ((a (car decoded)) (b (cadr decoded)) (strict (caddr decoded)))
        (let ((typed (b2-bounds-type-bounds lib a b evidence)))
          (if (failure-p typed)
              typed
            (proof-with-checked-results
                ((want (b2-bounds-coefficient-counts (library-diff b a)))
                 (sources (b2-bounds-sources lib evidence evidence 0))
                 (zero (library-library-axiom lib "ZERO" nil)))
              (or (b2-bounds-try-singles
                   (append sources (list (list *proof-zero* zero nil)))
                   want a b strict lib evidence)
                  (b2-bounds-try-pairs sources want a b strict lib evidence)
                  '(:failure "Unproved" "")))))))))
