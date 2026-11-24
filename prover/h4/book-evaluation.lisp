(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-evaluation-tail* (proof-sym "H4-EVALUATION-TAIL" "ACL2"))

(mutual-recursion
 (defun h4-book-evaluation-closed (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (or (proof-is-call term *proof-quote*)
       (and (proof-compound term)
            (h4-book-evaluation-closed-arguments (cdr term)))))
 (defun h4-book-evaluation-closed-arguments (arguments)
   (declare (xargs :measure (* 2 (acl2-count arguments))))
   (or (endp arguments)
       (and (h4-book-evaluation-closed (car arguments))
            (h4-book-evaluation-closed-arguments (cdr arguments))))))

(defun h4-book-evaluation-closed-evaluation-p (evaluation)
  (cadr evaluation))

(defun h4-book-evaluation-closed-evaluation-constructor (evaluation)
  (caddr evaluation))

(defun h4-book-evaluation-closed-evaluation-init (p)
  (proof-with-checked-results
      ((constructor (h4-book-finite-constructor-test p)))
    (list :h4-closed-evaluation p constructor)))

(defun h4-book-evaluation-spine-match (body formals)
  (and (proof-is-call body *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at body 1))
            (formal (proof-term-at formals 0)))
         (equal test (list *proof-consp* formal)))))

(defun h4-book-evaluation-spine-proof (evaluation call function values)
  (let* ((p (h4-book-evaluation-closed-evaluation-p evaluation))
         (proof (library-library-proof p))
         (constructor
          (h4-book-evaluation-closed-evaluation-constructor evaluation)))
    (proof-with-checked-results
        ((first (proof-quote (car values)))
         (tail (h4-tactics-cdr-data values))
         (suffix (proof-quote tail))
         (opened (proof-proof-unfold
                  proof
                  (list* function
                         (list *proof-cons* first *h4-book-evaluation-tail*)
                         (cddr call))))
         (opening (proof-step-first opened))
         (opening-body (proof-term-at opening 2))
         (body (h4-tactics-tactics-normalize
                p opening-body nil
                (remove-equal function
                              (table-keys (proof-proof-definitions proof)))
                nil (h4-tactics-constructor-provider constructor)))
         (chain (proof-proof-chain proof opened (list body)))
         (specialized (proof-proof-instantiate
                       proof chain
                       (list (list *h4-book-evaluation-tail* suffix))))
         (quotation (proof-proof-compute proof (list *proof-cons* first suffix)
                                         values))
         (reflexive (proof-proof-reflexive proof call))
         (symmetric (proof-proof-symmetric proof quotation))
         (exposed (proof-proof-rewrite proof reflexive symmetric '(1 2 1))))
      (proof-proof-chain proof exposed (list specialized)))))

(defun h4-book-evaluation-closed-evaluation-unfold-spine (evaluation call)
  (let* ((p (h4-book-evaluation-closed-evaluation-p evaluation))
         (proof (library-library-proof p)))
    (proof-with-checked-results ((function (proof-term-at call 0)))
      (let ((definition (assoc-equal function (proof-proof-definitions proof))))
        (and definition
             (consp (cdr call))
             (proof-is-call (cadr call) *proof-quote*)
             (proof-with-checked-results
                 ((values (proof-term-at (cadr call) 1)))
               (and (proof-compound values)
                    (<= 4 (len values))
                    (proof-with-checked-results
                        ((parts (proof-list-of-length (cdr definition) 2))
                         (match (h4-book-evaluation-spine-match
                                 (cadr parts) (car parts))))
                      (and match
                           (h4-book-evaluation-spine-proof
                            evaluation call function values))))))))))

(defun h4-book-evaluation-closed-evaluation-reduce-provide (call evaluation)
  (proof-with-checked-results
      ((reduction (h4-book-finite-reduction-provider-provide
                   call
                   (h4-book-evaluation-closed-evaluation-p evaluation)
                   (h4-book-evaluation-closed-evaluation-constructor evaluation))))
    (or reduction
        (h4-book-evaluation-closed-evaluation-unfold-spine evaluation call))))

(defun h4-book-evaluation-normalize (evaluation term expand replies)
  (h4-tactics-tactics-normalize
   (h4-book-evaluation-closed-evaluation-p evaluation)
   term nil expand nil (cons :h4-tactics-ordered-provider replies)))

(defun h4-book-evaluation-reply (evaluation term expand replies result)
  (let* ((call (h4-tactics-request-term result))
         (reply (h4-book-evaluation-closed-evaluation-reduce-provide call evaluation)))
    (if (failure-p reply)
        (cons reply replies)
      (let ((replies (append replies (list reply))))
        (cons (h4-book-evaluation-normalize evaluation term expand replies) replies)))))

(defun h4-book-evaluation-reduce-with-replies (n evaluation term expand current)
  ;; Each reply answers one provider call in normalization order.
  (declare (xargs :measure (nfix n)))
  (let ((result (car current)))
    (cond ((not (h4-tactics-request-p result)) result)
          ((zp n) '(:failure "Fuel" "h4-book-evaluation-reduce-with-replies"))
          (t (h4-book-evaluation-reduce-with-replies
              (1- n) evaluation term expand
              (h4-book-evaluation-reply evaluation term expand (cdr current) result))))))

(defun h4-book-evaluation-closed-evaluation-reduce (evaluation term)
  (let* ((p (h4-book-evaluation-closed-evaluation-p evaluation))
         (proof (library-library-proof p))
         (expand (table-keys (proof-proof-definitions proof))))
    (h4-book-evaluation-reduce-with-replies
     1000000 evaluation term expand
     (cons (h4-book-evaluation-normalize evaluation term expand nil) nil))))

(defun h4-book-evaluation-closed-evaluation-prove (evaluation formula)
  (proof-with-checked-results
      ((equality (h4-book-evaluation-closed-evaluation-reduce evaluation formula))
       (literal (proof-step-first equality))
       (value (proof-term-at literal 2)))
    (if (and (proof-is-call value *proof-quote*)
             (not (equal value *proof-false*)))
        (h4-tactics-tactics-non-nil
         (h4-book-evaluation-closed-evaluation-p evaluation) equality)
      '(:failure "InapplicableTerm" ""))))

(defun h4-book-evaluation-closed-goal (formula)
  (and (or (proof-is-call formula *proof-equal*)
           (proof-is-call formula *proof-if*))
       (proof-with-checked-results
           ((fits (h4-book-tactics-fits formula 1400)))
         (and fits (h4-book-evaluation-closed formula)))))

(defun h4-book-evaluation-closed-proof (p formula)
  (proof-with-checked-results
      ((goal (h4-book-evaluation-closed-goal formula)))
    (and goal
         (let ((result
                (proof-with-checked-results
                    ((evaluation (h4-book-evaluation-closed-evaluation-init p)))
                  (h4-book-evaluation-closed-evaluation-prove evaluation formula))))
           (if (and (failure-p result)
                    (member-equal (cadr result)
                                  '("InapplicableStep" "InapplicableTerm"
                                    "assertion" "value" "Unproved" "recursion")))
               nil
             result)))))
