(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h2-characters-char* (proof-cl "CHARACTERP"))
(defconst *h2-characters-rational* (proof-cl "RATIONALP"))
(defconst *h2-characters-numerator* (proof-cl "NUMERATOR"))
(defconst *h2-characters-real* (proof-cl "REALPART"))
(defconst *h2-characters-imag* (proof-cl "IMAGPART"))
(defconst *h2-characters-char-list* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *h2-characters-proper* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h2-characters-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *h2-characters-digit* (proof-sym "DIGIT-TO-CHAR" "ACL2"))
(defconst *h2-characters-atom-text* (proof-sym "EXPLODE-ATOM" "ACL2"))
(defconst *h2-characters-pack-list* (proof-sym "PACK-LIST" "ACL2"))
(defconst *h2-characters-pack-tree* (proof-sym "PACK-TREE" "ACL2"))

(defun h2-characters-auxiliary (proof name formula definitions facts variable)
  (h2-book-logic-auxiliary proof name formula definitions facts variable 1 "" nil nil 80))

(defun h2-characters-control (proof method args)
  (if (not (member-eq method (h2-search-search-hooks proof)))
      (cons nil proof)
    (let* ((replies (h2-search-search-replies proof))
           (pending (h2-search-reply-pending replies)))
      (if (endp pending)
          (cons (h2-search-hook-request :before proof method args nil replies) proof)
        (cons (cadar pending)
              (h2-search-search-with-replies proof (h2-search-reply-rest replies)))))))

(defun h2-characters-cons-fold-attempt (proof fixed formula replay replies)
  (let* ((hooks (h2-search-search-hooks proof))
         (scoped (h2-search-search-with-hooks proof (add-to-set-eq :can-open hooks)))
         (scoped (h2-search-search-with-replies scoped replay))
         (result (h2-characters-auxiliary scoped "CHARACTER-LIST-CONS" formula
                                          "CHARACTER-LISTP" nil nil))
         (value (car result)))
    (if (h2-search-request-p value)
        (let ((can-open (eq (h2-search-request-method value) :can-open))
              (term (car (h2-search-request-args value))))
          (cond
           ((and can-open (equal term fixed))
            (list :continue (append replay '((:return nil))) replies))
           ((and can-open (not (member-eq :can-open hooks)))
            (list :continue (append replay '(:base)) replies))
           ((consp replies)
            (list :continue (append replay (list (car replies))) (cdr replies)))
           (t result)))
      (cons value (h2-search-search-with-replies
                   (h2-search-search-with-hooks (cdr result) hooks) replies)))))

(defun h2-characters-cons-with-base-folds (n proof fixed formula result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) (cons '(:failure "fuel" "h2-characters-cons-with-base-folds") proof))
        ((eq (car result) :continue)
         (h2-characters-cons-with-base-folds
          (1- n) proof fixed formula
          (and (< 1 n)
               (h2-characters-cons-fold-attempt proof fixed formula (cadr result) (caddr result)))))
        (t result)))

(defun h2-characters-character-constructors-cons (proof fixed formula)
  (if (member-eq :keep-folded (h2-search-search-hooks proof))
      (h2-book-logic-with-results proof
          (((saved proof) (h2-characters-control proof :keep-folded (list (list fixed)))))
        (let* ((result (h2-characters-auxiliary proof "CHARACTER-LIST-CONS" formula
                                                 "CHARACTER-LISTP" nil nil))
               (proof (cdr result)))
          (if (h2-search-request-p (car result))
              result
            (h2-list-counts-after-update proof
                (h2-characters-control proof :restore-fixed-calls (list saved))
              (cons (car result) proof)))))
    (h2-characters-cons-with-base-folds
     1000000 proof fixed formula
     (h2-characters-cons-fold-attempt proof fixed formula nil (h2-search-search-replies proof)))))

(defun h2-characters-character-constructors (proof)
  (let* ((x *library-x*)
         (y *library-y*)
         (cell (list *proof-cons* x y))
         (fixed (list *h2-characters-char-list* y))
         (cons-formula (proof-eq (list *h2-characters-char-list* cell)
                                 (proof-ite (list *h2-characters-char* x) fixed *proof-false*)))
         (chars (list *h2-characters-char-list* x))
         (proper-formula (list *library-implies* chars (list *h2-characters-proper* x)))
         (guard (proof-ite chars fixed *proof-false*))
         (append-formula (list *library-implies* guard
                               (list *h2-characters-char-list* (list *h2-characters-append* x y)))))
    (h2-book-logic-with-results proof
        (((cons-name proof) (h2-characters-character-constructors-cons proof fixed cons-formula))
         ((proper proof) (h2-characters-auxiliary proof "CHARACTER-LIST-PROPER" proper-formula
                                                  "CHARACTER-LISTP TRUE-LISTP" nil "X"))
         ((append-name proof) (h2-characters-auxiliary proof "CHARACTER-LIST-APPEND" append-formula
                                                       "" (list proper "CHARACTER-LISTP-APPEND") nil)))
      (cons (list cons-name append-name) proof))))

(defun h2-characters-character-digits-character-at (value tests proof)
  (declare (ignore tests))
  (proof-with-checked-results
      ((typed (h2-list-counts-inherited proof-proof-compute proof
                                         (list *h2-characters-char* value) *proof-t*)))
    (h2-list-counts-inherited proof-proof-true-from-eq proof typed)))

(mutual-recursion
 (defun h2-characters-character-value (proof value rules leaves evidence)
   (declare (xargs :measure (acl2-count value)))
   (cond
    ((and (proof-is-call value *proof-cons*)
          (o< (acl2-count (caddr value)) (acl2-count value)))
     (h2-book-logic-with-results proof
         ((first (proof-term-at value 1))
          ((head proof) (h2-list-counts-derive proof (list *h2-characters-char* first)
                                              "" nil nil "" evidence))
          ((tail proof)
           (if (consp (cddr value))
               (h2-characters-character-value proof (caddr value) rules leaves evidence)
             (cons (proof-index-failure) proof)))
          (rule (proof-term-at rules 0))
          (equation (h2-list-counts-library-call library-library-axiom proof rule (cdr value)))
          (body (h2-list-counts-first-at equation 2))
          (typed (h2-list-counts-inherited proof-proof-prove proof body (list head tail) nil)))
       (cons (h2-list-counts-inherited proof-proof-transport proof typed equation) proof)))
    ((and (proof-is-call value *h2-characters-append*)
          (o< (acl2-count (cdr value)) (acl2-count value)))
     (h2-book-logic-with-results proof
         (((parts proof) (h2-characters-character-value-parts proof (cdr value) rules leaves evidence))
          (rule (proof-term-at rules 1))
          (implies (h2-list-counts-library-call library-library-axiom proof rule (cdr value)))
          (guard (h2-list-counts-first-at implies 1))
          (typed (h2-list-counts-inherited proof-proof-prove proof guard parts nil)))
       (cons (h2-list-counts-inherited proof-proof-modus-ponens proof implies typed) proof)))
    ((proof-is-call value *proof-quote*)
     (h2-list-counts-derive proof (list *h2-characters-char-list* value) "CHARACTER-LISTP"
                           nil nil "CHARACTER-LISTP" nil))
    (t (h2-list-counts-derive proof (list *h2-characters-char-list* value) "" leaves nil "" evidence))))

 (defun h2-characters-character-value-parts (proof values rules leaves evidence)
   (declare (xargs :measure (acl2-count values)))
   (if (and (consp values)
            (o< (acl2-count (car values)) (acl2-count values))
            (o< (acl2-count (cdr values)) (acl2-count values)))
       (h2-book-logic-with-results proof
           (((first proof) (h2-characters-character-value proof (car values) rules leaves evidence))
            ((rest proof) (h2-characters-character-value-parts proof (cdr values) rules leaves evidence)))
         (cons (cons first rest) proof))
     (cons nil proof))))

(defun h2-characters-assume-tests (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (step (h2-list-counts-inherited proof-proof-assume proof (car pair) (cadr pair)))
         (rest (h2-characters-assume-tests proof (cdr tests))))
      (cons step rest))))

(defun h2-characters-character-result-at-leaf (value tests proof rules leaves evidence)
  (h2-book-logic-with-results proof ((assumptions (h2-characters-assume-tests proof tests)))
    (h2-characters-character-value proof value rules leaves (append evidence assumptions))))

(defun h2-characters-by-value (n proof value template leaf tests rules leaves evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "fuel" "h2-characters-by-value") proof)
    (h2-book-logic-with-saved-result proof
      (cond
       ((proof-is-call value *proof-if*)
        (h2-book-logic-with-results proof
            ((branches (proof-list-of-length (cdr value) 3))
             (test (car branches))
             ((yes proof) (h2-characters-by-value (1- n) proof (cadr branches) template leaf
                                                   (append tests (list (list test t))) rules leaves evidence))
             ((no proof) (h2-characters-by-value (1- n) proof (caddr branches) template leaf
                                                  (append tests (list (list test nil))) rules leaves evidence)))
          (cons (h2-list-counts-inherited proof-by-value-join proof value template yes no) proof)))
       ((and (proof-compound value) (endp value))
        (cons (proof-index-failure) proof))
       ((and (proof-compound value) (proof-compound (car value)))
        (h2-book-logic-with-results proof
            ((equation (h2-list-counts-inherited proof-proof-beta proof value))
             (opened (h2-list-counts-first-at equation 2))
             ((step proof) (h2-characters-by-value (1- n) proof opened template leaf tests rules leaves evidence))
             (inverse (h2-list-counts-inherited proof-proof-symmetric proof equation)))
          (cons (h2-list-counts-inherited proof-proof-rewrite-result proof step inverse template *proof-result*)
                proof)))
       (t
        (h2-book-logic-with-results proof
            (((step proof)
              (if (eq leaf :digit)
                  (cons (h2-characters-character-digits-character-at value tests proof) proof)
                (h2-characters-character-result-at-leaf value tests proof rules leaves evidence)))
             (literal (proof-step-first step))
             (target (proof-subst template (list (cons *proof-result* value)))))
          (cons (if (equal literal target) step '(:failure "failure" "")) proof)))))))

(defun h2-characters-character-result (proof opening rules leaves evidence)
  (h2-book-logic-with-saved-result proof
    (h2-book-logic-with-results proof
        ((value (h2-list-counts-first-at opening 2))
         ((result proof) (h2-characters-by-value 1000000 proof value
                                                (list *h2-characters-char-list* *proof-result*)
                                                :result nil rules leaves evidence)))
      (cons (h2-list-counts-library-call library-library-transport-argument proof result opening 1) proof))))

(defun h2-characters-add-digit-lemma (proof digit)
  (h2-book-logic-with-saved-result proof
    (h2-book-logic-with-results proof
        ((opening (h2-list-counts-inherited proof-proof-unfold proof digit))
         (value (h2-list-counts-first-at opening 2))
         ((digit-step proof) (h2-characters-by-value 1000000 proof value
                                                    (list *h2-characters-char* *proof-result*)
                                                    :digit nil nil nil nil))
         (step (h2-list-counts-library-call library-library-transport-argument
                                           proof digit-step opening 1))
         (claim (proof-step-first step))
         (proof (h2-list-counts-add-lemma proof "H2-DIGIT-IS-CHARACTER" claim step)))
      (cons "SELF-H2-DIGIT-IS-CHARACTER" proof))))

(defun h2-characters-character-digits (proof rules)
  (let ((name "SELF-H2-CHARACTER-LIST-OF-EXPLODE-INTEGER"))
    (if (h2-list-counts-has-fact proof (proof-sym name "ACL2"))
        (cons name proof)
      (let* ((digit (list *h2-characters-digit* *library-x*))
             (z-chars (list *h2-characters-char-list* *library-z*))
             (explode (list *h2-division-explode* *library-x* *library-y* *library-z*))
             (formula (list *library-implies* z-chars (list *h2-characters-char-list* explode))))
        (h2-book-logic-with-results proof
            (((digit-lemma proof) (h2-characters-add-digit-lemma proof digit))
             (recognize (h2-division-make-recognizer "CHARACTER-LISTP" (cons digit-lemma rules)
                                                     "CHARACTER-LISTP"))
             ((induction proof) (h2-division-explode-accumulator proof formula recognize))
             (proof (h2-list-counts-add-lemma proof "H2-CHARACTER-LIST-OF-EXPLODE-INTEGER" formula induction)))
          (cons name proof))))))

(defun h2-characters-implication-lemma (proof name formula step)
  (proof-with-checked-results ((introduced (h2-search-search-introduce proof formula step)))
    (h2-list-counts-add-lemma proof name formula introduced)))

(defun h2-characters-character-atom (proof rules)
  (let ((name "SELF-H2-CHARACTER-LIST-OF-EXPLODE-ATOM"))
    (if (h2-list-counts-has-fact proof (proof-sym name "ACL2"))
        (cons name proof)
      (let* ((x *library-x*)
             (y *library-y*)
             (value (list *h2-characters-atom-text* x y))
             (goal (list *h2-characters-char-list* value))
             (integer (library-integer x))
             (rational (list *h2-characters-rational* x))
             (integer-formula (list *library-implies* integer goal))
             (rational-formula (list *library-implies* rational goal))
             (integer-name "SELF-H2-INTEGER-EXPLODE-ATOM-CHARACTERS")
             (rational-name "SELF-H2-RATIONAL-EXPLODE-ATOM-CHARACTERS"))
        (h2-book-logic-with-results proof
            (((digit-closure proof) (h2-book-logic-with-saved-result proof
                                      (h2-characters-character-digits proof rules)))
             ((nil-characters proof)
              (h2-list-counts-derive proof (list *h2-characters-char-list* *proof-false*)
                                    "CHARACTER-LISTP" nil nil "" nil))
             (open-atom (h2-list-counts-inherited proof-proof-unfold proof value))
             (typed (h2-list-counts-inherited proof-proof-assume proof integer t))
             (rational-from-integer
              (h2-list-counts-library-call library-library-rational proof x (list typed)))
             (selected (h2-book-logic-select-body proof open-atom rational-from-integer))
             (selected (h2-book-logic-select-body proof selected typed))
             ((body proof) (h2-characters-character-result proof selected rules (list digit-closure)
                                                            (list nil-characters)))
             (proof (h2-characters-implication-lemma proof "H2-INTEGER-EXPLODE-ATOM-CHARACTERS"
                                                     integer-formula body))
             (assumption (h2-list-counts-inherited proof-proof-assume proof rational t))
             (axiom (h2-list-counts-library-call library-library-axiom proof "RATIONAL-IMPLIES1" (list x)))
             (parts (h2-list-counts-inherited proof-proof-modus-ponens proof axiom assumption))
             (parts (h2-list-counts-inherited proof-proof-conjunct proof parts))
             (parts (h2-list-counts-inherited proof-proof-conjunct proof (cadr parts)))
             (numerator (car parts))
             (axiom (h2-list-counts-library-call library-library-axiom proof integer-name
                                                (list (list *h2-characters-numerator* x) y)))
             (top (h2-list-counts-inherited proof-proof-modus-ponens proof axiom numerator))
             (rational-open (h2-book-logic-select-body proof open-atom assumption))
             (noninteger (h2-list-counts-inherited proof-proof-assume proof integer nil))
             (fraction-open (h2-book-logic-select-body proof rational-open noninteger))
             ((fraction proof) (h2-characters-character-result proof fraction-open rules
                                                                (list digit-closure) (list nil-characters top)))
             (rational-case (h2-list-counts-inherited proof-proof-cases proof integer body fraction))
             (proof (h2-characters-implication-lemma proof "H2-RATIONAL-EXPLODE-ATOM-CHARACTERS"
                                                     rational-formula rational-case))
             (axiom (h2-list-counts-library-call library-library-axiom proof "COMPLEX-IMPLIES1" (list x)))
             (pieces (h2-list-counts-inherited proof-proof-conjunct proof axiom))
             (real (car pieces))
             (imag (cadr pieces))
             (axiom (h2-list-counts-library-call library-library-axiom proof rational-name
                                                (list (list *h2-characters-real* x) y)))
             (real-text (h2-list-counts-inherited proof-proof-modus-ponens proof axiom real))
             (axiom (h2-list-counts-library-call library-library-axiom proof rational-name
                                                (list (list *h2-characters-imag* x) y)))
             (imag-text (h2-list-counts-inherited proof-proof-modus-ponens proof axiom imag))
             (nonrational (h2-list-counts-inherited proof-proof-assume proof rational nil))
             (other-open (h2-book-logic-select-body proof open-atom nonrational))
             ((other-case proof)
              (h2-characters-character-result proof other-open rules (list "CHARACTER-LISTP-COERCE")
                                              (list nil-characters real-text imag-text)))
             (result (h2-list-counts-inherited proof-proof-cases proof rational rational-case other-case))
             (proof (h2-list-counts-add-lemma proof "H2-CHARACTER-LIST-OF-EXPLODE-ATOM" goal result)))
          (cons name proof))))))

(defun h2-characters-pack-characters-smaller (proof clause cons-step bindings formula)
  (proof-with-checked-results
      ((builtin (h2-list-counts-library-call library-library-builtin proof clause *library-x*))
       (decrease (h2-list-counts-inherited proof-proof-discharge proof builtin cons-step))
       (hypothesis (h2-list-counts-hypothesis proof decrease formula bindings))
       (result (h2-list-counts-inherited proof-proof-prove-if proof hypothesis decrease)))
    (h2-list-counts-inherited proof-proof-conjunct proof result)))

(defun h2-characters-pack-characters-shape-result (proof fn holds evidence test rules atom)
  (h2-book-logic-with-results proof
      ((opening (h2-list-counts-inherited proof-proof-unfold proof (list fn *library-x*)))
       (body (h2-list-counts-first-at opening 2))
       (guard (proof-term-at body 1))
       (sign (if holds (proof-neg guard) guard))
       (shape (h2-list-counts-inherited proof-proof-assume proof test holds))
       ((test-proof proof) (h2-list-counts-derive proof sign "" nil nil "" (list shape)))
       (view (h2-book-logic-select-body proof opening test-proof)))
    (h2-characters-character-result proof view rules (list atom) evidence)))

(defun h2-characters-pack-characters-shape (holds evidence proof test formula rules atom)
  (h2-book-logic-with-results proof
      (((list-result proof)
        (h2-characters-pack-characters-shape-result proof *h2-characters-pack-list*
                                                    holds evidence test rules atom))
       ((tree-result proof)
        (h2-characters-pack-characters-shape-result proof *h2-characters-pack-tree*
                                                    holds evidence test rules atom)))
    (cons (h2-list-counts-inherited proof-proof-prove proof formula (list list-result tree-result) nil)
          proof)))

(defun h2-characters-pack-characters-lemma (proof)
  (let* ((x *library-x*)
         (test (list *proof-consp* x))
         (packed-list (list *h2-characters-char-list* (list *h2-characters-pack-list* x)))
         (packed-tree (list *h2-characters-char-list* (list *h2-characters-pack-tree* x)))
         (formula (proof-ite packed-list packed-tree *proof-false*))
         (car-bindings (list (list x (list *library-car* x))))
         (cdr-bindings (list (list x (list *library-cdr* x))))
         (updates (list car-bindings cdr-bindings)))
    (h2-list-counts-after-update proof (h2-characters-control proof :set-fuel (list 44000))
      (h2-book-logic-with-results proof
          (((rules proof) (h2-book-logic-with-saved-result proof
                            (h2-characters-character-constructors proof)))
           ((atom proof) (h2-book-logic-with-saved-result proof
                           (h2-characters-character-atom proof rules)))
           (cons-step (h2-list-counts-inherited proof-proof-assume proof test t))
           (car-pieces (h2-characters-pack-characters-smaller proof 2 cons-step car-bindings formula))
           (cdr-pieces (h2-characters-pack-characters-smaller proof 3 cons-step cdr-bindings formula))
           (known (append car-pieces cdr-pieces))
           ((yes proof) (h2-characters-pack-characters-shape t known proof test formula rules atom))
           ((no proof) (h2-characters-pack-characters-shape nil nil proof test formula rules atom))
           (joint (h2-list-counts-inherited proof-proof-cases proof test yes no))
           (ordinal (h2-list-counts-library-call library-library-builtin proof 1 x))
           (step (h2-list-counts-inherited proof-proof-induct proof ordinal joint formula
                                           (list *library-count* x) updates))
           (proof (h2-list-counts-add-lemma proof "H2-PACK-CHARACTER-LISTS" formula step)))
        (cons nil proof)))))

(defun h2-characters-pack-characters (proof function variable)
  (let ((name (proof-sym "SELF-H2-PACK-CHARACTER-LISTS" "ACL2")))
    (h2-list-counts-after-update proof
        (if (h2-list-counts-has-fact proof name)
            (cons nil proof)
          (h2-characters-pack-characters-lemma proof))
      (h2-book-logic-with-results proof
          ((fact (h2-list-counts-inherited proof-proof-fact proof name (list (list *library-x* variable))))
           (projections (h2-list-counts-inherited proof-proof-conjunct proof fact)))
        (cons (if (equal function *h2-characters-pack-list*) (car projections) (cadr projections))
              proof)))))
