(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-printing-characters* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *t4-printing-true-list* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *t4-printing-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *t4-printing-digit* (proof-sym "DIGIT-TO-CHAR" "ACL2"))
(defconst *t4-printing-print-integer* (proof-sym "EXPLODE-NONNEGATIVE-INTEGER" "ACL2"))
(defconst *t4-printing-print-atom* (proof-sym "EXPLODE-ATOM" "ACL2"))
(defconst *t4-printing-zp* (proof-sym "ZP" "ACL2"))
(defconst *t4-printing-atom* (proof-cl "ATOM"))
(defconst *t4-printing-coerce* (proof-cl "COERCE"))
(defconst *t4-printing-characterp* (proof-cl "CHARACTERP"))
(defconst *t4-printing-realpart* (proof-cl "REALPART"))
(defconst *t4-printing-imagpart* (proof-cl "IMAGPART"))

(defun t4-printing-printed-list-init (lib)
  (list :t4-printing-printed-list lib (list *t4-printing-characters* *proof-result*)))

(defun t4-printing-printed-list-lib (printer)
  (cadr printer))

(defun t4-printing-printed-list-template (printer)
  (caddr printer))

(defun t4-printing-printed-list-with-lib (printer lib)
  (list :t4-printing-printed-list lib (t4-printing-printed-list-template printer)))

(defun t4-printing-printed-list-proof (printer)
  (library-library-proof (t4-printing-printed-list-lib printer)))

(defun t4-printing-prove (printer term evidence definitions)
  (proof-with-checked-results
   ((result (t4-ordinals-ordinals-prove
             (t4-printing-printed-list-lib printer) term evidence definitions)))
   (cons (car result) (t4-printing-printed-list-with-lib printer (cdr result)))))

(defun t4-printing-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun t4-printing-step-argument (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 1)))

(defun t4-printing-lemma-present-p (lib name)
  (if (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
                   (proof-proof-facts (library-library-proof lib)))
      t
    nil))

(defun t4-printing-printed-list-pick (printer equation condition)
  (let ((proof (t4-printing-printed-list-proof printer)))
    (proof-with-checked-results
     ((body (t4-printing-step-right equation))
      (selected (proof-proof-select proof body condition)))
     (proof-proof-chain proof equation (list selected)))))

(defun t4-printing-reverse-result (printer step equality template)
  (let ((proof (t4-printing-printed-list-proof printer)))
    (proof-with-checked-results ((reversed (proof-proof-symmetric proof equality)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*))))

(defun t4-printing-printed-list-unroll (printer proof term)
  (t4-printing-reverse-result printer proof term
                             (t4-printing-printed-list-template printer)))

(defun t4-printing-evidence-find (printer tests known formula)
  (proof-with-checked-results
   ((evidence (t4-structural-evidence-init
               (t4-printing-printed-list-lib printer) tests known))
    (found (t4-structural-evidence-find evidence formula)))
   (cons (car found)
         (t4-printing-printed-list-with-lib
          printer (t4-structural-evidence-proof (cdr found))))))

(defun t4-printing-character-quote-p (term)
  (and (proof-is-call term *proof-quote*)
       (proof-with-checked-results ((value (proof-term-at term 1)))
         (and (or (consp value) (null value))
              (proof-with-checked-results ((tag (proof-term-at value 0)))
                (equal tag "char"))))))

(defun t4-printing-check-leaf (result value template)
  (proof-with-checked-results
   ((literal (proof-step-first (car result)))
    (claim (proof-subst template (list (cons *proof-result* value)))))
   (if (equal literal claim)
       result
     '(:failure "inference-mismatch" ""))))

(defun t4-printing-join-result (value template yes no)
  (let* ((printer (cdr no))
         (proof (t4-printing-printed-list-proof printer)))
    (proof-with-checked-results
     ((step (proof-by-value-join proof value template (car yes) (car no))))
     (cons step printer))))

(mutual-recursion
 (defun t4-printing-character-run (n printer term tests)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-printing-character-run")
     (let ((formula (list *t4-printing-characterp* term))
           (name "DIGIT-PRINTS-A-CHARACTER"))
       (proof-with-checked-results
        ((known (t4-printing-evidence-find printer tests nil formula))
         (quoted (and (not (car known)) (t4-printing-character-quote-p term))))
        (let* ((printer (cdr known))
               (lib (t4-printing-printed-list-lib printer))
               (proof (library-library-proof lib)))
          (cond
           ((car known) known)
           (quoted
            (proof-with-checked-results
             ((computed (proof-proof-compute proof formula *proof-t*))
              (proved (proof-proof-true-from-eq proof computed)))
             (cons proved printer)))
           ((not (proof-is-call term *t4-printing-digit*))
            '(:failure "search-miss" ""))
           (t
            (proof-with-checked-results
             ((printer
               (if (t4-printing-lemma-present-p lib name)
                   printer
                 (let ((template (list *t4-printing-characterp* *proof-result*))
                       (digit (list *t4-printing-digit* *library-x*)))
                   (proof-with-checked-results
                    ((body (proof-proof-unfold proof digit))
                     (value (t4-printing-step-right body))
                     (result (t4-printing-character-by-value
                              (1- n) printer value template nil))
                     (step (t4-printing-reverse-result
                            (cdr result) (car result) body template))
                     (lib (library-library-lemma
                           (t4-printing-printed-list-lib (cdr result))
                           name (list *t4-printing-characterp* digit) step nil)))
                    (t4-printing-printed-list-with-lib (cdr result) lib)))))
              (step (library-library-cite (t4-printing-printed-list-lib printer)
                                          name (cdr term) nil)))
             (cons step printer)))))))))

 (defun t4-printing-character-by-value (n printer value template tests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-printing-character-by-value"))
    ((proof-is-call value *proof-if*)
     (proof-with-checked-results
      ((branches (proof-list-of-length (cdr value) 3))
       (yes (t4-printing-character-by-value
             (1- n) printer (cadr branches) template
             (append tests (list (list (car branches) t)))))
       (no (t4-printing-character-by-value
            (1- n) (cdr yes) (caddr branches) template
            (append tests (list (list (car branches) nil))))))
      (t4-printing-join-result value template yes no)))
    ((null value) '(:failure "failure" ""))
    ((and (proof-compound value) (proof-compound (car value)))
     (proof-with-checked-results
      ((opening (proof-proof-beta (t4-printing-printed-list-proof printer) value))
       (expanded (t4-printing-step-right opening))
       (result (t4-printing-character-by-value (1- n) printer expanded template tests))
       (step (t4-printing-reverse-result
              (cdr result) (car result) opening template)))
      (cons step (cdr result))))
    (t
     (proof-with-checked-results
      ((result (t4-printing-character-run (1- n) printer value tests)))
      (t4-printing-check-leaf result value template))))))

(defun t4-printing-printed-list-character (printer term tests)
  (t4-printing-character-run 1000000 printer term tests))

(defun t4-printing-add-cons-lemma (printer name)
  (let* ((lib (t4-printing-printed-list-lib printer))
         (proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (pair (list *proof-cons* x y))
         (claim (list *t4-printing-characters* pair))
         (head-claim (list *t4-printing-characterp* x))
         (tail-claim (list *t4-printing-characters* y)))
    (proof-with-checked-results
     ((shape (proof-proof-fact proof "consp-cons" nil))
      (opened (proof-proof-unfold proof claim))
      (nonatom (t4-printing-prove printer (proof-neg (list *t4-printing-atom* pair))
                                (list shape) (list *t4-printing-atom* *proof-not*)))
      (printer (cdr nonatom))
      (lib (t4-printing-printed-list-lib printer))
      (proof (library-library-proof lib))
      (opened (t4-printing-printed-list-pick printer opened (car nonatom)))
      (car-cons (library-library-axiom lib "CAR-CONS" (list x y)))
      (opened (proof-proof-rewrite-first proof opened car-cons))
      (cdr-cons (library-library-axiom lib "CDR-CONS" (list x y)))
      (opened (proof-proof-rewrite-first proof opened cdr-cons))
      (head (proof-proof-assume proof head-claim t))
      (tail (proof-proof-assume proof tail-claim t))
      (combined (t4-division-combine lib (list head tail)))
      (step (proof-proof-transport proof combined opened))
      (lib (library-library-lemma lib name claim step
                                  (list (proof-neg head-claim) (proof-neg tail-claim)))))
     (t4-printing-printed-list-with-lib printer lib))))

(defun t4-printing-printed-list-cons (printer head tail)
  (let ((name "CHARACTER-LIST-CONS"))
    (proof-with-checked-results
     ((printer (if (t4-printing-lemma-present-p (t4-printing-printed-list-lib printer) name)
                   printer
                 (t4-printing-add-cons-lemma printer name)))
      (a (t4-printing-step-argument head))
      (b (t4-printing-step-argument tail))
      (step (library-library-cite (t4-printing-printed-list-lib printer)
                                  name (list a b) (list head tail))))
     (cons step printer))))

(defun t4-printing-open-eq (proof step)
  (proof-with-checked-results ((right (t4-printing-step-right step)))
    (if (proof-is-call right (proof-cl "EQ"))
        (proof-with-checked-results ((opened (proof-proof-unfold proof right)))
          (proof-proof-chain proof step (list opened)))
      step)))

(defun t4-printing-add-true-list-lemma (printer name)
  (let* ((lib (t4-printing-printed-list-lib printer))
         (proof (library-library-proof lib))
         (x *library-x*)
         (guard (list *t4-printing-characters* x))
         (goal (list *t4-printing-true-list* x))
         (claim (list *library-implies* guard goal))
         (shape (list *proof-consp* x))
         (atom-test (list *t4-printing-atom* x))
         (definitions (list *t4-printing-atom* *proof-not*)))
    (proof-with-checked-results
     ((solid (proof-proof-assume proof shape t))
      (atomic (proof-proof-assume proof shape nil))
      (nonatom (t4-printing-prove printer (proof-neg atom-test) (list solid) definitions))
      (atom-proof (t4-printing-prove (cdr nonatom) atom-test (list atomic) definitions))
      (printer (cdr atom-proof))
      (lib (t4-printing-printed-list-lib printer))
      (proof (library-library-proof lib))
      (characters (proof-proof-assume proof guard t))
      (char-view (proof-proof-unfold proof guard))
      (list-view (proof-proof-unfold proof goal))
      (smaller (library-library-builtin lib 3 x))
      (smaller-term (proof-step-first smaller))
      (instance (proof-subst claim (list (cons x (list *library-cdr* x)))))
      (hypothesis (proof-proof-assume proof (proof-ite smaller-term instance *proof-true*) t))
      (tail (proof-proof-prove-if proof hypothesis smaller))
      (chosen (t4-printing-printed-list-pick printer char-view (car nonatom)))
      (tail-characters (proof-proof-rewrite proof characters chosen '(1)))
      (parts (proof-proof-conjunct proof tail-characters))
      (tail-proper (proof-proof-modus-ponens proof tail (cadr parts)))
      (chosen (t4-printing-printed-list-pick printer list-view solid))
      (yes (proof-proof-transport proof tail-proper chosen))
      (chosen (t4-printing-printed-list-pick printer char-view (car atom-proof)))
      (empty-char (proof-proof-rewrite proof characters chosen '(1)))
      (empty-list (t4-printing-printed-list-pick printer list-view atomic))
      (empty-list (t4-printing-open-eq proof empty-list))
      (no (proof-proof-transport proof empty-char empty-list))
      (branches (proof-proof-cases proof shape yes no))
      (cases (t4-ordinals-ordinals-imply lib guard branches))
      (ordinal (library-library-builtin lib 1 x))
      (step (proof-proof-induct proof ordinal cases claim (t4-structural-count x)
                                 (list (list (list x (list *library-cdr* x))))))
      (lib (library-library-lemma lib name claim step nil)))
     (t4-printing-printed-list-with-lib printer lib))))

(defun t4-printing-printed-list-true-list (printer characters)
  (let ((name "CHARACTER-LIST-IS-TRUE-LIST"))
    (proof-with-checked-results
     ((printer (if (t4-printing-lemma-present-p (t4-printing-printed-list-lib printer) name)
                   printer
                 (t4-printing-add-true-list-lemma printer name)))
      (literal (proof-step-first characters))
      (step (library-library-cite (t4-printing-printed-list-lib printer)
                                  name (cdr literal) nil))
      (step (proof-proof-modus-ponens
             (t4-printing-printed-list-proof printer) step characters)))
     (cons step printer))))

(defun t4-printing-literal-elements (elements suffix result printer)
  (if (endp elements)
      (cons result printer)
    (let ((element (car elements)))
      (proof-with-checked-results
       ((argument (t4-printing-step-argument result))
        (head-type (t4-printing-printed-list-character printer (proof-quote element) nil))
        (combined (t4-printing-printed-list-cons (cdr head-type) (car head-type) result)))
       (let* ((printer (cdr combined))
              (proof (t4-printing-printed-list-proof printer))
              (pair (list *proof-cons* (proof-quote element) argument))
              (suffix (cons element suffix)))
         (proof-with-checked-results
          ((computed (proof-proof-compute proof pair suffix))
           (step (proof-proof-rewrite proof (car combined) computed '(1 1))))
          (t4-printing-literal-elements (cdr elements) suffix step printer)))))))

(defun t4-printing-printed-list-literal (printer value)
  (proof-with-checked-results
   ((result (t4-printing-prove printer (list *t4-printing-characters* *proof-false*) nil
                             (list *t4-printing-characters* *t4-printing-atom* *proof-not*))))
   (if (equal value *proof-false*)
       result
     (proof-with-checked-results ((datum (proof-term-at value 1)))
       (if (proof-compound datum)
           (t4-printing-literal-elements (reverse datum) nil (car result) (cdr result))
         '(:failure "search-miss" ""))))))

(defun t4-printing-printed-list-missing-value (value tests)
  (declare (ignore value tests))
  '(:failure "search-miss" ""))

(defun t4-printing-printed-list-atoms-primitive (value tests printer i-r large-r)
  (if (not (proof-is-call value *t4-printing-print-integer*))
      (t4-printing-printed-list-missing-value value tests)
    (proof-with-checked-results
     ((fact (library-library-cite (t4-printing-printed-list-lib printer)
                                  "PRINT-INTEGER-CHARACTERS" (cdr value) nil))
      (accumulator (proof-term-at value 3))
      (literal (t4-printing-printed-list-literal printer accumulator)))
     (let* ((printer (cdr literal))
            (lib (t4-printing-printed-list-lib printer)))
       (proof-with-checked-results
        ((guard (t4-division-combine lib (list i-r large-r (car literal))))
         (step (proof-proof-modus-ponens (library-library-proof lib) fact guard)))
        (cons step printer))))))

(defun t4-printing-printed-list-atoms-numerator
    (value tests printer i-r large-r numerator-type obj)
  (proof-with-checked-results
   ((argument (and (proof-is-call value *t4-printing-print-atom*)
                   (proof-term-at value 1))))
   (if (equal argument (list *t4-division-numerator* obj))
       (let ((lib (t4-printing-printed-list-lib printer)))
         (proof-with-checked-results
          ((step (library-library-cite lib "PRINT-ATOM-OF-INTEGER" (cdr value) nil))
           (guard (t4-division-combine lib (list i-r large-r numerator-type)))
           (step (proof-proof-modus-ponens (library-library-proof lib) step guard)))
          (cons step printer)))
     (t4-printing-printed-list-atoms-primitive value tests printer i-r large-r))))

(defun t4-printing-printed-list-atoms-complex-part
    (value tests printer i-r large-r real-type imag-type obj)
  (proof-with-checked-results
   ((argument (and (proof-is-call value *t4-printing-print-atom*)
                   (proof-term-at value 1))))
   (let ((real (list *t4-printing-realpart* obj))
         (imag (list *t4-printing-imagpart* obj)))
     (if (or (equal argument real) (equal argument imag))
         (let ((lib (t4-printing-printed-list-lib printer))
               (typed (if (equal argument real) real-type imag-type)))
           (proof-with-checked-results
            ((step (library-library-cite lib "PRINT-ATOM-OF-RATIONAL" (cdr value) nil))
             (guard (t4-division-combine lib (list i-r large-r typed)))
             (step (proof-proof-modus-ponens (library-library-proof lib) step guard)))
            (cons step printer)))
       (t4-printing-printed-list-missing-value value tests)))))

(defun t4-printing-group-index (group head)
  (let ((index (seq-index-from group head 0)))
    (if (< index 0)
        '(:failure "search-miss" "")
      index)))

(defun t4-printing-character-results-recursive-leaf (value tests printer group joint obj)
  (proof-with-checked-results ((selector-call (proof-list-of-length (cadr value) 2)))
    (let ((selector (car selector-call))
          (source (cadr selector-call))
          (lib (t4-printing-printed-list-lib printer)))
      (if (or (not (member-equal selector (list *library-car* *library-cdr*)))
              (not (equal source obj)))
          '(:failure "search-miss" "")
        (proof-with-checked-results
         ((decrease (library-library-builtin lib (if (equal selector *library-car*) 2 3) obj))
          (decrease-term (proof-step-first decrease))
          (instance (proof-subst joint (list (cons obj selector-call))))
          (evidence (t4-structural-evidence-init lib tests nil))
          (shape (t4-structural-evidence-require evidence (list *proof-consp* obj))))
         (let* ((lib (t4-structural-evidence-proof (cdr shape)))
                (proof (library-library-proof lib))
                (hypothesis (proof-ite decrease-term instance *proof-true*)))
           (proof-with-checked-results
            ((assumed (proof-proof-assume proof hypothesis t))
             (discharged (proof-proof-discharge proof decrease (car shape)))
             (smaller (proof-proof-prove-if proof assumed discharged))
             (pieces (t4-division-pieces lib smaller))
             (index (t4-printing-group-index group (car value)))
             (step (proof-term-at pieces index)))
            (cons step (t4-printing-printed-list-with-lib printer lib)))))))))

(defun t4-printing-character-results-leaf (value tests printer group joint obj)
  (cond
   ((proof-is-call value *t4-printing-print-atom*)
    (let ((lib (t4-printing-printed-list-lib printer)))
      (proof-with-checked-results
       ((radix (proof-term-at value 2))
        (typed (t4-ordinals-ordinals-type-of lib radix nil))
        (large (t4-printing-prove printer (library-lt *proof-one* radix) nil nil))
        (printer (cdr large))
        (lib (t4-printing-printed-list-lib printer))
        (proof (library-library-proof lib))
        (guard (t4-division-combine lib (list typed (car large))))
        (fact (library-library-cite lib "PRINT-ATOM-CHARACTERS" (cdr value) nil))
        (step (proof-proof-modus-ponens proof fact guard)))
       (cons step printer))))
   ((null value) '(:failure "failure" ""))
   ((and (proof-compound value) (member-equal (car value) group) (equal (len value) 2))
    (t4-printing-character-results-recursive-leaf value tests printer group joint obj))
   (t (t4-printing-printed-list-missing-value value tests))))

(defun t4-printing-evaluate-leaf (value tests printer leaf)
  (case (car leaf)
    (:missing-value (t4-printing-printed-list-missing-value value tests))
    (:primitive (t4-printing-printed-list-atoms-primitive value tests printer
                                                         (cadr leaf) (caddr leaf)))
    (:numerator (t4-printing-printed-list-atoms-numerator
                 value tests printer (cadr leaf) (caddr leaf)
                 (cadddr leaf) (car (cddddr leaf))))
    (:complex-part (t4-printing-printed-list-atoms-complex-part
                    value tests printer (cadr leaf) (caddr leaf) (cadddr leaf)
                    (car (cddddr leaf)) (cadr (cddddr leaf))))
    (:character-results (t4-printing-character-results-leaf
                         value tests printer (cadr leaf) (caddr leaf) (cadddr leaf)))
    (otherwise
     (let ((entry (assoc-equal (list value tests) leaf)))
       (if (not entry)
           '(:failure "search-miss" "")
         (proof-with-checked-results ((step (cdr entry)))
           (cons step printer)))))))

(defun t4-printing-append-result (a b left right)
  (let ((lib (t4-printing-printed-list-lib (cdr right))))
    (proof-with-checked-results
     ((fact (library-library-axiom lib "CHARACTER-LISTP-APPEND" (list a b)))
      (proper (t4-printing-printed-list-true-list (cdr right) (car left))))
     (let* ((printer (cdr proper))
            (lib (t4-printing-printed-list-lib printer))
            (proof (library-library-proof lib)))
       (proof-with-checked-results
        ((equation (proof-proof-modus-ponens proof fact (car proper)))
         (combined (t4-division-combine lib (list (car left) (car right))))
         (step (proof-proof-transport proof combined equation)))
        (cons step printer))))))

(defun t4-printing-coerce-result (printer node cases leaf)
  (proof-with-checked-results ((kind (proof-term-at node 2)))
    (if (equal kind (proof-quote (proof-cl "LIST")))
        (proof-with-checked-results
         ((step (proof-proof-fact
                 (t4-printing-printed-list-proof printer)
                 (proof-sym "CHARACTER-LISTP-COERCE" "ACL2")
                 (list (list (proof-sym "STR" "ACL2") (cadr node))))))
         (cons step printer))
      (t4-printing-evaluate-leaf node cases printer leaf))))

(mutual-recursion
 (defun t4-printing-prove-result-run (n printer value leaf tests known)
   (declare (xargs :measure (nfix n)))
   (let ((template (t4-printing-printed-list-template printer)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-printing-prove-result-run"))
      ((proof-is-call value *proof-if*)
       (proof-with-checked-results
        ((branches (proof-list-of-length (cdr value) 3))
         (yes (t4-printing-prove-result-run
               (1- n) printer (cadr branches) leaf
               (append tests (list (list (car branches) t))) known))
         (no (t4-printing-prove-result-run
              (1- n) (cdr yes) (caddr branches) leaf
              (append tests (list (list (car branches) nil))) known)))
        (t4-printing-join-result value template yes no)))
      ((null value) '(:failure "failure" ""))
      ((and (proof-compound value) (proof-compound (car value)))
       (proof-with-checked-results
        ((opening (proof-proof-beta (t4-printing-printed-list-proof printer) value))
         (opened (t4-printing-step-right opening))
         (result (t4-printing-prove-result-run (1- n) printer opened leaf tests known))
         (step (t4-printing-reverse-result (cdr result) (car result) opening template)))
        (cons step (cdr result))))
      (t
       (proof-with-checked-results
        ((result (t4-printing-printed-list-prove-result-visit
                  (1- n) value tests printer leaf known)))
        (t4-printing-check-leaf result value template))))))

 (defun t4-printing-printed-list-prove-result-visit (n node cases printer leaf known)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-printing-printed-list-prove-result-visit")
     (proof-with-checked-results
      ((found (t4-printing-evidence-find printer cases known (list *t4-printing-characters* node))))
      (let ((printer (cdr found)))
        (cond
         ((car found) found)
         ((proof-is-call node *proof-quote*) (t4-printing-printed-list-literal printer node))
         ((proof-is-call node *proof-cons*)
          (proof-with-checked-results
           ((head (proof-term-at node 1))
            (head-type (t4-printing-printed-list-character printer head cases))
            (tail (proof-term-at node 2))
            (tail-result (t4-printing-prove-result-run
                          (1- n) (cdr head-type) tail leaf cases known)))
           (t4-printing-printed-list-cons (cdr tail-result) (car head-type) (car tail-result))))
         ((proof-is-call node *t4-printing-append*)
          (proof-with-checked-results
           ((arguments (proof-list-of-length (cdr node) 2))
            (left (t4-printing-prove-result-run (1- n) printer (car arguments) leaf cases known))
            (right (t4-printing-prove-result-run (1- n) (cdr left) (cadr arguments) leaf cases known)))
           (t4-printing-append-result (car arguments) (cadr arguments) left right)))
         ((proof-is-call node *t4-printing-coerce*)
          (t4-printing-coerce-result printer node cases leaf))
         (t (t4-printing-evaluate-leaf node cases printer leaf))))))))

(defun t4-printing-printed-list-prove-result (printer value leaf tests known)
  (t4-printing-prove-result-run 1000000 printer value leaf tests known))

(defun t4-printing-digit-positive-path (printer n test)
  (let* ((proof (t4-printing-printed-list-proof printer))
         (zp-test (list *t4-printing-zp* n))
         (positive (library-positive n)))
    (if (not (equal (seq-slice test 1 3) (list zp-test zp-test)))
        '(:failure "inference-mismatch" "")
      (proof-with-checked-results
       ((denied (proof-proof-assume proof test nil))
        (assumed (proof-proof-assume proof zp-test t))
        (yes (proof-proof-if-true proof test))
        (positive-path (proof-proof-transport proof assumed yes))
        (cut (proof-proof-cut proof positive-path denied))
        (not-zp (proof-proof-front proof cut (proof-neg zp-test)))
        (zp-view (proof-proof-unfold proof zp-test))
        (zp-body (t4-printing-step-right zp-view))
        (zp-false (proof-proof-if-false proof zp-body))
        (noninteger (proof-proof-chain proof zp-view (list zp-false)))
        (noninteger (proof-proof-true-from-eq proof noninteger))
        (cut (proof-proof-cut proof noninteger not-zp))
        (i-n (proof-proof-front proof cut (library-integer n)))
        (integer-path (t4-printing-printed-list-pick printer zp-view i-n))
        (doubled (proof-proof-rewrite proof not-zp integer-path '(1 1)))
        (denied (proof-proof-assume proof positive nil))
        (cut (proof-proof-cut proof denied doubled))
        (positive-n (proof-proof-front proof cut positive)))
       (list i-n positive-n)))))

(defun t4-printing-integer-recur-case
    (printer n radix ans claim view body recur test accumulator i-r large-r)
  (proof-with-checked-results
   ((positive-path (t4-printing-digit-positive-path printer n test))
    (bounds (t4-division-floor-bound (t4-printing-printed-list-lib printer)
                                     n radix (car positive-path) i-r (cadr positive-path) large-r))
    (parts (proof-list-of-length (car bounds) 3)))
   (let* ((lib (cdr bounds))
          (printer (t4-printing-printed-list-with-lib printer lib))
          (q (list *t4-division-floor* n radix)))
     (proof-with-checked-results
      ((decreases (library-library-cite
                   lib "NFIX-DECREASE" (list q n)
                   (list (car parts) (car positive-path) (cadr positive-path) (caddr parts)))))
      (if (not (equal (seq-slice recur :none 3) (list *t4-printing-print-integer* q radix)))
          '(:failure "inference-mismatch" "")
        (proof-with-checked-results
         ((next-ans (proof-term-at recur 3))
          (new-ans (t4-printing-printed-list-prove-result
                    printer next-ans '(:missing-value) nil (list accumulator))))
         (let* ((printer (cdr new-ans))
                (lib (t4-printing-printed-list-lib printer))
                (proof (library-library-proof lib))
                (bindings (list (list n q) (list ans next-ans))))
           (proof-with-checked-results
            ((test-term (proof-step-first decreases))
             (instance (proof-subst claim (list (cons n q) (cons ans next-ans))))
             (hypothesis (proof-proof-assume proof (proof-ite test-term instance *proof-true*) t))
             (ih (proof-proof-prove-if proof hypothesis decreases))
             (guard (t4-division-combine lib (list i-r large-r (car new-ans))))
             (no (proof-proof-modus-ponens proof ih guard))
             (false-branch (proof-proof-if-false proof body))
             (opened (proof-proof-chain proof view (list false-branch)))
             (no (t4-printing-printed-list-unroll printer no opened)))
            (list no printer bindings)))))))))

(defun t4-printing-printed-list-integer-digits (printer)
  (let* ((lib (t4-printing-printed-list-lib printer))
         (proof (library-library-proof lib))
         (n *library-x*)
         (radix *library-y*)
         (ans *library-z*)
         (call (list *t4-printing-print-integer* n radix ans)))
    (proof-with-checked-results
     ((guard (t4-division-conjunction (list (library-integer radix)
                                            (library-lt *proof-one* radix)
                                            (list *t4-printing-characters* ans))))
      (assumed (proof-proof-assume proof guard t))
      (pieces (t4-division-pieces lib assumed))
      (pieces (proof-list-of-length pieces 3))
      (view (proof-proof-unfold proof call))
      (body (t4-printing-step-right view))
      (body-parts (proof-list-of-length body 4)))
     (let ((claim (list *library-implies* guard (list *t4-printing-characters* call)))
           (test (cadr body-parts))
           (accumulator (caddr pieces)))
       (proof-with-checked-results
        ((base (t4-printing-printed-list-prove-result
                printer (caddr body-parts) '(:missing-value) nil (list accumulator))))
        (let* ((printer (cdr base))
               (proof (t4-printing-printed-list-proof printer)))
          (proof-with-checked-results
           ((true-branch (proof-proof-if-true proof body))
            (opened (proof-proof-chain proof view (list true-branch)))
            (yes (t4-printing-printed-list-unroll printer (car base) opened))
            (negative (t4-printing-integer-recur-case
                       printer n radix ans claim view body (cadddr body-parts) test
                       accumulator (car pieces) (cadr pieces))))
           (let* ((printer (cadr negative))
                  (lib (t4-printing-printed-list-lib printer))
                  (proof (library-library-proof lib))
                  (measure (list *library-nfix* n)))
             (proof-with-checked-results
              ((branches (proof-proof-cases proof test yes (car negative)))
               (cases (t4-ordinals-ordinals-imply lib guard branches))
               (ordinal (library-library-cite lib "NFIX-ORDINAL" (list n) nil))
               (step (proof-proof-induct proof ordinal cases claim measure (list (caddr negative))))
               (lib (library-library-lemma lib "PRINT-INTEGER-CHARACTERS" claim step nil)))
              (t4-printing-printed-list-with-lib printer lib))))))))))

(defun t4-printing-atom-integer-proof (printer obj radix rational-opened integer-test i-r large-r)
  (proof-with-checked-results
   ((integer-opened (t4-printing-printed-list-pick printer rational-opened integer-test))
    (value (t4-printing-step-right integer-opened))
    (result (t4-printing-printed-list-prove-result
             printer value (list :primitive i-r large-r) nil nil)))
   (let* ((printer (cdr result))
          (lib (t4-printing-printed-list-lib printer))
          (proof (library-library-proof lib)))
     (proof-with-checked-results
      ((result (t4-printing-printed-list-unroll printer (car result) integer-opened))
       (guard (t4-division-conjunction (list (library-integer radix)
                                              (library-lt *proof-one* radix)
                                              (library-integer obj))))
       (assumed (proof-proof-assume proof guard t))
       (parts (t4-division-pieces lib assumed))
       (parts (proof-list-of-length parts 3))
       (axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list obj)))
       (exact-is-rational (proof-proof-modus-ponens proof axiom (caddr parts)))
       (radix-guard (t4-division-combine lib (list (car parts) (cadr parts))))
       (result (proof-proof-discharge proof result radix-guard))
       (result (proof-proof-discharge proof result exact-is-rational))
       (result (proof-proof-discharge proof result (caddr parts)))
       (ira (t4-ordinals-ordinals-imply lib guard result))
       (claim (proof-step-first ira))
       (lib (library-library-lemma lib "PRINT-ATOM-OF-INTEGER" claim ira nil)))
      (t4-printing-printed-list-with-lib printer lib)))))

(defun t4-printing-atom-rational-proof
    (printer obj radix rational rational-test rational-opened i-r large-r)
  (let* ((lib (t4-printing-printed-list-lib printer))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((axiom (library-library-axiom lib "RATIONAL-IMPLIES1" (list obj)))
      (rational-types (proof-proof-modus-ponens proof axiom rational-test))
      (parts (t4-division-pieces lib rational-types))
      (parts (proof-list-of-length parts 3))
      (value (t4-printing-step-right rational-opened))
      (result (t4-printing-printed-list-prove-result
               printer value (list :numerator i-r large-r (cadr parts) obj) nil nil)))
     (let* ((printer (cdr result))
            (lib (t4-printing-printed-list-lib printer))
            (proof (library-library-proof lib)))
       (proof-with-checked-results
        ((result (t4-printing-printed-list-unroll printer (car result) rational-opened))
         (guard (t4-division-conjunction (list (library-integer radix)
                                                (library-lt *proof-one* radix) rational)))
         (assumed (proof-proof-assume proof guard t))
         (parts (t4-division-pieces lib assumed))
         (parts (proof-list-of-length parts 3))
         (radix-guard (t4-division-combine lib (list (car parts) (cadr parts))))
         (specialized (proof-proof-discharge proof result radix-guard))
         (discharged (proof-proof-discharge proof specialized (caddr parts)))
         (rat (t4-ordinals-ordinals-imply lib guard discharged))
         (claim (proof-step-first rat))
         (lib (library-library-lemma lib "PRINT-ATOM-OF-RATIONAL" claim rat nil)))
        (cons result (t4-printing-printed-list-with-lib printer lib)))))))

(defun t4-printing-atom-other-proof (printer obj rational root i-r large-r)
  (let* ((lib (t4-printing-printed-list-lib printer))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((axiom (library-library-axiom lib "COMPLEX-IMPLIES1" (list obj)))
      (parts (t4-division-pieces lib axiom))
      (parts (proof-list-of-length parts 2))
      (denied (proof-proof-assume proof rational nil))
      (nonrational (t4-printing-printed-list-pick printer root denied))
      (value (t4-printing-step-right nonrational))
      (result (t4-printing-printed-list-prove-result
               printer value (list :complex-part i-r large-r (car parts) (cadr parts) obj)
               nil nil))
      (step (t4-printing-printed-list-unroll (cdr result) (car result) nonrational)))
     (cons step (cdr result)))))

(defun t4-printing-printed-list-atoms (printer)
  (proof-with-checked-results ((printer (t4-printing-printed-list-integer-digits printer)))
    (let* ((lib (t4-printing-printed-list-lib printer))
           (proof (library-library-proof lib))
           (obj *library-x*)
           (radix *library-y*)
           (call (list *t4-printing-print-atom* obj radix))
           (rational (list *library-rationalp* obj)))
      (proof-with-checked-results
       ((guard (t4-division-conjunction (list (library-integer radix) (library-lt *proof-one* radix))))
        (assumed (proof-proof-assume proof guard t))
        (parts (t4-division-pieces lib assumed))
        (parts (proof-list-of-length parts 2))
        (rational-test (proof-proof-assume proof rational t))
        (integer-test (proof-proof-assume proof (library-integer obj) t))
        (root (proof-proof-unfold proof call))
        (rational-opened (t4-printing-printed-list-pick printer root rational-test))
        (printer (t4-printing-atom-integer-proof
                  printer obj radix rational-opened integer-test (car parts) (cadr parts)))
        (yes (t4-printing-atom-rational-proof
              printer obj radix rational rational-test rational-opened (car parts) (cadr parts)))
        (no (t4-printing-atom-other-proof (cdr yes) obj rational root (car parts) (cadr parts))))
       (let* ((printer (cdr no))
              (lib (t4-printing-printed-list-lib printer))
              (proof (library-library-proof lib)))
         (proof-with-checked-results
          ((cases (proof-proof-cases proof rational (car yes) (car no)))
           (step (t4-ordinals-ordinals-imply lib guard cases))
           (claim (proof-step-first step))
           (lib (library-library-lemma lib "PRINT-ATOM-CHARACTERS" claim step nil)))
          (t4-printing-printed-list-with-lib printer lib)))))))

(defun t4-printing-character-results-goals (group obj)
  (if (endp group)
      nil
    (cons (list *t4-printing-characters* (list (car group) obj))
          (t4-printing-character-results-goals (cdr group) obj))))

(defun t4-printing-character-results-proofs (goals printer leaf)
  (if (endp goals)
      (cons nil printer)
    (proof-with-checked-results
     ((opened (proof-proof-unfold (t4-printing-printed-list-proof printer)
                                  (cadar goals)))
      (value (t4-printing-step-right opened))
      (result (t4-printing-printed-list-prove-result printer value leaf nil nil))
      (step (t4-printing-printed-list-unroll (cdr result) (car result) opened))
      (rest (t4-printing-character-results-proofs (cdr goals) (cdr result) leaf)))
     (cons (cons step (car rest)) (cdr rest)))))

(defun t4-printing-character-results-lemma (lib name group arithmetic)
  (let* ((obj *library-x*)
         (goals (t4-printing-character-results-goals group obj))
         (bindings (list (list (list obj (list *library-car* obj)))
                         (list (list obj (list *library-cdr* obj))))))
    (proof-with-checked-results
     ((joint (t4-division-conjunction goals))
      (lib (if arithmetic lib (library-library-build lib)))
      (printer (t4-printing-printed-list-init lib))
      (printer (if (t4-printing-lemma-present-p lib "PRINT-ATOM-CHARACTERS")
                   printer
                 (t4-printing-printed-list-atoms printer)))
      (proofs (t4-printing-character-results-proofs
               goals printer (list :character-results group joint obj))))
     (let* ((lib (t4-printing-printed-list-lib (cdr proofs)))
            (proof (library-library-proof lib)))
       (proof-with-checked-results
        ((cases (t4-division-combine lib (car proofs)))
         (ordinal (library-library-builtin lib 1 obj))
         (step (proof-proof-induct proof ordinal cases joint
                                   (t4-structural-count obj) bindings)))
        (library-library-lemma lib name joint step nil))))))

(defun t4-printing-character-results-call (call group)
  (proof-with-checked-results
   ((first (proof-term-at group 0))
    (package-bytes (proof-term-at first 1))
    (name-bytes (proof-term-at first 2))
    (name (concatenate 'string "PRINTED-CHARACTERS-" package-bytes "-" name-bytes))
    (index (t4-printing-group-index group (car call))))
   (list call group name index)))

(defun t4-printing-character-results-target (formula mutual)
  (and (proof-is-call formula *t4-printing-characters*)
       (proof-with-checked-results ((call (proof-term-at formula 1)))
         (and (proof-compound call)
              (equal (len call) 2)
              (let ((entry (assoc-equal (car call) mutual)))
                (and entry
                     (not (proof-compound (cadr call)))
                     (t4-printing-character-results-call call (cdr entry))))))))

(defun t4-printing-character-results-arithmetic-needed-p (lib formula mutual)
  (proof-with-checked-results ((target (t4-printing-character-results-target formula mutual)))
    (and target (not (t4-printing-lemma-present-p lib (caddr target))))))

(defun t4-printing-character-results (lib formula mutual arithmetic)
  (proof-with-checked-results ((target (t4-printing-character-results-target formula mutual)))
    (if (not target)
        (cons nil lib)
      (let ((call (car target))
            (group (cadr target))
            (name (caddr target))
            (index (cadddr target)))
        (proof-with-checked-results
         ((lib (if (t4-printing-lemma-present-p lib name)
                   lib
                 (t4-printing-character-results-lemma lib name group arithmetic)))
          (fact (library-library-cite lib name (cdr call) nil))
          (parts (t4-division-pieces lib fact))
          (step (proof-term-at parts index)))
         (cons step lib))))))
