(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h2-sets-subset* (proof-sym "SUBSETP-EQUAL" "ACL2"))
(defconst *h2-sets-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h2-sets-list-fix* (proof-sym "TRUE-LIST-FIX" "ACL2"))
(defconst *h2-sets-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h2-sets-iff* (proof-sym "IFF" "ACL2"))
(defconst *h2-sets-set-equiv* (proof-sym "SET-EQUIV" "ACL2"))
(defconst *h2-sets-key* (proof-sym "K" "ACL2"))

(defmacro h2-sets-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (h2-search-stopped-p ,name)
             ,name
           (h2-sets-with-results ,(cdr bindings) ,result))))))

(defun h2-sets-term-at (term path)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      term
    (proof-with-checked-results ((argument (proof-term-at term (car path))))
      (h2-sets-term-at argument (cdr path)))))

(defun h2-sets-step-at (step path)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (h2-sets-term-at literal path)))

(defun h2-sets-pair-arguments (term)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) 2)))

(defun h2-sets-derive (proof formula definitions facts seeds)
  (h2-sets-with-results
      ((result (h2-book-logic-derive proof formula definitions facts nil 1 "" seeds nil 80))
       (step (car result)))
    (cons step (cdr result))))

(defun h2-sets-auxiliary (proof name formula definitions facts variable seeds cases)
  (h2-sets-with-results
      ((result (h2-book-logic-auxiliary proof name formula definitions facts variable 1 "" seeds cases 80))
       (fact-name (car result)))
    (cons fact-name (cdr result))))

(defun h2-sets-subset-laws-build (proof names)
  (let ((x *library-x*) (y *library-y*) (z *library-z*)
        (k *h2-sets-key*) (subset *h2-sets-subset*)
        (member *h2-sets-member*) (implies *library-implies*))
    (h2-sets-with-results
        ((nonnil (h2-book-logic-nonnil-cons proof))
         (nonnil-name (car nonnil))
         (proof (cdr nonnil))
         (member-condition (proof-ite (list member k x) (list subset x y) *proof-false*))
         (subset-condition (proof-ite (list subset x y) (list subset y z) *proof-false*))
         (member-law (h2-sets-auxiliary
                      proof "MEMBER-OF-SUBSET"
                      (list implies member-condition (list member k y))
                      "SUBSETP-EQUAL MEMBER-EQUAL" (list nonnil-name) "X" nil nil))
         (growth (h2-sets-auxiliary
                  (cdr member-law) "SUBSET-CONS-RIGHT"
                  (list implies (list subset x y) (list subset x (list *proof-cons* k y)))
                  "SUBSETP-EQUAL MEMBER-EQUAL" (list nonnil-name) "X" nil nil))
         (transitive (h2-sets-auxiliary
                      (cdr growth) "SUBSET-TRANSITIVE"
                      (list implies subset-condition (list subset x z))
                      "SUBSETP-EQUAL" (list (car member-law)) "X" nil nil))
         (boolean (h2-sets-auxiliary
                   (cdr transitive) "SUBSET-BOOLEAN"
                   (list *h2-sets-booleanp* (list subset x y))
                   "SUBSETP-EQUAL BOOLEANP" nil "X" nil nil))
         (proof (cdr boolean))
         (library (h2-search-search-library proof))
         (base (library-library-proof library))
         (test (list *proof-consp* x))
         (head (list *library-car* x))
         (tail (list *library-cdr* x))
         (cons-step (proof-proof-assume base test t))
         (builtin (library-library-builtin library 3 x))
         (smaller (proof-proof-discharge base builtin cons-step))
         (smaller-literal (proof-step-first smaller))
         (hypothesis (proof-proof-assume
                      base (proof-ite smaller-literal (list subset tail tail) *proof-true*) t))
         (smaller-subset (proof-proof-prove-if base hypothesis smaller))
         (grow (proof-proof-fact base (proof-sym (car growth) "ACL2")
                                (list (list x tail) (list y tail) (list k head))))
         (bigger-subset (proof-proof-modus-ponens base grow smaller-subset))
         (elimination (library-library-axiom library "CAR-CDR-ELIM" (list x)))
         (stored-pair (proof-proof-modus-ponens base elimination cons-step))
         (retained (proof-proof-rewrite base bigger-subset stored-pair '(1 2)))
         (reflexive (list subset x x))
         (yes (h2-sets-derive proof reflexive "SUBSETP-EQUAL MEMBER-EQUAL"
                             (list nonnil-name) (list cons-step retained)))
         (proof (cdr yes))
         (base (library-library-proof (h2-search-search-library proof)))
         (not-cons (proof-proof-assume base test nil))
         (no (h2-sets-derive proof reflexive "SUBSETP-EQUAL" nil (list not-cons)))
         (proof (cdr no))
         (library (h2-search-search-library proof))
         (base (library-library-proof library))
         (ordinal (library-library-builtin library 1 x))
         (case-step (proof-proof-cases base test (car yes) (car no)))
         (step (proof-proof-induct base ordinal case-step reflexive
                                   (list *library-count* x) (list (list (list x tail)))))
         (library (library-library-lemma library "H2-SUBSET-REFLEXIVE" reflexive step nil)))
      (cons names (h2-search-search-with-library proof library)))))

(defun h2-sets-subset-laws (proof)
  (let* ((names '("SELF-H2-SUBSET-REFLEXIVE" "SELF-H2-SUBSET-TRANSITIVE"
                  "SELF-H2-SUBSET-BOOLEAN"))
         (library (h2-search-search-library proof))
         (base (library-library-proof library)))
    (if (assoc-equal (proof-sym (car names) "ACL2") (proof-proof-facts base))
        (cons names proof)
      (h2-sets-subset-laws-build proof names))))

(defun h2-sets-subset-fix-right (proof)
  (let* ((x *library-x*) (y *library-y*) (k *h2-sets-key*)
         (subset *h2-sets-subset*) (implies *library-implies*)
         (fixed-y (list *h2-sets-list-fix* y))
         (a (list *h2-sets-member* k fixed-y))
         (b (list *h2-sets-member* k y)))
    (h2-sets-with-results
        ((nonnil (h2-book-logic-nonnil-cons proof))
         (nonnil-name (car nonnil))
         (member (h2-sets-auxiliary (cdr nonnil) "MEMBER-OF-FIX" (list *h2-sets-iff* a b)
                                   "TRUE-LIST-FIX MEMBER-EQUAL" (list nonnil-name) "Y" nil nil))
         (base (library-library-proof (h2-search-search-library (cdr member))))
         (iff (proof-proof-fact base (proof-sym (car member) "ACL2") nil))
         (to-raw (h2-sets-auxiliary (cdr member) "MEMBER-FIX-TO-RAW" (list implies a b)
                                   "" nil nil (list iff) (list b)))
         (to-fix (h2-sets-auxiliary (cdr to-raw) "MEMBER-RAW-TO-FIX" (list implies b a)
                                   "" nil nil (list iff) (list a)))
         (fixed (h2-sets-auxiliary (cdr to-fix) "SUBSET-FIX-RIGHT"
                                  (proof-eq (list subset x fixed-y) (list subset x y))
                                  "SUBSETP-EQUAL" (list (car to-raw) (car to-fix)) "X" nil nil)))
      (cdr fixed))))

(defun h2-sets-subset-fix (proof)
  (let* ((x *library-x*) (y *library-y*) (subset *h2-sets-subset*)
         (right-name "SELF-H2-SUBSET-FIX-RIGHT"))
    (h2-sets-with-results
        ((left (h2-sets-auxiliary
                proof "SUBSET-FIX-LEFT"
                (proof-eq (list subset (list *h2-sets-list-fix* x) y) (list subset x y))
                "SUBSETP-EQUAL TRUE-LIST-FIX" nil "X" nil nil))
         (proof (cdr left))
         (base (library-library-proof (h2-search-search-library proof)))
         (proof (if (assoc-equal (proof-sym right-name "ACL2") (proof-proof-facts base))
                    proof
                  (h2-sets-subset-fix-right proof))))
      (cons (list (car left) right-name) proof))))

(defun h2-sets-set-equivalence-type-at-leaf (value tests nil-boolean proof laws)
  (declare (ignore tests))
  (if (equal value *proof-false*)
      nil-boolean
    (proof-with-checked-results ((name (proof-term-at laws 2)))
      (library-library-axiom (h2-search-search-library proof) name (cdr value)))))

(defun h2-sets-set-equivalence-by-value (n value tests template nil-boolean proof laws)
  (declare (xargs :measure (nfix n)))
  (let ((base (library-library-proof (h2-search-search-library proof))))
    (cond
     ((zp n) '(:failure "fuel" "h2-sets-set-equivalence-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (test (car branches))
           (yes (h2-sets-set-equivalence-by-value
                 (1- n) (cadr branches) (append tests (list (list test t)))
                 template nil-boolean proof laws))
           (no (h2-sets-set-equivalence-by-value
                (1- n) (caddr branches) (append tests (list (list test nil)))
                template nil-boolean proof laws)))
        (proof-by-value-join base value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((beta (proof-proof-beta base value))
           (opened (h2-sets-step-at beta '(2)))
           (step (h2-sets-set-equivalence-by-value (1- n) opened tests template nil-boolean proof laws))
           (reversed (proof-proof-symmetric base beta)))
        (proof-proof-rewrite-result base step reversed template *proof-result*)))
     (t
      (let* ((step (h2-sets-set-equivalence-type-at-leaf value tests nil-boolean proof laws))
             (leaf (list (cons (list value tests) step))))
        (proof-proof-by-value base value template leaf tests))))))

(defun h2-sets-set-equivalence-results (proof goals laws)
  (declare (xargs :measure (acl2-count goals)))
  (if (endp goals)
      (cons nil proof)
    (h2-sets-with-results
        ((first (h2-sets-derive proof (car goals) "SET-EQUIV" laws nil))
         (rest (h2-sets-set-equivalence-results (cdr first) (cdr goals) laws)))
      (cons (cons (car first) (car rest)) (cdr rest)))))

(defun h2-sets-set-equivalence (proof formula laws)
  (let ((base (library-library-proof (h2-search-search-library proof)))
        (template (list *h2-sets-booleanp* *proof-result*)))
    (h2-sets-with-results
        ((boolean (proof-term-at formula 1))
         (reflexive (h2-sets-term-at formula '(2 1)))
         (symmetry (h2-sets-term-at formula '(2 2 1)))
         (transitivity (h2-sets-term-at formula '(2 2 2)))
         (subject (proof-term-at boolean 1))
         (opening (proof-proof-unfold base subject))
         (nil-boolean (h2-sets-derive proof (list *h2-sets-booleanp* *proof-false*)
                                     "BOOLEANP" nil nil))
         (proof (cdr nil-boolean))
         (library (h2-search-search-library proof))
         (value (h2-sets-step-at opening '(2)))
         (typed (h2-sets-set-equivalence-by-value 1000000 value nil template (car nil-boolean) proof laws))
         (typed (library-library-transport-argument library typed opening 1))
         (results (h2-sets-set-equivalence-results proof (list reflexive symmetry transitivity) laws))
         (proof (cdr results))
         (base (library-library-proof (h2-search-search-library proof)))
         (step (proof-proof-prove base formula (cons typed (car results)) nil)))
      (cons step proof))))

(defun h2-sets-list-to-set-fact (library base-step equality order a b left-fix right-fix)
  (let ((base (library-library-proof library)))
    (proof-with-checked-results
        ((both-fixed (proof-proof-rewrite base base-step equality (list 1 order)))
         (left (library-library-axiom library left-fix (list a (list *h2-sets-list-fix* b))))
         (only-right (proof-proof-rewrite base both-fixed left '(1)))
         (right (library-library-axiom library right-fix (list a b))))
      (proof-proof-rewrite base only-right right '(1)))))

(defun h2-sets-list-to-set (proof formula reflexive)
  (h2-sets-with-results
      ((fixes (h2-sets-subset-fix proof))
       (proof (cdr fixes))
       (library (h2-search-search-library proof))
       (base (library-library-proof library))
       (fields (h2-sets-pair-arguments formula))
       (condition (car fields))
       (claim (cadr fields))
       (sides (h2-sets-pair-arguments condition))
       (left (car sides))
       (right (cadr sides))
       (assumed (proof-proof-assume base condition t))
       (opening (h2-equivalence-opening-to-equal library condition))
       (equality (if opening
                     (proof-proof-rewrite base assumed opening '(1))
                   '(:failure "failure" "")))
       (base-step (library-library-axiom library reflexive (list (list *h2-sets-list-fix* left))))
       (left-fix (caar fixes))
       (right-fix (cadar fixes))
       (left-step (h2-sets-list-to-set-fact library base-step equality 2 left right left-fix right-fix))
       (right-step (h2-sets-list-to-set-fact library base-step equality 1 right left left-fix right-fix))
       (opening (proof-proof-unfold base claim))
       (target (h2-sets-step-at opening '(2)))
       (step (proof-proof-prove base target (list left-step right-step) nil))
       (result (proof-proof-transport base step opening))
       (step (h2-search-search-introduce proof formula result)))
    (cons step proof)))

(defun h2-sets-set-theorem (proof label formula)
  (if (not (member-equal label '("SET-EQUIV-IS-AN-EQUIVALENCE" "LIST-EQUIV-REFINES-SET-EQUIV"
                                "SUBSETP-REFL" "SUBSETP-TRANS")))
      (cons nil proof)
    (h2-sets-with-results
        ((laws (h2-sets-subset-laws proof))
         (proof (cdr laws))
         (laws (car laws)))
      (cond
       ((equal label "SET-EQUIV-IS-AN-EQUIVALENCE")
        (h2-sets-set-equivalence proof formula laws))
       ((equal label "LIST-EQUIV-REFINES-SET-EQUIV")
        (h2-sets-list-to-set proof formula (car laws)))
       (t
        (h2-sets-with-results
            ((view (h2-search-search-remove-wrappers proof formula))
             (target (if view (h2-sets-step-at view '(2)) formula))
             (result (h2-sets-derive proof target "" (seq-slice laws 0 2) nil)))
          (if view
              (let ((base (library-library-proof (h2-search-search-library (cdr result)))))
                (proof-with-checked-results ((step (proof-proof-transport base (car result) view)))
                  (cons step (cdr result))))
            result)))))))
