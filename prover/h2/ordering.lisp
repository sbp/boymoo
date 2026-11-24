(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-ordering-coerce* (proof-cl "COERCE"))
(defconst *h2-ordering-stringp* (proof-cl "STRINGP"))
(defconst *h2-ordering-string-lt* (proof-cl "STRING<"))
(defconst *h2-ordering-symbolp* (proof-cl "SYMBOLP"))
(defconst *h2-ordering-iff* (proof-sym "IFF" "ACL2"))
(defconst *h2-ordering-symbol-lt* (proof-sym "SYMBOL<" "ACL2"))
(defconst *h2-ordering-list-lt* (proof-sym "STRING<-L" "ACL2"))
(defconst *h2-ordering-character-order*
  (append *h2-arithmetic-integer-rules*
          '("SELF-H2-INTEGER-NONNIL" "EQUAL-CHAR-CODE" "SELF-H2-LESS-IMPLIES-UNEQUAL")))

(defun h2-ordering-cons-parts (search step value index)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results
        ((premise (proof-proof-assume proof (list *proof-consp* value) t))
         (eliminate (library-library-axiom (h2-search-search-library search)
                                            "CAR-CDR-ELIM" (list value)))
         (parts (proof-proof-modus-ponens proof eliminate premise))
         (parts (proof-proof-symmetric proof parts)))
      (proof-proof-rewrite proof step parts (list 1 2 index)))))

(defun h2-ordering-eql-on-conses (search)
  (let* ((name "SELF-H2-EQUAL-CONS-BY-PARTS")
         (proof (h2-book-logic-proof search))
         (x *library-x*)
         (y *library-y*))
    (if (h2-book-logic-has-fact search name)
        (cons name search)
      (h2-book-logic-with-results search
          ((step (proof-proof-reflexive proof (proof-eq x y)))
           (step (h2-ordering-cons-parts search step x 1))
           (step (h2-ordering-cons-parts search step y 2))
           (equality (proof-proof-fact
                      proof (proof-sym "CONS-EQUAL" "ACL2")
                      (list (list (proof-sym "X1" "ACL2") (list *library-car* x))
                            (list (proof-sym "Y1" "ACL2") (list *library-cdr* x))
                            (list (proof-sym "X2" "ACL2") (list *library-car* y))
                            (list (proof-sym "Y2" "ACL2") (list *library-cdr* y)))))
           (step (proof-proof-chain proof step (list equality)))
           (claim (proof-step-first step))
           (search (h2-book-logic-add-lemma
                    search "H2-EQUAL-CONS-BY-PARTS" claim step
                    (list (proof-neg (list *proof-consp* x))
                          (proof-neg (list *proof-consp* y))))))
        (cons name search)))))

(defun h2-ordering-character-list-trichotomy-unequal (left evidence search)
  (let ((proof (h2-book-logic-proof search))
        (test (proof-eq *library-x* *library-y*)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test t))
         (alignment (proof-proof-rewrite proof left assumed '(1 1)))
         (impossible (proof-proof-cut proof alignment evidence)))
      (proof-proof-front proof impossible (proof-neg test)))))

(defun h2-ordering-character-list-trichotomy-separate-seeds (search left right x-cons y-cons)
  (let ((proof (h2-book-logic-proof search)))
    (cond ((and left (not right))
           (proof-with-checked-results
               ((different (h2-ordering-character-list-trichotomy-unequal x-cons y-cons search)))
             (list different)))
          ((and right (not left))
           (let ((test (proof-eq *library-x* *library-y*)))
             (proof-with-checked-results
                 ((same (proof-proof-assume proof test t))
                  (same (proof-proof-symmetric proof same))
                  (aligned (proof-proof-rewrite proof y-cons same '(1 1)))
                  (impossible (proof-proof-cut proof aligned x-cons))
                  (different (proof-proof-front proof impossible (proof-neg test))))
               (list different))))
          (t nil))))

(defun h2-ordering-character-list-trichotomy-separate
    (left right search sx sy premise expected)
  (let ((proof (h2-book-logic-proof search)))
    (h2-book-logic-with-results search
        ((x-cons (proof-proof-assume proof sx left))
         (y-cons (proof-proof-assume proof sy right))
         (extra (h2-ordering-character-list-trichotomy-separate-seeds
                 search left right x-cons y-cons)))
      (h2-book-logic-search-call search :solve
                                 (list expected (list* premise x-cons y-cons extra) nil)))))

(defun h2-ordering-character-list-trichotomy-compare
    (search expected heads premise x-cons y-cons)
  (let* ((proof (h2-book-logic-proof search))
         (x *library-x*) (y *library-y*)
         (car-x (list *library-car* x))
         (car-y (list *library-car* y))
         (same-terms (proof-eq x y)))
    (h2-book-logic-with-results search
        ((different-heads (proof-proof-assume proof heads nil))
         (same-list (proof-proof-assume proof same-terms t))
         (same-head (proof-proof-reflexive proof car-x))
         (same-head (proof-proof-rewrite proof same-head same-list '(1 2 1)))
         (different (proof-proof-cut proof same-head different-heads))
         (different (proof-proof-front proof different (proof-neg same-terms)))
         (seeds (list premise x-cons y-cons different-heads different))
         (first-code (list (proof-cl "CHAR-CODE") car-x))
         (second-code (list (proof-cl "CHAR-CODE") car-y))
         (code-equality (proof-eq first-code second-code))
         (same-code (proof-proof-assume proof code-equality t))
         ((head-identity search)
          (h2-book-logic-search-call search :solve
                                     (list heads (list premise x-cons y-cons same-code) nil)))
         (distinct-codes (proof-proof-cut proof head-identity different-heads))
         (distinct-codes (proof-proof-front proof distinct-codes (proof-neg code-equality)))
         ((not-less search)
          (h2-book-logic-search-call search :solve
                                     (list (proof-neg (library-lt first-code second-code)) seeds nil)))
         ((greater search)
          (h2-book-logic-search-call search :solve
                                     (list (library-lt second-code first-code)
                                           (append seeds (list distinct-codes not-less)) nil))))
      (h2-book-logic-search-call search :solve (list expected (append seeds (list greater)) nil)))))

(defun h2-ordering-character-list-trichotomy-finish
    (search formula expected heads sx sy premise x-cons y-cons same bindings)
  (let ((proof (h2-book-logic-proof search))
        (library (h2-search-search-library search)))
    (h2-book-logic-with-results search
        (((comparison search)
          (h2-ordering-character-list-trichotomy-compare
           search expected heads premise x-cons y-cons))
         (both (proof-proof-cases proof heads same comparison))
         ((left-only search) (h2-ordering-character-list-trichotomy-separate
                              t nil search sx sy premise expected))
         (x-present (proof-proof-cases proof sy both left-only))
         ((right-only search) (h2-ordering-character-list-trichotomy-separate
                               nil t search sx sy premise expected))
         ((neither search) (h2-ordering-character-list-trichotomy-separate
                            nil nil search sx sy premise expected))
         (x-absent (proof-proof-cases proof sy right-only neither))
         (case-step (proof-proof-cases proof sx x-present x-absent))
         (result (h2-search-search-introduce search formula case-step))
         (ordinal (library-library-builtin library 1 *library-x*)))
      (cons (proof-proof-induct proof ordinal result formula (list *library-count* *library-x*)
                                (list bindings))
            search))))

(defun h2-ordering-character-list-trichotomy (search formula)
  (let* ((library (h2-search-search-library search))
         (proof (library-library-proof library))
         (x *library-x*) (y *library-y*)
         (i (proof-sym "I" "ACL2")) (j (proof-sym "J" "ACL2"))
         (sx (list *proof-consp* x)) (sy (list *proof-consp* y))
         (heads (proof-eq (list *library-car* x) (list *library-car* y)))
         (tail-x (list *library-cdr* x)) (tail-y (list *library-cdr* y))
         (next-i (library-plus i *proof-one*)) (next-j (library-plus j *proof-one*))
         (bindings (list (list x tail-x) (list y tail-y) (list i next-i) (list j next-j))))
    (h2-book-logic-with-results search
        ((smaller (proof-subst formula (h2-book-logic-zip-bindings
                                       (list x y i j) (list tail-x tail-y next-i next-j) nil)))
         (descent (library-library-builtin library 3 x))
         (descent-claim (proof-step-first descent))
         (hypothesis (proof-proof-assume proof (proof-ite descent-claim smaller *proof-true*) t))
         (expected (proof-term-at formula 2))
         (premise-term (proof-term-at formula 1))
         (premise (proof-proof-assume proof premise-term t))
         (conjuncts (proof-proof-conjunct proof premise))
         (not-ordered (car conjuncts))
         (search (h2-book-logic-set-rules search "STRING<-L CHAR< CHARACTER-LISTP"
                                          *h2-ordering-character-order* "" 28))
         (x-cons (proof-proof-assume proof sx t))
         (y-cons (proof-proof-assume proof sy t))
         (equal-heads (proof-proof-assume proof heads t))
         (same-seeds (list premise x-cons y-cons equal-heads))
         ((forward search)
          (h2-book-logic-search-call
           search :solve
           (list (proof-eq (list *h2-ordering-list-lt* x y i)
                           (list *h2-ordering-list-lt* tail-x tail-y next-i))
                 same-seeds nil)))
         ((backward search)
          (h2-book-logic-search-call
           search :solve
           (list (proof-eq (list *h2-ordering-list-lt* y x j)
                           (list *h2-ordering-list-lt* tail-y tail-x next-j))
                 same-seeds nil)))
         (reduced (proof-proof-rewrite proof not-ordered forward '(1 1)))
         (ih (proof-proof-prove-if proof hypothesis descent))
         (condition-term (proof-term-at smaller 1))
         ((condition search)
          (h2-book-logic-search-call search :solve
                                     (list condition-term (append same-seeds (list reduced)) nil)))
         (result (proof-proof-modus-ponens proof ih condition))
         ((parts-name search) (h2-ordering-eql-on-conses search))
         (proof (h2-book-logic-proof search))
         (parts (proof-proof-use proof (proof-sym parts-name "ACL2") nil (list x-cons y-cons)))
         (parts (h2-book-logic-select-body search parts equal-heads))
         (backward (proof-proof-symmetric proof backward))
         (same (proof-proof-rewrite proof result backward '(1 1)))
         (parts (proof-proof-symmetric proof parts))
         (same (proof-proof-rewrite proof same parts '(1 2 1))))
      (h2-ordering-character-list-trichotomy-finish
       search formula expected heads sx sy premise x-cons y-cons same bindings))))

(defun h2-ordering-list-updates (variables)
  (if (endp variables)
      nil
    (cons (list (car variables) (list *library-cdr* (car variables)))
          (h2-ordering-list-updates (cdr variables)))))

(defun h2-ordering-index-updates (variables)
  (if (endp variables)
      nil
    (cons (list (car variables) (library-plus (car variables) *proof-one*))
          (h2-ordering-index-updates (cdr variables)))))

(defun h2-ordering-cons-tests (variables)
  (if (endp variables)
      nil
    (cons (list *proof-consp* (car variables))
          (h2-ordering-cons-tests (cdr variables)))))

(defun h2-ordering-character-list-order (search theorem formula)
  (h2-book-logic-with-results search
      ((library (h2-arithmetic-integer-order (h2-search-search-library search)))
       (search (h2-search-search-with-library search library)))
    (cond ((equal theorem "STRING<-L-TRICHOTOMY")
           (h2-ordering-character-list-trichotomy search formula))
          (t
           (let ((parameters
                  (assoc-equal
                   theorem
                   '(("STRING<-L-ASYMMETRIC"
                      (("sym" "ACL2" "X1") ("sym" "ACL2" "X2"))
                      (("sym" "ACL2" "I")) "EQLABLE-LISTP")
                     ("STRING<-L-TRANSITIVE"
                      (("sym" "ACL2" "X") ("sym" "ACL2" "Y") ("sym" "ACL2" "Z"))
                      (("sym" "ACL2" "I") ("sym" "ACL2" "J") ("sym" "ACL2" "K"))
                      "CHARACTER-LISTP")))))
             (if (not parameters)
                 (cons '(:failure "TacticInapplicable" "") search)
               (let* ((lists (cadr parameters))
                      (accumulators (caddr parameters))
                      (definitions (concatenate 'string "STRING<-L CHAR< " (cadddr parameters)))
                      (variable (car lists))
                      (measure (list *library-count* variable))
                      (updated (append (h2-ordering-list-updates lists)
                                       (h2-ordering-index-updates accumulators))))
                 (h2-book-logic-with-results search
                     ((search (h2-book-logic-set-rules search definitions
                                                      *h2-ordering-character-order* "" 90))
                      (ordinal (library-library-builtin library 1 variable)))
                   (h2-book-logic-search-call
                    search :induction
                    (list formula measure (list updated) ordinal
                          (h2-ordering-cons-tests lists)))))))))))

(defun h2-ordering-coerce-list (value)
  (list *h2-ordering-coerce* value (proof-quote (proof-cl "LIST"))))

(defun h2-ordering-equality-value (search test evidence)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results
        ((parts (if (integerp test)
                    (proof-term-at test 1)
                  (proof-list-of-length (cdr test) 2)))
         (literal (proof-step-first evidence)))
      (let ((left (car parts))
            (right (cadr parts)))
        (if (equal literal test)
            (proof-with-checked-results
                ((same (proof-proof-fact proof "equal-same" (list (list *library-x* left)))))
              (proof-proof-rewrite proof same evidence '(1 1 2)))
          (proof-with-checked-results
              ((different (proof-proof-fact proof "equal-different"
                                            (list (list *library-x* left) (list *library-y* right))))
               (different (proof-proof-front proof different (proof-eq test *proof-false*))))
            (proof-proof-discharge proof different evidence)))))))

(defun h2-ordering-equal-tests (search left right forward backward)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results
        ((positive (proof-proof-assume proof left t))
         (left-true (h2-ordering-equality-value search left positive))
         (right-true (h2-ordering-equality-value search right forward))
         (right-true (proof-proof-symmetric proof right-true))
         (yes (proof-proof-chain proof left-true (list right-true)))
         (negative (proof-proof-assume proof left nil))
         (denied (proof-proof-cut proof backward negative))
         (denied (proof-proof-front proof denied (proof-neg right)))
         (left-false (h2-ordering-equality-value search left negative))
         (right-false (h2-ordering-equality-value search right denied))
         (right-false (proof-proof-symmetric proof right-false))
         (no (proof-proof-chain proof left-false (list right-false))))
      (proof-proof-cases proof left yes no))))

(defun h2-ordering-coerce-inverse (search value)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results
        ((inverse (library-library-axiom (h2-search-search-library search)
                                         "COERCE-INVERSE-2" (list value)))
         (typed (proof-proof-assume proof (list *h2-ordering-stringp* value) t)))
      (proof-proof-modus-ponens proof inverse typed))))

(defun h2-ordering-coerce-injective (search)
  (let* ((name "SELF-H2-STRING-COERCE-INJECTIVE")
         (proof (h2-book-logic-proof search))
         (x *library-x*) (y *library-y*)
         (coerce-x (h2-ordering-coerce-list x))
         (coerce-y (h2-ordering-coerce-list y)))
    (if (h2-book-logic-has-fact search name)
        (cons name search)
      (let ((condition (proof-eq coerce-x coerce-y))
            (sx (list *h2-ordering-stringp* x))
            (sy (list *h2-ordering-stringp* y))
            (term (proof-eq x y)))
        (h2-book-logic-with-results search
            ((evidence (proof-proof-assume proof condition t))
             (ax (h2-ordering-coerce-inverse search x))
             (ay (h2-ordering-coerce-inverse search y))
             (ax (proof-proof-symmetric proof ax))
             (evidence (proof-proof-symmetric proof evidence))
             (ay (proof-proof-rewrite proof ay evidence '(1 1 1)))
             (forward (proof-proof-chain proof ax (list ay)))
             (backward (proof-proof-reflexive proof coerce-x))
             (same (proof-proof-assume proof term t))
             (backward (proof-proof-rewrite proof backward same '(1 2 1)))
             (step (h2-ordering-equal-tests search condition term forward backward))
             (claim (proof-step-first step))
             (search (h2-book-logic-add-lemma search "H2-STRING-COERCE-INJECTIVE"
                                              claim step (list (proof-neg sx) (proof-neg sy)))))
          (cons name search))))))

(defun h2-ordering-string-asymmetry (search)
  (let ((goal (list *library-implies*
                    (list *h2-ordering-string-lt* *library-x* *library-y*)
                    (proof-neg (list *h2-ordering-string-lt* *library-y* *library-x*)))))
    (h2-book-logic-auxiliary
     search "STRING<-ASYMMETRIC" goal "STRING<"
     '("STRING<-L-ASYMMETRIC" "CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP")
     nil 1 "" nil nil 80)))

(defun h2-ordering-string-trichotomy (search)
  (let* ((name "SELF-H2-STRING<-TRICHOTOMY")
         (proof (h2-book-logic-proof search))
         (x *library-x*) (y *library-y*)
         (xy (list *h2-ordering-string-lt* x y))
         (yx (list *h2-ordering-string-lt* y x)))
    (if (h2-book-logic-has-fact search name)
        (cons name search)
      (let* ((precondition (proof-ite (list *h2-ordering-stringp* x)
                                       (proof-ite (list *h2-ordering-stringp* y)
                                                  (proof-neg xy) *proof-false*)
                                       *proof-false*))
             (claim (list *library-implies* precondition
                          (list *h2-ordering-iff* yx (proof-neg (proof-eq x y))))))
        (h2-book-logic-with-results search
            ((premise (proof-proof-assume proof precondition t))
             (first (proof-proof-conjunct proof premise))
             (sx (car first))
             (second (proof-proof-conjunct proof (cadr first)))
             (sy (car second))
             (denied (cadr second))
             (theorem
              (proof-proof-fact
               proof (proof-sym "STRING<-L-TRICHOTOMY" "ACL2")
               (list (list x (h2-ordering-coerce-list x))
                     (list y (h2-ordering-coerce-list y))
                     (list (proof-sym "I" "ACL2") *proof-zero*)
                     (list (proof-sym "J" "ACL2") *proof-zero*))))
             (opened (proof-proof-unfold proof xy))
             (not-ordered (proof-proof-rewrite proof denied opened '(1 1)))
             (required (h2-book-logic-first-at theorem 1))
             ((test search)
              (h2-book-logic-derive search required "" nil nil 1 "" (list not-ordered) nil 80))
             (instance (proof-proof-modus-ponens proof theorem test))
             (opened (proof-proof-unfold proof yx))
             (opened (proof-proof-symmetric proof opened))
             (restored (proof-proof-rewrite proof instance opened '(1 1)))
             ((coerce-name search) (h2-ordering-coerce-injective search))
             (proof (h2-book-logic-proof search))
             (coerce-equal (proof-proof-use proof (proof-sym coerce-name "ACL2") nil (list sx sy)))
             (restored (proof-proof-rewrite proof restored coerce-equal '(1 2 1)))
             (step (h2-search-search-introduce search claim restored))
             (search (h2-book-logic-add-lemma search "H2-STRING<-TRICHOTOMY" claim step nil)))
          (cons name search))))))

(defun h2-ordering-symbol-trichotomy-equivalent
    (search shared-name names name-evidence field-equality first sx sy)
  (let ((proof (h2-book-logic-proof search))
        (symbol-equal (proof-eq *library-x* *library-y*)))
    (if shared-name
        (h2-book-logic-with-results search
            ((equal-field (proof-proof-assume proof field-equality t))
             ((eq-symbols search)
              (h2-book-logic-derive search symbol-equal "" '("SYMBOL-EQUALITY")
                                    nil 1 "" (list sx sy name-evidence equal-field) nil 80))
             (same (proof-proof-reflexive proof first))
             (same-symbol (proof-proof-assume proof symbol-equal t))
             (eq-fields (proof-proof-rewrite proof same same-symbol '(1 2 1))))
          (cons (h2-ordering-equal-tests search field-equality symbol-equal eq-symbols eq-fields)
                search))
      (h2-book-logic-with-results search
          ((same (proof-proof-reflexive proof first))
           (same-symbol (proof-proof-assume proof symbol-equal t))
           (eq-fields (proof-proof-rewrite proof same same-symbol '(1 2 1)))
           (no-symbols (proof-proof-cut proof eq-fields name-evidence))
           (no-symbols (proof-proof-front proof no-symbols (proof-neg symbol-equal)))
           (name-value (h2-ordering-equality-value search names name-evidence))
           (symbol-value (h2-ordering-equality-value search symbol-equal no-symbols))
           (symbol-value (proof-proof-symmetric proof symbol-value)))
        (cons (proof-proof-chain proof name-value (list symbol-value)) search)))))

(defun h2-ordering-symbol-trichotomy-branch
    (shared-name search names symbol-name package irreflexive not-ordered trichotomy sx sy)
  (let* ((proof (h2-book-logic-proof search))
         (x *library-x*) (y *library-y*)
         (field (if shared-name package symbol-name))
         (first (list field x))
         (second (list field y))
         (eq-field (proof-eq first second)))
    (h2-book-logic-with-results search
        ((name-evidence (proof-proof-assume proof names shared-name))
         ((forward search)
          (h2-book-logic-derive
           search (proof-eq (list *h2-ordering-symbol-lt* x y)
                            (list *h2-ordering-string-lt* first second))
           "SYMBOL<" (list irreflexive) nil 1 "" (list name-evidence) nil 80))
         ((backward search)
          (h2-book-logic-derive
           search (proof-eq (list *h2-ordering-symbol-lt* y x)
                            (list *h2-ordering-string-lt* second first))
           "SYMBOL<" (list irreflexive) nil 1 "" (list name-evidence) nil 80))
         (test (proof-proof-rewrite proof not-ordered forward '(1 1)))
         (theorem (library-library-axiom (h2-search-search-library search)
                                         trichotomy (list first second)))
         (condition (h2-book-logic-first-at theorem 1))
         ((derived search)
          (h2-book-logic-derive search condition "" nil nil 1 "" (list test) nil 80))
         (iff (proof-proof-modus-ponens proof theorem derived))
         ((equivalent search)
          (h2-ordering-symbol-trichotomy-equivalent
           search shared-name names name-evidence eq-field first sx sy))
         (iff (proof-proof-rewrite proof iff equivalent '(1 2 1)))
         (backward (proof-proof-symmetric proof backward)))
      (cons (proof-proof-rewrite proof iff backward '(1 1)) search))))

(defun h2-ordering-symbol-trichotomy (search formula)
  (let* ((x *library-x*) (y *library-y*)
         (strict (list *h2-ordering-string-lt* x x))
         (irreflexive "SELF-H2-STRING<-IRREFLEXIVE")
         (symbol-name (proof-cl "SYMBOL-NAME"))
         (package (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
         (names (proof-eq (list symbol-name x) (list symbol-name y))))
    (h2-book-logic-with-results search
        (((trichotomy search) (h2-ordering-string-trichotomy search))
         ((asymmetry search) (h2-ordering-string-asymmetry search))
         (proof (h2-book-logic-proof search))
         (axiom (library-library-axiom (h2-search-search-library search) asymmetry (list x x)))
         (strict-step (proof-proof-assume proof strict t))
         (denied (proof-proof-modus-ponens proof axiom strict-step))
         (search (if (h2-book-logic-has-fact search irreflexive)
                     search
                   (h2-book-logic-add-lemma search "H2-STRING<-IRREFLEXIVE"
                                            (proof-neg strict) denied nil)))
         (proof (h2-book-logic-proof search))
         (precondition (proof-term-at formula 1))
         (precondition (proof-proof-assume proof precondition t))
         (first-conjuncts (proof-proof-conjunct proof precondition))
         (sx (car first-conjuncts))
         (second-conjuncts (proof-proof-conjunct proof (cadr first-conjuncts)))
         (sy (car second-conjuncts))
         (not-ordered (cadr second-conjuncts))
         ((yes search)
          (h2-ordering-symbol-trichotomy-branch
           t search names symbol-name package irreflexive not-ordered trichotomy sx sy))
         ((no search)
          (h2-ordering-symbol-trichotomy-branch
           nil search names symbol-name package irreflexive not-ordered trichotomy sx sy))
         (end (proof-proof-cases proof names yes no)))
      (cons (h2-search-search-introduce search formula end) search))))

(defun h2-ordering-symbol-order-add-unequal (search asymmetry)
  (let* ((label "SELF-H2-STRING<-UNEQUAL")
         (library (h2-search-search-library search))
         (proof (library-library-proof library))
         (x *library-x*) (y *library-y*))
    (if (h2-book-logic-has-fact search label)
        (cons label search)
      (h2-book-logic-with-results search
          ((strict (proof-proof-assume proof (list *h2-ordering-string-lt* x y) t))
           (same (proof-eq x y))
           (same-step (proof-proof-assume proof same t))
           (same-step (proof-proof-symmetric proof same-step))
           (loop (proof-proof-rewrite proof strict same-step '(1 2)))
           (axiom (library-library-axiom library asymmetry (list x x)))
           (denied (proof-proof-modus-ponens proof axiom loop))
           (contradiction (proof-proof-cut proof loop denied))
           (step (proof-proof-front proof contradiction (proof-neg same)))
           (condition (proof-step-first strict))
           (search (h2-book-logic-add-lemma search "H2-STRING<-UNEQUAL" (proof-neg same)
                                            step (list (proof-neg condition)))))
        (cons label search)))))

(defun h2-ordering-symbol-order (search theorem formula)
  (cond
   ((equal theorem "SYMBOL<-ASYMMETRIC")
    (h2-book-logic-with-results search
        (((fact search) (h2-ordering-string-asymmetry search))
         ((label search) (h2-ordering-symbol-order-add-unequal search fact)))
      (h2-book-logic-derive search formula "SYMBOL<" (list fact label) nil 1 "" nil nil 40)))
   ((equal theorem "SYMBOL<-TRANSITIVE")
    (let* ((x *library-x*) (y *library-y*) (z *library-z*)
           (xy (list *h2-ordering-string-lt* x y))
           (yz (list *h2-ordering-string-lt* y z))
           (claim (list *library-implies* (proof-ite xy yz *proof-false*)
                        (list *h2-ordering-string-lt* x z))))
      (h2-book-logic-with-results search
          (((fact search)
            (h2-book-logic-auxiliary search "STRING<-TRANSITIVE" claim "STRING<"
                                     '("STRING<-L-TRANSITIVE") nil 1 "" nil nil 80)))
        (h2-book-logic-derive search formula "SYMBOL<" (list fact) nil 1 "" nil nil 50))))
   (t (h2-ordering-symbol-trichotomy search formula))))
