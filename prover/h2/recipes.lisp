(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-recipes-alistp* (proof-sym "ALISTP" "ACL2"))
(defconst *h2-recipes-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h2-recipes-list-listp* (proof-sym "TRUE-LIST-LISTP" "ACL2"))
(defconst *h2-recipes-zp* (proof-sym "ZP" "ACL2"))
(defconst *h2-recipes-length* (proof-cl "LENGTH"))
(defconst *h2-recipes-nth* (proof-cl "NTH"))
(defconst *h2-recipes-stringp* (proof-cl "STRINGP"))
(defconst *h2-recipes-symbolp* (proof-cl "SYMBOLP"))
(defconst *h2-recipes-state-fields*
  (concatenate 'string
               "OPEN-INPUT-CHANNELS OPEN-OUTPUT-CHANNELS GLOBAL-TABLE IDATES ACL2-ORACLE "
               "FILE-CLOCK READABLE-FILES WRITTEN-FILES READ-FILES WRITEABLE-FILES USER-STOBJ-ALIST1"))
(defconst *h2-recipes-countdown*
  '("built-in-clause-9" "SELF-INTEGER-SUM" "SELF-NONNEGATIVE-SUM"
    "SELF-POSITIVE-NONNEGATIVE" "SELF-POSITIVE-ONE-PLUS"))
(defconst *h2-recipes-alist-execution*
  '((("sym" "ACL2" "REMOVE-ASSOC-EQ-EXEC") . ("sym" "ACL2" "REMOVE-ASSOC--EQUAL"))
    (("sym" "ACL2" "REMOVE-ASSOC-EQL-EXEC") . ("sym" "ACL2" "REMOVE-ASSOC--EQUAL"))
    (("sym" "ACL2" "PUT-ASSOC-EQ-EXEC") . ("sym" "ACL2" "PUT-ASSOC--EQUAL"))
    (("sym" "ACL2" "PUT-ASSOC-EQL-EXEC") . ("sym" "ACL2" "PUT-ASSOC--EQUAL"))))
(defconst *h2-recipes-arrays*
  '(("sym" "ACL2" "ARRAY1P") ("sym" "ACL2" "ARRAY2P")))
(defconst *h2-recipes-state* (proof-sym "STATE-P1" "ACL2"))
(defconst *h2-recipes-state-reads*
  '(("sym" "ACL2" "READ-ACL2-ORACLE") ("sym" "ACL2" "READ-RUN-TIME")))
(defconst *h2-recipes-lower* (proof-cl "LOWER-CASE-P"))
(defconst *h2-recipes-upper* (proof-cl "UPPER-CASE-P"))
(defconst *h2-recipes-alpha* (proof-cl "ALPHA-CHAR-P"))
(defconst *h2-recipes-character* (proof-cl "CHARACTERP"))
(defconst *h2-recipes-standard* (proof-cl "STANDARD-CHAR-P"))
(defconst *h2-recipes-downcase* (proof-cl "CHAR-DOWNCASE"))
(defconst *h2-recipes-upcase* (proof-cl "CHAR-UPCASE"))
(defconst *h2-recipes-character-shapes*
  (list (list (list *library-implies* (list *h2-recipes-lower* *library-x*)
                    (list *h2-recipes-alpha* *library-x*))
              "LOWER-CASE-P-FORWARD-TO-ALPHA-CHAR-P")
        (list (list *library-implies* (list *h2-recipes-upper* *library-x*)
                    (list *h2-recipes-alpha* *library-x*))
              "UPPER-CASE-P-FORWARD-TO-ALPHA-CHAR-P")
        (list (list *library-implies* (list *h2-recipes-standard* *library-x*)
                    (list *h2-recipes-character* *library-x*))
              "STANDARD-CHAR-P-FORWARD-TO-CHARACTERP")
        (list (list *h2-recipes-character* (list *h2-recipes-downcase* *library-x*))
              "CHARACTERP-CHAR-DOWNCASE")
        (list (list *h2-recipes-character* (list *h2-recipes-upcase* *library-x*))
              "CHARACTERP-CHAR-UPCASE")
        (list (list *library-implies* (list *h2-recipes-upper* *library-x*)
                    (list *h2-recipes-lower* (list *h2-recipes-downcase* *library-x*)))
              "LOWER-CASE-P-CHAR-DOWNCASE")
        (list (list *library-implies* (list *h2-recipes-lower* *library-x*)
                    (list *h2-recipes-upper* (list *h2-recipes-upcase* *library-x*)))
              "UPPER-CASE-P-CHAR-UPCASE")))

(defconst *h2-recipes-list-proofs*
  '(("FIXNAT-ALISTP-FORWARD-TO-NAT-ALISTP" "FIXNAT-ALISTP NAT-ALISTP" "X" nil)
    ("BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP"
     "BOUNDED-INTEGER-ALISTP EQLABLE-ALISTP EQLABLEP" "X" nil)
    ("KEYWORD-VALUE-LISTP-ASSOC-KEYWORD" "KEYWORD-VALUE-LISTP ASSOC-KEYWORD" "L" nil)
    ("CONSP-ASSOC-EQUAL" "ALISTP ASSOC-EQUAL" "L" nil)
    ("ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP" "ACL2-NUMBER-LISTP TRUE-LISTP" "X" nil)
    ("RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP" "RATIONAL-LISTP ACL2-NUMBER-LISTP" "X" nil)
    ("INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP" "INTEGER-LISTP RATIONAL-LISTP" "X" nil)
    ("NAT-LISTP-FORWARD-TO-INTEGER-LISTP" "NAT-LISTP INTEGER-LISTP NATP" "X" nil)
    ("KNOWN-PACKAGE-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP"
     "KNOWN-PACKAGE-ALISTP TRUE-LIST-LISTP ALISTP" "X" nil)
    ("TIMER-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-SYMBOL-ALISTP"
     "TIMER-ALISTP TRUE-LIST-LISTP SYMBOL-ALISTP TRUE-LISTP" "X"
     ("RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP"
      "ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP"))
    ("TYPED-IO-LISTP-FORWARD-TO-TRUE-LISTP" "TYPED-IO-LISTP TRUE-LISTP" "X" nil)
    ("READABLE-FILES-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP"
     "READABLE-FILES-LISTP TRUE-LIST-LISTP ALISTP" "X"
     ("READABLE-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP"))
    ("WRITTEN-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP"
     "WRITTEN-FILE-LISTP TRUE-LIST-LISTP ALISTP" "X"
     ("WRITTEN-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP"))
    ("READ-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP" "READ-FILE-LISTP TRUE-LIST-LISTP" "X"
     ("READ-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP"))
    ("WRITABLE-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP" "WRITABLE-FILE-LISTP TRUE-LIST-LISTP" "X"
     ("WRITABLE-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP"))
    ("ALL-BOUNDP-PRESERVES-ASSOC-EQUAL" "ALL-BOUNDP ASSOC-EQUAL" "TBL1" nil)
    ("TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP-ASSOC-EQUAL" "TRUE-LIST-LISTP ASSOC-EQUAL TRUE-LISTP" "L" nil)
    ("CHARACTER-LISTP-STRING-DOWNCASE-1" "STRING-DOWNCASE1 CHARACTER-LISTP" "X"
     ("CHARACTERP-CHAR-DOWNCASE"))
    ("CHARACTER-LISTP-STRING-UPCASE1-1" "STRING-UPCASE1 CHARACTER-LISTP" "X"
     ("CHARACTERP-CHAR-UPCASE"))
    ("STRING-ALISTP-FORWARD-TO-ALISTP" "STRING-ALISTP ALISTP" "X" nil)))

(defconst *h2-recipes-direct-proofs*
  (append
   '(("ARRAY1P-FORWARD" "ARRAY1P" nil)
     ("ARRAY1P-LINEAR" "ARRAY1P" nil)
     ("ARRAY2P-FORWARD" "ARRAY2P" nil)
     ("ARRAY2P-LINEAR" "ARRAY2P" nil)
     ("OPEN-CHANNEL1-FORWARD-TO-TRUE-LISTP-AND-CONSP" "OPEN-CHANNEL1" nil)
     ("FILE-CLOCK-P-FORWARD-TO-INTEGERP" "FILE-CLOCK-P" nil)
     ("READABLE-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP" "READABLE-FILE" nil)
     ("READABLE-FILES-P-FORWARD-TO-READABLE-FILES-LISTP" "READABLE-FILES-P" nil)
     ("WRITTEN-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP" "WRITTEN-FILE" nil)
     ("WRITTEN-FILES-P-FORWARD-TO-WRITTEN-FILE-LISTP" "WRITTEN-FILES-P" nil)
     ("READ-FILES-P-FORWARD-TO-READ-FILE-LISTP" "READ-FILES-P" nil)
     ("WRITEABLE-FILES-P-FORWARD-TO-WRITABLE-FILE-LISTP" "WRITEABLE-FILES-P" nil))
   (list (list "STATE-P1-FORWARD" (concatenate 'string "STATE-P1 " *h2-recipes-state-fields*) nil))
   '(("STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1" "STATE-P" nil)
     ("INTEGER-RANGE-P-FORWARD" "INTEGER-RANGE-P" ("SELF-H2-INTEGER-SUCCESSOR-BOUND"))
     ("SIGNED-BYTE-P-FORWARD-TO-INTEGERP" "SIGNED-BYTE-P INTEGER-RANGE-P" nil)
     ("UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP" "UNSIGNED-BYTE-P INTEGER-RANGE-P" nil)
     ("NTH-0-CONS" "NTH ZP" nil)
     ("STRINGP-SUBSEQ-TYPE-PRESCRIPTION" "SUBSEQ" nil)
     ("NATP-RANDOM$" "RANDOM$ READ-ACL2-ORACLE MV-NTH ZP NATP" nil)
     ("RANDOM$-LINEAR" "RANDOM$ READ-ACL2-ORACLE MV-NTH ZP NATP POSP" nil)
     ("NTH-0-READ-RUN-TIME-TYPE-PRESCRIPTION" "NTH READ-RUN-TIME ZP" nil))))

(mutual-recursion
 (defun h2-recipes-calls-state-read (term)
   (declare (xargs :measure (acl2-count term)))
   (and (consp term)
        (proof-compound term)
        (not (equal (car term) *proof-quote*))
        (or (if (member-equal (car term) *h2-recipes-state-reads*) t nil)
            (h2-recipes-calls-state-read (car term))
            (h2-recipes-calls-state-read-list (cdr term)))))
 (defun h2-recipes-calls-state-read-list (terms)
   (declare (xargs :measure (acl2-count terms)))
   (and (consp terms)
        (or (h2-recipes-calls-state-read (car terms))
            (h2-recipes-calls-state-read-list (cdr terms))))))

(defun h2-recipes-make-recipes (search names)
  (list :h2-recipes search names))

(defun h2-recipes-recipes-search (recipes)
  (cadr recipes))

(defun h2-recipes-recipes-names (recipes)
  (caddr recipes))

(defun h2-recipes-recipes-with-search (recipes search)
  (h2-recipes-make-recipes search (h2-recipes-recipes-names recipes)))

(defun h2-recipes-recipes-with-names (recipes names)
  (h2-recipes-make-recipes (h2-recipes-recipes-search recipes) names))

(defun h2-recipes-step-left (step)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal 1))))

(defun h2-recipes-step-right (step)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal 2))))

(defun h2-recipes-add-fact (library name clause)
  (let* ((proof (library-library-proof library))
         (facts (table-put (proof-proof-facts proof) name clause)))
    (library-library-with-proof library (proof-proof-with-facts proof facts))))

(defun h2-recipes-admit-constraints (pairs library)
  (if (endp pairs)
      library
    (proof-with-checked-results ((pair (proof-list-of-length (car pairs) 2)))
      (h2-recipes-admit-constraints
       (cdr pairs) (h2-recipes-add-fact library (car pair) (list (cadr pair)))))))

; A trie node holds a completed name and a table of edges by character.
(defun h2-recipes-dependency-trie-put (chars name trie)
  (if (endp chars)
      (cons name (cdr trie))
    (let* ((ch (car chars))
           (edges (cdr trie))
           (child (h2-recipes-dependency-trie-put
                   (cdr chars) name (cdr (assoc-equal ch edges)))))
      (cons (car trie) (table-put edges ch child)))))

(defun h2-recipes-dependency-trie (entries trie)
  (if (endp entries)
      trie
    (proof-with-checked-results
        ((name (proof-term-at (car entries) 1))
         (symbol (proof-write name)))
      (h2-recipes-dependency-trie
       (cdr entries) (h2-recipes-dependency-trie-put (coerce symbol 'list) name trie)))))

(defun h2-recipes-dependency-match (chars trie needed)
  (let* ((name (car trie))
         (needed (if (and name (not (h2-search-index-find name needed)))
                     (h2-search-index-put name nil needed)
                   needed)))
    (if (or (endp chars) (endp (cdr trie)))
        needed
      (let ((child (cdr (assoc-equal (car chars) (cdr trie)))))
        (if child
            (h2-recipes-dependency-match (cdr chars) child needed)
          needed)))))

(defun h2-recipes-dependency-scan (chars edges needed)
  (if (endp chars)
      needed
    (let* ((child (cdr (assoc-equal (car chars) edges)))
           (needed (if child
                       (h2-recipes-dependency-match (cdr chars) child needed)
                     needed)))
      (h2-recipes-dependency-scan (cdr chars) edges needed))))

(defun h2-recipes-select-dependencies (entries edges needed selected)
  (if (endp entries)
      selected
    (proof-with-checked-results ((name (proof-term-at (car entries) 1)))
      (if (h2-search-index-find name needed)
          (proof-with-checked-results ((source (proof-term-at (car entries) 3)))
            (h2-recipes-select-dependencies
             (cdr entries) edges
             (h2-recipes-dependency-scan (coerce source 'list) edges needed)
             (cons (car entries) selected)))
        (h2-recipes-select-dependencies (cdr entries) edges needed selected)))))

(defun h2-recipes-library (recipes)
  (h2-search-search-library (h2-recipes-recipes-search recipes)))

(defun h2-recipes-with-library (recipes library)
  (h2-recipes-recipes-with-search
   recipes (h2-search-search-with-library (h2-recipes-recipes-search recipes) library)))

(defun h2-recipes-proof (recipes)
  (library-library-proof (h2-recipes-library recipes)))

(defun h2-recipes-has-fact-p (recipes name)
  (if (assoc-equal (proof-sym name "ACL2") (proof-proof-facts (h2-recipes-proof recipes)))
      t
    nil))

(defun h2-recipes-lemma (recipes name claim step conditions)
  (proof-with-checked-results
   ((search (h2-book-logic-add-lemma (h2-recipes-recipes-search recipes) name claim step conditions)))
   (h2-recipes-recipes-with-search recipes search)))

(defun h2-recipes-recipes-double-cdr-lemma (recipes)
  (let* ((library (h2-recipes-library recipes))
         (proof (library-library-proof library))
         (tail (list *library-cdr* *library-x*))
         (child (list *library-cdr* tail))
         (a (list *library-count* child))
         (b (list *library-count* tail))
         (c (list *library-count* *library-x*)))
    (proof-with-checked-results
     ((first-builtin (library-library-builtin library 3 tail))
      (first-comparison (library-library-ordinal-comparison library a b))
      (first (proof-proof-rewrite proof first-builtin first-comparison '(1)))
      (second-builtin (library-library-builtin library 3 *library-x*))
      (second-comparison (library-library-ordinal-comparison library b c))
      (second (proof-proof-rewrite proof second-builtin second-comparison '(1)))
      (chain (library-library-compare-chain library first second))
      (comparison (library-library-ordinal-comparison library a c))
      (result (proof-proof-transport proof chain comparison))
      (claim (proof-step-first result)))
     (h2-recipes-lemma recipes "H2-COUNT-CDDR-LESS" claim result
                       (list (proof-neg (list *proof-consp* *library-x*))
                             (proof-neg (list *proof-consp* tail)))))))

(defun h2-recipes-recipes-successor-bound (recipes)
  (let ((library (h2-recipes-library recipes))
        (proof (h2-recipes-proof recipes))
        (comparison (library-lt *library-x* (library-plus *proof-one* *library-y*)))
        (reverse-comparison (library-lt *library-y* *library-x*))
        (distance (library-diff *library-x* *library-y*)))
    (proof-with-checked-results
     ((integers (library-library-ints library (list *library-x* *library-y*)))
      (smaller (proof-proof-assume proof comparison t))
      (larger (proof-proof-assume proof reverse-comparison t))
      (distance-comparison (library-library-comparison library *library-y* *library-x* integers))
      (positive-distance (proof-proof-rewrite proof larger distance-comparison '(1)))
      (is-integer (library-library-type-of library distance integers))
      (integer-term (proof-step-first is-integer))
      (integer-positive (proof-proof-prove proof
                                          (proof-ite integer-term (library-positive distance) *proof-false*)
                                          (list is-integer positive-distance) nil))
      (fact (proof-proof-fact proof "integer-discrete" (list (list *library-x* distance))))
      (bound (proof-proof-modus-ponens proof fact integer-positive))
      (equal-comparison (library-library-comparison library distance *proof-one* integers))
      (right (library-library-comparison library *library-x* (library-plus *proof-one* *library-y*) integers))
      (common (library-library-linear-equal library (library-diff *proof-one* distance)
                                             (library-diff (library-plus *proof-one* *library-y*) *library-x*)
                                             integers))
      (equal-comparison (proof-proof-rewrite proof equal-comparison common '(1 2 2)))
      (reversed-right (proof-proof-symmetric proof right))
      (chain (proof-proof-chain proof equal-comparison (list reversed-right)))
      (bound (proof-proof-rewrite proof bound chain '(1 1)))
      (cut (proof-proof-cut proof smaller bound))
      (bound (proof-proof-front proof cut (proof-neg reverse-comparison)))
      (claim (proof-step-first bound)))
     (h2-recipes-lemma recipes "H2-INTEGER-SUCCESSOR-BOUND" claim bound
                       (list (proof-neg (library-integer *library-x*))
                             (proof-neg (library-integer *library-y*))
                             (proof-neg comparison))))))

(defun h2-recipes-recipes-init ()
  (let ((ground (proof-proof-init)))
    (proof-with-checked-results
     ((names (h2-book-logic-definition-names (proof-proof-definitions ground) nil))
      (library (library-library-build (library-library-init ground)))
      (recipes (h2-recipes-recipes-double-cdr-lemma
                (h2-recipes-make-recipes (h2-search-search-init library) names))))
     (h2-recipes-recipes-successor-bound recipes))))

(defun h2-recipes-admit-definitions (definitions recipes)
  (if (endp definitions)
      recipes
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3))
      (proof (proof-proof-add-definition (h2-recipes-proof recipes)
                                         (car definition) (cadr definition) (caddr definition)))
      (name (proof-term-at (car definition) 2)))
     (let* ((library (library-library-with-proof (h2-recipes-library recipes) proof))
            (names (table-put (h2-recipes-recipes-names recipes) name (car definition))))
       (h2-recipes-admit-definitions
        (cdr definitions)
        (h2-recipes-recipes-with-names (h2-recipes-with-library recipes library) names))))))

(defun h2-recipes-recipes-admit (recipes kind data)
  (cond ((equal kind "define") (h2-recipes-admit-definitions (cdr data) recipes))
        ((member-equal kind '("theorem" "axiom"))
         (proof-with-checked-results ((name (proof-term-at data 0)))
           (h2-recipes-with-library
            recipes (h2-recipes-add-fact (h2-recipes-library recipes) name (cdr data)))))
        ((equal kind "constrain")
         (proof-with-checked-results ((constraints (proof-term-at data 1)))
           (if (equal constraints *proof-nil*)
               recipes
             (proof-with-checked-results
              ((library (h2-recipes-admit-constraints constraints (h2-recipes-library recipes))))
              (h2-recipes-with-library recipes library)))))
        (t recipes)))

(defun h2-recipes-recipes-dependencies (recipes entry)
  (let ((entries (library-library-entries (h2-recipes-library recipes))))
    (proof-with-checked-results
        ((trie (h2-recipes-dependency-trie entries nil))
         (source (proof-term-at entry 3)))
      (h2-recipes-select-dependencies
       (reverse entries) (cdr trie)
       (h2-recipes-dependency-scan (coerce source 'list) (cdr trie) nil)
       (list entry)))))

(defmacro h2-recipes-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (h2-search-stopped-p ,name)
             ,name
           (h2-recipes-with-results ,(cdr bindings) ,result))))))

(defun h2-recipes-recipes-set-rules (recipes definitions facts repeat split-limit)
  (h2-recipes-with-results
   ((search (h2-book-logic-set-rules-with-names (h2-recipes-recipes-search recipes)
                                               (h2-recipes-recipes-names recipes)
                                               definitions facts repeat split-limit)))
   (h2-recipes-recipes-with-search recipes search)))

(defun h2-recipes-import-search-result (recipes pair)
  (h2-recipes-with-results ((pair pair) (result (car pair)))
    (cons result (h2-recipes-recipes-with-search recipes (cdr pair)))))

(defun h2-recipes-call-search (recipes method arguments)
  (h2-recipes-import-search-result
   recipes (h2-search-search-call-with-remainder (h2-recipes-recipes-search recipes) method arguments)))

(defun h2-recipes-recipes-derive (recipes formula definitions facts variable depth repeat seeds cases split-limit)
  (h2-recipes-with-results
   ((recipes (h2-recipes-recipes-set-rules recipes definitions facts repeat split-limit)))
   (if (and variable (not (equal variable "")))
       (h2-recipes-call-search recipes :list-induction (list formula (proof-sym variable "ACL2") nil depth))
     (h2-recipes-call-search recipes :solve (list formula seeds cases)))))

(defun h2-recipes-recipes-auxiliary (recipes name formula definitions facts variable depth repeat seeds cases split-limit)
  (let* ((lemma (concatenate 'string "H2-" name))
         (label (concatenate 'string "SELF-" lemma)))
    (if (h2-recipes-has-fact-p recipes label)
        (cons label recipes)
      (h2-recipes-with-results
       ((derived (h2-recipes-recipes-derive recipes formula definitions facts variable depth repeat seeds cases split-limit))
        (recipes (h2-recipes-lemma (cdr derived) lemma formula (car derived) nil)))
       (cons label recipes)))))

(defun h2-recipes-recipes-true-list-facts (recipes)
  (h2-recipes-with-results
   ((a (h2-recipes-recipes-auxiliary recipes "TRUE-LISTP-OF-CONS"
                                   (proof-eq (list *h2-recipes-listp* (list *proof-cons* *library-x* *library-y*))
                                             (list *h2-recipes-listp* *library-y*))
                                   "TRUE-LISTP" nil nil 1 "" nil nil 80))
    (b (h2-recipes-recipes-auxiliary (cdr a) "TRUE-LISTP-OF-CDR"
                                   (list *library-implies* (list *h2-recipes-listp* *library-x*)
                                         (list *h2-recipes-listp* (list *library-cdr* *library-x*)))
                                   "TRUE-LISTP" nil nil 1 "" nil nil 80)))
   (cons (list (car a) (car b)) (cdr b))))

(defun h2-recipes-recipes-index-induction (recipes formula variable definitions facts updated cases)
  (let* ((variable (proof-sym variable "ACL2"))
         (measure (list *library-count* variable))
         (substitution (cons (list variable (library-plus *proof-neg-one* variable)) updated)))
    (h2-recipes-with-results
     ((recipes (h2-recipes-recipes-set-rules recipes definitions (append *h2-recipes-countdown* facts) "" 80))
      (ordinal (library-library-builtin (h2-recipes-library recipes) 1 variable)))
     (h2-recipes-call-search recipes :induction (list formula measure (list substitution) ordinal cases)))))

(defun h2-recipes-call-derive (recipes arguments)
  (h2-recipes-recipes-derive recipes (nth 0 arguments) (nth 1 arguments) (nth 2 arguments)
                            (nth 3 arguments) (nth 4 arguments) (nth 5 arguments)
                            (nth 6 arguments) (nth 7 arguments) (nth 8 arguments)))

(defun h2-recipes-derivation-outcome (search operation arguments replies)
  (let* ((library (h2-search-search-library search))
         (result (case operation
                   (:index-lemmas (h2-arithmetic-index-lemmas library replies))
                   (:maximum-lemmas (h2-arithmetic-maximum-lemmas library replies))
                   (:array-extension (h2-alists-array-extension library (car arguments) replies))
                   (:ordered-alist (h2-alists-ordered-alist library replies))
                   (:ordered-changes (h2-alists-ordered-changes library (car arguments) (cadr arguments) replies))
                   (:channel-headers (h2-alists-channel-headers library (car arguments) replies))
                   (:assoc-after-add (h2-alists-assoc-after-add library (car arguments) (cadr arguments) replies)))))
    (cond ((failure-p result) (cons result search))
          ((and (member-eq operation '(:index-lemmas :maximum-lemmas))
                (not (h2-alists-request-p (car result))))
           (cons nil (h2-search-search-with-library search result)))
          (t (cons (car result) (h2-search-search-with-library search (cdr result)))))))

(defun h2-recipes-derivation-round (recipes operation arguments replies)
  (let* ((search (h2-recipes-recipes-search recipes))
         (round (h2-book-logic-with-saved-result search
                  (h2-recipes-derivation-outcome search operation arguments replies)))
         (value (car round))
         (recipes (h2-recipes-recipes-with-search recipes (cdr round))))
    (cond ((failure-p value) value)
          ((h2-alists-request-p value)
           (h2-recipes-with-results
               ((derived (h2-recipes-call-derive recipes (h2-alists-request-arguments value))))
             (list :retry (cdr derived)
                   (list (cons (car derived) (h2-recipes-library (cdr derived)))))))
          ((member-eq operation '(:index-lemmas :maximum-lemmas)) recipes)
          (t (cons value recipes)))))

(defun h2-recipes-run-derivation-rounds (n operation arguments round)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h2-recipes-run-derivation-rounds"))
        ((eq (car round) :retry)
         (h2-recipes-run-derivation-rounds
          (1- n) operation arguments
          (h2-recipes-derivation-round (cadr round) operation arguments (caddr round))))
        (t round)))

(defun h2-recipes-run-derivations (recipes operation arguments)
  (h2-recipes-run-derivation-rounds
   1000000 operation arguments
   (h2-recipes-derivation-round recipes operation arguments nil)))

(defun h2-recipes-index-lemmas (recipes)
  (h2-recipes-run-derivations recipes :index-lemmas nil))

(defun h2-recipes-maximum-lemmas (recipes)
  (h2-recipes-run-derivations recipes :maximum-lemmas nil))

(defun h2-recipes-recipes-oracle-update-fact (recipes)
  (let* ((state (proof-sym "STATE" "ACL2"))
         (value *library-x*)
         (update (proof-sym "UPDATE-ACL2-ORACLE" "ACL2"))
         (premise (proof-ite (list *h2-recipes-state* state) (list *h2-recipes-listp* value)
                             *proof-false*))
         (goal (list *library-implies* premise (list *h2-recipes-state* (list update value state))))
         (label "SELF-H2-UPDATE-ACL2-ORACLE-STATE-P1"))
    (h2-recipes-with-results
     ((nonstring (h2-recipes-recipes-auxiliary
                  recipes "TRUE-LISTP-IMPLIES-NOT-STRINGP"
                  (list *library-implies* (list *h2-recipes-listp* *library-x*)
                        (proof-neg (list *h2-recipes-stringp* *library-x*)))
                  "TRUE-LISTP" nil nil 1 "" nil nil 80)))
     (let* ((recipes (cdr nonstring))
            (library (h2-recipes-library recipes))
            (proof (library-library-proof library)))
       (if (h2-recipes-has-fact-p recipes label)
           (cons label recipes)
         (h2-recipes-with-results
          ((assumed (proof-proof-assume proof premise t))
           (premises (proof-proof-conjunct proof assumed))
           (old-term (proof-step-first (car premises)))
           (old-definition (proof-proof-unfold proof old-term))
           (old (proof-proof-rewrite proof (car premises) old-definition '(1)))
           (fields (proof-proof-conjunct proof old))
           (properties (proof-proof-conjunct proof (cadr fields)))
           (fact (library-library-axiom library (car nonstring) (list state)))
           (not-string (proof-proof-modus-ponens proof fact (car fields)))
           (opened (proof-proof-unfold proof (list *h2-recipes-length* state)))
           (body (h2-recipes-step-right opened))
           (selected (proof-proof-select proof body not-string))
           (as-len (proof-proof-chain proof opened (list selected)))
           (size (proof-proof-rewrite proof (car properties) as-len '(1 1)))
           (derived (h2-recipes-recipes-derive
                     recipes goal
                     (concatenate 'string "STATE-P1 UPDATE-ACL2-ORACLE LENGTH MAX NFIX "
                                  *h2-recipes-state-fields*)
                     (list "TRUE-LISTP-UPDATE-NTH" "NTH-UPDATE-NTH" "LEN-UPDATE-NTH" (car nonstring))
                     nil 1 "" (list size) nil 80))
           (recipes (h2-recipes-lemma (cdr derived) "H2-UPDATE-ACL2-ORACLE-STATE-P1"
                                      goal (car derived) nil)))
          (cons label recipes)))))))

(defun h2-recipes-recipes-nth-index-fact (recipes)
  (h2-recipes-with-results
   ((recipes (h2-recipes-index-lemmas recipes)))
   (let* ((nfix (proof-sym "NFIX" "ACL2"))
          (same "SELF-H2-NTH-OF-NFIX")
          (x *library-x*)
          (y *library-y*)
          (goal (proof-eq (list *h2-recipes-nth* (list nfix x) y)
                          (list *h2-recipes-nth* x y))))
     (h2-recipes-with-results
      ((recipes (if (h2-recipes-has-fact-p recipes same)
                    recipes
                  (h2-recipes-with-results
                   ((auxiliary (h2-recipes-recipes-auxiliary
                                recipes "NTH-OF-NFIX" goal "NTH ZP" *h2-arithmetic-index-rules*
                                nil 1 "" nil (list (list *h2-recipes-zp* x) (list *proof-consp* y)) 80)))
                   (cdr auxiliary)))))
      (let* ((proof (h2-recipes-proof recipes))
             (l (proof-sym "L" "ACL2"))
             (condition (proof-eq (list nfix x) (list nfix y)))
             (name "SELF-H2-NTH-INDEX-EQUAL")
             (same (proof-sym same "ACL2")))
        (h2-recipes-with-results
         ((equal (proof-proof-assume proof condition t))
          (left (proof-proof-fact proof same (list (list x x) (list y l))))
          (right (proof-proof-fact proof same (list (list x y) (list y l))))
          (symmetric (proof-proof-symmetric proof equal))
          (adjusted (proof-proof-rewrite proof right symmetric '(1 1 1)))
          (symmetric-left (proof-proof-symmetric proof left))
          (step (proof-proof-chain proof symmetric-left (list adjusted)))
          (claim (proof-step-first step))
          (recipes (if (h2-recipes-has-fact-p recipes name)
                       recipes
                     (h2-recipes-lemma recipes "H2-NTH-INDEX-EQUAL" claim step (list (proof-neg condition))))))
         (cons name recipes)))))))

(defun h2-recipes-state-oracle-list (n cursor oracle proof)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h2-recipes-state-oracle-list")
    (proof-with-checked-results
     ((term (h2-recipes-step-left cursor))
      (parts (proof-proof-conjunct proof cursor)))
     (if (equal term (list *h2-recipes-listp* oracle))
         (car parts)
       (h2-recipes-state-oracle-list (1- n) (cadr parts) oracle proof)))))

(defun h2-recipes-state-read-premises (search formula)
  (h2-book-logic-with-saved-result search
    (let ((proof (h2-book-logic-proof search)))
      (h2-book-logic-with-results search
          ((assumption (proof-term-at formula 1))
           (old (proof-proof-assume proof assumption t))
           (state (h2-recipes-step-left old))
           (opened (proof-proof-unfold proof assumption))
           (cursor (proof-proof-rewrite proof old opened '(1)))
           (oracle (list (proof-sym "ACL2-ORACLE" "ACL2") state))
           (oracle-list (h2-recipes-state-oracle-list 1000000 cursor oracle proof))
           (updated (list (proof-sym "UPDATE-ACL2-ORACLE" "ACL2") (list *library-cdr* oracle) state)))
        (cons (list updated old oracle-list) search)))))

(defun h2-recipes-recipes-read-state (recipes formula)
  (h2-recipes-with-results
     ((premises (h2-recipes-import-search-result
                 recipes (h2-recipes-state-read-premises (h2-recipes-recipes-search recipes) formula)))
      (recipes (cdr premises))
      (updated (caar premises))
      (seeds (cdar premises))
      (update (if (h2-recipes-has-fact-p recipes "UPDATE-ACL2-ORACLE-PRESERVES-STATE-P1")
                  (cons "UPDATE-ACL2-ORACLE-PRESERVES-STATE-P1" recipes)
                (h2-recipes-recipes-oracle-update-fact recipes)))
      (true-list (h2-recipes-recipes-true-list-facts (cdr update)))
      (state-result (h2-recipes-recipes-derive
                     (cdr true-list) (list *h2-recipes-state* updated) ""
                     (list (car update) (cadar true-list)) nil 1 "" seeds nil 80))
      (goal (proof-term-at formula 2))
      (result-state (proof-term-at goal 1))
      (equality (h2-recipes-recipes-derive (cdr state-result) (proof-eq result-state updated)
                                          "READ-ACL2-ORACLE READ-RUN-TIME MV-NTH NTH ZP"
                                          nil nil 1 "NTH MV-NTH" nil nil 80))
      (state (library-library-transport-argument
              (h2-recipes-library (cdr equality)) (car state-result) (car equality) 1))
      (step (h2-search-search-introduce (h2-recipes-recipes-search (cdr equality)) formula state)))
    (cons step (cdr equality))))

(defun h2-recipes-length-update-setup
  (zero cons-branch search formula updated zero-test cons-test len-cons hypothesis descent)
  (h2-book-logic-with-saved-result search
    (let* ((library (h2-search-search-library search))
           (proof (library-library-proof library)))
      (h2-book-logic-with-results search
          ((zp (proof-proof-assume proof zero-test zero))
           (shape (proof-proof-assume proof cons-test cons-branch))
           (update (proof-proof-unfold proof updated))
           (update-body (h2-recipes-step-right update))
           (selected (proof-proof-select proof update-body zp))
           (update (proof-proof-chain proof update (list selected)))
           (update-value (h2-recipes-step-right update))
           (cell (proof-list-of-length update-value 3))
           (len-update (proof-proof-reflexive proof (list *library-len* updated)))
           (reduced (proof-proof-rewrite proof len-update update '(1 2 1)))
           (len-fact (proof-proof-fact proof (proof-sym len-cons "ACL2")
                                       (list (list *library-x* (cadr cell)) (list *library-y* (caddr cell)))))
           (reduced (proof-proof-chain proof reduced (list len-fact)))
           (reduced (if zero
                        reduced
                      (h2-recipes-with-results ((smaller (proof-proof-prove-if proof hypothesis descent)))
                        (proof-proof-rewrite proof reduced smaller '(1 2 2)))))
           (length (proof-proof-unfold proof (list *library-len* *library-x*)))
           (length-body (h2-recipes-step-right length))
           (selected (proof-proof-select proof length-body shape))
           (length (proof-proof-chain proof length (list selected)))
           (right-term (proof-term-at formula 2))
           (right-reflexive (proof-proof-reflexive proof right-term))
           (right (proof-proof-rewrite proof right-reflexive length '(1 2 2)))
           (seeds (if cons-branch
                      (list zp shape)
                    (h2-recipes-with-results
                     ((atom-tail (library-library-axiom library "COMPLETION-OF-CDR" (list *library-x*)))
                      (atom-tail-body (h2-recipes-step-right atom-tail))
                      (selected (proof-proof-select proof atom-tail-body shape))
                      (atom-tail (proof-proof-chain proof atom-tail (list selected)))
                      (nil-length
                       (proof-proof-prove proof (proof-eq (list *library-len* *proof-false*) *proof-zero*)
                                          nil (list *library-len*)))
                      (symmetric (proof-proof-symmetric proof atom-tail))
                      (tail-length (proof-proof-rewrite proof nil-length symmetric '(1 1 1))))
                     (list zp shape tail-length))))
           (left-value (h2-recipes-step-right reduced))
           (right-value (h2-recipes-step-right right)))
        (cons (list (proof-eq left-value right-value) seeds reduced right) search)))))

(defun h2-recipes-recipes-length-update-branch
  (zero cons-branch recipes formula updated zero-test cons-test len-cons hypothesis descent)
  (h2-recipes-with-results
      ((prepared (h2-recipes-import-search-result
                  recipes (h2-recipes-length-update-setup
                           zero cons-branch (h2-recipes-recipes-search recipes) formula updated
                           zero-test cons-test len-cons hypothesis descent)))
       (setup (car prepared))
       (solved (h2-recipes-call-search (cdr prepared) :solve (list (car setup) (cadr setup) nil)))
       (proof (h2-recipes-proof (cdr solved)))
       (symmetric (proof-proof-symmetric proof (cadddr setup)))
       (step (proof-proof-chain proof (caddr setup) (list (car solved) symmetric))))
    (cons step (cdr solved))))

(defun h2-recipes-recipes-length-update (recipes formula)
  (h2-recipes-with-results
   ((recipes (h2-recipes-maximum-lemmas recipes))
    (left (proof-term-at formula 1))
    (updated (proof-term-at left 1)))
   (let* ((n (proof-sym "N" "ACL2"))
          (x *library-x*)
          (y *library-y*)
          (tail (list *library-cdr* x))
          (predecessor (library-plus *proof-neg-one* n))
          (measure (list *library-count* n))
          (substitutions (list (list (list n predecessor) (list x tail))))
          (proof (h2-recipes-proof recipes)))
     (h2-recipes-with-results
      ((descent (library-library-builtin (h2-recipes-library recipes) 9 n))
       (smaller (proof-subst formula (list (cons n predecessor) (cons x tail))))
       (descent-term (proof-step-first descent))
       (hypothesis (proof-proof-assume proof (proof-ite descent-term smaller *proof-true*) t))
       (auxiliary (h2-recipes-recipes-auxiliary
                   recipes "LEN-OF-CONS" (proof-eq (list *library-len* (list *proof-cons* x y))
                                                 (library-plus *proof-one* (list *library-len* y)))
                   "LEN" nil nil 1 "" nil nil 80))
       (recipes (h2-recipes-recipes-set-rules
                 (cdr auxiliary) "MAX"
                 (append *h2-arithmetic-integer-rules* *h2-arithmetic-index-rules*
                         '("SELF-H2-SUB1-ADD1" "SELF-H2-MAX-SUCCESSOR"
                           "SELF-H2-LESS-SUCCESSOR-ONE" "SELF-NATURAL-NONNEGATIVE"))
                 "" 80)))
      (let ((zero-test (list *h2-recipes-zp* n))
            (cons-test (list *proof-consp* x))
            (len-cons (car auxiliary))
            (proof (h2-recipes-proof recipes)))
        (h2-recipes-with-results
         ((zero-cons (h2-recipes-recipes-length-update-branch
                      t t recipes formula updated zero-test cons-test len-cons hypothesis descent))
          (zero-atom (h2-recipes-recipes-length-update-branch
                      t nil (cdr zero-cons) formula updated zero-test cons-test len-cons hypothesis descent))
          (zero (proof-proof-cases proof cons-test (car zero-cons) (car zero-atom)))
          (positive-cons (h2-recipes-recipes-length-update-branch
                          nil t (cdr zero-atom) formula updated zero-test cons-test len-cons hypothesis descent))
          (positive-atom (h2-recipes-recipes-length-update-branch
                          nil nil (cdr positive-cons) formula updated zero-test cons-test len-cons hypothesis descent))
          (positive (proof-proof-cases proof cons-test (car positive-cons) (car positive-atom)))
          (ordinal (library-library-builtin (h2-recipes-library (cdr positive-atom)) 1 n))
          (case-step (proof-proof-cases proof zero-test zero positive))
          (step (proof-proof-induct proof ordinal case-step formula measure substitutions)))
         (cons step (cdr positive-atom))))))))

(defun h2-recipes-recipes-nth-update-predecessor (index)
  (library-plus *proof-neg-one* index))

(defun h2-recipes-recipes-nth-update-branch
  (zero-m zero-n recipes formula test-m test-n shape m n induction-step atom-nth)
  (let ((proof (h2-recipes-proof recipes)))
    (h2-recipes-with-results
     ((assume-m (proof-proof-assume proof test-m zero-m))
      (assume-n (proof-proof-assume proof test-n zero-n)))
     (let ((premises (list assume-m assume-n)))
       (if (or zero-m zero-n)
           (h2-recipes-call-search recipes :solve (list formula premises (list shape)))
         (h2-recipes-with-results
          ((left-term (proof-term-at formula 1))
           (induction-left (h2-recipes-step-left induction-step))
           (left (h2-recipes-call-search recipes :solve (list (proof-eq left-term induction-left) premises nil)))
           (recursive (h2-recipes-step-right induction-step))
           (original (proof-term-at formula 2))
           (comparison (proof-eq m n))
           (recursive-test (proof-term-at recursive 1))
           (rec-guard (h2-recipes-recipes-derive (cdr left) (proof-eq recursive-test comparison) ""
                                                *h2-arithmetic-index-rules* nil 1 "" premises nil 80))
           (original-test (proof-term-at original 1))
           (old-guard (h2-recipes-recipes-derive (cdr rec-guard) (proof-eq original-test comparison) ""
                                                *h2-arithmetic-index-rules* nil 1 "" premises nil 80))
           (original-tail (proof-term-at original 3))
           (recursive-tail (proof-term-at recursive 3))
           (old-tail (h2-recipes-recipes-derive (cdr old-guard) (proof-eq original-tail recursive-tail)
                                               "NTH ZP" (append *h2-arithmetic-index-rules* (list atom-nth))
                                               nil 1 "" premises (list shape) 80))
           (rec-value (proof-proof-reflexive proof recursive))
           (rec-value (proof-proof-rewrite proof rec-value (car rec-guard) '(1 2 1)))
           (old-value (proof-proof-reflexive proof original))
           (old-value (proof-proof-rewrite proof old-value (car old-guard) '(1 2 1)))
           (old-value (proof-proof-rewrite proof old-value (car old-tail) '(1 2 3)))
           (symmetric (proof-proof-symmetric proof old-value))
           (right (proof-proof-chain proof rec-value (list symmetric)))
           (recipes (h2-recipes-recipes-set-rules
                     (cdr old-tail) "NTH UPDATE-NTH ZP"
                     (append *h2-arithmetic-index-rules* *h2-arithmetic-integer-rules* (list atom-nth)) "" 80))
           (step (proof-proof-chain proof (car left) (list induction-step right))))
          (cons step recipes)))))))

(defun h2-recipes-recipes-nth-update (recipes formula)
  (h2-recipes-with-results ((recipes (h2-recipes-index-lemmas recipes)))
    (let* ((m (proof-sym "M" "ACL2"))
           (n (proof-sym "N" "ACL2"))
           (l (proof-sym "L" "ACL2"))
           (tail (list *library-cdr* l))
           (predecessor-n (h2-recipes-recipes-nth-update-predecessor n))
           (predecessor-m (h2-recipes-recipes-nth-update-predecessor m))
           (substitutions (list (list (list n predecessor-n) (list m predecessor-m) (list l tail)))))
      (h2-recipes-with-results
       ((auxiliary (h2-recipes-recipes-auxiliary
                    recipes "NTH-OF-NONCONS"
                    (list *library-implies* (proof-neg (list *proof-consp* *library-y*))
                          (proof-eq (list *h2-recipes-nth* *library-x* *library-y*) *proof-false*))
                    "NTH" nil nil 1 "" nil nil 80))
        (recipes (h2-recipes-recipes-set-rules
                  (cdr auxiliary) "NTH UPDATE-NTH ZP"
                  (append *h2-arithmetic-index-rules* *h2-arithmetic-integer-rules* (list (car auxiliary))) "" 80)))
       (let ((atom-nth (car auxiliary))
             (test-m (list *h2-recipes-zp* m))
             (test-n (list *h2-recipes-zp* n))
             (shape (list *proof-consp* l))
             (proof (h2-recipes-proof recipes)))
         (h2-recipes-with-results
          ((descent (library-library-builtin (h2-recipes-library recipes) 9 n))
           (smaller (proof-subst formula (list (cons n predecessor-n) (cons m predecessor-m) (cons l tail))))
           (descent-term (proof-step-first descent))
           (hypothesis (proof-proof-assume proof (proof-ite descent-term smaller *proof-true*) t))
           (induction-step (proof-proof-prove-if proof hypothesis descent))
           (both-zero (h2-recipes-recipes-nth-update-branch
                       t t recipes formula test-m test-n shape m n induction-step atom-nth))
           (only-m-zero (h2-recipes-recipes-nth-update-branch
                         t nil (cdr both-zero) formula test-m test-n shape m n induction-step atom-nth))
           (m-zero (proof-proof-cases proof test-n (car both-zero) (car only-m-zero)))
           (only-n-zero (h2-recipes-recipes-nth-update-branch
                         nil t (cdr only-m-zero) formula test-m test-n shape m n induction-step atom-nth))
           (neither-zero (h2-recipes-recipes-nth-update-branch
                          nil nil (cdr only-n-zero) formula test-m test-n shape m n induction-step atom-nth))
           (m-positive (proof-proof-cases proof test-n (car only-n-zero) (car neither-zero)))
           (case-step (proof-proof-cases proof test-m m-zero m-positive))
           (ordinal (library-library-builtin (h2-recipes-library (cdr neither-zero)) 1 n))
           (step (proof-proof-induct proof ordinal case-step formula (list *library-count* n) substitutions)))
          (cons step (cdr neither-zero))))))))

(defun h2-recipes-recipes-symbol-equality-intern-identity (value anchor seeds recipes package)
  (let* ((premise (proof-ite (list *h2-recipes-symbolp* value)
                             (proof-eq (list package value) (list package anchor)) *proof-false*))
         (library (h2-recipes-library recipes))
         (proof (library-library-proof library)))
    (h2-recipes-with-results
     ((theorem (library-library-axiom library "INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME" (list value anchor)))
      (evidence (h2-recipes-call-search recipes :solve (list premise seeds nil)))
      (step (proof-proof-modus-ponens proof theorem (car evidence))))
     (cons step (cdr evidence)))))

(defun h2-recipes-recipes-symbol-equality-prove-from
  (value anchor value-symbol recipes condition names packages first second name package)
  (let* ((seeds (list condition names packages value-symbol))
         (anchor-test (list *h2-recipes-symbolp* anchor))
         (library (h2-recipes-library recipes))
         (proof (library-library-proof library)))
    (h2-recipes-with-results
     ((anchor-symbol (proof-proof-assume proof anchor-test t))
      (one (h2-recipes-recipes-symbol-equality-intern-identity value anchor seeds recipes package))
      (two (h2-recipes-recipes-symbol-equality-intern-identity
            anchor anchor (append seeds (list anchor-symbol)) (cdr one) package))
      (names-equality (if (equal value second) names (proof-proof-symmetric proof names)))
      (aligned (proof-proof-rewrite proof (car two) names-equality '(1 1 1)))
      (symmetric-one (proof-proof-symmetric proof (car one)))
      (same (proof-proof-chain proof symmetric-one (list aligned)))
      (same (if (equal value first) same (proof-proof-symmetric proof same)))
      (no-symbol (proof-proof-assume proof anchor-test nil))
      (completion (library-library-axiom library "COMPLETION-OF-INTERN-IN-PACKAGE-OF-SYMBOL"
                                        (list (list name value) anchor)))
      (completion-body (h2-recipes-step-right completion))
      (guard (proof-term-at completion-body 1))
      (stringp-name (proof-proof-fact proof "stringp-symbol-name" (list (list *library-x* value))))
      (selected (proof-proof-select proof guard stringp-name))
      (nil-value (h2-search-search-nil-value (h2-recipes-recipes-search (cdr two)) no-symbol))
      (guard-false (proof-proof-chain proof selected (list nil-value)))
      (not-nil (h2-search-not-nil-in-proof (h2-recipes-recipes-search recipes) proof))
      (denied (library-library-transport-argument library not-nil guard-false 1))
      (selected (proof-proof-select proof completion-body denied))
      (empty (proof-proof-chain proof completion (list selected)))
      (symmetric-one (proof-proof-symmetric proof (car one)))
      (value-is-nil (proof-proof-chain proof symmetric-one (list empty)))
      (pkg-equality (if (equal value first) packages (proof-proof-symmetric proof packages)))
      (pkg-equality (proof-proof-rewrite proof pkg-equality value-is-nil '(1 1 1)))
      (nil-package (proof-proof-compute proof (list package *proof-false*) '("str" "COMMON-LISP")))
      (pkg-equality (proof-proof-rewrite proof pkg-equality nil-package '(1 1)))
      (anchor-fact (library-library-axiom library "DEFAULT-SYMBOL-PACKAGE-NAME" (list anchor)))
      (anchor-package (proof-proof-modus-ponens proof anchor-fact no-symbol))
      (pkg-equality (proof-proof-chain proof pkg-equality (list anchor-package)))
      (pkg-term (proof-step-first pkg-equality))
      (unequal (proof-proof-compute proof pkg-term *proof-nil*))
      (denied (library-library-transport-argument library not-nil unequal 1))
      (contradiction (proof-proof-cut proof pkg-equality denied))
      (no (proof-proof-subsume proof contradiction
                                (cons (proof-eq first second) (proof-step-clause contradiction))))
      (step (proof-proof-cases proof anchor-test same no)))
     (cons step (cdr two)))))

(defun h2-recipes-recipes-symbol-equality (recipes formula)
  (let* ((first (proof-sym "S1" "ACL2"))
         (second (proof-sym "S2" "ACL2"))
         (name (proof-cl "SYMBOL-NAME"))
         (package (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
         (first-symbol (list *h2-recipes-symbolp* first)))
    (h2-recipes-with-results
     ((recipes (h2-recipes-recipes-set-rules recipes "" '("DEFAULT-SYMBOL-PACKAGE-NAME") "" 80)))
     (let ((proof (h2-recipes-proof recipes)))
       (h2-recipes-with-results
        ((test (proof-term-at formula 1))
         (condition (proof-proof-assume proof test t))
         (both (proof-proof-conjunct proof condition))
         (equalities (proof-proof-conjunct proof (cadr both)))
         (yes-symbol (proof-proof-assume proof first-symbol t))
         (no-symbol (proof-proof-assume proof first-symbol nil))
         (second-symbol (proof-proof-prove-if proof (car both) no-symbol))
         (yes (h2-recipes-recipes-symbol-equality-prove-from
               first second yes-symbol recipes condition (car equalities) (cadr equalities) first second name package))
         (no (h2-recipes-recipes-symbol-equality-prove-from
              second first second-symbol (cdr yes) condition (car equalities) (cadr equalities) first second name package))
         (cases (proof-proof-cases proof first-symbol (car yes) (car no)))
         (step (h2-search-search-introduce (h2-recipes-recipes-search (cdr no)) formula cases)))
        (cons step (cdr no)))))))

(defun h2-recipes-last (items)
  (if (consp items)
      (car (last items))
    (proof-index-failure)))

(defun h2-recipes-prove-alist-execution (recipes formula)
  (if (not (proof-is-call formula *proof-equal*))
      (cons nil recipes)
    (h2-recipes-with-results ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((left (car sides)) (right (cadr sides)))
        (if (and (proof-compound left) (proof-compound right) (equal (cdr left) (cdr right)))
            (h2-recipes-with-results
             ((left-head (proof-term-at left 0))
              (right-head (proof-term-at right 0)))
             (if (equal (table-get *h2-recipes-alist-execution* left-head :none) right-head)
                 (h2-recipes-with-results ((variable (h2-recipes-last left)))
                   (if (proof-compound variable)
                       (cons nil recipes)
                     (h2-recipes-with-results
                      ((search (h2-search-search-configure (h2-recipes-recipes-search recipes)
                                                           (list left-head right-head) '("built-in-clause-3") nil 80)))
                      (h2-recipes-call-search (h2-recipes-recipes-with-search recipes search) :list-induction
                                              (list formula variable nil 1)))))
               (cons nil recipes)))
          (cons nil recipes))))))

(defun h2-recipes-prove-character-shape (shapes recipes formula)
  (if (endp shapes)
      (cons nil recipes)
    (let* ((shape (car shapes))
           (pattern (car shape))
           (name (cadr shape)))
      (h2-recipes-with-results ((match (h2-search-match pattern formula nil)))
        (if (car match)
            (h2-recipes-with-results
             ((proved (h2-recipes-import-search-result
                       recipes (h2-finite-character-proof (h2-recipes-recipes-search recipes) name pattern)))
              (step (proof-proof-instantiate (h2-recipes-proof (cdr proved)) (car proved)
                                              (table-items (cdr match)))))
             (cons step (cdr proved)))
          (h2-recipes-prove-character-shape (cdr shapes) recipes formula))))))

(defun h2-recipes-array-condition (condition)
  (declare (xargs :measure (acl2-count condition)))
  (if (and (consp condition) (proof-is-call condition *proof-if*))
      (proof-with-checked-results ((otherwise (proof-term-at condition 3)))
        (if (equal otherwise *proof-false*)
            (h2-recipes-array-condition (caddr condition))
          condition))
    condition))

(defun h2-recipes-array-extension-p (guard goal)
  (and (proof-compound goal)
       (proof-with-checked-results ((head (proof-term-at goal 0)))
         (and (member-equal head *h2-recipes-arrays*)
              (let ((extension (h2-recipes-last goal)))
                (and (proof-is-call extension *proof-cons*)
                     (proof-with-checked-results ((pair (proof-term-at extension 1)))
                       (and (proof-is-call pair *proof-cons*)
                            (proof-with-checked-results
                             ((condition (h2-recipes-array-condition guard))
                              (tail (proof-term-at extension 2)))
                             (equal condition (append (seq-slice goal 0 -1) (list tail))))))))))))

(defun h2-recipes-symbol-completion (recipes formula argument goal)
  (let ((name (proof-cl "SYMBOL-NAME"))
        (package (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
        (empty (proof-quote '("str" ""))))
    (cond ((equal goal (proof-eq (list name argument) empty))
           (h2-recipes-recipes-derive recipes formula "" '("COMPLETION-OF-SYMBOL-NAME") nil 1 "" nil nil 80))
          ((equal goal (proof-eq (list package argument) empty))
           (h2-recipes-recipes-derive recipes formula "" '("COMPLETION-OF-SYMBOL-PACKAGE-NAME") nil 1 "" nil nil 80))
          (t (cons nil recipes)))))

(defun h2-recipes-prove-symbol-completion (recipes formula guard goal)
  (if (proof-is-call guard *proof-not*)
      (h2-recipes-with-results ((test (proof-term-at guard 1)))
        (if (proof-is-call test *h2-recipes-symbolp*)
            (h2-recipes-with-results ((argument (proof-term-at test 1)))
              (h2-recipes-symbol-completion recipes formula argument goal))
          (cons nil recipes)))
    (cons nil recipes)))

(defun h2-recipes-prove-rational-shape (operations recipes guard argument)
  (if (endp operations)
      (cons nil recipes)
    (let ((operation (caar operations))
          (fact (cdar operations)))
      (if (proof-is-call argument operation)
          (h2-recipes-with-results ((parts (proof-list-of-length (cdr argument) 2)))
            (let ((left (car parts)) (right (cadr parts)))
              (if (equal guard (proof-ite (list *library-rationalp* left)
                                          (list *library-rationalp* right) *proof-false*))
                  (h2-recipes-with-results
                   ((step (proof-proof-fact (h2-recipes-proof recipes) fact
                                             (list (list *library-x* left) (list *library-y* right)))))
                   (cons step recipes))
                (h2-recipes-prove-rational-shape (cdr operations) recipes guard argument))))
        (h2-recipes-prove-rational-shape (cdr operations) recipes guard argument)))))

(defun h2-recipes-prove-implication-shape (recipes formula guard goal)
  (h2-recipes-with-results
   ((array-extension (h2-recipes-array-extension-p guard goal)))
   (if array-extension
       (h2-recipes-run-derivations recipes :array-extension (list formula))
     (h2-recipes-with-results
      ((state-read (and (proof-is-call guard *h2-recipes-state*)
                        (proof-is-call goal *h2-recipes-state*)
                        (proof-with-checked-results ((argument (proof-term-at goal 1)))
                          (h2-recipes-calls-state-read argument)))))
      (if state-read
          (h2-recipes-recipes-read-state recipes formula)
        (h2-recipes-with-results
         ((symbol-completion (h2-recipes-prove-symbol-completion recipes formula guard goal)))
         (if (car symbol-completion)
             symbol-completion
           (if (proof-is-call goal *library-rationalp*)
               (h2-recipes-with-results ((argument (proof-term-at goal 1)))
                 (h2-recipes-prove-rational-shape (list (cons *proof-plus* "rationalp-binary-+")
                                                        (cons *proof-times* "rationalp-binary-*"))
                                                  recipes guard argument))
             (cons nil recipes)))))))))

(defun h2-recipes-recipes-prove-shape (recipes formula)
  (h2-recipes-with-results ((alist-execution (h2-recipes-prove-alist-execution recipes formula)))
    (if (car alist-execution)
        alist-execution
      (h2-recipes-with-results
       ((character-proof (h2-recipes-prove-character-shape *h2-recipes-character-shapes* (cdr alist-execution) formula)))
       (cond ((car character-proof) character-proof)
             ((proof-is-call formula *library-implies*)
              (h2-recipes-with-results ((parts (proof-list-of-length (cdr formula) 2)))
                (h2-recipes-prove-implication-shape (cdr character-proof) formula (car parts) (cadr parts))))
             (t (cons nil (cdr character-proof))))))))

(defun h2-recipes-prove-equal-char-code (recipes formula)
  (let ((proof (h2-recipes-proof recipes))
        (search (h2-recipes-recipes-search recipes))
        (code-variable (proof-sym "C" "ACL2"))
        (identity (proof-sym "CODE-CHAR-CHAR-CODE-IS-IDENTITY" "ACL2")))
    (h2-recipes-with-results
     ((parts (proof-list-of-length (cdr formula) 2))
      (outer (car parts))
      (inner (cadr parts))
      (condition (proof-proof-assume proof outer t))
      (characters (proof-proof-conjunct proof condition))
      (inner-parts (proof-list-of-length (cdr inner) 2))
      (assumed (proof-proof-assume proof (car inner-parts) t))
      (x-fact (proof-proof-fact proof identity (list (list code-variable *library-x*))))
      (x-code (proof-proof-modus-ponens proof x-fact (car characters)))
      (y-fact (proof-proof-fact proof identity (list (list code-variable *library-y*))))
      (y-code (proof-proof-modus-ponens proof y-fact (cadr characters)))
      (symmetric-x (proof-proof-symmetric proof x-code))
      (symmetric-assumed (proof-proof-symmetric proof assumed))
      (rewritten-y (proof-proof-rewrite proof y-code symmetric-assumed '(1 1 1)))
      (chain (proof-proof-chain proof symmetric-x (list rewritten-y)))
      (inner-step (h2-search-search-introduce search inner chain))
      (step (h2-search-search-introduce search formula inner-step)))
     (cons step recipes))))

(defun h2-recipes-prove-open-channels (recipes formula)
  (h2-recipes-with-results
   ((order (h2-recipes-run-derivations recipes :ordered-alist nil))
    (true-list (h2-recipes-recipes-true-list-facts (cdr order))))
   (let* ((channels (proof-sym "OPEN-CHANNEL-LISTP" "ACL2"))
          (premise (proof-ite (list *h2-recipes-alistp* *library-x*) (list channels *library-x*) *proof-false*)))
     (h2-recipes-with-results
      ((lists (h2-recipes-recipes-auxiliary
               (cdr true-list) "OPEN-CHANNEL-LISTP-TRUE-LISTS"
               (list *library-implies* premise (list *h2-recipes-list-listp* *library-x*))
               "OPEN-CHANNEL-LISTP ALISTP TRUE-LIST-LISTP TRUE-LISTP"
               (list (caar true-list) "CAR-CDR-ELIM" "OPEN-CHANNEL1-FORWARD-TO-TRUE-LISTP-AND-CONSP")
               "X" 1 "" nil nil 80)))
      (h2-recipes-recipes-derive (cdr lists) formula "OPEN-CHANNELS-P" (list (car order) (car lists))
                                 nil 1 "" nil nil 80)))))

(defun h2-recipes-prove-initial-global-table (recipes formula)
  (let ((proof (h2-recipes-proof recipes)))
    (h2-recipes-with-results
     ((condition (proof-term-at formula 1))
      (assumed (proof-proof-assume proof condition t))
      (conjuncts (proof-proof-conjunct proof assumed))
      (recipes (h2-recipes-recipes-set-rules recipes "" nil "" 80))
      (association (proof-step-first (cadr conjuncts)))
      (normalized (h2-recipes-call-search recipes :normalize (list association (h2-search-context-init) nil nil)))
      (equality (caar normalized))
      (left (h2-recipes-step-right equality))
      (initial (h2-recipes-last left))
      (result (proof-term-at formula 2))
      (table (h2-recipes-last result))
      (earlier (proof-proof-fact proof (proof-sym "ALL-BOUNDP-PRESERVES-ASSOC-EQUAL" "ACL2")
                                  (list (list (proof-sym "TBL1" "ACL2") initial)
                                        (list (proof-sym "TBL2" "ACL2") table))))
      (test (h2-recipes-step-left earlier))
      (old (proof-proof-assume proof condition t))
      (guard (h2-recipes-recipes-derive (cdr normalized) test "GLOBAL-TABLE" '("STATE-P1-FORWARD")
                                        nil 1 "" (list old) nil 80))
      (conclusion (proof-proof-modus-ponens (h2-recipes-proof (cdr guard)) earlier (car guard)))
      (step (h2-search-search-introduce (h2-recipes-recipes-search (cdr guard)) formula conclusion)))
     (cons step (cdr guard)))))

(defun h2-recipes-prove-natural-position (recipes formula)
  (let ((lst (proof-sym "LST" "ACL2"))
        (acc (proof-sym "ACC" "ACL2")))
    (h2-recipes-with-results
     ((library (h2-arithmetic-integer-order (h2-recipes-library recipes)))
      (recipes (h2-recipes-with-library recipes library))
      (simple (h2-recipes-call-search recipes :remove-wrappers (list formula)))
      (recipes (h2-recipes-recipes-set-rules (cdr simple) "POSITION-EQUAL-AC FIX"
                                            '("SELF-INTEGER-SUM" "SELF-NONNEGATIVE-SUM" "SELF-H2-INTEGER-NONNIL")
                                            "" 80))
      (simplified (h2-recipes-step-right (car simple)))
      (step (h2-recipes-call-search recipes :list-induction
                                    (list simplified lst (list (list acc (library-plus *proof-one* acc))) 1)))
      (transported (proof-proof-transport (h2-recipes-proof (cdr step)) (car step) (car simple))))
     (cons transported (cdr step)))))

(defun h2-recipes-prove-standard-char-nth (recipes formula)
  (let* ((chars (proof-sym "CHARS" "ACL2"))
         (index (proof-sym "I" "ACL2"))
         (measure (list *library-count* chars))
         (updated (list (list chars (list *library-cdr* chars))
                        (list index (library-plus *proof-neg-one* index)))))
    (h2-recipes-with-results
     ((recipes (h2-recipes-index-lemmas recipes))
      (recipes (h2-recipes-recipes-set-rules
                recipes "STANDARD-CHAR-LISTP NTH LEN"
                (append *h2-arithmetic-integer-rules* *h2-arithmetic-index-rules* '("SELF-H2-PREDECESSOR-BOUND"))
                "" 80))
      (ordinal (library-library-builtin (h2-recipes-library recipes) 1 chars)))
     (h2-recipes-call-search recipes :induction
                             (list formula measure (list updated) ordinal
                                   (list (list *proof-consp* chars) (list *h2-recipes-zp* index)))))))

(defun h2-recipes-prove-pairlis (recipes formula)
  (let ((fixed (proof-sym "TRUE-LIST-FIX" "ACL2"))
        (y *library-y*))
    (h2-recipes-with-results
     ((car-rule (h2-recipes-recipes-auxiliary
                 recipes "CAR-TRUE-LIST-FIX" (proof-eq (list *library-car* (list fixed y)) (list *library-car* y))
                 "TRUE-LIST-FIX" nil nil 1 "" nil nil 80))
      (cdr-rule (h2-recipes-recipes-auxiliary
                 (cdr car-rule) "CDR-TRUE-LIST-FIX"
                 (proof-eq (list *library-cdr* (list fixed y)) (list fixed (list *library-cdr* y)))
                 "TRUE-LIST-FIX" nil nil 1 "" nil nil 80))
      (recipes (h2-recipes-recipes-set-rules (cdr cdr-rule) "PAIRLIS$" (list (car car-rule) (car cdr-rule)) "" 80)))
     (h2-recipes-call-search recipes :list-induction
                             (list formula *library-x* (list (list y (list *library-cdr* y))) 1)))))

(defun h2-recipes-prove-true-list-subseq (recipes formula)
  (let ((helper "SELF-H2-TRUE-LISTP-TAKE"))
    (h2-recipes-with-results
     ((recipes (if (h2-recipes-has-fact-p recipes helper)
                   recipes
                 (let* ((take (proof-sym "TAKE" "ACL2"))
                        (y *library-y*)
                        (goal (list *h2-recipes-listp* (list take *library-x* y))))
                   (h2-recipes-with-results
                    ((true-list (h2-recipes-recipes-true-list-facts recipes))
                     (proved (h2-recipes-recipes-index-induction
                              (cdr true-list) goal "X" "TAKE TRUE-LISTP" (car true-list)
                              (list (list y (list *library-cdr* y))) nil)))
                    (h2-recipes-lemma (cdr proved) "H2-TRUE-LISTP-TAKE" goal (car proved) nil))))))
     (h2-recipes-recipes-derive recipes formula "SUBSEQ SUBSEQ-LIST" (list helper) nil 1 "" nil nil 80))))

(defun h2-recipes-prove-named (recipes theorem formula)
  (let ((list-recipe (cdr (assoc-equal theorem *h2-recipes-list-proofs*)))
        (direct-recipe (cdr (assoc-equal theorem *h2-recipes-direct-proofs*)))
        (search (h2-recipes-recipes-search recipes)))
    (cond
     ((equal theorem "EQUAL-CHAR-CODE") (h2-recipes-prove-equal-char-code recipes formula))
     (list-recipe
      (h2-recipes-recipes-derive recipes formula (car list-recipe) (caddr list-recipe) (cadr list-recipe)
                                 (if (equal theorem "KEYWORD-VALUE-LISTP-ASSOC-KEYWORD") 2 1) "" nil nil 80))
     (direct-recipe
      (h2-recipes-recipes-derive recipes formula (car direct-recipe) (cadr direct-recipe) nil 1 "" nil nil 80))
     ((equal theorem "OPEN-CHANNELS-P-FORWARD") (h2-recipes-prove-open-channels recipes formula))
     ((member-equal theorem '("READ-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP"
                              "WRITABLE-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP"))
      (let ((recognizer (if (equal theorem "READ-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP")
                            "READ-FILE-LISTP1" "WRITABLE-FILE-LISTP1")))
        (h2-recipes-recipes-derive recipes formula (concatenate 'string recognizer " LENGTH LEN")
                                   nil nil 1 "" nil (list (list *proof-consp* *library-x*)) 80)))
     ((equal theorem "ALL-BOUNDP-INITIAL-GLOBAL-TABLE")
      (h2-recipes-prove-initial-global-table recipes formula))
     ((equal theorem "ALL-BOUNDP-INITIAL-GLOBAL-TABLE-ALT")
      (h2-recipes-recipes-derive recipes formula "BOUNDP-GLOBAL1 GLOBAL-TABLE"
                                 '("ALL-BOUNDP-INITIAL-GLOBAL-TABLE") nil 1 "" nil nil 80))
     ((equal theorem "TRUE-LISTP-EXPLODE-NONNEGATIVE-INTEGER")
      (h2-recipes-import-search-result recipes (h2-division-explode-true-list search formula)))
     ((equal theorem "SYMBOL-EQUALITY") (h2-recipes-recipes-symbol-equality recipes formula))
     ((member-equal theorem '("STRING<-L-ASYMMETRIC" "STRING<-L-TRANSITIVE" "STRING<-L-TRICHOTOMY"))
      (h2-recipes-import-search-result recipes (h2-ordering-character-list-order search theorem formula)))
     ((member-equal theorem '("SYMBOL<-ASYMMETRIC" "SYMBOL<-TRANSITIVE" "SYMBOL<-TRICHOTOMY"))
      (h2-recipes-import-search-result recipes (h2-ordering-symbol-order search theorem formula)))
     ((member-equal theorem '("ORDERED-SYMBOL-ALISTP-REMOVE1-ASSOC-EQ" "ORDERED-SYMBOL-ALISTP-ADD-PAIR"
                              "ORDERED-SYMBOL-ALISTP-GETPROPS"))
      (h2-recipes-run-derivations recipes :ordered-changes (list theorem formula)))
     ((equal theorem "SYMBOL<-IRREFLEXIVE")
      (h2-recipes-recipes-derive recipes formula "" '("SYMBOL<-ASYMMETRIC") nil 1 "" nil
                                 (list (list (proof-sym "SYMBOL<" "ACL2") *library-x* *library-x*)) 80))
     ((equal theorem "TRUE-LISTP-CADR-ASSOC-EQ-FOR-OPEN-CHANNELS-P")
      (h2-recipes-run-derivations recipes :channel-headers (list formula)))
     ((equal theorem "NATP-POSITION-AC") (h2-recipes-prove-natural-position recipes formula))
     ((equal theorem "STANDARD-CHAR-P-NTH") (h2-recipes-prove-standard-char-nth recipes formula))
     ((equal theorem "NTH-UPDATE-NTH") (h2-recipes-recipes-nth-update recipes formula))
     ((equal theorem "TRUE-LISTP-UPDATE-NTH")
      (h2-recipes-with-results ((true-list (h2-recipes-recipes-true-list-facts recipes)))
        (let ((l (proof-sym "L" "ACL2")))
          (h2-recipes-recipes-index-induction (cdr true-list) formula "KEY" "UPDATE-NTH TRUE-LISTP"
                                              (car true-list) (list (list l (list *library-cdr* l))) nil))))
     ((equal theorem "NTH-UPDATE-NTH-ARRAY")
      (h2-recipes-with-results ((index (h2-recipes-recipes-nth-index-fact recipes)))
        (h2-recipes-recipes-derive (cdr index) formula "UPDATE-NTH-ARRAY" (list "NTH-UPDATE-NTH" (car index))
                                   nil 1 "" nil nil 80)))
     ((equal theorem "LEN-UPDATE-NTH") (h2-recipes-recipes-length-update recipes formula))
     ((equal theorem "NTH-ADD1")
      (h2-recipes-with-results ((recipes (h2-recipes-index-lemmas recipes)))
        (h2-recipes-recipes-derive recipes formula "NTH ZP" (append *h2-arithmetic-index-rules* *h2-arithmetic-integer-rules*)
                                   nil 1 "" nil nil 80)))
     ((member-equal theorem '("ASSOC-ADD-PAIR" "ADD-PAIR-PRESERVES-ALL-BOUNDP"))
      (h2-recipes-run-derivations recipes :assoc-after-add (list theorem formula)))
     ((equal theorem "PAIRLIS$-TRUE-LIST-FIX") (h2-recipes-prove-pairlis recipes formula))
     ((equal theorem "TRUE-LISTP-SUBSEQ-TYPE-PRESCRIPTION") (h2-recipes-prove-true-list-subseq recipes formula))
     ((equal theorem "UPDATE-ACL2-ORACLE-PRESERVES-STATE-P1")
      (h2-recipes-with-results ((oracle (h2-recipes-recipes-oracle-update-fact recipes)))
        (h2-recipes-recipes-derive (cdr oracle) formula "" (list (car oracle)) nil 1 "" nil nil 80)))
     (t (cons nil recipes)))))

(defun h2-recipes-recipes-prove-theorem (recipes theorem formula)
  (h2-recipes-with-results ((shaped (h2-recipes-recipes-prove-shape recipes formula)))
    (if (car shaped)
        shaped
      (h2-recipes-prove-named (cdr shaped) theorem formula))))
