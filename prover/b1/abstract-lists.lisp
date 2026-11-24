(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-abstract-lists-last* (proof-cl "LAST"))
(defconst *b1-abstract-lists-reverse* (proof-cl "REVERSE"))
(defconst *b1-abstract-lists-revappend* (proof-cl "REVAPPEND"))
(defconst *b1-abstract-lists-null* (proof-cl "NULL"))
(defconst *b1-abstract-lists-nthcdr* (proof-cl "NTHCDR"))
(defconst *b1-abstract-lists-cons-hint* (proof-sym "CONS-WITH-HINT" "ACL2"))
(defconst *b1-abstract-lists-acl2-nfix* (proof-sym "NFIX" "ACL2"))

(defmacro b1-abstract-lists-normalize
    (lib term &optional evidence unfold rules inspect-branches)
  `(b1-logic-bookproof-normalize ,lib ,term ,evidence ,unfold ,rules
                                 nil nil ,inspect-branches))

(defmacro b1-abstract-lists-normalize-proof
    (lib goal &optional evidence unfold rules)
  `(b1-logic-bookproof-normalize-proof ,lib ,goal ,evidence ,unfold ,rules nil))

(defmacro b1-abstract-lists-case-proof (lib goal &optional evidence unfold rules)
  `(b1-logic-bookproof-case-proof ,lib ,goal ,evidence ,unfold ,rules 16))

(defun b1-abstract-lists-list-signature-arguments
    (args position cons-type body rule-name claims)
  (if (endp args)
      nil
    (proof-with-checked-results
     ((signature
       (if (proof-is-call (car args) *proof-cons*)
           (proof-with-checked-results ((tail (proof-term-at (car args) 2)))
             (let ((tail-type (update-nth position tail cons-type)))
               (and (equal body tail-type)
                    (proof-with-checked-results
                     ((atom (b1-logic-matching-claim
                             claims
                             (list *library-implies* (list *b1-logic-atom* tail)
                                   (proof-eq tail-type
                                             (list *b1-abstract-lists-null* tail))))))
                     (and atom (list position rule-name atom))))))
         nil)))
     (or signature
         (b1-abstract-lists-list-signature-arguments
          (cdr args) (1+ position) cons-type body rule-name claims)))))

(defun b1-abstract-lists-list-signature-rules (rules predicate claims)
  (if (endp rules)
      nil
    (let ((rule (car rules)))
      (proof-with-checked-results
       ((signature
         (if (b1-search-rule-path rule)
             nil
           (proof-with-checked-results
            ((parts (proof-list-of-length (b1-search-rule-term rule) 3)))
            (let ((cons-type (cadr parts))
                  (body (caddr parts)))
              (and (proof-is-call body *proof-if*)
                   (proof-with-checked-results ((last-branch (proof-term-at body 3)))
                     (and (equal last-branch *proof-false*)
                          (proof-is-call (caddr body) predicate)
                          (b1-abstract-lists-list-signature-arguments
                           (cdr cons-type) 1 cons-type (caddr body)
                           (b1-search-rule-name rule) claims)))))))))
       (or signature
           (b1-abstract-lists-list-signature-rules (cdr rules) predicate claims))))))

(defun b1-abstract-lists-list-signature (lib predicate index)
  (declare (ignore lib))
  (and index
       (let* ((claims (b1-search-fact-index-claims index))
              (rules (table-get claims (list *proof-equal* predicate) nil)))
         (b1-abstract-lists-list-signature-rules (reverse rules) predicate claims))))

(defun b1-abstract-lists-list-type-fallback (lib tag)
  (let ((name (proof-sym (concatenate 'string "LIST-TYPE" tag "-DEFUN") "ACL2"))
        (facts (proof-proof-facts (library-library-proof lib))))
    (proof-with-checked-results
     ((clause (if (assoc-equal name facts)
                  (table-get facts name nil)
                '(:failure "failure" "")))
      (literal (proof-term-at clause 0))
      (parts (proof-list-of-length literal 3))
      (test (proof-term-at (caddr parts) 1))
      (driver (proof-term-at test 1)))
     (let* ((canonical (cadr parts))
            (position (seq-index-from (cdr canonical) driver 1))
            (constraint (concatenate 'string "ELEM-TYPE" tag " constraint ")))
       (if (< position 0)
           '(:failure "failure" "")
         (list position
               (proof-sym (string-append constraint "1") "ACL2")
               (proof-sym (string-append constraint "2") "ACL2")))))))

(defun b1-abstract-lists-list-type-init (lib predicate index)
  (proof-with-checked-results
   ((name (proof-term-at predicate 0))
    (name-text (proof-term-at name 2)))
   (if (not (stringp name-text))
       '(:failure "failure" "")
     (let ((tag (seq-slice name-text -2 :none)))
       (proof-with-checked-results
        ((signature (b1-abstract-lists-list-signature lib name index))
         (signature (or signature (b1-abstract-lists-list-type-fallback lib tag))))
        (append (list :b1-list-type lib predicate tag) signature (list index)))))))

(defun b1-abstract-lists-list-type-lib (typed) (nth 1 typed))
(defun b1-abstract-lists-list-type-predicate (typed) (nth 2 typed))
(defun b1-abstract-lists-list-type-tag (typed) (nth 3 typed))
(defun b1-abstract-lists-list-type-position (typed) (nth 4 typed))
(defun b1-abstract-lists-list-type-cons-law (typed) (nth 5 typed))
(defun b1-abstract-lists-list-type-atom-law (typed) (nth 6 typed))
(defun b1-abstract-lists-list-type-index (typed) (nth 7 typed))

(defun b1-abstract-lists-list-type-with-lib (typed lib)
  (update-nth 1 lib typed))

(defun b1-abstract-lists-list-type-prior (typed operation goal)
  (let* ((lib (b1-abstract-lists-list-type-lib typed))
         (index (b1-abstract-lists-list-type-index typed))
         (claims (and index (b1-search-fact-index-claims index))))
    (proof-with-checked-results ((name (b1-logic-matching-claim claims goal)))
      (let ((name (or name (proof-sym
                            (concatenate 'string "LIST-TYPE-" operation
                                         (b1-abstract-lists-list-type-tag typed))
                            "ACL2"))))
        (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
            (b1-logic-bookproof-from-fact lib name goal)
          '(:failure "Unproved" ""))))))

(defun b1-abstract-lists-list-type-on (typed items)
  (let ((predicate (b1-abstract-lists-list-type-predicate typed))
        (position (b1-abstract-lists-list-type-position typed)))
    (append (take (min position (len predicate)) predicate)
            (cons items (nthcdr (1+ position) predicate)))))

(defun b1-abstract-lists-list-type-constructor (typed term)
  (let ((proof (library-library-proof (b1-abstract-lists-list-type-lib typed))))
    (proof-with-checked-results
     ((rule (proof-proof-fact proof (b1-abstract-lists-list-type-cons-law typed) nil))
      (literal (proof-step-first rule))
      (pattern (proof-term-at literal 1))
      (matched (b1-logic-match pattern term nil)))
     (if (car matched)
         (proof-proof-instantiate proof rule (table-items (cdr matched)))
       '(:failure "failure" "")))))

(defun b1-abstract-lists-list-type-at-atom (typed term atom)
  (let* ((lib (b1-abstract-lists-list-type-lib typed))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((rule (proof-proof-fact proof (b1-abstract-lists-list-type-atom-law typed) nil))
      (literal (proof-step-first rule))
      (conclusion (proof-term-at literal 2))
      (pattern (proof-term-at conclusion 1))
      (matched (b1-logic-match pattern term nil))
      (rule (if (car matched)
                (proof-proof-instantiate proof rule (table-items (cdr matched)))
              '(:failure "failure" "")))
      (literal (proof-step-first rule))
      (condition (proof-term-at literal 1))
      (test (b1-abstract-lists-normalize-proof
             lib condition (list atom) (list *b1-logic-atom* *proof-not*)))
      (result (proof-proof-modus-ponens proof rule test))
      (right (proof-rewritten-term result))
      (reduction (b1-abstract-lists-normalize
                  lib right nil (list *b1-abstract-lists-null* *b1-logic-eq*))))
     (proof-proof-chain proof result (list reduction)))))

(defun b1-abstract-lists-list-type-empty (typed)
  (let* ((lib (b1-abstract-lists-list-type-lib typed))
         (proof (library-library-proof lib))
         (call (b1-abstract-lists-list-type-on typed *proof-false*)))
    (proof-with-checked-results
     ((atom (b1-abstract-lists-normalize-proof
             lib (proof-neg (list *proof-consp* *proof-false*)) nil (list *proof-not*)))
      (equation (b1-abstract-lists-list-type-at-atom typed call atom)))
     (proof-proof-true-from-eq proof equation))))

(defun b1-abstract-lists-list-type-reconstructed (typed source cons)
  (let* ((lib (b1-abstract-lists-list-type-lib typed))
         (proof (library-library-proof lib))
         (position (b1-abstract-lists-list-type-position typed)))
    (proof-with-checked-results
     ((literal (proof-step-first source))
      (items (proof-term-at literal position))
      (test (proof-step-first cons))
      (rule (b1-logic-bookproof-from-fact
             lib (proof-sym "CAR-CDR-ELIM" "ACL2")
             (list *library-implies* test
                   (proof-eq (list *proof-cons* (list *library-car* items)
                                   (list *library-cdr* items))
                             items))))
      (taken (proof-proof-modus-ponens proof rule cons)))
     (library-library-transport-argument lib source taken position))))

(defun b1-abstract-lists-list-type-fields (typed source cons)
  (let ((proof (library-library-proof (b1-abstract-lists-list-type-lib typed))))
    (proof-with-checked-results
     ((pair (b1-abstract-lists-list-type-reconstructed typed source cons))
      (literal (proof-step-first pair))
      (constructor (b1-abstract-lists-list-type-constructor typed literal))
      (rewritten (proof-proof-rewrite proof pair constructor '(1))))
     (proof-proof-conjunct proof rewritten))))

(defun b1-abstract-lists-list-type-pair (typed cons element tail)
  (let* ((lib (b1-abstract-lists-list-type-lib typed))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((made (b1-abstract-lists-list-type-constructor
             typed (b1-abstract-lists-list-type-on typed cons)))
      (goal (proof-rewritten-term made))
      (claim (b1-abstract-lists-normalize-proof lib goal (list element tail))))
     (proof-proof-transport proof claim made))))

(defun b1-abstract-lists-list-type-proper (typed source)
  (let* ((lib (b1-abstract-lists-list-type-lib typed))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first source))
      (items (proof-term-at literal (b1-abstract-lists-list-type-position typed)))
      (law (b1-abstract-lists-list-type-prior
            typed "TRUE-LISTP"
            (list *library-implies* literal (list *b1-structures-true-listp* items)))))
     (proof-proof-modus-ponens proof law source))))

(defun b1-abstract-lists-positive-index (lib index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((step (proof-proof-assume proof (list *b1-logic-zp* index) nil))
      (integral (b1-logic-bookproof-forces lib (library-integer index) step nil
                                          (list *b1-logic-zp* *proof-not*) nil))
      (positive-bound (b1-integer-no-zp lib index step integral)))
     (list integral positive-bound))))

(defun b1-abstract-lists-index-descent (lib index next-index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((bounds (b1-abstract-lists-positive-index lib index))
      (child-type (library-library-type-of lib next-index (list (car bounds))))
      (positive-one (proof-proof-prove proof (library-positive *proof-one*) nil nil))
      (smaller (library-library-less-from-difference lib next-index index positive-one
                                                     (list (car bounds)))))
     (library-library-cite lib "NFIX-DECREASE" (list next-index index)
                           (list child-type (car bounds) (cadr bounds) smaller)))))

(defun b1-abstract-lists-decreased-formula (lib formula index next-index mapping)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((ordinal (b1-abstract-lists-index-descent lib index next-index))
      (test (proof-step-first ordinal))
      (child (proof-subst formula mapping))
      (conditional (proof-proof-assume proof (proof-ite test child *proof-true*) t)))
     (proof-proof-prove-if proof conditional ordinal))))

(defun b1-abstract-lists-shifted-positive-index (lib next-index integer-index positive-bound)
  (proof-with-checked-results
   ((next-type (library-library-type-of lib next-index (list integer-index)))
    (gives-one (b1-arithmetic-integer-discrete lib positive-bound integer-index))
    (literal (proof-step-first gives-one))
    (before (proof-term-at literal 1))
    (sums (b1-arithmetic-number-sums-init lib))
    (alignment (b1-arithmetic-number-sums-comparison-equation
                sums before (library-lt next-index *proof-zero*) (list integer-index))))
   (let* ((lib (b1-arithmetic-number-sums-library sums))
          (proof (library-library-proof lib)))
     (proof-with-checked-results ((lower (proof-proof-rewrite proof gives-one alignment '(1 1))))
       (cons (list next-type lower) lib)))))

(defun b1-abstract-lists-abstract-list-proper-base-consequence
    (premise atom lib source goal typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((constraint (b1-abstract-lists-list-type-at-atom typed source atom))
      (is-nil (proof-proof-rewrite proof premise constraint '(1)))
      (opening (b1-abstract-lists-normalize lib goal (list atom)
                                          (list *b1-structures-true-listp* *b1-logic-eq*))))
     (proof-proof-transport proof is-nil opening))))

(defun b1-abstract-lists-abstract-list-proper-base (atom lib formula typed)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-proper-base-consequence
             premise atom lib (cadr formula) (caddr formula) typed)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-proper-step-consequence
    (premise cons hypothesis lib goal typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((fields (b1-abstract-lists-list-type-fields typed premise cons))
      (child (proof-proof-modus-ponens proof hypothesis (cadr fields)))
      (opening (b1-revappend-open-list lib goal (list cons))))
     (proof-proof-transport proof child opening))))

(defun b1-abstract-lists-abstract-list-proper-step (cons hypothesis lib formula typed)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-proper-step-consequence
             premise cons hypothesis lib (caddr formula) typed)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-proper (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (typed (b1-abstract-lists-list-type-init lib (cadr parts) index))
      (xs (proof-term-at (cadr parts) (b1-abstract-lists-list-type-position typed)))
      (preparation (b1-revappend-list-induction-prepare lib formula xs nil))
      (here (b1-abstract-lists-abstract-list-proper-step
             (caddr preparation) (cadddr preparation) lib formula typed))
      (atom (proof-proof-assume proof (cadr preparation) nil))
      (there (b1-abstract-lists-abstract-list-proper-base atom lib formula typed)))
     (b1-revappend-list-induction lib preparation there here))))

(defun b1-abstract-lists-abstract-list-cons (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((goal (proof-term-at formula 2))
      (typed (b1-abstract-lists-list-type-init lib goal index))
      (law (b1-abstract-lists-list-type-constructor typed goal))
      (premise (b1-logic-bookproof-prove-implication-premise lib formula))
      (result (proof-proof-transport proof premise law)))
     (b1-logic-bookproof-prove-implication-with-premise lib formula premise result))))

(defun b1-abstract-lists-abstract-list-cdr (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (typed (b1-abstract-lists-list-type-init lib (cadr parts) index))
      (items (proof-term-at (cadr parts) (b1-abstract-lists-list-type-position typed))))
     (let ((test (list *proof-consp* items))
           (position (b1-abstract-lists-list-type-position typed)))
       (proof-with-checked-results
        ((cons (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (empty (b1-abstract-lists-list-type-empty typed))
         (selector (b1-structures-noncons-selector lib *library-cdr* atom))
         (empty (library-library-transport-argument lib empty selector position))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (fields (b1-abstract-lists-list-type-fields typed premise cons))
         (result (proof-proof-cases proof test (cadr fields) empty)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise result))))))

(defun b1-abstract-lists-abstract-list-car-consequence
    (premise lib typed test cons atom claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((facts (proof-proof-conjunct proof premise))
      (source (proof-step-first (car facts)))
      (atom-law (b1-abstract-lists-list-type-at-atom typed source atom))
      (is-nil (proof-proof-rewrite proof (car facts) atom-law '(1)))
      (impossible (proof-proof-rewrite proof (cadr facts) is-nil '(1)))
      (not-nil (b1-logic-proof-not-nil proof))
      (absent (b1-logic-bookproof-contradiction lib impossible not-nil claim))
      (fields (b1-abstract-lists-list-type-fields typed (car facts) cons)))
     (proof-proof-cases proof test (car fields) absent))))

(defun b1-abstract-lists-abstract-list-car (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (source (proof-term-at (cadr parts) 1))
      (typed (b1-abstract-lists-list-type-init lib source index))
      (xs (proof-term-at (cadr parts) 2)))
     (let ((test (list *proof-consp* xs)))
       (proof-with-checked-results
        ((cons (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (result (b1-abstract-lists-abstract-list-car-consequence
                  premise lib typed test cons atom (caddr parts))))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise result))))))

(defun b1-abstract-lists-abstract-list-member-base-consequence (premise atom lib lookup claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((facts (proof-proof-conjunct proof premise))
      (opening (b1-revappend-open-list lib lookup (list atom)))
      (impossible (proof-proof-rewrite proof (car facts) opening '(1)))
      (not-nil (b1-logic-proof-not-nil proof)))
     (b1-logic-bookproof-contradiction lib impossible not-nil claim))))

(defun b1-abstract-lists-abstract-list-member-base (atom lib formula lookup claim)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-member-base-consequence premise atom lib lookup claim)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-member-step-consequence
    (premise cons hypothesis lib lookup hit-test typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((premises (proof-proof-conjunct proof premise))
      (fields (b1-abstract-lists-list-type-fields typed (cadr premises) cons))
      (hit (proof-proof-assume proof hit-test t))
      (head (proof-step-first (car fields)))
      (value (proof-rewritten-term hit))
      (slot (let ((slot (seq-index-from (cdr head) value 1)))
              (if (< slot 0) '(:failure "failure" "") slot)))
      (symmetric (proof-proof-symmetric proof hit))
      (yes (proof-proof-rewrite proof (car fields) symmetric (list 1 slot)))
      (not-hit (proof-proof-assume proof hit-test nil))
      (miss (b1-revappend-open-list lib lookup (list cons not-hit)))
      (smaller (proof-proof-rewrite proof (car premises) miss '(1)))
      (child (proof-step-first hypothesis))
      (next-guard (b1-abstract-lists-normalize-proof lib (cadr child)
                                                    (list smaller (cadr fields))))
      (no (proof-proof-modus-ponens proof hypothesis next-guard)))
     (proof-proof-cases proof hit-test yes no))))

(defun b1-abstract-lists-abstract-list-member-step
    (cons hypothesis lib formula lookup hit-test typed)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-member-step-consequence
             premise cons hypothesis lib lookup hit-test typed)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-member (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (guard-parts (proof-list-of-length (cadr parts) 4))
      (typed (b1-abstract-lists-list-type-init lib (caddr guard-parts) index))
      (lookup-parts (proof-list-of-length (cadr guard-parts) 3)))
     (let* ((lookup (cadr guard-parts))
            (xs (caddr lookup-parts))
            (hit-test (proof-eq (cadr lookup-parts) (list *library-car* xs))))
       (proof-with-checked-results
        ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
         (here (b1-abstract-lists-abstract-list-member-step
                (caddr preparation) (cadddr preparation) lib formula lookup hit-test typed))
         (atom (proof-proof-assume proof (cadr preparation) nil))
         (there (b1-abstract-lists-abstract-list-member-base atom lib formula lookup (caddr parts))))
        (b1-revappend-list-induction lib preparation there here))))))

(defun b1-abstract-lists-abstract-list-memberp-consequence (premise lib typed rule claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((facts (proof-proof-conjunct proof premise))
      (found (proof-step-first (car facts)))
      (member-step (b1-logic-bookproof-forces lib (cons *b1-revappend-member* (cdr found))
                                             (car facts) nil nil (list rule)))
      (recognised (proof-step-first (cadr facts)))
      (guard (proof-ite (cons *b1-revappend-member* (cdr found)) recognised *proof-false*))
      (known (b1-abstract-lists-list-type-prior
              typed "MEMBER-EQUAL" (list *library-implies* guard claim)))
      (condition (b1-abstract-lists-normalize-proof lib guard
                                                    (list member-step (cadr facts)))))
     (proof-proof-modus-ponens proof known condition))))

(defun b1-abstract-lists-abstract-list-memberp (lib formula index)
  (proof-with-checked-results
   ((parts (proof-list-of-length formula 3))
    (source (proof-term-at (cadr parts) 2))
    (typed (b1-abstract-lists-list-type-init lib source index))
    (rule-and-lib (b1-set-laws-memberp-as-boolean lib)))
   (let* ((lib (cdr rule-and-lib))
          (typed (b1-abstract-lists-list-type-with-lib typed lib)))
     (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-abstract-lists-abstract-list-memberp-consequence
                     premise lib typed (car rule-and-lib) (caddr parts)))
       (result (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
      (cons result lib)))))

(defun b1-abstract-lists-abstract-list-append-base-consequence
    (premise atom lib proper typed call source out right)
  (let ((proof (library-library-proof lib))
        (position (b1-abstract-lists-list-type-position typed)))
    (proof-with-checked-results
     ((reduction (b1-abstract-lists-normalize lib proper (list atom)
                                            (list *b1-structures-true-listp* *b1-logic-eq*)))
      (is-nil (proof-proof-rewrite proof premise reduction '(1)))
      (atom-law (b1-abstract-lists-list-type-at-atom typed source atom))
      (has-type (proof-proof-transport proof is-nil atom-law))
      (opening (b1-revappend-open-list lib call (list atom)))
      (left (b1-revappend-lift-argument lib out opening position))
      (selected (proof-proof-select proof right has-type))
      (selected (proof-proof-symmetric proof selected)))
     (proof-proof-chain proof left (list selected)))))

(defun b1-abstract-lists-abstract-list-append-base
    (atom lib formula typed call source out right)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-append-base-consequence
             premise atom lib (cadr formula) typed call source out right)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-append-step-consequence
    (premise cons hypothesis lib typed xs call out right)
  (let ((proof (library-library-proof lib))
        (position (b1-abstract-lists-list-type-position typed))
        (pair (list *proof-cons* (list *library-car* xs) (list *library-cdr* xs))))
    (proof-with-checked-results
     ((proper-tail (b1-structures-true-list-tail lib premise cons))
      (child (proof-proof-modus-ponens proof hypothesis proper-tail))
      (append-eq (b1-revappend-open-list lib call (list cons)))
      (lhs (b1-revappend-lift-argument lib out append-eq position))
      (lhs-term (proof-rewritten-term lhs))
      (constructor (b1-abstract-lists-list-type-constructor typed lhs-term))
      (lhs (proof-proof-chain proof lhs (list constructor)))
      (lhs (proof-proof-rewrite proof lhs child '(1 2 2)))
      (test (proof-step-first cons))
      (reconstructed (b1-logic-bookproof-from-fact
                      lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                      (list *library-implies* test (proof-eq pair xs))))
      (source-eq (b1-abstract-lists-list-type-constructor
                  typed (b1-abstract-lists-list-type-on typed pair)))
      (pair-eq (proof-proof-modus-ponens proof reconstructed cons))
      (source-eq (proof-proof-rewrite proof source-eq pair-eq (list 1 1 position)))
      (rhs (b1-revappend-lift-argument lib right source-eq 1))
      (left-result (proof-rewritten-term lhs))
      (right-result (proof-rewritten-term rhs))
      (grouping (b1-abstract-lists-case-proof lib (proof-eq left-result right-result)))
      (reversed (proof-proof-symmetric proof rhs)))
     (proof-proof-chain proof lhs (list grouping reversed)))))

(defun b1-abstract-lists-abstract-list-append-step
    (cons hypothesis lib formula typed xs call out right)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-append-step-consequence
             premise cons hypothesis lib typed xs call out right)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-append (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (claim (proof-list-of-length (caddr parts) 3))
      (typed (b1-abstract-lists-list-type-init lib (cadr claim) index))
      (call (proof-term-at (cadr claim) (b1-abstract-lists-list-type-position typed)))
      (call-parts (proof-list-of-length call 3)))
     (let* ((xs (cadr call-parts))
            (out (cadr claim))
            (right (caddr claim))
            (source (b1-abstract-lists-list-type-on typed xs)))
       (proof-with-checked-results
        ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
         (here (b1-abstract-lists-abstract-list-append-step
                (caddr preparation) (cadddr preparation) lib formula typed xs call out right))
         (atom (proof-proof-assume proof (cadr preparation) nil))
         (there (b1-abstract-lists-abstract-list-append-base
                 atom lib formula typed call source out right)))
        (b1-revappend-list-induction lib preparation there here))))))

(defun b1-abstract-lists-two-bindings (key value other-key other-value)
  (table-put (list (cons key value)) other-key other-value))

(defun b1-abstract-lists-abstract-list-nthcdr-consequence
    (premise lib typed tail hypothesis closed opened test)
  (let ((proof (library-library-proof lib))
        (position (b1-abstract-lists-list-type-position typed)))
    (proof-with-checked-results
     ((source (proof-step-first premise))
      (rule (b1-abstract-lists-list-type-prior
             typed "CDR" (list *library-implies* source
                              (b1-abstract-lists-list-type-on typed tail))))
      (tail-typed (proof-proof-modus-ponens proof rule premise))
      (child (proof-proof-modus-ponens proof hypothesis tail-typed))
      (before (library-library-transport-argument lib premise closed position))
      (after (library-library-transport-argument lib child opened position)))
     (proof-proof-cases proof test before after))))

(defun b1-abstract-lists-abstract-list-nthcdr (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (claim (caddr parts))
      (typed (b1-abstract-lists-list-type-init lib claim index))
      (call (proof-term-at claim (b1-abstract-lists-list-type-position typed)))
      (call-parts (proof-list-of-length call 3)))
     (let* ((number (cadr call-parts))
            (xs (caddr call-parts))
            (test (list *b1-logic-zp* number)))
       (proof-with-checked-results
        ((stop (proof-proof-assume proof test t))
         (resume (proof-proof-assume proof test nil))
         (closed (b1-revappend-open-list lib call (list stop)))
         (opened (b1-revappend-open-list lib call (list resume)))
         (recursive-call (proof-rewritten-term opened))
         (arguments (proof-list-of-length (cdr recursive-call) 2)))
        (let* ((next-index (car arguments))
               (tail (cadr arguments))
               (mapping (b1-abstract-lists-two-bindings number next-index xs tail)))
          (proof-with-checked-results
           ((hypothesis (b1-abstract-lists-decreased-formula lib formula number next-index mapping))
            (ordinal (library-library-cite lib "NFIX-ORDINAL" (list number) nil))
            (premise (b1-logic-bookproof-prove-implication-premise lib formula))
            (consequence (b1-abstract-lists-abstract-list-nthcdr-consequence
                          premise lib typed tail hypothesis closed opened test))
            (result (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
           (proof-proof-induct proof ordinal result formula (list *library-nfix* number)
                               (list (table-items mapping))))))))))

(defun b1-abstract-lists-abstract-make-list (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (claim (cadr parts))
      (typed (b1-abstract-lists-list-type-init lib claim index))
      (call (proof-term-at claim (b1-abstract-lists-list-type-position typed)))
      (call-parts (proof-list-of-length call 4)))
     (let* ((number (cadr call-parts))
            (accumulator (cadddr call-parts))
            (test (list *b1-logic-zp* number)))
       (proof-with-checked-results
        ((stop (proof-proof-assume proof test t))
         (resume (proof-proof-assume proof test nil))
         (closed (b1-revappend-open-list lib call (list stop)))
         (opened (b1-revappend-open-list lib call (list resume)))
         (base (b1-abstract-lists-case-proof lib formula (list stop) (list *b1-revappend-iff*)
                                            (list (b1-logic-equal-to closed))))
         (recursive-call (proof-rewritten-term opened))
         (recursive-parts (proof-list-of-length recursive-call 4)))
        (let* ((next-index (cadr recursive-parts))
               (extended (cadddr recursive-parts))
               (mapping (b1-abstract-lists-two-bindings number next-index accumulator extended)))
          (proof-with-checked-results
           ((hypothesis (b1-abstract-lists-decreased-formula lib formula number next-index mapping))
            (constructor (b1-abstract-lists-list-type-constructor
                          typed (b1-abstract-lists-list-type-on typed extended)))
            (child-goal (proof-rewritten-term hypothesis))
            (regrouped (b1-abstract-lists-case-proof lib (proof-eq child-goal (caddr parts))
                                                    (list resume) nil
                                                    (list (b1-logic-equal-to constructor))))
            (child (proof-proof-rewrite proof hypothesis regrouped '(1 2)))
            (symmetric (proof-proof-symmetric proof opened))
            (continued (proof-proof-rewrite proof child symmetric
                                            (list 1 1 (b1-abstract-lists-list-type-position typed))))
            (result (proof-proof-cases proof test base continued))
            (ordinal (library-library-cite lib "NFIX-ORDINAL" (list number) nil)))
           (proof-proof-induct proof ordinal result formula (list *library-nfix* number)
                               (list (table-items mapping))))))))))

(defun b1-abstract-lists-abstract-list-reverse-consequence (premise lib typed call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((proper (b1-abstract-lists-list-type-proper typed premise))
      (not-string (b1-structures-proper-list-is-not-string lib proper))
      (opened (b1-abstract-lists-normalize lib call (list not-string)
                                          (list *b1-abstract-lists-reverse*)))
      (empty (b1-abstract-lists-list-type-empty typed))
      (source (proof-step-first premise))
      (nil-type (proof-step-first empty))
      (guard (proof-ite source nil-type *proof-false*))
      (value (proof-rewritten-term opened))
      (theorem (b1-abstract-lists-list-type-prior
                typed "REVAPPEND" (list *library-implies* guard
                                       (b1-abstract-lists-list-type-on typed value))))
      (known (b1-abstract-lists-normalize-proof lib guard (list premise empty)))
      (computed (proof-proof-modus-ponens proof theorem known)))
     (library-library-transport-argument lib computed opened
                                         (b1-abstract-lists-list-type-position typed)))))

(defun b1-abstract-lists-abstract-list-reverse (lib formula index)
  (proof-with-checked-results
   ((parts (proof-list-of-length formula 3))
    (typed (b1-abstract-lists-list-type-init lib (caddr parts) index))
    (call (proof-term-at (caddr parts) (b1-abstract-lists-list-type-position typed)))
    (premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (result (b1-abstract-lists-abstract-list-reverse-consequence premise lib typed call)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise result)))

(defun b1-abstract-lists-abstract-list-initial-sublist-consequence
    (premise lib typed induction prefix xs checked relation prefix-cons prefix-atom source-cons source-atom claim)
  (let ((proof (library-library-proof lib))
        (position (b1-abstract-lists-list-type-position typed))
        (test-prefix (list *proof-consp* prefix))
        (test-source (list *proof-consp* xs)))
    (proof-with-checked-results
     ((facts (b1-logic-bookproof-split-conjuncts lib premise))
      (facts (proof-list-of-length facts 3))
      (reduction (b1-abstract-lists-normalize lib checked (list prefix-atom)
                                            (list *b1-structures-true-listp* *b1-logic-eq*)))
      (empty (proof-proof-rewrite proof (cadr facts) reduction '(1)))
      (nil-type (b1-abstract-lists-list-type-empty typed))
      (base (library-library-transport-argument lib nil-type empty position))
      (open-short (b1-revappend-open-list lib relation (list prefix-cons source-atom)))
      (invalid (proof-proof-rewrite proof (caddr facts) open-short '(1)))
      (not-nil (b1-logic-proof-not-nil proof))
      (short (b1-logic-bookproof-contradiction lib invalid not-nil claim))
      (fields (b1-abstract-lists-list-type-fields typed (car facts) source-cons))
      (open-long (b1-revappend-open-list lib relation (list prefix-cons source-cons)))
      (shape (proof-proof-rewrite proof (caddr facts) open-long '(1)))
      (equal-and-tail (proof-proof-conjunct proof shape))
      (symmetric (proof-proof-symmetric proof (car equal-and-tail)))
      (element (proof-proof-rewrite proof (car fields) symmetric (list 1 position)))
      (child (b1-induction-tree-induction-hypothesis
              induction (b1-abstract-lists-two-bindings prefix (list *library-cdr* prefix)
                                                        xs (list *library-cdr* xs))
              (list (list test-prefix t))))
      (tail-proper (b1-structures-true-list-tail lib (cadr facts) prefix-cons))
      (child-formula (proof-step-first (car child)))
      (child-guard (b1-abstract-lists-normalize-proof
                    lib (cadr child-formula) (list (cadr fields) tail-proper (cadr equal-and-tail))))
      (tail (proof-proof-modus-ponens proof (car child) child-guard))
      (pair (list *proof-cons* (list *library-car* prefix) (list *library-cdr* prefix)))
      (output (b1-abstract-lists-list-type-pair typed pair element tail))
      (rule (b1-logic-bookproof-from-fact
             lib (proof-sym "CAR-CDR-ELIM" "ACL2")
             (list *library-implies* test-prefix (proof-eq pair prefix))))
      (elimination (proof-proof-modus-ponens proof rule prefix-cons))
      (long (proof-proof-rewrite proof output elimination (list 1 position)))
      (both (proof-proof-cases proof test-source long short))
      (result (proof-proof-cases proof test-prefix both base)))
     (cons result (cdr child)))))

(defun b1-abstract-lists-abstract-list-initial-sublist (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (claim (caddr parts))
      (typed (b1-abstract-lists-list-type-init lib claim index))
      (prefix (proof-term-at claim (b1-abstract-lists-list-type-position typed)))
      (guard-source (proof-term-at (cadr parts) 1))
      (tail-guard (proof-term-at (cadr parts) 2))
      (checked (proof-term-at tail-guard 1))
      (relation (proof-term-at tail-guard 2))
      (relation-parts (proof-list-of-length relation 3)))
     (let* ((xs (caddr relation-parts))
            (test-prefix (list *proof-consp* prefix))
            (test-source (list *proof-consp* xs)))
       (proof-with-checked-results
        ((prefix-cons (proof-proof-assume proof test-prefix t))
         (prefix-atom (proof-proof-assume proof test-prefix nil))
         (source-cons (proof-proof-assume proof test-source t))
         (source-atom (proof-proof-assume proof test-source nil))
         (induction (b1-induction-tree-induction-init lib formula prefix))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-abstract-lists-abstract-list-initial-sublist-consequence
                       premise lib typed induction prefix xs checked relation
                       prefix-cons prefix-atom source-cons source-atom claim))
         (result (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence))))
        (b1-induction-tree-induction-finish (cdr consequence) result))))))

(defun b1-abstract-lists-bind-changed-arguments (before after bindings)
  (if (or (endp before) (endp after))
      bindings
    (b1-abstract-lists-bind-changed-arguments
     (cdr before) (cdr after)
     (if (equal (car before) (car after))
         bindings
       (table-put bindings (car before) (car after))))))

(defun b1-abstract-lists-required-binding (bindings term)
  (let ((entry (assoc-equal term bindings)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun b1-abstract-lists-reuse-abstract-list-consequence-classify-leaf
    (value tests lib typed values fields operation is-cons induction)
  (declare (ignore tests)
           (xargs :measure (acl2-count value)))
  (let ((known (table-get values (b1-abstract-lists-list-type-on typed value) nil))
        (proof (library-library-proof lib))
        (name (car operation)))
    (cond
     (known (cons known induction))
     ((proof-is-call value *proof-cons*)
      (proof-with-checked-results
       ((element (proof-term-at value 1))
        (head (b1-abstract-lists-required-binding fields element)))
       (if (not (consp (cddr value)))
           '(:failure "failure" "")
         (proof-with-checked-results
          ((tail (b1-abstract-lists-reuse-abstract-list-consequence-classify-leaf
                  (caddr value) nil lib typed values fields operation is-cons induction))
           (pair (b1-abstract-lists-list-type-pair typed value head (car tail))))
          (cons pair (cdr tail))))))
     ((not (proof-is-call value name)) '(:failure "failure" ""))
     (t
      (proof-with-checked-results
       ((child (b1-induction-tree-induction-hypothesis
                induction (b1-abstract-lists-bind-changed-arguments (cdr operation) (cdr value) nil)
                (list (list is-cons t))))
        (facts
         (let ((facts (table-values values)))
           (if (not (equal name *b1-abstract-lists-revappend*))
               facts
             (proof-with-checked-results
              ((extended (proof-term-at value 2))
               (head-term (proof-term-at extended 1))
               (head (b1-abstract-lists-required-binding fields head-term))
               (accumulator (proof-term-at operation 2))
               (tail (b1-abstract-lists-required-binding
                      values (b1-abstract-lists-list-type-on typed accumulator)))
               (moved (b1-abstract-lists-list-type-pair typed extended head tail)))
              (append facts (list moved))))))
        (child-formula (proof-step-first (car child)))
        (guard (proof-term-at child-formula 1))
        (supported (b1-abstract-lists-normalize-proof lib guard facts))
        (step (proof-proof-modus-ponens proof (car child) supported)))
       (cons step (cdr child)))))))

(defun b1-abstract-lists-reuse-abstract-list-classify-leaves
    (requests lib typed values fields operation is-cons induction)
  (if (endp requests)
      (cons nil induction)
    (proof-with-checked-results
     ((request (car requests))
      (leaf (b1-abstract-lists-reuse-abstract-list-consequence-classify-leaf
             (car request) (cadr request) lib typed values fields operation is-cons induction))
      (rest (b1-abstract-lists-reuse-abstract-list-classify-leaves
             (cdr requests) lib typed values fields operation is-cons (cdr leaf))))
     (cons (cons (cons request (car leaf)) (car rest)) (cdr rest)))))

(defun b1-abstract-lists-reuse-abstract-list-consequence-classify
    (equation values fields lib typed operation is-cons induction template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((term (proof-rewritten-term equation))
      (opened (b1-abstract-lists-normalize lib term nil (list *b1-abstract-lists-cons-hint*) nil t))
      (equation (proof-proof-chain proof equation (list opened)))
      (value (proof-rewritten-term equation))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaves (b1-abstract-lists-reuse-abstract-list-classify-leaves
               requests lib typed values fields operation is-cons induction))
      (step (proof-proof-by-value proof value template (car leaves) nil))
      (result (library-library-transport-argument lib step equation
                                                   (b1-abstract-lists-list-type-position typed))))
     (cons result (cdr leaves)))))

(defun b1-abstract-lists-bind-proof-steps (steps bindings)
  (if (endp steps)
      bindings
    (proof-with-checked-results ((term (proof-step-first (car steps))))
      (b1-abstract-lists-bind-proof-steps (cdr steps) (table-put bindings term (car steps))))))

(defun b1-abstract-lists-reuse-abstract-list-classify-step
    (lib typed values fields operation is-cons induction template cons extra)
  (let* ((proof (library-library-proof lib))
         (name (car operation))
         (unfold (list name *b1-logic-atom* *b1-logic-endp* *proof-not*)))
    (if (not (equal name (proof-sym "PUT-SEG" "ACL2")))
        (proof-with-checked-results
         ((equation (b1-abstract-lists-normalize lib operation (list cons) unfold nil t)))
         (b1-abstract-lists-reuse-abstract-list-consequence-classify
          equation values fields lib typed operation is-cons induction template))
      (proof-with-checked-results
       ((segment-type (if (consp extra) (car extra) '(:failure "failure" "")))
        (segment (proof-term-at operation 2))
        (segment-test (list *proof-consp* segment))
        (found (proof-proof-assume proof segment-test t))
        (missing (proof-proof-assume proof segment-test nil))
        (new-fields (b1-abstract-lists-list-type-fields typed segment-type found))
        (after (b1-abstract-lists-normalize lib operation (list cons found) unfold nil t))
        (tail (proof-step-first (cadr new-fields)))
        (head (proof-step-first (car new-fields)))
        (element (proof-term-at head (b1-abstract-lists-list-type-position typed)))
        (yes (b1-abstract-lists-reuse-abstract-list-consequence-classify
              after (table-put values tail (cadr new-fields))
              (table-put fields element (car new-fields)) lib typed operation
              is-cons induction template))
        (after (b1-abstract-lists-normalize lib operation (list cons missing) unfold nil t))
        (no (b1-abstract-lists-reuse-abstract-list-consequence-classify
             after values fields lib typed operation is-cons (cdr yes) template))
        (result (proof-proof-cases proof segment-test (car yes) (car no))))
       (cons result (cdr no))))))

(defun b1-abstract-lists-reuse-abstract-list-open-base (lib operation driver atom)
  (if (equal (car operation) *b1-abstract-lists-last*)
      (proof-with-checked-results
       ((empty-tail (b1-structures-noncons-selector lib *library-cdr* atom))
        (tail-atom (b1-abstract-lists-normalize
                    lib (list *b1-logic-atom* (list *library-cdr* driver)) nil
                    (list *b1-logic-atom* *proof-not*) (list (b1-logic-equal-to empty-tail)))))
       (b1-abstract-lists-normalize lib operation nil (list *b1-abstract-lists-last*)
                                    (list (b1-logic-equal-to tail-atom))))
    (b1-revappend-open-list lib operation (list atom))))

(defun b1-abstract-lists-reuse-abstract-list-consequence
    (premise lib typed induction operation driver is-cons cons atom template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((premises (b1-logic-bookproof-split-conjuncts lib premise))
      (empty-call (b1-abstract-lists-list-type-on typed *proof-false*))
      (empty (b1-abstract-lists-list-type-empty typed))
      (source (proof-step-first (car premises)))
      (tails (b1-abstract-lists-bind-proof-steps
              (cdr premises)
              (b1-abstract-lists-two-bindings empty-call empty source (car premises))))
      (pieces (b1-abstract-lists-list-type-fields typed (car premises) cons))
      (tail (proof-step-first (cadr pieces)))
      (head (proof-step-first (car pieces)))
      (element (proof-term-at head (b1-abstract-lists-list-type-position typed)))
      (step (b1-abstract-lists-reuse-abstract-list-classify-step
             lib typed (table-put tails tail (cadr pieces)) (list (cons element (car pieces)))
             operation is-cons induction template cons (cdr premises)))
      (opened (b1-abstract-lists-reuse-abstract-list-open-base lib operation driver atom))
      (base (b1-abstract-lists-reuse-abstract-list-consequence-classify
             opened tails nil lib typed operation is-cons (cdr step) template))
      (result (proof-proof-cases proof is-cons (car step) (car base))))
     (cons result (cdr base)))))

(defun b1-abstract-lists-reuse-abstract-list (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (typed (b1-abstract-lists-list-type-init lib (caddr parts) index))
      (operation (proof-term-at (caddr parts) (b1-abstract-lists-list-type-position typed)))
      (name (proof-term-at operation 0))
      (driver (if (member-equal name (list *b1-abstract-lists-last* *b1-abstract-lists-revappend*
                                            (proof-sym "REMOVE-DUPLICATES-EQUAL" "ACL2")))
                  (proof-term-at operation 1)
                (car (last operation)))))
     (let ((is-cons (list *proof-consp* driver)))
       (proof-with-checked-results
        ((cons (proof-proof-assume proof is-cons t))
         (atom (proof-proof-assume proof is-cons nil))
         (induction (b1-induction-tree-induction-init lib formula driver))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-abstract-lists-reuse-abstract-list-consequence
                       premise lib typed induction operation driver is-cons cons atom
                       (b1-abstract-lists-list-type-on typed *proof-result*)))
         (result (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence))))
        (b1-induction-tree-induction-finish (cdr consequence) result))))))

(defun b1-abstract-lists-nfix-at-zero-test (lib index zp)
  (let ((proof (library-library-proof lib))
        (fixed (list *b1-abstract-lists-acl2-nfix* index))
        (integer-test (library-integer index))
        (negative (library-lt index *proof-zero*)))
    (proof-with-checked-results
     ((valid (proof-proof-assume proof integer-test t))
      (invalid (proof-proof-assume proof integer-test nil))
      (below (proof-proof-assume proof negative t))
      (nonnegative (proof-proof-assume proof negative nil))
      (pos (proof-proof-assume proof (library-positive index) t))
      (zp-test (proof-step-first zp))
      (false-zp (b1-abstract-lists-normalize lib zp-test (list valid pos)
                                              (list *b1-logic-zp* *proof-not*)))
      (impossible (proof-proof-rewrite proof zp false-zp '(1)))
      (not-nil (b1-logic-proof-not-nil proof))
      (impossible (proof-proof-cut proof impossible not-nil))
      (positive-test (proof-step-first pos))
      (upper (proof-proof-front proof impossible (proof-neg positive-test)))
      (order (b1-arithmetic-integer-compare lib index *proof-zero* (list valid)))
      (zero (proof-proof-cut proof order upper))
      (zero (proof-proof-front proof zero (proof-eq index *proof-zero*)))
      (unchanged (b1-abstract-lists-normalize lib fixed (list valid nonnegative)
                                               (list *b1-abstract-lists-acl2-nfix* *proof-not*)))
      (case-zero (proof-proof-chain proof unchanged (list zero)))
      (case-negative (b1-abstract-lists-normalize lib fixed (list valid below)
                                                   (list *b1-abstract-lists-acl2-nfix* *proof-not*)))
      (other (b1-abstract-lists-normalize lib fixed (list invalid)
                                           (list *b1-abstract-lists-acl2-nfix* *proof-not*)))
      (integral-case (proof-proof-cases proof negative case-negative case-zero)))
     (proof-proof-cases proof integer-test integral-case other))))

(defun b1-abstract-lists-shift-fixed-index (lib index next-index)
  (proof-with-checked-results
   ((bounds (b1-abstract-lists-positive-index lib index))
    (natural (b1-quotient-natural-from-positive lib index (car bounds) (cadr bounds)))
    (original (b1-integer-nfix-identity lib natural))
    (shifted (b1-abstract-lists-shifted-positive-index lib next-index (car bounds) (cadr bounds))))
   (let ((lib (cdr shifted)))
     (proof-with-checked-results
      ((next-nat (library-library-cite lib "NATURAL-FROM-BOUNDS" (list next-index) (car shifted)))
       (next-fixed (b1-integer-nfix-identity lib next-nat)))
      (cons (list (car bounds) original next-fixed) lib)))))

(defun b1-abstract-lists-number-comparison (lib before after evidence)
  (proof-with-checked-results
   ((sums (b1-arithmetic-number-sums-init lib))
    (equation (b1-arithmetic-number-sums-comparison-equation sums before after evidence)))
   (cons equation (b1-arithmetic-number-sums-library sums))))

(defun b1-abstract-lists-smaller-strict-index-bound (lib limit cons index next-index)
  (proof-with-checked-results
   ((shifted (b1-abstract-lists-shift-fixed-index lib index next-index)))
   (let* ((lib (cdr shifted))
          (proof (library-library-proof lib))
          (steps (car shifted)))
     (proof-with-checked-results
      ((size-term (proof-term-at limit 2))
       (size (b1-revappend-open-list lib size-term (list cons)))
       (before (proof-proof-reflexive proof limit))
       (before (proof-proof-rewrite proof before (cadr steps) '(1 2 1)))
       (before (proof-proof-rewrite proof before size '(1 2 2)))
       (test (proof-step-first cons))
       (items (proof-term-at test 1))
       (before-term (proof-rewritten-term before))
       (alignment (b1-abstract-lists-number-comparison
                   lib before-term (library-lt next-index (list *library-len* (list *library-cdr* items)))
                   (list (car steps)))))
      (let* ((lib (cdr alignment))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
         ((before (proof-proof-chain proof before (list (car alignment))))
          (next-fixed (proof-proof-symmetric proof (caddr steps)))
          (result (proof-proof-rewrite proof before next-fixed '(1 2 1))))
         (cons result lib)))))))

(defun b1-abstract-lists-beyond-empty-list (lib comparison atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((fixed (proof-term-at comparison 1))
      (natural (b1-integer-nfix-natural lib fixed))
      (lower (library-library-cite lib "NATURAL-NONNEGATIVE" (list fixed) (list natural)))
      (size (proof-term-at comparison 2))
      (opened (b1-revappend-open-list lib size (list atom)))
      (symmetric (proof-proof-symmetric proof opened)))
     (proof-proof-rewrite proof lower symmetric '(1 1 2)))))

(defun b1-abstract-lists-at-least (parts minimum)
  (cond ((integerp parts)
         '(:failure "failure" ""))
        ((< (len parts) minimum)
         '(:failure "failure" ""))
        (t parts)))

(defun b1-abstract-lists-abstract-list-bounded-operation-supported
    (lib typed source fields xs opened update)
  (if (not update)
      (b1-abstract-lists-list-type-empty typed)
    (let ((proof (library-library-proof lib))
          (smaller (b1-abstract-lists-list-type-on typed (list *library-cdr* xs))))
      (proof-with-checked-results
       ((source-term (proof-step-first source))
        (cdr-law (b1-abstract-lists-list-type-prior typed "CDR"
                                                   (list *library-implies* source-term smaller)))
        (value (proof-rewritten-term opened))
        (head (if (consp fields) (car fields) '(:failure "failure" "")))
        (tail (proof-proof-modus-ponens proof cdr-law source)))
       (b1-abstract-lists-list-type-pair typed value head tail)))))

(defun b1-abstract-lists-abstract-list-bounded-operation-step
    (lib typed xs index test has-cell induction premises stop resume cons atom call claim update)
  (let* ((proof (library-library-proof lib))
         (source (car premises))
         (fields (butlast (cdr premises) 1))
         (upper (car (last premises)))
         (position (b1-abstract-lists-list-type-position typed)))
    (proof-with-checked-results
     ((opened (b1-revappend-open-list lib call (list stop)))
      (supported (b1-abstract-lists-abstract-list-bounded-operation-supported
                  lib typed source fields xs opened update))
      (base (library-library-transport-argument lib supported opened position))
      (bounds (b1-abstract-lists-positive-index lib index))
      (upper-term (proof-step-first upper))
      (comparison (proof-term-at upper-term 1))
      (size (proof-term-at comparison 1))
      (empty-size (b1-revappend-open-list lib size (list atom)))
      (too-short (proof-proof-rewrite proof upper empty-size '(1 1 1)))
      (impossible (b1-logic-bookproof-contradiction lib (cadr bounds) too-short claim))
      (pieces (b1-abstract-lists-list-type-fields typed source cons))
      (open-next (b1-revappend-open-list lib call (list resume)))
      (next-value (proof-rewritten-term open-next))
      (child (proof-term-at next-value 2))
      (new-index (proof-term-at child 1))
      (new-list (car (last child)))
      (size (b1-revappend-open-list lib size (list cons)))
      (smaller (proof-proof-rewrite proof upper size '(1 1 1)))
      (smaller-term (proof-step-first smaller))
      (comparison (b1-abstract-lists-number-comparison
                   lib (cadr smaller-term) (library-lt (list *library-len* new-list) new-index)
                   (list (car bounds)))))
     (let* ((lib (cdr comparison))
            (proof (library-library-proof lib))
            (typed (b1-abstract-lists-list-type-with-lib typed lib))
            (induction (b1-induction-tree-induction-with-lib induction lib)))
       (proof-with-checked-results
        ((smaller (proof-proof-rewrite proof smaller (car comparison) '(1 1)))
         (hypothesis (b1-induction-tree-induction-hypothesis
                      induction (b1-abstract-lists-two-bindings xs new-list index new-index)
                      (list (list has-cell t))))
         (child-formula (proof-step-first (car hypothesis)))
         (guard (b1-abstract-lists-normalize-proof
                 lib (cadr child-formula) (append (cons (cadr pieces) fields) (list smaller))))
         (tail (proof-proof-modus-ponens proof (car hypothesis) guard))
         (step (b1-abstract-lists-list-type-pair typed next-value (car pieces) tail))
         (step (library-library-transport-argument lib step open-next position))
         (cons-case (proof-proof-cases proof has-cell step impossible))
         (result (proof-proof-cases proof test base cons-case)))
        (list result (cdr hypothesis) lib))))))

(defun b1-abstract-lists-abstract-list-bounded-operation-consequence
    (premise lib typed xs index test has-cell induction stop resume cons atom call claim update)
  (proof-with-checked-results
   ((premises (b1-logic-bookproof-split-conjuncts lib premise))
    (premises (b1-abstract-lists-at-least premises 2)))
   (b1-abstract-lists-abstract-list-bounded-operation-step
    lib typed xs index test has-cell induction premises stop resume cons atom call claim update)))

(defun b1-abstract-lists-abstract-list-bounded-operation (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (claim (caddr parts))
      (typed (b1-abstract-lists-list-type-init lib claim index))
      (call (proof-term-at claim (b1-abstract-lists-list-type-position typed)))
      (call (b1-abstract-lists-at-least call 3)))
     (let* ((number (cadr call))
            (xs (car (last call)))
            (test (list *b1-logic-zp* number))
            (has-cell (list *proof-consp* xs)))
       (proof-with-checked-results
        ((stop (proof-proof-assume proof test t))
         (resume (proof-proof-assume proof test nil))
         (cons (proof-proof-assume proof has-cell t))
         (atom (proof-proof-assume proof has-cell nil))
         (induction (b1-induction-tree-induction-init lib formula xs))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-abstract-lists-abstract-list-bounded-operation-consequence
                       premise lib typed xs number test has-cell induction stop resume cons atom
                       call claim (equal (len call) 4)))
         (result (b1-logic-bookproof-prove-implication-with-premise
                  (caddr consequence) formula premise (car consequence)))
         (result (b1-induction-tree-induction-finish (cadr consequence) result)))
        (cons result (caddr consequence)))))))

(defun b1-abstract-lists-abstract-list-nth-consequence
    (premise lib typed induction lookup index xs test has-cell stop resume cons atom comparison claim)
  (let ((proof (library-library-proof lib))
        (position (b1-abstract-lists-list-type-position typed)))
    (proof-with-checked-results
     ((parts (proof-proof-conjunct proof premise))
      (outside (b1-abstract-lists-beyond-empty-list lib comparison atom))
      (empty (b1-logic-bookproof-contradiction lib (cadr parts) outside claim))
      (fields (b1-abstract-lists-list-type-fields typed (car parts) cons))
      (head-equation (b1-revappend-open-list lib lookup (list cons stop)))
      (chose-head (library-library-transport-argument lib (car fields) head-equation position))
      (opened (b1-revappend-open-list lib lookup (list cons resume)))
      (call (proof-rewritten-term opened))
      (child-args (proof-list-of-length (cdr call) 2))
      (hypothesis (b1-induction-tree-induction-hypothesis
                   induction (b1-abstract-lists-two-bindings index (car child-args) xs (cadr child-args))
                   (list (list has-cell t))))
      (alignment (b1-abstract-lists-smaller-strict-index-bound lib comparison cons index (car child-args))))
     (let* ((lib (cdr alignment))
            (proof (library-library-proof lib))
            (induction (b1-induction-tree-induction-with-lib (cdr hypothesis) lib)))
       (proof-with-checked-results
        ((smaller (proof-proof-rewrite proof (cadr parts) (car alignment) '(1)))
         (child-formula (proof-step-first (car hypothesis)))
         (supported (b1-abstract-lists-normalize-proof lib (cadr child-formula) (list (cadr fields) smaller)))
         (child (proof-proof-modus-ponens proof (car hypothesis) supported))
         (continued (library-library-transport-argument lib child opened position))
         (nonempty (proof-proof-cases proof test chose-head continued))
         (result (proof-proof-cases proof has-cell nonempty empty)))
        (list result induction lib))))))

(defun b1-abstract-lists-abstract-list-nth (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (guard (proof-list-of-length (cadr parts) 4))
      (claim (caddr parts))
      (typed (b1-abstract-lists-list-type-init lib (cadr guard) index))
      (lookup (proof-term-at claim (b1-abstract-lists-list-type-position typed)))
      (call (proof-list-of-length lookup 3)))
     (let* ((number (cadr call))
            (xs (caddr call))
            (test (list *b1-logic-zp* number))
            (has-cell (list *proof-consp* xs)))
       (proof-with-checked-results
        ((stop (proof-proof-assume proof test t))
         (resume (proof-proof-assume proof test nil))
         (cons (proof-proof-assume proof has-cell t))
         (atom (proof-proof-assume proof has-cell nil))
         (induction (b1-induction-tree-induction-init lib formula xs))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-abstract-lists-abstract-list-nth-consequence
                       premise lib typed induction lookup number xs test has-cell stop resume cons atom
                       (caddr guard) claim))
         (result (b1-logic-bookproof-prove-implication-with-premise
                  (caddr consequence) formula premise (car consequence)))
         (result (b1-induction-tree-induction-finish (cadr consequence) result)))
        (cons result (caddr consequence)))))))

(defun b1-abstract-lists-abstract-list-put-nth-consequence
    (premise lib typed induction call index xs test has-cell stop resume cons atom comparison claim destination)
  (let ((proof (library-library-proof lib))
        (position (b1-abstract-lists-list-type-position typed)))
    (proof-with-checked-results
     ((empty (b1-abstract-lists-list-type-empty typed))
      (atom-opening (b1-revappend-open-list lib call (list atom)))
      (empty (library-library-transport-argument lib empty atom-opening position))
      (outside (b1-abstract-lists-beyond-empty-list lib comparison atom))
      (base (b1-abstract-lists-normalize-proof lib claim (list empty outside) (list *b1-revappend-iff*)))
      (fields (b1-abstract-lists-list-type-fields typed premise cons))
      (first (b1-revappend-open-list lib call (list cons stop)))
      (to-pair (b1-revappend-lift-argument lib destination first position))
      (pair (proof-rewritten-term to-pair))
      (rule (b1-abstract-lists-list-type-constructor typed pair))
      (positive-size (b1-revappend-positive-length lib cons))
      (fixed-zero (b1-abstract-lists-nfix-at-zero-test lib index stop))
      (within (library-library-transport-argument lib positive-size fixed-zero 1))
      (yes (b1-abstract-lists-case-proof lib claim (list (cadr fields) within) (list *b1-revappend-iff*)
                                         (list (b1-logic-equal-to to-pair) (b1-logic-equal-to rule))))
      (updated (b1-revappend-open-list lib call (list cons resume)))
      (value (proof-rewritten-term updated))
      (child (proof-term-at value 2))
      (child-args (proof-list-of-length (cdr child) 3))
      (hypothesis (b1-induction-tree-induction-hypothesis
                   induction
                   (b1-abstract-lists-two-bindings xs (caddr child-args) index (car child-args))
                   (list (list has-cell t))))
      (recursive (proof-proof-modus-ponens proof (car hypothesis) (cadr fields)))
      (exposed (b1-revappend-lift-argument lib destination updated position))
      (exposed-term (proof-rewritten-term exposed))
      (stored (b1-abstract-lists-list-type-constructor typed exposed-term))
      (stored-term (proof-rewritten-term stored))
      (reduction (b1-abstract-lists-normalize lib stored-term (list (car fields))))
      (carried (proof-proof-chain proof exposed (list stored reduction)))
      (carried (proof-proof-symmetric proof carried))
      (no (proof-proof-rewrite proof recursive carried '(1 1)))
      (alignment (b1-abstract-lists-smaller-strict-index-bound
                  lib comparison cons index (car child-args))))
     (let* ((lib (cdr alignment))
            (proof (library-library-proof lib))
            (induction (b1-induction-tree-induction-with-lib (cdr hypothesis) lib)))
       (proof-with-checked-results
        ((reversed (proof-proof-symmetric proof (car alignment)))
         (no (proof-proof-rewrite proof no reversed '(1 2 1)))
         (cons-case (proof-proof-cases proof test yes no))
         (result (proof-proof-cases proof has-cell cons-case base)))
        (list result induction lib))))))

(defun b1-abstract-lists-abstract-list-put-nth (lib formula index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (claim (proof-list-of-length (caddr parts) 3))
      (destination (cadr claim))
      (typed (b1-abstract-lists-list-type-init lib destination index))
      (call (proof-term-at destination (b1-abstract-lists-list-type-position typed)))
      (call-parts (proof-list-of-length call 4)))
     (let* ((number (cadr call-parts))
            (xs (cadddr call-parts))
            (test (list *b1-logic-zp* number))
            (has-cell (list *proof-consp* xs)))
       (proof-with-checked-results
        ((stop (proof-proof-assume proof test t))
         (resume (proof-proof-assume proof test nil))
         (cons (proof-proof-assume proof has-cell t))
         (atom (proof-proof-assume proof has-cell nil))
         (comparison (proof-term-at (caddr claim) 1))
         (induction (b1-induction-tree-induction-init lib formula xs))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-abstract-lists-abstract-list-put-nth-consequence
                       premise lib typed induction call number xs test has-cell stop resume cons atom
                       comparison (caddr parts) destination))
         (result (b1-logic-bookproof-prove-implication-with-premise
                  (caddr consequence) formula premise (car consequence)))
         (result (b1-induction-tree-induction-finish (cadr consequence) result)))
        (cons result (caddr consequence)))))))

(defun b1-abstract-lists-abstract-list-butlast-leaves (requests typed take-head kept)
  (if (endp requests)
      nil
    (proof-with-checked-results
     ((step (if (proof-is-call (caar requests) take-head)
                kept
              (b1-abstract-lists-list-type-empty typed)))
      (rest (b1-abstract-lists-abstract-list-butlast-leaves (cdr requests) typed take-head kept)))
     (cons (cons (car requests) step) rest))))

(defun b1-abstract-lists-abstract-list-butlast-consequence (premise lib typed upper call xs amount)
  (let ((proof (library-library-proof lib))
        (take (list (proof-sym "TAKE" "ACL2") amount xs))
        (template (b1-abstract-lists-list-type-on typed *proof-result*)))
    (proof-with-checked-results
     ((fields (proof-proof-conjunct proof premise))
      (source (proof-step-first (car fields)))
      (upper-term (proof-step-first upper))
      (guard (proof-ite source upper-term *proof-false*))
      (theorem (b1-abstract-lists-list-type-prior
                typed "TAKE" (list *library-implies* guard (b1-abstract-lists-list-type-on typed take))))
      (known (b1-abstract-lists-normalize-proof lib guard (list (car fields) upper)))
      (kept (proof-proof-modus-ponens proof theorem known))
      (view (b1-abstract-lists-normalize lib call nil (list (car call))))
      (value (proof-rewritten-term view))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaves (b1-abstract-lists-abstract-list-butlast-leaves requests typed (car take) kept))
      (result (proof-proof-by-value proof value template leaves nil)))
     (library-library-transport-argument lib result view (b1-abstract-lists-list-type-position typed)))))

(defun b1-abstract-lists-abstract-list-butlast-with-library (lib formula index)
  (proof-with-checked-results
   ((parts (proof-list-of-length formula 3))
    (typed (b1-abstract-lists-list-type-init lib (caddr parts) index))
    (call (proof-term-at (caddr parts) (b1-abstract-lists-list-type-position typed)))
    (call-parts (proof-list-of-length call 3)))
   (let* ((xs (cadr call-parts))
          (size (list *library-len* xs))
          (fixed (list *b1-abstract-lists-acl2-nfix* (caddr call-parts))))
     (proof-with-checked-results
      ((fixed-nat (b1-integer-nfix-natural lib fixed))
       (fixed-type (library-library-cite lib "NATURAL-INTEGER" (list fixed) (list fixed-nat)))
       (lower (library-library-cite lib "NATURAL-NONNEGATIVE" (list fixed) (list fixed-nat)))
       (amount (library-diff size fixed))
       (literal (proof-step-first lower))
       (comparison (b1-abstract-lists-number-comparison
                    lib (cadr literal) (library-lt size amount) (list fixed-type))))
      (let* ((lib (cdr comparison))
             (typed (b1-abstract-lists-list-type-with-lib typed lib))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
         ((upper (proof-proof-rewrite proof lower (car comparison) '(1 1)))
          (premise (b1-logic-bookproof-prove-implication-premise lib formula))
          (consequence (b1-abstract-lists-abstract-list-butlast-consequence
                        premise lib typed upper call xs amount))
          (result (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
         (cons result lib)))))))

(defun b1-abstract-lists-abstract-list-butlast (lib formula index)
  (proof-with-checked-results
   ((result (b1-abstract-lists-abstract-list-butlast-with-library lib formula index)))
   (car result)))

(defun b1-abstract-lists-length-after-dropping-zero (lib index size rest target zero integral lower)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list index) (list integral lower)))
      (identity (b1-integer-nfix-identity lib natural))
      (identity (proof-proof-symmetric proof identity))
      (fixed-zero (b1-abstract-lists-nfix-at-zero-test lib index zero))
      (is-zero (proof-proof-chain proof identity (list fixed-zero)))
      (opening (b1-revappend-open-list lib rest (list zero)))
      (dropped (b1-revappend-lift-argument lib (cadr target) opening 1))
      (amount (proof-proof-reflexive proof (caddr target)))
      (amount (proof-proof-rewrite proof amount is-zero '(1 2 2 1)))
      (amount-term (proof-rewritten-term amount))
      (reduction (library-library-linear-equal lib amount-term size nil))
      (amount (proof-proof-chain proof amount (list reduction)))
      (amount (proof-proof-symmetric proof amount)))
     (proof-proof-chain proof dropped (list amount)))))

(defun b1-abstract-lists-length-after-dropping-active
    (lib induction index items size rest target active cons atom integral upper)
  (let ((proof (library-library-proof lib))
        (cell (list *proof-consp* items)))
    (proof-with-checked-results
     ((bounds (b1-abstract-lists-positive-index lib index))
      (empty-size (b1-revappend-open-list lib size (list atom)))
      (too-short (proof-proof-rewrite proof upper empty-size '(1 1 1)))
      (impossible (b1-logic-bookproof-contradiction lib (cadr bounds) too-short target))
      (advanced (b1-revappend-open-list lib rest (list active)))
      (advanced-term (proof-rewritten-term advanced))
      (child-args (proof-list-of-length (cdr advanced-term) 2))
      (shifted (b1-abstract-lists-shifted-positive-index lib (car child-args) integral (cadr bounds))))
     (let* ((new-index (car child-args))
            (tail (cadr child-args))
            (next-length (list *library-len* tail))
            (lib (cdr shifted))
            (proof (library-library-proof lib)))
       (proof-with-checked-results
        ((size-step (b1-revappend-open-list lib size (list cons)))
         (comparison (proof-proof-rewrite proof upper size-step '(1 1 1)))
         (literal (proof-step-first comparison))
         (alignment (b1-abstract-lists-number-comparison lib (cadr literal)
                                                         (library-lt next-length new-index)
                                                         (list integral))))
        (let* ((lib (cdr alignment))
               (proof (library-library-proof lib))
               (induction (b1-induction-tree-induction-with-lib induction lib)))
          (proof-with-checked-results
           ((next-upper (proof-proof-rewrite proof comparison (car alignment) '(1 1)))
            (hypothesis (b1-induction-tree-induction-hypothesis
                         induction (b1-abstract-lists-two-bindings index new-index items tail)
                         (list (list cell t))))
            (child-formula (proof-step-first (car hypothesis)))
            (next-guard (b1-abstract-lists-normalize-proof lib (cadr child-formula)
                                                          (append (car shifted) (list next-upper))))
            (result (proof-proof-modus-ponens proof (car hypothesis) next-guard))
            (left (b1-revappend-lift-argument lib (cadr target) advanced 1))
            (right (b1-revappend-lift-argument lib (caddr target) size-step 1))
            (before (proof-rewritten-term right))
            (after (proof-rewritten-term result))
            (linear (library-library-linear-equal lib before after (list integral)))
            (right (proof-proof-chain proof right (list linear)))
            (right (proof-proof-symmetric proof right))
            (step (proof-proof-chain proof left (list result right)))
            (cases (proof-proof-cases proof cell step impossible)))
           (list cases (cdr hypothesis) lib))))))))

(defun b1-abstract-lists-length-after-dropping-consequence
    (premise lib induction index items size rest target zero active cons atom)
  (proof-with-checked-results
   ((premises (b1-logic-bookproof-split-conjuncts lib premise))
    (premises (proof-list-of-length premises 3))
    (base (b1-abstract-lists-length-after-dropping-zero
           lib index size rest target zero (car premises) (cadr premises)))
    (active (b1-abstract-lists-length-after-dropping-active
             lib induction index items size rest target active cons atom (car premises) (caddr premises))))
   (let* ((lib (caddr active))
          (proof (library-library-proof lib)))
     (proof-with-checked-results
      ((result (proof-proof-cases proof (list *b1-logic-zp* index) base (car active))))
      (list result (cadr active) lib)))))

(defun b1-abstract-lists-length-after-dropping-lemma (lib)
  (let* ((index (proof-sym "N" "ACL2"))
         (items *library-x*)
         (size (list *library-len* items))
         (rest (list *b1-abstract-lists-nthcdr* index items))
         (target (proof-eq (list *library-len* rest) (library-diff size index)))
         (guard (proof-ite (library-integer index)
                           (proof-ite (proof-neg (library-lt index *proof-zero*))
                                      (proof-neg (library-lt size index)) *proof-false*)
                           *proof-false*))
         (formula (list *library-implies* guard target))
         (induction (b1-induction-tree-induction-init lib formula items))
         (test (list *b1-logic-zp* index))
         (cell (list *proof-consp* items))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((zero (proof-proof-assume proof test t))
      (active (proof-proof-assume proof test nil))
      (cons (proof-proof-assume proof cell t))
      (atom (proof-proof-assume proof cell nil))
      (premise (b1-logic-bookproof-prove-implication-premise lib formula))
      (consequence (b1-abstract-lists-length-after-dropping-consequence
                    premise lib induction index items size rest target zero active cons atom))
      (lib (caddr consequence))
      (result (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence)))
      (result (b1-induction-tree-induction-finish (cadr consequence) result)))
     (library-library-lemma lib "LEN-NTHCDR-BOUNDED" formula result nil))))

(defun b1-abstract-lists-length-after-dropping (lib index items evidence)
  (let ((name (proof-sym "SELF-LEN-NTHCDR-BOUNDED" "ACL2")))
    (proof-with-checked-results
     ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
               lib
             (b1-abstract-lists-length-after-dropping-lemma lib)))
      (proof (library-library-proof lib))
      (law (proof-proof-fact proof name (list (list (proof-sym "N" "ACL2") index)
                                             (list *library-x* items))))
      (literal (proof-step-first law))
      (guard (b1-abstract-lists-normalize-proof lib (cadr literal) evidence))
      (result (proof-proof-modus-ponens proof law guard)))
     (cons result lib))))

(defun b1-abstract-lists-abstract-list-subseq-consequence-slice-with
    (end-test limit limit-type upper-end lib typed call start drop integral remaining subset not-string size-equation)
  (let ((amount (library-diff limit start)))
    (proof-with-checked-results
     ((upper (proof-step-first upper-end))
      (size (proof-rewritten-term remaining))
      (shifted (b1-abstract-lists-number-comparison lib (cadr upper) (library-lt size amount)
                                                   (list integral limit-type))))
     (let* ((lib (cdr shifted))
            (proof (library-library-proof lib))
            (typed (b1-abstract-lists-list-type-with-lib typed lib)))
       (proof-with-checked-results
        ((supported (proof-proof-rewrite proof upper-end (car shifted) '(1 1)))
         (remaining (proof-proof-symmetric proof remaining))
         (supported (proof-proof-rewrite proof supported remaining '(1 1 1)))
         (subject (proof-step-first subset))
         (bound (proof-step-first supported))
         (guard (proof-ite subject bound *proof-false*))
         (take (list (proof-sym "TAKE" "ACL2") amount drop))
         (fact (b1-abstract-lists-list-type-prior
                typed "TAKE" (list *library-implies* guard (b1-abstract-lists-list-type-on typed take))))
         (condition (b1-abstract-lists-normalize-proof lib guard (list subset supported)))
         (typed-slice (proof-proof-modus-ponens proof fact condition))
         (head (proof-term-at call 0))
         (opened (b1-abstract-lists-normalize lib call (list not-string end-test)
                                             (list head (proof-sym "SUBSEQ-LIST" "ACL2"))
                                             (list (b1-logic-equal-to size-equation))))
         (result (library-library-transport-argument lib typed-slice opened
                                                      (b1-abstract-lists-list-type-position typed))))
        (cons result lib))))))

(defun b1-abstract-lists-abstract-list-subseq-cases
    (lib typed call start end drop size integral remaining subset not-string size-equation end-bounds)
  (let ((proof (library-library-proof lib))
        (is-nil (proof-eq end *proof-false*)))
    (proof-with-checked-results
     ((present (proof-proof-assume proof end t))
      (missing (proof-proof-assume proof end nil))
      (nil-test (proof-proof-assume proof is-nil t))
      (impossible (proof-proof-rewrite proof present nil-test '(1)))
      (not-nil (b1-logic-proof-not-nil proof))
      (impossible (proof-proof-cut proof impossible not-nil))
      (positive-end (proof-proof-front proof impossible (proof-neg is-nil)))
      (literal (proof-step-first end-bounds))
      (null-eq (b1-abstract-lists-normalize lib (cadr literal) nil
                                            (list *b1-abstract-lists-null* *b1-logic-eq*)))
      (nonempty (library-library-transport-argument lib positive-end null-eq 1))
      (proved (proof-proof-prove-if proof end-bounds nonempty))
      (end-types (proof-proof-conjunct proof proved))
      (yes (b1-abstract-lists-abstract-list-subseq-consequence-slice-with
            present end (car end-types) (cadr end-types) lib typed call start drop
            integral remaining subset not-string size-equation)))
     (let ((lib (cdr yes)))
       (proof-with-checked-results
        ((size-type (library-library-type-of lib size nil))
         (weak-size (library-library-cite lib "WEAK-REFLEXIVE" (list size) (list size-type)))
         (no (b1-abstract-lists-abstract-list-subseq-consequence-slice-with
              missing size size-type weak-size lib typed call start drop integral remaining
              subset not-string size-equation))
         (result (proof-proof-cases (library-library-proof (cdr no)) end (car yes) (car no))))
        (cons result (cdr no)))))))

(defun b1-abstract-lists-abstract-list-subseq-consequence
    (premise lib typed call xs start end drop size)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((premises (b1-logic-bookproof-split-conjuncts lib premise))
      (premises (proof-list-of-length premises 5))
      (proper (b1-abstract-lists-list-type-proper typed (car premises)))
      (not-string (b1-structures-proper-list-is-not-string lib proper))
      (size-equation (b1-structures-length-of-list lib proper))
      (source (proof-step-first (car premises)))
      (drop-type (b1-abstract-lists-list-type-prior
                  typed "NTHCDR" (list *library-implies* source (b1-abstract-lists-list-type-on typed drop))))
      (subset (proof-proof-modus-ponens proof drop-type (car premises)))
      (remaining (b1-abstract-lists-length-after-dropping
                  lib start xs (list (cadr premises) (caddr premises) (cadddr premises)))))
     (b1-abstract-lists-abstract-list-subseq-cases
      (cdr remaining) typed call start end drop size (cadr premises) (car remaining)
      subset not-string size-equation (nth 4 premises)))))

(defun b1-abstract-lists-abstract-list-subseq (lib formula index)
  (proof-with-checked-results
   ((parts (proof-list-of-length formula 3))
    (typed (b1-abstract-lists-list-type-init lib (caddr parts) index))
    (call (proof-term-at (caddr parts) (b1-abstract-lists-list-type-position typed)))
    (call-parts (proof-list-of-length call 4)))
   (let* ((xs (cadr call-parts))
          (start (caddr call-parts))
          (end (cadddr call-parts))
          (drop (list *b1-abstract-lists-nthcdr* start xs))
          (size (list *library-len* xs)))
     (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-abstract-lists-abstract-list-subseq-consequence
                     premise lib typed call xs start end drop size))
       (result (b1-logic-bookproof-prove-implication-with-premise
                (cdr consequence) formula premise (car consequence))))
      (cons result (cdr consequence))))))
