(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h3-atom-order-alphorder* (proof-sym "ALPHORDER" "ACL2"))
(defconst *h3-atom-order-bad-atom* (proof-sym "BAD-ATOM" "ACL2"))
(defconst *h3-atom-order-bad-le* (proof-sym "BAD-ATOM<=" "ACL2"))
(defconst *h3-atom-order-complex-rationalp* (proof-sym "COMPLEX-RATIONALP" "ACL2"))
(defconst *h3-atom-order-length* (proof-cl "LENGTH"))
(defconst *h3-atom-order-string-le* (proof-cl "STRING<="))
(defconst *h3-atom-order-char-code* (proof-cl "CHAR-CODE"))
(defconst *h3-atom-order-kinds*
  (list *library-rationalp* *h3-atom-order-complex-rationalp*
        *h3-rewrite-characterp* *h3-rewrite-stringp* *h3-rewrite-symbolp*))

(defun h3-atom-order-step-term (step index)
  (if (null step)
      '(:failure "MalformedTacticInput" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun h3-atom-order-less-same (library)
  (let* ((proof (library-library-proof library))
         (name (proof-sym "SELF-H3-LESS-SAME" "ACL2")))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name library)
      (proof-with-checked-results
          ((opened (library-library-axiom library "<-ON-OTHERS" (list *library-x* *library-x*)))
           (inverse (library-library-axiom library "INVERSE-OF-+" (list *library-x*)))
           (step (proof-proof-rewrite proof opened inverse '(1 2 1)))
           (test (library-lt *proof-zero* *proof-zero*))
           (computation (proof-proof-compute proof test (cadr *proof-false*)))
           (step (proof-proof-chain proof step (list computation)))
           (claim (proof-eq (library-lt *library-x* *library-x*) *proof-false*))
           (library (library-library-lemma library "H3-LESS-SAME" claim step nil)))
        (cons name library)))))

(defun h3-atom-order-bad-atom-order (library)
  (let* ((proof (library-library-proof library))
         (name (proof-sym "SELF-H3-BAD-ATOM-REFLEXIVE" "ACL2")))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name library)
      (proof-with-checked-results
          ((bad (list *h3-atom-order-bad-atom* *library-x*))
           (test (list *h3-atom-order-bad-le* *library-x* *library-x*))
           (p (proof-proof-assume proof bad t))
           (total (library-library-axiom library "BAD-ATOM<=-TOTAL" (list *library-x* *library-x*)))
           (search (h3-rewrite-search-init library nil nil nil 150 nil))
           (guard (h3-atom-order-step-term total 1))
           (guard-proof (car (h3-rewrite-search-prove search guard (list p))))
           (total (proof-proof-modus-ponens proof total guard-proof))
           (yes (proof-proof-assume proof test t))
           (denial (proof-proof-assume proof test nil))
           (no (proof-proof-prove-if proof total denial))
           (result (proof-proof-cases proof test yes no))
           (library (library-library-lemma library "H3-BAD-ATOM-REFLEXIVE" test result
                                           (list (proof-neg bad)))))
        (cons name library)))))

(defun h3-atom-order-other-than-number (library)
  (let* ((proof (library-library-proof library))
         (name (proof-sym "SELF-H3-NONNUMBER-FROM-TYPES" "ACL2")))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name library)
      (proof-with-checked-results
          ((rational (list *library-rationalp* *library-x*))
           (complexp (list *h3-atom-order-complex-rationalp* *library-x*))
           (number (list *library-numberp* *library-x*))
           (p (proof-proof-assume proof rational nil))
           (q (proof-proof-assume proof complexp nil))
           (fact (proof-proof-fact proof "acl2-numberp-cases" nil))
           (hypothesis (proof-proof-assume proof number t))
           (cases (proof-proof-modus-ponens proof fact hypothesis))
           (complex-case (proof-proof-prove-if proof cases p))
           (contradiction (proof-proof-cut proof complex-case q))
           (claim (proof-neg number))
           (result (proof-proof-front proof contradiction claim))
           (library (library-library-lemma library "H3-NONNUMBER-FROM-TYPES" claim result
                                           (list rational complexp))))
        (cons name library)))))

(defun h3-atom-order-length-holds (library)
  (let ((name (proof-sym "SELF-H3-LENGTH-NON-NIL" "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof library)))
        (cons name library)
      (proof-with-checked-results
          ((library (h3-merges-arithmetic library))
           (term (list *h3-atom-order-length* *library-x*))
           (number (library-library-cite library "LENGTH-NUMBER" (list *library-x*) nil))
           (step (h3-rewrite-nonnil-from-type library number))
           (library (library-library-lemma library "H3-LENGTH-NON-NIL" term step nil)))
        (cons name library)))))

(defun h3-atom-order-alphorder-reflexive (library formula)
  (proof-with-checked-results
      ((less-same (h3-atom-order-less-same library))
       (bad-atom-order (h3-atom-order-bad-atom-order (cdr less-same)))
       (other-than-number (h3-atom-order-other-than-number (cdr bad-atom-order)))
       (length-holds (h3-atom-order-length-holds (cdr other-than-number)))
       (library (cdr length-holds))
       (names (list (car less-same) (car bad-atom-order) (car other-than-number) (car length-holds)
                    (proof-sym "SYMBOL<-IRREFLEXIVE" "ACL2")))
       (definitions (list *h3-atom-order-alphorder* (proof-cl "=") *h3-atom-order-string-le*
                          *proof-not* *h3-atom-order-bad-atom*))
       (rules (h3-rewrite-rules-init library names nil))
       (search (h3-rewrite-search-init library definitions nil rules 150 nil))
       (step (car (h3-rewrite-search-prove search formula nil))))
    (cons step library)))

(defun h3-atom-order-complex-evidence (library fact-name values types)
  (if (or (endp values) (endp types))
      nil
    (let ((proof (library-library-proof library)))
      (proof-with-checked-results
          ((fact (proof-proof-fact proof fact-name (list (list *library-x* (car values)))))
           (step (proof-proof-modus-ponens proof fact (car types)))
           (rest (h3-atom-order-complex-evidence library fact-name (cdr values) (cdr types))))
        (cons step rest)))))

(defun h3-atom-order-complex-weak-order-prove (evidence library rules target facts)
  (let ((search (h3-rewrite-search-init
                 library (list *h3-atom-order-alphorder* (proof-cl "=") *proof-not*)
                 nil rules 35 nil)))
    (car (h3-rewrite-search-prove search target (append facts evidence)))))

(defun h3-atom-order-complex-weak-order (library types)
  (proof-with-checked-results
      ((types (proof-list-of-length types 2))
       (x (h3-atom-order-step-term (car types) 1))
       (y (h3-atom-order-step-term (cadr types) 1))
       (x-parts (h3-numeric-real-and-imaginary library x))
       (y-parts (h3-numeric-real-and-imaginary library y))
       (rationals (list (car x-parts) (car y-parts)))
       (not-rational (h3-atom-order-complex-evidence
                      library "complex-rationalp-not-rationalp" (list x y) types))
       (numbers (h3-atom-order-complex-evidence
                 library "complex-rationalp-acl2-numberp" (list x y) types))
       (a (list *h3-numeric-real* x))
       (b (list *h3-numeric-real* y))
       (lower (library-lt a b))
       (same-term (proof-eq a b))
       (source (list *h3-atom-order-alphorder* x y))
       (comparison (library-library-axiom library "COMPLETION-OF-<" (list y x)))
       (target (proof-eq source (library-le x y)))
       (less-same (h3-atom-order-less-same library))
       (library (cdr less-same))
       (proof (library-library-proof library))
       (rules (h3-rewrite-rules-init library (list (car less-same)) nil))
       (facts (append types not-rational numbers (list comparison)))
       (ascend (proof-proof-assume proof lower t))
       (boolean (proof-proof-fact proof "booleanp-<" (list (list *library-x* a) (list *library-y* b))))
       (test (h3-atom-order-step-term boolean 1)))
    (if (not (equal test lower))
        '(:failure "ProofMismatch" "")
      (proof-with-checked-results
          ((nil-case (proof-eq lower *proof-false*))
           (assumption (proof-proof-assume proof nil-case t))
           (nonnil (proof-proof-rewrite proof ascend assumption '(1)))
           (nonnil (proof-proof-tidy proof nonnil))
           (nonnil (proof-proof-front proof nonnil (proof-neg nil-case)))
           (head (h3-atom-order-step-term boolean 0))
           (search (h3-rewrite-search-init library (list head (proof-cl "EQ")) nil nil 150 nil))
           (ascend-value (car (h3-rewrite-search-prove search (proof-eq lower *proof-true*)
                                                      (list boolean nonnil))))
           (no-descend (h3-numeric-order-cite library "LESS-ASYMMETRIC" (list a b)
                                             (append rationals (list ascend))))
           (assumption (proof-proof-assume proof same-term t))
           (contradiction (proof-proof-rewrite proof ascend assumption '(1 1)))
           (less-same (h3-atom-order-less-same library))
           (library (cdr less-same))
           (proof (library-library-proof library))
           (fact (proof-proof-fact proof (car less-same) (list (list *library-x* b))))
           (contradiction (proof-proof-rewrite proof contradiction fact '(1)))
           (contradiction (proof-proof-tidy proof contradiction))
           (not-equal (proof-proof-front proof contradiction (proof-neg same-term)))
           (good (h3-atom-order-complex-weak-order-prove
                  (list ascend ascend-value no-descend not-equal) library rules target facts))
           (no-ascend (proof-proof-assume proof lower nil))
           (assumption (proof-proof-assume proof same-term t))
           (same (h3-atom-order-complex-weak-order-prove
                  (list no-ascend assumption) library rules target facts))
           (no-equal (proof-proof-assume proof same-term nil))
           (denied (proof-proof-assume proof (library-lt b a) nil))
           (eq-when-neither (h3-numeric-order-cite library "WEAK-ANTISYMMETRIC" (list a b)
                                                  (append rationals (list denied no-ascend))))
           (contradiction (proof-proof-cut proof eq-when-neither no-equal))
           (descend (proof-proof-front proof contradiction (library-lt b a)))
           (bad (h3-atom-order-complex-weak-order-prove
                 (list no-ascend no-equal descend) library rules target facts))
           (no (proof-proof-cases proof same-term same bad))
           (step (proof-proof-cases proof lower good no)))
        (cons step library)))))

(defun h3-atom-order-atom-type (library value rank evidence)
  (if (< rank (len *h3-atom-order-kinds*))
      (proof-with-checked-results
          ((index (if (< rank 0) (+ (len *h3-atom-order-kinds*) rank) rank))
           (predicate (if (< index 0)
                          '(:failure "MalformedTacticInput" "")
                        (proof-term-at *h3-atom-order-kinds* index)))
           (key (list predicate value)))
        (let ((entry (assoc-equal key evidence)))
          (if entry
              (cons (cdr entry) library)
            '(:failure "MissingProofData" ""))))
    (proof-with-checked-results
        ((other (h3-atom-order-other-than-number library))
         (library (cdr other))
         (rules (h3-rewrite-rules-init library (list (car other)) nil))
         (search (h3-rewrite-search-init library (list *h3-atom-order-bad-atom* *proof-not*)
                                        nil rules 150 nil))
         (step (car (h3-rewrite-search-prove search (list *h3-atom-order-bad-atom* value)
                                            (table-values evidence)))))
      (cons step library))))

(defun h3-atom-order-atom-types (values library rank evidence)
  (if (endp values)
      (cons nil library)
    (proof-with-checked-results
        ((first (h3-atom-order-atom-type library (car values) rank evidence))
         (rest (h3-atom-order-atom-types (cdr values) (cdr first) rank evidence)))
      (cons (cons (car first) (car rest)) (cdr rest)))))

(defun h3-atom-order-comparison-equation (library first second rank1 rank2 evidence lengths)
  (let ((values (list first second)))
    (if (and (equal rank1 1) (equal rank2 1))
        (proof-with-checked-results ((types (h3-atom-order-atom-types values library rank1 evidence)))
          (h3-atom-order-complex-weak-order (cdr types) (car types)))
      (let ((proof (library-library-proof library)))
        (proof-with-checked-results
            ((call (list *h3-atom-order-alphorder* first second))
             (equation (proof-proof-unfold proof call))
             (search (h3-rewrite-search-init library nil nil nil 150 nil))
             (right (h3-atom-order-step-term equation 2))
             (reduced (car (h3-rewrite-search-reduce search right evidence nil nil)))
             (equation (proof-proof-chain proof equation (list reduced))))
          (if (and (equal rank1 3) (equal rank2 3))
              (proof-with-checked-results
                  ((types (h3-atom-order-atom-types values library rank1 evidence))
                   (library (cdr types))
                   (string-order (h3-symbolic-order-boolean-string-order library (car types) lengths))
                   (step (proof-proof-chain (library-library-proof library) equation (list string-order))))
                (cons step library))
            (cons equation library)))))))

(defun h3-atom-order-character-arguments (values)
  (if (endp values)
      nil
    (cons (list *h3-atom-order-char-code* (car values))
          (h3-atom-order-character-arguments (cdr values)))))

(defun h3-atom-order-character-types (args values library)
  (if (or (endp args) (endp values))
      nil
    (let ((proof (library-library-proof library)))
      (proof-with-checked-results
          ((axiom (library-library-axiom library "INTEGER-IMPLIES-RATIONAL" (list (car args))))
           (fact (proof-proof-fact proof "integerp-char-code" (list (list *library-x* (car values)))))
           (step (proof-proof-modus-ponens proof axiom fact))
           (rest (h3-atom-order-character-types (cdr args) (cdr values) library)))
        (cons step rest)))))

(defun h3-atom-order-numeric-parts (library values types rank)
  (cond ((equal rank 2)
         (proof-with-checked-results
             ((args (h3-atom-order-character-arguments values))
              (types (h3-atom-order-character-types args values library)))
           (list args types)))
        ((equal rank 1)
         (proof-with-checked-results
             ((types (h3-atom-order-complex-evidence
                      library "complex-rationalp-acl2-numberp" values types)))
           (list values types)))
        (t (list values types))))

(defun h3-atom-order-character-equality (library types codes)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((types (proof-list-of-length types 2))
         (a (h3-atom-order-step-term (car types) 1))
         (b (h3-atom-order-step-term (cadr types) 1))
         (rule (proof-sym "CODE-CHAR-CHAR-CODE-IS-IDENTITY" "ACL2"))
         (c (proof-sym "C" "ACL2"))
         (fact (proof-proof-fact proof rule (list (list c a))))
         (left (proof-proof-modus-ponens proof fact (car types)))
         (fact (proof-proof-fact proof rule (list (list c b))))
         (right (proof-proof-modus-ponens proof fact (cadr types)))
         (symmetric (proof-proof-symmetric proof left))
         (step (proof-proof-rewrite proof symmetric codes '(1 2 1))))
      (proof-proof-chain proof step (list right)))))

(defun h3-atom-order-reverse-order (library rank x y types not-forward)
  (cond ((<= rank 2)
         (proof-with-checked-results
             ((parts (h3-atom-order-numeric-parts library (list y x) (reverse types) rank))
              (forward (h3-rewrite-double-negation library not-forward)))
           (h3-numeric-order-cite library "LESS-ASYMMETRIC" (car parts)
                                 (append (cadr parts) (list forward)))))
        ((<= rank 4)
         (proof-with-checked-results ((forward (h3-rewrite-double-negation library not-forward)))
           (h3-symbolic-order-asymmetry library forward)))
        (t (proof-with-checked-results
               ((axiom (library-library-axiom library "BAD-ATOM<=-TOTAL" (list x y)))
                (total (h3-symbolic-order-guarded library axiom types)))
             (proof-proof-prove-if (library-library-proof library) total not-forward)))))

(defun h3-atom-order-same-type-antisymmetry (library rank values types comparisons)
  (proof-with-checked-results ((values (proof-list-of-length values 2)))
    (cond ((<= rank 2)
           (proof-with-checked-results
               ((parts (h3-atom-order-numeric-parts library values types rank))
                (same (h3-numeric-order-cite library "WEAK-ANTISYMMETRIC" (car parts)
                                             (append (cadr parts) comparisons))))
             (if (equal rank 2)
                 (h3-atom-order-character-equality library types same)
               same)))
          ((<= rank 4)
           (let ((head (if (equal rank 3) *h3-symbolic-order-string-lt* *h3-symbolic-order-symbol-lt*)))
             (h3-symbolic-order-antisymmetry library head (car values) (cadr values) types
                                              (car comparisons) (cadr comparisons))))
          (t (proof-with-checked-results
                 ((axiom (library-library-axiom library "BAD-ATOM<=-ANTISYMMETRIC" values)))
               (h3-symbolic-order-guarded library axiom (append types comparisons)))))))

(defun h3-atom-order-same-type-transitivity (library rank values types comparisons)
  (cond ((<= rank 2)
         (proof-with-checked-results ((parts (h3-atom-order-numeric-parts library values types rank)))
           (h3-numeric-order-cite library "WEAK-TRANSITIVE" (car parts)
                                 (append (cadr parts) comparisons))))
        ((<= rank 4)
         (let ((head (if (equal rank 3) *h3-symbolic-order-string-lt* *h3-symbolic-order-symbol-lt*)))
           (h3-symbolic-order-transitivity library head (car values) (cadr values) (caddr values)
                                            types (car comparisons) (cadr comparisons))))
        (t (proof-with-checked-results
               ((axiom (library-library-axiom library "BAD-ATOM<=-TRANSITIVE" values)))
             (h3-symbolic-order-guarded library axiom (append types comparisons))))))

(defun h3-atom-order-alphorder-law-rank (variable ranks)
  (let ((entry (assoc-equal variable ranks)))
    (if entry
        (cdr entry)
      '(:failure "MissingProofData" ""))))

(defun h3-atom-order-alphorder-law-get-pair (pair library ranks equations known length-name)
  (proof-with-checked-results
      ((pair (proof-list-of-length pair 2))
       (a (car pair))
       (b (cadr pair))
       (rank-a (h3-atom-order-alphorder-law-rank a ranks))
       (rank-b (h3-atom-order-alphorder-law-rank b ranks))
       (key (list a b rank-a rank-b)))
    (let ((entry (assoc-equal key equations)))
      (if entry
          (list (cdr entry) library equations)
        (proof-with-checked-results
            ((result (h3-atom-order-comparison-equation library a b rank-a rank-b known length-name)))
          (list (car result) (cdr result) (table-put equations key (car result))))))))

(defun h3-atom-order-alphorder-law-total (library variables goal pairs known ranks equations length-name)
  (proof-with-checked-results
      ((direct (h3-atom-order-alphorder-law-get-pair (car pairs) library ranks equations known length-name))
       (reverse (h3-atom-order-alphorder-law-get-pair (cadr pairs) (cadr direct) ranks
                                                      (caddr direct) known length-name))
       (library (cadr reverse))
       (equations (caddr reverse))
       (reverse (car reverse))
       (direct (car direct))
       (proof (library-library-proof library))
       (test (h3-atom-order-step-term direct 1))
       (right (h3-atom-order-step-term direct 2)))
    (cond ((equal right *proof-true*)
           (proof-with-checked-results
               ((yes (proof-proof-true-from-eq proof direct))
                (selected (proof-proof-select proof goal yes))
                (step (proof-proof-transport proof yes selected)))
             (list step library equations)))
          ((equal right *proof-false*)
           (proof-with-checked-results
               ((no (proof-proof-true-from-eq proof reverse))
                (negation (h3-rewrite-negation library direct))
                (selected (proof-proof-select proof goal negation))
                (step (proof-proof-transport proof no selected)))
             (list step library equations)))
          (t (proof-with-checked-results
                 ((assumption (proof-proof-assume proof test t))
                  (if-true (proof-proof-if-true proof goal))
                  (yes (proof-proof-transport proof assumption if-true))
                  (denied (proof-proof-assume proof test nil))
                  (denied (proof-proof-rewrite proof denied direct '(1 1)))
                  (denied (proof-proof-tidy proof denied))
                  (rank (h3-atom-order-alphorder-law-rank *library-x* ranks))
                  (types (h3-atom-order-atom-types variables library rank known))
                  (library (cdr types))
                  (proof (library-library-proof library))
                  (swapped (h3-atom-order-reverse-order library rank *library-x* *library-y*
                                                        (car types) denied))
                  (swapped (proof-proof-transport proof swapped reverse))
                  (if-false (proof-proof-if-false proof goal))
                  (no (proof-proof-transport proof swapped if-false))
                  (step (proof-proof-cases proof test yes no)))
               (list step library equations))))))

(defun h3-atom-order-alphorder-law-comparisons
    (pairs library goal source known ranks equations length-name comparisons)
  (if (endp pairs)
      (list nil comparisons library equations)
    (proof-with-checked-results
        ((result (h3-atom-order-alphorder-law-get-pair (car pairs) library ranks equations known length-name))
         (equation (car result))
         (library (cadr result))
         (equations (caddr result))
         (proof (library-library-proof library))
         (left (h3-atom-order-step-term equation 1))
         (entry (assoc-equal left source))
         (evidence (if entry (cdr entry) '(:failure "MissingProofData" "")))
         (rewritten (proof-proof-rewrite proof evidence equation '(1)))
         (reduced (proof-proof-tidy proof rewritten))
         (right (h3-atom-order-step-term equation 2)))
      (if (equal right *proof-false*)
          (proof-with-checked-results
              ((step (proof-proof-subsume proof reduced (cons goal (proof-step-clause reduced)))))
            (list step comparisons library equations))
        (h3-atom-order-alphorder-law-comparisons
         (cdr pairs) library goal source known ranks equations length-name
         (append comparisons (list reduced)))))))

(defun h3-atom-order-alphorder-law-typed-branch
    (library variables goal transitive total pairs source known ranks equations length-name)
  (if total
      (h3-atom-order-alphorder-law-total library variables goal pairs known ranks equations length-name)
    (proof-with-checked-results
        ((result (h3-atom-order-alphorder-law-comparisons
                  (list (car pairs) (cadr pairs)) library goal source known ranks equations length-name nil))
         (step (car result))
         (comparisons (cadr result))
         (library (caddr result))
         (equations (cadddr result)))
      (if step
          (list step library equations)
        (proof-with-checked-results
            ((conclusion (if transitive
                             (h3-atom-order-alphorder-law-get-pair (caddr pairs) library ranks equations known length-name)
                           (list nil library equations)))
             (library (cadr conclusion))
             (equations (caddr conclusion))
             (proof (library-library-proof library))
             (conclusion (car conclusion))
             (right (and transitive (h3-atom-order-step-term conclusion 2))))
          (if (and transitive (equal right *proof-true*))
              (proof-with-checked-results ((step (proof-proof-true-from-eq proof conclusion)))
                (list step library equations))
            (proof-with-checked-results
                ((rank (h3-atom-order-alphorder-law-rank *library-x* ranks))
                 (result (h3-atom-order-atom-types variables library rank known))
                 (types (car result))
                 (library (cdr result))
                 (step (if transitive
                           (proof-with-checked-results
                               ((proof-step (h3-atom-order-same-type-transitivity
                                             library rank variables types comparisons)))
                             (proof-proof-transport (library-library-proof library) proof-step conclusion))
                         (h3-atom-order-same-type-antisymmetry library rank variables types comparisons))))
              (list step library equations))))))))

(defun h3-atom-order-alphorder-law-partition-plan (n variables rank)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '((:failure "Fuel" "h3-atom-order-alphorder-law-partition-plan")))
        ((endp variables) '((:prove)))
        ((equal rank (len *h3-atom-order-kinds*))
         (cons (list :rank (car variables) rank)
               (h3-atom-order-alphorder-law-partition-plan (1- n) (cdr variables) 0)))
        (t (let ((test (list (nth rank *h3-atom-order-kinds*) (car variables))))
             (append (list (list :yes test rank))
                     (h3-atom-order-alphorder-law-partition-plan (1- n) (cdr variables) 0)
                     (list (list :no test))
                     (h3-atom-order-alphorder-law-partition-plan (1- n) variables (1+ rank))
                     (list (list :join test)))))))

(defun h3-atom-order-alphorder-law-partition-step
    (action result variables goal transitive total pairs source length-name)
  (let* ((step (car result))
         (library (cadr result))
         (proof (library-library-proof library))
         (known (caddr result))
         (ranks (cadddr result))
         (equations (nth 4 result))
         (positive-proofs (nth 5 result)))
    (case (car action)
      (:rank
       (list step library known (table-put ranks (cadr action) (caddr action)) equations positive-proofs))
      (:yes
       (let* ((test (cadr action))
              (ranks (table-put ranks (cadr test) (caddr action))))
         (proof-with-checked-results ((assumption (proof-proof-assume proof test t)))
           (list step library (table-put known test assumption) ranks equations positive-proofs))))
      (:no
       (let ((test (cadr action)))
         (proof-with-checked-results
             ((known (table-delete known test))
              (assumption (proof-proof-assume proof test nil)))
           (list step library (table-put known (proof-neg test) assumption) ranks equations
                 (cons step positive-proofs)))))
      (:join
       (let ((test (cadr action)))
         (proof-with-checked-results
             ((known (table-delete known (proof-neg test)))
              (step (proof-proof-cases proof test (car positive-proofs) step)))
           (list step library known ranks equations (cdr positive-proofs)))))
      (:prove
       (proof-with-checked-results
           ((result (h3-atom-order-alphorder-law-typed-branch
                     library variables goal transitive total pairs source known ranks equations length-name)))
         (list (car result) (cadr result) known ranks (caddr result) positive-proofs)))
      (otherwise action))))

(defun h3-atom-order-alphorder-law-partition
    (plan result variables goal transitive total pairs source length-name)
  (declare (xargs :measure (acl2-count plan)))
  (if (or (endp plan) (failure-p result))
      result
    (h3-atom-order-alphorder-law-partition
     (cdr plan)
     (h3-atom-order-alphorder-law-partition-step
      (car plan) result variables goal transitive total pairs source length-name)
     variables goal transitive total pairs source length-name)))

(defun h3-atom-order-alphorder-law (library name formula)
  (proof-with-checked-results
      ((library (h3-numeric-order-numeric-order library))
       (length-result (h3-atom-order-length-holds library))
       (length-name (car length-result))
       (library (cdr length-result))
       (proof (library-library-proof library))
       (parts (if (integerp formula)
                  '(:failure "MalformedTacticInput" "")
                (proof-list-of-length (cdr formula) 2)))
       (antecedent (car parts))
       (goal (cadr parts))
       (transitive (text-ends-with name "TRANSITIVE"))
       (total (text-ends-with name "TOTAL"))
       (variables (if transitive
                      (list *library-x* *library-y* *library-z*)
                    (list *library-x* *library-y*)))
       (pairs (if transitive
                  (list (list *library-x* *library-y*) (list *library-y* *library-z*) (list *library-x* *library-z*))
                (list (list *library-x* *library-y*) (list *library-y* *library-x*))))
       (search (h3-rewrite-search-init library nil nil nil 150 nil))
       (step (proof-proof-assume proof antecedent t))
       (source (h3-rewrite-search-context search (list step)))
       (plan (h3-atom-order-alphorder-law-partition-plan 1000000 variables 0))
       (result (h3-atom-order-alphorder-law-partition
                plan (list nil library source nil nil nil) variables goal transitive total pairs source length-name))
       (library (cadr result))
       (step (h3-rewrite-implication library antecedent (car result))))
    (cons step library)))
