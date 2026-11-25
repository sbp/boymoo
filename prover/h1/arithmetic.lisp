(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-arithmetic-abs* (proof-sym "INTEGER-ABS" "ACL2"))
(defconst *h1-arithmetic-reciprocal* (proof-sym "UNARY-/" "ACL2"))
(defconst *h1-arithmetic-expt* (proof-cl "EXPT"))
(defconst *h1-arithmetic-fix* (proof-sym "FIX" "ACL2"))
(defconst *h1-arithmetic-zip* (proof-sym "ZIP" "ACL2"))
(defconst *h1-arithmetic-zp* (proof-sym "ZP" "ACL2"))

; These inference operations are also used by the propositional methods.
(defun h1-arithmetic-proof-has-fact (proof name)
  (if (assoc-equal (proof-sym name "ACL2") (proof-proof-facts proof)) t nil))

(defun h1-arithmetic-proof-cite (proof name arguments evidence)
  (proof-proof-use proof
                  (proof-sym (concatenate 'string "SELF-" name) "ACL2")
                  (seq-zip (list *library-x* *library-y* *library-z*) arguments)
                  evidence))

(defun h1-arithmetic-proof-reflexive (proof term)
  (if (h1-arithmetic-proof-has-fact proof "SELF-REFLEXIVITY")
      (h1-arithmetic-proof-cite proof "REFLEXIVITY" (list term) nil)
    (proof-proof-reflexive-base proof term)))

(defun h1-arithmetic-proof-symmetric (proof equality)
  (proof-with-checked-results
      ((literal (proof-step-first equality))
       (left (proof-term-at literal 1))
       (reflexive (h1-arithmetic-proof-reflexive proof left)))
    (proof-proof-rewrite proof reflexive equality '(1 1))))

(defun h1-arithmetic-proof-assume (proof term holds)
  (if (or (h1-arithmetic-proof-has-fact proof "SELF-EXCLUDED-MIDDLE")
          (not (h1-arithmetic-proof-has-fact proof "SELF-REFLEXIVITY")))
      (proof-proof-assume proof term holds)
    (proof-with-checked-results
        ((not-nil (proof-proof-not-nil proof))
         (nil-or-true (proof-proof-nil-or-true proof term))
         (reversed (h1-arithmetic-proof-symmetric proof nil-or-true))
         (rewritten (proof-proof-rewrite proof not-nil reversed '(1 1)))
         (excluded (proof-proof-tidy proof rewritten)))
      (if holds (proof-proof-front proof excluded term) excluded))))

(defun h1-arithmetic-proof-if-false (proof term)
  (if (or (h1-arithmetic-proof-has-fact proof "SELF-IF-FALSE")
          (not (h1-arithmetic-proof-has-fact proof "SELF-REFLEXIVITY")))
      (proof-proof-if-false proof term)
    (proof-with-checked-results
        ((parts (proof-list-of-length term 4))
         (step (proof-proof-fact proof "if-nil"
                                 (seq-zip (list *library-y* *library-z*) (cddr parts))))
         (nil-or-true (proof-proof-nil-or-true proof (cadr parts)))
         (reversed (h1-arithmetic-proof-symmetric proof nil-or-true)))
      (proof-proof-rewrite proof step reversed '(1 1 1)))))

(defun h1-arithmetic-proof-if-true (proof term)
  (if (or (h1-arithmetic-proof-has-fact proof "SELF-IF-TRUE")
          (not (h1-arithmetic-proof-has-fact proof "SELF-REFLEXIVITY")))
      (proof-proof-if-true proof term)
    (proof-with-checked-results
        ((parts (proof-list-of-length term 4))
         (step (proof-proof-fact proof "if-non-nil"
                                 (seq-zip (list *library-x* *library-y* *library-z*)
                                         (cdr parts))))
         (nil-test (proof-step-first step))
         (assumed (h1-arithmetic-proof-assume proof nil-test t))
         (test-is-nil (h1-arithmetic-proof-symmetric proof assumed))
         (not-nil (proof-proof-not-nil proof))
         (negated-test (proof-proof-rewrite proof not-nil test-is-nil '(1 1)))
         (guard (proof-proof-front proof negated-test (proof-neg nil-test)))
         (result (proof-proof-cut proof step guard)))
      (proof-proof-front proof result (proof-eq term (caddr parts))))))

(defun h1-arithmetic-term-tail (term)
  (if (integerp term)
      '(:failure "failure" "")
    (cdr term)))

(defun h1-arithmetic-proof-select (proof term evidence)
  (proof-with-checked-results
      ((tail (h1-arithmetic-term-tail term))
       (parts (proof-list-of-length tail 3))
       (literal (proof-step-first evidence)))
    (let* ((test (car parts))
           (holds (equal literal test))
           (complement (if holds (proof-neg test) test))
           (name (if holds "IF-TRUE-GUARD" "IF-FALSE-GUARD")))
      (if (or (not (h1-arithmetic-proof-has-fact proof (concatenate 'string "SELF-" name)))
              (equal (proof-step-clause evidence) (list literal complement)))
          (proof-with-checked-results
              ((branch (cond (holds (h1-arithmetic-proof-if-true proof term))
                             ((equal literal (proof-neg test))
                              (h1-arithmetic-proof-if-false proof term))
                             (t '(:failure "failure" "")))))
            (proof-proof-discharge proof branch evidence))
        (proof-with-checked-results
            ((clause (h1-arithmetic-proof-cite proof name parts nil))
             (selected (if holds
                           (proof-proof-cut proof evidence clause)
                         (proof-proof-cut proof clause evidence))))
          (proof-proof-front proof selected
                             (proof-eq term (if holds (cadr parts) (caddr parts)))))))))

(defun h1-arithmetic-proof-prove-if (proof step test-proof)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (selected (h1-arithmetic-proof-select proof literal test-proof))
       (rewritten (proof-proof-rewrite proof step selected '(1))))
    (proof-proof-tidy proof rewritten)))

(defun h1-arithmetic-proof-conjoin (proof formula left right)
  (proof-with-checked-results
      ((left-literal (proof-step-first left))
       (right-literal (proof-step-first right)))
    (if (not (equal formula (proof-ite left-literal right-literal *proof-false*)))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((selected (h1-arithmetic-proof-cite proof "CONJUNCTION-WHEN-LEFT"
                                              (list (cadr formula) (caddr formula)) nil))
           (joined (proof-proof-cut proof left selected))
           (equality (proof-proof-front proof joined (proof-eq right-literal formula)))
           (rewritten (proof-proof-rewrite proof right equality '(1))))
        (proof-proof-tidy proof rewritten)))))

(defun h1-arithmetic-proof-conjunct-base (proof step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (parts (proof-list-of-length literal 4)))
    (if (not (equal (cadddr parts) *proof-false*))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((branch (h1-arithmetic-proof-if-false proof literal))
           (rewritten (proof-proof-rewrite proof step branch '(1)))
           (tidied (proof-proof-tidy proof rewritten))
           (left (proof-proof-front proof tidied (cadr parts)))
           (right (h1-arithmetic-proof-prove-if proof step left)))
        (list left right)))))

(defun h1-arithmetic-proof-conjunct (proof step)
  (if (not (h1-arithmetic-proof-has-fact proof "SELF-CONJUNCTION-RIGHT"))
      (h1-arithmetic-proof-conjunct-base proof step)
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (parts (proof-list-of-length literal 4)))
      (if (not (and (equal (car parts) *proof-if*)
                    (equal (cadddr parts) *proof-false*)))
          '(:failure "failure" "")
        (let ((args (list (cadr parts) (caddr parts))))
          (proof-with-checked-results
              ((left (h1-arithmetic-proof-cite proof "CONJUNCTION-LEFT" args (list step)))
               (right (h1-arithmetic-proof-cite proof "CONJUNCTION-RIGHT" args (list step))))
            (list left right)))))))

(defun h1-arithmetic-proof-modus-ponens-base (proof step evidence)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (head (proof-term-at literal 0)))
    (if (not (equal head *library-implies*))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((opened (proof-proof-unfold proof literal))
           (rewritten (proof-proof-rewrite proof step opened '(1)))
           (reduced (h1-arithmetic-proof-prove-if proof rewritten evidence))
           (remaining (proof-step-first reduced))
           (parts (proof-list-of-length remaining 4)))
        (if (not (and (equal (caddr parts) *proof-true*)
                      (equal (cadddr parts) *proof-false*)))
            '(:failure "failure" "")
          (proof-with-checked-results
              ((branch (h1-arithmetic-proof-if-false proof remaining))
               (result (proof-proof-rewrite proof reduced branch '(1)))
               (tidied (proof-proof-tidy proof result)))
            (proof-proof-front proof tidied (cadr parts))))))))

(defun h1-arithmetic-proof-modus-ponens (proof step evidence)
  (if (not (h1-arithmetic-proof-has-fact proof "SELF-IMPLICATION-ELIM"))
      (h1-arithmetic-proof-modus-ponens-base proof step evidence)
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (parts (proof-list-of-length literal 3)))
      (if (not (equal (car parts) *library-implies*))
          '(:failure "failure" "")
        (proof-with-checked-results ((premise (proof-step-first evidence)))
          (if (not (equal (cadr parts) premise))
              '(:failure "failure" "")
            (h1-arithmetic-proof-cite proof "IMPLICATION-ELIM" (cdr parts)
                                      (list step evidence))))))))

(defun h1-arithmetic-proof-false-premise (proof formula evidence)
  (proof-with-checked-results
      ((step (if (h1-arithmetic-proof-has-fact proof "SELF-IMPLICATION-NO-PREMISE")
                 (proof-with-checked-results ((args (h1-arithmetic-term-tail formula)))
                   (h1-arithmetic-proof-cite proof "IMPLICATION-NO-PREMISE" args nil))
               (proof-with-checked-results
                   ((opened (proof-proof-unfold proof formula))
                    (value (proof-rewritten-term opened))
                    (branch (h1-arithmetic-proof-if-false proof value))
                    (equation (proof-proof-chain proof opened (list branch))))
                 (proof-proof-true-from-eq proof equation)))))
    (if evidence (proof-proof-discharge proof step evidence) step)))

(defun h1-arithmetic-proof-implies-from (proof formula consequence)
  (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
    (if (not (equal (car parts) *library-implies*))
        '(:failure "failure" "")
      (proof-with-checked-results ((literal (proof-step-first consequence)))
        (let ((premise (cadr parts))
              (goal (caddr parts)))
          (cond
           ((not (equal goal literal)) '(:failure "failure" ""))
           ((not (h1-arithmetic-proof-has-fact proof "SELF-IMPLICATION-CONSEQUENT"))
            (proof-with-checked-results
                ((opened (proof-proof-unfold proof formula))
                 (value (proof-rewritten-term opened))
                 (branch (h1-arithmetic-proof-if-true proof value))
                 (yes-equation (proof-proof-chain proof opened (list branch)))
                 (yes-value (proof-rewritten-term yes-equation))
                 (selected (h1-arithmetic-proof-select proof yes-value consequence))
                 (chained (proof-proof-chain proof yes-equation (list selected)))
                 (yes (proof-proof-true-from-eq proof chained))
                 (no (h1-arithmetic-proof-false-premise proof formula nil)))
              (proof-proof-cases proof premise yes no)))
           (t (proof-with-checked-results
                   ((yes (h1-arithmetic-proof-cite proof "IMPLICATION-CONSEQUENT"
                                                  (list premise goal) (list consequence))))
                (if (not (member-equal (proof-neg premise) (proof-step-clause yes)))
                    yes
                  (proof-with-checked-results
                      ((no (h1-arithmetic-proof-false-premise proof formula nil)))
                    (proof-proof-cases proof premise yes no)))))))))))

(defun h1-arithmetic-proof-transport (proof step equality)
  (proof-with-checked-results
      ((reversed (h1-arithmetic-proof-symmetric proof equality))
       (rewritten (proof-proof-rewrite proof step reversed '(1))))
    (proof-proof-tidy proof rewritten)))

(defun h1-arithmetic-library-transport-argument (lib step equality index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reversed (h1-arithmetic-proof-symmetric proof equality))
         (rewritten (proof-proof-rewrite proof step reversed (list 1 index))))
      (proof-proof-tidy proof rewritten))))

(defun h1-arithmetic-simplify-branch (proof redex evidence)
  (let ((test (cadr redex)))
    (if (or (equal test *proof-false*) (equal test *proof-true*))
        (proof-simplify-if-select proof redex evidence)
      (proof-with-checked-results
          ((premise (proof-find-evidence evidence (list test (proof-neg test)))))
        (and premise (h1-arithmetic-proof-select proof redex premise))))))

(defun h1-arithmetic-simplify-chain (proof term first selected)
  (if (not first)
      selected
    (proof-with-checked-results
        ((reflexive (h1-arithmetic-proof-reflexive proof term))
         (rewritten (proof-proof-rewrite proof reflexive first '(1 2 1))))
      (proof-proof-chain proof rewritten (list selected)))))

(mutual-recursion
 (defun h1-arithmetic-simplify-visit (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((head (car term)))
     (cond
      ((zp n) '(:failure "fuel" "h1-arithmetic-simplify-visit"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (next (h1-arithmetic-simplify-visit (1- n) proof (cadr expansion)
                                                evidence definitions)))
         (proof-proof-chain proof (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (h1-arithmetic-simplify-visit (1- n) proof test evidence definitions))
            (redex (proof-simplify-if-redex term first))
            (branch (h1-arithmetic-simplify-branch proof redex evidence))
            (selected (h1-arithmetic-simplify-chain proof term first branch))
            (right (and selected (proof-rewritten-term selected))))
         (if (or (not selected) (equal right redex))
             selected
           (proof-with-checked-results
               ((next (h1-arithmetic-simplify-visit (1- n) proof right evidence definitions)))
             (proof-proof-chain proof selected (list next))))))
      (t (proof-with-checked-results
             ((result (h1-arithmetic-simplify-args (1- n) proof term (cdr term) 1 nil
                                                  evidence definitions))
              (current (if result (proof-rewritten-term result) term))
              (constant (proof-proof-constant-base proof current)))
           (cond ((not constant) result)
                 (result (proof-proof-chain proof result (list constant)))
                 (t constant)))))))
 (defun h1-arithmetic-simplify-args (n proof term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h1-arithmetic-simplify-args"))
    ((endp args) result)
    (t (proof-with-checked-results
           ((equality (h1-arithmetic-simplify-visit (1- n) proof (car args) evidence definitions))
            (next (if equality
                      (proof-with-checked-results
                          ((previous (or result (h1-arithmetic-proof-reflexive proof term))))
                        (proof-proof-rewrite proof previous equality (list 1 2 index)))
                    result)))
         (h1-arithmetic-simplify-args (1- n) proof term (cdr args) (1+ index) next
                                     evidence definitions))))))

(defun h1-arithmetic-proof-simplify (proof term evidence definitions)
  (h1-arithmetic-simplify-visit 1000000 proof term evidence definitions))

(defun h1-arithmetic-conjunction (lib formula claims)
  (declare (xargs :measure (acl2-count claims)))
  (cond
   ((endp claims) '(:failure "failure" ""))
   ((endp (cdr claims))
    (proof-with-checked-results ((literal (proof-step-first (car claims))))
      (if (equal literal formula) (car claims) '(:failure "failure" ""))))
   (t (proof-with-checked-results
          ((right-term (proof-term-at formula 2))
           (right (h1-arithmetic-conjunction lib right-term (cdr claims))))
        (h1-arithmetic-proof-conjoin (library-library-proof lib) formula (car claims) right)))))

(defun h1-arithmetic-discrete (lib integral pos)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first integral))
         (term (proof-term-at literal 1))
         (axiom (proof-proof-fact proof "integer-discrete" (list (list *library-x* term))))
         (claim (proof-step-first axiom))
         (formula (proof-term-at claim 1))
         (premises (h1-arithmetic-conjunction lib formula (list integral pos))))
      (h1-arithmetic-proof-modus-ponens proof axiom premises))))

(defun h1-arithmetic-comparison-by-difference (lib left right difference)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left-args (h1-arithmetic-term-tail left))
         (a (library-library-axiom lib "<-ON-OTHERS" left-args))
         (right-args (h1-arithmetic-term-tail right))
         (b (library-library-axiom lib "<-ON-OTHERS" right-args))
         (rewritten (proof-proof-rewrite proof a difference '(1 2 1)))
         (reversed (h1-arithmetic-proof-symmetric proof b)))
      (proof-proof-chain proof rewritten (list reversed)))))

(defun h1-arithmetic-decrease-nonnegative (lib term integral pos left)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((bound (h1-arithmetic-discrete lib integral pos))
         (axiom (library-library-axiom lib "<-ON-OTHERS" (list term *proof-one*)))
         (delta (proof-proof-rewrite proof bound axiom '(1 1)))
         (computed (proof-proof-compute proof (library-minus *proof-one*) -1))
         (delta (proof-proof-rewrite proof delta computed '(1 1 1 2)))
         (delta (if left
                    (proof-with-checked-results
                        ((commute (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                                         (list term *proof-neg-one*))))
                      (proof-proof-rewrite proof delta commute '(1 1 1)))
                  delta)))
      (proof-proof-tidy proof delta))))

(defun h1-arithmetic-request-p (value)
  (and (consp value) (eq (car value) :h1-arithmetic-request)))

(defun h1-arithmetic-request-key (request)
  (cadr request))

(defun h1-arithmetic-request-method (request)
  (caddr request))

(defun h1-arithmetic-request-library (request)
  (cadddr request))

(defun h1-arithmetic-request-args (request)
  (car (cddddr request)))

(defun h1-arithmetic-reply (key method lib arguments replies)
  (let ((reply (assoc-equal key replies)))
    (if reply
        (cdr reply)
      (list :h1-arithmetic-request key method lib arguments))))

(defmacro h1-arithmetic-with-replies (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (or (failure-p ,name) (h1-arithmetic-request-p ,name))
             ,name
           (h1-arithmetic-with-replies ,(cdr bindings) ,body))))))

(defund h1-arithmetic-natural-successor (lib replies)
  (let ((proof (library-library-proof lib)))
    (if (h1-arithmetic-proof-has-fact proof "H1-NATURAL-SUCCESSOR")
        lib
      (h1-arithmetic-with-replies
          ((self-natural (proof-proof-fact proof (proof-sym "SELF-NATURAL-INTEGER" "ACL2") nil))
           (added (h1-arithmetic-reply :natural-successor-rule :rules-add lib
                                       (list self-natural t t) replies)))
        (let* ((x *library-x*)
               (nat (list *library-natp* x))
               (successor (library-plus *proof-one* x)))
          (h1-arithmetic-with-replies
              ((assumed (h1-arithmetic-proof-assume proof nat t))
               (integral (library-library-cite lib "NATURAL-INTEGER" (list x) (list assumed)))
               (bound (library-library-cite lib "NATURAL-NONNEGATIVE" (list x) (list assumed)))
               (successor-integer (library-library-type-of lib successor (list integral)))
               (advance (library-library-cite lib "POSITIVE-ONE-PLUS" (list x)
                                               (list integral bound)))
               (nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE" (list successor)
                                                  (list successor-integer advance)))
               (step (library-library-cite lib "NATURAL-FROM-BOUNDS" (list successor)
                                           (list successor-integer nonnegative)))
               (helper (h1-arithmetic-reply :natural-successor-helper :helper lib
                                           (list "NATURAL-SUCCESSOR" step (list (proof-neg nat)) t)
                                           replies)))
            (cdr helper)))))))

(defun h1-arithmetic-index-bound-on-cdr (lib bound length-equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((bound-literal (proof-step-first bound))
         (bound-parts (proof-list-of-length bound-literal 3))
         (length-literal (proof-step-first length-equation))
         (length-parts (proof-list-of-length length-literal 3))
         (upper (caddr length-parts))
         (upper-parts (proof-list-of-length upper 3)))
      (if (not (equal (cadr upper-parts) *proof-one*))
          '(:failure "failure" "")
        (let ((index (cadr bound-parts))
              (tail-length (caddr upper-parts)))
          (proof-with-checked-results
              ((neg-length (library-library-axiom lib "DISTRIBUTIVITY-OF-MINUS-OVER-+"
                                                   (list *proof-one* tail-length)))
               (same (h1-arithmetic-proof-reflexive proof (library-diff index upper)))
               (delta (proof-proof-rewrite proof same neg-length '(1 2 2)))
               (computed (proof-proof-compute proof (library-minus *proof-one*) -1))
               (delta (proof-proof-rewrite proof delta computed '(1 2 2 1)))
               (assoc (library-library-axiom lib "ASSOCIATIVITY-OF-+"
                                              (list index *proof-neg-one*
                                                    (library-minus tail-length))))
               (reversed (h1-arithmetic-proof-symmetric proof assoc))
               (delta (proof-proof-chain proof delta (list reversed)))
               (commute (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                                (list index *proof-neg-one*)))
               (delta (proof-proof-rewrite proof delta commute '(1 2 1)))
               (adjusted (proof-proof-rewrite proof bound length-equation '(1 2)))
               (comparison (h1-arithmetic-comparison-by-difference
                            lib (library-lt index upper)
                            (library-lt (library-plus *proof-neg-one* index) tail-length) delta))
               (rewritten (proof-proof-rewrite proof adjusted comparison '(1))))
            (proof-proof-tidy proof rewritten)))))))

(defund h1-arithmetic-character-at-index (lib formula replies)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (length-term (list *library-len* x))
         (openings (list (proof-cl "ATOM") (proof-cl "ENDP") *proof-not*)))
    (h1-arithmetic-with-replies
        ((parts (proof-list-of-length formula 3))
         (premise (cadr parts))
         (claim-call (proof-term-at (caddr parts) 1))
         (i (proof-term-at claim-call 1))
         (down (library-plus *proof-neg-one* i))
         (tail (list *library-cdr* x))
         (assumed (h1-arithmetic-proof-assume proof premise t))
         (premises (h1-arithmetic-proof-conjunct proof assumed))
         (chars (car premises))
         (limits (h1-arithmetic-proof-conjunct proof (cadr premises)))
         (low (car limits))
         (high (cadr limits))
         (length-eq (proof-proof-unfold proof length-term))
         (length-value (proof-rewritten-term length-eq))
         (zero-branch (h1-arithmetic-proof-if-false proof length-value))
         (zero-length (proof-proof-chain proof length-eq (list zero-branch)))
         (invalid-index (proof-proof-rewrite proof high zero-length '(1 2)))
         (contradiction (proof-proof-cut proof invalid-index low))
         (cons-step (proof-proof-front proof contradiction (list *proof-consp* x)))
         (length-branch (h1-arithmetic-proof-select proof length-value cons-step))
         (next-length (proof-proof-chain proof length-eq (list length-branch)))
         (chars-literal (proof-step-first chars))
         (chars-definition (proof-proof-unfold proof chars-literal))
         (opened-chars (proof-proof-rewrite proof chars chars-definition '(1)))
         (not-nil (proof-proof-not-nil proof))
         (opened-chars-literal (proof-step-first opened-chars))
         (atom-test (proof-term-at opened-chars-literal 1))
         (atom-eq (h1-arithmetic-proof-simplify proof atom-test (list cons-step) openings))
         (not-atom (h1-arithmetic-library-transport-argument lib not-nil atom-eq 1))
         (chars-case (h1-arithmetic-proof-prove-if proof opened-chars not-atom))
         (chars-parts (h1-arithmetic-proof-conjunct proof chars-case))
         (first-char (car chars-parts))
         (tail-chars (cadr chars-parts))
         (opened-nth (proof-proof-unfold proof claim-call))
         (nth-definition (proof-rewritten-term opened-nth))
         (end-test (proof-term-at nth-definition 1))
         (blocked (h1-arithmetic-proof-simplify proof end-test (list cons-step) openings))
         (not-nil (proof-proof-not-nil proof))
         (not-end (h1-arithmetic-library-transport-argument lib not-nil blocked 1))
         (nth-branch (h1-arithmetic-proof-select proof nth-definition not-end))
         (nth-equation (proof-proof-chain proof opened-nth (list nth-branch)))
         (nth-value (proof-rewritten-term nth-equation))
         (stop (proof-term-at nth-value 1))
         (stop-branch (h1-arithmetic-proof-if-true proof nth-value))
         (stopped (proof-proof-chain proof nth-equation (list stop-branch)))
         (yes (h1-arithmetic-library-transport-argument lib first-char stopped 1))
         (not-stop (h1-arithmetic-proof-assume proof stop nil))
         (integral (h1-arithmetic-reply :character-at-index-integer :solve lib
                                        (list (list *library-implies* (proof-neg stop)
                                                    (library-integer i))
                                              (list *h1-arithmetic-zp*) 160)
                                        replies))
         (pos (h1-arithmetic-reply :character-at-index-positive :solve lib
                                   (list (list *library-implies* (proof-neg stop)
                                               (library-positive i))
                                         (list *h1-arithmetic-zp*) 160)
                                   replies))
         (integral (h1-arithmetic-proof-modus-ponens proof integral not-stop))
         (pos (h1-arithmetic-proof-modus-ponens proof pos not-stop))
         (next-low (h1-arithmetic-decrease-nonnegative lib i integral pos t))
         (next-high (h1-arithmetic-index-bound-on-cdr lib high next-length))
         (pairs (list (list i down) (list x tail)))
         (bindings (table-put (list (cons i down)) x tail))
         (child (proof-subst formula bindings))
         (builtin (library-library-builtin lib 3 x))
         (smaller (proof-proof-discharge proof builtin cons-step))
         (smaller-term (proof-step-first smaller))
         (hypothesis (proof-ite smaller-term child *proof-true*))
         (hypothesis-step (h1-arithmetic-proof-assume proof hypothesis t))
         (recursive (h1-arithmetic-proof-prove-if proof hypothesis-step smaller))
         (child-test (proof-term-at child 1))
         (child-premise (h1-arithmetic-conjunction lib child-test
                                                  (list tail-chars next-low next-high)))
         (child-char (h1-arithmetic-proof-modus-ponens proof recursive child-premise))
         (continue-branch (h1-arithmetic-proof-if-false proof nth-value))
         (continued (proof-proof-chain proof nth-equation (list continue-branch)))
         (no (h1-arithmetic-library-transport-argument lib child-char continued 1))
         (branches (proof-proof-cases proof stop yes no))
         (case-step (h1-arithmetic-proof-implies-from proof formula branches))
         (ordinal (library-library-builtin lib 1 x)))
      (proof-proof-induct proof ordinal case-step formula (list *library-count* x) (list pairs)))))

(defun h1-arithmetic-library-number (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
         (axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list term)))
         (integral (library-library-type-of lib term evidence))
         (rational-step (h1-arithmetic-proof-modus-ponens proof axiom integral)))
      (h1-arithmetic-proof-modus-ponens proof fact rational-step))))

(defun h1-arithmetic-positive-trichotomy (lib term integral)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((axiom (library-library-axiom lib "TRICHOTOMY" (list term)))
         (parts (h1-arithmetic-proof-conjunct proof axiom))
         (number (h1-arithmetic-library-number lib term (list integral))))
      (h1-arithmetic-proof-modus-ponens proof (car parts) number))))

(defund h1-arithmetic-nonpositive-absolute-value (lib replies)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (integer-term (library-integer x))
         (positive-term (library-positive x))
         (neg-test (library-lt x *proof-zero*))
         (zero-test (proof-eq x *proof-zero*))
         (abs-x (list *h1-arithmetic-abs* x))
         (openings (list *h1-arithmetic-abs*)))
    (h1-arithmetic-with-replies
        ((integral (h1-arithmetic-proof-assume proof integer-term t))
         (not-positive (h1-arithmetic-proof-assume proof positive-term nil))
         (neg-case (h1-arithmetic-proof-assume proof neg-test t))
         (yes (h1-arithmetic-proof-simplify proof abs-x (list integral neg-case) openings))
         (nonnegative-case (h1-arithmetic-proof-assume proof neg-test nil))
         (zero-negation (proof-proof-compute proof (library-minus *proof-zero*) 0))
         (same (h1-arithmetic-proof-reflexive proof (library-diff x *proof-zero*)))
         (delta (proof-proof-rewrite proof same zero-negation '(1 2 2)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list x *proof-zero*)))
         (delta (proof-proof-chain proof delta (list commute)))
         (double (library-library-cite lib "DOUBLE-NEGATION" (list x) (list integral)))
         (reversed (h1-arithmetic-proof-symmetric proof double))
         (delta (proof-proof-rewrite proof delta reversed '(1 2 2)))
         (comparison (h1-arithmetic-comparison-by-difference
                      lib neg-test (library-positive (library-minus x)) delta))
         (not-negation-positive (proof-proof-rewrite proof nonnegative-case comparison '(1 1)))
         (trichotomy (h1-arithmetic-positive-trichotomy lib x integral))
         (alternatives (h1-arithmetic-proof-prove-if proof trichotomy not-positive))
         (not-zero (h1-arithmetic-proof-assume proof zero-test nil))
         (negative-branch (h1-arithmetic-proof-prove-if proof alternatives not-zero))
         (contradiction (proof-proof-cut proof negative-branch not-negation-positive))
         (zero-assumption (h1-arithmetic-proof-assume proof zero-test t))
         (subsumed (proof-proof-subsume proof contradiction
                                       (cons zero-test (proof-step-clause contradiction))))
         (zero (proof-proof-cases proof zero-test zero-assumption subsumed))
         (no (h1-arithmetic-proof-simplify proof abs-x (list integral nonnegative-case) openings))
         (reversed (h1-arithmetic-proof-symmetric proof zero-negation))
         (no (proof-proof-chain proof no (list zero reversed)))
         (reversed (h1-arithmetic-proof-symmetric proof zero))
         (no (proof-proof-rewrite proof no reversed '(1 2 1)))
         (no (proof-proof-tidy proof no))
         (step (proof-proof-cases proof neg-test yes no)))
      (h1-arithmetic-reply :nonpositive-absolute-value-helper :helper lib
                           (list "ABS-NONPOSITIVE" step (list (proof-neg integer-term) positive-term) t)
                           replies))))

(defun h1-arithmetic-transport-descent (lib step child parent)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reversed-child (h1-arithmetic-proof-symmetric proof child))
         (step (proof-proof-rewrite proof step reversed-child '(1 1 1)))
         (reversed-parent (h1-arithmetic-proof-symmetric proof parent))
         (step (proof-proof-rewrite proof step reversed-parent '(1 2 1))))
      (proof-proof-tidy proof step))))

(defun h1-arithmetic-signed-countdown-down (lib i integral pos)
  (let* ((proof (library-library-proof lib))
         (down (library-plus i *proof-neg-one*))
         (openings (list *h1-arithmetic-abs*)))
    (proof-with-checked-results
        ((number-down (library-library-type-of lib down (list integral)))
         (down-nonnegative (h1-arithmetic-decrease-nonnegative lib i integral pos nil))
         (i-nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE" (list i)
                                             (list integral pos)))
         (abs-i (h1-arithmetic-proof-simplify proof (list *h1-arithmetic-abs* i)
                                              (list integral i-nonnegative) openings))
         (abs-down (h1-arithmetic-proof-simplify proof (list *h1-arithmetic-abs* down)
                                                 (list number-down down-nonnegative) openings))
         (down-step (library-library-builtin lib 10 i))
         (down-step (proof-proof-discharge proof down-step integral))
         (down-step (proof-proof-discharge proof down-step pos)))
      (h1-arithmetic-transport-descent lib down-step abs-down abs-i))))

(defun h1-arithmetic-signed-countdown-up (lib i integral nonzero not-pos replies)
  (let* ((proof (library-library-proof lib))
         (i-neg (library-minus i))
         (up (library-plus i *proof-one*))
         (sum-term (library-plus i-neg *proof-neg-one*)))
    (h1-arithmetic-with-replies
        ((int-neg (library-library-type-of lib i-neg (list integral)))
         (trichotomy (h1-arithmetic-positive-trichotomy lib i integral))
         (possibilities (h1-arithmetic-proof-prove-if proof trichotomy not-pos))
         (neg-positive (h1-arithmetic-proof-prove-if proof possibilities nonzero))
         (up-step (library-library-builtin lib 10 i-neg))
         (up-step (proof-proof-discharge proof up-step int-neg))
         (up-step (proof-proof-discharge proof up-step neg-positive))
         (minus-one (proof-proof-compute proof (library-minus *proof-one*) -1))
         (negated-up (library-library-axiom lib "DISTRIBUTIVITY-OF-MINUS-OVER-+"
                                            (list i *proof-one*)))
         (negated-up (proof-proof-rewrite proof negated-up minus-one '(1 2 2)))
         (reversed (h1-arithmetic-proof-symmetric proof negated-up))
         (up-step (proof-proof-rewrite proof up-step reversed '(1 1 1)))
         (up-limit (h1-arithmetic-discrete lib int-neg neg-positive))
         (same (h1-arithmetic-proof-reflexive proof (library-diff *proof-zero* up)))
         (delta (proof-proof-rewrite proof same negated-up '(1 2 2)))
         (sum-integer (library-library-type-of lib sum-term (list integral)))
         (add-zero (library-library-cite lib "ADD-ZERO-LEFT" (list sum-term) (list sum-integer)))
         (delta (proof-proof-chain proof delta (list add-zero)))
         (reversed (h1-arithmetic-proof-symmetric proof minus-one))
         (delta (proof-proof-rewrite proof delta reversed '(1 2 2)))
         (compare (h1-arithmetic-comparison-by-difference
                   lib (library-positive up) (library-lt i-neg *proof-one*) delta))
         (up-not-positive (h1-arithmetic-library-transport-argument lib up-limit compare 1))
         (int-up (library-library-type-of lib up (list integral)))
         (absolute-value (h1-arithmetic-nonpositive-absolute-value lib replies))
         (lib (cdr absolute-value))
         (proof (library-library-proof lib))
         (rule (proof-sym "H1-ABS-NONPOSITIVE" "ACL2"))
         (abs-up (proof-proof-use proof rule (list (list *library-x* up))
                                  (list int-up up-not-positive)))
         (abs-i (proof-proof-use proof rule (list (list *library-x* i)) (list integral not-pos)))
         (step (h1-arithmetic-transport-descent lib up-step abs-up abs-i)))
      (cons step lib))))

(defund h1-arithmetic-signed-countdown-lemmas (lib replies)
  (let ((proof (library-library-proof lib)))
    (if (h1-arithmetic-proof-has-fact proof "H1-COUNT-ABS-UP")
        lib
      (let* ((i *library-x*)
             (zip-call (list *h1-arithmetic-zip* i))
             (not-zip-term (proof-neg zip-call))
             (pos-term (library-positive i))
             (openings (list *h1-arithmetic-zip*)))
        (h1-arithmetic-with-replies
            ((not-zip (h1-arithmetic-proof-assume proof zip-call nil))
             (integral (h1-arithmetic-reply :signed-countdown-integral :solve lib
                                            (list (list *library-implies* not-zip-term
                                                        (library-integer i)) openings 160)
                                            replies))
             (nonzero (h1-arithmetic-reply :signed-countdown-nonzero :solve lib
                                           (list (list *library-implies* not-zip-term
                                                       (proof-neg (proof-eq i *proof-zero*)))
                                                 openings 160)
                                           replies))
             (integral (h1-arithmetic-proof-modus-ponens proof integral not-zip))
             (nonzero (h1-arithmetic-proof-modus-ponens proof nonzero not-zip))
             (pos (h1-arithmetic-proof-assume proof pos-term t))
             (not-pos (h1-arithmetic-proof-assume proof pos-term nil))
             (down-step (h1-arithmetic-signed-countdown-down lib i integral pos))
             (up (h1-arithmetic-signed-countdown-up lib i integral nonzero not-pos replies))
             (up-step (car up))
             (lib (cdr up))
             (down-helper (h1-arithmetic-reply :signed-countdown-down-helper :helper lib
                                               (list "COUNT-ABS-DOWN" down-step
                                                     (list zip-call (proof-neg pos-term)) t)
                                               replies))
             (lib (cdr down-helper))
             (up-helper (h1-arithmetic-reply :signed-countdown-up-helper :helper lib
                                             (list "COUNT-ABS-UP" up-step (list zip-call pos-term) t)
                                             replies)))
          (cdr up-helper))))))

(defund h1-arithmetic-signed-countdowns (lib i replies)
  (h1-arithmetic-with-replies ((lib (h1-arithmetic-signed-countdown-lemmas lib replies)))
    (let ((proof (library-library-proof lib))
          (measure (list *library-count* (list *h1-arithmetic-abs* i)))
          (bindings (list (list *library-x* i))))
      (proof-with-checked-results
          ((down (proof-proof-fact proof (proof-sym "H1-COUNT-ABS-DOWN" "ACL2") bindings))
           (up (proof-proof-fact proof (proof-sym "H1-COUNT-ABS-UP" "ACL2") bindings)))
        (let ((cases (list (list (list (list i (library-plus i *proof-neg-one*))) down)
                           (list (list (list i (library-plus i *proof-one*))) up))))
          (cons (list measure cases) lib))))))

(defund h1-arithmetic-multiplicative-types (lib replies)
  (let ((proof (library-library-proof lib)))
    (h1-arithmetic-with-replies
        ((axiom (library-library-axiom lib "CLOSURE" (list *library-x* *library-y*)))
         (conjuncts (h1-arithmetic-proof-conjunct proof axiom))
         (conjuncts (h1-arithmetic-proof-conjunct proof (cadr conjuncts)))
         (numeric-product (car conjuncts))
         (conjuncts (h1-arithmetic-proof-conjunct proof (cadr conjuncts)))
         (numeric-inverse (cadr conjuncts))
         (added-product (h1-arithmetic-reply :multiplicative-types-product :rules-add lib
                                             (list numeric-product t t) replies))
         (added-inverse (h1-arithmetic-reply :multiplicative-types-inverse :rules-add lib
                                             (list numeric-inverse t t) replies))
         (rational-product (proof-proof-fact proof "rationalp-binary-*" nil))
         (added-rational-product
          (h1-arithmetic-reply :multiplicative-types-rational-product :rules-add-formula lib
                               (list rational-product t t) replies))
         (rational-inverse (proof-proof-fact proof "rationalp-unary-/" nil))
         (added-rational-inverse
          (h1-arithmetic-reply :multiplicative-types-rational-inverse :rules-add-formula lib
                               (list rational-inverse t t) replies)))
      lib)))

(defund h1-arithmetic-multiplication-by-zero (lib replies)
  (let* ((proof (library-library-proof lib))
         (zero *proof-zero*)
         (x *library-x*)
         (product (list *proof-times* x zero)))
    (h1-arithmetic-with-replies
        ((double (library-library-axiom lib "DISTRIBUTIVITY" (list x zero zero)))
         (computed (proof-proof-compute proof (library-plus zero zero) 0))
         (double (proof-proof-rewrite proof double computed '(1 1 2)))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list product)))
         (cancel (proof-proof-rewrite proof inverse double '(1 1 1)))
         (right (library-library-axiom lib "ASSOCIATIVITY-OF-+"
                                        (list product product (library-minus product))))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list product)))
         (right (proof-proof-rewrite proof right inverse '(1 2 2)))
         (one-zero (library-library-axiom lib "UNICITY-OF-0" (list product)))
         (numeric (h1-arithmetic-reply :multiplication-by-zero-numeric :solve lib
                                       (list (list *library-numberp* product) nil 160) replies))
         (fixed (h1-arithmetic-proof-simplify proof (list *h1-arithmetic-fix* product)
                                              (list numeric) (list *h1-arithmetic-fix*)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list product zero)))
         (right (proof-proof-chain proof right (list commute one-zero fixed)))
         (reversed (h1-arithmetic-proof-symmetric proof right)))
      (proof-proof-chain proof reversed (list cancel)))))

(defun h1-arithmetic-reciprocal-nonzero (lib inverse zero nx recip replies)
  (let* ((proof (library-library-proof lib))
         (recip-zero (proof-eq recip *proof-zero*)))
    (h1-arithmetic-with-replies
        ((assumed (h1-arithmetic-proof-assume proof recip-zero t))
         (bad (proof-proof-rewrite proof inverse assumed '(1 1 2)))
         (bad (proof-proof-rewrite proof bad zero '(1 1)))
         (computed (proof-proof-compute proof (proof-eq *proof-zero* *proof-one*) *proof-nil*))
         (bad (proof-proof-rewrite proof bad computed '(1)))
         (bad (proof-proof-tidy proof bad))
         (recip-nonzero (proof-proof-front proof bad (proof-neg recip-zero)))
         (helper (h1-arithmetic-reply :zero-product-reciprocal :helper lib
                                     (list "NONZERO-RECIPROCAL" recip-nonzero
                                           (list (proof-neg nx)
                                                 (proof-eq *library-x* *proof-zero*)) t)
                                     replies)))
      (cdr helper))))

(defun h1-arithmetic-nonzero-product (lib inverse zero nx ny recip replies)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (product (list *proof-times* x y))
         (product-zero (proof-eq product *proof-zero*))
         (y-zero (proof-eq y *proof-zero*)))
    (h1-arithmetic-with-replies
        ((associativity (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list recip x y)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list recip x)))
         (left (proof-proof-rewrite proof associativity commute '(1 1 1)))
         (left (proof-proof-rewrite proof left inverse '(1 1 1)))
         (product-zero-step (h1-arithmetic-proof-assume proof product-zero t))
         (left (proof-proof-rewrite proof left product-zero-step '(1 2 2)))
         (at-zero (proof-proof-instantiate proof zero (list (list x recip))))
         (left (proof-proof-chain proof left (list at-zero)))
         (unit (library-library-axiom lib "UNICITY-OF-1" (list y)))
         (assumed (h1-arithmetic-proof-assume proof ny t))
         (fixed (h1-arithmetic-proof-simplify proof (list *h1-arithmetic-fix* y)
                                              (list assumed) (list *h1-arithmetic-fix*)))
         (unit (proof-proof-chain proof unit (list fixed)))
         (rewritten (proof-proof-rewrite proof left unit '(1 1)))
         (equals-zero (proof-proof-tidy proof rewritten))
         (not-zero (h1-arithmetic-proof-assume proof y-zero nil))
         (contradiction (proof-proof-cut proof equals-zero not-zero))
         (step (proof-proof-front proof contradiction (proof-neg product-zero)))
         (helper (h1-arithmetic-reply :zero-product-nonzero :helper lib
                                     (list "NONZERO-PRODUCT" step
                                           (list (proof-neg nx) (proof-neg ny)
                                                 (proof-eq x *proof-zero*) y-zero) t)
                                     replies)))
      (cdr helper))))

(defund h1-arithmetic-zero-product-rules (lib replies)
  (h1-arithmetic-with-replies
      ((zero (h1-arithmetic-multiplication-by-zero lib replies))
       (helper (h1-arithmetic-reply :zero-product-zero :helper lib
                                   (list "MULTIPLY-BY-ZERO" zero nil t) replies))
       (zero (car helper))
       (lib (cdr helper)))
    (let* ((proof (library-library-proof lib))
           (x *library-x*)
           (nx (list *library-numberp* x))
           (ny (list *library-numberp* *library-y*))
           (x-zero (proof-eq x *proof-zero*))
           (recip (list *h1-arithmetic-reciprocal* x)))
      (h1-arithmetic-with-replies
          ((inverse (library-library-axiom lib "INVERSE-OF-*" (list x)))
           (inverse-literal (proof-step-first inverse))
           (inverse-test (proof-term-at inverse-literal 1))
           (nx-step (h1-arithmetic-proof-assume proof nx t))
           (not-zero (h1-arithmetic-proof-assume proof x-zero nil))
           (known (h1-arithmetic-conjunction lib inverse-test (list nx-step not-zero)))
           (inverse (h1-arithmetic-proof-modus-ponens proof inverse known))
           (lib (h1-arithmetic-reciprocal-nonzero lib inverse zero nx recip replies)))
        (h1-arithmetic-nonzero-product lib inverse zero nx ny recip replies)))))

(defun h1-arithmetic-nonzero-exponentiation (lib replies)
  (h1-arithmetic-with-replies
      ((lib (h1-arithmetic-zero-product-rules lib replies))
       (number-term (list *library-numberp*
                          (list *h1-arithmetic-expt* (proof-sym "R" "ACL2")
                                (proof-sym "I" "ACL2"))))
       (number-step (h1-arithmetic-reply :exponentiation-number :solve lib
                                         (list number-term (list *h1-arithmetic-expt*) 160)
                                         replies))
       (helper (h1-arithmetic-reply :exponentiation-helper :helper lib
                                   (list "NUMBERP-EXPT" number-step nil t) replies)))
    (cdr helper)))

(defund h1-arithmetic-exponentiation (lib formula nonzero replies)
  (h1-arithmetic-with-replies
      ((lib (h1-arithmetic-multiplicative-types lib replies))
       (lib (if nonzero (h1-arithmetic-nonzero-exponentiation lib replies) lib))
       (countdowns (h1-arithmetic-signed-countdowns lib (proof-sym "I" "ACL2") replies))
       (lib (cdr countdowns))
       (measure (caar countdowns))
       (cases (cadar countdowns))
       (step (h1-arithmetic-reply :exponentiation-induction :by-induction lib
                                  (list formula measure cases
                                        (list *h1-arithmetic-expt* *h1-arithmetic-fix*)
                                        nil 160 t nil nil)
                                  replies)))
    (cons step lib)))

(defund h1-arithmetic-query (recipe lib args replies)
  (case recipe
    (:natural-successor (h1-arithmetic-natural-successor lib replies))
    (:character-at-index (h1-arithmetic-character-at-index lib (car args) replies))
    (:nonpositive-absolute-value (h1-arithmetic-nonpositive-absolute-value lib replies))
    (:signed-countdown-lemmas (h1-arithmetic-signed-countdown-lemmas lib replies))
    (:signed-countdowns (h1-arithmetic-signed-countdowns lib (car args) replies))
    (:multiplicative-types (h1-arithmetic-multiplicative-types lib replies))
    (:multiplication-by-zero (h1-arithmetic-multiplication-by-zero lib replies))
    (:zero-product-rules (h1-arithmetic-zero-product-rules lib replies))
    (:exponentiation (h1-arithmetic-exponentiation lib (car args) (cadr args) replies))
    (otherwise '(:failure "failure" ""))))
