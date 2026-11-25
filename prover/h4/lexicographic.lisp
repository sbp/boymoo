(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-lexicographic-list-ordinal* (proof-sym "H4-LEX-LIST-ORDINAL" "ACL2"))
(defconst *h4-lexicographic-lex-ordinal* (proof-sym "H4-LEX-ORDINAL" "ACL2"))
(defconst *h4-lexicographic-lex-fix* (proof-sym "LEX-FIX" "ACL2"))
(defconst *h4-lexicographic-nat-list* (proof-sym "NAT-LISTP" "ACL2"))
(defconst *h4-lexicographic-nfix-list* (proof-sym "NFIX-LIST" "ACL2"))
(defconst *h4-lexicographic-acl2-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *h4-lexicographic-first-expt* (proof-sym "O-FIRST-EXPT" "ACL2"))
(defconst *h4-lexicographic-first-coeff* (proof-sym "O-FIRST-COEFF" "ACL2"))
(defconst *h4-lexicographic-rest-ord* (proof-sym "O-RST" "ACL2"))
(defconst *h4-lexicographic-posp* (proof-sym "POSP" "ACL2"))
(defconst *h4-lexicographic-d-less* (proof-sym "D<" "ACL2"))
(defconst *h4-lexicographic-l-less* (proof-sym "L<" "ACL2"))
(defconst *h4-lexicographic-num-equal* (proof-cl "="))
(defconst *h4-lexicographic-selector-definitions*
  (list *library-o-finp* *h4-lexicographic-first-expt* *h4-lexicographic-first-coeff*
        *h4-lexicographic-rest-ord* *h4-terms-atom* *proof-not* *h4-terms-eq*
        *h4-terms-eql* *h4-lexicographic-num-equal*))

(defun h4-lexicographic-natural-list-type (value)
  (proof-ite (list *proof-consp* value) (list *h4-lexicographic-nat-list* value)
             (list *library-natp* value)))

(defun h4-lexicographic-distinct (p strict integers)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first strict))
         (arguments (proof-list-of-length literal 3))
         (same (proof-proof-assume proof (proof-eq (cadr arguments) (caddr arguments)) t))
         (impossible (proof-proof-rewrite proof strict same '(1 1)))
         (type (library-library-type-of p (caddr arguments) integers))
         (irreflexive (library-library-cite p "WEAK-REFLEXIVE"
                                           (list (caddr arguments)) (list type)))
         (cut (proof-proof-cut proof impossible irreflexive))
         (equality (proof-step-first same)))
      (proof-proof-front proof cut (proof-neg equality)))))

(defun h4-lexicographic-reverse-distinct (p inequality)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first inequality))
         (negated (proof-term-at literal 1))
         (arguments (proof-list-of-length negated 3))
         (reverse (proof-proof-assume proof (proof-eq (caddr arguments) (cadr arguments)) t))
         (symmetric (proof-proof-symmetric proof reverse))
         (cut (proof-proof-cut proof symmetric inequality))
         (equality (proof-step-first reverse)))
      (proof-proof-front proof cut (proof-neg equality)))))

(defun h4-lexicographic-constructor (p redex)
  (if (integerp redex)
      '(:failure "failure" "")
    (and (equal (len redex) 2)
         (member-equal (car redex) (list *library-car* *library-cdr*))
         (proof-is-call (cadr redex) *proof-cons*)
         (library-library-axiom
          p (if (equal (car redex) *library-car*) "CAR-CONS" "CDR-CONS")
          (cdadr redex)))))

(defun h4-lexicographic-cons-fact (p construction)
  (if (proof-is-call construction *proof-cons*)
      (proof-proof-fact (library-library-proof p) "consp-cons"
                        (seq-zip (list *library-x* *library-y*) (cdr construction)))
    '(:failure "failure" "")))

(defun h4-lexicographic-select-definition (p call evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (literal (proof-step-first opened))
         (conditional (proof-term-at literal 2))
         (selected (proof-proof-select proof conditional evidence)))
      (proof-proof-chain proof opened (list selected)))))

(defun h4-lexicographic-define-list-ordinal (p)
  (let* ((proof (library-library-proof p))
         (name *h4-lexicographic-list-ordinal*)
         (x *library-x*)
         (formals (list x))
         (count (list *library-count* x))
         (tail (list *library-cdr* x))
         (coefficient (library-plus *proof-one* (list *library-nfix* (list *library-car* x))))
         (body (proof-ite (list *proof-consp* x)
                          (list *proof-cons* (list *proof-cons* (list *library-len* x) coefficient)
                                (list name tail))
                          *proof-zero*)))
    (proof-with-checked-results
        ((declaration (proof-line "define" (list (list *proof-if*) (list name formals body))))
         (descent (library-library-builtin p 3 x))
         (literal (proof-step-first descent))
         (clause (append (cdr (proof-step-clause descent)) (list literal)))
         (ordinal (library-library-builtin p 1 x))
         (decrease (proof-proof-subsume proof descent clause))
         (measure (proof-proof-entry "measure" name (list name count) (list ordinal decrease))))
      (let* ((entry (list "define" name (caddr measure)
                          (string-append declaration (cadddr measure))))
             (p (library-library-with-entries p (append (library-library-entries p) (list entry)))))
        (library-library-with-proof p (proof-proof-add-definition proof name formals body))))))

(defun h4-lexicographic-embedding-p (embedding)
  (nth 1 embedding))

(defun h4-lexicographic-embedding-leading (embedding)
  (nth 2 embedding))

(defun h4-lexicographic-embedding-list-ordinal (embedding)
  (nth 3 embedding))

(defun h4-lexicographic-embedding-ordinal (embedding)
  (nth 4 embedding))

(defun h4-lexicographic-embedding-fix-type (embedding)
  (nth 5 embedding))

(defun h4-lexicographic-embedding-list-order (embedding)
  (nth 6 embedding))

(defun h4-lexicographic-embedding-order (embedding)
  (nth 7 embedding))

(defun h4-lexicographic-embedding-with-p (embedding p)
  (update-nth 1 p embedding))

(defun h4-lexicographic-embedding-local-lemma (embedding label step)
  (proof-with-checked-results
      ((result (h4-tactics-tactics-local-lemma (h4-lexicographic-embedding-p embedding) label step)))
    (cons (car result) (h4-lexicographic-embedding-with-p embedding (cdr result)))))

(defun h4-lexicographic-embedding-fact (embedding name x y)
  (proof-proof-fact (library-library-proof (h4-lexicographic-embedding-p embedding))
                    name (if (eq y :none)
                             (list (list *library-x* x))
                           (list (list *library-x* x) (list *library-y* y)))))

(defun h4-lexicographic-embedding-encoding (embedding evidence head)
  (proof-with-checked-results
      ((literal (proof-step-first evidence))
       (argument (proof-term-at literal 1))
       (term (if (proof-is-call literal *proof-consp*) argument (proof-term-at argument 1))))
    (h4-lexicographic-select-definition
     (h4-lexicographic-embedding-p embedding) (list head term) evidence)))

(defun h4-lexicographic-embedding-cons-encodings-equations (embedding shapes)
  (if (endp shapes)
      nil
    (proof-with-checked-results
        ((equation (h4-lexicographic-embedding-encoding
                    embedding (car shapes) *h4-lexicographic-list-ordinal*))
         (rest (h4-lexicographic-embedding-cons-encodings-equations embedding (cdr shapes))))
      (cons equation rest))))

(defun h4-lexicographic-embedding-cons-encodings-conditions (p encodings)
  (if (endp encodings)
      nil
    (proof-with-checked-results
        ((literal (proof-step-first (car encodings)))
         (pair (proof-term-at literal 2))
         (head (proof-term-at pair 1))
         (pair-fact (h4-lexicographic-cons-fact p pair))
         (head-fact (h4-lexicographic-cons-fact p head))
         (rest (h4-lexicographic-embedding-cons-encodings-conditions p (cdr encodings))))
      (list* pair-fact head-fact rest))))

(defun h4-lexicographic-embedding-cons-encodings (embedding shapes)
  (proof-with-checked-results
      ((encodings (h4-lexicographic-embedding-cons-encodings-equations embedding shapes))
       (conditions (h4-lexicographic-embedding-cons-encodings-conditions
                    (h4-lexicographic-embedding-p embedding) encodings)))
    (list encodings conditions)))

(defun h4-lexicographic-constructor-reply (p term evidence expand rewrites establish replies)
  (let* ((provider (cons :h4-tactics-provider replies))
         (result (if establish
                     (h4-tactics-tactics-establish p term evidence expand rewrites provider)
                   (h4-tactics-tactics-normalize p term evidence expand rewrites provider))))
    (if (h4-tactics-request-p result)
        (let* ((redex (h4-tactics-request-term result))
               (reply (h4-lexicographic-constructor p redex)))
          (if (failure-p reply)
              (cons :done reply)
            (cons :pending (table-put replies redex reply))))
      (cons :done result))))

(defun h4-lexicographic-with-constructor (n p term evidence expand rewrites establish pending)
  (declare (xargs :measure (nfix n)))
  (cond ((eq (car pending) :done) (cdr pending))
        ((zp n) '(:failure "fuel" "h4-lexicographic-with-constructor"))
        (t (h4-lexicographic-with-constructor
            (1- n) p term evidence expand rewrites establish
            (h4-lexicographic-constructor-reply p term evidence expand
                                               rewrites establish (cdr pending))))))

(defun h4-lexicographic-embedding-normalize-selectors (embedding term evidence rewrites)
  (h4-lexicographic-with-constructor
   1000000 (h4-lexicographic-embedding-p embedding) term evidence
   *h4-lexicographic-selector-definitions* rewrites nil nil))

(defun h4-lexicographic-embedding-ordinal-proposition (embedding formula evidence rewrites)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof formula))
         (literal (proof-step-first opened))
         (body (proof-term-at literal 2))
         (normalized (h4-lexicographic-embedding-normalize-selectors embedding body evidence rewrites))
         (equality (proof-proof-chain proof opened (list normalized)))
         (literal (proof-step-first equality))
         (value (proof-term-at literal 2))
         (established (h4-tactics-tactics-establish p value evidence nil nil nil)))
      (proof-proof-transport proof established equality))))

(defun h4-lexicographic-embedding-leading-exponent-cons (shape embedding goal)
  (proof-with-checked-results
      ((encodings (h4-lexicographic-embedding-cons-encodings embedding (list shape)))
       (left (proof-term-at goal 1)))
    (h4-lexicographic-embedding-normalize-selectors embedding left
                                                    (cadr encodings) (car encodings))))

(defun h4-lexicographic-embedding-leading-exponent-atom (shape embedding goal length)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((left (proof-term-at goal 1))
         (encoding (h4-lexicographic-embedding-encoding embedding shape *h4-lexicographic-list-ordinal*))
         (value (h4-lexicographic-embedding-normalize-selectors embedding left nil (list encoding)))
         (length-equality (h4-lexicographic-select-definition p length shape))
         (reversed (proof-proof-symmetric proof length-equality)))
      (proof-proof-chain proof value (list reversed)))))

(defun h4-lexicographic-embedding-leading-exponent (embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (argument (list *h4-lexicographic-list-ordinal* *library-x*))
         (length (list *library-len* *library-x*))
         (goal (proof-eq (list *h4-lexicographic-first-expt* argument) length))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((yes-test (proof-proof-assume proof test t))
         (yes (h4-lexicographic-embedding-leading-exponent-cons yes-test embedding goal))
         (no-test (proof-proof-assume proof test nil))
         (no (h4-lexicographic-embedding-leading-exponent-atom no-test embedding goal length))
         (cases (h4-tactics-tactics-case-of p goal test yes no)))
      (h4-lexicographic-embedding-local-lemma embedding "LEX-LEADING-EXPONENT" cases))))

(defun h4-lexicographic-embedding-positive-successor (embedding number)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((head (proof-term-at number 0))
         (natural (if (equal head *library-nfix*)
                      (library-library-cite p "NFIX-NATURAL" (cdr number) nil)
                    (library-library-natural p number)))
         (fix (library-library-cite p "NATURAL-INTEGER" (list number) (list natural)))
         (bound (library-library-cite p "NATURAL-NONNEGATIVE" (list number) (list natural)))
         (positive (library-library-cite p "POSITIVE-ONE-PLUS" (list number) (list fix bound))))
      (list positive fix))))

(defun h4-lexicographic-embedding-length-positive (embedding cons-step)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((literal (proof-step-first cons-step))
         (x (proof-term-at literal 1))
         (successor (h4-lexicographic-embedding-positive-successor
                     embedding (list *library-len* (list *library-cdr* x))))
         (equation (h4-lexicographic-select-definition p (list *library-len* x) cons-step)))
      (library-library-transport-argument p (car successor) equation 2))))

(defun h4-lexicographic-embedding-ordinal-on-lists-cons (shape embedding formula tail substitution)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (exponent (list *library-len* x)))
    (proof-with-checked-results
        ((encodings (h4-lexicographic-embedding-cons-encodings embedding (list shape)))
         (exponent-natural (library-library-natural p exponent))
         (exponent-is-ordinal (library-library-cite p "NATURAL-ORDINAL"
                                                    (list exponent) (list exponent-natural)))
         (length-positive (h4-lexicographic-embedding-length-positive embedding shape))
         (exponent-nonzero (h4-lexicographic-distinct p length-positive nil))
         (successor (h4-lexicographic-embedding-positive-successor
                     embedding (list *library-nfix* (list *library-car* x))))
         (comp (proof-step-first (car successor)))
         (coeff (proof-term-at comp 2))
         (one-type (library-library-type-of p *proof-one* nil))
         (coeff-int (library-library-cite p "INTEGER-SUM" (cdr coeff)
                                          (list one-type (cadr successor))))
         (coefficient-positive
          (h4-tactics-tactics-establish p (list *h4-lexicographic-posp* coeff)
                                        (list coeff-int (car successor))
                                        (list *h4-lexicographic-posp*) nil nil))
         (builtin (library-library-builtin p 3 x))
         (decrease (proof-proof-discharge proof builtin shape))
         (condition (proof-step-first decrease))
         (child (proof-subst formula (proof-bindings-table substitution nil)))
         (assumed (proof-proof-assume proof (proof-ite condition child *proof-true*) t))
         (rest-is-ordinal (proof-proof-prove-if proof assumed decrease))
         (shorter-length (library-library-cite p "LEN-CDR-LESS" (list x) (list shape)))
         (comparison (library-library-ordinal-comparison p (list *library-len* tail) exponent))
         (shorter-exponent (proof-proof-transport proof shorter-length comparison))
         (leading (h4-lexicographic-embedding-fact
                   embedding (h4-lexicographic-embedding-leading embedding) tail :none)))
      (h4-lexicographic-embedding-ordinal-proposition
       embedding formula
       (append (cadr encodings) (list exponent-is-ordinal exponent-nonzero coefficient-positive
                                      rest-is-ordinal shorter-exponent))
       (append (car encodings) (list leading))))))

(defun h4-lexicographic-embedding-ordinal-on-lists-atom (shape embedding formula)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((natural (library-library-natural p *proof-zero*))
         (encoding (h4-lexicographic-embedding-encoding embedding shape *h4-lexicographic-list-ordinal*)))
      (h4-lexicographic-embedding-ordinal-proposition embedding formula (list natural) (list encoding)))))

(defun h4-lexicographic-embedding-ordinal-on-lists (embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (formula (list *proof-ordinalp* (list *h4-lexicographic-list-ordinal* x)))
         (tail (list *library-cdr* x))
         (count (list *library-count* x))
         (substitution (list (list x tail)))
         (test (list *proof-consp* x)))
    (proof-with-checked-results
        ((yes-test (proof-proof-assume proof test t))
         (yes (h4-lexicographic-embedding-ordinal-on-lists-cons yes-test embedding formula tail substitution))
         (no-test (proof-proof-assume proof test nil))
         (no (h4-lexicographic-embedding-ordinal-on-lists-atom no-test embedding formula))
         (cases (h4-tactics-tactics-case-of p formula test yes no))
         (ordinal (library-library-builtin p 1 x))
         (step (proof-proof-induct proof ordinal cases formula count (list substitution))))
      (h4-lexicographic-embedding-local-lemma embedding "LEX-LIST-IS-ORDINAL" step))))

(defun h4-lexicographic-embedding-ordinal-on-values-branch (shape step embedding)
  (proof-with-checked-results
      ((encoding (h4-lexicographic-embedding-encoding embedding shape *h4-lexicographic-lex-ordinal*)))
    (library-library-transport-argument (h4-lexicographic-embedding-p embedding) step encoding 1)))

(defun h4-lexicographic-embedding-ordinal-on-values (embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (goal (list *proof-ordinalp* (list *h4-lexicographic-lex-ordinal* x)))
         (test (list *proof-consp* x)))
    (proof-with-checked-results
        ((yes-test (proof-proof-assume proof test t))
         (ordinal (h4-lexicographic-embedding-fact
                   embedding (h4-lexicographic-embedding-list-ordinal embedding) x :none))
         (yes (h4-lexicographic-embedding-ordinal-on-values-branch yes-test ordinal embedding))
         (no-test (proof-proof-assume proof test nil))
         (nfix-ordinal (library-library-cite p "NFIX-ORDINAL" (list x) nil))
         (no (h4-lexicographic-embedding-ordinal-on-values-branch no-test nfix-ordinal embedding))
         (step (h4-tactics-tactics-case-of p goal test yes no)))
      (h4-lexicographic-embedding-local-lemma embedding "LEX-VALUE-IS-ORDINAL" step))))

(defun h4-lexicographic-embedding-acl2-nfix (embedding x)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((desired (proof-proof-unfold proof (list *h4-lexicographic-acl2-nfix* x)))
         (own (h4-tactics-tactics-normalize p (list *library-nfix* x) nil
                                            (list *library-nfix* *library-natp*) nil nil))
         (reversed (proof-proof-symmetric proof own)))
      (proof-proof-chain proof desired (list reversed)))))

(defun h4-lexicographic-embedding-fixed-types-atomic (shape p formula value)
  (proof-with-checked-results ((equation (h4-lexicographic-select-definition p value shape)))
    (h4-tactics-tactics-establish p formula nil
                                   (list *h4-lexicographic-nat-list* *h4-terms-atom* *proof-not* *h4-terms-eq*)
                                   (list equation) nil)))

(defun h4-lexicographic-embedding-fixed-types-pair (shape embedding formula substitution value)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (head (list *library-car* x)))
    (proof-with-checked-results
        ((builtin (library-library-builtin p 3 x))
         (decrease (proof-proof-discharge proof builtin shape))
         (condition (proof-step-first decrease))
         (child (proof-subst formula (proof-bindings-table substitution nil)))
         (assumed (proof-proof-assume proof (proof-ite condition child *proof-true*) t))
         (rest-nat (proof-proof-prove-if proof assumed decrease))
         (head-nfix (library-library-cite p "NFIX-NATURAL" (list head) nil))
         (fixers (h4-lexicographic-embedding-acl2-nfix embedding head))
         (head-nat (library-library-transport-argument p head-nfix fixers 1))
         (equation (h4-lexicographic-select-definition p value shape))
         (literal (proof-step-first equation))
         (output (proof-term-at literal 2))
         (cons-fact (h4-lexicographic-cons-fact p output)))
      (h4-lexicographic-with-constructor
       1000000 p formula (list head-nat rest-nat cons-fact)
       (list *h4-lexicographic-nat-list* *h4-terms-atom* *proof-not* *h4-terms-eq*)
       (list equation) t nil))))

(defun h4-lexicographic-embedding-fixed-types-fixed-atom (shape embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (call (list *h4-lexicographic-lex-fix* x))
         (fixed (list *library-nfix* x)))
    (proof-with-checked-results
        ((selected (h4-lexicographic-select-definition p call shape))
         (fixers (h4-lexicographic-embedding-acl2-nfix embedding x))
         (equation (proof-proof-chain proof selected (list fixers)))
         (integer (library-library-cite p "NFIX-INTEGER" (list x) nil))
         (finite (library-library-cite p "INTEGER-FINITE" (list fixed) (list integer)))
         (finp (proof-proof-unfold proof (list *library-o-finp* fixed)))
         (atom (proof-proof-unfold proof (list *h4-terms-atom* fixed)))
         (atom (proof-proof-chain proof finp (list atom)))
         (not-cons (proof-proof-rewrite proof finite atom '(1)))
         (natural (library-library-cite p "NFIX-NATURAL" (list x) nil)))
      (h4-tactics-tactics-establish p (h4-lexicographic-natural-list-type call)
                                    (list not-cons natural) nil (list equation) nil))))

(defun h4-lexicographic-embedding-fixed-types-fixed-pair (shape embedding value fixed-list-type)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (x *library-x*)
         (call (list *h4-lexicographic-lex-fix* x)))
    (proof-with-checked-results
        ((equation (h4-lexicographic-select-definition p call shape))
         (cons-step (h4-terms-cons-evidence p shape))
         (own (h4-lexicographic-select-definition p value cons-step))
         (literal (proof-step-first own))
         (output (proof-term-at literal 2))
         (cons-fact (h4-lexicographic-cons-fact p output))
         (is-cons (library-library-transport-argument p cons-fact own 1))
         (list-type (h4-lexicographic-embedding-fact embedding fixed-list-type x :none)))
      (h4-tactics-tactics-establish p (h4-lexicographic-natural-list-type call)
                                    (list is-cons list-type) nil (list equation) nil))))

(defun h4-lexicographic-embedding-fixed-types (embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (value (list *h4-lexicographic-nfix-list* x))
         (formula (list *h4-lexicographic-nat-list* value))
         (cons-test (list *proof-consp* x))
         (tail (list *library-cdr* x))
         (substitution (list (list x tail))))
    (proof-with-checked-results
        ((yes-test (proof-proof-assume proof cons-test t))
         (yes (h4-lexicographic-embedding-fixed-types-pair yes-test embedding formula substitution value))
         (no-test (proof-proof-assume proof cons-test nil))
         (no (h4-lexicographic-embedding-fixed-types-atomic no-test p formula value))
         (cases (h4-tactics-tactics-case-of p formula cons-test yes no))
         (ordinal (library-library-builtin p 1 x))
         (induction (proof-proof-induct proof ordinal cases formula (list *library-count* x)
                                        (list substitution)))
         (fixed-list (h4-lexicographic-embedding-local-lemma embedding "NFIX-LIST-NATURAL-LIST" induction)))
      (let* ((embedding (cdr fixed-list))
             (p (h4-lexicographic-embedding-p embedding))
             (proof (library-library-proof p))
             (goal (h4-lexicographic-natural-list-type (list *h4-lexicographic-lex-fix* x)))
             (atom-test (list *h4-terms-atom* x)))
        (proof-with-checked-results
            ((yes-test (proof-proof-assume proof atom-test t))
             (yes (h4-lexicographic-embedding-fixed-types-fixed-atom yes-test embedding))
             (no-test (proof-proof-assume proof atom-test nil))
             (no (h4-lexicographic-embedding-fixed-types-fixed-pair
                  no-test embedding value (car fixed-list)))
             (result (h4-tactics-tactics-case-of p goal atom-test yes no)))
          (h4-lexicographic-embedding-local-lemma embedding "LEX-FIX-TYPE" result))))))

(defun h4-lexicographic-embedding-length-cancellation-open-one (p same shape index)
  (proof-with-checked-results
      ((literal (proof-step-first shape))
       (arg (proof-term-at literal 1))
       (selected (h4-lexicographic-select-definition p (list *library-len* arg) shape)))
    (proof-proof-rewrite (library-library-proof p) same selected (list 1 index))))

(defun h4-lexicographic-embedding-length-cancellation-open (p same shapes index)
  (declare (xargs :measure (acl2-count shapes)))
  (if (or (failure-p same) (endp shapes))
      same
    (h4-lexicographic-embedding-length-cancellation-open
     p (h4-lexicographic-embedding-length-cancellation-open-one p same (car shapes) index)
     (cdr shapes) (1+ index))))

(defun h4-lexicographic-embedding-length-cancellation-adjust-one (p step tail index)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (argument (proof-term-at literal index))
       (equality (library-library-linear-equal p argument tail nil)))
    (proof-proof-rewrite (library-library-proof p) step equality (list 1 index))))

(defun h4-lexicographic-embedding-length-cancellation-adjust (p step tails index)
  (declare (xargs :measure (acl2-count tails)))
  (if (or (failure-p step) (endp tails))
      step
    (h4-lexicographic-embedding-length-cancellation-adjust
     p (h4-lexicographic-embedding-length-cancellation-adjust-one p step (car tails) index)
     (cdr tails) (1+ index))))

(defun h4-lexicographic-embedding-length-cancellation (embedding same x-cons y-cons)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (tails (list (list *library-len* (list *library-cdr* *library-x*))
                      (list *library-len* (list *library-cdr* *library-y*)))))
    (proof-with-checked-results
        ((same (h4-lexicographic-embedding-length-cancellation-open p same (list x-cons y-cons) 1))
         (literal (proof-step-first same))
         (arguments (proof-list-of-length literal 3))
         (identity (proof-proof-reflexive proof (library-plus *proof-neg-one* (cadr arguments))))
         (step (proof-proof-rewrite proof identity same '(1 2 2)))
         (step (h4-lexicographic-embedding-length-cancellation-adjust p step tails 1)))
      (proof-proof-tidy proof step))))

(defun h4-lexicographic-embedding-coefficient-order-integer (p natural)
  (proof-with-checked-results
      ((literal (proof-step-first natural))
       (argument (proof-term-at literal 1)))
    (library-library-cite p "NATURAL-INTEGER" (list argument) (list natural))))

(defun h4-lexicographic-embedding-coefficient-order-adjust-one (p result natural index)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first natural))
         (argument (proof-term-at literal 1))
         (commuted (library-library-axiom p "COMMUTATIVITY-OF-+" (list argument *proof-one*)))
         (result (proof-proof-rewrite proof result commuted (list 1 index)))
         (equation (h4-tactics-tactics-normalize
                    p (library-plus *proof-one* (list *library-nfix* argument))
                    (list natural) (list *library-nfix*) nil nil)))
      (library-library-transport-argument p result equation index))))

(defun h4-lexicographic-embedding-coefficient-order-adjust (p result naturals index)
  (declare (xargs :measure (acl2-count naturals)))
  (if (or (failure-p result) (endp naturals))
      result
    (h4-lexicographic-embedding-coefficient-order-adjust
     p (h4-lexicographic-embedding-coefficient-order-adjust-one p result (car naturals) index)
     (cdr naturals) (1+ index))))

(defun h4-lexicographic-embedding-coefficient-order (embedding strict x-nat y-nat)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((literal (proof-step-first strict))
         (arguments (if (integerp literal)
                        '(:failure "failure" "")
                      (proof-list-of-length (cdr literal) 2)))
         (x-int (h4-lexicographic-embedding-coefficient-order-integer p x-nat))
         (y-int (h4-lexicographic-embedding-coefficient-order-integer p y-nat))
         (one-type (library-library-type-of p *proof-one* nil))
         (result (library-library-cite p "LESS-SHIFT"
                                       (list (car arguments) (cadr arguments) *proof-one*)
                                       (list x-int y-int one-type strict))))
      (h4-lexicographic-embedding-coefficient-order-adjust p result (list x-nat y-nat) 1))))

(defun h4-lexicographic-embedding-order-on-lists-impossible (shapes p lex-smaller goal)
  (proof-with-checked-results
      ((contradiction (h4-terms-simplify-evidence p lex-smaller shapes (list *h4-lexicographic-d-less*))))
    (h4-terms-if-false-impossible p goal contradiction)))

(defun h4-lexicographic-embedding-order-on-lists-pair-smaller-head
  (strict embedding x-nat y-nat goal conditions encodings)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((smaller (h4-lexicographic-embedding-coefficient-order embedding strict x-nat y-nat))
         (type (library-library-cite p "NFIX-INTEGER" (list (list *library-car* *library-y*)) nil))
         (differ (h4-lexicographic-distinct p smaller (list type))))
      (h4-lexicographic-embedding-ordinal-proposition
       embedding goal (append conditions (list differ smaller)) encodings))))

(defun h4-lexicographic-embedding-order-on-lists-pair-equal-head
  (nonstrict embedding a b goal conditions encodings lex-smaller
             same-length x-tail y-tail tail-formula)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((reduced (h4-terms-simplify-evidence p lex-smaller (list a b nonstrict)
                                              (list *h4-lexicographic-d-less* *h4-lexicographic-num-equal*)))
         (parts (h4-tactics-tactics-conjunct p reduced))
         (coefficient (library-plus *proof-one* (list *library-nfix* (list *library-car* *library-x*))))
         (identity (proof-proof-reflexive proof coefficient))
         (coeff-equal (proof-proof-rewrite proof identity (car parts) '(1 2 2 1)))
         (equal-tails (h4-lexicographic-embedding-length-cancellation embedding same-length a b))
         (builtin (library-library-builtin p 3 *library-x*))
         (descent (proof-proof-discharge proof builtin a))
         (condition (proof-step-first descent))
         (hypothesis (proof-proof-assume proof (proof-ite condition tail-formula *proof-true*) t))
         (induction (proof-proof-prove-if proof hypothesis descent))
         (tail-guard (proof-term-at tail-formula 1))
         (tail-data (h4-tactics-tactics-establish p tail-guard
                                                 (list x-tail y-tail equal-tails (cadr parts)) nil nil nil))
         (tail-order (h4-tactics-tactics-modus-ponens p induction tail-data)))
      (h4-lexicographic-embedding-ordinal-proposition
       embedding goal (append conditions (list coeff-equal tail-order)) encodings))))

(defun h4-lexicographic-embedding-order-on-lists-pair
  (a b embedding first second same-length lex-smaller goal tail-formula compare-heads)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (expand (list *h4-lexicographic-nat-list* *h4-terms-atom* *proof-not*)))
    (proof-with-checked-results
        ((x-reduced (h4-terms-simplify-evidence p first (list a) expand))
         (x-parts (h4-tactics-tactics-conjunct p x-reduced))
         (y-reduced (h4-terms-simplify-evidence p second (list b) expand))
         (y-parts (h4-tactics-tactics-conjunct p y-reduced))
         (data (h4-lexicographic-embedding-cons-encodings embedding (list a b)))
         (conditions (append (cadr data) (list same-length)))
         (yes-test (proof-proof-assume proof compare-heads t))
         (yes (h4-lexicographic-embedding-order-on-lists-pair-smaller-head
               yes-test embedding (car x-parts) (car y-parts) goal conditions (car data)))
         (no-test (proof-proof-assume proof compare-heads nil))
         (no (h4-lexicographic-embedding-order-on-lists-pair-equal-head
              no-test embedding a b goal conditions (car data) lex-smaller same-length
              (cadr x-parts) (cadr y-parts) tail-formula)))
      (h4-tactics-tactics-case-of p goal compare-heads yes no))))

(defun h4-lexicographic-embedding-order-on-lists-cons
  (a embedding first second same-length lex-smaller goal tail-formula compare-heads y-cons)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((b (proof-proof-assume proof y-cons t))
         (yes (h4-lexicographic-embedding-order-on-lists-pair
               a b embedding first second same-length lex-smaller goal tail-formula compare-heads))
         (b (proof-proof-assume proof y-cons nil))
         (no (h4-lexicographic-embedding-order-on-lists-impossible (list a b) p lex-smaller goal)))
      (h4-tactics-tactics-case-of p goal y-cons yes no))))

(defun h4-lexicographic-embedding-order-on-lists (embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (y *library-y*)
         (lengths (proof-eq (list *library-len* x) (list *library-len* y)))
         (lex (list *h4-lexicographic-d-less* x y))
         (x-cons (list *proof-consp* x))
         (y-cons (list *proof-consp* y))
         (premise (proof-ite (list *h4-lexicographic-nat-list* x)
                             (proof-ite (list *h4-lexicographic-nat-list* y)
                                        (proof-ite lengths lex *proof-false*) *proof-false*)
                             *proof-false*))
         (goal (list *proof-ordinal-less* (list *h4-lexicographic-list-ordinal* x)
                     (list *h4-lexicographic-list-ordinal* y)))
         (formula (list *library-implies* premise goal)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof premise t))
         (parts (h4-tactics-tactics-conjunct p assumed))
         (further (h4-tactics-tactics-conjunct p (cadr parts)))
         (ordering (h4-tactics-tactics-conjunct p (cadr further)))
         (substitution (list (list x (list *library-cdr* x)) (list y (list *library-cdr* y))))
         (tail-formula (proof-subst formula (proof-bindings-table substitution nil)))
         (compare-heads (library-lt (list *library-car* x) (list *library-car* y)))
         (a (proof-proof-assume proof x-cons t))
         (yes (h4-lexicographic-embedding-order-on-lists-cons
               a embedding (car parts) (car further) (car ordering) (cadr ordering)
               goal tail-formula compare-heads y-cons))
         (a (proof-proof-assume proof x-cons nil))
         (no (h4-lexicographic-embedding-order-on-lists-impossible (list a) p (cadr ordering) goal))
         (result (h4-tactics-tactics-case-of p goal x-cons yes no))
         (case-step (h4-tactics-tactics-imply p formula result))
         (ordinal (library-library-builtin p 1 x))
         (proven (proof-proof-induct proof ordinal case-step formula (list *library-count* x)
                                      (list substitution))))
      (h4-lexicographic-embedding-local-lemma embedding "LEX-ORDER-ON-LISTS" proven))))

(defun h4-lexicographic-embedding-order-on-values-list-pair-shorter
  (strict embedding goal conditions wrappers list-rewrites)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first strict))
         (lengths (if (integerp literal)
                      '(:failure "failure" "")
                    (proof-list-of-length (cdr literal) 2)))
         (comparison (library-library-ordinal-comparison p (car lengths) (cadr lengths)))
         (compare-lengths (proof-proof-transport proof strict comparison))
         (distinct (h4-lexicographic-distinct p strict nil)))
      (h4-lexicographic-embedding-ordinal-proposition
       embedding goal (append conditions (list distinct compare-lengths))
       (append wrappers list-rewrites)))))

(defun h4-lexicographic-embedding-order-on-values-list-pair-transport (p step wrappers index)
  (declare (xargs :measure (acl2-count wrappers)))
  (if (or (failure-p step) (endp wrappers))
      step
    (h4-lexicographic-embedding-order-on-values-list-pair-transport
     p (library-library-transport-argument p step (car wrappers) index)
     (cdr wrappers) (1+ index))))

(defun h4-lexicographic-embedding-order-on-values-list-pair-same-length
  (has-not-shrunk embedding smaller x-cons x-nat y-nat wrappers)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((step (h4-terms-simplify-evidence p smaller (list has-not-shrunk)
                                           (list *h4-lexicographic-l-less* *h4-lexicographic-num-equal*)))
         (parts (h4-tactics-tactics-conjunct p step))
         (component-order (h4-terms-simplify-evidence p (cadr parts) (list x-cons)
                                                      (list *h4-terms-atom* *proof-not*)))
         (lemma (h4-lexicographic-embedding-fact
                 embedding (h4-lexicographic-embedding-list-order embedding) *library-x* *library-y*))
         (literal (proof-step-first lemma))
         (guard (proof-term-at literal 1))
         (facts (h4-tactics-tactics-establish p guard (list x-nat y-nat (car parts) component-order)
                                              nil nil nil))
         (step (h4-tactics-tactics-modus-ponens p lemma facts)))
      (h4-lexicographic-embedding-order-on-values-list-pair-transport p step wrappers 1))))

(defun h4-lexicographic-embedding-order-on-values-list-pair
  (x-cons y-cons embedding type-x type-y smaller goal length-lt)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((x-nat (proof-proof-prove-if proof type-x x-cons))
         (y-nat (proof-proof-prove-if proof type-y y-cons))
         (data (h4-lexicographic-embedding-cons-encodings embedding (list x-cons y-cons)))
         (left (h4-lexicographic-embedding-encoding embedding x-cons *h4-lexicographic-lex-ordinal*))
         (right (h4-lexicographic-embedding-encoding embedding y-cons *h4-lexicographic-lex-ordinal*))
         (wrappers (list left right))
         (yes-test (proof-proof-assume proof length-lt t))
         (yes (h4-lexicographic-embedding-order-on-values-list-pair-shorter
               yes-test embedding goal (cadr data) wrappers (car data)))
         (no-test (proof-proof-assume proof length-lt nil))
         (no (h4-lexicographic-embedding-order-on-values-list-pair-same-length
              no-test embedding smaller x-cons x-nat y-nat wrappers)))
      (h4-tactics-tactics-case-of p goal length-lt yes no))))

(defun h4-lexicographic-embedding-order-on-values-atomic-encoding (shape type-proof embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first shape))
         (cons-test (proof-term-at literal 1))
         (argument (proof-term-at cons-test 1))
         (natural (proof-proof-prove-if proof type-proof shape))
         (encoded (h4-lexicographic-embedding-encoding embedding shape *h4-lexicographic-lex-ordinal*))
         (fixed (h4-lexicographic-select-definition p (list *library-nfix* argument) natural)))
      (proof-proof-chain proof encoded (list fixed)))))

(defun h4-lexicographic-embedding-order-on-values-atom-left (x-atom y-cons embedding type-x goal)
  (proof-with-checked-results
      ((data (h4-lexicographic-embedding-cons-encodings embedding (list y-cons)))
       (left (h4-lexicographic-embedding-order-on-values-atomic-encoding x-atom type-x embedding))
       (right (h4-lexicographic-embedding-encoding embedding y-cons *h4-lexicographic-lex-ordinal*)))
    (h4-lexicographic-embedding-ordinal-proposition
     embedding goal (cons x-atom (cadr data)) (list* left right (car data)))))

(defun h4-lexicographic-embedding-order-on-values-atom-right (x-cons y-atom embedding smaller goal)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (len-x (list *library-len* *library-x*))
         (len-y (list *library-len* *library-y*)))
    (proof-with-checked-results
        ((y-zero (h4-lexicographic-select-definition p len-y y-atom))
         (positivity (h4-lexicographic-embedding-length-positive embedding x-cons))
         (distinct (h4-lexicographic-distinct p positivity nil))
         (zero-is-y (proof-proof-symmetric proof y-zero))
         (neq (proof-proof-rewrite proof distinct zero-is-y '(1 1 1)))
         (neq (h4-lexicographic-reverse-distinct p neq))
         (natural (library-library-natural p len-x))
         (nonnegative (library-library-cite p "NATURAL-NONNEGATIVE" (list len-x) (list natural)))
         (zero-is-y (proof-proof-symmetric proof y-zero))
         (bad-length (proof-proof-rewrite proof nonnegative zero-is-y '(1 1 2)))
         (contradiction (h4-terms-simplify-evidence
                         p smaller (list neq bad-length)
                         (list *h4-lexicographic-l-less* *h4-lexicographic-num-equal*))))
      (h4-terms-if-false-impossible p goal contradiction))))

(defun h4-lexicographic-embedding-order-on-values-both-atoms
  (x-atom y-atom embedding relation smaller type-x type-y goal)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((left-length (h4-lexicographic-select-definition
                       p (list *library-len* *library-x*) x-atom))
         (right-length (h4-lexicographic-select-definition
                        p (list *library-len* *library-y*) y-atom))
         (evidence (list x-atom y-atom))
         (reduction (h4-tactics-tactics-normalize
                     p relation evidence
                     (list *h4-lexicographic-l-less* *h4-lexicographic-num-equal*
                           *h4-terms-atom* *proof-not*)
                     (list left-length right-length) nil))
         (comparison (proof-proof-rewrite proof smaller reduction '(1)))
         (left (h4-lexicographic-embedding-order-on-values-atomic-encoding x-atom type-x embedding))
         (right (h4-lexicographic-embedding-order-on-values-atomic-encoding y-atom type-y embedding)))
      (h4-lexicographic-embedding-ordinal-proposition
       embedding goal (append evidence (list comparison)) (list left right)))))

(defun h4-lexicographic-embedding-order-on-values-cons
  (a embedding type-x type-y smaller goal length-lt y-cons)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((b (proof-proof-assume proof y-cons t))
         (yes (h4-lexicographic-embedding-order-on-values-list-pair
               a b embedding type-x type-y smaller goal length-lt))
         (b (proof-proof-assume proof y-cons nil))
         (no (h4-lexicographic-embedding-order-on-values-atom-right a b embedding smaller goal)))
      (h4-tactics-tactics-case-of p goal y-cons yes no))))

(defun h4-lexicographic-embedding-order-on-values-atom
  (a embedding type-x type-y smaller goal relation y-cons)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((b (proof-proof-assume proof y-cons t))
         (yes (h4-lexicographic-embedding-order-on-values-atom-left a b embedding type-x goal))
         (b (proof-proof-assume proof y-cons nil))
         (no (h4-lexicographic-embedding-order-on-values-both-atoms
              a b embedding relation smaller type-x type-y goal)))
      (h4-tactics-tactics-case-of p goal y-cons yes no))))

(defun h4-lexicographic-embedding-order-on-values (embedding)
  (let* ((p (h4-lexicographic-embedding-p embedding))
         (proof (library-library-proof p))
         (x *library-x*)
         (y *library-y*)
         (relation (list *h4-lexicographic-l-less* x y))
         (left (list *h4-lexicographic-lex-ordinal* x))
         (right (list *h4-lexicographic-lex-ordinal* y))
         (goal (list *proof-ordinal-less* left right))
         (length-lt (library-lt (list *library-len* x) (list *library-len* y)))
         (premise (proof-ite (h4-lexicographic-natural-list-type x)
                             (proof-ite (h4-lexicographic-natural-list-type y) relation *proof-false*)
                             *proof-false*))
         (formula (list *library-implies* premise goal))
         (x-cons (list *proof-consp* x))
         (y-cons (list *proof-consp* y)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof premise t))
         (parts (h4-tactics-tactics-conjunct p assumed))
         (further (h4-tactics-tactics-conjunct p (cadr parts)))
         (a (proof-proof-assume proof x-cons t))
         (yes (h4-lexicographic-embedding-order-on-values-cons
               a embedding (car parts) (car further) (cadr further) goal length-lt y-cons))
         (a (proof-proof-assume proof x-cons nil))
         (no (h4-lexicographic-embedding-order-on-values-atom
              a embedding (car parts) (car further) (cadr further) goal relation y-cons))
         (result (h4-tactics-tactics-case-of p goal x-cons yes no))
         (step (h4-tactics-tactics-imply p formula result)))
      (h4-lexicographic-embedding-local-lemma embedding "LEX-ORDER-ON-VALUES" step))))

(defun h4-lexicographic-embedding-init (p)
  (let ((x *library-x*))
    (proof-with-checked-results
        ((p (h4-terms-tactics-build p))
         (p (h4-lexicographic-define-list-ordinal p))
         (p (library-library-definition
             p *h4-lexicographic-lex-ordinal* (list x)
             (proof-ite (list *proof-consp* x) (list *h4-lexicographic-list-ordinal* x)
                        (list *library-nfix* x))))
         (embedding (list :h4-embedding p nil nil nil nil nil nil))
         (leading (h4-lexicographic-embedding-leading-exponent embedding))
         (embedding (update-nth 2 (car leading) (cdr leading)))
         (list-ordinal (h4-lexicographic-embedding-ordinal-on-lists embedding))
         (embedding (update-nth 3 (car list-ordinal) (cdr list-ordinal)))
         (ordinal (h4-lexicographic-embedding-ordinal-on-values embedding))
         (embedding (update-nth 4 (car ordinal) (cdr ordinal)))
         (fix-type (h4-lexicographic-embedding-fixed-types embedding))
         (embedding (update-nth 5 (car fix-type) (cdr fix-type)))
         (list-order (h4-lexicographic-embedding-order-on-lists embedding))
         (embedding (update-nth 6 (car list-order) (cdr list-order)))
         (order (h4-lexicographic-embedding-order-on-values embedding)))
      (update-nth 7 (car order) (cdr order)))))

(defun h4-lexicographic-embedding-fixed-ordinal-order (embedding comparison)
  (let ((p (h4-lexicographic-embedding-p embedding)))
    (proof-with-checked-results
        ((literal (proof-step-first comparison))
         (arguments (proof-list-of-length literal 3))
         (a (cadr arguments))
         (b (caddr arguments))
         (lemma (h4-lexicographic-embedding-fact embedding (h4-lexicographic-embedding-order embedding) a b))
         (a-argument (proof-term-at a 1))
         (a-type (h4-lexicographic-embedding-fact
                  embedding (h4-lexicographic-embedding-fix-type embedding) a-argument :none))
         (b-argument (proof-term-at b 1))
         (b-type (h4-lexicographic-embedding-fact
                  embedding (h4-lexicographic-embedding-fix-type embedding) b-argument :none))
         (literal (proof-step-first lemma))
         (guard (proof-term-at literal 1))
         (established (h4-tactics-tactics-establish p guard (list a-type b-type comparison) nil nil nil)))
      (h4-tactics-tactics-modus-ponens p lemma established))))
