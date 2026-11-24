(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-arithmetic-fix* (proof-sym "FIX" "ACL2"))
(defconst *h1-book-arithmetic-reciprocal* (proof-sym "UNARY-/" "ACL2"))
(defconst *h1-book-arithmetic-iff* (proof-sym "IFF" "ACL2"))
(defconst *h1-book-arithmetic-expt* (proof-cl "EXPT"))
(defconst *h1-book-arithmetic-operators*
  (list (cons *proof-plus* "+") (cons *proof-times* "*")))

(defun h1-book-arithmetic-rational-constant (term)
  (h1-tactics-rational-constant term))

(defun h1-book-arithmetic-compute-rational (proof term)
  (h1-tactics-compute-rational proof term))

(defun h1-book-arithmetic-operator-name (prefix operator)
  (let ((entry (assoc-equal operator *h1-book-arithmetic-operators*)))
    (if entry
        (concatenate 'string prefix (cdr entry))
      '(:failure "failure" ""))))

(defun h1-book-arithmetic-right-unit (proof operator term)
  (let* ((lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof))
         (additive (equal operator *proof-plus*))
         (unit (if additive *proof-zero* *proof-one*))
         (identity (if additive "UNICITY-OF-0" "UNICITY-OF-1")))
    (proof-with-checked-results
        ((name (h1-book-arithmetic-operator-name "COMMUTATIVITY-OF-" operator))
         (commuted (library-library-axiom lib name (list term unit)))
         (unit-step (library-library-axiom lib identity (list term))))
      (proof-proof-chain base commuted (list unit-step)))))

(defun h1-book-arithmetic-right-side (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun h1-book-arithmetic-collapse-fix (proof term numeric)
  (let ((lib (h1-tactics-prover-library proof))
        (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold base (list *h1-book-arithmetic-fix* term)))
         (branch (h1-book-arithmetic-right-side equation))
         (selected (h1-propositions-propositional-proof-select lib branch numeric)))
      (proof-proof-chain base equation (list selected)))))

(defun h1-book-arithmetic-sum-with-fix (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof))
         (x *library-x*)
         (y *library-y*)
         (numeric (list *library-numberp* x)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold base (list *h1-book-arithmetic-fix* x)))
         (opened-right (h1-book-arithmetic-right-side opened))
         (yes (h1-arithmetic-proof-if-true base opened-right))
         (yes (proof-proof-chain base opened (list yes)))
         (no (h1-arithmetic-proof-if-false base opened-right))
         (no (proof-proof-chain base opened (list no)))
         (first (h1-propositions-propositional-proof-reflexive lib (library-plus x y)))
         (yes-reverse (h1-propositions-proof-symmetric base yes))
         (first (proof-proof-rewrite base first yes-reverse '(1 2 1)))
         (original (library-library-axiom lib "COMPLETION-OF-+" (list x y)))
         (original-right (h1-book-arithmetic-right-side original))
         (reduced (h1-arithmetic-proof-if-false base original-right))
         (reduced (proof-proof-chain base original (list reduced)))
         (fixed-y (proof-proof-unfold base (list *h1-book-arithmetic-fix* y)))
         (fixed-y (h1-propositions-proof-symmetric base fixed-y))
         (reduced (proof-proof-chain base reduced (list fixed-y)))
         (other (library-library-axiom lib "UNICITY-OF-0" (list y)))
         (no-reverse (h1-propositions-proof-symmetric base no))
         (other (proof-proof-rewrite base other no-reverse '(1 1 1)))
         (other (h1-propositions-proof-symmetric base other))
         (last (proof-proof-chain base reduced (list other))))
      (proof-proof-cases base numeric first last))))

(defun h1-book-arithmetic-same-equality-value (proof left right forward reverse-step)
  (let ((base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((assumed (h1-arithmetic-proof-assume base left t))
         (left-true (h1-tactics-prover-equality-is-true proof assumed))
         (right-true (h1-tactics-prover-equality-is-true proof forward))
         (right-true (h1-propositions-proof-symmetric base right-true))
         (yes (proof-proof-chain base left-true (list right-true)))
         (not-left (h1-arithmetic-proof-assume base left nil))
         (not-right (proof-proof-cut base reverse-step not-left))
         (not-right (proof-proof-front base not-right (proof-neg right)))
         (left-false (h1-tactics-prover-false-equation proof not-left))
         (right-false (h1-tactics-prover-false-equation proof not-right))
         (right-false (h1-propositions-proof-symmetric base right-false))
         (no (proof-proof-chain base left-false (list right-false))))
      (proof-proof-cases base left yes no))))

(defun h1-book-arithmetic-cancel-addend-reduce (proof forward index term common)
  (let ((lib (h1-tactics-prover-library proof))
        (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((assoc-step (library-library-axiom
                      lib "ASSOCIATIVITY-OF-+" (list term common (library-minus common))))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list common)))
         (reduced (proof-proof-rewrite base assoc-step inverse '(1 2 2)))
         (unit (h1-book-arithmetic-right-unit proof *proof-plus* term))
         (reduction (proof-proof-chain base reduced (list unit))))
      (proof-proof-rewrite base forward reduction (list 1 index)))))

(defun h1-book-arithmetic-cancel-addend-proof (proof right x common y swapped)
  (let* ((lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof))
         (sum-left (library-plus x common))
         (summed (proof-eq sum-left (library-plus y common)))
         (fixed-name "H1-SUM-WITH-FIX"))
    (proof-with-checked-results
        ((forward (h1-propositions-propositional-proof-reflexive
                   lib (library-plus sum-left (library-minus common))))
         (assumed-sum (h1-arithmetic-proof-assume base summed t))
         (forward (proof-proof-rewrite base forward assumed-sum '(1 2 1)))
         (forward (h1-book-arithmetic-cancel-addend-reduce proof forward 1 x common))
         (forward (h1-book-arithmetic-cancel-addend-reduce proof forward 2 y common))
         (left-fix (library-library-axiom lib fixed-name (list x common)))
         (right-fix (library-library-axiom lib fixed-name (list y common)))
         (assumed-right (h1-arithmetic-proof-assume base right t))
         (reverse-step (proof-proof-rewrite base left-fix assumed-right '(1 2 1)))
         (right-fix (h1-propositions-proof-symmetric base right-fix))
         (reverse-step (proof-proof-chain base reverse-step (list right-fix)))
         (step (h1-book-arithmetic-same-equality-value proof summed right forward reverse-step))
         (step (if swapped
                   (proof-with-checked-results
                       ((left-swap (library-library-axiom lib "COMMUTATIVITY-OF-+" (list x common)))
                        (step (proof-proof-rewrite base step left-swap '(1 1 1)))
                        (right-swap (library-library-axiom lib "COMMUTATIVITY-OF-+" (list y common))))
                     (proof-proof-rewrite base step right-swap '(1 1 2)))
                 step)))
      (proof-proof-tidy base step))))

(defun h1-book-arithmetic-binary-arguments (term)
  (proof-with-checked-results ((tail (h1-arithmetic-term-tail term)))
    (proof-list-of-length tail 2)))

(defun h1-book-arithmetic-cancel-addend (proof formula)
  (proof-with-checked-results ((parts (h1-book-arithmetic-binary-arguments formula)))
    (let ((left (car parts))
          (right (cadr parts)))
      (if (not (and (proof-is-call left *proof-equal*)
                    (proof-is-call right *proof-equal*)))
          nil
        (proof-with-checked-results ((sums (h1-book-arithmetic-binary-arguments left)))
          (let ((a (car sums))
                (b (cadr sums)))
            (if (not (and (proof-is-call a *proof-plus*) (proof-is-call b *proof-plus*)))
                nil
              (proof-with-checked-results
                  ((a (h1-book-arithmetic-binary-arguments a))
                   (b (h1-book-arithmetic-binary-arguments b)))
                (let* ((left-start (car a))
                       (left-end (cadr a))
                       (right-start (car b))
                       (right-end (cadr b))
                       (swapped (not (equal left-end right-end)))
                       (x (if swapped left-end left-start))
                       (common (if swapped left-start left-end))
                       (y (if swapped right-end right-start)))
                  (if (or (and swapped (not (equal left-start right-start)))
                          (not (equal right (proof-eq (list *h1-book-arithmetic-fix* x)
                                                      (list *h1-book-arithmetic-fix* y)))))
                      nil
                    (h1-book-arithmetic-cancel-addend-proof proof right x common y swapped)))))))))))

(defun h1-book-arithmetic-minus-as-product (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof))
         (x *library-x*)
         (fixed (list *h1-book-arithmetic-fix* x))
         (term (list *proof-times* x *proof-neg-one*))
         (inverse (library-minus fixed)))
    (proof-with-checked-results
        ((distribution (library-library-axiom lib "DISTRIBUTIVITY"
                                              (list x *proof-one* *proof-neg-one*)))
         (zero (proof-proof-compute base (library-plus *proof-one* *proof-neg-one*) 0))
         (distribution (proof-proof-rewrite base distribution zero '(1 1 2)))
         (product-zero (proof-proof-fact base (proof-sym "H1-PRODUCT-ZERO" "ACL2") nil))
         (distribution (proof-proof-rewrite base distribution product-zero '(1 1)))
         (unit (h1-book-arithmetic-right-unit proof *proof-times* x))
         (distribution (proof-proof-rewrite base distribution unit '(1 2 1)))
         (sum-zero (h1-propositions-proof-symmetric base distribution))

         (number (h1-tactics-prover-solve proof (list *library-numberp* term) nil 160))
         (zero-unit (library-library-axiom lib "UNICITY-OF-0" (list term)))
         (numeric-fix (h1-book-arithmetic-collapse-fix proof term number))
         (term-plus-zero (proof-proof-chain base zero-unit (list numeric-fix)))
         (commuted (library-library-axiom lib "COMMUTATIVITY-OF-+" (list inverse fixed)))
         (inverse-step (library-library-axiom lib "INVERSE-OF-+" (list fixed)))
         (reversed-sum (proof-proof-chain base commuted (list inverse-step)))
         (start (h1-propositions-proof-symmetric base term-plus-zero))
         (reversed-sum (h1-propositions-proof-symmetric base reversed-sum))
         (start (proof-proof-rewrite base start reversed-sum '(1 2 1)))
         (assoc-step (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list inverse fixed term)))
         (start (proof-proof-chain base start (list assoc-step)))
         (start (proof-proof-rewrite base start sum-zero '(1 2 2)))
         (has-number (h1-tactics-prover-solve proof (list *library-numberp* inverse) nil 160))
         (unit (h1-book-arithmetic-right-unit proof *proof-plus* inverse))
         (inverse-fix (h1-book-arithmetic-collapse-fix proof inverse has-number))
         (exact (proof-proof-chain base start (list unit inverse-fix)))

         (reduced (proof-proof-unfold base fixed))
         (source (h1-propositions-propositional-proof-reflexive lib inverse))
         (reduced-right (h1-book-arithmetic-right-side reduced))
         (true-branch (h1-arithmetic-proof-if-true base reduced-right))
         (true-branch (proof-proof-chain base reduced (list true-branch)))
         (has-x (proof-proof-rewrite base source true-branch '(1 2 1)))
         (false-branch (h1-arithmetic-proof-if-false base reduced-right))
         (false-branch (proof-proof-chain base reduced (list false-branch)))
         (no-x (proof-proof-rewrite base source false-branch '(1 2 1)))
         (zero-minus (proof-proof-compute base (library-minus *proof-zero*) 0))
         (no-x (proof-proof-chain base no-x (list zero-minus)))
         (completion (library-library-axiom lib "COMPLETION-OF-UNARY-MINUS" (list x)))
         (completion-right (h1-book-arithmetic-right-side completion))
         (default (h1-arithmetic-proof-if-false base completion-right))
         (default (proof-proof-chain base completion (list default)))
         (default (h1-propositions-proof-symmetric base default))
         (no-x (proof-proof-chain base no-x (list default)))
         (has-inverse (proof-proof-cases base (list *library-numberp* x) has-x no-x))
         (has-inverse (h1-propositions-proof-symmetric base has-inverse))
         (exact (h1-propositions-proof-symmetric base exact))
         (last (library-library-axiom lib "COMMUTATIVITY-OF-*" (list x *proof-neg-one*))))
      (proof-proof-chain base has-inverse (list exact last)))))

(defun h1-book-arithmetic-byte-field-p (term index)
  (and (consp term)
       (cond ((equal (car term) "sym") (or (equal index 1) (equal index 2)))
             ((equal (car term) "str") (equal index 1))
             (t nil))))

(defun h1-book-arithmetic-index (term index bytes)
  (cond
   ((integerp term) '(:failure "failure" ""))
   ((eq term t) '(:failure "failure" ""))
   ((rationalp term) '(:failure "failure" ""))
   (t
    (let* ((index (cond ((eq index t) 1) ((not index) 0) (t index)))
           (size (if (stringp term) (length term) (len term)))
           (offset (if (< index 0) (+ size index) index)))
      (cond
       ((not (integerp index)) '(:failure "failure" ""))
       ((or (< offset 0) (<= size offset))
        '(:failure "failure" ""))
       ((stringp term)
        (let ((byte-char (char term offset)))
          (cons (if bytes (char-code byte-char) (coerce (list byte-char) 'string)) nil)))
       (t (cons (nth offset term) (h1-book-arithmetic-byte-field-p term offset))))))))

(defun h1-book-arithmetic-at-places (term place bytes)
  (declare (xargs :measure (acl2-count place)))
  (if (endp place)
      term
    (proof-with-checked-results ((part (h1-book-arithmetic-index term (car place) bytes)))
      (h1-book-arithmetic-at-places (car part) (cdr place) (cdr part)))))

(defun h1-book-arithmetic-at (term place)
  (h1-book-arithmetic-at-places term place nil))

(defun h1-book-arithmetic-add-rule (proof step)
  (proof-with-checked-results
      ((rules (h1-tactics-rules-add (h1-tactics-prover-rules proof) step t t)))
    (h1-tactics-prover-with-rules proof rules)))

(defun h1-book-arithmetic-install-closure (remaining proof tail)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (h1-book-arithmetic-add-rule proof tail)
    (proof-with-checked-results
        ((parts (h1-propositions-propositional-proof-conjunct
                 (h1-tactics-prover-library proof) tail))
         (proof (h1-book-arithmetic-add-rule proof (car parts))))
      (h1-book-arithmetic-install-closure (1- remaining) proof (cadr parts)))))

(defun h1-book-arithmetic-install-formula (proof name)
  (proof-with-checked-results
      ((step (proof-proof-fact (h1-tactics-prover-proof proof) name nil))
       (rules (h1-tactics-rules-add-formula (h1-tactics-prover-rules proof) step t t)))
    (h1-tactics-prover-with-rules proof rules)))

(defun h1-book-arithmetic-install-formulas (proof names)
  (declare (xargs :measure (acl2-count names)))
  (if (or (endp names) (failure-p proof))
      proof
    (h1-book-arithmetic-install-formulas
     (h1-book-arithmetic-install-formula proof (car names)) (cdr names))))

(defun h1-book-arithmetic-install-citation (proof name)
  (proof-with-checked-results
      ((step (library-library-cite (h1-tactics-prover-library proof) name nil nil)))
    (h1-book-arithmetic-add-rule proof step)))

(defun h1-book-arithmetic-install-citations (proof names)
  (declare (xargs :measure (acl2-count names)))
  (if (or (endp names) (failure-p proof))
      proof
    (h1-book-arithmetic-install-citations
     (h1-book-arithmetic-install-citation proof (car names)) (cdr names))))

(defun h1-book-arithmetic-install-units (proof operator name)
  (proof-with-checked-results
      ((identity (library-library-axiom (h1-tactics-prover-library proof)
                                        name (list *library-x*)))
       (proof (h1-book-arithmetic-add-rule proof identity))
       (right (h1-book-arithmetic-right-unit proof operator *library-x*)))
    (h1-book-arithmetic-add-rule proof right)))

(defun h1-book-arithmetic-install-fix-branches (proof)
  (let* ((base (h1-tactics-prover-proof proof))
         (term (list *h1-book-arithmetic-fix* *library-x*)))
    (proof-with-checked-results
        ((fixed (proof-proof-unfold base term))
         (conditional (h1-book-arithmetic-right-side fixed))
         (no (h1-arithmetic-proof-if-false base conditional))
         (no (proof-proof-chain base fixed (list no)))
         (proof (h1-book-arithmetic-add-rule proof no))
         (yes (h1-arithmetic-proof-if-true base conditional))
         (yes (proof-proof-chain base fixed (list yes)))
         (proof (h1-book-arithmetic-add-rule proof yes))
         (number (h1-tactics-prover-solve
                  proof (list *library-numberp* term) (list *h1-book-arithmetic-fix*) 160))
         (helper (h1-tactics-prover-helper proof "FIX-NUMBER" number nil t)))
      (cdr helper))))

(defun h1-book-arithmetic-install-equality-symmetry (proof)
  (let* ((base (h1-tactics-prover-proof proof))
         (xy (proof-eq *library-x* *library-y*))
         (yx (proof-eq *library-y* *library-x*)))
    (proof-with-checked-results
        ((forward (h1-arithmetic-proof-assume base xy t))
         (forward (h1-propositions-proof-symmetric base forward))
         (reverse-step (h1-arithmetic-proof-assume base yx t))
         (reverse-step (h1-propositions-proof-symmetric base reverse-step))
         (symmetry (h1-book-arithmetic-same-equality-value proof xy yx forward reverse-step))
         (helper (h1-tactics-prover-helper proof "EQUALITY-SYMMETRIC-VALUE" symmetry nil nil)))
      (cdr helper))))

(defun h1-book-arithmetic-install-reciprocal (proof)
  (let ((base (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((reciprocal (library-library-axiom lib "COMPLETION-OF-UNARY-/" (list *library-x*)))
         (right (h1-book-arithmetic-right-side reciprocal))
         (guard-test (proof-term-at right 1))
         (default (h1-arithmetic-proof-if-false base guard-test))
         (branch (proof-proof-rewrite base reciprocal default '(1 2 1)))
         (right (h1-book-arithmetic-right-side branch))
         (value-term (proof-term-at right 2))
         (value (proof-proof-fact base "if-nil"
                                  (list (list *library-y* value-term)
                                        (list *library-z* *proof-zero*))))
         (test (proof-term-at right 1)))
      (if (not (equal test *proof-false*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((step (proof-proof-chain base branch (list value)))
             (proof (h1-book-arithmetic-add-rule proof step))
             (zero (proof-proof-compute
                    base (list *h1-book-arithmetic-reciprocal* *proof-zero*) 0)))
          (h1-book-arithmetic-add-rule proof zero))))))

(defun h1-book-arithmetic-multiplication-by-zero (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (result (h1-arithmetic-multiplication-by-zero lib nil)))
    (if (not (h1-arithmetic-request-p result))
        result
      (let* ((args (h1-arithmetic-request-args result))
             (step (h1-tactics-prover-solve proof (car args) (cadr args) (caddr args))))
        (h1-arithmetic-multiplication-by-zero
         lib (list (cons (h1-arithmetic-request-key result) step)))))))

(defun h1-book-arithmetic-install-zero-and-minus (proof)
  (proof-with-checked-results
      ((step (h1-book-arithmetic-multiplication-by-zero proof))
       (helper (h1-tactics-prover-helper proof "PRODUCT-ZERO" step nil t))
       (proof (cdr helper))
       (base (h1-tactics-prover-proof proof))
       (zero (library-library-axiom
              (h1-tactics-prover-library proof) "COMMUTATIVITY-OF-*"
              (list *proof-zero* *library-x*)))
       (step (proof-proof-fact base (proof-sym "H1-PRODUCT-ZERO" "ACL2") nil))
       (zero (proof-proof-chain base zero (list step)))
       (proof (h1-book-arithmetic-add-rule proof zero))
       (step (h1-book-arithmetic-minus-as-product proof))
       (helper (h1-tactics-prover-helper proof "MINUS-AS-PRODUCT" step nil nil)))
    (cdr helper)))

(defun h1-book-arithmetic-install-swap-and-expt (proof)
  (let* ((base (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (x *library-x*)
         (y *library-y*)
         (z *library-z*))
    (proof-with-checked-results
        ((assoc-step (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list x y z)))
         (left (h1-propositions-proof-symmetric base assoc-step))
         (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list x y)))
         (swap (proof-proof-rewrite base left commuted '(1 2 1)))
         (right (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list y x z)))
         (swap (proof-proof-chain base swap (list right)))
         (helper (h1-tactics-prover-helper proof "PRODUCT-SWAP" swap nil nil))
         (proof (cdr helper))
         (expt (h1-tactics-prover-solve
                proof (proof-eq (list *h1-book-arithmetic-expt* x *proof-zero*) *proof-one*)
                (list *h1-book-arithmetic-expt* (proof-sym "ZIP" "ACL2")) 160))
         (helper (h1-tactics-prover-helper proof "EXPT-AT-ZERO" expt nil t)))
      (cdr helper))))

(defun h1-book-arithmetic-install-arithmetic (proof)
  (proof-with-checked-results
      ((tail (library-library-axiom (h1-tactics-prover-library proof) "CLOSURE"
                                    (list *library-x* *library-y*)))
       (proof (h1-book-arithmetic-install-closure 3 proof tail))
       (proof (h1-book-arithmetic-install-formulas
               proof '("integerp-binary-+" "integerp-binary-*" "integerp-unary--"
                       "rationalp-binary-+" "rationalp-binary-*" "rationalp-unary--"
                       "rationalp-unary-/")))
       (proof (h1-book-arithmetic-install-citations
               proof '("POSITIVE-SUM" "POSITIVE-PRODUCT" "POSITIVE-NONNEGATIVE"
                       "NATURAL-INTEGER" "NATURAL-NONNEGATIVE" "NATURAL-FROM-BOUNDS")))
       (proof (h1-book-arithmetic-install-units proof *proof-plus* "UNICITY-OF-0"))
       (proof (h1-book-arithmetic-install-units proof *proof-times* "UNICITY-OF-1"))
       (proof (h1-book-arithmetic-install-fix-branches proof))
       (step (h1-book-arithmetic-sum-with-fix proof))
       (helper (h1-tactics-prover-helper proof "SUM-WITH-FIX" step nil nil))
       (proof (h1-book-arithmetic-install-equality-symmetry (cdr helper)))
       (proof (h1-book-arithmetic-install-reciprocal proof))
       (proof (h1-book-arithmetic-install-zero-and-minus proof)))
    (h1-book-arithmetic-install-swap-and-expt proof)))

(defun h1-book-arithmetic-algebra-proof (self)
  (cadr self))

(defun h1-book-arithmetic-algebra-context (self)
  (caddr self))

(defun h1-book-arithmetic-algebra-work (self)
  (cadddr self))

(defun h1-book-arithmetic-algebra-with-context (self context)
  (list :h1-algebra (h1-book-arithmetic-algebra-proof self)
        context (h1-book-arithmetic-algebra-work self)))

(defun h1-book-arithmetic-algebra-with-work (self work)
  (list :h1-algebra (h1-book-arithmetic-algebra-proof self)
        (h1-book-arithmetic-algebra-context self) work))

(defun h1-book-arithmetic-algebra-with-proof (self proof)
  (let* ((context (h1-book-arithmetic-algebra-context self))
         (old (h1-tactics-context-search context))
         (search (h1-tactics-search-init
                  proof (h1-tactics-search-openings old) (h1-tactics-search-local old)
                  (h1-tactics-search-ambient old) (h1-tactics-search-protected old)
                  (h1-tactics-search-remaining old) (h1-tactics-search-rewrite-equalities old)))
         (search (h1-tactics-search-with-work search (h1-tactics-search-work old))))
    (list :h1-algebra proof (h1-tactics-context-with-search context search)
          (h1-book-arithmetic-algebra-work self))))

(defun h1-book-arithmetic-algebra-add-evidence (context step)
  (proof-with-checked-results
      ((step step)
       (term (proof-step-first step))
       (entries (table-put (h1-tactics-context-evidence context) term step))
       (context (h1-tactics-context-with-evidence context entries)))
    (h1-tactics-context-bind-equality context step)))

(defun h1-book-arithmetic-algebra-evidence-context (context evidence)
  (declare (xargs :measure (acl2-count evidence)))
  (if (or (endp evidence) (failure-p context))
      context
    (h1-book-arithmetic-algebra-evidence-context
     (h1-book-arithmetic-algebra-add-evidence context (car evidence)) (cdr evidence))))

(defun h1-book-arithmetic-algebra-init (proof tests evidence)
  (proof-with-checked-results
      ((search (h1-tactics-search-init proof nil nil nil nil 160 nil))
       (context (h1-tactics-context-init search tests))
       (context (h1-book-arithmetic-algebra-evidence-context context evidence)))
    (list :h1-algebra proof context 150)))

(defun h1-book-arithmetic-algebra-assoc (self head x y z)
  (let ((lib (h1-tactics-prover-library (h1-book-arithmetic-algebra-proof self))))
    (proof-with-checked-results
        ((name (h1-book-arithmetic-operator-name "ASSOCIATIVITY-OF-" head)))
      (library-library-axiom lib name (list x y z)))))

(defun h1-book-arithmetic-algebra-commute (self head x y)
  (let ((lib (h1-tactics-prover-library (h1-book-arithmetic-algebra-proof self))))
    (proof-with-checked-results
        ((name (h1-book-arithmetic-operator-name "COMMUTATIVITY-OF-" head)))
      (library-library-axiom lib name (list x y)))))

(defun h1-book-arithmetic-algebra-distribute (self term)
  (let* ((proof (h1-book-arithmetic-algebra-proof self))
         (lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results ((parts (proof-list-of-length term 3)))
      (let ((left (cadr parts))
            (right (caddr parts)))
        (cond ((proof-is-call right *proof-plus*)
               (library-library-axiom lib "DISTRIBUTIVITY" (cons left (cdr right))))
              ((proof-is-call left *proof-plus*)
               (proof-with-checked-results
                   ((commuted (h1-book-arithmetic-algebra-commute self *proof-times* left right))
                    (law (library-library-axiom lib "DISTRIBUTIVITY" (cons right (cdr left)))))
                 (proof-proof-chain base commuted (list law))))
              (t nil))))))

(defun h1-book-arithmetic-spine-node (step place)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (h1-book-arithmetic-at literal (cdr place))))

(defun h1-book-arithmetic-algebra-associate-next (self step head place)
  (proof-with-checked-results ((node (h1-book-arithmetic-spine-node step place)))
    (if (not (proof-is-call node head))
        (list nil step)
      (proof-with-checked-results ((parts (h1-book-arithmetic-binary-arguments node)))
        (let ((left (car parts))
              (right (cadr parts)))
          (if (not (proof-is-call left head))
              (list (append place '(2)) step)
            (let ((base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
              (proof-with-checked-results
                  ((args (h1-book-arithmetic-binary-arguments left))
                   (law (h1-book-arithmetic-algebra-assoc self head (car args) (cadr args) right))
                   (step (proof-proof-rewrite base step law place)))
                (list place step)))))))))

(defun h1-book-arithmetic-algebra-associate-loop (n self head cursor)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h1-book-arithmetic-algebra-associate-loop"))
        ((failure-p cursor) cursor)
        ((not (car cursor)) (cadr cursor))
        (t (h1-book-arithmetic-algebra-associate-loop
            (1- n) self head
            (h1-book-arithmetic-algebra-associate-next
             self (cadr cursor) head (car cursor))))))

(defun h1-book-arithmetic-algebra-associate (self step head)
  (h1-book-arithmetic-algebra-associate-loop 1000000 self head (list '(1 2) step)))

(defun h1-book-arithmetic-algebra-coefficient (self term)
  (declare (ignore self))
  (if (not (proof-is-call term *proof-times*))
      (list *proof-one* term)
    (proof-with-checked-results
        ((first (proof-term-at term 1))
         (value (h1-book-arithmetic-rational-constant first)))
      (if (not value)
          (list *proof-one* term)
        (proof-with-checked-results ((second (proof-term-at term 2)))
          (list first second))))))

(defun h1-book-arithmetic-algebra-sort-key (term self head)
  (proof-with-checked-results
      ((base (cond ((equal head *proof-plus*)
                    (proof-with-checked-results
                        ((parts (h1-book-arithmetic-algebra-coefficient self term)))
                      (cadr parts)))
                   ((proof-is-call term *h1-book-arithmetic-reciprocal*)
                    (proof-term-at term 1))
                   (t term)))
       (numeric (h1-book-arithmetic-rational-constant term))
       (base-text (proof-write base))
       (term-text (proof-write term)))
    (list (not numeric) base-text term-text)))

(defun h1-book-arithmetic-key-later-p (left right)
  (cond ((not (eq (car left) (car right))) (car left))
        ((not (equal (cadr left) (cadr right))) (string< (cadr right) (cadr left)))
        (t (string< (caddr right) (caddr left)))))

(defun h1-book-arithmetic-algebra-sort-swap (self head left right rest suffix)
  (if (not suffix)
      (h1-book-arithmetic-algebra-commute self head left right)
    (let* ((proof (h1-book-arithmetic-algebra-proof self))
           (lib (h1-tactics-prover-library proof))
           (name (if (equal head *proof-times*) "H1-PRODUCT-SWAP" "COMMUTATIVITY-2-OF-+")))
      (proof-with-checked-results ((tail (proof-term-at rest 2)))
        (library-library-axiom lib name (list left right tail))))))

(defun h1-book-arithmetic-algebra-sort-next (self step head place changed)
  (proof-with-checked-results ((node (h1-book-arithmetic-spine-node step place)))
    (if (not (proof-is-call node head))
        (list nil step changed)
      (proof-with-checked-results ((parts (h1-book-arithmetic-binary-arguments node)))
        (let* ((left (car parts))
               (rest (cadr parts))
               (suffix (proof-is-call rest head))
               (base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
          (proof-with-checked-results
              ((right (if suffix (proof-term-at rest 1) rest))
               (left-key (h1-book-arithmetic-algebra-sort-key left self head))
               (right-key (h1-book-arithmetic-algebra-sort-key right self head))
               (swap-p (h1-book-arithmetic-key-later-p left-key right-key))
               (step (if swap-p
                         (proof-with-checked-results
                             ((swap (h1-book-arithmetic-algebra-sort-swap
                                     self head left right rest suffix)))
                           (proof-proof-rewrite base step swap place))
                       step)))
            (list (append place '(2)) step (or changed swap-p))))))))

(defun h1-book-arithmetic-algebra-sort-pass (n self head cursor)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h1-book-arithmetic-algebra-sort-pass"))
        ((failure-p cursor) cursor)
        ((not (car cursor)) (cons (cadr cursor) (caddr cursor)))
        (t (h1-book-arithmetic-algebra-sort-pass
            (1- n) self head
            (h1-book-arithmetic-algebra-sort-next
             self (cadr cursor) head (car cursor) (caddr cursor))))))

(defun h1-book-arithmetic-algebra-sort-loop (n self head result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h1-book-arithmetic-algebra-sort-loop"))
        ((failure-p result) result)
        ((not (cdr result)) (car result))
        (t (h1-book-arithmetic-algebra-sort-loop
            (1- n) self head
            (h1-book-arithmetic-algebra-sort-pass 1000000 self head (list '(1 2) (car result) nil))))))

(defun h1-book-arithmetic-algebra-sort (self step head)
  (h1-book-arithmetic-algebra-sort-loop 1000000 self head (cons step t)))

(defmacro h1-book-arithmetic-with-algebra (self bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (failure-p ,name)
             (cons ,name ,self)
           (h1-book-arithmetic-with-algebra ,self ,(cdr bindings) ,body))))))

(defun h1-book-arithmetic-algebra-context-result (self result)
  (if (failure-p result)
      (cons result self)
    (cons (car result) (h1-book-arithmetic-algebra-with-context self (cdr result)))))

(defun h1-book-arithmetic-algebra-find (self term)
  (h1-book-arithmetic-algebra-context-result
   self (h1-tactics-context-find (h1-book-arithmetic-algebra-context self) term)))

(defun h1-book-arithmetic-algebra-constant-or-rewrite (self term)
  (let ((computed (h1-tactics-prover-constant (h1-book-arithmetic-algebra-proof self) term)))
    (if computed
        (cons computed self)
      (h1-book-arithmetic-algebra-context-result
       self (h1-tactics-context-apply (h1-book-arithmetic-algebra-context self)
                                     "rewrites" term)))))

(defun h1-book-arithmetic-algebra-collect-with-coefficient (term value self base numeric)
  (if (not (equal term base))
      (h1-book-arithmetic-algebra-commute self *proof-times* value base)
    (let* ((proof (h1-book-arithmetic-algebra-proof self))
           (prf (h1-tactics-prover-proof proof)))
      (proof-with-checked-results
          ((unit (h1-book-arithmetic-right-unit proof *proof-times* term))
           (fixed (h1-book-arithmetic-collapse-fix proof term numeric))
           (identity (proof-proof-chain prf unit (list fixed))))
        (h1-propositions-proof-symmetric prf identity)))))

(defun h1-book-arithmetic-algebra-collect-inverse (self left right term a)
  (let* ((proof (h1-book-arithmetic-algebra-proof self))
         (lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((negation (proof-proof-fact base (proof-sym "H1-MINUS-AS-PRODUCT" "ACL2")
                                    (list (list *library-x* term))))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list term)))
         (inverse (proof-proof-rewrite base inverse negation '(1 1 2))))
      (if (not (equal a *proof-neg-one*))
          inverse
        (proof-with-checked-results
            ((swap (h1-book-arithmetic-algebra-commute self *proof-plus* left right)))
          (proof-proof-chain base swap (list inverse)))))))

(defun h1-book-arithmetic-algebra-collect-numeric (self left right a b term numeric)
  (let* ((proof (h1-book-arithmetic-algebra-proof self))
         (lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((step (h1-propositions-propositional-proof-reflexive lib (library-plus left right)))
         (left-coefficient (h1-book-arithmetic-algebra-collect-with-coefficient
                            left a self term numeric))
         (step (proof-proof-rewrite base step left-coefficient '(1 2 1)))
         (right-coefficient (h1-book-arithmetic-algebra-collect-with-coefficient
                             right b self term numeric))
         (step (proof-proof-rewrite base step right-coefficient '(1 2 2)))
         (distributed (library-library-axiom lib "DISTRIBUTIVITY" (list term a b)))
         (distributed (h1-propositions-proof-symmetric base distributed))
         (swap (h1-book-arithmetic-algebra-commute self *proof-times* term (library-plus a b))))
      (proof-proof-chain base step (list distributed swap)))))

(defun h1-book-arithmetic-algebra-collect (self left right)
  (h1-book-arithmetic-with-algebra self
      ((left-parts (h1-book-arithmetic-algebra-coefficient self left))
       (right-parts (h1-book-arithmetic-algebra-coefficient self right)))
    (let ((a (car left-parts))
          (base (cadr left-parts))
          (b (car right-parts))
          (other (cadr right-parts)))
      (cond
       ((not (equal base other)) (cons nil self))
       ((or (and (equal a *proof-neg-one*) (equal right base))
            (and (equal b *proof-neg-one*) (equal left base)))
        (cons (h1-book-arithmetic-algebra-collect-inverse self left right base a) self))
       (t
        (let* ((lookup (h1-book-arithmetic-algebra-find self (list *library-numberp* base)))
               (numeric (car lookup))
               (self (cdr lookup)))
          (cond ((failure-p numeric) lookup)
                ((and (not numeric) (or (equal left base) (equal right base))) lookup)
                (t (cons (h1-book-arithmetic-algebra-collect-numeric
                          self left right a b base numeric)
                         self)))))))))

(defun h1-book-arithmetic-algebra-cancel-reciprocal-loop (n self left right)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) (cons '(:failure "Fuel" "h1-book-arithmetic-algebra-cancel-reciprocal-loop") self))
   ((equal right (list *h1-book-arithmetic-reciprocal* left))
    (let* ((proof (h1-book-arithmetic-algebra-proof self))
           (lib (h1-tactics-prover-library proof)))
      (h1-book-arithmetic-with-algebra self
          ((inverse (library-library-axiom lib "INVERSE-OF-*" (list left)))
           (literal (proof-step-first inverse))
           (needed (proof-term-at literal 1)))
        (let* ((lookup (h1-book-arithmetic-algebra-find self needed))
               (premise (car lookup))
               (self (cdr lookup)))
          (if (or (not premise) (failure-p premise))
              lookup
            (cons (h1-propositions-propositional-proof-modus-ponens lib inverse premise) self))))))
   ((equal left (list *h1-book-arithmetic-reciprocal* right))
    (let* ((result (h1-book-arithmetic-algebra-cancel-reciprocal-loop (1- n) self right left))
           (inverse (car result))
           (self (cdr result)))
      (if (or (not inverse) (failure-p inverse))
          result
        (let ((base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
          (h1-book-arithmetic-with-algebra self
              ((swap (h1-book-arithmetic-algebra-commute self *proof-times* left right)))
            (cons (proof-proof-chain base swap (list inverse)) self))))))
   (t (cons nil self))))

(defun h1-book-arithmetic-algebra-cancel-reciprocal (self left right)
  (h1-book-arithmetic-algebra-cancel-reciprocal-loop 1000000 self left right))

(defun h1-book-arithmetic-algebra-fold (self head left right)
  (let* ((result (h1-book-arithmetic-algebra-constant-or-rewrite self (list head left right)))
         (fold (car result))
         (self (cdr result)))
    (cond (fold result)
          ((equal head *proof-plus*) (h1-book-arithmetic-algebra-collect self left right))
          (t (h1-book-arithmetic-algebra-cancel-reciprocal self left right)))))

(defun h1-book-arithmetic-algebra-apply-fold (self step head place left right rest suffix fold)
  (let ((base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
    (if (not suffix)
        (proof-proof-rewrite base step fold place)
      (proof-with-checked-results
          ((tail (proof-term-at rest 2))
           (law (h1-book-arithmetic-algebra-assoc self head left right tail))
           (law (h1-propositions-proof-symmetric base law))
           (step (proof-proof-rewrite base step law place)))
        (proof-proof-rewrite base step fold (append place '(1)))))))

(defun h1-book-arithmetic-algebra-equal-shortcut (self current)
  (let* ((lookup (h1-book-arithmetic-algebra-find self current))
         (known (car lookup))
         (self (cdr lookup))
         (proof (h1-book-arithmetic-algebra-proof self)))
    (cond ((failure-p known) lookup)
          (known (cons (h1-tactics-prover-equality-is-true proof known) self))
          (t
           (let* ((lookup (h1-book-arithmetic-algebra-find self (proof-neg current)))
                  (denied (car lookup))
                  (self (cdr lookup)))
             (if (failure-p denied)
                 lookup
               (cons (h1-tactics-prover-false-equation proof denied) self)))))))

(defun h1-book-arithmetic-algebra-shortcut (self head current)
  (let ((result (h1-book-arithmetic-algebra-constant-or-rewrite self current)))
    (if (or (car result) (not (equal head *proof-equal*)))
        result
      (h1-book-arithmetic-algebra-equal-shortcut (cdr result) current))))

(mutual-recursion
 (defun h1-book-arithmetic-algebra-normal-loop (n self term)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "h1-book-arithmetic-algebra-normal-loop") self)
     (let ((self (h1-book-arithmetic-algebra-with-work
                  self (1- (h1-book-arithmetic-algebra-work self)))))
       (if (< (h1-book-arithmetic-algebra-work self) 0)
           (cons '(:failure "Unproved" "") self)
         (let* ((proof (h1-book-arithmetic-algebra-proof self))
                (base (h1-tactics-prover-proof proof))
                (lib (h1-tactics-prover-library proof))
                (binding (table-get (h1-tactics-context-bindings
                                       (h1-book-arithmetic-algebra-context self))
                                      term nil))
                (head (h1-tactics-call-head term)))
           (cond
            (binding (h1-book-arithmetic-algebra-normal-follow (1- n) self binding nil))
            ((not (member-equal head (list *proof-plus* *proof-times* *proof-minus*
                                          *h1-book-arithmetic-fix*
                                          *h1-book-arithmetic-reciprocal* *proof-equal*)))
             (cons (h1-propositions-propositional-proof-reflexive lib term) self))
            ((equal head *proof-minus*)
             (h1-book-arithmetic-with-algebra self
                 ((arg (proof-term-at term 1))
                  (equation (proof-proof-fact
                             base (proof-sym "H1-MINUS-AS-PRODUCT" "ACL2")
                             (list (list *library-x* arg)))))
               (h1-book-arithmetic-algebra-normal-follow (1- n) self equation nil)))
            (t
             (h1-book-arithmetic-with-algebra self
                 ((step (h1-propositions-propositional-proof-reflexive lib term)))
               (h1-book-arithmetic-algebra-normal-args
                (1- n) self (cdr term) 1 step head)))))))))

 (defun h1-book-arithmetic-algebra-normal-follow (n self equation before)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "h1-book-arithmetic-algebra-normal-follow") self)
     (h1-book-arithmetic-with-algebra self
         ((term (h1-book-arithmetic-right-side equation)))
       (let* ((result (h1-book-arithmetic-algebra-normal-loop (1- n) self term))
              (step (car result))
              (self (cdr result))
              (base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
         (cond ((failure-p step) result)
               (before (cons (proof-proof-chain base before (list equation step)) self))
               (t (cons (proof-proof-chain base equation (list step)) self)))))))

 (defun h1-book-arithmetic-algebra-normal-args (n self args index step head)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "h1-book-arithmetic-algebra-normal-args") self))
    ((endp args) (h1-book-arithmetic-algebra-normal-reduce (1- n) self step head))
    (t
     (let* ((arg (car args))
            (result (h1-book-arithmetic-algebra-normal-loop (1- n) self arg))
            (normalized (car result))
            (self (cdr result))
            (base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
       (if (failure-p normalized)
           result
         (h1-book-arithmetic-with-algebra self
             ((right (h1-book-arithmetic-right-side normalized))
              (step (if (equal right arg)
                        step
                      (proof-proof-rewrite base step normalized (list 1 2 index)))))
           (h1-book-arithmetic-algebra-normal-args (1- n) self (cdr args) (1+ index) step head)))))))

 (defun h1-book-arithmetic-algebra-normal-reduce (n self step head)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "h1-book-arithmetic-algebra-normal-reduce") self)
     (h1-book-arithmetic-with-algebra self
         ((current (h1-book-arithmetic-right-side step)))
       (let* ((result (h1-book-arithmetic-algebra-shortcut self head current))
              (shortcut (car result))
              (self (cdr result))
              (base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
         (if (failure-p shortcut)
             result
           (h1-book-arithmetic-with-algebra self
               ((right (and shortcut (h1-book-arithmetic-right-side shortcut))))
             (cond
              ((and shortcut (not (equal right current)))
               (h1-book-arithmetic-algebra-normal-follow (1- n) self shortcut step))
              ((not (assoc-equal head *h1-book-arithmetic-operators*))
               (cons (proof-proof-tidy base step) self))
              (t
               (h1-book-arithmetic-with-algebra self
                   ((distribution (and (equal head *proof-times*)
                                       (h1-book-arithmetic-algebra-distribute self current))))
                 (if distribution
                     (h1-book-arithmetic-algebra-normal-follow (1- n) self distribution step)
                   (h1-book-arithmetic-with-algebra self
                       ((spine (h1-book-arithmetic-algebra-associate self step head))
                        (sorted (h1-book-arithmetic-algebra-sort self spine head)))
                     (h1-book-arithmetic-algebra-combine-loop
                      (1- n) self sorted head '(1 2)))))))))))))

 (defun h1-book-arithmetic-algebra-combine-loop (n self step head place)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "h1-book-arithmetic-algebra-combine-loop") self)
     (let ((base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
       (h1-book-arithmetic-with-algebra self
           ((node (h1-book-arithmetic-spine-node step place)))
         (if (not (proof-is-call node head))
             (cons (proof-proof-tidy base step) self)
           (h1-book-arithmetic-with-algebra self
               ((parts (proof-list-of-length (cdr node) 2))
                (left (car parts))
                (rest (cadr parts))
                (suffix (proof-is-call rest head))
                (right (if suffix (proof-term-at rest 1) rest)))
             (let* ((result (h1-book-arithmetic-algebra-fold self head left right))
                    (fold (car result))
                    (self (cdr result)))
               (if (failure-p fold)
                   result
                 (h1-book-arithmetic-with-algebra self
                     ((folded (and fold (h1-book-arithmetic-right-side fold))))
                   (if (or (not fold) (equal folded (list head left right)))
                       (h1-book-arithmetic-algebra-combine-loop
                        (1- n) self step head (append place '(2)))
                     (h1-book-arithmetic-with-algebra self
                         ((step (h1-book-arithmetic-algebra-apply-fold
                                 self step head place left right rest suffix fold)))
                       (h1-book-arithmetic-algebra-normal-follow
                        (1- n) self step nil)))))))))))))

(defun h1-book-arithmetic-algebra-normal (self term)
  (h1-book-arithmetic-algebra-normal-loop 1000000 self term))

(defun h1-book-arithmetic-algebra-combine (self step head)
  (h1-book-arithmetic-algebra-combine-loop 1000000 self step head '(1 2)))

(defun h1-book-arithmetic-algebra-equality (self left right)
  (let* ((left-result (h1-book-arithmetic-algebra-normal self left))
         (a (car left-result)))
    (if (failure-p a)
        left-result
      (let* ((right-result (h1-book-arithmetic-algebra-normal (cdr left-result) right))
             (b (car right-result))
             (self (cdr right-result))
             (base (h1-tactics-prover-proof (h1-book-arithmetic-algebra-proof self))))
        (if (failure-p b)
            right-result
          (h1-book-arithmetic-with-algebra self
              ((left-value (h1-book-arithmetic-right-side a))
               (right-value (h1-book-arithmetic-right-side b)))
            (if (not (equal left-value right-value))
                (cons '(:failure "Unproved" "") self)
              (h1-book-arithmetic-with-algebra self
                  ((reversed (h1-propositions-proof-symmetric base b)))
                (cons (proof-proof-chain base a (list reversed)) self)))))))))

(defun h1-book-arithmetic-difference (comparison)
  (proof-with-checked-results
      ((tail (h1-arithmetic-term-tail comparison))
       (parts (proof-list-of-length tail 2)))
    (library-diff (car parts) (cadr parts))))

(defun h1-book-arithmetic-algebra-order-finish
    (self earlier comparison candidate normalized equation negative)
  (let* ((proof (h1-book-arithmetic-algebra-proof self))
         (lib (h1-tactics-prover-library proof))
         (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((reverse-step (h1-propositions-proof-symmetric base equation))
         (equal-terms (proof-proof-chain base normalized (list reverse-step)))
         (equal-comparisons
          (h1-arithmetic-comparison-by-difference lib comparison candidate equal-terms)))
      (if negative
          (h1-propositions-library-transport-argument lib earlier equal-comparisons 1)
        (h1-propositions-proof-transport base earlier equal-comparisons)))))

(defun h1-book-arithmetic-algebra-order-candidate (self earlier comparison normalized negative)
  (h1-book-arithmetic-with-algebra self
      ((literal (and earlier (proof-step-first earlier)))
       (candidate (if negative
                      (and (proof-is-call literal *proof-not*) (proof-term-at literal 1))
                    literal)))
    (if (not (proof-is-call candidate *proof-less*))
        (cons nil self)
      (h1-book-arithmetic-with-algebra self
          ((difference (h1-book-arithmetic-difference candidate)))
        (let* ((result (h1-book-arithmetic-algebra-normal self difference))
               (equation (car result))
               (self (cdr result)))
          (if (failure-p equation)
              result
            (h1-book-arithmetic-with-algebra self
                ((left (h1-book-arithmetic-right-side normalized))
                 (right (h1-book-arithmetic-right-side equation)))
              (cons (and (equal left right)
                         (h1-book-arithmetic-algebra-order-finish
                          self earlier comparison candidate normalized equation negative))
                    self))))))))

(defun h1-book-arithmetic-algebra-order-evidence (result evidence comparison normalized negative)
  (declare (xargs :measure (acl2-count evidence)))
  (cond ((car result) result)
        ((endp evidence)
         (cons '(:failure "Unproved" "") (cdr result)))
        (t (h1-book-arithmetic-algebra-order-evidence
            (h1-book-arithmetic-algebra-order-candidate
             (cdr result) (car evidence) comparison normalized negative)
            (cdr evidence) comparison normalized negative))))

(defun h1-book-arithmetic-algebra-order (self goal)
  (let ((negative (proof-is-call goal *proof-not*)))
    (h1-book-arithmetic-with-algebra self
        ((comparison (if negative (proof-term-at goal 1) goal))
         (difference (h1-book-arithmetic-difference comparison)))
      (let* ((result (h1-book-arithmetic-algebra-normal self difference))
             (normalized (car result))
             (self (cdr result)))
        (if (failure-p normalized)
            result
          (h1-book-arithmetic-algebra-order-evidence
           (cons nil self) (table-values (h1-tactics-context-evidence
                                            (h1-book-arithmetic-algebra-context self)))
           comparison normalized negative))))))

(defun h1-book-arithmetic-premises (formula reversed)
  (declare (xargs :measure (acl2-count formula)))
  (if (not (proof-is-call formula *library-implies*))
      (cons formula reversed)
    (if (endp (cddr formula))
        (proof-term-at formula 2)
      (h1-book-arithmetic-premises (caddr formula) (cons formula reversed)))))

(defun h1-book-arithmetic-operator-occurs-p (terms)
  (if (endp terms)
      nil
    (or (member-equal (h1-tactics-call-head (car terms))
                      (list *proof-plus* *proof-times* *proof-minus*
                            *h1-book-arithmetic-fix* *h1-book-arithmetic-reciprocal*))
        (h1-book-arithmetic-operator-occurs-p (cdr terms)))))

(defun h1-book-arithmetic-premise-tests (premises)
  (if (endp premises)
      nil
    (cons (list (cadar premises) t)
          (h1-book-arithmetic-premise-tests (cdr premises)))))

(defun h1-book-arithmetic-restore-premises (lib reversed step)
  (if (or (endp reversed) (failure-p step))
      step
    (h1-book-arithmetic-restore-premises
     lib (cdr reversed) (h1-propositions-propositional-proof-implies-from lib (car reversed) step))))

(defun h1-book-arithmetic-algebraic-equality (proof self goal)
  (let ((lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results ((parts (proof-list-of-length (cdr goal) 2)))
      (let ((left (car parts))
            (right (cadr parts)))
        (proof-with-checked-results
            ((cancelled (and (proof-is-call goal *proof-equal*)
                             (h1-book-arithmetic-cancel-addend proof goal)))
             (step (cond (cancelled cancelled)
                         ((and (proof-is-call left *proof-less*)
                               (proof-is-call right *proof-less*))
                          (proof-with-checked-results
                              ((left-delta (h1-book-arithmetic-difference left))
                               (right-delta (h1-book-arithmetic-difference right))
                               (delta (car (h1-book-arithmetic-algebra-equality
                                            self left-delta right-delta))))
                            (h1-arithmetic-comparison-by-difference lib left right delta)))
                         (t (car (h1-book-arithmetic-algebra-equality self left right))))))
          (if (not (proof-is-call goal *h1-book-arithmetic-iff*))
              step
            (proof-with-checked-results
                ((reflexive (h1-tactics-prover-solve
                             proof (list *h1-book-arithmetic-iff* right right)
                             (list *h1-book-arithmetic-iff*) 160)))
              (h1-propositions-library-transport-argument lib reflexive step 1))))))))

(defun h1-book-arithmetic-algebraic-proof (proof formula)
  (proof-with-checked-results
      ((parts (h1-book-arithmetic-premises formula nil))
       (goal (car parts))
       (inner (and (proof-is-call goal *proof-not*) (proof-term-at goal 1))))
    (let ((order (or (proof-is-call goal *proof-less*) (proof-is-call inner *proof-less*)))
          (reversed (cdr parts)))
      (cond
       ((not (or order (proof-is-call goal *proof-equal*)
                 (proof-is-call goal *h1-book-arithmetic-iff*)))
        '(:failure "Unproved" ""))
       ((not (h1-book-arithmetic-operator-occurs-p (h1-tactics-subterms goal)))
        '(:failure "Unproved" ""))
       (t
        (proof-with-checked-results
            ((self (h1-book-arithmetic-algebra-init
                    proof (h1-book-arithmetic-premise-tests (reverse reversed)) nil))
             (step (if order
                       (car (h1-book-arithmetic-algebra-order self goal))
                     (h1-book-arithmetic-algebraic-equality proof self goal))))
          (h1-book-arithmetic-restore-premises
           (h1-tactics-prover-library proof) reversed step)))))))
