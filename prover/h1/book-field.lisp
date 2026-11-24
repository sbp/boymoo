(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-field-inverse-unique* (proof-sym "H1-INVERSE-UNIQUE" "ACL2"))

(defun h1-book-field-fixed (term)
  (list *h1-book-arithmetic-fix* term))

(defun h1-book-field-reciprocal (term)
  (list *h1-book-arithmetic-reciprocal* term))

(defun h1-book-field-find (normalizer literal)
  (proof-with-checked-results
      ((found (h1-tactics-context-find
               (h1-book-arithmetic-algebra-context normalizer) literal)))
    (cons (car found)
          (h1-book-arithmetic-algebra-with-context normalizer (cdr found)))))

(defun h1-book-field-require (normalizer literal)
  (proof-with-checked-results ((found (h1-book-field-find normalizer literal)))
    (if (car found)
        found
      '(:failure "Unproved" ""))))

(defun h1-book-field-remember (normalizer steps)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      normalizer
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (let* ((context (h1-book-arithmetic-algebra-context normalizer))
             (evidence (h1-tactics-context-evidence context))
             (updated (h1-tactics-context-with-evidence
                       context (table-put evidence literal (car steps)))))
        (proof-with-checked-results
            ((bound (h1-tactics-context-bind-equality updated (car steps))))
          (h1-book-field-remember
           (h1-book-arithmetic-algebra-with-context normalizer bound)
           (cdr steps)))))))

(defun h1-book-field-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun h1-book-field-search (proof term tests)
  (proof-with-checked-results
      ((search (h1-tactics-search-init proof nil nil nil nil 160 nil))
       (result (h1-tactics-search-prove search term tests t)))
    (car result)))

(defun h1-book-field-fixing-equation (proof operation arguments)
  (let* ((logic (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (term (cons operation (cons *library-x* arguments)))
         (fixed-term (cons operation (cons (h1-book-field-fixed *library-x*) arguments)))
         (numeric (list *library-numberp* *library-x*)))
    (proof-with-checked-results
        ((assumed-number (h1-arithmetic-proof-assume logic numeric t))
         (yes-fix (h1-book-arithmetic-collapse-fix proof *library-x* assumed-number))
         (assumed-nonnumber (h1-arithmetic-proof-assume logic numeric nil))
         (no-fix (h1-book-arithmetic-collapse-fix proof *library-x* assumed-nonnumber))
         (reflexive (h1-propositions-propositional-proof-reflexive lib term))
         (reversed-fix (h1-propositions-proof-symmetric logic yes-fix))
         (yes (proof-proof-rewrite logic reflexive reversed-fix '(1 2 1)))
         (no (h1-book-field-search proof (proof-eq term *proof-zero*)
                                  (list (list numeric nil))))
         (fixed-reflexive (h1-propositions-propositional-proof-reflexive lib fixed-term))
         (fixed-default (proof-proof-rewrite logic fixed-reflexive no-fix '(1 2 1)))
         (default-term (h1-book-field-step-right fixed-default))
         (default-zero (h1-tactics-prover-solve
                        proof (proof-eq default-term *proof-zero*) nil 160))
         (default-value (proof-proof-chain logic fixed-default (list default-zero)))
         (reversed-default (h1-propositions-proof-symmetric logic default-value))
         (no-case (proof-proof-chain logic no (list reversed-default))))
      (proof-proof-cases logic numeric yes no-case))))

(defun h1-book-field-add-rule (proof step)
  (proof-with-checked-results
      ((rules (h1-tactics-rules-add (h1-tactics-prover-rules proof) step t t)))
    (h1-tactics-prover-with-rules proof rules)))

(defun h1-book-field-add-symmetric-zero-rules (proof alternatives symmetry)
  (declare (xargs :measure (acl2-count alternatives)))
  (if (endp alternatives)
      proof
    (proof-with-checked-results
        ((step (proof-proof-rewrite (h1-tactics-prover-proof proof)
                                   (car alternatives) symmetry '(2 1)))
         (updated (h1-book-field-add-rule proof step)))
      (h1-book-field-add-symmetric-zero-rules updated (cdr alternatives) symmetry))))

(defun h1-book-field-product-zero-rules (proof lemma symmetry)
  (let ((logic (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*"
                                         (list *library-y* *library-x*)))
         (swapped (proof-proof-chain logic commute (list lemma)))
         (updated (h1-book-field-add-rule proof swapped)))
      (h1-book-field-add-symmetric-zero-rules updated (list lemma swapped) symmetry))))

(defun h1-book-field-fixed-zero-operation (proof label operation arguments fixed-zero symmetry)
  (let ((logic (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((on-fixed (h1-book-field-fixing-equation proof operation arguments))
         (assumed-zero (h1-arithmetic-proof-assume logic fixed-zero t))
         (equation (proof-proof-rewrite logic on-fixed assumed-zero '(1 2 1)))
         (rhs (h1-book-field-step-right equation))
         (zero-value (h1-tactics-prover-solve proof (proof-eq rhs *proof-zero*) nil 160))
         (value (proof-proof-chain logic equation (list zero-value)))
         (lemma (h1-tactics-prover-helper proof label value (list (proof-neg fixed-zero)) t)))
      (if (equal operation *proof-times*)
          (h1-book-field-product-zero-rules (cdr lemma) (car lemma) symmetry)
        (h1-book-field-add-symmetric-zero-rules (cdr lemma) (list (car lemma)) symmetry)))))

(defun h1-book-field-fixed-zero-rules (proof)
  (let* ((logic (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (numeric (list *library-numberp* *library-x*))
         (fixed-zero (proof-eq (h1-book-field-fixed *library-x*) *proof-zero*))
         (zero (proof-eq *library-x* *proof-zero*)))
    (proof-with-checked-results
        ((assumed-nonnumber (h1-arithmetic-proof-assume logic numeric nil))
         (nonnumber (h1-book-arithmetic-collapse-fix proof *library-x* assumed-nonnumber))
         (fixed-at-zero (h1-tactics-prover-solve
                         proof (proof-eq (h1-book-field-fixed *proof-zero*) *proof-zero*) nil 160))
         (assumed-zero (h1-arithmetic-proof-assume logic zero t))
         (reversed-zero (h1-propositions-proof-symmetric logic assumed-zero))
         (fixed-if-zero (proof-proof-rewrite logic fixed-at-zero reversed-zero '(1 1 1)))
         (symmetry (library-library-axiom lib "H1-EQUALITY-SYMMETRIC-VALUE"
                                         (list (h1-book-field-fixed *library-x*) *proof-zero*)))
         (typed (proof-proof-front logic nonnumber numeric))
         (nonzero (proof-proof-front logic fixed-if-zero (proof-neg zero)))
         (type-literal (proof-step-first typed))
         (type-lib (library-library-lemma lib "FIX-NONZERO-NUMBER"
                                          type-literal typed (list fixed-zero)))
         (argument-literal (proof-step-first nonzero))
         (argument-lib (library-library-lemma type-lib "FIX-NONZERO-ARGUMENT"
                                              argument-literal nonzero (list fixed-zero)))
         (with-lemmas (h1-tactics-prover-with-library proof argument-lib))
         (with-product (h1-book-field-fixed-zero-operation
                        with-lemmas "PRODUCT-FIX-ZERO" *proof-times*
                        (list *library-y*) fixed-zero symmetry)))
      (h1-book-field-fixed-zero-operation
       with-product "RECIPROCAL-FIX-ZERO" *h1-book-arithmetic-reciprocal*
       nil fixed-zero symmetry))))

(defun h1-book-field-reject-zero-product (proof one zero conclusion)
  (let ((logic (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((rewritten (proof-proof-rewrite logic one zero '(1 1)))
         (conflict (proof-proof-tidy logic rewritten))
         (not-nil (proof-proof-not-nil logic))
         (computed (proof-proof-compute logic (proof-eq *proof-zero* *proof-one*) *proof-nil*))
         (unequal (h1-propositions-library-transport-argument lib not-nil computed 1))
         (result (proof-proof-cut logic conflict unequal)))
      (proof-proof-front logic result conclusion))))

(defun h1-book-field-inverse-unique (proof)
  (let* ((logic (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (product (h1-book-order-product *library-x* *library-y*))
         (premise (proof-eq product *proof-one*))
         (nx (list *library-numberp* *library-x*))
         (ny (list *library-numberp* *library-y*))
         (zero-test (proof-eq *library-x* *proof-zero*))
         (nonzero-x (proof-neg zero-test))
         (inv (h1-book-field-reciprocal *library-x*)))
    (proof-with-checked-results
        ((one (h1-arithmetic-proof-assume logic premise t))
         (false-x (h1-book-field-search proof (proof-eq product *proof-zero*)
                                      (list (list nx nil))))
         (known-x (h1-book-field-reject-zero-product proof one false-x nx))
         (false-y (h1-book-field-search proof (proof-eq product *proof-zero*)
                                      (list (list ny nil))))
         (known-y (h1-book-field-reject-zero-product proof one false-y ny))
         (zero-x (h1-tactics-prover-solve
                  proof (proof-eq (h1-book-order-product *proof-zero* *library-y*) *proof-zero*) nil 160))
         (assumed-zero (h1-arithmetic-proof-assume logic zero-test t))
         (reversed-zero (h1-propositions-proof-symmetric logic assumed-zero))
         (zero-product (proof-proof-rewrite logic zero-x reversed-zero '(1 1 1)))
         (not-zero (h1-book-field-reject-zero-product proof one zero-product nonzero-x))
         (inverse (library-library-axiom lib "INVERSE-OF-*" (list *library-x*)))
         (inverse-claim (proof-step-first inverse))
         (inverse-premise (proof-term-at inverse-claim 1))
         (known (h1-propositions-propositional-proof-conjoin lib inverse-premise known-x not-zero))
         (inverse-step (h1-propositions-propositional-proof-modus-ponens lib inverse known))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list inv *library-x*)))
         (reversed-inverse (proof-proof-chain logic commute (list inverse-step)))
         (left-unit (library-library-axiom lib "UNICITY-OF-1" (list *library-y*)))
         (fix-y (h1-book-arithmetic-collapse-fix proof *library-y* known-y))
         (unit (proof-proof-chain logic left-unit (list fix-y)))
         (from-y (h1-propositions-proof-symmetric logic unit))
         (to-product (h1-propositions-proof-symmetric logic reversed-inverse))
         (start (proof-proof-rewrite logic from-y to-product '(1 2 1)))
         (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                          (list inv *library-x* *library-y*)))
         (middle (proof-proof-chain logic start (list associate)))
         (with-one (proof-proof-rewrite logic middle one '(1 2 2)))
         (right-unit (h1-book-arithmetic-right-unit proof *proof-times* inv))
         (number-inv (h1-tactics-prover-solve proof (list *library-numberp* inv) nil 160))
         (fix-inv (h1-book-arithmetic-collapse-fix proof inv number-inv)))
      (proof-proof-chain logic with-one (list right-unit fix-inv)))))

(defun h1-book-field-normalized-inverse-cases (arguments tests regular proof base candidate)
  (declare (xargs :measure (acl2-count arguments)))
  (proof-with-checked-results
      ((normalizer (h1-book-arithmetic-algebra-init proof tests nil)))
    (let ((logic (h1-tactics-prover-proof proof)))
      (cond
       ((not regular)
        (car (h1-book-arithmetic-algebra-equality
              normalizer (h1-book-field-reciprocal base) candidate)))
       ((endp arguments)
        (proof-with-checked-results
            ((identity (car (h1-book-arithmetic-algebra-equality
                             normalizer (h1-book-order-product base candidate) *proof-one*)))
             (inverse (proof-proof-use logic *h1-book-field-inverse-unique*
                                       (list (list *library-x* base) (list *library-y* candidate))
                                       (list identity)))
             (reversed (h1-propositions-proof-symmetric logic inverse)))
          (proof-proof-tidy logic reversed)))
       (t (let* ((argument (car arguments))
                 (numeric (list *library-numberp* argument))
                 (zero (proof-eq argument *proof-zero*))
                 (good (append tests (list (list numeric t)))))
            (proof-with-checked-results
                ((nonzero (h1-book-field-normalized-inverse-cases
                           (cdr arguments) (append good (list (list zero nil)))
                           t proof base candidate))
                 (zeros (h1-book-field-normalized-inverse-cases
                         (cdr arguments) (append good (list (list zero t)))
                         nil proof base candidate))
                 (other (h1-book-field-normalized-inverse-cases
                         (cdr arguments) (append tests (list (list numeric nil)))
                         nil proof base candidate))
                 (numeric-case (proof-proof-cases logic zero zeros nonzero)))
              (proof-proof-cases logic numeric numeric-case other))))))))

(defun h1-book-field-normalized-inverse (proof base candidate arguments)
  (h1-book-field-normalized-inverse-cases arguments nil t proof base candidate))

(defun h1-book-field-install-nonnumber (proof swaps)
  (let ((logic (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof))
        (xy (list *library-x* *library-y*)))
    (proof-with-checked-results
        ((completion (library-library-axiom lib "COMPLETION-OF-*" xy))
         (completion-value (h1-book-field-step-right completion))
         (if-false (h1-arithmetic-proof-if-false logic completion-value))
         (first (proof-proof-chain logic completion (list if-false)))
         (left (h1-tactics-prover-helper proof "PRODUCT-NONNUMBER" first
                                         (cdr (proof-step-clause first)) t)))
      (let* ((updated (cdr left))
             (logic (h1-tactics-prover-proof updated))
             (lib (h1-tactics-prover-library updated)))
        (proof-with-checked-results
            ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" xy))
             (swapped (proof-proof-instantiate logic (car left) swaps))
             (right (proof-proof-chain logic commute (list swapped))))
          (h1-book-field-add-rule updated right))))))

(defun h1-book-field-unfix-swapped (proof lemma operator-name swaps)
  (let ((logic (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((front (library-library-axiom lib operator-name
                                        (list *library-x* (h1-book-field-fixed *library-y*))))
         (swapped (proof-proof-instantiate logic lemma swaps))
         (back (library-library-axiom lib operator-name (list *library-y* *library-x*)))
         (equation (proof-proof-chain logic front (list swapped back))))
      (h1-book-field-add-rule proof equation))))

(defun h1-book-field-install-unfix (proof label operation arguments swaps)
  (let ((logic (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((equation (h1-book-field-fixing-equation proof operation arguments))
         (reversed (h1-propositions-proof-symmetric logic equation))
         (lemma (h1-tactics-prover-helper proof label reversed nil t)))
      (if (equal operation *proof-times*)
          (h1-book-field-unfix-swapped (cdr lemma) (car lemma) "COMMUTATIVITY-OF-*" swaps)
        (cdr lemma)))))

(defun h1-book-field-install-sum (proof swaps)
  (let ((logic (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((sum-fixed (library-library-axiom lib "H1-SUM-WITH-FIX" (list *library-x* *library-y*)))
         (reversed (h1-propositions-proof-symmetric logic sum-fixed))
         (updated (h1-book-field-add-rule proof reversed)))
      (h1-book-field-unfix-swapped updated reversed "COMMUTATIVITY-OF-+" swaps))))

(defun h1-book-field-install-inverse (proof label base value arguments)
  (proof-with-checked-results
      ((equation (h1-book-field-normalized-inverse proof base value arguments))
       (result (h1-tactics-prover-helper proof label equation nil t)))
    (cdr result)))

(defun h1-book-field-install-field (proof)
  (let* ((x *library-x*)
         (y *library-y*)
         (swaps (list (list x y) (list y x)))
         (product (h1-book-order-product x y)))
    (proof-with-checked-results
        ((nonnumber (h1-book-field-install-nonnumber proof swaps))
         (product-unfix (h1-book-field-install-unfix nonnumber "PRODUCT-UNFIX"
                                                     *proof-times* (list y) swaps))
         (reciprocal-unfix (h1-book-field-install-unfix product-unfix "RECIPROCAL-UNFIX"
                                                        *h1-book-arithmetic-reciprocal* nil swaps))
         (sum (h1-book-field-install-sum reciprocal-unfix swaps))
         (fixed-zero (h1-book-field-fixed-zero-rules sum))
         (unique-inverse (h1-book-field-inverse-unique fixed-zero))
         (unique-rule (h1-tactics-prover-helper fixed-zero "INVERSE-UNIQUE" unique-inverse
                                                (list (proof-neg (proof-eq product *proof-one*))) nil))
         (involution (h1-book-field-install-inverse
                      (cdr unique-rule) "RECIPROCAL-INVOLUTION"
                      (h1-book-field-reciprocal x) (h1-book-field-fixed x) (list x)))
         (product-rule (h1-book-field-install-inverse
                        involution "RECIPROCAL-PRODUCT" product
                        (h1-book-order-product (h1-book-field-reciprocal x)
                                               (h1-book-field-reciprocal y))
                        (list x y))))
      (h1-book-field-install-inverse product-rule "RECIPROCAL-NEGATION" (library-minus x)
                                     (library-minus (h1-book-field-reciprocal x)) (list x)))))

(defun h1-book-field-expression-subterms (expressions)
  (declare (xargs :measure (acl2-count expressions)))
  (if (endp expressions)
      nil
    (append (h1-tactics-subterms (car expressions))
            (h1-book-field-expression-subterms (cdr expressions)))))

(defun h1-book-field-transformation-terms (terms factors summands minus reciprocal)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      (list (reverse factors) (reverse summands) minus reciprocal)
    (let ((head (h1-tactics-call-head (car terms)))
          (arguments (cdar terms)))
      (h1-book-field-transformation-terms
       (cdr terms)
       (if (or (equal head *proof-times*) (equal head *h1-book-arithmetic-reciprocal*))
           (revappend arguments factors)
         factors)
       (if (equal head *proof-plus*) (revappend arguments summands) summands)
       (or minus (equal head *proof-minus*))
       (or reciprocal (equal head *h1-book-arithmetic-reciprocal*))))))

(defun h1-book-field-factor-transformations (factors)
  (declare (xargs :measure (acl2-count factors)))
  (if (endp factors)
      nil
    (let ((factor (car factors)))
      (list* (list :multiply factor)
             (list :multiply (h1-book-field-reciprocal factor))
             (h1-book-field-factor-transformations (cdr factors))))))

(defun h1-book-field-summand-transformations (summands)
  (declare (xargs :measure (acl2-count summands)))
  (if (endp summands)
      nil
    (let ((summand (car summands)))
      (list* (list :add summand)
             (list :add (library-minus summand))
             (h1-book-field-summand-transformations (cdr summands))))))

; A product or sum transformation stores the term for its left operand.
(defun h1-book-field-transformations (left right)
  (let* ((expressions (append (cdr left) (cdr right)))
         (terms (h1-book-field-expression-subterms expressions))
         (parts (h1-book-field-transformation-terms terms nil nil nil nil))
         (factors (if (caddr parts)
                      (append (car parts) (list *proof-neg-one*))
                    (car parts)))
         (summands (cadr parts)))
    (cons :identity
          (append (and (cadddr parts) (list :reciprocal))
                  (h1-book-field-factor-transformations
                   (seq-slice (proof-unique factors) :none 6))
                  (h1-book-field-summand-transformations
                   (seq-slice (proof-unique summands) :none 6))))))

(defun h1-book-field-apply-transformation (change value)
  (cond ((eq change :identity) value)
        ((eq change :reciprocal) (h1-book-field-reciprocal value))
        ((eq (car change) :multiply) (h1-book-order-product (cadr change) value))
        (t (library-plus (cadr change) value))))

(defun h1-book-field-cite-nonzero (proof assumption left right)
  (if (and (proof-is-call left *h1-book-arithmetic-fix*) (equal right *proof-zero*))
      (let ((lib (h1-tactics-prover-library proof)))
        (proof-with-checked-results
            ((argument (proof-term-at left 1))
             (typed (library-library-cite lib "FIX-NONZERO-NUMBER"
                                          (list argument) (list assumption)))
             (nonzero (library-library-cite lib "FIX-NONZERO-ARGUMENT"
                                             (list argument) (list assumption))))
          (list typed nonzero)))
    nil))

(defun h1-book-field-fixed-evidence (proof assumption)
  (proof-with-checked-results ((literal (proof-step-first assumption)))
    (if (not (proof-is-call literal *proof-not*))
        nil
      (proof-with-checked-results ((equation (proof-term-at literal 1)))
        (if (not (proof-is-call equation *proof-equal*))
            nil
          (proof-with-checked-results ((args (proof-list-of-length (cdr equation) 2)))
            (let ((left (car args))
                  (right (cadr args)))
              (if (and (equal left *proof-zero*) (proof-is-call right *h1-book-arithmetic-fix*))
                  (let ((logic (h1-tactics-prover-proof proof))
                        (lib (h1-tactics-prover-library proof)))
                    (proof-with-checked-results
                        ((symmetry (library-library-axiom lib "H1-EQUALITY-SYMMETRIC-VALUE"
                                                          (list left right)))
                         (rewritten (proof-proof-rewrite logic assumption symmetry '(1 1)))
                         (swapped (proof-proof-tidy logic rewritten)))
                      (h1-book-field-cite-nonzero proof swapped right left)))
                (h1-book-field-cite-nonzero proof assumption left right)))))))))

(defun h1-book-field-test-evidence (proof test holds)
  (let ((logic (h1-tactics-prover-proof proof)))
    (proof-with-checked-results ((assumption (h1-arithmetic-proof-assume logic test holds)))
      (if (and (not holds) (proof-is-call test *proof-not*))
          (proof-with-checked-results
              ((inner (proof-term-at test 1))
               (negated (h1-arithmetic-proof-assume logic inner nil))
               (combined (proof-proof-cut logic negated assumption))
               (extra (h1-book-field-fixed-evidence proof combined)))
            (cons combined extra))
        (h1-book-field-fixed-evidence proof assumption)))))

(defun h1-book-field-normalizer-evidence (proof tests)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (current (h1-book-field-test-evidence proof (car pair) (cadr pair)))
         (rest (h1-book-field-normalizer-evidence proof (cdr tests))))
      (append current rest))))

(defun h1-book-field-field-normalizer (proof tests)
  (proof-with-checked-results
      ((evidence (h1-book-field-normalizer-evidence proof tests))
       (normalizer (h1-book-arithmetic-algebra-init proof tests evidence)))
    (h1-book-order-add-signed-evidence proof normalizer)))

(defun h1-book-field-unproved-p (value)
  (and (failure-p value) (equal (cadr value) "Unproved")))

(defun h1-book-field-imply-lift (proof first given last left change swap)
  (let ((logic (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((reflexive (h1-propositions-propositional-proof-reflexive lib left))
         (lifted (proof-proof-rewrite-result
                  logic reflexive given
                  (proof-eq left (h1-book-field-apply-transformation change *proof-result*))
                  *proof-result*))
         (result (proof-proof-chain logic first (list lifted last))))
      (if swap
          (proof-with-checked-results ((reversed (h1-propositions-proof-symmetric logic result)))
            (proof-proof-tidy logic reversed))
        result))))

; A failed alignment leaves the Algebra for the next orientation.
(defun h1-book-field-imply-direction (proof normalizer given start end left right change swap)
  (let* ((first (h1-book-arithmetic-algebra-equality normalizer start left))
         (first-step (car first)))
    (cond ((h1-book-field-unproved-p first-step) (cons nil (cdr first)))
          ((failure-p first-step) first-step)
          (t
           (let* ((last (h1-book-arithmetic-algebra-equality (cdr first) right end))
                  (last-step (car last)))
             (cond
              ((h1-book-field-unproved-p last-step) (cons nil (cdr last)))
              ((failure-p last-step) last-step)
              (t (proof-with-checked-results
                     ((result (h1-book-field-imply-lift proof first-step given last-step left change swap)))
                   (cons result (cdr last))))))))))

(defun h1-book-field-imply-transformations (changes proof given antecedent conclusion tests)
  (declare (xargs :measure (acl2-count changes)))
  (if (endp changes)
      '(:failure "Unproved" "")
    (let ((change (car changes)))
      (proof-with-checked-results
          ((normalizer (h1-book-field-field-normalizer proof tests))
           (operands (proof-list-of-length (cdr antecedent) 2))
           (start (proof-term-at conclusion 1))
           (end (proof-term-at conclusion 2)))
        (let ((left (h1-book-field-apply-transformation change (car operands)))
              (right (h1-book-field-apply-transformation change (cadr operands))))
          (proof-with-checked-results
              ((direct (h1-book-field-imply-direction
                        proof normalizer given start end left right change nil)))
            (if (car direct)
                (car direct)
              (proof-with-checked-results
                  ((reverse (h1-book-field-imply-direction
                             proof (cdr direct) given end start left right change t)))
                (if (car reverse)
                    (car reverse)
                  (h1-book-field-imply-transformations
                   (cdr changes) proof given antecedent conclusion tests))))))))))

(defun h1-book-field-imply-reciprocal (proof given antecedent base inverse)
  (let* ((logic (h1-tactics-prover-proof proof))
         (product (h1-book-order-product base inverse))
         (multiplies-to-one (proof-eq product *proof-one*)))
    (if (or (equal antecedent multiplies-to-one)
            (equal antecedent (proof-eq *proof-one* product)))
        (proof-with-checked-results
            ((one (if (equal antecedent multiplies-to-one)
                      given
                    (h1-propositions-proof-symmetric logic given)))
             (result (proof-proof-use logic *h1-book-field-inverse-unique*
                                       (list (list *library-x* base) (list *library-y* inverse))
                                       (list one)))
             (reversed (h1-propositions-proof-symmetric logic result)))
          (proof-proof-tidy logic reversed))
      nil)))

(defun h1-book-field-imply-equality (proof antecedent conclusion tests)
  (let ((logic (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((given (h1-arithmetic-proof-assume logic antecedent t))
         (left (proof-term-at conclusion 1))
         (reciprocal
          (if (proof-is-call left *h1-book-arithmetic-reciprocal*)
              (proof-with-checked-results ((base (proof-term-at left 1))
                                           (inverse (proof-term-at conclusion 2)))
                (h1-book-field-imply-reciprocal proof given antecedent base inverse))
            nil)))
      (if reciprocal
          reciprocal
        (h1-book-field-imply-transformations
         (h1-book-field-transformations antecedent conclusion) proof given antecedent conclusion tests)))))

(defun h1-book-field-equality-false-step (proof left index typed opposite)
  (let ((logic (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((assumed (h1-arithmetic-proof-assume logic left t))
         (equality (if (equal index 2)
                       (h1-propositions-proof-symmetric logic assumed)
                     assumed))
         (rewritten (proof-proof-rewrite logic typed equality '(1 1)))
         (disputed (proof-proof-tidy logic rewritten))
         (cut (proof-proof-cut logic disputed opposite))
         (denied (proof-proof-front logic cut (proof-neg left))))
      (h1-tactics-prover-false-equation proof denied))))

(defun h1-book-field-equality-false (operands proof left index normalizer)
  (declare (xargs :measure (acl2-count operands)))
  (if (endp operands)
      '(:failure "Unproved" "")
    (let ((opposite-index (- 3 index)))
      (proof-with-checked-results
          ((typed (h1-book-field-find normalizer (list *library-numberp* (car operands))))
           (other (proof-term-at left (if (< opposite-index 0)
                                          (+ (len left) opposite-index)
                                        opposite-index)))
           (opposite (h1-book-field-find
                      (cdr typed) (proof-neg (list *library-numberp* other)))))
        (if (and (car typed) (car opposite))
            (h1-book-field-equality-false-step proof left index (car typed) (car opposite))
          (h1-book-field-equality-false (cdr operands) proof left (1+ index) (cdr opposite)))))))

(defun h1-book-field-order-known (proof source other reversed normalizer)
  (proof-with-checked-results
      ((positive (h1-book-field-find normalizer other))
       (known (if (car positive)
                  positive
                (h1-book-field-find (cdr positive) (proof-neg other)))))
    (if (not (car known))
        known
      (proof-with-checked-results
          ((boolean (h1-book-order-boolean-value proof (car known)))
           (value (h1-book-field-step-right boolean)))
        (let* ((attempt (h1-book-order-compare-value proof source value (cdr known)))
               (match (car attempt))
               (logic (h1-tactics-prover-proof proof)))
          (cond
           ((h1-book-field-unproved-p match) (cons nil (cdr attempt)))
           ((failure-p match) match)
           (t (proof-with-checked-results
                   ((reversed-value (h1-propositions-proof-symmetric logic boolean))
                    (result (proof-proof-chain logic match (list reversed-value)))
                    (swapped (if reversed (h1-propositions-proof-symmetric logic result) result))
                    (step (if reversed (proof-proof-tidy logic swapped) swapped)))
                 (cons step (cdr attempt))))))))))

(defun h1-book-field-order-test-present (tests lower higher)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      nil
    (proof-with-checked-results ((pair (proof-list-of-length (car tests) 2)))
      (or (equal (car pair) lower)
          (equal (car pair) higher)
          (h1-book-field-order-test-present (cdr tests) lower higher)))))

(defun h1-book-field-order-split-candidate (term source other tests normalizer)
  (if (and (proof-is-call term *h1-book-arithmetic-reciprocal*)
           (member-equal *proof-zero* source))
      (proof-with-checked-results ((divisor (proof-term-at term 1)))
        (if (and (member-equal *proof-zero* other) (member-equal divisor other))
            (let ((lower (library-lt divisor *proof-zero*))
                  (higher (library-positive divisor)))
              (proof-with-checked-results
                  ((present (h1-book-field-order-test-present tests lower higher)))
                (if present
                    (cons nil normalizer)
                  (proof-with-checked-results
                      ((rational (h1-book-field-find normalizer (h1-book-order-rational divisor))))
                    (cons (and (car rational) (list :split lower higher)) (cdr rational))))))
          (cons nil normalizer)))
    (cons nil normalizer)))

(defun h1-book-field-order-split-terms (terms source other tests normalizer)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      (cons nil normalizer)
    (proof-with-checked-results
        ((found (h1-book-field-order-split-candidate (car terms) source other tests normalizer)))
      (if (car found)
          found
        (h1-book-field-order-split-terms (cdr terms) source other tests (cdr found))))))

; A sign split supplies its two tests in place of a completed Step.
(defun h1-book-field-order-alternatives (directions proof tests normalizer)
  (declare (xargs :measure (acl2-count directions)))
  (if (endp directions)
      (cons '(:failure "Unproved" "") normalizer)
    (let* ((direction (car directions))
           (source (car direction))
           (other (cadr direction))
           (reversed (caddr direction)))
      (proof-with-checked-results
          ((known (h1-book-field-order-known proof source other reversed normalizer)))
        (if (car known)
            known
          (proof-with-checked-results
              ((split (h1-book-field-order-split-terms
                       (cdr source) (cdr source) (cdr other) tests (cdr known))))
            (if (car split)
                split
              (h1-book-field-order-alternatives (cdr directions) proof tests (cdr split)))))))))

(defun h1-book-field-equality-of-equalities (proof left right tests)
  (proof-with-checked-results
      ((forward (h1-book-field-imply-equality proof left right tests))
       (reverse (h1-book-field-imply-equality proof right left tests)))
    (h1-book-arithmetic-same-equality-value proof left right forward reverse)))

(defun h1-book-field-by-value-join (proof value template yes no)
  (let ((logic (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((if-true (h1-arithmetic-proof-if-true logic value))
         (true-equality (h1-propositions-proof-symmetric logic if-true))
         (yes-proof (proof-proof-rewrite-result logic yes true-equality template *proof-result*))
         (if-false (h1-arithmetic-proof-if-false logic value))
         (false-equality (h1-propositions-proof-symmetric logic if-false))
         (no-proof (proof-proof-rewrite-result logic no false-equality template *proof-result*)))
      (proof-proof-cases logic (cadr value) yes-proof no-proof))))

(mutual-recursion
 (defun h1-book-field-field-equality (n proof left right tests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-field-field-equality"))
    ((proof-is-call left *proof-if*)
     (h1-book-field-field-equality-by-value
      (1- n) proof left right tests t (proof-eq *proof-result* right)))
    ((proof-is-call right *proof-if*)
     (h1-book-field-field-equality-by-value
      (1- n) proof right left tests nil (proof-eq left *proof-result*)))
    ((proof-is-call right *h1-book-arithmetic-iff*)
     (let ((logic (h1-tactics-prover-proof proof)))
       (proof-with-checked-results
           ((equation (proof-proof-unfold logic right))
            (opened (h1-book-field-step-right equation))
            (expanded (h1-book-field-field-equality (1- n) proof left opened tests))
            (reversed (h1-propositions-proof-symmetric logic equation)))
         (proof-proof-chain logic expanded (list reversed)))))
    (t (proof-with-checked-results
           ((normalizer (h1-book-field-field-normalizer proof tests)))
         (let* ((attempt (h1-book-arithmetic-algebra-equality normalizer left right))
                (step (car attempt))
                (updated (cdr attempt)))
           (cond
            ((not (h1-book-field-unproved-p step)) step)
            ((and (proof-is-call left *proof-less*)
                  (or (equal right *proof-true*) (equal right *proof-false*)))
             (car (h1-book-order-compare-value proof left right updated)))
            ((and (proof-is-call left *proof-less*) (proof-is-call right *proof-less*))
             (proof-with-checked-results
                 ((result (h1-book-field-field-order (1- n) proof left right tests updated)))
               (car result)))
            ((and (proof-is-call left *proof-equal*) (proof-is-call right *proof-equal*))
             (h1-book-field-equality-of-equalities proof left right tests))
            ((and (proof-is-call left *proof-equal*) (equal right *proof-false*))
             (h1-book-field-equality-false (cdr left) proof left 1 updated))
            (t '(:failure "Unproved" ""))))))))

 (defun h1-book-field-field-equality-by-value (n proof value other tests leftp template)
   (declare (xargs :measure (nfix n)))
   (let ((logic (h1-tactics-prover-proof proof)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-field-field-equality-by-value"))
      ((proof-is-call value *proof-if*)
       (proof-with-checked-results
           ((branches (proof-list-of-length (cdr value) 3))
            (yes (h1-book-field-field-equality-by-value
                  (1- n) proof (cadr branches) other (append tests (list (list (car branches) t)))
                  leftp template))
            (no (h1-book-field-field-equality-by-value
                 (1- n) proof (caddr branches) other (append tests (list (list (car branches) nil)))
                 leftp template)))
         (h1-book-field-by-value-join proof value template yes no)))
      ((and (proof-compound value) (endp value))
       '(:failure "failure" ""))
      ((and (proof-compound value) (proof-compound (car value)))
       (proof-with-checked-results
           ((equation (proof-proof-beta logic value))
            (opened (h1-book-field-step-right equation))
            (step (h1-book-field-field-equality-by-value (1- n) proof opened other tests leftp template))
            (reversed (h1-propositions-proof-symmetric logic equation)))
         (proof-proof-rewrite-result logic step reversed template *proof-result*)))
      (t (proof-with-checked-results
             ((step (if leftp
                        (h1-book-field-field-equality (1- n) proof value other tests)
                      (h1-book-field-field-equality (1- n) proof other value tests)))
              (literal (proof-step-first step))
              (expected (proof-subst template (list (cons *proof-result* value)))))
           (if (equal literal expected)
               step
             '(:failure "failure" "")))))))

 (defun h1-book-field-field-order (n proof left right tests normalizer)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "h1-book-field-field-order")
     (let ((compared (h1-book-order-compare-orders proof left right normalizer)))
       (if (h1-book-field-unproved-p (car compared))
           (proof-with-checked-results
               ((choice (h1-book-field-order-alternatives
                         (list (list left right nil) (list right left t)) proof tests (cdr compared))))
             (if (eq (caar choice) :split)
                 (let* ((logic (h1-tactics-prover-proof proof))
                        (lower (cadar choice))
                        (higher (caddar choice)))
                   (proof-with-checked-results
                       ((minus-case (h1-book-field-field-equality
                                     (1- n) proof left right (append tests (list (list lower t)))))
                        (positive-tests (append tests (list (list lower nil))))
                        (plus-case (h1-book-field-field-equality
                                    (1- n) proof left right (append positive-tests (list (list higher t)))))
                        (zero-case (h1-book-field-field-equality
                                    (1- n) proof left right (append positive-tests (list (list higher nil)))))
                        (nonnegative (proof-proof-cases logic higher plus-case zero-case))
                        (result (proof-proof-cases logic lower minus-case nonnegative)))
                     (cons result (cdr choice))))
               (if (failure-p (car choice)) (car choice) choice)))
         (if (failure-p (car compared)) (car compared) compared))))))

(defun h1-book-field-premises (formula premises)
  (declare (xargs :measure (acl2-count formula)))
  (if (proof-is-call formula *library-implies*)
      (if (consp (cddr formula))
          (h1-book-field-premises (caddr formula) (cons formula premises))
        '(:failure "failure" ""))
    (cons formula premises)))

(defun h1-book-field-operator-present (terms)
  (declare (xargs :measure (acl2-count terms)))
  (and (consp terms)
       (or (member-equal (h1-tactics-call-head (car terms))
                         (list *proof-times* *proof-minus* *proof-plus* *h1-book-arithmetic-reciprocal*))
           (h1-book-field-operator-present (cdr terms)))))

(defun h1-book-field-premise-tests (premises)
  (declare (xargs :measure (acl2-count premises)))
  (if (endp premises)
      nil
    (cons (list (cadar premises) t) (h1-book-field-premise-tests (cdr premises)))))

(defun h1-book-field-restore-premises (lib premises result)
  (declare (xargs :measure (acl2-count premises)))
  (if (endp premises)
      result
    (proof-with-checked-results
        ((step (h1-propositions-propositional-proof-implies-from lib (car premises) result)))
      (h1-book-field-restore-premises lib (cdr premises) step))))

(defun h1-book-field-field-proof (proof formula)
  (proof-with-checked-results ((parts (h1-book-field-premises formula nil)))
    (let ((goal (car parts))
          (premises (cdr parts)))
      (if (and (proof-is-call goal *proof-equal*)
               (h1-book-field-operator-present (h1-tactics-subterms goal)))
          (let* ((tests (h1-book-field-premise-tests (reverse premises)))
                 (operands (len (cdr goal))))
            (if (equal operands 2)
                (proof-with-checked-results
                    ((result (h1-book-field-field-equality 1000000 proof (cadr goal) (caddr goal) tests)))
                  (h1-book-field-restore-premises (h1-tactics-prover-library proof) premises result))
              '(:failure "failure" "")))
        '(:failure "Unproved" "")))))
