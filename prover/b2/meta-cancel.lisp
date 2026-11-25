(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-meta-cancel-add-equal* '("sym" "ACL2" "CANCEL_PLUS-EQUAL-CORRECT"))
(defconst *b2-meta-cancel-add-less* '("sym" "ACL2" "CANCEL_PLUS-LESSP-CORRECT"))
(defconst *b2-meta-cancel-multiply-equal* '("sym" "ACL2" "CANCEL_TIMES-EQUAL-CORRECT"))

(defconst *b2-meta-cancel-meta-cancellation*
  (list *b2-meta-cancel-add-equal* *b2-meta-cancel-add-less*
        *b2-meta-cancel-multiply-equal*))

(defun b2-meta-cancel-cancellation-lib (self) (nth 1 self))
(defun b2-meta-cancel-cancellation-formula (self) (nth 2 self))
(defun b2-meta-cancel-cancellation-term (self) (nth 3 self))
(defun b2-meta-cancel-cancellation-cancel (self) (nth 4 self))
(defun b2-meta-cancel-cancellation-relation (self) (nth 5 self))
(defun b2-meta-cancel-cancellation-fold (self) (nth 6 self))
(defun b2-meta-cancel-cancellation-operands (self) (nth 7 self))
(defun b2-meta-cancel-cancellation-operator (self) (nth 8 self))
(defun b2-meta-cancel-cancellation-fringes (self) (nth 9 self))
(defun b2-meta-cancel-cancellation-openers (self) (nth 11 self))

(defun b2-meta-cancel-cancellation-with-fold (self fold)
  (update-nth 6 fold
    (update-nth 1 (b2-meta-fold-arithmetic-fold-lib fold) self)))

(defun b2-meta-cancel-cancellation-with-lib (self lib)
  (b2-meta-cancel-cancellation-with-fold
   self (b2-meta-fold-arithmetic-fold-with-lib (b2-meta-cancel-cancellation-fold self) lib)))

(defun b2-meta-cancel-cancellation-init (lib formula operation less)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (application (proof-list-of-length (cadr parts) 3))
       (right (proof-list-of-length (caddr parts) 3)))
    (if (not (equal (caddr application) *b2-bags-a*))
        '(:failure "tactic-rejected" "")
      (let ((relation (if less *proof-less* *proof-equal*))
            (term (cadr application))
            (cancel (cadr right)))
        (proof-with-checked-results
            ((fold (b2-meta-fold-arithmetic-fold-init lib (car application) operation less))
             (head (proof-term-at cancel 0))
             (name (proof-term-at head 2)))
          (let* ((operands (list (b2-tactics-field term 1) (b2-tactics-field term 2)))
                 (operator (proof-quote operation))
                 (fringes (list (list *b2-bags-fringe* operator (car operands))
                                (list *b2-bags-fringe* operator (cadr operands))))
                 (fallback (proof-sym (concatenate 'string name "$1") "ACL2"))
                 (openers (list cancel fallback (proof-sym "MV-NTH" "ACL2")
                                (proof-sym "ZP" "ACL2"))))
            (list :b2-meta-cancel-cancellation lib formula term cancel relation fold
                  operands operator fringes fallback openers)))))))

(defmacro b2-meta-cancel-solve (lib goal &optional evidence rules)
  `(b2-tactics-tactics-solve ,lib ,goal ,evidence nil ,rules 0 nil))

(defun b2-meta-cancel-with-self (step self)
  (if (failure-p step) step (cons step self)))

(defun b2-meta-cancel-step-at (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun b2-meta-cancel-cancellation-cancel-equation (self evidence)
  (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize
                  (b2-meta-cancel-cancellation-lib self)
                  (b2-meta-cancel-cancellation-cancel self)
                  evidence (b2-meta-cancel-cancellation-openers self) nil 2000 nil)))
    (if equation equation (b2-tactics-unproved))))

(defun b2-meta-cancel-cancellation-unchanged (self evidence)
  (proof-with-checked-results
      ((equation (b2-meta-cancel-cancellation-cancel-equation self evidence)))
    (b2-meta-cancel-solve (b2-meta-cancel-cancellation-lib self)
                         (b2-meta-cancel-cancellation-formula self) evidence (list equation))))

(defun b2-meta-cancel-relation-equation (self term evidence)
  (let ((lib (b2-meta-cancel-cancellation-lib self))
        (fold (b2-meta-cancel-cancellation-fold self))
        (relation (b2-meta-cancel-cancellation-relation self)))
    (proof-with-checked-results
        ((equation (b2-meta-fold-arithmetic-fold-interpret fold term relation evidence)))
      (if (not (equal relation *proof-less*))
          equation
        (proof-with-checked-results
            ((value (b2-meta-cancel-step-at equation 2))
             (left (proof-term-at value 1))
             (right (proof-term-at value 2))
             (fixed (b2-algebra-fixed-order lib left right)))
          (proof-proof-chain (library-library-proof lib) equation (list fixed)))))))

(defun b2-meta-cancel-cancellation-old-values (self evidence)
  (b2-meta-cancel-relation-equation self (b2-meta-cancel-cancellation-term self) evidence))

(defun b2-meta-cancel-cancellation-actual-fringe (self term evidence)
  (proof-with-checked-results
      ((fringe (b2-meta-fold-arithmetic-fold-fringe-value (b2-meta-cancel-cancellation-fold self) term)))
    (let* ((fold (cdr fringe))
           (self (b2-meta-cancel-cancellation-with-fold self fold))
           (lib (b2-meta-cancel-cancellation-lib self))
           (proof (library-library-proof lib)))
      (proof-with-checked-results ((collected (proof-proof-symmetric proof (car fringe))))
        (if (equal (b2-meta-cancel-cancellation-relation self) *proof-less*)
            (cons collected self)
          (proof-with-checked-results
              ((opened (b2-meta-fold-arithmetic-fold-interpret
                        fold term (b2-meta-fold-arithmetic-fold-operation fold) evidence))
               (value (b2-meta-cancel-step-at opened 2))
               (positive-type (b2-products-numeric-closure lib value))
               (number (library-library-transport-argument lib positive-type opened 1))
               (fixed (b2-meta-fold-arithmetic-fold-fixed
                       fold (b2-meta-fold-arithmetic-fold-ev fold term *b2-bags-a*) number))
               (reversed (proof-proof-symmetric proof fixed)))
            (b2-meta-cancel-with-self (proof-proof-chain proof reversed (list collected)) self)))))))

(defun b2-meta-cancel-equal-shift-branch (lib goal signed equation)
  (proof-with-checked-results ((tidied (proof-proof-tidy (library-library-proof lib) equation)))
    (b2-meta-cancel-solve lib goal (list signed) (list tidied))))

(defun b2-meta-cancel-cancellation-equal-shift
    (self common left right left-number right-number common-number)
  (let* ((fold (b2-meta-cancel-cancellation-fold self))
         (lib (b2-meta-cancel-cancellation-lib self))
         (inputs (proof-eq (b2-meta-fold-arithmetic-fold-op fold common left)
                           (b2-meta-fold-arithmetic-fold-op fold common right)))
         (output (proof-eq (list *b2-products-fix* left) (list *b2-products-fix* right))))
    (proof-with-checked-results
        ((left-fix (b2-meta-fold-arithmetic-fold-fixed fold left left-number))
         (right-fix (b2-meta-fold-arithmetic-fold-fixed fold right right-number)))
      (if (equal (b2-meta-fold-arithmetic-fold-operation fold) *proof-plus*)
          (proof-with-checked-results
              ((cancelled (b2-algebra-common-operand lib (proof-eq inputs output))))
            (let* ((self (b2-meta-cancel-cancellation-with-lib self (cdr cancelled)))
                   (fold (b2-meta-cancel-cancellation-fold self)))
              (b2-meta-cancel-with-self
               (b2-meta-fold-arithmetic-fold-rewrite-operands fold (car cancelled)
                                                            (list left-fix right-fix)) self)))
        (let ((zero (proof-eq *proof-zero* (list *b2-products-fix* common))))
          (proof-with-checked-results
              ((cancelled (b2-algebra-common-operand lib (proof-eq inputs (proof-ite zero zero output)))))
            (let* ((lib (cdr cancelled))
                   (self (b2-meta-cancel-cancellation-with-lib self lib))
                   (fold (b2-meta-cancel-cancellation-fold self))
                   (proof (library-library-proof lib))
                   (test (proof-eq *proof-zero* common))
                   (goal (proof-eq inputs (proof-ite test *proof-true* (proof-eq left right)))))
              (proof-with-checked-results
                  ((fixed-common (b2-meta-fold-arithmetic-fold-fixed fold common common-number))
                   (equation (proof-proof-rewrite proof (car cancelled) fixed-common '(1 2 1 2)))
                   (equation (proof-proof-rewrite proof equation fixed-common '(1 2 2 2)))
                   (equation (proof-proof-rewrite proof equation left-fix '(1 2 3 1)))
                   (equation (proof-proof-rewrite proof equation right-fix '(1 2 3 2)))
                   (signs (b2-bags-signed lib test))
                   (yes (b2-meta-cancel-equal-shift-branch lib goal (car signs) equation))
                   (no (b2-meta-cancel-equal-shift-branch lib goal (cadr signs) equation)))
                (b2-meta-cancel-with-self (proof-proof-cases proof test yes no) self)))))))))

(defun b2-meta-cancel-normalized-quote (self equation direction evidence)
  (let ((lib (b2-meta-cancel-cancellation-lib self))
        (fold (b2-meta-cancel-cancellation-fold self))
        (less (equal (b2-meta-cancel-cancellation-relation self) *proof-less*)))
    (proof-with-checked-results
        ((value (b2-meta-cancel-step-at equation 2))
         (arg (proof-term-at value direction))
         (actual (if less (proof-term-at arg 1) arg))
         (syntax (proof-term-at actual 1))
         (given (b2-meta-fold-arithmetic-fold-interpret fold syntax *proof-quote* evidence)))
      (if (not less)
          given
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((step (proof-proof-reflexive proof (list *b2-products-fix* actual)))
               (lifted (proof-proof-rewrite proof step given '(1 2 1)))
               (zero-number (b2-meta-cancel-solve lib (list *library-numberp* *proof-zero*)))
               (fixed (b2-meta-fold-arithmetic-fold-fixed fold *proof-zero* zero-number)))
            (proof-proof-chain proof lifted (list fixed))))))))

(defun b2-meta-cancel-normalized-reductions (self equation args direction evidence)
  (declare (xargs :measure (len args)))
  (if (not (o< (len (cdr args)) (len args)))
      (cons nil self)
    (proof-with-checked-results
        ((reduction
          (if (eq (car args) :none)
              (b2-meta-cancel-with-self
               (b2-meta-cancel-normalized-quote self equation direction evidence) self)
            (proof-with-checked-results
                ((result (b2-meta-fold-arithmetic-fold-tree-value
                          (b2-meta-cancel-cancellation-fold self) (car args))))
              (cons (car result) (b2-meta-cancel-cancellation-with-fold self (cdr result))))))
         (rest (b2-meta-cancel-normalized-reductions
                (cdr reduction) equation (cdr args) (1+ direction) evidence)))
      (cons (cons (car reduction) (car rest)) (cdr rest)))))

(defun b2-meta-cancel-cancellation-normalized-relation (self syntax args evidence)
  (proof-with-checked-results
      ((equation (b2-meta-cancel-relation-equation self syntax evidence))
       (reductions (b2-meta-cancel-normalized-reductions self equation args 1 evidence)))
    (let* ((self (cdr reductions))
           (fold (b2-meta-cancel-cancellation-fold self)))
      (b2-meta-cancel-with-self
       (b2-meta-fold-arithmetic-fold-rewrite-operands fold equation (car reductions)) self))))

(defun b2-meta-cancel-cancellation-transport-to-result (self original changed evidence)
  (let* ((lib (b2-meta-cancel-cancellation-lib self))
         (proof (library-library-proof lib))
         (fold (b2-meta-cancel-cancellation-fold self)))
    (proof-with-checked-results
        ((produced (b2-meta-cancel-cancellation-cancel-equation self evidence))
         (left (b2-meta-cancel-step-at changed 1))
         (value (b2-meta-cancel-step-at produced 2)))
      (if (not (equal left (b2-meta-fold-arithmetic-fold-ev fold value *b2-bags-a*)))
          (b2-tactics-unproved)
        (proof-with-checked-results
            ((step (proof-proof-reflexive proof
                      (b2-meta-fold-arithmetic-fold-ev
                       fold (b2-meta-cancel-cancellation-cancel self) *b2-bags-a*)))
             (right (proof-proof-rewrite proof step produced '(1 2 1)))
             (rest (proof-proof-chain proof right (list changed)))
             (reversed (proof-proof-symmetric proof rest)))
          (proof-proof-chain proof original (list reversed)))))))

(defun b2-meta-cancel-fringe-residues (fringes common)
  (if (endp fringes)
      nil
    (cons (list *b2-meta-fold-bagdiff* (car fringes) common)
          (b2-meta-cancel-fringe-residues (cdr fringes) common))))

(defun b2-meta-cancel-both-decompose (self names fringes operands common evidence)
  (declare (xargs :measure (len names)))
  (if (or (not (o< (len (cdr names)) (len names)))
          (endp fringes) (endp operands))
      (cons nil self)
    (let ((all-fringes (b2-meta-cancel-cancellation-fringes self))
          (lib (b2-meta-cancel-cancellation-lib self)))
      (proof-with-checked-results
          ((subset (b2-bags-bag-fact lib (car names)
                    (list (list *library-x* (car all-fringes))
                          (list *library-y* (cadr all-fringes)))))
           (self (b2-meta-cancel-cancellation-with-lib self (cdr subset)))
           (fold (b2-meta-cancel-cancellation-fold self))
           (difference (b2-meta-fold-arithmetic-fold-difference-value fold (car fringes) common))
           (self (b2-meta-cancel-cancellation-with-fold self (cdr difference)))
           (difference-step (proof-proof-modus-ponens
                             (library-library-proof (b2-meta-cancel-cancellation-lib self))
                             (car difference) (car subset)))
           (actual (b2-meta-cancel-cancellation-actual-fringe self (car operands) evidence))
           (self (cdr actual))
           (proof (library-library-proof (b2-meta-cancel-cancellation-lib self)))
           (reversed (proof-proof-symmetric proof difference-step))
           (joined (proof-proof-chain proof (car actual) (list reversed)))
           (rest (b2-meta-cancel-both-decompose self (cdr names) (cdr fringes)
                                               (cdr operands) common evidence)))
        (cons (cons joined (car rest)) (cdr rest))))))

(defun b2-meta-cancel-both-shift (self common residues)
  (let* ((fold (b2-meta-cancel-cancellation-fold self))
         (factor (b2-meta-fold-arithmetic-fold-call fold common *b2-bags-a*))
         (left (b2-meta-fold-arithmetic-fold-call fold (car residues) *b2-bags-a*))
         (right (b2-meta-fold-arithmetic-fold-call fold (cadr residues) *b2-bags-a*)))
    (if (equal (b2-meta-cancel-cancellation-relation self) *proof-less*)
        (b2-meta-cancel-with-self
         (b2-algebra-cancel-common-shift (b2-meta-cancel-cancellation-lib self) factor left right)
         self)
      (proof-with-checked-results
          ((left-number (b2-meta-fold-arithmetic-fold-number fold (car residues)))
           (right-number (b2-meta-fold-arithmetic-fold-number (cdr left-number) (cadr residues)))
           (fold (cdr right-number))
           (common-number (if (equal (b2-meta-fold-arithmetic-fold-operation fold) *proof-times*)
                              (b2-meta-fold-arithmetic-fold-number fold common)
                            (cons nil fold))))
        (b2-meta-cancel-cancellation-equal-shift
         (b2-meta-cancel-cancellation-with-fold self (cdr common-number))
         factor left right (car left-number) (car right-number) (car common-number))))))

(defun b2-meta-cancel-expression-terms (values)
  (declare (xargs :measure (len values)))
  (if (not (o< (len (cdr values)) (len values)))
      nil
    (proof-with-checked-results
        ((first (proof-term-at (car values) 1))
         (rest (b2-meta-cancel-expression-terms (cdr values))))
      (cons first rest))))

(defun b2-meta-cancel-conditional-trees (opened)
  (proof-with-checked-results
      ((value (b2-meta-cancel-step-at opened 2))
       (terms (b2-meta-cancel-expression-terms (seq-slice value 1 5))))
    (proof-list-of-length terms 3)))

(defun b2-meta-cancel-both-update (self syntax residues common yes evidence)
  (let ((fold (b2-meta-cancel-cancellation-fold self)))
    (if (not (equal (b2-meta-fold-arithmetic-fold-operation fold) *proof-times*))
        (b2-meta-cancel-cancellation-normalized-relation self syntax residues evidence)
      (proof-with-checked-results
          ((opened (b2-meta-fold-arithmetic-fold-interpret fold syntax *proof-if* evidence))
           (trees (b2-meta-cancel-conditional-trees opened))
           (formal-zero (b2-meta-fold-arithmetic-fold-formal-zero fold common))
           (self (b2-meta-cancel-cancellation-with-fold self (cdr formal-zero)))
           (intersection (b2-bags-intersection-cons (b2-meta-cancel-cancellation-lib self) yes))
           (self (b2-meta-cancel-cancellation-with-lib self (cdr intersection)))
           (fold (b2-meta-cancel-cancellation-fold self))
           (proof (library-library-proof (b2-meta-cancel-cancellation-lib self)))
           (zeros (proof-proof-modus-ponens proof (car formal-zero) (car intersection)))
           (truth (b2-meta-fold-arithmetic-fold-interpret fold (cadr trees) *proof-quote* evidence))
           (residue-value (b2-meta-cancel-cancellation-normalized-relation
                           self (caddr trees) residues evidence)))
        (let* ((self (cdr residue-value))
               (fold (b2-meta-cancel-cancellation-fold self)))
          (b2-meta-cancel-with-self
           (b2-meta-fold-arithmetic-fold-rewrite-operands fold opened
             (list zeros truth (car residue-value))) self))))))

(defun b2-meta-cancel-cancellation-both (self evidence)
  (let* ((lib (b2-meta-cancel-cancellation-lib self))
         (fringes (b2-meta-cancel-cancellation-fringes self))
         (common (cons *b2-bags-intersect* fringes)))
    (proof-with-checked-results ((signs (b2-bags-signed lib common)))
      (let ((current (append evidence (list (car signs))))
            (residues (b2-meta-cancel-fringe-residues fringes common)))
        (proof-with-checked-results
            ((decomposed (b2-meta-cancel-both-decompose
                          self (list *b2-bags-intersect1* *b2-bags-intersect2*)
                          fringes (b2-meta-cancel-cancellation-operands self) common current))
             (self (cdr decomposed))
             (old (b2-meta-cancel-cancellation-old-values self current))
             (original (b2-meta-fold-arithmetic-fold-rewrite-operands
                        (b2-meta-cancel-cancellation-fold self) old (car decomposed)))
             (cancel (b2-meta-cancel-both-shift self common residues))
             (self (cdr cancel))
             (proof (library-library-proof (b2-meta-cancel-cancellation-lib self)))
             (original (proof-proof-chain proof original (list (car cancel))))
             (equation (b2-meta-cancel-cancellation-cancel-equation self current))
             (syntax (b2-meta-cancel-step-at equation 2))
             (updated (b2-meta-cancel-both-update self syntax residues common (car signs) current))
             (self (cdr updated))
             (positive (b2-meta-cancel-cancellation-transport-to-result self original (car updated) current))
             (negative (b2-meta-cancel-cancellation-unchanged self (append evidence (list (cadr signs))))))
          (b2-meta-cancel-with-self
           (proof-proof-cases (library-library-proof (b2-meta-cancel-cancellation-lib self))
                              common positive negative) self))))))

(defun b2-meta-cancel-pair-position (position)
  (cond ((or (equal position 0) (equal position -2) (null position)) 0)
        ((or (equal position 1) (equal position -1) (eq position t)) 1)
        ((integerp position) '(:failure "tactic-rejected" ""))
        (t '(:failure "tactic-rejected" ""))))

(defun b2-meta-cancel-cancellation-single-less (self position difference remainder other evidence)
  (let* ((fold (b2-meta-cancel-cancellation-fold self))
         (lib (b2-meta-cancel-cancellation-lib self))
         (proof (library-library-proof lib))
         (retained (b2-meta-fold-arithmetic-fold-call fold remainder *b2-bags-a*))
         (ev-other (b2-meta-fold-arithmetic-fold-ev fold other *b2-bags-a*)))
    (proof-with-checked-results
        ((identity (b2-meta-fold-arithmetic-fold-right-identity fold ev-other))
         (reversed (proof-proof-symmetric proof identity))
         (slot (b2-meta-cancel-pair-position position))
         (old (b2-meta-cancel-cancellation-old-values self evidence))
         (original (b2-meta-fold-arithmetic-fold-rewrite-operands
                    fold old (update-nth slot difference (list reversed reversed))))
         (results (update-nth slot retained (list *proof-zero* *proof-zero*)))
         (shift (b2-algebra-cancel-common-shift lib ev-other (car results) (cadr results)))
         (original (proof-proof-chain proof original (list shift)))
         (args (update-nth slot remainder (list :none :none)))
         (equation (b2-meta-cancel-cancellation-cancel-equation self evidence))
         (syntax (b2-meta-cancel-step-at equation 2))
         (changed (b2-meta-cancel-cancellation-normalized-relation self syntax args evidence)))
      (b2-meta-cancel-with-self
       (b2-meta-cancel-cancellation-transport-to-result (cdr changed) original (car changed) evidence)
       (cdr changed)))))

(defun b2-meta-cancel-symmetric-equivalence (lib left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof left t))
         (no (proof-proof-assume proof left nil))
         (forward (proof-proof-symmetric proof yes))
         (positive (b2-algebra-boolean-equivalence-positive lib (proof-eq left right) yes forward))
         (assumption (proof-proof-assume proof right t))
         (backward (proof-proof-symmetric proof assumption)))
      (b2-algebra-boolean-equivalence-negative lib left right no positive backward))))

(defun b2-meta-cancel-single-equal-switch (lib positive comparison position product-test)
  (if (not (or (equal position 0) (null position)))
      positive
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((right (b2-meta-cancel-step-at positive 2))
           (original-test (if product-test (proof-term-at right 3) right))
           (switched (b2-meta-cancel-symmetric-equivalence lib original-test comparison)))
        (if product-test
            (proof-with-checked-results
                ((rewritten (proof-proof-rewrite proof positive switched '(1 2 3))))
              (proof-proof-tidy proof rewritten))
          (proof-proof-chain proof positive (list switched)))))))

(defun b2-meta-cancel-single-equal-merge
    (lib position difference old positive comparison numeric signs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (b2-meta-cancel-step-at old 2))
         (same (proof-proof-assume proof test t))
         (op-value (b2-meta-cancel-step-at difference 2))
         (number-proof (b2-products-numeric-closure lib op-value))
         (op-argument (library-library-transport-argument lib number-proof difference 1))
         (opposite (if (or (equal position 0) (null position)) same
                     (proof-proof-symmetric proof same)))
         (rewritten (proof-proof-rewrite proof op-argument opposite '(1 1)))
         (tidied (proof-proof-tidy proof rewritten))
         (contradiction (proof-proof-cut proof tidied (cadr signs)))
         (not-equal (proof-proof-front proof contradiction (proof-neg test)))
         (closed (b2-tactics-tactics-close-false lib test not-equal))
         (negative (proof-proof-chain proof old (list closed)))
         (merged (proof-ite numeric comparison *proof-false*))
         (selected (proof-proof-select proof merged (car signs)))
         (reversed (proof-proof-symmetric proof selected))
         (positive (proof-proof-chain proof positive (list reversed)))
         (selected (proof-proof-select proof merged (cadr signs)))
         (reversed (proof-proof-symmetric proof selected))
         (negative (proof-proof-chain proof negative (list reversed))))
      (proof-proof-cases proof numeric positive negative))))

(defun b2-meta-cancel-single-equal-product (self yes-tree remainder ev-other evidence)
  (let* ((fold (b2-meta-cancel-cancellation-fold self))
         (lib (b2-meta-cancel-cancellation-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((zero-guard (b2-meta-fold-arithmetic-fold-interpret fold yes-tree *proof-if* evidence))
         (trees (b2-meta-cancel-conditional-trees zero-guard))
         (probe (b2-meta-fold-arithmetic-fold-interpret fold (car trees) *proof-equal* evidence))
         (probe-eq (b2-meta-fold-arithmetic-fold-evaluate-arguments
                    fold probe (list nil *proof-quote*) evidence))
         (switched (b2-meta-cancel-symmetric-equivalence
                    lib (proof-eq ev-other *proof-zero*) (proof-eq *proof-zero* ev-other)))
         (probe-eq (proof-proof-chain proof probe-eq (list switched)))
         (truth-eq (b2-meta-fold-arithmetic-fold-interpret fold (cadr trees) *proof-quote* evidence))
         (kept-eq (b2-meta-cancel-cancellation-normalized-relation
                   self (caddr trees) (list :none remainder) evidence)))
      (let* ((self (cdr kept-eq))
             (fold (b2-meta-cancel-cancellation-fold self)))
        (b2-meta-cancel-with-self
         (b2-meta-fold-arithmetic-fold-rewrite-operands fold zero-guard
           (list probe-eq truth-eq (car kept-eq))) self)))))

(defun b2-meta-cancel-single-equal-update (self syntax remainder ev-other evidence product-test)
  (let ((fold (b2-meta-cancel-cancellation-fold self)))
    (proof-with-checked-results
        ((opened (b2-meta-fold-arithmetic-fold-interpret fold syntax *proof-if* evidence))
         (trees (b2-meta-cancel-conditional-trees opened))
         (test-eq (b2-meta-fold-arithmetic-fold-interpret fold (car trees) *library-numberp* evidence))
         (yes-eq (if product-test
                     (b2-meta-cancel-single-equal-product self (cadr trees) remainder ev-other evidence)
                   (b2-meta-cancel-cancellation-normalized-relation
                    self (cadr trees) (list :none remainder) evidence)))
         (self (cdr yes-eq))
         (fold (b2-meta-cancel-cancellation-fold self))
         (no-eq (b2-meta-fold-arithmetic-fold-interpret fold (caddr trees) *proof-quote* evidence)))
      (b2-meta-cancel-with-self
       (b2-meta-fold-arithmetic-fold-rewrite-operands fold opened (list test-eq (car yes-eq) no-eq))
       self))))

(defun b2-meta-cancel-cancellation-single-equal (self position difference remainder other evidence)
  (let* ((fold (b2-meta-cancel-cancellation-fold self))
         (lib (b2-meta-cancel-cancellation-lib self))
         (proof (library-library-proof lib))
         (ev-other (b2-meta-fold-arithmetic-fold-ev fold other *b2-bags-a*))
         (numeric (list *library-numberp* ev-other)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib numeric))
         (kept (b2-meta-fold-arithmetic-fold-call fold remainder *b2-bags-a*))
         (identity (b2-meta-fold-arithmetic-fold-right-identity fold ev-other))
         (fixed (b2-meta-fold-arithmetic-fold-fixed fold ev-other (car signs)))
         (identity (proof-proof-chain proof identity (list fixed)))
         (reversed (proof-proof-symmetric proof identity))
         (slot (b2-meta-cancel-pair-position position))
         (old (b2-meta-cancel-cancellation-old-values self evidence))
         (with-unit (b2-meta-fold-arithmetic-fold-rewrite-operands
                     fold old (update-nth slot difference (list reversed reversed))))
         (unit (b2-meta-fold-arithmetic-fold-constant fold))
         (unit-number (b2-meta-cancel-solve lib (list *library-numberp* unit)))
         (values (update-nth slot kept (list unit unit)))
         (kept-number (b2-meta-fold-arithmetic-fold-number fold remainder))
         (self (b2-meta-cancel-cancellation-with-fold self (cdr kept-number)))
         (kinds (update-nth slot (car kept-number) (list unit-number unit-number)))
         (removed (b2-meta-cancel-cancellation-equal-shift
                   self ev-other (car values) (cadr values) (car kinds) (cadr kinds) (car signs)))
         (self (cdr removed))
         (lib (b2-meta-cancel-cancellation-lib self))
         (proof (library-library-proof lib))
         (positive (proof-proof-chain proof with-unit (list (car removed))))
         (comparison (proof-eq unit kept))
         (product-test (equal (b2-meta-fold-arithmetic-fold-operation
                               (b2-meta-cancel-cancellation-fold self)) *proof-times*))
         (positive (b2-meta-cancel-single-equal-switch lib positive comparison position product-test))
         (comparison (if product-test
                         (proof-ite (proof-eq *proof-zero* ev-other) *proof-true* comparison)
                       comparison))
         (original (b2-meta-cancel-single-equal-merge lib position difference old positive comparison numeric signs))
         (equation (b2-meta-cancel-cancellation-cancel-equation self evidence))
         (syntax (b2-meta-cancel-step-at equation 2))
         (updated (b2-meta-cancel-single-equal-update self syntax remainder ev-other evidence product-test)))
      (b2-meta-cancel-with-self
       (b2-meta-cancel-cancellation-transport-to-result (cdr updated) original (car updated) evidence)
       (cdr updated)))))

(defun b2-meta-cancel-cancellation-one-try-delete
    (current self position occurs other term fringe)
  (let ((lib (b2-meta-cancel-cancellation-lib self)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib occurs))
         (selected (append current (list (car signs))))
         (link (b2-bags-bag-fact lib *b2-bags-fringe-member*
                 (list (list *b2-bags-binop* (b2-meta-cancel-cancellation-operator self))
                       (list *b2-bags-arg* other) (list *b2-bags-term* term))))
         (self (b2-meta-cancel-cancellation-with-lib self (cdr link)))
         (proof (library-library-proof (cdr link)))
         (rewritten (proof-proof-rewrite proof (car signs) (car link) '(1)))
         (present (proof-proof-tidy proof rewritten))
         (remainder (list *b2-bags-del* other fringe))
         (reduced (b2-meta-fold-arithmetic-fold-delete-value
                   (b2-meta-cancel-cancellation-fold self) other fringe))
         (self (b2-meta-cancel-cancellation-with-fold self (cdr reduced)))
         (proof (library-library-proof (b2-meta-cancel-cancellation-lib self)))
         (reduced (proof-proof-modus-ponens proof (car reduced) present))
         (actual (b2-meta-cancel-cancellation-actual-fringe self term selected))
         (self (cdr actual))
         (proof (library-library-proof (b2-meta-cancel-cancellation-lib self)))
         (reversed (proof-proof-symmetric proof reduced))
         (difference (proof-proof-chain proof (car actual) (list reversed)))
         (positive
          (if (equal (b2-meta-cancel-cancellation-relation self) *proof-less*)
              (b2-meta-cancel-cancellation-single-less self position difference remainder other selected)
            (b2-meta-cancel-cancellation-single-equal self position difference remainder other selected)))
         (self (cdr positive))
         (negative (b2-meta-cancel-cancellation-unchanged self (append current (list (cadr signs))))))
      (b2-meta-cancel-with-self
       (proof-proof-cases (library-library-proof (b2-meta-cancel-cancellation-lib self))
                          occurs (car positive) negative) self))))

(defun b2-meta-cancel-position-term (terms position)
  (cond ((not (integerp position))
         '(:failure "tactic-rejected" ""))
        ((< position (- (len terms))) '(:failure "tactic-rejected" ""))
        (t (proof-term-at terms (if (< position 0) (+ position (len terms)) position)))))

(defun b2-meta-cancel-cancellation-one (self position evidence)
  (let ((lib (b2-meta-cancel-cancellation-lib self))
        (operands (b2-meta-cancel-cancellation-operands self))
        (position (cond ((eq position t) 1) ((not position) 0) (t position))))
    (proof-with-checked-results
        ((term (b2-meta-cancel-position-term operands position))
         (other (b2-meta-cancel-position-term operands (- 1 position)))
         (fringe (b2-meta-cancel-position-term (b2-meta-cancel-cancellation-fringes self) position))
         (occurs (list *b2-bags-occur* (b2-meta-cancel-cancellation-operator self) other term)))
      (if (equal (b2-meta-cancel-cancellation-relation self) *proof-less*)
          (b2-meta-cancel-cancellation-one-try-delete evidence self position occurs other term fringe)
        (proof-with-checked-results
            ((signs (b2-bags-signed lib other))
             (positive (b2-meta-cancel-cancellation-one-try-delete
                        (append evidence (list (car signs))) self position occurs other term fringe))
             (self (cdr positive))
             (negative (b2-meta-cancel-cancellation-unchanged self (append evidence (list (cadr signs))))))
          (b2-meta-cancel-with-self
           (proof-proof-cases (library-library-proof (b2-meta-cancel-cancellation-lib self))
                              other (car positive) negative) self))))))

(defun b2-meta-cancel-cancellation-prove-relation-left-right (second inner self first)
  (cond ((and first second) (b2-meta-cancel-cancellation-both self inner))
        ((or first second) (b2-meta-cancel-cancellation-one self (if first 0 1) inner))
        (t (b2-meta-cancel-with-self (b2-meta-cancel-cancellation-unchanged self inner) self))))

(mutual-recursion
 (defun b2-meta-cancel-cons-operation-run (n self term operation evidence prove)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-meta-cancel-cons-operation-run")
     (let ((test (list *proof-consp* term))
           (same (proof-eq (list *library-car* term) (proof-quote operation)))
           (lib (b2-meta-cancel-cancellation-lib self)))
       (proof-with-checked-results
           ((tests (b2-bags-signed lib test))
            (matches (b2-bags-signed lib same))
            (yes (b2-meta-cancel-apply-cons-recipe
                  (1- n) self prove t (append evidence (list (car tests) (car matches)))))
            (other (b2-meta-cancel-apply-cons-recipe
                    (1- n) (cdr yes) prove nil (append evidence (list (car tests) (cadr matches)))))
            (no (b2-meta-cancel-apply-cons-recipe
                 (1- n) (cdr other) prove nil (append evidence (list (cadr tests)))))
            (self (cdr no))
            (proof (library-library-proof (b2-meta-cancel-cancellation-lib self)))
            (on-cons (proof-proof-cases proof same (car yes) (car other))))
         (b2-meta-cancel-with-self (proof-proof-cases proof test on-cons (car no)) self)))))

 (defun b2-meta-cancel-apply-cons-recipe (n self recipe sign evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-meta-cancel-apply-cons-recipe")
     (cond ((eq recipe :relation)
            (b2-meta-cancel-cancellation-prove-relation (1- n) sign evidence self))
           ((eq recipe :left)
            (b2-meta-cancel-cancellation-prove-relation-left (1- n) sign evidence self))
           (t (b2-meta-cancel-cancellation-prove-relation-left-right sign evidence self (cadr recipe))))))

 (defun b2-meta-cancel-cancellation-prove-relation (n active evidence self)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "b2-meta-cancel-cancellation-prove-relation"))
         ((not active)
          (b2-meta-cancel-with-self (b2-meta-cancel-cancellation-unchanged self evidence) self))
         (t (b2-meta-cancel-cons-operation-run
             (1- n) self (car (b2-meta-cancel-cancellation-operands self))
             (b2-meta-fold-arithmetic-fold-operation (b2-meta-cancel-cancellation-fold self))
             evidence :left))))

 (defun b2-meta-cancel-cancellation-prove-relation-left (n first outer self)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-meta-cancel-cancellation-prove-relation-left")
     (b2-meta-cancel-cons-operation-run
      (1- n) self (cadr (b2-meta-cancel-cancellation-operands self))
      (b2-meta-fold-arithmetic-fold-operation (b2-meta-cancel-cancellation-fold self))
      outer (list :right first)))))

(defun b2-meta-cancel-cancellation-cons-operation (self term operation evidence prove)
  (b2-meta-cancel-cons-operation-run 1000000 self term operation evidence prove))

(defun b2-meta-cancel-cancellation-prove (self)
  (proof-with-checked-results
      ((fold (b2-meta-fold-arithmetic-fold-install (b2-meta-cancel-cancellation-fold self))))
    (let ((self (b2-meta-cancel-cancellation-with-fold self fold)))
      (b2-meta-cancel-cancellation-cons-operation self (b2-meta-cancel-cancellation-term self)
        (b2-meta-cancel-cancellation-relation self) nil :relation))))

(defun b2-meta-cancel-prove-meta-cancel (lib name formula)
  (let ((operation (if (equal name *b2-meta-cancel-multiply-equal*) *proof-times* *proof-plus*)))
    (proof-with-checked-results
        ((self (b2-meta-cancel-cancellation-init lib formula operation
                                              (equal name *b2-meta-cancel-add-less*)))
         (result (b2-meta-cancel-cancellation-prove self)))
      (cons (car result) (b2-meta-cancel-cancellation-lib (cdr result))))))
