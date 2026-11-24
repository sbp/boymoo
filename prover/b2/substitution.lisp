(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-substitution-pseudo-list* '("sym" "ACL2" "PSEUDO-TERM-LISTP"))
(defconst *b2-substitution-salist* '("sym" "ACL2" "SYMBOL-ALISTP"))
(defconst *b2-substitution-term* '("sym" "ACL2" "SUBLIS-VAR1"))
(defconst *b2-substitution-terms* '("sym" "ACL2" "SUBLIS-VAR1-LST"))
(defconst *b2-substitution-construct* '("sym" "ACL2" "CONS-TERM"))
(defconst *b2-substitution-fold* '("sym" "ACL2" "CONS-TERM1"))
(defconst *b2-substitution-fold-mv* '("sym" "ACL2" "CONS-TERM1-MV2"))
(defconst *b2-substitution-mv* '("sym" "ACL2" "MV-NTH"))
(defconst *b2-substitution-kwote* '("sym" "ACL2" "KWOTE"))
(defconst *b2-substitution-env* '("sym" "ACL2" "ALIST"))
(defconst *b2-substitution-fn* '("sym" "ACL2" "FN"))
(defconst *b2-substitution-args* '("sym" "ACL2" "ARGS"))
(defconst *b2-substitution-form* '("sym" "ACL2" "FORM"))

(defun b2-substitution-second (term)
  (list *b2-substitution-mv* *proof-one* term))

(defun b2-substitution-output (fn expression)
  (b2-substitution-second (list fn *b2-substitution-env* expression)))

(defun b2-substitution-step-result (step)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((first (proof-step-first step)))
      (proof-term-at first 2))))

(defun b2-substitution-required-value (key dictionary)
  (let ((entry (assoc-equal key dictionary)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-substitution-facts (lib)
  (proof-proof-facts (library-library-proof lib)))

(defun b2-substitution-rewrite-opened (lib step opened template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((symmetric (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite-result proof step symmetric template *proof-result*))))

(defun b2-substitution-close-result-cases (lib opened value template prove)
  (proof-with-checked-results
   ((step (proof-proof-by-value (library-library-proof lib) value template prove nil)))
   (b2-substitution-rewrite-opened lib step opened template)))

(defun b2-substitution-result-cases (lib call template prove)
  (proof-with-checked-results
   ((opened (proof-proof-unfold (library-library-proof lib) call))
    (value (b2-substitution-step-result opened)))
   (b2-substitution-close-result-cases lib opened value template prove)))

(defun b2-substitution-add-pair-projection (lib name)
  (if (assoc-equal name (b2-substitution-facts lib))
      (cons name lib)
    (let* ((proof (library-library-proof lib))
           (target (b2-substitution-second (list *proof-cons* *library-x*
                                                (list *proof-cons* *library-y* *proof-false*))))
           (zp-symbol (proof-sym "ZP" "ACL2")))
      (proof-with-checked-results
       ((equation (b2-tactics-tactics-normalize lib target nil (list target zp-symbol)
                                                nil 1500 nil))
        (rest (b2-substitution-step-result equation))
        (tail (b2-tactics-tactics-normalize lib rest nil (list rest zp-symbol)
                                            nil 1500 nil))
        (equation (proof-proof-chain proof equation (list tail))))
       (b2-tactics-tactics-add-lemma lib "SECOND-OF-PAIR" equation :none)))))

(defun b2-substitution-pair-projection (lib pair)
  (let ((name (proof-sym "B2-SECOND-OF-PAIR" "ACL2")))
    (proof-with-checked-results
     ((added (b2-substitution-add-pair-projection lib name))
      (lib (cdr added))
      (clause (b2-substitution-required-value name (b2-substitution-facts lib)))
      (first (proof-term-at clause 0))
      (pattern (proof-term-at first 1))
      (step (b2-tactics-tactics-exact lib name pattern (b2-substitution-second pair))))
     (cons step lib))))

(defun b2-substitution-size-preserved-branch (value cons-step hypothesis lib template)
  (proof-with-checked-results
   ((projection (b2-substitution-pair-projection lib value))
    (lib (cdr projection))
    (projection (car projection))
    (goal (proof-subst template (list (cons *proof-result* value))))
    (visible (b2-substitution-step-result projection)))
   (let ((proof (library-library-proof lib))
         (length-x (list *library-len* *library-x*)))
     (if (equal visible *library-x*)
         (proof-with-checked-results
          ((own-length (proof-proof-reflexive proof length-x))
           (symmetric (proof-proof-symmetric proof projection))
           (rewritten (proof-proof-rewrite proof own-length symmetric '(1 1 1)))
           (step (proof-proof-tidy proof rewritten)))
          (cons step lib))
       (proof-with-checked-results
        ((left (proof-term-at goal 1))
         (step (b2-tactics-tactics-solve lib goal (list cons-step) (list left length-x)
                                        (list projection hypothesis) 0 nil)))
        (cons step lib))))))

(defun b2-substitution-size-preserved-base (atom lib call template)
  (proof-with-checked-results
   ((equation (b2-tactics-tactics-normalize lib call (list atom) (list call) nil 1500 nil))
    (value (b2-substitution-step-result equation))
    (branch (b2-substitution-size-preserved-branch value atom nil lib template))
    (lib (cdr branch))
    (step (b2-substitution-rewrite-opened lib (car branch) equation template)))
   (cons step lib)))

(defun b2-substitution-size-preserved-leaves (requests lib template cons-step hypothesis answers)
  (if (endp requests)
      (cons answers lib)
    (let ((request (car requests)))
      (proof-with-checked-results
       ((branch (b2-substitution-size-preserved-branch
                 (car request) cons-step hypothesis lib template)))
       (b2-substitution-size-preserved-leaves
        (cdr requests) (cdr branch) template cons-step hypothesis
        (table-put answers request (car branch)))))))

(defun b2-substitution-size-preserved-advance (cons-step hypothesis lib call template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof call))
      (value (b2-substitution-step-result opened))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaves (b2-substitution-size-preserved-leaves
               requests lib template cons-step hypothesis nil))
      (lib (cdr leaves))
      (step (b2-substitution-close-result-cases lib opened value template (car leaves))))
     (cons step lib))))

(defun b2-substitution-size-preserved (lib)
  (let ((name (proof-sym "B2-SUBLIS-LENGTH" "ACL2")))
    (if (assoc-equal name (b2-substitution-facts lib))
        (cons name lib)
      (let ((call (list *b2-substitution-terms* *b2-substitution-env* *library-x*))
            (template (proof-eq (list *library-len* (b2-substitution-second *proof-result*))
                                (list *library-len* *library-x*))))
        (proof-with-checked-results
         ((formula (proof-subst template (list (cons *proof-result* call))))
          (advance-request (b2-tactics-tactics-on-list lib formula *library-x* nil nil nil))
          (request (car advance-request))
          (advance (b2-substitution-size-preserved-advance
                    (nth 3 request) (nth 4 request) (cdr advance-request) call template))
          (base-request (b2-tactics-tactics-on-list lib formula *library-x* nil advance nil))
          (request (car base-request))
          (base (b2-substitution-size-preserved-base
                 (nth 3 request) (cdr base-request) call template))
          (proof (b2-tactics-tactics-on-list lib formula *library-x* base advance nil))
          (step (car proof)))
         (b2-tactics-tactics-add-lemma (cdr proof) "SUBLIS-LENGTH" step :none))))))

(defund b2-substitution-folded-equation-step (lib equation)
  (proof-with-checked-results ((value (b2-substitution-step-result equation)))
    (if (not (proof-compound value))
        equation
      (proof-with-checked-results ((operator (proof-term-at value 0)))
        (if (not (proof-compound operator))
            equation
          (let ((proof (library-library-proof lib)))
            (proof-with-checked-results
             ((beta (proof-proof-beta proof value))
              (equation (proof-proof-chain proof equation (list beta))))
             (list :continue equation))))))))

(defun b2-substitution-folded-equation-visit (n lib equation)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b2-substitution-folded-equation-visit")
    (let ((next (b2-substitution-folded-equation-step lib equation)))
      (if (eq (car next) :continue)
          (b2-substitution-folded-equation-visit (1- n) lib (cadr next))
        next))))

(defun b2-substitution-folded-equation (lib call)
  (proof-with-checked-results ((equation (proof-proof-unfold (library-library-proof lib) call)))
    (b2-substitution-folded-equation-visit 1000000 lib equation)))

(defun b2-substitution-computed-term-leaf (value tests lib template quoted-rule)
  (declare (ignore tests))
  (proof-with-checked-results
   ((goal (proof-subst template (list (cons *proof-result* value)))))
   (if (equal value *proof-false*)
       (b2-tactics-tactics-solve lib goal nil nil nil 0 nil)
     (proof-with-checked-results ((operator (proof-term-at value 0)))
       (if (not (equal operator *b2-substitution-kwote*))
           '(:failure "tactic-rejected" "")
         (proof-with-checked-results
          ((term (proof-term-at value 1))
           (typed (proof-proof-fact (library-library-proof lib) quoted-rule
                                    (list (list *library-x* term)))))
          (b2-tactics-tactics-solve lib goal (list typed) nil nil 1 nil)))))))

(defun b2-substitution-computed-term-leaves (requests lib template quoted-rule)
  (if (endp requests)
      nil
    (let ((request (car requests)))
      (proof-with-checked-results
       ((step (b2-substitution-computed-term-leaf (car request) (cadr request)
                                                  lib template quoted-rule))
        (rest (b2-substitution-computed-term-leaves (cdr requests) lib template quoted-rule)))
       (cons (cons request step) rest)))))

(defun b2-substitution-computed-term (lib)
  (let ((name (proof-sym "B2-COMPUTED-PSEUDO-TERM" "ACL2")))
    (if (assoc-equal name (b2-substitution-facts lib))
        (cons name lib)
      (proof-with-checked-results
       ((opened (b2-substitution-folded-equation
                 lib (list *b2-substitution-fold* *b2-substitution-fn* *b2-substitution-args*)))
        (body (b2-substitution-step-result opened))
        (computation (proof-term-at body 1)))
       (let ((template (proof-ite *proof-result* (list *b2-association-pseudo-term*
                                                       *proof-result*) *proof-true*))
             (quoted (list *b2-substitution-kwote* *library-x*)))
         (proof-with-checked-results
          ((typed (b2-tactics-tactics-solve lib (list *b2-association-pseudo-term* quoted)
                                           nil (list quoted *b2-association-pseudo-term*)
                                           nil 0 nil))
           (quoted-rule (b2-tactics-tactics-add-lemma lib "KWOTE-PSEUDO-TERM" typed :none))
           (lib (cdr quoted-rule))
           (proof (library-library-proof lib))
           (requests (proof-proof-by-value-leaves proof computation nil))
           (leaves (b2-substitution-computed-term-leaves requests lib template (car quoted-rule)))
           (step (proof-proof-by-value proof computation template leaves nil)))
          (b2-tactics-tactics-add-lemma lib "COMPUTED-PSEUDO-TERM" step :none)))))))

(defun b2-substitution-folded-branch (lib opened selection fact value multiple)
  (proof-with-checked-results
   ((equation (proof-proof-chain (library-library-proof lib) opened (list selection))))
   (if multiple
       (proof-with-checked-results
        ((projection (b2-substitution-pair-projection lib value))
         (lib (cdr projection))
         (proof (library-library-proof lib))
         (symmetric (proof-proof-symmetric proof equation))
         (lifted (proof-proof-rewrite proof (car projection) symmetric '(1 1 2)))
         (step (library-library-transport-argument lib fact lifted 1)))
        (cons step lib))
     (proof-with-checked-results
      ((step (library-library-transport-argument lib fact equation 1)))
      (cons step lib)))))

(defun b2-substitution-folded-term-property (lib call original)
  (proof-with-checked-results
   ((arguments (proof-list-of-length (seq-slice call 1 3) 2))
    (opened (b2-substitution-folded-equation lib call))
    (body (b2-substitution-step-result opened))
    (test (proof-term-at body 1))
    (computed (b2-substitution-computed-term lib))
    (lib (cdr computed))
    (proof (library-library-proof lib))
    (computed (proof-proof-fact proof (car computed)
                                (list (list *b2-substitution-fn* (car arguments))
                                      (list *b2-substitution-args* (cadr arguments)))))
    (assumed (proof-proof-assume proof test t))
    (taken (proof-proof-prove-if proof computed assumed))
    (true (proof-proof-if-true proof body))
    (false (proof-proof-if-false proof body))
    (multiple (equal (car call) *b2-substitution-fold-mv*))
    (yes (b2-substitution-folded-branch lib opened true taken (caddr body) multiple))
    (no (b2-substitution-folded-branch (cdr yes) opened false original (cadddr body) multiple))
    (lib (cdr no))
    (step (proof-proof-cases (library-library-proof lib) test (car yes) (car no))))
   (cons step lib)))

(defun b2-substitution-wrap-construction (lib fn args typed)
  (let* ((call (list *b2-substitution-construct* fn args))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof call))
      (body (b2-substitution-step-result opened))
      (test (proof-term-at body 1))
      (true (proof-proof-if-true proof body))
      (true (proof-proof-chain proof opened (list true)))
      (false (proof-proof-if-false proof body))
      (false (proof-proof-chain proof opened (list false)))
      (value (b2-substitution-step-result true))
      (on-true (b2-substitution-folded-term-property lib value typed))
      (lib (cdr on-true))
      (yes (library-library-transport-argument lib (car on-true) true 1))
      (no (library-library-transport-argument lib typed false 1))
      (step (proof-proof-cases (library-library-proof lib) test yes no)))
     (cons step lib))))

(defund b2-substitution-return-last-step (term lib result collectp)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold proof term))
      (result (if collectp
                  (cons equation result)
                (proof-proof-rewrite-first proof result equation)))
      (value (b2-substitution-step-result equation)))
     (list value result))))

(mutual-recursion
 (defun b2-substitution-return-values-term (n term lib result collectp)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "b2-substitution-return-values-term"))
    ((proof-is-call term *termination-return-last*)
     (proof-with-checked-results
      ((next (b2-substitution-return-last-step term lib result collectp)))
      (b2-substitution-return-values-term (1- n) (car next) lib (cadr next) collectp)))
    ((proof-compound term)
     (proof-with-checked-results ((operator (proof-term-at term 0)))
       (if (equal operator *proof-quote*)
           result
         (b2-substitution-return-values-args (1- n) (cdr term) lib result collectp))))
    (t result)))
 (defun b2-substitution-return-values-args (n args lib result collectp)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "b2-substitution-return-values-args"))
         ((endp args) result)
         (t
          (proof-with-checked-results
           ((result (b2-substitution-return-values-term (1- n) (car args) lib result collectp)))
           (b2-substitution-return-values-args (1- n) (cdr args) lib result collectp))))))

(defun b2-substitution-erase-return-values-collect (term lib)
  (proof-with-checked-results
   ((equations (b2-substitution-return-values-term 1000000 term lib nil t)))
   (reverse equations)))

(defun b2-substitution-erase-return-values (lib definition)
  (proof-with-checked-results ((value (b2-substitution-step-result definition)))
    (b2-substitution-return-values-term 1000000 value lib definition nil)))

(defun b2-substitution-original-tail (lib value predicate cons-proof not-quote)
  (proof-with-checked-results ((first (proof-step-first predicate)))
    (b2-tactics-tactics-from-impossible
     lib (list *b2-substitution-pseudo-list* (list *library-cdr* value))
     predicate (list cons-proof not-quote) (list first) nil 1500 nil)))

(defun b2-substitution-rebuild-statement-consequent
    (known lib head original goal nonquote tail-type length-eq)
  (let ((proof (library-library-proof lib))
        (cons-test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
     ((facts (b2-tactics-tactics-evidence lib (list known)))
      (original-proof (b2-substitution-required-value original facts))
      (cons-proof (b2-substitution-required-value cons-test facts))
      (nonquote-proof (b2-substitution-required-value nonquote facts))
      (valid-tail (b2-substitution-original-tail lib *library-x* original-proof
                                                cons-proof nonquote-proof))
      (old (proof-proof-unfold proof original))
      (old (b2-substitution-erase-return-values lib old))
      (old-body (b2-substitution-step-result old))
      (simplified (b2-tactics-tactics-normalize lib old-body
                                               (list valid-tail cons-proof nonquote-proof)
                                               nil nil 1500 nil))
      (old (proof-proof-chain proof old (list simplified)))
      (new (proof-proof-unfold proof goal))
      (car-axiom (library-library-axiom lib "CAR-CONS" (list head *library-y*)))
      (new (proof-proof-rewrite-first proof new car-axiom))
      (cdr-axiom (library-library-axiom lib "CDR-CONS" (list head *library-y*)))
      (new (proof-proof-rewrite-first proof new cdr-axiom))
      (new (b2-substitution-erase-return-values lib new))
      (cons (proof-proof-fact proof "consp-cons" (list (list *library-x* head)
                                                        (list *library-y* *library-y*))))
      (new-body (b2-substitution-step-result new))
      (tail-proof (b2-substitution-required-value tail-type facts))
      (simplified (b2-tactics-tactics-normalize lib new-body (list cons tail-proof nonquote-proof)
                                               nil nil 1500 nil))
      (new (proof-proof-chain proof new (list simplified)))
      (length-proof (b2-substitution-required-value length-eq facts))
      (new (proof-proof-rewrite-first proof new length-proof))
      (symmetric (proof-proof-symmetric proof old))
      (equation (proof-proof-chain proof new (list symmetric))))
     (proof-proof-transport proof original-proof equation))))

(defun b2-substitution-rebuild-statement (lib)
  (let ((name (proof-sym "B2-REBUILD-PSEUDO-TERM" "ACL2")))
    (if (assoc-equal name (b2-substitution-facts lib))
        (cons name lib)
      (let* ((head (list *library-car* *library-x*))
             (tail (list *library-cdr* *library-x*))
             (original (list *b2-association-pseudo-term* *library-x*))
             (pair (list *proof-cons* head *library-y*))
             (goal (list *b2-association-pseudo-term* pair))
             (nonquote (proof-neg (proof-eq head (proof-quote *proof-quote*))))
             (tail-type (list *b2-substitution-pseudo-list* *library-y*))
             (length-eq (proof-eq (list *library-len* *library-y*) (list *library-len* tail))))
        (proof-with-checked-results
         ((conditions (b2-powers-and-terms
                       (list original (list *proof-consp* *library-x*) nonquote tail-type length-eq)))
          (requested (b2-tactics-tactics-implication lib conditions goal nil))
          (known (nth 3 (car requested)))
          (step (b2-substitution-rebuild-statement-consequent
                 known lib head original goal nonquote tail-type length-eq))
          (proved (b2-tactics-tactics-implication lib conditions goal (cons step lib)))
          (step (car proved)))
         (b2-tactics-tactics-add-lemma (cdr proved) "REBUILD-PSEUDO-TERM" step :none))))))

(defun b2-substitution-preservation-children (steps cons-step number lib formula measure binding)
  (let ((proof (library-library-proof lib))
        (position (- number 2)))
    (proof-with-checked-results
     ((builtin (library-library-builtin lib number *library-x*))
      (descent (proof-proof-discharge proof builtin cons-step))
      (bindings (proof-term-at binding position))
      (hypothesis (b2-tactics-tactics-induction-hypothesis lib formula measure bindings descent))
      (conjuncts (proof-proof-conjunct proof hypothesis))
      (selected (proof-term-at conjuncts position))
      (first (proof-step-first selected))
      (condition (proof-term-at first 1))
      (premise (b2-tactics-tactics-solve lib condition steps nil nil 0 nil)))
     (proof-proof-modus-ponens proof selected premise))))

(defun b2-substitution-assume-signed (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
     ((pair (proof-list-of-length (car signed) 2))
      (assumption (proof-proof-assume proof (car pair) (cadr pair)))
      (rest (b2-substitution-assume-signed proof (cdr signed))))
     (cons assumption rest))))

(defun b2-substitution-preservation-preserve-terms-leaf
    (value signed lib premise usual formula measure binding)
  (let ((list-type (list *b2-substitution-pseudo-list* *library-x*)))
    (proof-with-checked-results
     ((projection (b2-substitution-pair-projection lib value))
      (lib (cdr projection))
      (projection (car projection))
      (new (b2-substitution-step-result projection)))
     (if (equal new *library-x*)
         (proof-with-checked-results
          ((valid (b2-substitution-required-value list-type premise))
           (step (library-library-transport-argument lib valid projection 1)))
          (cons step lib))
       (proof-with-checked-results
        ((signed (b2-substitution-assume-signed (library-library-proof lib) signed))
         (facts (b2-tactics-tactics-evidence lib signed))
         (cons-step (b2-substitution-required-value (list *proof-consp* *library-x*) facts))
         (valid (b2-substitution-required-value list-type premise))
         (conjuncts (b2-lists-opened-conjuncts lib valid (list cons-step)
                                               (list *b2-substitution-pseudo-list*)))
         (head (b2-substitution-preservation-children (append usual (list (car conjuncts)))
                                                       cons-step 2 lib formula measure binding))
         (tail (b2-substitution-preservation-children (append usual (list (cadr conjuncts)))
                                                       cons-step 3 lib formula measure binding))
         (goal (list *b2-substitution-pseudo-list* new))
         (step (b2-tactics-tactics-solve lib goal (list head tail) (list goal) nil 0 nil))
         (step (library-library-transport-argument lib step projection 1)))
        (cons step lib))))))

(defun b2-substitution-preservation-preserve-terms-leaves
    (requests lib premise usual formula measure binding answers)
  (if (endp requests)
      (cons answers lib)
    (let ((request (car requests)))
      (proof-with-checked-results
       ((leaf (b2-substitution-preservation-preserve-terms-leaf
               (car request) (cadr request) lib premise usual formula measure binding)))
       (b2-substitution-preservation-preserve-terms-leaves
        (cdr requests) (cdr leaf) premise usual formula measure binding
        (table-put answers request (car leaf)))))))

(defun b2-substitution-preservation-preserve-terms (antecedent lib alist usable formula measure binding)
  (let ((call (list *b2-substitution-terms* *b2-substitution-env* *library-x*))
        (template (list *b2-substitution-pseudo-list* (b2-substitution-second *proof-result*)))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((premise (b2-tactics-tactics-evidence lib (list antecedent)))
      (alist-proof (b2-substitution-required-value alist premise))
      (usable-proof (b2-substitution-required-value usable premise))
      (opened (proof-proof-unfold proof call))
      (value (b2-substitution-step-result opened))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaves (b2-substitution-preservation-preserve-terms-leaves
               requests lib premise (list alist-proof usable-proof) formula measure binding nil))
      (lib (cdr leaves))
      (step (b2-substitution-close-result-cases lib opened value template (car leaves))))
     (cons step lib))))

(defun b2-substitution-preservation-construct
    (lib new signed premise valid alist usable length-lemma rebuild formula measure binding)
  (if (not (proof-is-call new *b2-substitution-construct*))
      '(:failure "tactic-rejected" "")
    (let* ((proof (library-library-proof lib))
           (head (list *library-car* *library-x*))
           (quote-constant (proof-quote *proof-quote*))
           (quote-test (proof-eq head quote-constant)))
      (proof-with-checked-results
       ((signed-proofs (b2-substitution-assume-signed proof signed))
        (known (b2-tactics-tactics-evidence lib signed-proofs))
        (cons-step (b2-substitution-required-value (list *proof-consp* *library-x*) known))
        (opposite (b2-substitution-required-value (proof-neg (proof-eq quote-constant head)) known))
        (bad (proof-proof-assume proof quote-test t))
        (bad (proof-proof-symmetric proof bad))
        (nonquote (proof-proof-cut proof bad opposite))
        (nonquote (proof-proof-front proof nonquote (proof-neg quote-test)))
        (old-args (b2-substitution-original-tail lib *library-x* valid cons-step nonquote))
        (alist-proof (b2-substitution-required-value alist premise))
        (usable-proof (b2-substitution-required-value usable premise))
        (new-args (b2-substitution-preservation-children
                   (list alist-proof usable-proof old-args) cons-step 3 lib formula measure binding))
        (arity (proof-proof-fact proof length-lemma
                                  (list (list *library-x* (list *library-cdr* *library-x*)))))
        (args (proof-term-at new 2))
        (adjusted (proof-proof-fact proof rebuild (list (list *library-y* args))))
        (first (proof-step-first adjusted))
        (condition (proof-term-at first 1))
        (known-args (b2-tactics-tactics-solve lib condition
                                             (list valid cons-step nonquote new-args arity)
                                             nil nil 0 nil))
        (well-formed (proof-proof-modus-ponens proof adjusted known-args))
        (fn (proof-term-at new 1)))
       (b2-substitution-wrap-construction lib fn args well-formed)))))

(defun b2-substitution-preservation-association (lib term usable premise)
  (proof-with-checked-results
   ((opened (b2-tactics-tactics-normalize lib term nil nil nil 1500 nil))
    (normalized (b2-substitution-step-result opened))
    (available (b2-substitution-required-value usable premise))
    (typed (b2-tactics-tactics-use-fact
            lib (proof-sym "PSEUDO-TERMP-CDR-ASSOC-EQUAL" "ACL2")
            (list *b2-association-pseudo-term* normalized) (list available) nil nil 0 nil))
    (step (library-library-transport-argument lib typed opened 1)))
   (cons step lib)))

(defun b2-substitution-preservation-preserve-term-leaf
    (value signed lib premise valid alist usable length-lemma rebuild formula measure binding)
  (if (proof-is-call value *b2-substitution-fold-mv*)
      (b2-substitution-folded-term-property lib value valid)
    (proof-with-checked-results
     ((projection (b2-substitution-pair-projection lib value))
      (lib (cdr projection))
      (projection (car projection))
      (new (b2-substitution-step-result projection))
      (typed (cond ((equal new *library-x*) (cons valid lib))
                   ((proof-is-call new *library-cdr*)
                    (b2-substitution-preservation-association lib new usable premise))
                   (t
                    (b2-substitution-preservation-construct
                     lib new signed premise valid alist usable length-lemma rebuild
                     formula measure binding))))
      (lib (cdr typed))
      (step (library-library-transport-argument lib (car typed) projection 1)))
     (cons step lib))))

(defun b2-substitution-preservation-preserve-term-leaves
    (requests lib premise valid alist usable length-lemma rebuild formula measure binding answers)
  (if (endp requests)
      (cons answers lib)
    (let ((request (car requests)))
      (proof-with-checked-results
       ((leaf (b2-substitution-preservation-preserve-term-leaf
               (car request) (cadr request) lib premise valid alist usable length-lemma rebuild
               formula measure binding)))
       (b2-substitution-preservation-preserve-term-leaves
        (cdr requests) (cdr leaf) premise valid alist usable length-lemma rebuild
        formula measure binding (table-put answers request (car leaf)))))))

(defun b2-substitution-preservation-preserve-term
    (antecedent lib alist usable length-lemma rebuild formula measure binding)
  (let ((call (list *b2-substitution-term* *b2-substitution-env* *library-x*))
        (template (list *b2-association-pseudo-term* (b2-substitution-second *proof-result*)))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((premise (b2-tactics-tactics-evidence lib (list antecedent)))
      (valid (b2-substitution-required-value (list *b2-association-pseudo-term* *library-x*) premise))
      (opened (proof-proof-unfold proof call))
      (value (b2-substitution-step-result opened))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaves (b2-substitution-preservation-preserve-term-leaves
               requests lib premise valid alist usable length-lemma rebuild formula measure binding nil))
      (lib (cdr leaves))
      (step (b2-substitution-close-result-cases lib opened value template (car leaves))))
     (cons step lib))))

(defun b2-substitution-preservation-half (alist usable predicate fn)
  (proof-with-checked-results
   ((condition (b2-powers-and-terms (list alist usable (list predicate *library-x*)))))
   (list *library-implies* condition (list predicate (b2-substitution-output fn *library-x*)))))

(defun b2-substitution-preservation-proof (lib length-lemma rebuild)
  (let ((alist (list *b2-substitution-salist* *b2-substitution-env*))
        (usable (list *b2-substitution-pseudo-list* (list *b2-association-strip*
                                                        *b2-substitution-env*)))
        (binding (list (list (list *library-x* (list *library-car* *library-x*)))
                       (list (list *library-x* (list *library-cdr* *library-x*)))))
        (measure (list *library-count* *library-x*)))
    (proof-with-checked-results
     ((term (b2-substitution-preservation-half alist usable *b2-association-pseudo-term*
                                              *b2-substitution-term*))
      (terms (b2-substitution-preservation-half alist usable *b2-substitution-pseudo-list*
                                               *b2-substitution-terms*))
      (formula (b2-powers-and-terms (list term terms)))
      (requested (b2-tactics-tactics-implication lib (cadr term) (caddr term) nil))
      (proved (b2-substitution-preservation-preserve-term
               (nth 3 (car requested)) lib alist usable length-lemma rebuild formula measure binding))
      (first (b2-tactics-tactics-implication lib (cadr term) (caddr term) proved))
      (lib (cdr first))
      (requested (b2-tactics-tactics-implication lib (cadr terms) (caddr terms) nil))
      (proved (b2-substitution-preservation-preserve-terms
               (nth 3 (car requested)) lib alist usable formula measure binding))
      (second (b2-tactics-tactics-implication lib (cadr terms) (caddr terms) proved))
      (lib (cdr second))
      (case-step (b2-tactics-tactics-solve lib formula (list (car first) (car second)) nil nil 0 nil))
      (ordinal (library-library-builtin lib 1 *library-x*))
      (proof (proof-proof-induct (library-library-proof lib) ordinal case-step formula measure binding)))
     (cons proof lib))))

(defun b2-substitution-preservation (lib)
  (let ((name (proof-sym "B2-SUBLIS-PSEUDO-TERMS" "ACL2")))
    (if (assoc-equal name (b2-substitution-facts lib))
        (cons name lib)
      (proof-with-checked-results
       ((length-lemma (b2-substitution-size-preserved lib))
        (rebuild (b2-substitution-rebuild-statement (cdr length-lemma)))
        (proved (b2-substitution-preservation-proof (cdr rebuild) (car length-lemma) (car rebuild))))
       (b2-tactics-tactics-add-lemma (cdr proved) "SUBLIS-PSEUDO-TERMS" (car proved) :none)))))

(defun b2-substitution-first-matching-conjunct (steps formula)
  (if (endp steps)
      '(:failure "failure" "")
    (proof-with-checked-results ((first (proof-step-first (car steps))))
      (if (equal first formula)
          (car steps)
        (b2-substitution-first-matching-conjunct (cdr steps) formula)))))

(defun b2-substitution-substitution-preserves-term (lib name formula)
  (declare (ignore name))
  (proof-with-checked-results
   ((preserved (b2-substitution-preservation lib))
    (lib (cdr preserved))
    (proof (library-library-proof lib))
    (fact (proof-proof-fact proof (car preserved) nil))
    (conjuncts (proof-proof-conjunct proof fact))
    (step (b2-substitution-first-matching-conjunct conjuncts formula)))
   (cons step lib)))
