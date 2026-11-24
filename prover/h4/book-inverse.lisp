(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-inverse-atoc-type* (proof-sym "oa.x  <=>  oc(atoc.x)" "ACL2"))
(defconst *h4-book-inverse-ctoa-type* (proof-sym "oc.x  <=>  oa(ctoa.x)" "ACL2"))
(defconst *h4-book-inverse-inverse-conversion*
  (proof-sym "H4-EXPANSION-INVERTS-COMPRESSION" "ACL2"))

(defun h4-book-inverse-step-argument (step index)
  (proof-with-checked-results
    ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h4-book-inverse-compression-type (p e0-ordinal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((subject (h4-book-inverse-step-argument e0-ordinal 1))
       (instance (proof-proof-fact
                  proof *h4-book-inverse-atoc-type* (list (list *library-x* subject)))))
      (h4-tactics-tactics-modus-ponens p instance e0-ordinal))))

(defun h4-book-inverse-converted-constructor (p term continuing)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((arguments (if (integerp term)
                     '(:failure "failure" "")
                   (proof-list-of-length (cdr term) 3)))
       (cells (h4-book-compression-ordinal-cells
               p (car arguments) (cadr arguments) (caddr arguments)))
       (opened (proof-proof-unfold proof term))
       (lifted (h4-book-flatten-rewrite-argument
                p (list *h4-book-expansion-ctoa* term) 1 opened))
       (exposed (h4-book-order-order-view
                 p (list *h4-book-expansion-ctoa* (car cells)) (cadr cells) nil))
       (rhs (h4-book-inverse-step-argument exposed 2))
       (fields (h4-tactics-tactics-normalize p rhs nil nil (caddr cells) nil))
       (spliced (h4-book-expansion-copied-prefix
                 p (list *h4-book-expansion-ctoa* (car arguments)) (cadr arguments)
                 (list *h4-book-expansion-ctoa* (caddr arguments)) continuing)))
      (proof-proof-chain proof lifted (list exposed fields spliced)))))

(defun h4-book-inverse-nonzero-inverse (p identity original)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((converted (h4-book-inverse-step-argument identity 1))
       (exponent (proof-term-at converted 1)))
      (let ((test (proof-eq exponent *proof-zero*)))
        (proof-with-checked-results
          ((assumed (proof-proof-assume proof test t))
           (changed (proof-proof-rewrite proof identity assumed (list 1 1 1)))
           (at-zero (h4-book-order-order-view p (list *h4-book-expansion-ctoa* *proof-zero*) nil nil))
           (same (proof-proof-rewrite proof changed at-zero (list 1 1)))
           (symmetric (proof-proof-symmetric proof same))
           (contradiction (proof-proof-cut proof symmetric original)))
          (proof-proof-front proof contradiction (proof-neg test)))))))

(defun h4-book-inverse-expansion-of-sum-inserted
  (changed p one-active exponent right one-stopped exp-identity suffix-identity source)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((term (h4-book-inverse-step-argument changed 2))
       (exposed (h4-book-inverse-converted-constructor p term one-active))
       (tail (h4-book-expansion-copied-prefix
              p (list *h4-book-expansion-ctoa* exponent)
              (h4-book-arithmetic-predecessor *proof-one*)
              (list *h4-book-expansion-ctoa* right) one-stopped))
       (exposed (proof-proof-rewrite proof exposed tail (list 1 2 2)))
       (with-head (proof-proof-rewrite proof exposed exp-identity (list 1 2 1)))
       (joined (proof-proof-rewrite proof with-head suffix-identity (list 1 2 2)))
       (lifted (h4-book-flatten-rewrite-argument p source 1 changed)))
      (proof-proof-chain proof lifted (list joined)))))

(defun h4-book-inverse-expansion-of-sum-finite
  (shape result p exponent-type nonzero one-active exponent right one-stopped
         exp-identity suffix-identity source)
  (proof-with-checked-results
    ((bounds (h4-book-compression-singleton-sum-finite-bounds
              result p exponent-type nonzero shape))
     (changed (h4-book-compression-singleton-sum-reduce result p shape (car bounds))))
    (h4-book-inverse-expansion-of-sum-inserted
     changed p one-active exponent right one-stopped exp-identity suffix-identity source)))

(defun h4-book-inverse-expansion-of-sum-infinite-unequal
  (strict result p shape no-less one-active exponent right one-stopped
          exp-identity suffix-identity source)
  (proof-with-checked-results
    ((changed (h4-book-compression-singleton-sum-reduce result p shape (list no-less strict))))
    (h4-book-inverse-expansion-of-sum-inserted
     changed p one-active exponent right one-stopped exp-identity suffix-identity source)))

(defun h4-book-inverse-expansion-of-sum-infinite-equal
  (no-greater p exponent expansion exponent-type power-type no-less
              result shape suffix-identity exp-identity source)
  (let* ((proof (library-library-proof p))
         (count (h4-book-expansion-ordinal-expansion-count expansion))
         (key (list *h4-book-order-posp* count)))
    (proof-with-checked-results
      ((tied (proof-proof-fact
              proof *h4-book-order-order-ties*
              (list (list *library-x* exponent)
                    (list *library-y* (h4-book-expansion-ordinal-expansion-power expansion)))))
       (evidence (h4-book-division-conjunction p (list exponent-type power-type no-less no-greater)))
       (same (h4-tactics-tactics-modus-ponens p tied evidence))
       (addition (h4-book-compression-singleton-sum-reduce result p shape (list no-less no-greater)))
       (entry (assoc-equal key (h4-book-expansion-ordinal-expansion-pieces expansion)))
       (positive (if entry (cdr entry) '(:failure "failure" "")))
       (larger (h4-book-compression-coefficient-successor p positive))
       (sum (h4-book-inverse-step-argument addition 2))
       (continuing (h4-book-expansion-active-count p larger))
       (exposed (h4-book-inverse-converted-constructor p sum continuing))
       (literal (proof-step-first positive))
       (opened (proof-proof-unfold proof literal))
       (typed (proof-proof-rewrite proof positive opened (list 1)))
       (conjuncts (h4-tactics-tactics-conjunct p typed))
       (uncancel (library-library-linear-equal
                  p (h4-book-arithmetic-predecessor (library-plus *proof-one* count))
                  count (list (car conjuncts))))
       (exposed (proof-proof-rewrite proof exposed uncancel (list 1 2 2 1 2)))
       (closed (proof-proof-symmetric proof (h4-book-expansion-ordinal-expansion-opened expansion)))
       (exposed (proof-proof-rewrite proof exposed closed (list 1 2 2)))
       (exposed (proof-proof-rewrite proof exposed suffix-identity (list 1 2 2)))
       (shifted (h4-book-flatten-rewrite-argument p (list *h4-book-expansion-ctoa* exponent) 1 same))
       (symmetric (proof-proof-symmetric proof shifted))
       (exposed (proof-proof-rewrite proof exposed symmetric (list 1 2 1)))
       (exposed (proof-proof-rewrite proof exposed exp-identity (list 1 2 1)))
       (lifted (h4-book-flatten-rewrite-argument p source 1 addition)))
      (proof-proof-chain proof lifted (list exposed)))))

(defun h4-book-inverse-expansion-of-sum-infinite
  (shape p right-type suffix-identity original-tail sorted-tail exp-identity
         order exponent-type exponent result one-active right one-stopped source goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((expansion (h4-book-expansion-ordinal-expansion-init p right-type shape))
       (power-type (h4-book-expansion-ordinal-expansion-power-type expansion))
       (spine (h4-book-expansion-ordinal-expansion-spine expansion))
       (result-pair (h4-book-inverse-step-argument spine 2))
       (pair (proof-proof-fact
              proof "consp-cons" (seq-zip (list *library-x* *library-y*) (cdr result-pair))))
       (actual-shape (library-library-transport-argument p pair spine 1))
       (actual-shape (proof-proof-rewrite proof actual-shape suffix-identity (list 1 1)))
       (not-atom (h4-tactics-tactics-establish
                  p (proof-neg (list (proof-cl "ATOM") original-tail))
                  (list actual-shape) *h4-book-flatten-logic* nil nil))
       (bounded (proof-proof-prove-if proof sorted-tail not-atom))
       (symmetric (proof-proof-symmetric proof suffix-identity))
       (head (h4-book-flatten-rewrite-argument p (list *library-car* original-tail) 1 symmetric))
       (raw-head (h4-book-flatten-rewrite-argument
                  p (list *library-car* (h4-book-expansion-ordinal-expansion-converted expansion))
                  1 spine))
       (car-cons (library-library-axiom p "CAR-CONS" (cdr result-pair)))
       (first (proof-proof-chain proof head (list raw-head car-cons)))
       (symmetric (proof-proof-symmetric proof exp-identity))
       (abstract (proof-proof-rewrite proof bounded symmetric (list 1 1 1)))
       (abstract (proof-proof-rewrite proof abstract first (list 1 1 2)))
       (comparisons (h4-book-expansion-compare-expansions p order exponent-type power-type))
       (no-less (proof-proof-rewrite proof abstract (car comparisons) (list 1 1))))
      (let ((test (list *proof-ordinal-less*
                        (h4-book-expansion-ordinal-expansion-power expansion) exponent)))
        (proof-with-checked-results
          ((positive (proof-proof-assume proof test t))
           (yes (h4-book-inverse-expansion-of-sum-infinite-unequal
                 positive result p shape no-less one-active exponent right one-stopped
                 exp-identity suffix-identity source))
           (negative (proof-proof-assume proof test nil))
           (no (h4-book-inverse-expansion-of-sum-infinite-equal
                negative p exponent expansion exponent-type power-type no-less
                result shape suffix-identity exp-identity source)))
          (h4-tactics-tactics-case-of p goal test yes no))))))

; Expand one merged or inserted exponent onto the original suffix.
(defun h4-book-inverse-expansion-of-sum
  (p exponent-type right-type nonzero exp-identity suffix-identity sorted-tail order)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((exponent (h4-book-inverse-step-argument exponent-type 1))
       (right (h4-book-inverse-step-argument right-type 1))
       (original-head (h4-book-inverse-step-argument exp-identity 2))
       (original-tail (h4-book-inverse-step-argument suffix-identity 2))
       (result (h4-book-compression-singleton-sum-init p exponent right-type)))
      (let* ((source (list *h4-book-expansion-ctoa*
                           (h4-book-compression-singleton-sum-result result)))
             (goal (proof-eq source (list *proof-cons* original-head original-tail)))
             (expand (list *h4-book-arithmetic-zp* *proof-not*))
             (test (list *proof-consp* right)))
        (proof-with-checked-results
          ((one-active (h4-tactics-tactics-establish
                        p (proof-neg (list *h4-book-arithmetic-zp* *proof-one*)) nil expand nil nil))
           (one-stopped (h4-tactics-tactics-establish
                         p (list *h4-book-arithmetic-zp* (h4-book-arithmetic-predecessor *proof-one*))
                         nil expand nil nil))
           (positive (proof-proof-assume proof test t))
           (yes (h4-book-inverse-expansion-of-sum-infinite
                 positive p right-type suffix-identity original-tail sorted-tail exp-identity
                 order exponent-type exponent result one-active right one-stopped source goal))
           (negative (proof-proof-assume proof test nil))
           (no (h4-book-inverse-expansion-of-sum-finite
                negative result p exponent-type nonzero one-active exponent right one-stopped
                exp-identity suffix-identity source)))
          (h4-tactics-tactics-case-of p goal test yes no))))))

(defun h4-book-inverse-expansion-inverts-compression-atom (shape p goal formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((opened (h4-book-order-order-view p (list *h4-book-compression-atoc* *library-x*) (list shape) nil))
       (lifted (h4-book-flatten-rewrite-argument p (cadr goal) 1 opened))
       (expanded (h4-book-order-order-view p (list *h4-book-expansion-ctoa* *library-x*) (list shape) nil))
       (joined (proof-proof-chain proof lifted (list expanded))))
      (h4-tactics-tactics-imply p formula joined))))

(defun h4-book-inverse-expansion-inverts-compression-child
  (p shape formula index substitution typed)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((bound (library-library-builtin p index *library-x*))
       (smaller (proof-proof-discharge proof bound shape))
       (child (proof-subst formula (list (cons (caar substitution) (cadar substitution)))))
       (literal (proof-step-first smaller))
       (assumed (proof-proof-assume proof (proof-ite literal child *proof-true*) t))
       (hypothesis (proof-proof-prove-if proof assumed smaller)))
      (h4-tactics-tactics-modus-ponens p hypothesis typed))))

(defun h4-book-inverse-expansion-inverts-compression-pair
  (shape p source given bindings formula goal order)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((opened (h4-book-order-order-view p (list *h4-book-compression-atoc* *library-x*) (list shape) nil))
       (type-view (h4-book-order-order-view p source (list shape) nil))
       (body (proof-proof-rewrite proof given type-view (list 1)))
       (parts (h4-book-list-types-conjunct-proofs p body))
       (parts (proof-list-of-length parts 4)))
      (let ((head-type (car parts))
            (nonzero (cadr parts))
            (tail-type (caddr parts))
            (sorted-tail (cadddr parts)))
        (proof-with-checked-results
          ((head (h4-book-inverse-expansion-inverts-compression-child
                  p shape formula 2 (car bindings) head-type))
           (tail (h4-book-inverse-expansion-inverts-compression-child
                  p shape formula 3 (cadr bindings) tail-type))
           (ex-type (h4-book-inverse-compression-type p head-type))
           (right-type (h4-book-inverse-compression-type p tail-type))
           (ex-nonzero (h4-book-inverse-nonzero-inverse p head nonzero))
           (result (h4-book-inverse-expansion-of-sum
                    p ex-type right-type ex-nonzero head tail sorted-tail order))
           (eliminate (library-library-axiom p "CAR-CDR-ELIM" (list *library-x*)))
           (rebuilt (h4-tactics-tactics-modus-ponens p eliminate shape))
           (lifted (h4-book-flatten-rewrite-argument p (cadr goal) 1 opened))
           (joined (proof-proof-chain proof lifted (list result rebuilt))))
          (h4-tactics-tactics-imply p formula joined))))))

(defun h4-book-inverse-expansion-inverts-compression (p order)
  (let* ((source (list *h4-book-expansion-e0-ordinal* *library-x*))
         (goal (proof-eq (list *h4-book-expansion-ctoa*
                               (list *h4-book-compression-atoc* *library-x*))
                         *library-x*))
         (formula (list *library-implies* source goal))
         (bindings (list (list (list *library-x* (list *library-car* *library-x*)))
                         (list (list *library-x* (list *library-cdr* *library-x*)))))
         (proof (library-library-proof p))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
      ((given (proof-proof-assume proof source t))
       (positive (proof-proof-assume proof test t))
       (yes (h4-book-inverse-expansion-inverts-compression-pair
             positive p source given bindings formula goal order))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-inverse-expansion-inverts-compression-atom negative p goal formula))
       (cases (h4-tactics-tactics-case-of p formula test yes no))
       (ordinal (library-library-builtin p 1 *library-x*)))
      (proof-proof-induct proof ordinal cases formula (list *library-count* *library-x*) bindings))))

(defun h4-book-inverse-expansion-injective-bound (p step comparison)
  (proof-with-checked-results
    ((denied (h4-book-order-false-value p step)))
    (proof-proof-rewrite (library-library-proof p) denied comparison (list 1 1))))

(defun h4-book-inverse-expansion-injective (p expansions left-type right-type equality)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((left (h4-book-inverse-step-argument left-type 1))
       (right (h4-book-inverse-step-argument right-type 1))
       (reflexive (or (h4-book-expansion-expansion-proofs-reflexive expansions)
                      '(:failure "failure" "")))
       (self-order (proof-proof-instantiate
                    proof reflexive
                    (list (list *library-x* (list *h4-book-expansion-ctoa* left)))))
       (forward (proof-proof-rewrite proof self-order equality (list 1 1 2)))
       (backward (proof-proof-rewrite proof self-order equality (list 1 1 1)))
       (comparisons (h4-book-expansion-compare-expansions
                     p (h4-book-expansion-expansion-proofs-order expansions) left-type right-type))
       (forward-bound (h4-book-inverse-expansion-injective-bound p forward (car comparisons)))
       (backward-bound (h4-book-inverse-expansion-injective-bound p backward (cadr comparisons)))
       (tied (proof-proof-fact proof *h4-book-order-order-ties*
                              (list (list *library-x* left) (list *library-y* right))))
       (guard (h4-book-division-conjunction p (list left-type right-type forward-bound backward-bound))))
      (h4-tactics-tactics-modus-ponens p tied guard))))

(defun h4-book-inverse-atom-expansion-pair (shape p typed atom goal formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((expansion (h4-book-expansion-ordinal-expansion-init p typed shape))
       (spine (h4-book-expansion-ordinal-expansion-spine expansion))
       (raw (h4-book-inverse-step-argument spine 2))
       (exists (proof-proof-fact proof "consp-cons" (seq-zip (list *library-x* *library-y*) (cdr raw))))
       (converted (library-library-transport-argument p exists spine 1))
       (literal (proof-step-first atom))
       (no-atom (h4-tactics-tactics-establish
                 p (proof-neg literal) (list converted) *h4-book-flatten-logic* nil nil))
       (conflict (proof-proof-cut proof atom no-atom))
       (weakened (proof-proof-subsume proof conflict (cons goal (proof-step-clause conflict)))))
      (h4-tactics-tactics-imply p formula weakened))))

(defun h4-book-inverse-atom-expansion-finite (shape p goal formula)
  (proof-with-checked-results
    ((left (proof-term-at goal 1))
     (opened (h4-book-order-order-view p left (list shape) nil)))
    (h4-tactics-tactics-imply p formula opened)))

(defun h4-book-inverse-atom-expansion (p formula subject)
  (let ((proof (library-library-proof p))
        (test (list *proof-consp* subject)))
    (proof-with-checked-results
      ((guard (proof-term-at formula 1))
       (assumed (proof-proof-assume proof guard t))
       (parts (h4-tactics-tactics-conjunct p assumed))
       (goal (proof-term-at formula 2))
       (positive (proof-proof-assume proof test t))
       (yes (h4-book-inverse-atom-expansion-pair positive p (car parts) (cadr parts) goal formula))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-inverse-atom-expansion-finite negative p goal formula)))
      (h4-tactics-tactics-case-of p formula test yes no))))

(defun h4-book-inverse-inverse-shape-order (guard left right)
  (proof-with-checked-results
    ((operands (proof-list-of-length (cdr right) 2)))
    (let ((a (car operands))
          (b (cadr operands)))
      (and (not (proof-compound a))
           (not (proof-compound b))
           (equal left (list *proof-ordinal-less*
                             (list *h4-book-compression-atoc* a)
                             (list *h4-book-compression-atoc* b)))
           (equal guard (proof-ite (list *h4-book-expansion-e0-ordinal* a)
                                   (list *h4-book-expansion-e0-ordinal* b) *proof-false*))
           (list "compression order" a b)))))

(defun h4-book-inverse-inverse-shape-equality (guard left right)
  (proof-with-checked-results
    ((operands (proof-list-of-length (cdr right) 2)))
    (let ((a (car operands))
          (b (cadr operands)))
      (and (not (proof-compound a))
           (not (proof-compound b))
           (cond
            ((and (equal left (proof-eq (list *h4-book-expansion-ctoa* a)
                                        (list *h4-book-expansion-ctoa* b)))
                  (equal guard (proof-ite (list *proof-ordinalp* a)
                                          (list *proof-ordinalp* b) *proof-false*)))
             (list "expansion equality" a b))
            ((and (equal left (proof-eq (list *h4-book-compression-atoc* a)
                                        (list *h4-book-compression-atoc* b)))
                  (equal guard (proof-ite (list *h4-book-expansion-e0-ordinal* a)
                                          (list *h4-book-expansion-e0-ordinal* b) *proof-false*)))
             (list "compression equality" a b)))))))

(defun h4-book-inverse-inverse-shape (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results
         ((goal (proof-term-at formula 2)))
         (and (proof-is-call goal *proof-equal*)
              (proof-with-checked-results
                ((parts (proof-list-of-length (cdr formula) 2))
                 (sides (proof-list-of-length goal 3)))
                (let* ((guard (car parts))
                       (left (cadr sides))
                       (right (caddr sides))
                       (e0-type (proof-is-call guard *h4-book-expansion-e0-ordinal*))
                       (ordinal-type (proof-is-call guard *proof-ordinalp*))
                       (expansion (proof-is-call left *h4-book-expansion-ctoa*)))
                  (proof-with-checked-results
                    ((subject (and (or e0-type ordinal-type) (proof-term-at guard 1))))
                    (cond
                     ((and e0-type
                           (equal subject right)
                           (not (proof-compound right))
                           (equal left (list *h4-book-expansion-ctoa*
                                             (list *h4-book-compression-atoc* right))))
                      (list "expansion after compression" right))
                     ((and ordinal-type
                           (equal subject right)
                           (equal left (list *h4-book-compression-atoc*
                                             (list *h4-book-expansion-ctoa* right))))
                      (list "compression after expansion" right))
                     (t
                      (proof-with-checked-results
                        ((argument (and expansion (proof-term-at left 1))))
                        (cond
                         ((and expansion
                               (equal argument right)
                               (not (proof-compound right))
                               (equal guard (proof-ite (list *proof-ordinalp* right)
                                                       (list (proof-cl "ATOM") left) *proof-false*)))
                          (list "finite expansion" right))
                         ((proof-is-call right *h4-book-expansion-e0-less*)
                          (h4-book-inverse-inverse-shape-order guard left right))
                         ((and (proof-is-call left *proof-equal*)
                               (proof-is-call right *proof-equal*))
                          (h4-book-inverse-inverse-shape-equality guard left right)))))))))))))

(defun h4-book-inverse-make-inversion-proofs (expansions inverse)
  (list :h4-book-inverse-inversion-proofs expansions inverse))

(defun h4-book-inverse-inversion-proofs-init (expansions)
  (h4-book-inverse-make-inversion-proofs expansions nil))

(defun h4-book-inverse-inversion-proofs-expansions (self)
  (cadr self))

(defun h4-book-inverse-inversion-proofs-inverse (self)
  (caddr self))

(defun h4-book-inverse-inversion-proofs-with-expansions (self expansions)
  (h4-book-inverse-make-inversion-proofs expansions
                                         (h4-book-inverse-inversion-proofs-inverse self)))

(defun h4-book-inverse-with-facts (p facts)
  (library-library-with-proof p (proof-proof-with-facts (library-library-proof p) facts)))

(defun h4-book-inverse-inversion-proofs-prepare (self p)
  (proof-with-checked-results
    ((prepared (h4-book-expansion-expansion-proofs-prepare
                (h4-book-inverse-inversion-proofs-expansions self) p)))
    (let* ((self (h4-book-inverse-inversion-proofs-with-expansions self (car prepared)))
           (p (cadr prepared))
           (proof (library-library-proof p))
           (inverse (h4-book-inverse-inversion-proofs-inverse self)))
      (if inverse
          (list self
                (h4-book-inverse-with-facts
                 p (table-put (proof-proof-facts proof) *h4-book-inverse-inverse-conversion*
                                (proof-step-clause inverse))))
        (proof-with-checked-results
          ((lemma (h4-book-inverse-expansion-inverts-compression
                   p (h4-book-expansion-expansion-proofs-order (car prepared))))
           (added (h4-tactics-tactics-local-lemma p *h4-book-inverse-inverse-conversion* lemma))
           (inverse (proof-proof-fact (library-library-proof (cdr added))
                                      *h4-book-inverse-inverse-conversion* nil)))
          (list (h4-book-inverse-make-inversion-proofs (car prepared) inverse) (cdr added)))))))

(defun h4-book-inverse-inversion-proofs-apply (self p proof-step)
  (proof-with-checked-results
    ((subject (h4-book-inverse-step-argument proof-step 1)))
    (let ((inverse (h4-book-inverse-inversion-proofs-inverse self)))
      (cond
       (inverse
        (proof-with-checked-results
          ((instance (proof-proof-instantiate
                     (library-library-proof p) inverse (list (list *library-x* subject)))))
          (h4-tactics-tactics-modus-ponens p instance proof-step)))
       ((equal subject *library-x*)
        '(:failure "failure" ""))
       (t '(:failure "failure" ""))))))

(defun h4-book-inverse-inversion-proofs-from-compressed-equality (self p equality left-type right-type)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((left (h4-book-inverse-step-argument equality 1))
       (opened (h4-book-flatten-rewrite-argument p (list *h4-book-expansion-ctoa* left) 1 equality))
       (applied (h4-book-inverse-inversion-proofs-apply self p left-type))
       (first (proof-proof-symmetric proof applied))
       (last (h4-book-inverse-inversion-proofs-apply self p right-type)))
      (proof-proof-chain proof first (list opened last)))))

(defun h4-book-inverse-conversion-equality-same (proof-step p goal)
  (h4-tactics-tactics-establish p goal nil nil (list proof-step) nil))

(defun h4-book-inverse-conversion-equality-different
  (proof-step p converted evidence invert goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((assumed (proof-proof-assume proof converted t))
       (refute
        (if (eq (car invert) :expansion)
            (h4-book-inverse-expansion-injective p (cadr invert)
                                                 (car evidence) (cadr evidence) assumed)
          (h4-book-inverse-inversion-proofs-from-compressed-equality
           (cadr invert) p assumed (car evidence) (cadr evidence))))
       (conflict (proof-proof-cut proof refute proof-step))
       (denied (proof-proof-front proof conflict (proof-neg converted))))
      (h4-tactics-tactics-establish p goal (list proof-step denied) nil nil nil))))

(defun h4-book-inverse-conversion-equality (p formula evidence invert)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (sides (if (integerp goal)
                  '(:failure "failure" "")
                (proof-list-of-length (cdr goal) 2))))
      (let ((converted (car sides))
            (original (cadr sides)))
        (proof-with-checked-results
          ((positive (proof-proof-assume proof original t))
           (yes (h4-book-inverse-conversion-equality-same positive p goal))
           (negative (proof-proof-assume proof original nil))
           (no (h4-book-inverse-conversion-equality-different
                negative p converted evidence invert goal))
           (cases (h4-tactics-tactics-case-of p goal original yes no)))
          (h4-tactics-tactics-imply p formula cases))))))

(defun h4-book-inverse-inversion-proofs-prove-compression-after-expansion
  (self p formula given subject)
  (proof-with-checked-results
    ((rule (proof-proof-fact (library-library-proof p) *h4-book-inverse-ctoa-type*
                             (list (list *library-x* subject))))
     (typed (h4-tactics-tactics-modus-ponens p rule given))
     (compressed (h4-book-inverse-compression-type p typed))
     (identity (h4-book-inverse-inversion-proofs-apply self p typed))
     (result (h4-book-inverse-expansion-injective
              p (h4-book-inverse-inversion-proofs-expansions self) compressed given identity)))
    (h4-tactics-tactics-imply p formula result)))

(defun h4-book-inverse-inversion-proofs-prove-compression-order (self p formula given)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((types (h4-tactics-tactics-conjunct p given))
       (ex-type (h4-book-inverse-compression-type p (car types)))
       (ey-type (h4-book-inverse-compression-type p (cadr types)))
       (comparisons (h4-book-expansion-compare-expansions
                     p (h4-book-expansion-expansion-proofs-order
                        (h4-book-inverse-inversion-proofs-expansions self))
                     ex-type ey-type))
       (x-original (h4-book-inverse-inversion-proofs-apply self p (car types)))
       (comparison (proof-proof-rewrite proof (car comparisons) x-original (list 1 1 1)))
       (y-original (h4-book-inverse-inversion-proofs-apply self p (cadr types)))
       (comparison (proof-proof-rewrite proof comparison y-original (list 1 1 2)))
       (symmetric (proof-proof-symmetric proof comparison)))
      (h4-tactics-tactics-imply p formula symmetric))))

(defun h4-book-inverse-inversion-proofs-prove-prepared (self p formula given mode subjects)
  (cond
   ((equal mode "expansion after compression")
    (proof-with-checked-results
      ((result (h4-book-inverse-inversion-proofs-apply self p given)))
      (h4-tactics-tactics-imply p formula result)))
   ((equal mode "compression after expansion")
    (h4-book-inverse-inversion-proofs-prove-compression-after-expansion
     self p formula given (car subjects)))
   ((equal mode "compression equality")
    (proof-with-checked-results
      ((evidence (h4-tactics-tactics-conjunct p given)))
      (h4-book-inverse-conversion-equality p formula evidence (list :compression self))))
   (t (h4-book-inverse-inversion-proofs-prove-compression-order self p formula given))))

(defun h4-book-inverse-inversion-proofs-prove-with-support
  (self p formula match support)
  (let* ((previous (proof-proof-facts (library-library-proof p)))
         (p (h4-book-inverse-with-facts p (table-update previous support)))
         (mode (car match)))
    (proof-with-checked-results
      ((guard (proof-term-at formula 1))
       (given (proof-proof-assume (library-library-proof p) guard t)))
      (if (equal mode "expansion equality")
          (proof-with-checked-results
            ((prepared (h4-book-expansion-expansion-proofs-prepare
                        (h4-book-inverse-inversion-proofs-expansions self) p))
             (expansions (car prepared))
             (p (cadr prepared))
             (evidence (h4-tactics-tactics-conjunct p given))
             (step (h4-book-inverse-conversion-equality
                    p formula evidence (list :expansion expansions))))
            (list step (h4-book-inverse-inversion-proofs-with-expansions self expansions)
                  (h4-book-inverse-with-facts p previous)))
        (proof-with-checked-results
          ((prepared (h4-book-inverse-inversion-proofs-prepare self p))
           (step (h4-book-inverse-inversion-proofs-prove-prepared
                  (car prepared) (cadr prepared) formula given mode (cdr match))))
          (list step (car prepared) (h4-book-inverse-with-facts (cadr prepared) previous)))))))

(defun h4-book-inverse-inversion-proofs-prove (self p formula support)
  (proof-with-checked-results
    ((match (h4-book-inverse-inverse-shape formula)))
    (cond
     ((or (not match) (not support)) (list nil self p))
     ((equal (car match) "finite expansion")
      (proof-with-checked-results
        ((step (h4-book-inverse-atom-expansion p formula (cadr match))))
        (list step self p)))
     ((and (not (equal (car match) "expansion equality"))
           (not (assoc-equal *h4-book-inverse-atoc-type* (proof-proof-facts (library-library-proof p)))))
      (list nil self p))
     (t (h4-book-inverse-inversion-proofs-prove-with-support self p formula match support)))))
