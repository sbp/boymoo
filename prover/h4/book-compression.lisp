(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-compression-e0-ordinal* (proof-sym "E0-ORDINALP" "ACL2"))
(defconst *h4-book-compression-atoc* (proof-sym "ATOC" "ACL2"))
(defconst *h4-book-compression-add* (proof-sym "OB+" "ACL2"))
(defconst *h4-book-compression-fix* (proof-sym "FIX" "ACL2"))

(defun h4-book-compression-cons-evidence (p value)
  (let ((proof (library-library-proof p))
        (parts (cdr value)))
    (if (integerp value)
        '(:failure "failure" "")
      (proof-with-checked-results
          ((shape (proof-proof-fact proof "consp-cons"
                                    (seq-zip (list *library-x* *library-y*) parts)))
           (head (library-library-axiom p "CAR-CONS" parts))
           (tail (library-library-axiom p "CDR-CONS" parts)))
        (list shape head tail)))))

(defun h4-book-compression-nonzero-cons (p shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first shape))
         (subject (proof-term-at literal 1))
         (test (proof-eq subject *proof-zero*))
         (assumed (proof-proof-assume proof test t))
         (clash (proof-proof-rewrite proof shape assumed '(1 1)))
         (computed (proof-proof-compute proof (list *proof-consp* *proof-zero*)
                                        (cadr *proof-false*)))
         (false-step (proof-proof-rewrite proof clash computed '(1)))
         (tidied (proof-proof-tidy proof false-step)))
      (proof-proof-front proof tidied (proof-neg test)))))

(defun h4-book-compression-ordinal-cells-projection (p raw facts selector outer inner)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (h4-book-order-order-view p (list selector raw) facts nil)))
      (if inner
          (proof-with-checked-results
              ((replaced (proof-proof-rewrite proof opened outer '(1 2 1))))
            (proof-proof-chain proof replaced (list inner)))
        (proof-proof-chain proof opened (list outer))))))

(defun h4-book-compression-ordinal-cells (p exponent coefficient tail)
  (let* ((cell (list *proof-cons* exponent coefficient))
         (raw (list *proof-cons* cell tail)))
    (proof-with-checked-results
        ((outer (h4-book-compression-cons-evidence p raw))
         (inner (h4-book-compression-cons-evidence p cell))
         (facts (list (car outer) (car inner)))
         (exponent-equality
          (h4-book-compression-ordinal-cells-projection
           p raw facts *h4-book-order-exponent* (cadr outer) (cadr inner)))
         (coefficient-equality
          (h4-book-compression-ordinal-cells-projection
           p raw facts *h4-book-order-coefficient* (cadr outer) (caddr inner)))
         (rest-equality
          (h4-book-compression-ordinal-cells-projection
           p raw facts *h4-book-order-rest* (caddr outer) nil)))
      (list raw facts (list (cadr outer) exponent-equality coefficient-equality rest-equality)))))

(defun h4-book-compression-typed-ordinal-cells (p exponent coefficient tail facts)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((cells (h4-book-compression-ordinal-cells p exponent coefficient tail))
         (term (list *h4-book-order-make-ord* exponent coefficient tail))
         (opened (proof-proof-unfold proof term))
         (typed (h4-tactics-tactics-establish
                 p (list *proof-ordinalp* (car cells)) (append (cadr cells) facts)
                 (append *h4-book-order-obasics* (list *proof-ordinalp* (proof-cl "EQL")))
                 (caddr cells) nil))
         (ordinal (library-library-transport-argument p typed opened 1))
         (shape (library-library-transport-argument p (caadr cells) opened 1)))
      (list ordinal shape))))

(defun h4-book-compression-zero-plus-ordinal (p typ shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((typing (proof-step-first typ))
         (tail (proof-term-at typing 1))
         (original (proof-proof-unfold proof
                                       (list *h4-book-compression-add* *proof-zero* tail)))
         (original-literal (proof-step-first original))
         (body (proof-term-at original-literal 2))
         (reduced (h4-tactics-tactics-normalize
                   p body (list shape) *h4-book-order-obasics* nil nil))
         (equation (proof-proof-chain proof original (list reduced)))
         (shape-literal (proof-step-first shape)))
      (if (proof-is-call shape-literal *proof-consp*)
          equation
        (proof-with-checked-results
            ((opened (h4-book-order-order-view p typing (list shape) nil))
             (natural (proof-proof-rewrite proof typ opened '(1)))
             (integral (library-library-cite p "NATURAL-INTEGER" (list tail) (list natural)))
             (zero (library-library-axiom p "UNICITY-OF-0" (list tail)))
             (numeric (h4-association-number p tail (list integral)))
             (fixed (h4-tactics-tactics-normalize
                     p (list *h4-book-compression-fix* tail) (list numeric)
                     (list *h4-book-compression-fix*) nil nil)))
          (proof-proof-chain proof equation (list zero fixed)))))))

(defun h4-book-compression-coefficient-successor (p positive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first positive))
         (coefficient (proof-term-at literal 1))
         (opened (proof-proof-unfold proof literal))
         (expanded (proof-proof-rewrite proof positive opened '(1)))
         (parts (h4-tactics-tactics-conjunct p expanded))
         (one-positive (h4-tactics-tactics-establish
                        p (list *proof-less* *proof-zero* *proof-one*) nil nil nil nil))
         (larger (library-library-cite p "POSITIVE-SUM" (list *proof-one* coefficient)
                                       (list one-positive (cadr parts))))
         (sum (library-plus *proof-one* coefficient))
         (new-type (library-library-type-of p sum (list (car parts)))))
      (h4-tactics-tactics-establish p (list *h4-book-order-posp* sum)
                                   (list larger new-type) (list *h4-book-order-posp*) nil nil))))

(defun h4-book-compression-singleton-sum-exponent (single)
  (nth 1 single))

(defun h4-book-compression-singleton-sum-tail-type (single)
  (nth 2 single))

(defun h4-book-compression-singleton-sum-result (single)
  (nth 3 single))

(defun h4-book-compression-singleton-sum-tail-exponent (single)
  (nth 4 single))

(defun h4-book-compression-singleton-sum-raw (single)
  (nth 5 single))

(defun h4-book-compression-singleton-sum-shapes (single)
  (nth 6 single))

(defun h4-book-compression-singleton-sum-projections (single)
  (nth 7 single))

(defun h4-book-compression-singleton-sum-start (single)
  (nth 8 single))

(defun h4-book-compression-singleton-sum-init (p exponent tail-type)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((typing (proof-step-first tail-type))
         (tail (proof-term-at typing 1))
         (omega-term (list *h4-book-order-omega-term* exponent *proof-one*))
         (result (list *h4-book-compression-add* omega-term tail))
         (tail-exponent (list *h4-book-order-exponent* tail))
         (cells (h4-book-compression-ordinal-cells p exponent *proof-one* *proof-zero*))
         (opened-atom (proof-proof-unfold proof omega-term))
         (opened-ordinal (proof-proof-unfold
                          proof (list *h4-book-order-make-ord* exponent *proof-one* *proof-zero*)))
         (atom-eq (proof-proof-chain proof opened-atom (list opened-ordinal)))
         (raw-sum (proof-proof-unfold proof (list *h4-book-compression-add* (car cells) tail)))
         (identity (proof-proof-reflexive proof result))
         (replace-atom (proof-proof-rewrite proof identity atom-eq '(1 2 1)))
         (start (proof-proof-chain proof replace-atom (list raw-sum))))
      (list :h4-book-compression-singleton-sum exponent tail-type result tail-exponent
            (car cells) (cadr cells) (caddr cells) start))))

(defun h4-book-compression-singleton-sum-reduce (single p shape facts)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((zero-plus (h4-book-compression-zero-plus-ordinal
                     p (h4-book-compression-singleton-sum-tail-type single) shape))
         (rewrites (append (h4-book-compression-singleton-sum-projections single)
                           (list zero-plus)))
         (shape-literal (proof-step-first shape))
         (rewrites (if (proof-is-call shape-literal *proof-consp*)
                       rewrites
                     (proof-with-checked-results
                         ((tail-exponent (h4-book-order-order-view
                                          p (h4-book-compression-singleton-sum-tail-exponent single)
                                          (list shape) nil)))
                       (append rewrites (list tail-exponent)))))
         (start (h4-book-compression-singleton-sum-start single))
         (literal (proof-step-first start))
         (body (proof-term-at literal 2))
         (reduced (h4-tactics-tactics-normalize
                   p body (append (h4-book-compression-singleton-sum-shapes single)
                                  (cons shape facts))
                   (append *h4-book-order-obasics* (list *h4-book-order-ocmp* (proof-cl "EQ")))
                   rewrites nil)))
      (proof-proof-chain proof start (list reduced)))))

(defun h4-book-compression-singleton-sum-finite-bounds (single p exponent-type nonzero shape)
  (let ((proof (library-library-proof p))
        (exponent (h4-book-compression-singleton-sum-exponent single))
        (signs (list exponent-type nonzero)))
    (proof-with-checked-results
        ((positive (h4-book-order-order-formula
                    p (list *proof-ordinal-less* *proof-zero* exponent) signs))
         (no-less (h4-book-order-order-formula
                   p (proof-neg (list *proof-ordinal-less* exponent *proof-zero*)) signs))
         (tail-power (h4-book-order-order-view
                      p (h4-book-compression-singleton-sum-tail-exponent single) (list shape) nil))
         (reverse-power (proof-proof-symmetric proof tail-power))
         (strict (if positive
                     (proof-proof-rewrite proof positive reverse-power '(1 1))
                   '(:failure "failure" ""))))
      (list (list positive no-less) strict))))

(defun h4-book-compression-transport-conjuncts (p expected value)
  (if (endp expected)
      nil
    (proof-with-checked-results
        ((first (library-library-transport-argument p (car expected) value 1))
         (rest (h4-book-compression-transport-conjuncts p (cdr expected) value)))
      (cons first rest))))

(defun h4-book-compression-singleton-ordinal-sum-branch-conclude
    (facts expected p shape single formula)
  (proof-with-checked-results
      ((value (h4-book-compression-singleton-sum-reduce single p shape facts))
       (literal (proof-step-first value))
       (right (proof-term-at literal 2))
       (expected-type (proof-term-at expected 0))
       (expected-literal (proof-step-first expected-type))
       (subject (proof-term-at expected-literal 1)))
    (if (equal right subject)
        (proof-with-checked-results
            ((transported (h4-book-compression-transport-conjuncts p expected value))
             (both (h4-book-division-conjunction p transported)))
          (h4-tactics-tactics-imply p formula both))
      '(:failure "failure" ""))))

(defun h4-book-compression-singleton-ordinal-sum-branch-larger
    (facts bound p shape single formula exponent-type oriented one-positive tail-type)
  (proof-with-checked-results
      ((expected (h4-book-compression-typed-ordinal-cells
                  p *library-x* *proof-one* *library-y*
                  (list exponent-type oriented one-positive tail-type bound))))
    (h4-book-compression-singleton-ordinal-sum-branch-conclude
     facts expected p shape single formula)))

(defun h4-book-compression-ordinal-component (pieces literal)
  (let ((entry (assoc-equal literal pieces)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-compression-singleton-ordinal-sum-branch-not-smaller-same-power
    (not-backward not-forward p shape single formula pieces tail-ex tail-coeff tail-rest)
  (proof-with-checked-results
      ((positive (h4-book-compression-ordinal-component pieces (list *h4-book-order-posp* tail-coeff)))
       (coefficient (h4-book-compression-coefficient-successor p positive))
       (successor (library-plus *proof-one* tail-coeff))
       (power-type (h4-book-compression-ordinal-component pieces (list *proof-ordinalp* tail-ex)))
       (power-nonzero (h4-book-compression-ordinal-component
                       pieces (proof-neg (list (proof-cl "EQL") *proof-zero* tail-ex))))
       (rest-type (h4-book-compression-ordinal-component pieces (list *proof-ordinalp* tail-rest)))
       (rest-bound (h4-book-compression-ordinal-component
                    pieces (list *proof-ordinal-less* (list *h4-book-order-exponent* tail-rest) tail-ex)))
       (expected (h4-book-compression-typed-ordinal-cells
                  p tail-ex successor tail-rest
                  (list power-type power-nonzero coefficient rest-type rest-bound))))
    (h4-book-compression-singleton-ordinal-sum-branch-conclude
     (list not-forward not-backward) expected p shape single formula)))

(defun h4-book-compression-singleton-ordinal-sum-branch-not-smaller
    (not-forward p shape single formula exponent-type oriented one-positive tail-type
                 pieces backward tail-ex tail-coeff tail-rest)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((bound (proof-proof-assume proof backward t))
         (yes (h4-book-compression-singleton-ordinal-sum-branch-larger
               (list not-forward bound) bound p shape single formula
               exponent-type oriented one-positive tail-type))
         (not-backward (proof-proof-assume proof backward nil))
         (no (h4-book-compression-singleton-ordinal-sum-branch-not-smaller-same-power
              not-backward not-forward p shape single formula pieces tail-ex tail-coeff tail-rest)))
      (h4-tactics-tactics-case-of p formula backward yes no))))

(defun h4-book-compression-singleton-ordinal-sum-branch
    (shape p single formula exponent-type nonzero oriented one-positive tail-type
           tail-ex tail-coeff tail-rest forward backward)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((literal (proof-step-first shape)))
      (if (proof-is-call literal *proof-consp*)
          (proof-with-checked-results
              ((pieces (h4-book-order-ordinal-components p tail-type shape))
               (strict (proof-proof-assume proof forward t))
               (yes (h4-book-compression-singleton-ordinal-sum-branch-conclude
                     (list strict) (list tail-type shape) p shape single formula))
               (not-forward (proof-proof-assume proof forward nil))
               (no (h4-book-compression-singleton-ordinal-sum-branch-not-smaller
                    not-forward p shape single formula exponent-type oriented one-positive tail-type
                    pieces backward tail-ex tail-coeff tail-rest)))
            (h4-tactics-tactics-case-of p formula forward yes no))
        (proof-with-checked-results
            ((bounds (h4-book-compression-singleton-sum-finite-bounds
                      single p exponent-type nonzero shape)))
          (h4-book-compression-singleton-ordinal-sum-branch-larger
           (car bounds) (cadr bounds) p shape single formula
           exponent-type oriented one-positive tail-type))))))

(defun h4-book-compression-singleton-ordinal-sum (p)
  (let* ((proof (library-library-proof p))
         (ex-type (list *proof-ordinalp* *library-x*))
         (tail-type (list *proof-ordinalp* *library-y*))
         (nonzero (proof-neg (proof-eq *library-x* *proof-zero*)))
         (condition (proof-ite ex-type (proof-ite nonzero tail-type *proof-false*) *proof-false*))
         (omega-term (list *h4-book-order-omega-term* *library-x* *proof-one*))
         (result (list *h4-book-compression-add* omega-term *library-y*))
         (goal (proof-ite (list *proof-ordinalp* result) (list *proof-consp* result) *proof-false*))
         (formula (list *library-implies* condition goal)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof condition t))
         (conjuncts (h4-book-list-types-conjunct-proofs p assumed))
         (parts (proof-list-of-length conjuncts 3))
         (ex-type (car parts))
         (nonzero (cadr parts))
         (tail-type (caddr parts))
         (oriented (h4-book-order-reflected-test p nonzero))
         (one-positive (h4-tactics-tactics-establish
                        p (list *h4-book-order-posp* *proof-one*) nil
                        (list *h4-book-order-posp*) nil nil))
         (single (h4-book-compression-singleton-sum-init p *library-x* tail-type))
         (tail-ex (list *h4-book-order-exponent* *library-y*))
         (tail-coeff (list *h4-book-order-coefficient* *library-y*))
         (tail-rest (list *h4-book-order-rest* *library-y*))
         (forward (list *proof-ordinal-less* *library-x* tail-ex))
         (backward (list *proof-ordinal-less* tail-ex *library-x*))
         (test (list *proof-consp* *library-y*))
         (shape (proof-proof-assume proof test t))
         (yes (h4-book-compression-singleton-ordinal-sum-branch
               shape p single formula ex-type nonzero oriented one-positive tail-type
               tail-ex tail-coeff tail-rest forward backward))
         (atom-shape (proof-proof-assume proof test nil))
         (no (h4-book-compression-singleton-ordinal-sum-branch
              atom-shape p single formula ex-type nonzero oriented one-positive tail-type
              tail-ex tail-coeff tail-rest forward backward)))
      (h4-tactics-tactics-case-of p formula test yes no))))

(defun h4-book-compression-compression-shape (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results ((premise (proof-term-at formula 1)))
        (if (proof-is-call premise *h4-book-compression-e0-ordinal*)
            (proof-with-checked-results ((subject (proof-term-at premise 1)))
              (if (proof-compound subject)
                  nil
                (proof-with-checked-results ((goal (proof-term-at formula 2)))
                  (and (equal goal (list *proof-ordinalp* (list *h4-book-compression-atoc* subject)))
                       subject))))
          nil))
    nil))

(defun h4-book-compression-compress-ordinal-atom (shape p value source subject strengthened)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((result (h4-book-order-order-view p value (list shape) nil))
         (source-literal (proof-step-first source))
         (opened (h4-book-order-order-view p source-literal (list shape) nil))
         (natural (proof-proof-rewrite proof source opened '(1)))
         (unfolded (proof-proof-unfold proof (list *library-natp* subject)))
         (natural (proof-proof-transport proof natural unfolded))
         (typed (library-library-cite p "NATURAL-ORDINAL" (list subject) (list natural)))
         (test (proof-eq subject *proof-zero*))
         (nonzero (proof-proof-assume proof test nil))
         (reverse-result (proof-proof-symmetric proof result))
         (nonzero (proof-proof-rewrite proof nonzero reverse-result '(1 1 1)))
         (still-nonzero (h4-tactics-tactics-guarded p test nonzero nil))
         (preserved-type (library-library-transport-argument p typed result 1))
         (preserved (h4-book-division-conjunction p (list preserved-type still-nonzero))))
      (h4-tactics-tactics-imply p strengthened preserved))))

(defun h4-book-compression-compress-ordinal-hypothesis
    (p shape subject strengthened index substitution given)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((builtin (library-library-builtin p index subject))
         (decrease (proof-proof-discharge proof builtin shape))
         (instance (proof-subst strengthened
                               (list (cons (caar substitution) (cadar substitution)))))
         (test (proof-step-first decrease))
         (assumed (proof-proof-assume proof (proof-ite test instance *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed decrease))
         (conclusion (h4-tactics-tactics-modus-ponens p induction given)))
      (h4-tactics-tactics-conjunct p conclusion))))

(defun h4-book-compression-compress-ordinal-pair
    (shape p source subject strengthened bindings singleton value)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((source-literal (proof-step-first source))
         (opened (h4-book-order-order-view p source-literal (list shape) nil))
         (reduced (proof-proof-rewrite proof source opened '(1)))
         (parts (h4-book-list-types-conjunct-proofs p reduced))
         (initial (proof-list-of-length (seq-slice parts 0 3) 3))
         (head-hypotheses (h4-book-compression-compress-ordinal-hypothesis
                          p shape subject strengthened 2 (car bindings) (car initial)))
         (rest-hypotheses (h4-book-compression-compress-ordinal-hypothesis
                          p shape subject strengthened 3 (cadr bindings) (caddr initial)))
         (exponent (car head-hypotheses))
         (preserved (cadr head-hypotheses))
         (nonzero (proof-proof-prove-if proof preserved (cadr initial)))
         (suffix (car rest-hypotheses))
         (given (h4-book-division-conjunction p (list exponent nonzero suffix)))
         (exp-type (proof-step-first exponent))
         (power (proof-term-at exp-type 1))
         (suffix-type (proof-step-first suffix))
         (tail (proof-term-at suffix-type 1))
         (addition (proof-proof-instantiate
                    proof singleton (list (list *library-x* power) (list *library-y* tail))))
         (summed (h4-tactics-tactics-modus-ponens p addition given))
         (sum-parts (h4-tactics-tactics-conjunct p summed))
         (result (h4-book-order-order-view p value (list shape) nil))
         (typed (library-library-transport-argument p (car sum-parts) result 1))
         (nonzero-sum (h4-book-compression-nonzero-cons p (cadr sum-parts)))
         (reverse-result (proof-proof-symmetric proof result))
         (nonzero (proof-proof-rewrite proof nonzero-sum reverse-result '(1 1 1)))
         (still-nonzero (h4-tactics-tactics-guarded
                         p (proof-eq subject *proof-zero*) nonzero nil))
         (conjunction (h4-book-division-conjunction p (list typed still-nonzero))))
      (h4-tactics-tactics-imply p strengthened conjunction))))

(defun h4-book-compression-compress-ordinal (p formula subject)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((premise (proof-term-at formula 1))
         (source (proof-proof-assume proof premise t))
         (value (list *h4-book-compression-atoc* subject))
         (survives (proof-ite (proof-eq subject *proof-zero*) *proof-true*
                              (proof-neg (proof-eq value *proof-zero*))))
         (source-literal (proof-step-first source))
         (goal (proof-term-at formula 2))
         (strengthened (list *library-implies* source-literal
                             (proof-ite goal survives *proof-false*)))
         (bindings (list (list (list subject (list *library-car* subject)))
                         (list (list subject (list *library-cdr* subject)))))
         (singleton (h4-book-compression-singleton-ordinal-sum p))
         (test (list *proof-consp* subject))
         (cons-shape (proof-proof-assume proof test t))
         (pair (h4-book-compression-compress-ordinal-pair
                cons-shape p source subject strengthened bindings singleton value))
         (atom-shape (proof-proof-assume proof test nil))
         (atom (h4-book-compression-compress-ordinal-atom
                atom-shape p value source subject strengthened))
         (cases (h4-tactics-tactics-case-of p strengthened test pair atom))
         (ordinal (library-library-builtin p 1 subject))
         (induction (proof-proof-induct proof ordinal cases strengthened
                                        (list *library-count* subject) bindings))
         (conclusion (h4-tactics-tactics-modus-ponens p induction source))
         (parts (h4-tactics-tactics-conjunct p conclusion)))
      (h4-tactics-tactics-imply p formula (car parts)))))

(defun h4-book-compression-compression-proof (p formula support)
  (proof-with-checked-results ((subject (h4-book-compression-compression-shape formula)))
    (if (and subject support)
        (let* ((proof (library-library-proof p))
               (facts (table-update (proof-proof-facts proof) support))
               (extended (library-library-with-proof p (proof-proof-with-facts proof facts))))
          (h4-book-compression-compress-ordinal extended formula subject))
      nil)))
