(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-ordinals-make-ord* (proof-sym "MAKE-ORD" "ACL2"))
(defconst *h2-ordinals-first* (proof-sym "O-FIRST-EXPT" "ACL2"))
(defconst *h2-ordinals-posp* (proof-sym "POSP" "ACL2"))
(defconst *h2-ordinals-list* (proof-sym "NAT-LIST-MEASURE" "ACL2"))

(defun h2-ordinals-has-fact (proof name)
  (assoc-equal name (proof-proof-facts (h2-modular-proof proof))))

(defun h2-ordinals-search (proof method args)
  (h2-recipes-call-search proof method args))

; A local folding scope answers its opening tests before consuming inherited replies.
(defun h2-ordinals-folded-search (n search formula seeds fixed inherited-hooks replies pending)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h2-ordinals-folded-search")
    (let ((result (h2-search-search-call-with-remainder
                   (h2-search-search-with-replies search replies) :solve (list formula seeds nil))))
      (cond
       ((failure-p result) result)
       ((not (h2-search-request-p result)) (cons (car result) pending))
       (t
        (let ((method (h2-search-request-method result)))
          (cond
           ((and (eq method :can-open)
                 (eq (h2-search-request-phase result) :before)
                 (member-equal (car (h2-search-request-args result)) fixed))
            (h2-ordinals-folded-search (1- n) search formula seeds fixed inherited-hooks
                                       (append replies (list '(:return nil))) pending))
           ((not (member-eq method inherited-hooks))
            (h2-ordinals-folded-search (1- n) search formula seeds fixed inherited-hooks
                                       (append replies (list :base)) pending))
           ((consp pending)
            (h2-ordinals-folded-search (1- n) search formula seeds fixed inherited-hooks
                                       (append replies (list (car pending))) (cdr pending)))
           (t result))))))))

(defun h2-ordinals-folded-outcome (proof formula seeds fixed)
  (let ((search (h2-recipes-recipes-search proof)))
    (if (endp fixed)
        (let ((outcome (h2-search-search-call-with-outcome search :solve (list formula seeds nil))))
          (if (h2-search-request-p outcome)
              outcome
            (cons (car outcome) (h2-recipes-recipes-with-search proof (cdr outcome)))))
      (let* ((hooks (h2-search-search-hooks search))
             (scoped (h2-search-search-with-hooks search (add-to-set-eq :can-open hooks)))
             (outcome (h2-ordinals-folded-search 1000000 scoped formula seeds fixed hooks nil
                                                (h2-search-search-replies search))))
        (cond ((h2-search-request-p outcome) outcome)
              ((failure-p outcome) (cons outcome proof))
              (t (cons (car outcome)
                       (h2-recipes-recipes-with-search
                        proof (h2-search-search-with-replies search (cdr outcome))))))))))

(defun h2-ordinals-folded-recipe-body (proof fixed name formula definitions facts seeds split-limit)
  (let* ((lemma (and name (concatenate 'string "H2-" name)))
         (label (and lemma (concatenate 'string "SELF-" lemma))))
    (if (and label (h2-ordinals-has-fact proof (proof-sym label "ACL2")))
        (cons label proof)
      (let ((configured (h2-recipes-recipes-set-rules proof definitions facts "" split-limit)))
        (if (failure-p configured)
            (cons configured proof)
          (let ((outcome (h2-ordinals-folded-outcome configured formula seeds fixed)))
            (if (or (h2-search-request-p outcome) (not label) (failure-p (car outcome)))
                outcome
              (let* ((proof (cdr outcome))
                     (updated (h2-recipes-lemma proof lemma formula (car outcome) nil)))
                (if (failure-p updated)
                    (cons updated proof)
                  (cons label updated))))))))))

; Restore the fixed calls before returning the scoped result.
(defun h2-ordinals-folded-recipe (proof fixed name formula definitions facts seeds split-limit)
  (if (member-eq :keep-folded (h2-search-search-hooks (h2-recipes-recipes-search proof)))
      (h2-recipes-with-results
       ((saved (h2-ordinals-search proof :keep-folded (list fixed)))
        (outcome (h2-ordinals-folded-recipe-body (cdr saved) nil name formula
                                                definitions facts seeds split-limit))
        (restored (h2-ordinals-search (cdr outcome) :restore-fixed-calls (list (car saved))))
        (value (car outcome)))
       (cons value (cdr restored)))
    (h2-recipes-with-results
     ((outcome (h2-ordinals-folded-recipe-body proof fixed name formula definitions facts seeds split-limit))
      (value (car outcome)))
     (cons value (cdr outcome)))))

(defun h2-ordinals-derive (proof formula definitions facts seeds split-limit)
  (h2-recipes-recipes-derive proof formula definitions facts nil 1 "" seeds nil split-limit))

(defun h2-ordinals-select-body (proof opening evidence)
  (h2-book-logic-select-body (h2-recipes-recipes-search proof) opening evidence))

(defun h2-ordinals-natural-fix (proof value)
  (h2-recipes-with-results
   ((named (h2-modular-fixed-natural proof))
    (name (car named))
    (proof (cdr named))
    (step (library-library-axiom (h2-modular-library proof) name (list value))))
   (cons step proof)))

(defun h2-ordinals-noncons-fix (proof value)
  (let ((fixed (list *h2-modular-natural-fix* value)))
    (h2-recipes-with-results
     ((natural (h2-ordinals-natural-fix proof value))
      (proof (cdr natural))
      (library (h2-modular-library proof))
      (logic (library-library-proof library))
      (typed (library-library-cite library "NATURAL-INTEGER" (list fixed)
                                   (list (car natural))))
      (numeric (library-library-number library fixed (list typed)))
      (cons-step (proof-proof-assume logic (list *proof-consp* fixed) t))
      (fact (proof-proof-fact logic "consp-not-acl2-numberp"
                              (list (list *library-x* fixed))))
      (not-numeric (proof-proof-modus-ponens logic fact cons-step))
      (conflict (proof-proof-cut logic numeric not-numeric))
      (shape (proof-step-first cons-step))
      (step (proof-proof-front logic conflict (proof-neg shape))))
     (cons step proof))))

(defun h2-ordinals-integer-fix (proof value)
  (h2-recipes-with-results
   ((natural (h2-ordinals-natural-fix proof value))
    (proof (cdr natural))
    (step (library-library-cite (h2-modular-library proof) "NATURAL-INTEGER"
                                 (list (list *h2-modular-natural-fix* value))
                                 (list (car natural)))))
   (cons step proof)))

(defun h2-ordinals-successor-facts (proof natural)
  (let ((library (h2-modular-library proof)))
    (h2-recipes-with-results
     ((value (h2-modular-first-at natural '(1)))
      (number (library-library-cite library "NATURAL-INTEGER" (list value)
                                    (list natural)))
      (bound (library-library-cite library "NATURAL-NONNEGATIVE" (list value)
                                   (list natural)))
      (positive (library-library-cite library "POSITIVE-ONE-PLUS" (list value)
                                      (list number bound)))
      (typed (library-library-type-of library (library-plus *proof-one* value)
                                      (list number))))
     (list typed positive))))

(defun h2-ordinals-ordinal-constructor (proof)
  (let ((name "SELF-H2-ORDINAL-CONSTRUCTOR"))
    (if (h2-ordinals-has-fact proof (proof-sym name "ACL2"))
        (cons name proof)
      (let* ((value (list *h2-ordinals-make-ord* *library-x* *library-y* *library-z*))
             (formula (proof-eq (list *proof-ordinalp* value)
                                (list *proof-ordinal-less*
                                      (list *h2-ordinals-first* *library-z*)
                                      *library-x*)))
             (logic (h2-modular-proof proof)))
        (h2-recipes-with-results
         ((exponent (proof-proof-assume logic (list *proof-ordinalp* *library-x*) t))
          (nonzero (proof-proof-assume
                    logic (proof-neg (list (proof-cl "EQL") *proof-zero* *library-x*)) t))
          (coefficient (proof-proof-assume logic (list *h2-ordinals-posp* *library-y*) t))
          (rest (proof-proof-assume logic (list *proof-ordinalp* *library-z*) t))
          (derived (h2-ordinals-derive proof formula
                                        "MAKE-ORD O-P O-FINP O-FIRST-EXPT O-FIRST-COEFF O-RST"
                                        nil (list exponent nonzero coefficient rest) 80))
          (step (car derived))
          (proof (h2-recipes-lemma (cdr derived) "H2-ORDINAL-CONSTRUCTOR"
                                       formula step (cdr (proof-step-clause step)))))
         (cons name proof))))))

(defun h2-ordinals-constructor-ordinal
    (proof value exponent-int exponent-positive coefficient rest comparison)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((exponent (proof-term-at value 1))
      (exp-nonnegative (library-library-cite library "POSITIVE-NONNEGATIVE" (list exponent)
                                             (list exponent-int exponent-positive)))
      (exp-natural (library-library-cite library "NATURAL-FROM-BOUNDS" (list exponent)
                                        (list exponent-int exp-nonnegative)))
      (exp-ordinal (library-library-cite library "NATURAL-ORDINAL" (list exponent)
                                        (list exp-natural)))
      (zero-int (library-library-type-of library *proof-zero* nil))
      (nonzero (library-library-cite library "H2-LESS-IMPLIES-UNEQUAL"
                                     (list *proof-zero* exponent) (list zero-int exponent-positive)))
      (eql-open (proof-proof-unfold logic (list (proof-cl "EQL") *proof-zero* exponent)))
      (eql-close (proof-proof-symmetric logic eql-open))
      (nonzero (proof-proof-rewrite logic nonzero eql-close '(1 1)))
      (value-coefficient (proof-term-at value 2))
      (positive-coefficient (proof-proof-prove logic (list *h2-ordinals-posp* value-coefficient)
                                               coefficient (list *h2-ordinals-posp*)))
      (named (h2-ordinals-ordinal-constructor proof))
      (name (car named))
      (proof (cdr named))
      (logic (h2-modular-proof proof))
      (equation (proof-proof-use logic (proof-sym name "ACL2")
                                 (seq-zip (list *library-x* *library-y* *library-z*) (cdr value))
                                 (list exp-ordinal nonzero positive-coefficient rest)))
      (step (proof-proof-chain logic equation (list comparison))))
     (cons step proof))))

(defun h2-ordinals-pair-ordinal (proof formula)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((pair (h2-modular-term-at formula '(1 1)))
      (arguments (h2-modular-tail-of-size pair 2))
      (outer (proof-proof-unfold logic pair))
      (first (h2-modular-first-at outer '(2)))
      (rest (proof-term-at first 3))
      (zero-natural (library-library-natural library *proof-zero*))
      (zero (library-library-cite library "NATURAL-ORDINAL" (list *proof-zero*)
                                  (list zero-natural)))
      (small (h2-ordinals-derive
              proof
              (proof-eq (list *proof-ordinal-less*
                              (list *h2-ordinals-first* *proof-zero*) *proof-one*)
                        *proof-true*)
              "O< O-FINP O-FIRST-EXPT" nil nil 80))
      (proof (cdr small))
      (library (h2-modular-library proof))
      (logic (library-library-proof library))
      (one-int (library-library-type-of library *proof-one* nil))
      (one-positive (proof-proof-prove logic (library-lt *proof-zero* *proof-one*) nil nil))
      (b-natural (h2-ordinals-natural-fix proof (cadr arguments)))
      (proof (cdr b-natural))
      (b-successor (h2-ordinals-successor-facts proof (car b-natural)))
      (rest-eq (h2-ordinals-constructor-ordinal proof rest one-int one-positive
                                               b-successor zero (car small)))
      (proof (cdr rest-eq))
      (two (proof-quote 2))
      (large (h2-ordinals-derive
              proof
              (proof-eq (list *proof-ordinal-less* (list *h2-ordinals-first* rest) two)
                        *proof-true*)
              "O< O-FINP O-FIRST-EXPT MAKE-ORD" nil nil 80))
      (proof (cdr large))
      (library (h2-modular-library proof))
      (logic (library-library-proof library))
      (two-int (library-library-type-of library two nil))
      (two-positive (proof-proof-prove logic (library-lt *proof-zero* two) nil nil))
      (a-natural (h2-ordinals-natural-fix proof (car arguments)))
      (proof (cdr a-natural))
      (a-successor (h2-ordinals-successor-facts proof (car a-natural)))
      (rest-ordinal (proof-proof-true-from-eq (h2-modular-proof proof) (car rest-eq)))
      (side (h2-ordinals-constructor-ordinal proof first two-int two-positive
                                            a-successor rest-ordinal (car large)))
      (proof (cdr side))
      (logic (h2-modular-proof proof))
      (close (proof-proof-symmetric logic outer))
      (step (proof-proof-rewrite logic (car side) close '(1 1 1))))
     (cons step proof))))

(defun h2-ordinals-positive-length (proof cons-step)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((data (h2-modular-first-at cons-step '(1)))
      (length (list *library-len* data))
      (tail (list *library-len* (list *library-cdr* data)))
      (opened (proof-proof-unfold logic length))
      (length-eq (h2-ordinals-select-body proof opened cons-step))
      (natural (library-library-natural library tail))
      (facts (h2-ordinals-successor-facts proof natural))
      (typed (library-library-transport-argument library (car facts) length-eq 1))
      (positive (library-library-transport-argument library (cadr facts) length-eq 2)))
     (list typed positive))))

(defun h2-ordinals-boolean-value (proof term evidence)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((typed (proof-proof-fact logic "booleanp-<"
                               (seq-zip (list *library-x* *library-y*) (cdr term)))))
     (library-library-cite library "H2-TRUE-BOOLEAN" (list term) (list evidence typed)))))

(defun h2-ordinals-list-ordinal-comparison
    (proof rest length exponent-int exponent strict branch)
  (h2-recipes-with-results
   ((derived (h2-ordinals-derive
              proof (proof-eq (list *h2-ordinals-first* rest) exponent)
              "O-FIRST-EXPT O-FINP" '("CONSP-NAT-LIST-MEASURE" "ATOM-CAAR-NAT-LIST-MEASURE")
              (list branch) 80))
    (proof (cdr derived))
    (library (h2-modular-library proof))
    (logic (library-library-proof library))
    (typed (library-library-type-of library exponent nil))
    (comparison (library-library-cite library "FINITE-ORDER" (list exponent length)
                                        (list typed exponent-int)))
    (literal (proof-step-first strict))
    (truth (h2-ordinals-boolean-value proof literal strict))
    (comparison (proof-proof-chain logic comparison (list truth)))
    (first (proof-proof-symmetric logic (car derived)))
    (step (proof-proof-rewrite logic comparison first '(1 1 1))))
   (cons step proof)))

(defun h2-ordinals-list-ordinal (proof formula)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((measure (proof-term-at formula 1))
      (data (proof-term-at measure 1))
      (tail (list *library-cdr* data))
      (rest (list *h2-ordinals-list* tail))
      (cons-step (proof-proof-assume logic (list *proof-consp* data) t))
      (length (list *library-len* data))
      (child-length (list *library-len* tail))
      (length-facts (h2-ordinals-positive-length proof cons-step))
      (exponent-int (car length-facts))
      (exponent-positive (cadr length-facts))
      (opened (proof-proof-unfold logic measure))
      (test (h2-modular-first-at opened '(2 1)))
      (no (h2-ordinals-derive proof (proof-neg test) "" nil (list cons-step) 80))
      (proof (cdr no))
      (hit (h2-ordinals-select-body proof opened (car no)))
      (logic (h2-modular-proof proof))
      (shape (proof-step-first cons-step))
      (atom-step (proof-proof-assume logic shape nil))
      (yes (h2-ordinals-derive proof test "" nil (list atom-step) 80))
      (proof (cdr yes))
      (base (h2-ordinals-select-body proof opened (car yes)))
      (fixed-natural (h2-ordinals-natural-fix proof data))
      (proof (cdr fixed-natural))
      (library (h2-modular-library proof))
      (logic (library-library-proof library))
      (fixed (library-library-cite library "NATURAL-ORDINAL"
                                    (list (list *h2-modular-natural-fix* data))
                                    (list (car fixed-natural))))
      (empty (library-library-transport-argument library fixed base 1))
      (decrease (library-library-builtin library 3 data))
      (smaller (proof-proof-discharge logic decrease cons-step))
      (less (proof-step-first smaller))
      (assumption (proof-ite less (list *proof-ordinalp* rest) *proof-true*))
      (assumed (proof-proof-assume logic assumption t))
      (tail-ordinal (proof-proof-prove-if logic assumed smaller))
      (tail-test (list *proof-consp* tail))
      (strict (library-library-cite library "LEN-CDR-LESS" (list data) (list cons-step)))
      (tail-cons (proof-proof-assume logic tail-test t))
      (tail-atom (proof-proof-assume logic tail-test nil))
      (first (h2-ordinals-list-ordinal-comparison
              proof rest length exponent-int child-length strict tail-cons))
      (second (h2-ordinals-list-ordinal-comparison
               (cdr first) rest length exponent-int *proof-zero* exponent-positive tail-atom))
      (proof (cdr second))
      (logic (h2-modular-proof proof))
      (ordered (proof-proof-cases logic tail-test (car first) (car second)))
      (coefficient (h2-ordinals-natural-fix proof (list *library-car* data)))
      (proof (cdr coefficient))
      (coefficients (h2-ordinals-successor-facts proof (car coefficient)))
      (constructor (h2-modular-first-at hit '(2)))
      (valid (h2-ordinals-constructor-ordinal proof constructor exponent-int exponent-positive
                                             coefficients tail-ordinal ordered))
      (proof (cdr valid))
      (library (h2-modular-library proof))
      (logic (library-library-proof library))
      (valid-step (proof-proof-true-from-eq logic (car valid)))
      (nonempty (library-library-transport-argument library valid-step hit 1))
      (ordinal (library-library-builtin library 1 data))
      (cases (proof-proof-cases logic shape nonempty empty))
      (step (proof-proof-induct logic ordinal cases formula (list *library-count* data)
                                (list (list (list data tail))))))
     (cons step proof))))

(defun h2-ordinals-rewrite-successor (proof forward binding position)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((eqn (library-library-cite library "H2-ADD1-SUB1" (list (car binding))
                                  (list (cadr binding)))))
     (proof-proof-rewrite logic forward eqn (list 1 position)))))

(defun h2-ordinals-successor-equality-rewrites (proof forward bindings position)
  (declare (xargs :measure (acl2-count bindings)))
  (if (or (endp bindings) (failure-p forward))
      forward
    (h2-ordinals-successor-equality-rewrites
     proof (h2-ordinals-rewrite-successor proof forward (car bindings) position)
     (cdr bindings) (1+ position))))

(defun h2-ordinals-comparison-rules (proof)
  (let ((names '("SELF-H2-ORDINAL-COMPARE" "SELF-H2-SUCCESSOR-LESS"
                 "SELF-H2-SUCCESSOR-EQUAL" "SELF-H2-INTEGER-LESS-SELF-NIL"
                 "SELF-WEAK-REFLEXIVE" "SELF-H2-LESS-IMPLIES-UNEQUAL")))
    (if (h2-ordinals-has-fact proof (proof-sym (car names) "ACL2"))
        (cons names proof)
      (let* ((x *library-x*)
             (y *library-y*)
             (z *library-z*)
             (exponent (proof-sym "U" "ACL2"))
             (coeff (proof-sym "V" "ACL2"))
             (rest (proof-sym "W" "ACL2"))
             (left (list *h2-ordinals-make-ord* x y z))
             (right (list *h2-ordinals-make-ord* exponent coeff rest))
             (order (proof-ite (proof-eq x exponent)
                               (proof-ite (proof-eq y coeff) (list *proof-ordinal-less* z rest)
                                          (library-lt y coeff))
                               (library-lt x exponent)))
             (claim (proof-eq (list *proof-ordinal-less* left right) order)))
        (h2-recipes-with-results
         ((comparison-ints (library-library-ints (h2-modular-library proof) (list x exponent)))
          (comparison (h2-ordinals-derive
                       proof claim "MAKE-ORD O< O-FINP O-FIRST-EXPT O-FIRST-COEFF O-RST"
                       '("SELF-FINITE-ORDER") comparison-ints 80))
          (proof (h2-recipes-lemma (cdr comparison) "H2-ORDINAL-COMPARE" claim
                                       (car comparison)
                                       (library-guards (list (library-integer x)
                                                             (library-integer exponent)))))
          (library (h2-modular-library proof))
          (logic (library-library-proof library))
          (inputs (library-library-ints library (list x y)))
          (guard-x (proof-step-first (car inputs)))
          (guard-y (proof-step-first (cadr inputs)))
          (guards (library-guards (list guard-x guard-y)))
          (a (library-plus *proof-one* x))
          (b (library-plus *proof-one* y))
          (shifted (library-library-comparison library a b inputs))
          (direct (library-library-comparison library x y inputs))
          (shifted-difference (h2-modular-first-at shifted '(2 2)))
          (direct-difference (h2-modular-first-at direct '(2 2)))
          (delta (library-library-linear-equal library shifted-difference direct-difference inputs))
          (shifted (proof-proof-rewrite logic shifted delta '(1 2 2)))
          (reversed (proof-proof-symmetric logic direct))
          (less (proof-proof-chain logic shifted (list reversed)))
          (less-claim (proof-step-first less))
          (proof (h2-recipes-lemma proof "H2-SUCCESSOR-LESS" less-claim less guards))
          (logic (h2-modular-proof proof))
          (same (proof-eq x y))
          (shifted-same (proof-eq a b))
          (a-same (proof-proof-reflexive logic a))
          (same-step (proof-proof-assume logic same t))
          (backward (proof-proof-rewrite logic a-same same-step '(1 2 2)))
          (sub-one (proof-proof-reflexive logic (library-plus *proof-neg-one* a)))
          (shifted-step (proof-proof-assume logic shifted-same t))
          (forward (proof-proof-rewrite logic sub-one shifted-step '(1 2 2)))
          (forward (h2-ordinals-successor-equality-rewrites
                    proof forward (seq-zip (list x y) inputs) 1))
          (equality (h2-ordering-equal-tests (h2-recipes-recipes-search proof)
                                             shifted-same same forward backward))
          (equality-claim (proof-step-first equality))
          (proof (h2-recipes-lemma proof "H2-SUCCESSOR-EQUAL" equality-claim equality guards))
          (irreflexive (library-library-cite (h2-modular-library proof) "WEAK-REFLEXIVE"
                                            (list x) (list (car inputs))))
          (self-nil (h2-search-search-nil-value (h2-recipes-recipes-search proof) irreflexive))
          (self-nil-claim (proof-step-first self-nil))
          (proof (h2-recipes-lemma proof "H2-INTEGER-LESS-SELF-NIL" self-nil-claim
                                       self-nil (list (car guards)))))
         (cons names proof))))))

(defun h2-ordinals-pair-order-arguments (pairs)
  (if (endp pairs)
      nil
    (h2-recipes-with-results
     ((pair (car pairs))
      (arguments (if (integerp pair) (proof-term-at pair 1) (seq-slice pair 1 :none)))
      (remaining (h2-ordinals-pair-order-arguments (cdr pairs))))
     (append arguments remaining))))

(defun h2-ordinals-fix-arguments (inputs integer-facts-p previous reversed)
  (declare (xargs :measure (acl2-count inputs)))
  (cond
   ((h2-search-stopped-p previous) previous)
   ((endp inputs) (cons (reverse reversed) (cdr previous)))
   (t
    (let* ((proof (cdr previous))
           (value (car inputs))
           (fact (if integer-facts-p
                     (h2-ordinals-integer-fix proof value)
                   (h2-ordinals-noncons-fix proof value))))
      (h2-ordinals-fix-arguments (cdr inputs) integer-facts-p fact (cons (car fact) reversed))))))

(defun h2-ordinals-pair-order (proof formula)
  (h2-recipes-with-results
   ((rules (h2-ordinals-comparison-rules proof))
    (proof (cdr rules))
    (goal (proof-term-at formula 1))
    (pairs (if (integerp goal) (proof-term-at goal 1) (seq-slice goal 1 :none)))
    (inputs (h2-ordinals-pair-order-arguments pairs))
    (typed (h2-ordinals-fix-arguments inputs t (cons nil proof) nil))
    (empty (h2-ordinals-derive
            (cdr typed) (proof-eq (list *proof-ordinal-less* *proof-zero* *proof-zero*) *proof-false*)
            "O< O-FINP" nil nil 80)))
   (h2-ordinals-derive (cdr empty) formula "TWO-NATS-MEASURE" (car rules)
                       (append (car typed) (list (car empty))) 20)))

(defun h2-ordinals-list-order-inputs (terms)
  (if (endp terms)
      nil
    (h2-recipes-with-results
     ((value (proof-term-at (car terms) 1))
      (rest (h2-ordinals-list-order-inputs (cdr terms))))
     (cons value rest))))

(defun h2-ordinals-list-order-tests (inputs)
  (if (endp inputs)
      nil
    (cons (list *proof-consp* (car inputs)) (h2-ordinals-list-order-tests (cdr inputs)))))

(defun h2-ordinals-list-order-fixed (inputs)
  (if (endp inputs)
      nil
    (cons (list *h2-ordinals-list* (list *library-cdr* (car inputs)))
          (h2-ordinals-list-order-fixed (cdr inputs)))))

(defun h2-ordinals-list-order-learn (proof value test has-cons known fixed)
  (let* ((library (h2-modular-library proof))
         (logic (library-library-proof library)))
    (h2-recipes-with-results
     ((shape (proof-proof-assume logic test has-cons))
      (known (append known (list shape))))
     (if has-cons
         (let ((length (list *library-len* value)))
           (h2-recipes-with-results
            ((facts (h2-ordinals-positive-length proof shape))
             (typed (car facts))
             (positive (cadr facts))
             (literal (proof-step-first positive))
             (true-value (h2-ordinals-boolean-value proof literal positive))
             (zero-int (library-library-type-of library *proof-zero* nil))
             (asymmetry (library-library-cite library "H2-INTEGER-ASYMMETRY"
                                               (list *proof-zero* length)
                                               (list zero-int typed positive)))
             (zero-int (library-library-type-of library *proof-zero* nil))
             (distinct (library-library-cite library "H2-LESS-IMPLIES-UNEQUAL"
                                              (list *proof-zero* length) (list zero-int positive)))
             (integer-fix (h2-ordinals-integer-fix proof (list *library-car* value))))
            (cons (list (append known (list typed positive true-value asymmetry distinct (car integer-fix)))
                        (append fixed (list length)))
                  (cdr integer-fix))))
       (h2-recipes-with-results ((fixed-type (h2-ordinals-noncons-fix proof value)))
         (cons (list (append known (list (car fixed-type))) fixed) (cdr fixed-type)))))))

(defun h2-ordinals-list-order-known (inputs tests flags result)
  (declare (xargs :measure (acl2-count inputs)))
  (if (or (h2-search-stopped-p result) (endp inputs) (endp tests) (endp flags))
      result
    (h2-ordinals-list-order-known
     (cdr inputs) (cdr tests) (cdr flags)
     (h2-ordinals-list-order-learn (cdr result) (car inputs) (car tests) (car flags)
                                   (caar result) (cadar result)))))

(defun h2-ordinals-list-order-branch (first-cons second-cons proof not-nil inputs tests rules goal)
  (h2-recipes-with-results
   ((fixed (h2-ordinals-list-order-fixed inputs))
    (known (h2-ordinals-list-order-known inputs tests (list first-cons second-cons)
                                        (cons (list (list not-nil) fixed) proof))))
   (h2-ordinals-folded-recipe
    (cdr known) (cadar known) nil goal
    (if (and first-cons second-cons) "NAT-LIST-MEASURE" "NAT-LIST-MEASURE MAKE-ORD O< O-FINP LEN")
    rules (caar known) 20)))

(defun h2-ordinals-list-order (proof formula)
  (h2-recipes-with-results
     ((rules (h2-ordinals-comparison-rules proof))
      (proof (cdr rules))
      (goal (proof-term-at formula 2))
      (comparison (proof-term-at goal 1))
      (terms (if (integerp comparison) (proof-term-at comparison 1) (seq-slice comparison 1 :none)))
      (inputs (h2-ordinals-list-order-inputs terms))
      (tests (h2-ordinals-list-order-tests inputs))
      (logic (h2-modular-proof proof))
      (opening (proof-proof-unfold logic (proof-neg *proof-false*)))
      (body (h2-modular-first-at opening '(2)))
      (branch (proof-proof-if-false logic body))
      (not-nil (proof-proof-chain logic opening (list branch)))
      (second-test (proof-term-at tests 1))
      (cons-cons (h2-ordinals-list-order-branch t t proof not-nil inputs tests (car rules) goal))
      (cons-atom (h2-ordinals-list-order-branch t nil (cdr cons-cons) not-nil inputs tests (car rules) goal))
      (proof (cdr cons-atom))
      (first (proof-proof-cases (h2-modular-proof proof) second-test (car cons-cons) (car cons-atom)))
      (atom-cons (h2-ordinals-list-order-branch nil t proof not-nil inputs tests (car rules) goal))
      (atom-atom (h2-ordinals-list-order-branch nil nil (cdr atom-cons) not-nil inputs tests (car rules) goal))
      (proof (cdr atom-atom))
      (logic (h2-modular-proof proof))
      (second (proof-proof-cases logic second-test (car atom-cons) (car atom-atom)))
      (first-test (proof-term-at tests 0))
      (cases (proof-proof-cases logic first-test first second))
      (step (h2-modular-introduce proof formula cases)))
   (cons step proof)))

(defun h2-ordinals-measure-argument (n argument)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h2-ordinals-measure-argument")
    (h2-recipes-with-results ((head (proof-term-at argument 0)))
      (if (equal head *h2-ordinals-list*)
          (proof-term-at argument 1)
        (h2-recipes-with-results ((child (proof-term-at argument 1)))
          (h2-ordinals-measure-argument (1- n) child))))))

(defun h2-ordinals-measure-theorem (proof label formula)
  (cond
   ((equal label "O-P-OF-TWO-NATS-MEASURE") (h2-ordinals-pair-ordinal proof formula))
   ((equal label "O-P-OF-NAT-LIST-MEASURE") (h2-ordinals-list-ordinal proof formula))
   ((equal label "O<-OF-TWO-NATS-MEASURE") (h2-ordinals-pair-order proof formula))
   ((equal label "O<-OF-NAT-LIST-MEASURE") (h2-ordinals-list-order proof formula))
   ((member-equal label '("CONSP-NAT-LIST-MEASURE" "ATOM-CAAR-NAT-LIST-MEASURE"))
    (h2-recipes-with-results
     ((argument (proof-term-at formula 1))
      (value (h2-ordinals-measure-argument 1000000 argument))
      (noncons (h2-ordinals-noncons-fix proof value)))
     (h2-ordinals-derive (cdr noncons) formula "NAT-LIST-MEASURE MAKE-ORD" nil (list (car noncons)) 80)))
   ((equal label "NAT-LIST-WFR")
    (h2-ordinals-derive proof formula "NAT-LIST-<" '("O-P-OF-NAT-LIST-MEASURE") nil 80))
   ((equal label "OPEN-NAT-LIST-<")
    (h2-ordinals-derive proof formula "NAT-LIST-< SYNP" '("O<-OF-NAT-LIST-MEASURE") nil 80))
   ((equal label "NATP-NAT-LIST-<")
    (h2-recipes-with-results
     ((comparison (h2-modular-term-at formula '(2 1)))
      (inputs (if (integerp comparison) (proof-term-at comparison 1) (seq-slice comparison 1 :none)))
      (noncons (h2-ordinals-fix-arguments inputs nil (cons nil proof) nil)))
     (h2-ordinals-derive (cdr noncons) formula "NAT-LIST-< NAT-LIST-MEASURE O< O-FINP"
                         nil (car noncons) 80)))
   (t (cons nil proof))))
