(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-trees-dumb-negate* (proof-sym "DUMB-NEGATE-LIT" "ACL2"))
(defconst *t3-trees-parse-declarations* (proof-sym "SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1" "ACL2"))
(defconst *t3-trees-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *t3-trees-guard-index* (proof-quote 5))
(defconst *t3-trees-guard-count* (proof-sym "SELF-T3-PARSED-GUARD-COUNT" "ACL2"))

(defun t3-trees-right-side (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun t3-trees-count-cons (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *library-count* term)))
         (cons-proof (if (proof-is-call term *proof-cons*)
                         (proof-with-checked-results
                             ((step (proof-proof-fact proof "consp-cons"
                                                      (seq-zip (list *library-x* *library-y*) (cdr term)))))
                           (cons step evidence))
                       (t3-logic-evidence-require evidence (list *t3-logic-consp* term))))
         (value (t3-trees-right-side opened))
         (selected (proof-proof-select proof value (car cons-proof)))
         (result (proof-proof-chain proof opened (list selected)))
         (value (t3-trees-right-side result))
         (normalized (t3-logic-libraryproofs-normalize lib value nil nil))
         (step (proof-proof-chain proof result (list normalized))))
      (cons step (cdr cons-proof)))))

(mutual-recursion
 (defun t3-trees-folded-count (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *proof-quote*)
     (proof-with-checked-results
         ((result (t3-logic-libraryproofs-normalize
                   lib (list *library-count* term) nil
                   (list *library-count* (proof-sym "INTEGER-ABS" "ACL2")))))
       (cons result evidence)))
    ((not (proof-is-call term *proof-cons*)) (cons nil evidence))
    (t
     (proof-with-checked-results
         ((opened (t3-trees-count-cons lib term evidence))
          (children (t3-trees-folded-count-children lib (cdr term) 1 (car opened) (cdr opened)))
          (value (t3-trees-right-side (car children)))
          (normalized (t3-logic-libraryproofs-normalize lib value nil nil))
          (step (proof-proof-chain (library-library-proof lib) (car children) (list normalized))))
       (cons step (cdr children))))))

 (defun t3-trees-folded-count-children (lib children index step evidence)
   (declare (xargs :measure (acl2-count children)))
   (if (endp children)
       (cons step evidence)
     (proof-with-checked-results
         ((reached (t3-trees-folded-count lib (car children) evidence))
          (step (if (car reached)
                    (proof-proof-rewrite (library-library-proof lib)
                                         step (car reached) (list 1 2 2 index))
                  step)))
       (t3-trees-folded-count-children lib (cdr children) (1+ index) step (cdr reached))))))

(defun t3-trees-negated-literal-construction (lib construction old upper evidence)
  (let ((proof (library-library-proof lib))
        (two *t3-arithmetic-two*))
    (proof-with-checked-results ((after (t3-trees-right-side construction)))
      (if (equal after two)
          (proof-with-checked-results
              ((nonnegative (t3-logic-evidence-nonnegative evidence old))
               (weak (t3-size-shift lib (car nonnegative) two t nil))
               (sum (proof-proof-compute proof (library-plus two *proof-zero*) 2))
               (weak (proof-proof-rewrite proof weak sum '(1 1 2)))
               (reversed (proof-proof-symmetric proof construction))
               (result (proof-proof-rewrite proof weak reversed '(1 1 2))))
            (proof-proof-tidy proof result))
        (proof-with-checked-results
            ((after-type (t3-logic-libraryproofs-type-of lib after nil))
             (old-type (t3-logic-libraryproofs-type-of lib old nil))
             (same (library-library-linear-equal lib after upper (list after-type old-type)))
             (construction (proof-proof-chain proof construction (list same)))
             (upper-type (t3-logic-libraryproofs-type-of lib upper nil))
             (weak (library-library-cite lib "WEAK-REFLEXIVE" (list upper) (list upper-type)))
             (reversed (proof-proof-symmetric proof construction))
             (result (proof-proof-rewrite proof weak reversed '(1 1 2))))
          (proof-proof-tidy proof result))))))

(defun t3-trees-negated-literal-bound-leaf (value tests lib old upper)
  (proof-with-checked-results
      ((evidence (t3-logic-evidence-init lib tests nil nil))
       (construction (t3-trees-folded-count lib value evidence)))
    (if (car construction)
        (t3-trees-negated-literal-construction lib (car construction) old upper (cdr construction))
      (proof-with-checked-results
          ((weak (t3-size-count-bound lib value *library-x* (cdr construction)))
           (increase (t3-arithmetic-integer-comparison lib old upper (cdr weak)))
           (strict (t3-size-chain lib (car weak) (car increase) nil)))
        (library-library-as-weak lib strict)))))

(defun t3-trees-negated-literal-bound-leaves (requests lib old upper)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((step (t3-trees-negated-literal-bound-leaf (caar requests) (cadar requests) lib old upper))
         (rest (t3-trees-negated-literal-bound-leaves (cdr requests) lib old upper)))
      (acons (car requests) step rest))))

(defun t3-trees-negated-literal-bound (lib)
  (let* ((proof (library-library-proof lib))
         (negated (list *t3-trees-dumb-negate* *library-x*))
         (old (list *library-count* *library-x*))
         (upper (library-plus *t3-arithmetic-two* old))
         (template (library-le (list *library-count* *proof-result*) upper)))
    (proof-with-checked-results
        ((body (proof-proof-unfold proof negated))
         (value (t3-trees-right-side body))
         (requests (t3-logic-libraryproofs-by-value-leaves lib value nil))
         (leaves (t3-trees-negated-literal-bound-leaves requests lib old upper))
         (step (t3-logic-libraryproofs-by-value lib value template leaves nil))
         (reversed (proof-proof-symmetric proof body))
         (step (proof-proof-rewrite-result proof step reversed template *proof-result*)))
      (library-library-lemma lib "T3-NEGATED-LITERAL-COUNT"
                             (library-le (list *library-count* negated) upper) step nil))))

(defun t3-trees-three-cons-margin (lib parent field evidence)
  (let* ((proof (library-library-proof lib))
         (middle (list *library-cdr* parent))
         (inner (list *library-cdr* middle)))
    (proof-with-checked-results
        ((expansion (t3-trees-count-cons lib parent evidence))
         (middle-proof (t3-trees-count-cons lib middle (cdr expansion)))
         (step (proof-proof-rewrite proof (car expansion) (car middle-proof) '(1 2 2 2)))
         (inner-proof (t3-trees-count-cons lib inner (cdr middle-proof)))
         (expansion (proof-proof-rewrite proof step (car inner-proof) '(1 2 2 2 2 2)))
         (intermediate (library-plus *t3-arithmetic-two* (list *library-count* field)))
         (value (t3-trees-right-side expansion))
         (advance (t3-arithmetic-integer-comparison lib intermediate value (cdr inner-proof)))
         (step (library-library-transport-argument lib (car advance) expansion 2)))
      (cons step (cdr advance)))))

(defun t3-trees-evidence-after-library (evidence before after)
  (if (equal (t3-logic-evidence-lib evidence) before)
      (t3-logic-evidence-with-lib evidence after)
    evidence))

(defun t3-trees-negated-literal-descent (lib smaller larger evidence)
  (proof-with-checked-results
      ((output (proof-term-at smaller 1))
       (parent (proof-term-at larger 1)))
    (if (not (proof-is-call output *t3-trees-dumb-negate*))
        (cons (list nil evidence) lib)
      (proof-with-checked-results ((test (proof-term-at output 1)))
        (if (not (equal test (list *library-car* (list *library-cdr* parent))))
            '(:failure "Unsupported" "")
          (proof-with-checked-results
              ((before lib)
               (lib (if (assoc-equal (proof-sym "SELF-T3-NEGATED-LITERAL-COUNT" "ACL2")
                                     (proof-proof-facts (library-library-proof lib)))
                        lib
                      (t3-trees-negated-literal-bound lib)))
               (evidence (t3-trees-evidence-after-library evidence before lib))
               (advance (t3-trees-three-cons-margin lib parent test evidence))
               (bound (library-library-cite lib "T3-NEGATED-LITERAL-COUNT" (list test) nil))
               (strict (t3-size-chain lib bound (car advance) nil))
               (order (library-library-ordinal-comparison lib smaller larger))
               (step (proof-proof-transport (library-library-proof lib) strict order)))
            (cons (list step (cdr advance)) lib)))))))

(defun t3-trees-guard-upper (edcls guard)
  (library-plus *t3-arithmetic-two*
                (library-plus (list *library-count* edcls) (list *library-count* guard))))

(defun t3-trees-guard-input-bound (lib edcls guard new-edcls new-guard evidence)
  (let ((two *t3-arithmetic-two*))
    (if (equal new-guard guard)
        (proof-with-checked-results
            ((bound (t3-size-count-bound lib new-edcls edcls evidence))
             (extended (t3-size-shift lib (car bound) (list *library-count* guard) nil nil))
             (step (t3-size-shift lib extended two t nil)))
          (cons step (cdr bound)))
      (let ((head (list *library-car* edcls))
            (size (list *library-count* new-edcls)))
        (proof-with-checked-results
            ((weak (t3-size-count-bound lib new-guard head evidence))
             (bound (t3-size-shift lib (car weak) size t nil))
             (expansion (t3-trees-count-cons lib edcls (cdr weak)))
             (total (library-plus size (list *library-count* head)))
             (value (t3-trees-right-side (car expansion)))
             (strict (t3-arithmetic-integer-comparison lib total value (cdr expansion)))
             (order (library-library-transport-argument lib (car strict) (car expansion) 2))
             (nonnegative (t3-logic-evidence-nonnegative (cdr strict) (list *library-count* guard)))
             (grows (t3-size-sum-at-least lib (list *library-count* edcls) (car nonnegative) nil t))
             (combined (t3-size-chain lib bound order nil))
             (combined (t3-size-chain lib combined grows nil))
             (step (t3-size-shift lib combined two t nil)))
          (cons step (cdr nonnegative)))))))

(defun t3-trees-guard-leaf (lib field edcls guard tests)
  (let ((upper (t3-trees-guard-upper edcls guard))
        (proof (library-library-proof lib))
        (two *t3-arithmetic-two*))
    (proof-with-checked-results ((evidence (t3-logic-evidence-init lib tests nil nil)))
      (if (equal field guard)
          (proof-with-checked-results
              ((strict (t3-arithmetic-integer-comparison lib (list *library-count* guard) upper evidence)))
            (library-library-as-weak lib (car strict)))
        (proof-with-checked-results ((opened (t3-trees-folded-count lib field evidence)))
          (if (not (car opened))
              '(:failure "Unsupported" "")
            (proof-with-checked-results
                ((size (t3-trees-right-side (car opened)))
                 (bound (if (equal size two)
                            (proof-with-checked-results
                                ((nonnegative (t3-logic-evidence-nonnegative (cdr opened) (caddr upper))))
                              (t3-size-sum-at-least lib two (car nonnegative) nil t))
                          (proof-with-checked-results
                              ((strict (t3-arithmetic-integer-comparison lib size upper (cdr opened))))
                            (library-library-as-weak lib (car strict)))))
                 (reversed (proof-proof-symmetric proof (car opened)))
                 (step (proof-proof-rewrite proof bound reversed '(1 1 2))))
              (proof-proof-tidy proof step))))))))

(defun t3-trees-parsed-guard-definition (lib)
  (let ((entry (assoc-equal *t3-trees-parse-declarations*
                           (proof-proof-definitions (library-library-proof lib)))))
    (if entry
        (proof-list-of-length (cdr entry) 2)
      '(:failure "failure" ""))))

(defun t3-trees-parsed-guard-field-leaves (requests lib edcls guard)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((step (t3-trees-guard-leaf lib (caar requests) edcls guard (cadar requests)))
         (rest (t3-trees-parsed-guard-field-leaves (cdr requests) lib edcls guard)))
      (acons (car requests) step rest))))

(defun t3-trees-parsed-guard-recursive-leaf
    (lib value formals edcls guard measure formula substitutions evidence)
  (let* ((proof (library-library-proof lib))
         (pairs (proof-nonidentity-pairs (seq-zip formals (cdr value))))
         (substitutions (if (member-equal pairs substitutions)
                            substitutions
                          (append substitutions (list pairs)))))
    (proof-with-checked-results
        ((new-edcls (proof-term-at value 1))
         (smaller (t3-size-count-descent lib (list *library-count* new-edcls) measure evidence))
         (claim (proof-subst formula (proof-bindings-table pairs nil)))
         (comparison (proof-step-first (car smaller)))
         (assumed (proof-proof-assume proof (proof-ite comparison claim *proof-true*) t))
         (inductive (proof-proof-prove-if proof assumed (car smaller)))
         (new-guard (car (last value)))
         (bound (t3-trees-guard-input-bound lib edcls guard new-edcls new-guard (cdr smaller)))
         (strict (t3-size-chain lib inductive (car bound) nil))
         (step (library-library-as-weak lib strict)))
      (cons step substitutions))))

(defun t3-trees-parsed-guard-result-leaf (lib value tests edcls guard upper)
  (let ((proof (library-library-proof lib))
        (selected (list *t3-trees-mv-nth* *t3-trees-guard-index* value)))
    (proof-with-checked-results
        ((opened (t3-logic-libraryproofs-normalize
                  lib selected nil (list *t3-trees-mv-nth* *t3-logic-zp* *proof-not* *t3-logic-atom*))))
      (if (not opened)
          '(:failure "Unsupported" "")
        (proof-with-checked-results
            ((value (t3-trees-right-side opened))
             (requests (t3-logic-libraryproofs-by-value-leaves lib value tests))
             (leaves (t3-trees-parsed-guard-field-leaves requests lib edcls guard))
             (template (library-le (list *library-count* *proof-result*) upper))
             (field (t3-logic-libraryproofs-by-value lib value template leaves tests))
             (reversed (proof-proof-symmetric proof opened))
             (step (proof-proof-rewrite proof field reversed '(1 1 2 1))))
          (proof-proof-tidy proof step))))))

(defun t3-trees-parsed-guard-bound-leaf
    (value tests lib formals edcls guard measure upper formula substitutions)
  (proof-with-checked-results ((evidence (t3-logic-evidence-init lib tests nil nil)))
    (if (proof-is-call value *t3-trees-parse-declarations*)
        (t3-trees-parsed-guard-recursive-leaf
         lib value formals edcls guard measure formula substitutions evidence)
      (proof-with-checked-results
          ((step (t3-trees-parsed-guard-result-leaf lib value tests edcls guard upper)))
        (cons step substitutions)))))

(defun t3-trees-parsed-guard-bound-leaves
    (requests lib formals edcls guard measure upper formula substitutions)
  (if (endp requests)
      (cons nil substitutions)
    (proof-with-checked-results
        ((leaf (t3-trees-parsed-guard-bound-leaf
                (caar requests) (cadar requests) lib formals edcls guard measure upper formula
                substitutions))
         (rest (t3-trees-parsed-guard-bound-leaves
                (cdr requests) lib formals edcls guard measure upper formula (cdr leaf))))
      (cons (acons (car requests) (car leaf) (car rest)) (cdr rest)))))

(defun t3-trees-parsed-guard-bound (lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((definition (t3-trees-parsed-guard-definition lib))
         (formals (car definition))
         (edcls (proof-term-at formals 0))
         (guard (car (last formals)))
         (call (cons *t3-trees-parse-declarations* formals))
         (measure (list *library-count* edcls))
         (upper (t3-trees-guard-upper edcls guard))
         (template (library-le (list *library-count*
                                     (list *t3-trees-mv-nth* *t3-trees-guard-index* *proof-result*))
                               upper))
         (formula (proof-subst template (list (cons *proof-result* call))))
         (body (proof-proof-unfold proof call))
         (value (t3-trees-right-side body))
         (requests (t3-logic-libraryproofs-by-value-leaves lib value nil))
         (leaves (t3-trees-parsed-guard-bound-leaves
                  requests lib formals edcls guard measure upper formula nil))
         (step (t3-logic-libraryproofs-by-value lib value template (car leaves) nil))
         (reversed (proof-proof-symmetric proof body))
         (step (proof-proof-rewrite-result proof step reversed template *proof-result*))
         (ordinal (library-library-builtin lib 1 edcls))
         (step (proof-proof-induct proof ordinal step formula measure (cdr leaves))))
      (library-library-lemma lib "T3-PARSED-GUARD-COUNT" formula step nil))))

(defun t3-trees-parsed-guard-descent-bound (lib smaller larger edcls field inputs evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((definition (t3-trees-parsed-guard-definition lib))
         (bound (proof-proof-fact proof *t3-trees-guard-count* (seq-zip (car definition) inputs)))
         (nil-size (t3-trees-folded-count lib *proof-false* evidence))
         (count-term (list *library-count* edcls))
         (typed (t3-logic-libraryproofs-type-of lib count-term nil))
         (trim (library-library-cite lib "ADD-ZERO-RIGHT" (list count-term) (list typed)))
         (bound (if (car nil-size)
                    (proof-proof-rewrite proof bound (car nil-size) '(1 1 1 2 2))
                  '(:failure "failure" "")))
         (bound (proof-proof-rewrite proof bound trim '(1 1 1 2)))
         (weak (t3-size-count-bound lib edcls field (cdr nil-size)))
         (field-bound (t3-size-shift lib (car weak) *t3-arithmetic-two* t nil))
         (parent (cadr larger))
         (strict (t3-trees-three-cons-margin lib parent field (cdr weak)))
         (decrease (t3-size-chain lib bound field-bound nil))
         (decrease (t3-size-chain lib decrease (car strict) nil))
         (order (library-library-ordinal-comparison lib smaller larger))
         (step (proof-proof-transport proof decrease order)))
      (cons (list step (cdr strict)) lib))))

(defun t3-trees-parsed-guard-descent (lib smaller larger evidence)
  (proof-with-checked-results
      ((value (proof-term-at smaller 1))
       (parent (proof-term-at larger 1)))
    (if (not (proof-is-call value *t3-trees-mv-nth*))
        (cons (list nil evidence) lib)
      (proof-with-checked-results ((index (proof-term-at value 1)))
        (if (not (equal index *t3-trees-guard-index*))
            (cons (list nil evidence) lib)
          (proof-with-checked-results ((call (proof-term-at value 2)))
            (if (not (proof-is-call call *t3-trees-parse-declarations*))
                (cons (list nil evidence) lib)
              (proof-with-checked-results
                  ((inputs (cdr call))
                   (edcls (proof-term-at inputs 0))
                   (guard (car (last inputs)))
                   (field (list *library-car* (list *library-cdr* (list *library-cdr* parent)))))
                (if (or (not (equal guard *proof-false*))
                        (not (equal edcls (list *library-cdr* field))))
                    '(:failure "Unsupported" "")
                  (proof-with-checked-results
                      ((before lib)
                       (lib (if (assoc-equal *t3-trees-guard-count*
                                             (proof-proof-facts (library-library-proof lib)))
                                lib
                              (t3-trees-parsed-guard-bound lib)))
                       (evidence (t3-trees-evidence-after-library evidence before lib)))
                    (t3-trees-parsed-guard-descent-bound
                     lib smaller larger edcls field inputs evidence)))))))))))
