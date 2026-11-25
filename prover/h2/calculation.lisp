(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-calculation-numberp* (proof-sym "ACL2-NUMBERP" "ACL2"))
(defconst *h2-calculation-fix* (proof-sym "FIX" "ACL2"))
(defconst *h2-calculation-reciprocal* (proof-sym "UNARY-/" "ACL2"))
(defconst *h2-calculation-rationalp* (proof-cl "RATIONALP"))
(defconst *h2-calculation-number-rules*
  '("SELF-H2-NUMBER-ADD-ZERO-LEFT" "SELF-H2-NUMBER-ADD-ZERO-RIGHT"
    "SELF-H2-NUMBER-DOUBLE-NEGATION" "SELF-H2-NUMBER-NEGATE-SUM" "SELF-H2-PRODUCT-NUMBER"
    "SELF-H2-RECIPROCAL-NUMBER" "SELF-H2-FIX-NUMBER" "SELF-H2-NEGATIVE-NONNUMBER"
    "SELF-H2-NUMBER-FIX"))

(defconst *h2-calculation-number-closure*
  (list (cons *proof-plus* "SUM-NUMBER")
        (cons *proof-minus* "NEGATION-NUMBER")
        (cons *proof-times* "H2-PRODUCT-NUMBER")
        (cons *h2-calculation-reciprocal* "H2-RECIPROCAL-NUMBER")
        (cons *h2-calculation-fix* "H2-FIX-NUMBER")))

(defun h2-calculation-number-sums-init (library)
  (list :h2-number-sums library))

(defun h2-calculation-number-sums-proof (sums)
  (cadr sums))

(defconst *h2-calculation-sum-delegates*
  '("add-definition" "fact" "instantiate" "use" "subsume" "tidy" "front" "cut" "rewrite"
    "rewrite-first" "rewrite-result" "beta" "compute" "induct" "unfold" "reflexive" "symmetric"
    "chain" "true-from-eq" "nil-or-true" "not-nil" "excluded-middle" "assume" "discharge"
    "if-false" "if-true" "select" "prove-if" "conjunct" "modus-ponens" "transport" "cases"
    "by-value" "simplify" "constant" "simplify-first" "prove" "lemma" "definition" "axiom"
    "builtin" "cite" "ints" "type-of" "natural" "rational" "number" "logic-and-types"
    "transport-argument" "additive-identities" "push-minus" "linear-form" "linear-equal" "comparison"
    "less-from-difference" "weak-from-difference" "ordered-arithmetic" "tenfold-increase"
    "order-lemmas" "compare-chain" "as-weak" "ordinal-comparison" "length-lemmas" "count-lemmas"
    "weak-selectors" "integer-measures" "build"))

(defun h2-calculation-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h2-calculation-inapplicable-p (result)
  (and (failure-p result)
       (member-equal (cadr result) '("arithmetic-inapplicable" "value"))
       t))

(defun h2-calculation-sum-p (term)
  (or (proof-is-call term *proof-plus*) (proof-is-call term *proof-minus*)))

(defun h2-calculation-number-sums-cite (sums name arguments evidence)
  (library-library-cite
   (h2-calculation-number-sums-proof sums)
   (if (member-equal name '("ADD-ZERO-LEFT" "ADD-ZERO-RIGHT" "DOUBLE-NEGATION" "NEGATE-SUM"))
       (concatenate 'string "H2-NUMBER-" name)
     name)
   arguments evidence))

(defun h2-calculation-number-evidence (library term evidence)
  (declare (xargs :measure (acl2-count evidence)))
  (if (endp evidence)
      nil
    (let ((proof (library-library-proof library))
          (step (car evidence)))
      (proof-with-checked-results ((literal (proof-step-first step)))
        (cond
         ((equal literal (list *h2-calculation-numberp* term)) step)
         ((equal literal (list *proof-integerp* term))
          (library-library-number library term (list step)))
         ((equal literal (list *h2-calculation-rationalp* term))
          (proof-with-checked-results
           ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term)))))
           (proof-proof-modus-ponens proof fact step)))
         (t (h2-calculation-number-evidence library term (cdr evidence))))))))

(defun h2-calculation-quoted-number-p (term)
  (and (proof-is-call term *proof-quote*)
       (proof-with-checked-results ((value (proof-term-at term 1)))
         (cond
          ((integerp value) t)
          ((null value) (proof-index-failure))
          (t (and (consp value) (member-equal (car value) '("ratio" "complex"))))))))

(defun h2-calculation-number-sums-type-of (sums term evidence)
  (let* ((library (h2-calculation-number-sums-proof sums))
         (proof (library-library-proof library)))
    (proof-with-checked-results ((typed (h2-calculation-number-evidence library term evidence)))
      (if typed
          typed
        (proof-with-checked-results ((quoted (h2-calculation-quoted-number-p term)))
          (if quoted
              (proof-with-checked-results
               ((computed (proof-proof-compute proof (list *h2-calculation-numberp* term) *proof-t*)))
               (proof-proof-true-from-eq proof computed))
            (let ((closure (and (proof-compound term)
                                (assoc-equal (car term) *h2-calculation-number-closure*))))
              (if closure
                  (library-library-cite library (cdr closure) (cdr term) nil)
                '(:failure "arithmetic-inapplicable" "")))))))))

(defun h2-calculation-number-types (sums terms evidence)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (proof-with-checked-results
     ((first (h2-calculation-number-sums-type-of sums (car terms) evidence))
      (rest (h2-calculation-number-types sums (cdr terms) evidence)))
     (cons first rest))))

(defun h2-calculation-number-negation (sums argument evidence)
  (let* ((library (h2-calculation-number-sums-proof sums))
         (facts (proof-proof-facts (library-library-proof library))))
    (cond
     ((and (proof-is-call argument *proof-minus*)
           (assoc-equal (proof-sym "SELF-DOUBLE-NEGATION" "ACL2") facts))
      (proof-with-checked-results
       ((inner (proof-term-at argument 1))
        (typed (h2-calculation-number-sums-type-of sums inner evidence)))
       (h2-calculation-number-sums-cite sums "DOUBLE-NEGATION" (list inner) (list typed))))
     ((and (proof-is-call argument *proof-plus*)
           (assoc-equal (proof-sym "SELF-NEGATE-SUM" "ACL2") facts))
      (proof-with-checked-results ((types (h2-calculation-number-types sums (cdr argument) evidence)))
        (h2-calculation-number-sums-cite sums "NEGATE-SUM" (cdr argument) types)))
     (t nil))))

(defun h2-calculation-number-sums-push-minus-visit (n sums term evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h2-calculation-number-sums-push-minus-visit")
    (let* ((library (h2-calculation-number-sums-proof sums))
           (proof (library-library-proof library)))
      (cond
       ((proof-is-call term *proof-plus*)
        (proof-with-checked-results
         ((result (proof-proof-reflexive proof term))
          (left (proof-term-at term 1))
          (left-step (h2-calculation-number-sums-push-minus-visit (1- n) sums left evidence))
          (result (if left-step (proof-proof-rewrite proof result left-step '(1 2 1)) result))
          (right (proof-term-at term 2))
          (right-step (h2-calculation-number-sums-push-minus-visit (1- n) sums right evidence))
          (result (if right-step (proof-proof-rewrite proof result right-step '(1 2 2)) result))
          (normalized (h2-calculation-step-at result 2)))
         (if (equal normalized term) nil result)))
       ((proof-is-call term *proof-minus*)
        (proof-with-checked-results ((argument (proof-term-at term 1)))
          (if (proof-is-call argument *proof-quote*)
              (proof-proof-constant proof term)
            (proof-with-checked-results ((result (h2-calculation-number-negation sums argument evidence)))
              (and result
                   (proof-with-checked-results
                    ((right (h2-calculation-step-at result 2))
                     (rest (h2-calculation-number-sums-push-minus-visit (1- n) sums right evidence)))
                    (proof-proof-chain proof result (list rest))))))))
       (t nil)))))

(defun h2-calculation-number-sums-push-minus (sums term evidence)
  (h2-calculation-number-sums-push-minus-visit 1000000 sums term evidence))

(defun h2-calculation-number-remove-zero (sums step name term place evidence)
  (proof-with-checked-results
   ((typed (h2-calculation-number-sums-type-of sums term evidence))
    (zero-step (h2-calculation-number-sums-cite sums name (list term) (list typed))))
   (proof-proof-rewrite (library-library-proof (h2-calculation-number-sums-proof sums))
                       step zero-step place)))

(defun h2-calculation-number-combine (n sums step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h2-calculation-number-combine")
    (let* ((library (h2-calculation-number-sums-proof sums))
           (proof (library-library-proof library)))
      (proof-with-checked-results
       ((literal (proof-step-first step))
        (node (library-linear-form-get literal (cdr place))))
       (if (not (proof-is-call node *proof-plus*))
           (proof-proof-tidy proof step)
         (proof-with-checked-results ((pair (proof-list-of-length (cdr node) 2)))
           (let* ((a (car pair))
                  (rest (cadr pair))
                  (suffix (proof-is-call rest *proof-plus*)))
             (proof-with-checked-results ((b (if suffix (proof-term-at rest 1) rest)))
               (cond
                ((equal a *proof-zero*)
                 (proof-with-checked-results
                  ((step (h2-calculation-number-remove-zero sums step "ADD-ZERO-LEFT"
                                                            rest place evidence)))
                  (h2-calculation-number-combine (1- n) sums step place evidence)))
                ((and (equal b *proof-zero*) (not suffix))
                 (proof-with-checked-results
                  ((step (h2-calculation-number-remove-zero sums step "ADD-ZERO-RIGHT"
                                                            a place evidence)))
                  (h2-calculation-number-combine (1- n) sums step place evidence)))
                (t
                 (proof-with-checked-results ((combine (library-linear-combine-pair library a b)))
                   (if (not combine)
                       (h2-calculation-number-combine (1- n) sums step (append place '(2)) evidence)
                     (proof-with-checked-results
                      ((step (if suffix
                                 (proof-with-checked-results
                                  ((tail (proof-term-at rest 2))
                                   (association (library-library-axiom library "ASSOCIATIVITY-OF-+"
                                                                       (list a b tail)))
                                   (reverse (proof-proof-symmetric proof association)))
                                  (proof-proof-rewrite proof step reverse place))
                               step))
                       (step (proof-proof-rewrite proof step combine
                                                  (if suffix (append place '(1)) place))))
                      (h2-calculation-number-combine (1- n) sums step '(1 2) evidence))))))))))))))

(defun h2-calculation-number-sums-linear-form (sums term evidence)
  (let ((library (h2-calculation-number-sums-proof sums)))
    (proof-with-checked-results
     ((step (h2-calculation-number-sums-push-minus sums term evidence))
      (step (or step (proof-proof-reflexive (library-library-proof library) term)))
      (step (library-linear-reassociate 1000000 library step '(1 2)))
      (step (library-linear-sort 1000000 library step '(1 2) nil)))
     (h2-calculation-number-combine 1000000 sums step '(1 2) evidence))))

(defun h2-calculation-number-sums-linear-equal (sums left right evidence)
  (proof-with-checked-results
   ((a (h2-calculation-number-sums-linear-form sums left evidence))
    (b (h2-calculation-number-sums-linear-form sums right evidence))
    (a-normal (h2-calculation-step-at a 2))
    (b-normal (h2-calculation-step-at b 2)))
   (if (equal a-normal b-normal)
       (let ((proof (library-library-proof (h2-calculation-number-sums-proof sums))))
         (proof-with-checked-results ((reverse (proof-proof-symmetric proof b)))
           (proof-proof-chain proof a (list reverse))))
     (proof-with-checked-results ((a-text (proof-write a-normal)) (b-text (proof-write b-normal)))
       '(:failure "arithmetic-inapplicable" "")))))

(defun h2-calculation-number-sums-unique-inverse (a b cancels proof sums evidence)
  (let ((library (h2-calculation-number-sums-proof sums)))
    (proof-with-checked-results
     ((commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus a) a)))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list a)))
      (inverse (proof-proof-chain proof commute (list inverse)))
      (b-type (h2-calculation-number-sums-type-of sums b evidence))
      (left (h2-calculation-number-sums-cite sums "ADD-ZERO-LEFT" (list b) (list b-type)))
      (reverse (proof-proof-symmetric proof inverse))
      (left (proof-proof-rewrite proof left reverse '(1 1 1)))
      (associate (library-library-axiom library "ASSOCIATIVITY-OF-+" (list (library-minus a) a b)))
      (left (proof-proof-symmetric proof left))
      (expanded (proof-proof-chain proof left (list associate)))
      (expanded (proof-proof-rewrite proof expanded cancels '(1 2 2)))
      (minus-type (h2-calculation-number-sums-type-of sums (library-minus a) evidence))
      (right (h2-calculation-number-sums-cite sums "ADD-ZERO-RIGHT" (list (library-minus a))
                                              (list minus-type))))
     (proof-proof-chain proof expanded (list right)))))

(defun h2-calculation-number-sums (library)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (y *library-y*)
         (fix (list *h2-calculation-fix* x)))
    (if (assoc-equal (proof-sym (car *h2-calculation-number-rules*) "ACL2") (proof-proof-facts proof))
        library
      (proof-with-checked-results
       ((xn (proof-proof-assume proof (list *h2-calculation-numberp* x) t))
        (yn (proof-proof-assume proof (list *h2-calculation-numberp* y) t))
        (x-type (proof-step-first xn))
        (y-type (proof-step-first yn))
        (fixed (proof-proof-unfold proof fix))
        (body (h2-calculation-step-at fixed 2))
        (selected (proof-proof-select proof body xn))
        (fix-x (proof-proof-chain proof fixed (list selected)))
        (claim (proof-step-first fix-x))
        (library (library-library-lemma library "H2-NUMBER-FIX" claim fix-x (list (proof-neg x-type))))
        (proof (library-library-proof library))
        (left-zero (library-library-axiom library "UNICITY-OF-0" (list x)))
        (left-zero (proof-proof-chain proof left-zero (list fix-x)))
        (right-zero (library-library-axiom library "COMMUTATIVITY-OF-+" (list x *proof-zero*)))
        (right-zero (proof-proof-chain proof right-zero (list left-zero)))
        (claim (proof-step-first left-zero))
        (library (library-library-lemma library "H2-NUMBER-ADD-ZERO-LEFT" claim left-zero
                                        (list (proof-neg x-type))))
        (claim (proof-step-first right-zero))
        (library (library-library-lemma library "H2-NUMBER-ADD-ZERO-RIGHT" claim right-zero
                                        (list (proof-neg x-type))))
        (proof (library-library-proof library))
        (closure (library-library-axiom library "CLOSURE" (list x y)))
        (closure (proof-proof-conjunct proof closure))
        (closure (proof-proof-conjunct proof (cadr closure)))
        (product (car closure))
        (closure (proof-proof-conjunct proof (cadr closure)))
        (reciprocal (cadr closure))
        (claim (proof-step-first product))
        (library (library-library-lemma library "H2-PRODUCT-NUMBER" claim product nil))
        (claim (proof-step-first reciprocal))
        (library (library-library-lemma library "H2-RECIPROCAL-NUMBER" claim reciprocal nil))
        (proof (library-library-proof library))
        (nonnumber (proof-proof-assume proof x-type nil))
        (selected (proof-proof-select proof body nonnumber))
        (absent (proof-proof-chain proof fixed (list selected)))
        (zero (h2-calculation-number-sums-type-of (h2-calculation-number-sums-init library) *proof-zero* nil))
        (projected (library-library-transport-argument library zero absent 1))
        (present (library-library-transport-argument library xn fix-x 1))
        (proper (proof-proof-cases proof x-type present projected))
        (claim (proof-step-first proper))
        (library (library-library-lemma library "H2-FIX-NUMBER" claim proper nil))
        (proof (library-library-proof library))
        (completion (library-library-axiom library "COMPLETION-OF-UNARY-MINUS" (list x)))
        (body (h2-calculation-step-at completion 2))
        (selected (proof-proof-select proof body nonnumber))
        (negative (proof-proof-chain proof completion (list selected)))
        (claim (proof-step-first negative))
        (library (library-library-lemma library "H2-NEGATIVE-NONNUMBER" claim negative (list x-type)))
        (proof (library-library-proof library))
        (sums (h2-calculation-number-sums-init library))
        (evidence (list xn yn))
        (inverse (library-library-axiom library "INVERSE-OF-+" (list x)))
        (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus x) x)))
        (reverse-inverse (proof-proof-chain proof commute (list inverse)))
        (inverse (h2-calculation-number-sums-unique-inverse (library-minus x) x reverse-inverse
                                                           proof sums evidence))
        (involution (proof-proof-symmetric proof inverse))
        (claim (proof-step-first involution))
        (library (library-library-lemma library "H2-NUMBER-DOUBLE-NEGATION" claim involution
                                        (list (proof-neg x-type))))
        (proof (library-library-proof library))
        (sums (h2-calculation-number-sums-init library))
        (left (library-plus x y))
        (right (library-plus (library-minus x) (library-minus y)))
        (cancels (h2-calculation-number-sums-linear-equal sums (library-plus left right) *proof-zero* evidence))
        (inverse (h2-calculation-number-sums-unique-inverse left right cancels proof sums evidence))
        (distributed (proof-proof-symmetric proof inverse))
        (claim (proof-step-first distributed)))
       (library-library-lemma library "H2-NUMBER-NEGATE-SUM" claim distributed
                              (list (proof-neg x-type) (proof-neg y-type)))))))

(defun h2-calculation-product-form-at (place result)
  (proof-with-checked-results ((literal (proof-step-first result)))
    (library-linear-form-get literal (cdr place))))

(defun h2-calculation-product-form-factor-key (factor)
  (cond
   ((proof-is-call factor *h2-calculation-reciprocal*)
    (proof-with-checked-results ((argument (proof-term-at factor 1)) (text (proof-write argument)))
      (list text 1)))
   ((equal factor *proof-one*) (list "" 0))
   (t (proof-with-checked-results ((text (proof-write factor)))
        (list text 0)))))

(defun h2-calculation-factor-after-p (first second)
  (proof-with-checked-results
   ((a (h2-calculation-product-form-factor-key first))
    (b (h2-calculation-product-form-factor-key second)))
   (or (string< (car b) (car a))
       (and (equal (car a) (car b)) (< (cadr b) (cadr a))))))

(defun h2-calculation-product-reassociate (n library result place)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h2-calculation-product-reassociate")
    (proof-with-checked-results ((node (h2-calculation-product-form-at place result)))
      (if (not (proof-is-call node *proof-times*))
          result
        (proof-with-checked-results ((call (proof-list-of-length node 3)))
          (let ((left (cadr call)) (right (caddr call)))
            (if (not (proof-is-call left *proof-times*))
                (h2-calculation-product-reassociate (1- n) library result (append place '(2)))
              (proof-with-checked-results
               ((a (proof-term-at left 1))
                (b (proof-term-at left 2))
                (association (library-library-axiom library "ASSOCIATIVITY-OF-*" (list a b right)))
                (result (proof-proof-rewrite (library-library-proof library) result association place)))
               (h2-calculation-product-reassociate (1- n) library result place)))))))))

(defun h2-calculation-product-swap (library first rest)
  (if (proof-is-call rest *proof-times*)
      (proof-with-checked-results
       ((pair (proof-list-of-length (cdr rest) 2))
        (after (h2-calculation-factor-after-p first (car pair))))
       (if (not after)
           nil
         (let ((second (car pair)) (tail (cadr pair)) (proof (library-library-proof library)))
           (proof-with-checked-results
            ((association (library-library-axiom library "ASSOCIATIVITY-OF-*" (list first second tail)))
             (swap (proof-proof-symmetric proof association))
             (commute (library-library-axiom library "COMMUTATIVITY-OF-*" (list first second)))
             (swap (proof-proof-rewrite proof swap commute '(1 2 1)))
             (association (library-library-axiom library "ASSOCIATIVITY-OF-*" (list second first tail))))
            (proof-proof-chain proof swap (list association))))))
    (proof-with-checked-results ((after (h2-calculation-factor-after-p first rest)))
      (if after (library-library-axiom library "COMMUTATIVITY-OF-*" (list first rest)) nil))))

(defun h2-calculation-product-sort (n library result place changed)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h2-calculation-product-sort")
    (proof-with-checked-results ((node (h2-calculation-product-form-at place result)))
      (if (not (proof-is-call node *proof-times*))
          (if changed (h2-calculation-product-sort (1- n) library result '(1 2) nil) result)
        (proof-with-checked-results
         ((call (proof-list-of-length node 3))
          (swap (h2-calculation-product-swap library (cadr call) (caddr call)))
          (result (if swap (proof-proof-rewrite (library-library-proof library) result swap place) result)))
         (h2-calculation-product-sort (1- n) library result (append place '(2)) (if swap t changed)))))))

(defun h2-calculation-product-identity (library first rest context)
  (let* ((proof (library-library-proof library))
         (remaining (if (equal first *proof-one*) rest first)))
    (proof-with-checked-results
     ((identity (library-library-axiom library "UNICITY-OF-1" (list remaining)))
      (identity (if (and (equal rest *proof-one*) (not (equal first *proof-one*)))
                    (proof-with-checked-results
                     ((commute (library-library-axiom library "COMMUTATIVITY-OF-*" (list first *proof-one*))))
                     (proof-proof-chain proof commute (list identity)))
                  identity)))
     (let ((known (h2-calculation-number-sums-type-of
                   (h2-calculation-number-sums-init library) remaining
                   (table-values (h2-search-context-literals context)))))
       (if (h2-calculation-inapplicable-p known)
           identity
         (proof-with-checked-results
          ((known known)
           (fix (library-library-cite library "H2-NUMBER-FIX" (list remaining) (list known))))
          (proof-proof-chain proof identity (list fix))))))))

(defun h2-calculation-request-p (value)
  (and (consp value) (eq (car value) :h2-calculation-request)))

(defun h2-calculation-request-operation (request)
  (cadr request))

(defun h2-calculation-request-proof (request)
  (caddr request))

(defun h2-calculation-request-context (request)
  (cadddr request))

(defun h2-calculation-request-arguments (request)
  (car (cddddr request)))

(defun h2-calculation-search-result (step search context replies)
  (if (failure-p step)
      step
    (cons (cons step (cons search context)) replies)))

(defun h2-calculation-search-reply (search context replies operation arguments)
  (if (endp replies)
      (list :h2-calculation-request operation search context arguments)
    (let ((reply (car replies)))
      (cond
       ((failure-p reply) reply)
       ((failure-p (car reply)) (car reply))
       (t (cons reply (cdr replies)))))))

(defun h2-calculation-product-combined (search context first second replies)
  (cond
   ((equal second (list *h2-calculation-reciprocal* first))
    (proof-with-checked-results
     ((inverse (library-library-axiom (h2-search-search-library search) "INVERSE-OF-*" (list first)))
      (condition (h2-calculation-step-at inverse 1))
      (answer (h2-calculation-search-reply search context replies :deduce (list condition '(nil)))))
     (if (h2-calculation-request-p answer)
         answer
       (let* ((result (car answer))
              (guard (car result))
              (search (cadr result))
              (context (cddr result)))
         (h2-calculation-search-result
          (if guard (proof-proof-modus-ponens (library-library-proof (h2-search-search-library search))
                                             inverse guard) nil)
          search context (cdr answer))))))
   ((and (proof-is-call first *proof-quote*) (proof-is-call second *proof-quote*))
    (h2-calculation-search-reply search context replies :primitive (list (list *proof-times* first second))))
   (t (h2-calculation-search-result nil search context replies))))

(defun h2-calculation-product-rewrite-combined (library result first rest second suffix combined place)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((result (if suffix
                  (proof-with-checked-results
                   ((tail (proof-term-at rest 2))
                    (association (library-library-axiom library "ASSOCIATIVITY-OF-*" (list first second tail)))
                    (reverse (proof-proof-symmetric proof association)))
                   (proof-proof-rewrite proof result reverse place))
                result)))
     (proof-proof-rewrite proof result combined (if suffix (append place '(1)) place)))))

(defun h2-calculation-product-combine (n search context result place replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h2-calculation-product-combine")
    (proof-with-checked-results ((node (h2-calculation-product-form-at place result)))
      (if (not (proof-is-call node *proof-times*))
          (h2-calculation-search-result result search context replies)
        (proof-with-checked-results ((call (proof-list-of-length node 3)))
          (let* ((first (cadr call))
                 (rest (caddr call))
                 (suffix (proof-is-call rest *proof-times*)))
            (proof-with-checked-results ((second (if suffix (proof-term-at rest 1) rest)))
              (if (or (equal first *proof-one*) (equal rest *proof-one*))
                  (let* ((library (h2-search-search-library search))
                         (proof (library-library-proof library)))
                    (proof-with-checked-results
                     ((identity (h2-calculation-product-identity library first rest context))
                      (result (proof-proof-rewrite proof result identity place)))
                     (h2-calculation-product-combine (1- n) search context result place replies)))
                (proof-with-checked-results
                 ((answer (h2-calculation-product-combined search context first second replies)))
                 (if (h2-calculation-request-p answer)
                     answer
                   (let* ((value (car answer))
                          (combined (car value))
                          (search (cadr value))
                          (context (cddr value))
                          (replies (cdr answer)))
                     (if (not combined)
                         (h2-calculation-product-combine (1- n) search context result (append place '(2)) replies)
                       (proof-with-checked-results
                        ((result (h2-calculation-product-rewrite-combined
                                  (h2-search-search-library search) result first rest second suffix combined place)))
                        (h2-calculation-product-combine (1- n) search context result '(1 2) replies))))))))))))))

(defun h2-calculation-product-form-result (search term context replies)
  (let ((library (h2-search-search-library search)))
    (proof-with-checked-results
     ((result (proof-proof-reflexive (library-library-proof library) term))
      (result (h2-calculation-product-reassociate 1000000 library result '(1 2)))
      (result (h2-calculation-product-sort 1000000 library result '(1 2) nil)))
     (h2-calculation-product-combine 1000000 search context result '(1 2) replies))))

(defun h2-calculation-finish-search (answer)
  (if (or (failure-p answer) (h2-calculation-request-p answer)) answer (car answer)))

(defun h2-calculation-product-form-with-replies (search term context replies)
  (h2-calculation-finish-search (h2-calculation-product-form-result search term context replies)))

(defun h2-calculation-number-literals (literals)
  (if (endp literals)
      nil
    (let ((literal (caar literals)))
      (if (or (proof-is-call literal *proof-integerp*)
              (proof-is-call literal *h2-calculation-rationalp*)
              (proof-is-call literal *h2-calculation-numberp*))
          (cons (cdar literals) (h2-calculation-number-literals (cdr literals)))
        (h2-calculation-number-literals (cdr literals))))))

(defun h2-calculation-equal-products (search left right context replies)
  (proof-with-checked-results ((a (h2-calculation-product-form-result search left context replies)))
    (if (h2-calculation-request-p a)
        a
      (let ((left-step (caar a)))
        (proof-with-checked-results ((b (h2-calculation-product-form-result (cadar a) right (cddar a) (cdr a))))
          (if (h2-calculation-request-p b)
              b
            (let* ((right-step (caar b))
                   (search (cadar b))
                   (context (cddar b))
                   (proof (library-library-proof (h2-search-search-library search))))
              (proof-with-checked-results
               ((left-normal (h2-calculation-step-at left-step 2))
                (right-normal (h2-calculation-step-at right-step 2)))
               (h2-calculation-search-result
                (if (equal left-normal right-normal)
                    (proof-with-checked-results ((reverse (proof-proof-symmetric proof right-step)))
                      (proof-proof-chain proof left-step (list reverse)))
                  nil)
                search context (cdr b))))))))))

(defun h2-calculation-calculate-equality (search left right context numbers replies)
  (let ((align (if (or (h2-calculation-sum-p left) (h2-calculation-sum-p right))
                   (h2-calculation-number-sums-linear-equal
                    (h2-calculation-number-sums-init (h2-search-search-library search)) left right numbers)
                 nil)))
    (if (and align (not (h2-calculation-inapplicable-p align)))
        (h2-calculation-search-result align search context replies)
      (if (or (proof-is-call left *proof-times*) (proof-is-call right *proof-times*))
          (h2-calculation-equal-products search left right context replies)
        (h2-calculation-search-result nil search context replies)))))

(defun h2-calculation-comparison (search left right a b align evidence negative)
  (let* ((library (h2-search-search-library search))
         (proof (library-library-proof library)))
    (proof-with-checked-results
     ((comparison (library-library-axiom library "<-ON-OTHERS" (list left right)))
      (comparison (proof-proof-rewrite proof comparison align '(1 2 1)))
      (other (library-library-axiom library "<-ON-OTHERS" (list a b)))
      (other (proof-proof-symmetric proof other))
      (comparison (proof-proof-chain proof comparison (list other))))
     (if negative
         (library-library-transport-argument library evidence comparison 1)
       (proof-proof-transport proof evidence comparison)))))

(defun h2-calculation-align-comparisons (search left right negative literals context numbers replies)
  (declare (xargs :measure (acl2-count literals)))
  (if (endp literals)
      (h2-calculation-search-result nil search context replies)
    (let ((literal (caar literals)) (evidence (cdar literals)))
      (proof-with-checked-results
       ((other (if negative
                   (if (proof-is-call literal *proof-not*) (proof-term-at literal 1) nil)
                 literal)))
       (if (or (not (proof-is-call other *proof-less*)) (> (h2-search-size other) 64))
           (h2-calculation-align-comparisons search left right negative (cdr literals) context numbers replies)
         (proof-with-checked-results
          ((pair (proof-list-of-length (cdr other) 2))
           (spent (h2-calculation-search-reply search context replies :spend nil)))
          (if (h2-calculation-request-p spent)
              spent
            (let* ((search (cadar spent))
                   (context (cddar spent))
                   (replies (cdr spent))
                   (a (car pair))
                   (b (cadr pair))
                   (align (h2-calculation-number-sums-linear-equal
                           (h2-calculation-number-sums-init (h2-search-search-library search))
                           (library-diff left right) (library-diff a b) numbers)))
              (if (h2-calculation-inapplicable-p align)
                  (h2-calculation-align-comparisons search left right negative (cdr literals) context numbers replies)
                (proof-with-checked-results
                 ((align align)
                  (step (h2-calculation-comparison search left right a b align evidence negative)))
                 (h2-calculation-search-result step search context replies)))))))))))

(defun h2-calculation-sum-argument-p (arguments include-fix)
  (and (consp arguments)
       (or (h2-calculation-sum-p (car arguments))
           (and include-fix (proof-is-call (car arguments) *h2-calculation-fix*))
           (h2-calculation-sum-argument-p (cdr arguments) include-fix))))

(defun h2-calculation-calculate-with-replies (search goal context replies)
  (if (> (h2-search-size goal) 64)
      (cons nil (cons search context))
    (let* ((literals (h2-search-context-literals context))
           (numbers (h2-calculation-number-literals literals)))
      (h2-calculation-finish-search
       (if (proof-is-call goal *proof-equal*)
           (proof-with-checked-results ((pair (proof-list-of-length (cdr goal) 2)))
             (h2-calculation-calculate-equality search (car pair) (cadr pair) context numbers replies))
         (let ((negative (proof-is-call goal *proof-not*)))
           (proof-with-checked-results ((test (if negative (proof-term-at goal 1) goal)))
             (if (and (proof-is-call test *proof-less*) (h2-calculation-sum-argument-p (cdr test) nil))
                 (proof-with-checked-results ((pair (proof-list-of-length (cdr test) 2)))
                   (h2-calculation-align-comparisons search (car pair) (cadr pair) negative
                                                     literals context numbers replies))
               (h2-calculation-search-result nil search context replies)))))))))

(defconst *h2-calculation-projection-rules*
  '("SELF-H2-ADD-FIXED-OPERANDS" "SELF-H2-NEGATE-FIXED-OPERAND"))

(defun h2-calculation-projection-operand (proof normalized variable evidence position)
  (proof-with-checked-results
   ((opening (proof-proof-unfold proof (list *h2-calculation-fix* variable)))
    (value (h2-calculation-step-at opening 2))
    (selected (proof-proof-select proof value evidence))
    (opening (proof-proof-chain proof opening (list selected))))
   (proof-proof-rewrite proof normalized opening (list 1 2 position))))

(defun h2-calculation-projected-arithmetic-branch (x-present y-present proof x-number y-number sums completion fixed)
  (proof-with-checked-results
   ((x-test (proof-proof-assume proof x-number x-present))
    (y-test (proof-proof-assume proof y-number y-present))
    (body (h2-calculation-step-at completion 2))
    (selected (proof-proof-select proof body x-test))
    (raw (proof-proof-chain proof completion (list selected)))
    (body (h2-calculation-step-at raw 2))
    (selected (proof-proof-select proof body y-test))
    (raw (proof-proof-chain proof raw (list selected)))
    (normalized (proof-proof-reflexive proof fixed))
    (normalized (h2-calculation-projection-operand proof normalized *library-x* x-test 1))
    (normalized (h2-calculation-projection-operand proof normalized *library-y* y-test 2))
    (normalized
     (cond
      ((not (equal x-present y-present))
       (let ((name (if x-present "ADD-ZERO-RIGHT" "ADD-ZERO-LEFT"))
             (typed (if x-present x-test y-test)))
         (proof-with-checked-results
          ((term (h2-calculation-step-at typed 1))
           (identity (h2-calculation-number-sums-cite sums name (list term) (list typed))))
          (proof-proof-chain proof normalized (list identity)))))
      ((not x-present)
       (proof-with-checked-results ((zero (proof-proof-compute proof (library-plus *proof-zero* *proof-zero*) 0)))
         (proof-proof-chain proof normalized (list zero))))
      (t normalized)))
    (reverse (proof-proof-symmetric proof normalized)))
   (proof-proof-chain proof raw (list reverse))))

(defun h2-calculation-addition-projection (search)
  (let* ((library (h2-search-search-library search))
         (proof (library-library-proof library))
         (x *library-x*)
         (y *library-y*))
    (if (assoc-equal (proof-sym (car *h2-calculation-projection-rules*) "ACL2") (proof-proof-facts proof))
        search
      (let* ((x-number (list *h2-calculation-numberp* x))
             (y-number (list *h2-calculation-numberp* y))
             (sums (h2-calculation-number-sums-init library))
             (fixed (library-plus (list *h2-calculation-fix* x) (list *h2-calculation-fix* y))))
        (proof-with-checked-results
         ((completion (library-library-axiom library "COMPLETION-OF-+" (list x y)))
          (both (h2-calculation-projected-arithmetic-branch t t proof x-number y-number sums completion fixed))
          (left (h2-calculation-projected-arithmetic-branch t nil proof x-number y-number sums completion fixed))
          (yes (proof-proof-cases proof y-number both left))
          (right (h2-calculation-projected-arithmetic-branch nil t proof x-number y-number sums completion fixed))
          (neither (h2-calculation-projected-arithmetic-branch nil nil proof x-number y-number sums completion fixed))
          (no (proof-proof-cases proof y-number right neither))
          (proved (proof-proof-cases proof x-number yes no))
          (library (library-library-lemma library "H2-ADD-FIXED-OPERANDS"
                                          (proof-eq (library-plus x y) fixed) proved nil)))
         (h2-search-search-with-library search library))))))

(defun h2-calculation-projected-arithmetic-result (search replies)
  (let ((prepared (h2-calculation-addition-projection search)))
    (if (failure-p prepared)
        (list prepared search replies)
      (let* ((x *library-x*)
             (negation (proof-eq (library-minus x) (library-minus (list *h2-calculation-fix* x))))
             (auxiliary (h2-alist-recognizers-auxiliary
                         prepared replies "NEGATE-FIXED-OPERAND" negation "FIX"
                         '("SELF-H2-NEGATIVE-NONNUMBER") "" nil
                         (list (list *h2-calculation-numberp* x)) nil)))
        (cond
         ((failure-p auxiliary) (list auxiliary prepared replies))
         ((or (failure-p (car auxiliary))
              (h2-alist-recognizers-request-p (car auxiliary))
              (h2-search-request-p (car auxiliary))) auxiliary)
         (t (cons *h2-calculation-projection-rules* (cdr auxiliary))))))))

(mutual-recursion
 (defun h2-calculation-normalize-total-sum-visit (n library term rules sums)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "h2-calculation-normalize-total-sum-visit")
     (let ((proof (library-library-proof library)))
       (cond
        ((proof-is-call term *h2-calculation-fix*)
         (proof-with-checked-results ((item (proof-term-at term 1)))
           (let ((typed (h2-calculation-number-sums-type-of sums item nil)))
             (if (h2-calculation-inapplicable-p typed)
                 (proof-proof-reflexive proof term)
               (proof-with-checked-results
                ((typed typed)
                 (fixing (library-library-cite library "H2-NUMBER-FIX" (list item) (list typed)))
                 (normalized (h2-calculation-normalize-total-sum-visit (1- n) library item rules sums)))
                (proof-proof-chain proof fixing (list normalized)))))))
        ((h2-calculation-sum-p term)
         (proof-with-checked-results
          ((name (proof-term-at rules (if (proof-is-call term *proof-plus*) 0 1)))
           (step (library-library-axiom library name (cdr term))))
          (h2-calculation-normalize-total-arguments (1- n) library (cdr term) 1 step rules sums)))
        (t (proof-proof-reflexive proof term))))))
 (defun h2-calculation-normalize-total-arguments (n library arguments position step rules sums)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "h2-calculation-normalize-total-arguments")
     (if (endp arguments)
         step
       (proof-with-checked-results
        ((normalized (h2-calculation-normalize-total-sum-visit
                      (1- n) library (list *h2-calculation-fix* (car arguments)) rules sums))
         (step (proof-proof-rewrite (library-library-proof library) step normalized (list 1 2 position))))
        (h2-calculation-normalize-total-arguments (1- n) library (cdr arguments) (1+ position) step rules sums))))))

(defun h2-calculation-normalize-total-sum (library term rules sums)
  (h2-calculation-normalize-total-sum-visit 1000000 library term rules sums))

(defun h2-calculation-total-sum-alignment (library left right rules)
  (let ((sums (h2-calculation-number-sums-init library)))
    (proof-with-checked-results
     ((a (h2-calculation-normalize-total-sum library left rules sums))
      (b (h2-calculation-normalize-total-sum library right rules sums))
      (left (h2-calculation-step-at a 2))
      (right (h2-calculation-step-at b 2))
      (alignment (h2-calculation-number-sums-linear-equal sums left right nil)))
     (list a b alignment))))

(defun h2-calculation-chain-total-sums (library steps)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results ((reverse (proof-proof-symmetric proof (cadr steps))))
      (proof-proof-chain proof (car steps) (list (caddr steps) reverse)))))

(defun h2-calculation-equal-total-sums-result (search left right replies)
  (let* ((sums (h2-calculation-number-sums-init (h2-search-search-library search)))
         (typed (proof-with-checked-results
                 ((left-type (h2-calculation-number-sums-type-of sums left nil))
                  (right-type (h2-calculation-number-sums-type-of sums right nil)))
                 (list left-type right-type))))
    (cond
     ((h2-calculation-inapplicable-p typed) (list nil search replies))
     ((failure-p typed) (list typed search replies))
     (t
      (let* ((result (h2-calculation-projected-arithmetic-result search replies))
             (rules (car result))
             (search (cadr result))
             (replies (caddr result)))
        (cond
         ((h2-calculation-inapplicable-p rules) (list nil search replies))
         ((or (failure-p rules) (h2-alist-recognizers-request-p rules) (h2-search-request-p rules)) result)
         (t
          (let* ((library (h2-search-search-library search))
                 (steps (h2-calculation-total-sum-alignment library left right rules))
                 (step (cond ((h2-calculation-inapplicable-p steps) nil)
                             ((failure-p steps) steps)
                             (t (h2-calculation-chain-total-sums library steps)))))
            (list step search replies)))))))))

(defun h2-calculation-equal-total-sums-with-replies (search left right replies)
  (let ((result (h2-calculation-equal-total-sums-result search left right replies)))
    (if (failure-p (car result))
        (car result)
      (cons (car result) (cadr result)))))

(defun h2-calculation-establish-difference-test (library name)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (y *library-y*)
         (sums (h2-calculation-number-sums-init library)))
    (if (assoc-equal (proof-sym name "ACL2") (proof-proof-facts proof))
        library
      (let* ((x-type (list *h2-calculation-numberp* x))
             (y-type (list *h2-calculation-numberp* y))
             (same (proof-eq x y))
             (delta (library-diff x y))
             (difference (proof-eq delta *proof-zero*)))
        (proof-with-checked-results
         ((x-number (proof-proof-assume proof x-type t))
          (y-number (proof-proof-assume proof y-type t))
          (inverse (library-library-axiom library "INVERSE-OF-+" (list x)))
          (assumed (proof-proof-assume proof same t))
          (forward (proof-proof-rewrite proof inverse assumed '(1 1 2 1)))
          (backward (h2-calculation-number-sums-linear-equal sums (library-plus delta y) x (list x-number y-number)))
          (assumed (proof-proof-assume proof difference t))
          (backward (proof-proof-rewrite proof backward assumed '(1 1 1)))
          (zero (h2-calculation-number-sums-cite sums "ADD-ZERO-LEFT" (list y) (list y-number)))
          (zero (proof-proof-symmetric proof zero))
          (backward (proof-proof-chain proof zero (list backward)))
          (backward (proof-proof-symmetric proof backward))
          (step (h2-ordering-equal-tests library same difference forward backward))
          (claim (proof-step-first step)))
         (library-library-lemma library "H2-EQUALITY-BY-DIFFERENCE" claim step
                                (list (proof-neg x-type) (proof-neg y-type))))))))

(defun h2-calculation-difference-test-result (library equality)
  (let ((prepared (h2-calculation-establish-difference-test library "SELF-H2-EQUALITY-BY-DIFFERENCE")))
    (if (failure-p prepared)
        (cons prepared library)
      (cons (proof-with-checked-results
             ((types (h2-calculation-number-types (h2-calculation-number-sums-init prepared) (cdr equality) nil)))
             (library-library-cite prepared "H2-EQUALITY-BY-DIFFERENCE" (cdr equality) types))
            prepared))))

(defun h2-calculation-test-orientation (search reverse right result)
  (let* ((library (h2-search-search-library search))
         (proof (library-library-proof library)))
    (proof-with-checked-results
     ((assumed (proof-proof-assume proof reverse t))
      (forward (proof-proof-symmetric proof assumed))
      (assumed (proof-proof-assume proof right t))
      (backward (proof-proof-symmetric proof assumed))
      (orientation (h2-ordering-equal-tests search reverse right forward backward)))
     (proof-proof-chain proof result (list orientation)))))

(defun h2-calculation-align-equality-tests (search first targets right reverse replies)
  (declare (xargs :measure (acl2-count targets)))
  (if (endp targets)
      (cons nil search)
    (let ((other (caar targets))
          (mirrored (cadar targets)))
      (proof-with-checked-results
       ((first-test (h2-calculation-step-at first 2))
        (first-difference (proof-term-at first-test 1))
        (other-test (h2-calculation-step-at other 2))
        (other-difference (proof-term-at other-test 1)))
       (let* ((answer (h2-calculation-equal-total-sums-result search first-difference other-difference replies))
              (align (car answer))
              (search (cadr answer))
              (replies (caddr answer)))
         (cond
          ((failure-p align) align)
          ((or (h2-alist-recognizers-request-p align) (h2-search-request-p align)) (cons align search))
          ((not align) (h2-calculation-align-equality-tests search first (cdr targets) right reverse replies))
          (t
           (let ((proof (library-library-proof (h2-search-search-library search))))
             (proof-with-checked-results
              ((aligned (proof-proof-rewrite proof first align '(1 2 1)))
               (reverse-other (proof-proof-symmetric proof other))
               (result (proof-proof-chain proof aligned (list reverse-other)))
               (result (if mirrored (h2-calculation-test-orientation search reverse right result) result)))
              (cons result search))))))))))

(defun h2-calculation-signed-identity-differences (search left right replies)
  (let* ((library (h2-search-search-library search))
         (answer (h2-calculation-difference-test-result library left))
         (first (car answer))
         (search (h2-search-search-with-library search (cdr answer))))
    (cond
     ((h2-calculation-inapplicable-p first) (cons nil search))
     ((failure-p first) first)
     (t
      (let* ((answer (h2-calculation-difference-test-result (cdr answer) right))
             (direct (car answer))
             (search (h2-search-search-with-library search (cdr answer))))
        (cond
         ((h2-calculation-inapplicable-p direct) (cons nil search))
         ((failure-p direct) direct)
         (t
          (proof-with-checked-results
           ((b (proof-term-at right 2))
            (a (proof-term-at right 1)))
           (let* ((reverse (proof-eq b a))
                  (answer (h2-calculation-difference-test-result (cdr answer) reverse))
                  (mirrored (car answer))
                  (search (h2-search-search-with-library search (cdr answer))))
             (cond
              ((h2-calculation-inapplicable-p mirrored) (cons nil search))
              ((failure-p mirrored) mirrored)
              (t (h2-calculation-align-equality-tests search first (list (list direct nil) (list mirrored t))
                                                      right reverse replies))))))))))))

(defun h2-calculation-signed-identity-with-replies (search formula replies)
  (if (or (not (proof-is-call formula *proof-equal*)) (> (h2-search-size formula) 64))
      (cons nil search)
    (proof-with-checked-results ((pair (proof-list-of-length (cdr formula) 2)))
      (let ((left (car pair)) (right (cadr pair)))
        (cond
         ((h2-calculation-sum-argument-p pair t)
          (h2-calculation-equal-total-sums-with-replies search left right replies))
         ((and (proof-is-call left *proof-equal*) (proof-is-call right *proof-equal*)
               (h2-calculation-sum-argument-p (append (cdr left) (cdr right)) t))
          (h2-calculation-signed-identity-differences search left right replies))
         (t (cons nil search)))))))

