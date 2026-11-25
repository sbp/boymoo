(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-reciprocal-minus-zero* (proof-sym "EQUAL-MINUS-0" "ACL2"))
(defconst *b2-reciprocal-invert-twice*
  (proof-sym "FUNCTIONAL-SELF-INVERSION-OF-/" "ACL2"))
(defconst *b2-reciprocal-invert-product*
  (proof-sym "DISTRIBUTIVITY-OF-/-OVER-*" "ACL2"))
(defconst *b2-reciprocal-invert-minus* (proof-sym "RECIPROCAL-MINUS" "ACL2"))
(defconst *b2-reciprocal-cancel-right*
  (proof-sym "/-CANCELLATION-ON-RIGHT" "ACL2"))
(defconst *b2-reciprocal-cancel-left*
  (proof-sym "/-CANCELLATION-ON-LEFT" "ACL2"))
(defconst *b2-reciprocal-zero-product*
  (proof-sym "ZERO-IS-ONLY-ZERO-DIVISOR" "ACL2"))
(defconst *b2-reciprocal-product-x* (proof-sym "EQUAL-*-X-Y-X" "ACL2"))
(defconst *b2-reciprocal-product-y* (proof-sym "EQUAL-*-X-Y-Y" "ACL2"))
(defconst *b2-reciprocal-inverse-equal* (proof-sym "EQUAL-/" "ACL2"))
(defconst *b2-reciprocal-numerator-nonzero*
  (proof-sym "NUMERATOR-NONZERO-FORWARD" "ACL2"))
(defconst *b2-reciprocal-injective* (proof-sym "EQUAL-/-/" "ACL2"))
(defconst *b2-reciprocal-ratio-unit* (proof-sym "/R-WHEN-ABS-NUMERATOR=1" "ACL2"))
(defconst *b2-reciprocal-move-left* (proof-sym "EQUAL-*-/-1" "ACL2"))
(defconst *b2-reciprocal-move-right* (proof-sym "EQUAL-*-/-2" "ACL2"))

(defconst *b2-reciprocal-reciprocal-theorems*
  (list *b2-reciprocal-cancel-left* *b2-reciprocal-cancel-right*
        *b2-reciprocal-ratio-unit* *b2-reciprocal-invert-product*
        *b2-reciprocal-move-left* *b2-reciprocal-move-right*
        *b2-reciprocal-product-x* *b2-reciprocal-product-y*
        *b2-reciprocal-inverse-equal* *b2-reciprocal-injective*
        *b2-reciprocal-minus-zero* *b2-reciprocal-invert-twice*
        *b2-reciprocal-numerator-nonzero* *b2-reciprocal-invert-minus*
        *b2-reciprocal-zero-product*))

; A binding marked :library also binds the Library returned by its recipe.
(defmacro b2-reciprocal-results (lib bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding)))
      (if (eq (caddr binding) :library)
          `(proof-with-checked-results ((b2-reciprocal-pair ,form))
             (let ((,name (car b2-reciprocal-pair))
                   (,lib (cdr b2-reciprocal-pair)))
               (declare (ignorable ,name ,lib))
               (b2-reciprocal-results ,lib ,(cdr bindings) ,result)))
        `(proof-with-checked-results ((,name ,form))
           (b2-reciprocal-results ,lib ,(cdr bindings) ,result))))))

(defmacro b2-reciprocal-return (lib form)
  `(proof-with-checked-results ((b2-reciprocal-value ,form))
     (cons b2-reciprocal-value ,lib)))

(defmacro b2-reciprocal-normalize (lib term &optional evidence unfold rules)
  `(b2-tactics-tactics-normalize ,lib ,term ,evidence ,unfold ,rules 1500 nil))

(defmacro b2-reciprocal-solve (lib term &optional evidence unfold rules branches)
  `(b2-tactics-tactics-solve ,lib ,term ,evidence ,unfold ,rules 0 ,branches))

(defmacro b2-reciprocal-impossible (lib goal premise &optional evidence unfold rules)
  `(b2-tactics-tactics-from-impossible ,lib ,goal ,premise
                                     ,evidence ,unfold ,rules 1500 nil))

(defmacro b2-reciprocal-rewrite (lib step equation &optional (place ''(1)))
  `(proof-proof-rewrite (library-library-proof ,lib) ,step ,equation ,place))

(defmacro b2-reciprocal-tidy (lib step)
  `(proof-proof-tidy (library-library-proof ,lib) ,step))

(defmacro b2-reciprocal-symmetric (lib step)
  `(proof-proof-symmetric (library-library-proof ,lib) ,step))

(defmacro b2-reciprocal-chain (lib first &rest rest)
  `(proof-proof-chain (library-library-proof ,lib) ,first (list ,@rest)))

(defmacro b2-reciprocal-assume (lib term &optional (holds 't))
  `(proof-proof-assume (library-library-proof ,lib) ,term ,holds))

(defmacro b2-reciprocal-axiom (lib name &rest terms)
  `(library-library-axiom ,lib ,name (list ,@terms)))

(defun b2-reciprocal-evidence-at (known term)
  (let ((entry (assoc-equal term known)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defmacro b2-reciprocal-choose (lib test evidence sign facts branch)
  `(proof-with-checked-results
       ((b2-reciprocal-case-test ,test)
        (b2-reciprocal-case-evidence ,evidence)
        (b2-reciprocal-case-first
         (b2-tactics-choose ,lib b2-reciprocal-case-test
                           b2-reciprocal-case-evidence nil))
        (b2-reciprocal-case-yes
         (let ((,lib (cdr b2-reciprocal-case-first))
               (,sign (nth 3 (car b2-reciprocal-case-first)))
               (,facts (nth 4 (car b2-reciprocal-case-first))))
           (declare (ignorable ,lib ,sign ,facts))
           ,branch))
        (b2-reciprocal-case-next
         (b2-tactics-choose ,lib b2-reciprocal-case-test
                           b2-reciprocal-case-evidence
                           (list b2-reciprocal-case-yes))))
     (if (eq (caar b2-reciprocal-case-next) :call)
         (proof-with-checked-results
             ((b2-reciprocal-case-no
               (let ((,lib (cdr b2-reciprocal-case-next))
                     (,sign (nth 3 (car b2-reciprocal-case-next)))
                     (,facts (nth 4 (car b2-reciprocal-case-next))))
                 (declare (ignorable ,lib ,sign ,facts))
                 ,branch)))
           (b2-tactics-choose ,lib b2-reciprocal-case-test
                             b2-reciprocal-case-evidence
                             (list b2-reciprocal-case-yes b2-reciprocal-case-no)))
       b2-reciprocal-case-next)))

(defmacro b2-reciprocal-imply (lib antecedent consequent premise branch)
  `(proof-with-checked-results
       ((b2-reciprocal-antecedent ,antecedent)
        (b2-reciprocal-consequent ,consequent)
        (,premise (b2-reciprocal-assume ,lib b2-reciprocal-antecedent))
        (b2-reciprocal-implication-reply ,branch))
     (b2-tactics-tactics-implication ,lib b2-reciprocal-antecedent
                                    b2-reciprocal-consequent
                                    b2-reciprocal-implication-reply)))

(defmacro b2-reciprocal-equivalence (lib left right assumption forward backward)
  `(b2-reciprocal-results ,lib
       ((b2-reciprocal-left ,left)
        (b2-reciprocal-right ,right)
        (b2-reciprocal-yes (b2-reciprocal-assume ,lib b2-reciprocal-left))
        (b2-reciprocal-no (b2-reciprocal-assume ,lib b2-reciprocal-left nil))
        (b2-reciprocal-forward
         (let ((,assumption b2-reciprocal-yes)) ,forward) :library)
        (b2-reciprocal-positive
         (b2-algebra-boolean-equivalence-positive
          ,lib (proof-eq b2-reciprocal-left b2-reciprocal-right)
          b2-reciprocal-yes b2-reciprocal-forward))
        (b2-reciprocal-right-yes (b2-reciprocal-assume ,lib b2-reciprocal-right))
        (b2-reciprocal-backward
         (let ((,assumption b2-reciprocal-right-yes)) ,backward) :library))
     (b2-reciprocal-return ,lib
       (b2-algebra-boolean-equivalence-negative
        ,lib b2-reciprocal-left b2-reciprocal-right b2-reciprocal-no
        b2-reciprocal-positive b2-reciprocal-backward))))

(defun b2-reciprocal-equal-swap (lib a b)
  (proof-with-checked-results
      ((result
        (b2-reciprocal-equivalence lib (proof-eq a b) (proof-eq b a) same
          (b2-reciprocal-return lib (b2-reciprocal-symmetric lib same))
          (b2-reciprocal-return lib (b2-reciprocal-symmetric lib same)))))
    (car result)))

(defmacro b2-reciprocal-nonzero-cases (lib value evidence active facts branch)
  `(b2-reciprocal-choose ,lib (list *library-numberp* ,value)
                         ,evidence b2-reciprocal-numeric ,facts
     (if b2-reciprocal-numeric
         (b2-reciprocal-choose ,lib (proof-eq ,value *proof-zero*)
                                ,facts b2-reciprocal-zero ,facts
           (let ((,active (not b2-reciprocal-zero)))
             (declare (ignorable ,active))
             ,branch))
       (let ((,active nil))
         (declare (ignorable ,active))
         ,branch))))

(defun b2-reciprocal-invert-unit (lib unit typed)
  (b2-reciprocal-results lib
      ((equation (proof-step-first unit))
       (equation (proof-list-of-length equation 3))
       (product (proof-list-of-length (cadr equation) 3))
       (zero (proof-eq (cadr product) *proof-zero*))
       (same (b2-reciprocal-assume lib zero))
       (conflict (b2-reciprocal-rewrite lib unit same '(1 1 1)))
       (rule (b2-products-zero-left-product lib (caddr product)) :library)
       (conflict (b2-reciprocal-rewrite lib conflict rule '(1 1)))
       (computed (proof-proof-compute (library-library-proof lib)
                                      (proof-eq *proof-zero* *proof-one*) *proof-nil*))
       (conflict (b2-reciprocal-rewrite lib conflict computed))
       (conflict (b2-reciprocal-tidy lib conflict))
       (nonzero (proof-proof-front (library-library-proof lib) conflict (proof-neg zero)))
       (inverse (b2-products-inverse-from-product lib unit typed nonzero)))
    (b2-reciprocal-return lib (b2-reciprocal-symmetric lib inverse))))

(defun b2-reciprocal-invert-involutively-prove (nonzero facts lib goal left fixed value inv)
  (if (not nonzero)
      (b2-reciprocal-results lib
          ((opening (b2-quotient-algebra-completed-product lib left facts) :library))
        (b2-reciprocal-return lib
          (b2-reciprocal-solve lib goal facts (list fixed) (list opening))))
    (b2-reciprocal-results lib
        ((known (b2-tactics-tactics-evidence lib facts))
         (typed (b2-reciprocal-evidence-at known (list *library-numberp* value)))
         (different (b2-quotient-algebra-require-nonzero lib value known))
         (unit (b2-products-reciprocal-identity lib value typed different))
         (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" inv value))
         (reverse (b2-reciprocal-chain lib commute unit))
         (closed (b2-products-numeric-closure lib inv))
         (inverted (b2-reciprocal-invert-unit lib reverse closed) :library))
      (b2-reciprocal-return lib
        (b2-reciprocal-solve lib goal facts (list fixed) (list inverted))))))

(defun b2-reciprocal-invert-involutively (lib goal)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (value (proof-term-at (caddr parts) 1)))
    (let ((inv (list *b2-products-recip* value)))
      (b2-reciprocal-nonzero-cases lib value nil nonzero facts
        (b2-reciprocal-invert-involutively-prove
         nonzero facts lib goal (cadr parts) (caddr parts) value inv)))))

(defun b2-reciprocal-invert-factors-first-last (active-b both lib active-a left right a b)
  (if (not (and active-a active-b))
      (b2-reciprocal-results lib
          ((left-eq (b2-quotient-algebra-completed-product lib left both) :library)
           (right-eq (b2-quotient-algebra-completed-product lib right both) :library)
           (right-back (b2-reciprocal-symmetric lib right-eq)))
        (b2-reciprocal-return lib (b2-reciprocal-chain lib left-eq right-back)))
    (b2-reciprocal-results lib
        ((known (b2-tactics-tactics-evidence lib both))
         (type-a (b2-reciprocal-evidence-at known (list *library-numberp* a)))
         (nz-a (b2-quotient-algebra-require-nonzero lib a known))
         (au (b2-products-reciprocal-identity lib a type-a nz-a))
         (type-b (b2-reciprocal-evidence-at known (list *library-numberp* b)))
         (nz-b (b2-quotient-algebra-require-nonzero lib b known))
         (bu (b2-products-reciprocal-identity lib b type-b nz-b)))
      (b2-quotient-algebra-reciprocal-of-pair
       lib a b (list *b2-products-recip* a) (list *b2-products-recip* b) au bu))))

(defun b2-reciprocal-invert-factors-first (active-a facts lib left right a b)
  (b2-reciprocal-nonzero-cases lib b facts active-b both
    (b2-reciprocal-invert-factors-first-last active-b both lib active-a left right a b)))

(defun b2-reciprocal-invert-factors (lib goal)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (inner (proof-term-at (cadr parts) 1))
       (product (proof-list-of-length inner 3)))
    (let ((a (cadr product)) (b (caddr product)))
      (b2-reciprocal-nonzero-cases lib a nil active-a facts
        (b2-reciprocal-invert-factors-first
         active-a facts lib (cadr parts) (caddr parts) a b)))))

(defun b2-reciprocal-invert-negation-prove (nonzero facts lib goal value inverse)
  (if (not nonzero)
      (b2-reciprocal-results lib
          ((opened (b2-quotient-algebra-completed-product lib inverse facts) :library)
           (minus-law (b2-reciprocal-axiom lib "COMPLETION-OF-UNARY-MINUS" value))
           (equation (proof-step-first minus-law))
           (normal (b2-reciprocal-normalize lib (caddr equation) facts))
           (recovery (b2-reciprocal-chain lib minus-law normal)))
        (b2-reciprocal-return lib
          (b2-reciprocal-solve lib goal facts nil (list opened recovery))))
    (b2-reciprocal-results lib
        ((known (b2-tactics-tactics-evidence lib facts))
         (typed (b2-reciprocal-evidence-at known (list *library-numberp* value)))
         (different (b2-quotient-algebra-require-nonzero lib value known))
         (unit (b2-products-reciprocal-identity lib value typed different))
         (both (b2-fraction-reduction-negative-first lib value (library-minus inverse)) :library)
         (negative (b2-fraction-reduction-negative-factor lib value inverse) :library)
         (both (b2-reciprocal-rewrite lib both negative '(1 2 1)))
         (reduced (b2-reciprocal-rewrite lib both unit '(1 2 1 1)))
         (reduced (b2-reciprocal-tidy lib reduced))
         (equation (proof-step-first reduced))
         (normal (b2-reciprocal-normalize lib (caddr equation)))
         (reduced (b2-reciprocal-chain lib reduced normal))
         (closed (b2-products-numeric-closure lib (library-minus value))))
      (b2-reciprocal-invert-unit lib reduced closed))))

(defun b2-reciprocal-invert-negation (lib goal)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (minus (proof-term-at (cadr parts) 1))
       (value (proof-term-at minus 1)))
    (let ((inverse (list *b2-products-recip* value)))
      (b2-reciprocal-nonzero-cases lib value nil nonzero facts
        (b2-reciprocal-invert-negation-prove nonzero facts lib goal value inverse)))))

(defun b2-reciprocal-remove-reciprocals-prove (premise lib a b c y inv right)
  (b2-reciprocal-results lib
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (typed (b2-reciprocal-evidence-at known (list *library-numberp* a)))
       (different (b2-quotient-algebra-require-nonzero lib a known))
       (unit (b2-products-reciprocal-identity lib a typed different))
       (opened
        (if right
            (b2-reciprocal-results lib
                ((opened (b2-products-product-swap lib a y inv))
                 (opened (b2-reciprocal-rewrite lib opened unit '(1 2 2)))
                 (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" y *proof-one*)))
              (b2-reciprocal-chain lib opened commute))
          (b2-reciprocal-results lib
              ((assoc (b2-reciprocal-axiom lib "ASSOCIATIVITY-OF-*" a b c))
               (opened (b2-reciprocal-symmetric lib assoc)))
            (b2-reciprocal-rewrite lib opened unit '(1 2 1)))))
       (unit-y (b2-reciprocal-axiom lib "UNICITY-OF-1" y)))
    (b2-reciprocal-return lib (b2-reciprocal-chain lib opened unit-y))))

(defun b2-reciprocal-remove-reciprocals (lib formula right)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length formula 3))
       (result (proof-list-of-length (caddr parts) 3))
       (fixed (proof-list-of-length (caddr result) 2))
       (product (proof-list-of-length (cadr result) 3))
       (inner (proof-list-of-length (caddr product) 3)))
    (let* ((a (cadr product))
           (inv (list *b2-products-recip* a)))
      (proof-with-checked-results
          ((proved
            (b2-reciprocal-imply lib (cadr parts) result premise
              (b2-reciprocal-remove-reciprocals-prove
               premise lib a (cadr inner) (caddr inner) (cadr fixed) inv right))))
        (car proved)))))

(defun b2-reciprocal-boolean-zero-product (lib goal)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length goal 3))
       (test (proof-list-of-length (cadr parts) 3))
       (product (proof-list-of-length (cadr test) 3)))
    (let* ((a (cadr product)) (b (caddr product))
           (fixed-a (list *b2-products-fix* a))
           (fixed-b (list *b2-products-fix* b)))
      (b2-reciprocal-results lib
          ((law (b2-algebra-product-zero-test lib a b) :library)
           (swapped (b2-reciprocal-equal-swap lib *proof-zero* (b2-products-product a b)))
           (law (b2-reciprocal-rewrite lib law swapped '(1 1)))
           (swapped (b2-reciprocal-equal-swap lib *proof-zero* fixed-a))
           (law (b2-reciprocal-rewrite lib law swapped '(1 2 1)))
           (swapped (b2-reciprocal-equal-swap lib *proof-zero* fixed-b))
           (law (b2-reciprocal-rewrite lib law swapped '(1 2 3)))
           (law (b2-reciprocal-tidy lib law)))
        (b2-reciprocal-choose lib (proof-eq fixed-a *proof-zero*) nil yes facts
          (b2-reciprocal-return lib (b2-reciprocal-solve lib goal facts nil (list law))))))))

(defun b2-reciprocal-product-same-zero-numeric-forward (equality lib commute factored inverse-unit other)
  (b2-reciprocal-results lib
      ((equality (if commute (b2-reciprocal-rewrite lib equality commute '(1 1)) equality))
       (rendered (proof-step-first factored))
       (same (b2-algebra-congruence lib equality (cadr rendered) '(2)))
       (back (b2-reciprocal-symmetric lib factored))
       (reduced (b2-reciprocal-chain lib back same inverse-unit))
       (number (b2-reciprocal-impossible lib (list *library-numberp* other) reduced
                                        nil (list *b2-products-fix*)))
       (fixed (b2-reciprocal-normalize lib (list *b2-products-fix* other)
                                       (list number) (list *b2-products-fix*)))
       (answer (b2-reciprocal-rewrite lib reduced fixed '(1 1))))
    (b2-reciprocal-return lib (b2-reciprocal-tidy lib answer))))

(defun b2-reciprocal-product-same-zero-numeric-backward (equality lib commute result other numbers)
  (b2-reciprocal-results lib
      ((proof (b2-algebra-congruence lib equality (b2-products-product result other) '(2)))
       (swapped (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" result *proof-one*))
       (unit (b2-products-multiplicative-unit lib result numbers))
       (proof (b2-reciprocal-chain lib proof swapped unit)))
    (b2-reciprocal-return lib (if commute (b2-reciprocal-chain lib commute proof) proof))))

(defun b2-reciprocal-product-same-zero-numeric
    (yes states lib goal actual left right result other compare-second facts)
  (if (not yes)
      (b2-reciprocal-results lib
          ((eq-product (b2-reciprocal-assume lib actual))
           (closed (b2-products-numeric-closure lib (cadr actual)))
           (outside (b2-reciprocal-rewrite lib closed eq-product '(1 1)))
           (outside (b2-reciprocal-tidy lib outside))
           (conflict (proof-proof-cut (library-library-proof lib) outside (car (last states))))
           (denied (proof-proof-front (library-library-proof lib) conflict (proof-neg actual))))
        (b2-reciprocal-choose lib (proof-eq other *proof-one*) (append states (list denied))
                               holds case-facts
          (b2-reciprocal-return lib (b2-reciprocal-solve lib goal case-facts))))
    (let ((numbers (car (last states)))
          (inverse (list *b2-products-recip* result))
          (same (proof-eq other *proof-one*)))
      (b2-reciprocal-results lib
          ((unit (b2-products-reciprocal-identity lib result numbers (car (last facts))))
           (swap (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" inverse result))
           (inverse-unit (b2-reciprocal-chain lib swap unit))
           (commute (if compare-second (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" left right) nil))
           (assoc (b2-reciprocal-axiom lib "ASSOCIATIVITY-OF-*" inverse result other))
           (back (b2-reciprocal-symmetric lib assoc))
           (factored (b2-reciprocal-chain lib back))
           (factored (b2-reciprocal-rewrite lib factored inverse-unit '(1 2 1)))
           (unit-other (b2-reciprocal-axiom lib "UNICITY-OF-1" other))
           (factored (b2-reciprocal-chain lib factored unit-other))
           (equivalent
            (b2-reciprocal-equivalence lib actual same equality
              (b2-reciprocal-product-same-zero-numeric-forward
               equality lib commute factored inverse-unit other)
              (b2-reciprocal-product-same-zero-numeric-backward
               equality lib commute result other numbers)) :library))
        (b2-reciprocal-choose lib same states holds options
          (b2-reciprocal-return lib (b2-reciprocal-solve lib goal options nil (list equivalent))))))))

(defun b2-reciprocal-product-same-zero
    (is-zero facts lib goal actual left right result other compare-second)
  (if is-zero
      (b2-reciprocal-results lib
          ((rule (if compare-second
                     (b2-products-zero-product lib other)
                   (b2-products-zero-left-product lib other)) :library))
        (b2-reciprocal-return lib (b2-reciprocal-solve lib goal facts nil (list rule))))
    (b2-reciprocal-choose lib (list *library-numberp* result) facts yes states
      (b2-reciprocal-product-same-zero-numeric
       yes states lib goal actual left right result other compare-second facts))))

(defun b2-reciprocal-product-same (lib goal compare-second)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length goal 3))
       (actual (proof-list-of-length (cadr parts) 3))
       (product (proof-list-of-length (cadr actual) 3)))
    (let* ((left (cadr product)) (right (caddr product))
           (result (caddr actual))
           (other (if compare-second left right))
           (tested (proof-eq result *proof-zero*)))
      (b2-reciprocal-choose lib tested nil is-zero facts
        (b2-reciprocal-product-same-zero
         is-zero facts lib goal actual left right result other compare-second)))))

(defun b2-reciprocal-inverse-equality-establish-forward (equality lib unit)
  (b2-reciprocal-results lib
      ((changed (b2-reciprocal-rewrite lib unit equality '(1 1 2)))
       (changed (b2-reciprocal-tidy lib changed)))
    (b2-reciprocal-return lib (b2-reciprocal-symmetric lib changed))))

(defun b2-reciprocal-inverse-equality-establish-backward (equality lib typed nonzero)
  (b2-reciprocal-results lib
      ((reverse (b2-reciprocal-symmetric lib equality))
       (inverse (b2-products-inverse-from-product lib reverse typed nonzero)))
    (b2-reciprocal-return lib (b2-reciprocal-symmetric lib inverse))))

(defun b2-reciprocal-inverse-equality-establish (premise lib a inv b right)
  (b2-reciprocal-results lib
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (typed (b2-reciprocal-evidence-at known (list *library-numberp* a)))
       (nonzero (b2-quotient-algebra-require-nonzero lib a known))
       (unit (b2-products-reciprocal-identity lib a typed nonzero)))
    (b2-reciprocal-equivalence lib (proof-eq inv b) right equality
      (b2-reciprocal-inverse-equality-establish-forward equality lib unit)
      (b2-reciprocal-inverse-equality-establish-backward equality lib typed nonzero))))

(defun b2-reciprocal-inverse-equality (lib formula)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length formula 3))
       (goal (proof-list-of-length (caddr parts) 3))
       (left (proof-list-of-length (cadr goal) 3))
       (a (proof-term-at (cadr left) 1))
       (result
        (b2-reciprocal-imply lib (cadr parts) goal premise
          (b2-reciprocal-inverse-equality-establish
           premise lib a (cadr left) (caddr left) (caddr goal)))))
    (car result)))

(defun b2-reciprocal-rational-numerator (lib term premise)
  (b2-reciprocal-results lib
      ((completion (b2-reciprocal-axiom lib "COMPLETION-OF-NUMERATOR" term)))
    (b2-reciprocal-impossible lib (list *library-rationalp* term) premise
                              nil nil (list completion))))

(defun b2-reciprocal-numerator-forward-prove (premise lib term goal)
  (b2-reciprocal-results lib
      ((typed (b2-reciprocal-rational-numerator lib term premise))
       (nonzero (b2-reciprocal-impossible lib (proof-neg (proof-eq term *proof-zero*)) premise))
       (numeric (b2-scaling-number-of-rational lib term typed)))
    (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (list numeric nonzero)))))

(defun b2-reciprocal-numerator-forward (lib formula)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (inner (proof-term-at condition 1))
       (numerator (proof-term-at inner 1))
       (term (proof-term-at numerator 1))
       (result
        (b2-reciprocal-imply lib condition goal premise
          (b2-reciprocal-numerator-forward-prove premise lib term goal))))
    (car result)))

(defun b2-reciprocal-reciprocal-injective-forward (equality lib a b)
  (b2-reciprocal-results lib
      ((inverse-a (list *b2-products-recip* (list *b2-products-recip* a)))
       (inverse-b (list *b2-products-recip* (list *b2-products-recip* b)))
       (hold (b2-algebra-congruence lib equality inverse-a '(1)))
       (exact (b2-tactics-tactics-use-fact
               lib *b2-reciprocal-invert-twice*
               (proof-eq inverse-a (list *b2-products-fix* a)) nil nil nil 0 nil))
       (hold (b2-reciprocal-rewrite lib hold exact '(1 1)))
       (exact (b2-tactics-tactics-use-fact
               lib *b2-reciprocal-invert-twice*
               (proof-eq inverse-b (list *b2-products-fix* b)) nil nil nil 0 nil))
       (hold (b2-reciprocal-rewrite lib hold exact '(1 2))))
    (b2-reciprocal-return lib (b2-reciprocal-tidy lib hold))))

(defun b2-reciprocal-reciprocal-injective-retains (term lib)
  (let* ((fixed (list *b2-products-fix* term))
         (inverse (list *b2-products-recip* term))
         (target-eq (proof-eq inverse (list *b2-products-recip* fixed))))
    (b2-reciprocal-choose lib (list *library-numberp* term) nil yes facts
      (if yes
          (b2-reciprocal-return lib (b2-reciprocal-solve lib target-eq facts (list fixed)))
        (b2-reciprocal-results lib
            ((completed (b2-quotient-algebra-completed-product lib inverse facts) :library))
          (b2-reciprocal-return lib
            (b2-reciprocal-solve lib target-eq facts (list fixed) (list completed))))))))

(defun b2-reciprocal-reciprocal-injective-backward (equality lib a b)
  (b2-reciprocal-results lib
      ((left-fixed (b2-reciprocal-reciprocal-injective-retains a lib) :library)
       (right-fixed (b2-reciprocal-reciprocal-injective-retains b lib) :library)
       (equation (proof-step-first left-fixed))
       (changed (b2-algebra-congruence lib equality (caddr equation) '(1)))
       (back (b2-reciprocal-symmetric lib right-fixed)))
    (b2-reciprocal-return lib (b2-reciprocal-chain lib left-fixed changed back))))

(defun b2-reciprocal-reciprocal-injective (lib goal)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length goal 3))
       (left (proof-list-of-length (cadr parts) 3))
       (a (proof-term-at (cadr left) 1))
       (b (proof-term-at (caddr left) 1)))
    (b2-reciprocal-equivalence lib left (caddr parts) equality
      (b2-reciprocal-reciprocal-injective-forward equality lib a b)
      (b2-reciprocal-reciprocal-injective-backward equality lib a b))))

(defun b2-reciprocal-reciprocal-numerator-prove (premise lib value index)
  (b2-reciprocal-results lib
      ((rational (b2-reciprocal-rational-numerator lib value premise))
       (factored (b2-products-rational-product lib value rational) :library)
       (unit (b2-reciprocal-rewrite lib factored premise '(1 2)))
       (unit (b2-reciprocal-tidy lib unit))
       (negative-unit
        (if (zp index)
            (cons unit lib)
          (b2-reciprocal-results lib
              ((sign (b2-fraction-reduction-negative-factor
                      lib value (list *b2-products-den* value)) :library)
               (sign (b2-reciprocal-rewrite lib sign unit '(1 2 1)))
               (equation (proof-step-first premise))
               (computed (proof-proof-compute (library-library-proof lib)
                                              (library-minus (caddr equation)) 1)))
            (b2-reciprocal-return lib (b2-reciprocal-chain lib sign computed)))) :library)
       (typed (b2-scaling-number-of-rational lib value rational)))
    (b2-reciprocal-invert-unit lib negative-unit typed)))

(defun b2-reciprocal-reciprocal-numerator-parts (lib parts index)
  (declare (xargs :measure (acl2-count parts)))
  (if (endp parts)
      (cons nil lib)
    (b2-reciprocal-results lib
        ((part (proof-list-of-length (car parts) 3))
         (condition (cadr part))
         (numerator (proof-term-at condition 1))
         (value (proof-term-at numerator 1))
         (proof (b2-reciprocal-imply lib condition (caddr part) premise
                  (b2-reciprocal-reciprocal-numerator-prove premise lib value index)) :library)
         (tail (b2-reciprocal-reciprocal-numerator-parts lib (cdr parts) (1+ index)) :library))
      (cons (cons proof tail) lib))))

(defun b2-reciprocal-reciprocal-numerator (lib formula)
  (if (integerp formula)
      '(:failure "tactic-rejected" "")
    (b2-reciprocal-results lib
        ((proofs (b2-reciprocal-reciprocal-numerator-parts lib (seq-slice formula 1 3) 0) :library))
      (b2-reciprocal-return lib (b2-reciprocal-solve lib formula proofs)))))

(defun b2-reciprocal-move-divisor-establish-by-output-forward
    (equality lib cancel x value z reverse)
  (b2-reciprocal-results lib
      ((lifted (b2-algebra-congruence lib equality (b2-products-product x value) '(2)))
       (back (b2-reciprocal-symmetric lib cancel))
       (answer (b2-reciprocal-chain lib back lifted)))
    (if reverse
        (b2-reciprocal-results lib
            ((commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" x z)))
          (b2-reciprocal-return lib (b2-reciprocal-chain lib answer commute)))
      (cons answer lib))))

(defun b2-reciprocal-move-divisor-establish-by-output-backward
    (equality lib reverse z x standard inv inverse-unit facts commute-value)
  (b2-reciprocal-results lib
      ((positioned (if reverse
                       (b2-reciprocal-results lib
                           ((commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" z x)))
                         (b2-reciprocal-chain lib equality commute))
                     equality))
       (fixed (b2-algebra-fixed-operand lib standard 2))
       (moved (b2-reciprocal-rewrite lib fixed positioned '(1 2 2)))
       (divided (b2-products-distribute-cancel lib inv x z inverse-unit (car (last facts))))
       (step (b2-reciprocal-chain lib moved divided)))
    (b2-reciprocal-return lib
      (if reverse (b2-reciprocal-chain lib commute-value step) step))))

(defun b2-reciprocal-move-divisor-establish-by-output
    (yes facts lib goal left value cancel x z reverse standard inv inverse-unit commute-value comparison)
  (if (not yes)
      (b2-reciprocal-results lib
          ((closed (b2-products-numeric-closure lib value))
           (same (b2-reciprocal-assume lib left))
           (result (b2-reciprocal-rewrite lib closed same '(1 1)))
           (result (b2-reciprocal-tidy lib result))
           (conflict (proof-proof-cut (library-library-proof lib) result (car (last facts))))
           (refused (proof-proof-front (library-library-proof lib) conflict (proof-neg left))))
        (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (append facts (list refused)))))
    (b2-reciprocal-results lib
        ((law
          (b2-reciprocal-equivalence lib left comparison equality
            (b2-reciprocal-move-divisor-establish-by-output-forward
             equality lib cancel x value z reverse)
            (b2-reciprocal-move-divisor-establish-by-output-backward
             equality lib reverse z x standard inv inverse-unit facts commute-value)) :library))
      (b2-reciprocal-return lib (b2-reciprocal-solve lib goal facts nil (list law))))))

(defun b2-reciprocal-move-divisor-establish
    (premise lib x inv y reverse value numeric goal left z comparison)
  (b2-reciprocal-results lib
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (typed (b2-reciprocal-evidence-at known (list *library-numberp* x)))
       (different (b2-quotient-algebra-require-nonzero lib x known))
       (unit (b2-products-reciprocal-identity lib x typed different))
       (swap (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" inv x))
       (inverse-unit (b2-reciprocal-chain lib swap unit))
       (standard (b2-products-product inv y))
       (assoc (b2-reciprocal-axiom lib "ASSOCIATIVITY-OF-*" x inv y))
       (cancel (b2-reciprocal-symmetric lib assoc))
       (cancel (b2-reciprocal-rewrite lib cancel unit '(1 2 1)))
       (unit-y (b2-reciprocal-axiom lib "UNICITY-OF-1" y))
       (cancel (b2-reciprocal-chain lib cancel unit-y))
       (commute-value (if reverse (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" y inv) nil))
       (cancel
        (if reverse
            (b2-reciprocal-results lib
                ((lifted (b2-algebra-congruence lib commute-value (b2-products-product x value) '(2))))
              (b2-reciprocal-chain lib lifted cancel))
          cancel)))
    (b2-reciprocal-choose lib numeric nil yes facts
      (b2-reciprocal-move-divisor-establish-by-output
       yes facts lib goal left value cancel x z reverse standard inv inverse-unit commute-value comparison))))

(defun b2-reciprocal-move-divisor (lib formula reverse)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length formula 3))
       (goal (proof-list-of-length (caddr parts) 3))
       (right (proof-list-of-length (caddr goal) 4))
       (left (proof-list-of-length (cadr goal) 3))
       (value (proof-list-of-length (cadr left) 3))
       (inv (if reverse (caddr value) (cadr value)))
       (y (if reverse (cadr value) (caddr value)))
       (x (proof-term-at inv 1))
       (result
        (b2-reciprocal-imply lib (cadr parts) goal premise
          (b2-reciprocal-move-divisor-establish
           premise lib x inv y reverse value (cadr right) goal left (caddr left) (caddr right)))))
    (car result)))

(defun b2-reciprocal-reciprocal-theorem (lib name formula)
  (cond
   ((equal name *b2-reciprocal-minus-zero*)
    (b2-reciprocal-results lib
        ((left (proof-term-at formula 1))
         (minus (proof-term-at left 2))
         (term (proof-term-at minus 1))
         (fixed-zero (list *b2-products-fix* *proof-zero*))
         (equivalence (b2-algebra-minus-equality
                       lib (proof-eq (library-minus *proof-zero*) (library-minus term))
                       (proof-eq fixed-zero (list *b2-products-fix* term))))
         (zero (proof-proof-compute (library-library-proof lib) (library-minus *proof-zero*) 0))
         (equivalence (b2-reciprocal-rewrite lib equivalence zero '(1 1 1)))
         (opened (b2-reciprocal-normalize lib fixed-zero nil (list *b2-products-fix*)))
         (equivalence (b2-reciprocal-rewrite lib equivalence opened '(1 2 1))))
      (b2-reciprocal-return lib (b2-reciprocal-tidy lib equivalence))))
   ((equal name *b2-reciprocal-invert-twice*)
    (b2-reciprocal-invert-involutively lib formula))
   ((equal name *b2-reciprocal-invert-product*)
    (b2-reciprocal-invert-factors lib formula))
   ((equal name *b2-reciprocal-invert-minus*)
    (b2-reciprocal-invert-negation lib formula))
   ((member-equal name (list *b2-reciprocal-cancel-right* *b2-reciprocal-cancel-left*))
    (b2-reciprocal-return lib
      (b2-reciprocal-remove-reciprocals lib formula (equal name *b2-reciprocal-cancel-right*))))
   ((equal name *b2-reciprocal-zero-product*)
    (b2-reciprocal-boolean-zero-product lib formula))
   ((member-equal name (list *b2-reciprocal-product-x* *b2-reciprocal-product-y*))
    (b2-reciprocal-product-same lib formula (equal name *b2-reciprocal-product-y*)))
   ((equal name *b2-reciprocal-inverse-equal*)
    (b2-reciprocal-return lib (b2-reciprocal-inverse-equality lib formula)))
   ((equal name *b2-reciprocal-numerator-nonzero*)
    (b2-reciprocal-return lib (b2-reciprocal-numerator-forward lib formula)))
   ((equal name *b2-reciprocal-injective*)
    (b2-reciprocal-reciprocal-injective lib formula))
   ((member-equal name (list *b2-reciprocal-move-left* *b2-reciprocal-move-right*))
    (b2-reciprocal-return lib
      (b2-reciprocal-move-divisor lib formula (equal name *b2-reciprocal-move-right*))))
   (t (b2-reciprocal-reciprocal-numerator lib formula))))
