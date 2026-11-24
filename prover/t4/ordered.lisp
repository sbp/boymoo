(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-ordered-iff* (proof-sym "IFF" "ACL2"))

(defun t4-ordered-sign (obj order proof)
  (list :sign obj order proof))

(defun t4-ordered-sign-obj (sign)
  (cadr sign))

(defun t4-ordered-sign-order (sign)
  (caddr sign))

(defun t4-ordered-sign-proof (sign)
  (cadddr sign))

(defun t4-ordered-request-p (value)
  (and (consp value) (eq (car value) :call)))

(defund t4-ordered-interrupted-p (value)
  (or (failure-p value) (t4-ordered-request-p value)))

(defun t4-ordered-retry-comparison-p (value)
  (and (failure-p value)
       (member-equal (cadr value) '("SearchMiss" "value" "Unproved" "MissingProof"))))

(defmacro t4-ordered-with-library (bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (rest `(t4-ordered-with-library ,(cdr bindings) ,result)))
      (if (caddr binding)
          `(let* ((ordered-result ,form)
                  (,name (if (failure-p ordered-result) ordered-result
                           (car ordered-result)))
                  (lib (if (failure-p ordered-result) lib (cdr ordered-result))))
             (if (t4-ordered-interrupted-p ,name) (cons ,name lib) ,rest))
        `(let ((,name ,form))
           (if (t4-ordered-interrupted-p ,name) (cons ,name lib) ,rest))))))

(defmacro t4-ordered-infer (rule lib &rest args)
  `(,rule (library-library-proof ,lib) ,@args))

(defun t4-ordered-request (kind lib args replies)
  (let* ((request (list* :call kind lib args))
         (reply (assoc-equal request replies)))
    (if reply (cdr reply) (cons request lib))))

(defund t4-ordered-side (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t4-ordered-premise (target premises)
  (if (endp premises)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car premises))))
      (if (equal literal target)
          (car premises)
        (t4-ordered-premise target (cdr premises))))))

(defun t4-ordered-rational-rule (head)
  (cond ((equal head *proof-plus*) "rationalp-binary-+")
        ((equal head *proof-times*) "rationalp-binary-*")
        ((equal head *proof-minus*) "rationalp-unary--")
        ((equal head *t4-algebra-reciprocal*) "rationalp-unary-/")
        (t nil)))

(defun t4-ordered-rational-from-facts (lib value target premises replies)
  (t4-ordered-with-library
      ((integer (t4-ordered-premise (list *proof-integerp* value) premises)))
    (if integer
        (t4-ordered-with-library
            ((axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list value))))
          (cons (t4-ordered-infer proof-proof-modus-ponens lib axiom integer) lib))
      (t4-ordered-with-library
          ((evidence (t4-structural-evidence-init lib nil premises))
           (known (t4-ordered-request :fact-proof lib (list target evidence) replies) :library))
        (cons (or known '(:failure "SearchMiss" "")) lib)))))

(mutual-recursion
 (defun t4-ordered-rational-with-replies (lib value premises replies)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (let ((target (list *library-rationalp* value)))
     (t4-ordered-with-library ((known (t4-ordered-premise target premises)))
       (if known
           (cons known lib)
         (t4-ordered-with-library
             ((constant (t4-ordinals-ordinals-constant lib target) :library)
              (constant-value (and constant (t4-ordered-side constant 2))))
           (cond
            ((equal constant-value *proof-true*)
             (cons (t4-ordered-infer proof-proof-true-from-eq lib constant) lib))
            ((and (proof-compound value) (not (consp value)))
             (cons '(:failure "failure" "") lib))
            ((and (consp value) (proof-compound value) (t4-ordered-rational-rule (car value)))
             (t4-ordered-with-library
                 ((proofs (t4-ordered-rational-arguments lib (cdr value) premises replies) :library)
                  (rule (t4-ordered-rational-rule (car value)))
                  (fact (t4-ordered-infer proof-proof-fact lib rule
                                          (seq-zip (list *library-x* *library-y*) (cdr value))))
                  (combined (t4-division-combine lib proofs)))
               (cons (t4-ordered-infer proof-proof-modus-ponens lib fact combined) lib)))
            (t (t4-ordered-rational-from-facts lib value target premises replies))))))))
 (defun t4-ordered-rational-arguments (lib values premises replies)
   (declare (xargs :measure (* 2 (acl2-count values))))
   (if (endp values)
       (cons nil lib)
     (t4-ordered-with-library
         ((first (t4-ordered-rational-with-replies lib (car values) premises replies) :library)
          (rest (t4-ordered-rational-arguments lib (cdr values) premises replies) :library))
       (cons (cons first rest) lib)))))

(defun t4-ordered-rational (lib value premises)
  (t4-ordered-rational-with-replies lib value premises nil))

(defun t4-ordered-identity-with-replies (lib left right premises replies)
  (t4-ordered-with-library ((step (t4-ordered-infer proof-proof-reflexive lib left)))
    (t4-algebra-orient-normalized-with-replies lib step (proof-eq left right) premises replies)))

(defun t4-ordered-identity (lib left right premises)
  (t4-ordered-identity-with-replies lib left right premises nil))

(defun t4-ordered-positive (term)
  (list *proof-less* *proof-zero* term))

(defun t4-ordered-negative (term)
  (list *proof-less* term *proof-zero*))

(defun t4-ordered-signed-cases-prepare (lib value typed replies)
  (let ((pos (t4-ordered-positive value))
        (zero (proof-eq value *proof-zero*)))
    (t4-ordered-with-library
        ((numeric (t4-algebra-number-with-replies lib value (list typed) replies) :library)
         (axiom (library-library-axiom lib "TRICHOTOMY" (list value)))
         (parts (t4-ordered-infer proof-proof-conjunct lib axiom))
         (disjunction (t4-ordered-infer proof-proof-modus-ponens lib (car parts) numeric))
         (not-pos (t4-ordered-infer proof-proof-assume lib pos nil))
         (remaining (t4-ordered-infer proof-proof-prove-if lib disjunction not-pos))
         (not-zero (t4-ordered-infer proof-proof-assume lib zero nil))
         (below (t4-ordered-infer proof-proof-prove-if lib remaining not-zero))
         (literal (proof-step-first below))
         (reversed (t4-ordered-identity-with-replies
                    lib literal (t4-ordered-negative value) (list typed) replies)
                   :library))
      (cons (t4-ordered-infer proof-proof-rewrite lib below reversed '(1)) lib))))

(defun t4-ordered-signed-cases-sign (lib value order below)
  (proof-with-checked-results
      ((proof (case order
                (1 (t4-ordered-infer proof-proof-assume lib (t4-ordered-positive value) t))
                (0 (t4-ordered-infer proof-proof-assume lib (proof-eq value *proof-zero*) t))
                (otherwise below))))
    (t4-ordered-sign value order proof)))

(defun t4-ordered-signed-cases-join (lib value yes same no)
  (t4-ordered-with-library
      ((remaining (t4-ordered-infer proof-proof-cases lib (proof-eq value *proof-zero*) same no)))
    (cons (t4-ordered-infer proof-proof-cases lib (t4-ordered-positive value) yes remaining)
          lib)))

(defmacro t4-ordered-with-signs (sign value typed replies body)
  `(t4-ordered-with-library
       ((below (t4-ordered-signed-cases-prepare lib ,value ,typed ,replies) :library)
        (yes (t4-ordered-with-library
                 ((,sign (t4-ordered-signed-cases-sign lib ,value 1 below)))
               ,body)
             :library)
        (same (t4-ordered-with-library
                  ((,sign (t4-ordered-signed-cases-sign lib ,value 0 below)))
                ,body)
              :library)
        (no (t4-ordered-with-library
                ((,sign (t4-ordered-signed-cases-sign lib ,value -1 below)))
              ,body)
            :library))
     (t4-ordered-signed-cases-join lib ,value yes same no)))

(defun t4-ordered-signed-cases-leaf (lib sign leaf)
  (let ((replies (case (t4-ordered-sign-order sign)
                   (1 leaf)
                   (0 (cdr leaf))
                   (otherwise (cddr leaf)))))
    (if (endp replies)
        (cons (list :call :leaf lib sign) lib)
      (let ((reply (car replies)))
        (if (failure-p reply) (cons reply lib) reply)))))

(defun t4-ordered-signed-cases-with-replies (lib value typed leaf replies)
  (t4-ordered-with-signs sign value typed replies
    (t4-ordered-signed-cases-leaf lib sign leaf)))

(defun t4-ordered-signed-cases (lib value typed leaf)
  (t4-ordered-signed-cases-with-replies lib value typed leaf nil))

(defun t4-ordered-no-negative-with-replies (lib value above replies)
  (t4-ordered-with-library
      ((axiom (library-library-axiom lib "TRICHOTOMY" (list value)))
       (clauses (t4-ordered-infer proof-proof-conjunct lib axiom))
       (literal (proof-step-first above))
       (not-twice (t4-ordered-request :prove lib
                                     (list (proof-neg (proof-neg literal))
                                           (list above) (list *proof-not*))
                                     replies)
                  :library)
       (excluded (t4-ordered-infer proof-proof-prove-if lib (cadr clauses) not-twice))
       (test (t4-ordered-side excluded 1))
       (equation (t4-ordered-identity-with-replies lib test (t4-ordered-negative value) nil replies)
                 :library)
       (rewritten (t4-ordered-infer proof-proof-rewrite lib excluded equation '(1 1))))
    (cons (t4-ordered-infer proof-proof-tidy lib rewritten) lib)))

(defun t4-ordered-no-negative (lib value above)
  (t4-ordered-no-negative-with-replies lib value above nil))

(defund t4-ordered-nonzero-sign (lib sign)
  (let ((test (proof-eq (t4-ordered-sign-obj sign) *proof-zero*)))
    (proof-with-checked-results
        ((assumed (t4-ordered-infer proof-proof-assume lib test t))
         (impossible (t4-ordered-infer proof-proof-rewrite lib (t4-ordered-sign-proof sign)
                                       assumed (list 1 (if (< 0 (t4-ordered-sign-order sign)) 2 1))))
         (zero (library-library-axiom lib "ZERO" nil))
         (cut (t4-ordered-infer proof-proof-cut lib impossible zero)))
      (t4-ordered-infer proof-proof-front lib cut (proof-neg test)))))

(defun t4-ordered-sign-test-comparison (lib obj order given term positive replies)
  (cond
   ((equal order (if positive 1 -1))
    (cons given lib))
   ((equal order 0)
    (t4-ordered-with-library
        ((reflexive (t4-ordered-infer proof-proof-reflexive lib term))
         (zero (t4-ordered-infer proof-proof-rewrite lib reflexive given
                                 (list 1 2 (if positive 2 1))))
         (axiom (library-library-axiom lib "ZERO" nil)))
      (cons (library-library-transport-argument lib axiom zero 1) lib)))
   ((< 0 order)
    (t4-ordered-no-negative-with-replies lib obj given replies))
   (t
    (t4-ordered-with-library
        ((assumed (t4-ordered-infer proof-proof-assume lib term t))
         (refused (t4-ordered-no-negative-with-replies lib obj assumed replies) :library)
         (cut (t4-ordered-infer proof-proof-cut lib given refused)))
      (cons (t4-ordered-infer proof-proof-front lib cut (proof-neg term)) lib)))))

(defun t4-ordered-sign-test-with-replies (lib sign term replies)
  (let* ((obj (t4-ordered-sign-obj sign))
         (order (t4-ordered-sign-order sign))
         (given (t4-ordered-sign-proof sign))
         (positive (equal term (t4-ordered-positive obj)))
         (zero (proof-eq obj *proof-zero*))
         (reversed-zero (proof-eq *proof-zero* obj)))
    (cond
     ((or positive (equal term (t4-ordered-negative obj)))
      (t4-ordered-sign-test-comparison lib obj order given term positive replies))
     ((or (equal term zero) (equal term reversed-zero))
      (if (equal order 0)
          (t4-ordered-with-library ((literal (proof-step-first given)))
            (cons (if (equal term literal) given
                    (t4-ordered-infer proof-proof-symmetric lib given))
                  lib))
        (t4-ordered-with-library ((denied (t4-ordered-nonzero-sign lib sign)))
          (if (equal term reversed-zero)
              (t4-ordered-with-library
                  ((assumed (t4-ordered-infer proof-proof-assume lib term t))
                   (reversed (t4-ordered-infer proof-proof-symmetric lib assumed))
                   (cut (t4-ordered-infer proof-proof-cut lib reversed denied)))
                (cons (t4-ordered-infer proof-proof-front lib cut (proof-neg term)) lib))
            (cons denied lib)))))
     (t (cons nil lib)))))

(defun t4-ordered-sign-test (lib sign term)
  (t4-ordered-sign-test-with-replies lib sign term nil))

(defun t4-ordered-as-boolean (lib test premise)
  (if (proof-is-call test *proof-equal*)
      (cons (t4-algebra-value-of test lib premise) lib)
    (t4-ordered-with-library
        ((literal (if premise (proof-step-first premise)
                    '(:failure "failure" ""))))
      (cond
       ((equal literal (proof-neg test))
        (cons (t4-algebra-value-of test lib premise) lib))
       ((proof-is-call test *proof-less*)
        (t4-ordered-with-library
            ((boolean (t4-ordered-infer proof-proof-fact lib "booleanp-<"
                                        (seq-zip (list *library-x* *library-y*) (cdr test))))
             (truth (t4-ordinals-ordinals-true-boolean lib boolean premise) :library))
          (cons truth lib)))
       (t (cons '(:failure "SearchMiss" "") lib))))))

(defun t4-ordered-product-sign-magnitude (sign lib premises replies)
  (let ((obj (t4-ordered-sign-obj sign))
        (given (t4-ordered-sign-proof sign)))
    (if (< 0 (t4-ordered-sign-order sign))
        (cons (list obj given) lib)
      (let ((reversed (list *proof-minus* obj)))
        (t4-ordered-with-library
            ((literal (proof-step-first given))
             (conversion (t4-ordered-identity-with-replies
                          lib literal (t4-ordered-positive reversed) premises replies)
                         :library)
             (proof (t4-ordered-infer proof-proof-rewrite lib given conversion '(1))))
          (cons (list reversed proof) lib))))))

(defun t4-ordered-product-sign-move (lib multiplied product a b d x-order y-order replies)
  (cond
   ((< x-order 0)
    (t4-ordered-with-library
        ((moved (t4-algebra-negate-product-with-replies lib d a 1 replies) :library))
      (if (< y-order 0)
          (t4-ordered-with-library
              ((negated (t4-algebra-negate-product-with-replies lib a b 2 replies) :library)
               (rewritten (t4-ordered-infer proof-proof-rewrite lib moved negated '(1 2 1)))
               (double (t4-algebra-double-negative-with-replies lib product replies) :library)
               (typed (t4-algebra-number-with-replies lib product nil replies) :library)
               (fixed (t4-algebra-fixed lib product typed))
               (moved (t4-ordered-infer proof-proof-chain lib rewritten (list double fixed))))
            (cons (t4-ordered-infer proof-proof-rewrite lib multiplied moved '(1 2)) lib))
        (cons (t4-ordered-infer proof-proof-rewrite lib multiplied moved '(1 2)) lib))))
   ((< y-order 0)
    (t4-ordered-with-library
        ((moved (t4-algebra-negate-product-with-replies lib a b 2 replies) :library))
      (cons (t4-ordered-infer proof-proof-rewrite lib multiplied moved '(1 2)) lib)))
   (t (cons multiplied lib))))

(defun t4-ordered-product-sign-with-replies (lib x y premises replies)
  (let* ((a (t4-ordered-sign-obj x))
         (b (t4-ordered-sign-obj y))
         (x-order (t4-ordered-sign-order x))
         (y-order (t4-ordered-sign-order y))
         (product (list *proof-times* a b)))
    (cond
     ((equal x-order 0)
      (t4-ordered-with-library
          ((reflexive (t4-ordered-infer proof-proof-reflexive lib product))
           (proof (t4-ordered-infer proof-proof-rewrite lib reflexive
                                    (t4-ordered-sign-proof x) '(1 2 1)))
           (zero (t4-algebra-multiply-zero-with-replies lib b replies) :library)
           (equation (t4-ordered-infer proof-proof-chain lib proof (list zero))))
        (cons (t4-ordered-sign product 0 equation) lib)))
     ((equal y-order 0)
      (t4-ordered-with-library
          ((reflexive (t4-ordered-infer proof-proof-reflexive lib product))
           (proof (t4-ordered-infer proof-proof-rewrite lib reflexive
                                    (t4-ordered-sign-proof y) '(1 2 2)))
           (commuted (t4-algebra-commuted lib *proof-times* a *proof-zero*))
           (zero (t4-algebra-multiply-zero-with-replies lib a replies) :library)
           (zero (t4-ordered-infer proof-proof-chain lib commuted (list zero)))
           (equation (t4-ordered-infer proof-proof-chain lib proof (list zero))))
        (cons (t4-ordered-sign product 0 equation) lib)))
     (t
      (t4-ordered-with-library
          ((magnitude-x (t4-ordered-product-sign-magnitude x lib premises replies) :library)
           (magnitude-y (t4-ordered-product-sign-magnitude y lib premises replies) :library)
           (c (car magnitude-x))
           (d (car magnitude-y))
           (typed-c (t4-ordered-rational-with-replies lib c premises replies) :library)
           (typed-d (t4-ordered-rational-with-replies lib d premises replies) :library)
           (multiplied (library-library-cite lib "POSITIVE-PRODUCT" (list c d)
                                              (list typed-c typed-d (cadr magnitude-x)
                                                    (cadr magnitude-y))))
           (moved (t4-ordered-product-sign-move lib multiplied product a b d
                                               x-order y-order replies)
                  :library)
           (order (* x-order y-order))
           (goal (if (< 0 order) (t4-ordered-positive product) (t4-ordered-negative product)))
           (literal (proof-step-first moved))
           (conversion (t4-ordered-identity-with-replies lib literal goal premises replies)
                       :library)
           (proof (t4-ordered-infer proof-proof-rewrite lib moved conversion '(1))))
        (cons (t4-ordered-sign product order proof) lib))))))

(defun t4-ordered-product-sign (lib x y premises)
  (t4-ordered-product-sign-with-replies lib x y premises nil))

(defun t4-ordered-sign-formula-test (lib term signs replies)
  (if (endp signs)
      (cons '(:failure "SearchMiss" "") lib)
    (t4-ordered-with-library
        ((premise (t4-ordered-sign-test-with-replies lib (car signs) term replies) :library))
      (if premise
          (t4-ordered-as-boolean lib term premise)
        (t4-ordered-sign-formula-test lib term (cdr signs) replies)))))

(defun t4-ordered-sign-formula-visit (n lib term signs replies)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n)))
    (cons '(:failure "Fuel" "t4-ordered-sign-formula-visit") lib))
   ((or (equal term *proof-true*) (equal term *proof-false*))
    (cons (t4-ordered-infer proof-proof-reflexive lib term) lib))
   ((proof-is-call term *proof-if*)
    (t4-ordered-with-library
        ((test-term (proof-term-at term 1))
         (computed (t4-ordered-sign-formula-visit (1- n) lib test-term signs replies) :library)
         (reflexive (t4-ordered-infer proof-proof-reflexive lib term))
         (moved (t4-ordered-infer proof-proof-rewrite lib reflexive computed '(1 2 1)))
         (computed-value (t4-ordered-side computed 2))
         (test (if (equal computed-value *proof-true*)
                   (t4-ordered-infer proof-proof-prove lib *proof-true* nil nil)
                 (t4-ordered-infer proof-proof-not-nil lib)))
         (chosen (t4-algebra-choose lib moved test))
         (right (t4-ordered-side chosen 2))
         (rest (t4-ordered-sign-formula-visit (1- n) lib right signs replies) :library))
      (cons (t4-ordered-infer proof-proof-chain lib chosen (list rest)) lib)))
   ((or (proof-is-call term *t4-ordered-iff*) (proof-is-call term *proof-not*))
    (t4-ordered-with-library
        ((opening (t4-ordered-infer proof-proof-unfold lib term))
         (right (t4-ordered-side opening 2))
         (rest (t4-ordered-sign-formula-visit (1- n) lib right signs replies) :library))
      (cons (t4-ordered-infer proof-proof-chain lib opening (list rest)) lib)))
   (t (t4-ordered-sign-formula-test lib term signs replies))))

(defun t4-ordered-sign-formula-with-replies (lib term signs replies)
  (t4-ordered-sign-formula-visit 1000000 lib term signs replies))

(defun t4-ordered-sign-formula (lib term signs)
  (t4-ordered-sign-formula-with-replies lib term signs nil))

(defun t4-ordered-product-sign-theorem-compare (sa sb lib premises left right replies)
  (t4-ordered-with-library
      ((current (t4-ordered-product-sign-with-replies lib sa sb premises replies) :library)
       (tested (t4-ordered-sign-test-with-replies lib current left replies) :library)
       (shown (t4-ordered-as-boolean lib left tested) :library)
       (target (t4-ordered-sign-formula-with-replies lib right (list sa sb) replies) :library)
       (reversed (t4-ordered-infer proof-proof-symmetric lib target)))
    (cons (t4-ordered-infer proof-proof-chain lib shown (list reversed)) lib)))

(defun t4-ordered-product-sign-theorem-right-cases (lib sa b tb premises left right replies)
  (t4-ordered-with-signs sb b tb replies
    (t4-ordered-product-sign-theorem-compare sa sb lib premises left right replies)))

(defun t4-ordered-product-sign-input (formula)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((goal (proof-term-at formula 2)))
      (if (not (proof-is-call goal *proof-equal*))
          nil
        (proof-with-checked-results
            ((parts (proof-list-of-length (cdr formula) 2))
             (sides (proof-list-of-length goal 3)))
          (let ((left (cadr sides))
                (right (caddr sides)))
            (if (and (proof-is-call left *proof-less*)
                     (member-equal *proof-zero* (cdr left)))
                (proof-with-checked-results
                    ((operand (proof-term-at left 2))
                     (product (if (equal operand *proof-zero*) (cadr left) operand)))
                  (and (proof-is-call product *proof-times*)
                       (proof-is-call right *proof-if*)
                       (list (car parts) left right product)))
              nil)))))))

(defun t4-ordered-product-sign-theorem-with-replies (lib formula replies)
  (t4-ordered-with-library ((input (t4-ordered-product-sign-input formula)))
    (if (not input)
        (cons nil lib)
      (let ((guard (nth 0 input))
            (left (nth 1 input))
            (right (nth 2 input))
            (product (nth 3 input)))
        (t4-ordered-with-library
            ((arithmetic (t4-ordered-request :arithmetic lib nil replies) :library)
             (assumed (t4-ordered-infer proof-proof-assume lib guard t))
             (premises (t4-division-pieces lib assumed))
             (operands (proof-list-of-length (cdr product) 2))
             (a (car operands))
             (b (cadr operands))
             (ta (t4-ordered-rational-with-replies lib a premises replies) :library)
             (tb (t4-ordered-rational-with-replies lib b premises replies) :library)
             (step (t4-ordered-with-signs sa a ta replies
                     (t4-ordered-product-sign-theorem-right-cases
                      lib sa b tb premises left right replies))
                   :library))
          (cons (t4-ordinals-ordinals-imply lib guard step) lib))))))

(defun t4-ordered-product-sign-theorem (lib formula)
  (t4-ordered-product-sign-theorem-with-replies lib formula nil))

(defun t4-ordered-scaled-order-lemma-compare (scale base lib premises typed-delta
                                                   value mark right delta replies)
  (t4-ordered-with-library
      ((sign (t4-ordered-product-sign-with-replies lib base scale
                                                  (append premises (list typed-delta)) replies)
             :library)
       (tested (t4-ordered-sign-test-with-replies lib sign mark replies) :library)
       (boolean (t4-ordered-as-boolean lib mark tested) :library)
       (shown (t4-ordered-infer proof-proof-chain lib value (list boolean)))
       (decision (t4-ordered-sign-test-with-replies lib scale (cadr right) replies) :library)
       (target (t4-ordered-infer proof-proof-select lib right decision))
       (order (t4-ordered-sign-order scale))
       (target (if (<= order 0)
                   (t4-ordered-with-library
                       ((rhs (t4-ordered-side target 2))
                        (test-term (proof-term-at rhs 1))
                        (test (t4-ordered-sign-test-with-replies lib scale test-term replies) :library))
                     (cons (t4-algebra-choose lib target test) lib))
                 (cons target lib))
               :library)
       (target (if (equal order 0)
                   (cons target lib)
                 (let ((required (if (< 0 order) (t4-ordered-negative delta)
                                   (t4-ordered-positive delta))))
                   (t4-ordered-with-library
                       ((rhs (t4-ordered-side target 2))
                        (same (t4-ordered-identity-with-replies lib rhs required premises replies)
                              :library)
                        (tested (t4-ordered-sign-test-with-replies lib base required replies)
                                :library)
                        (boolean (t4-ordered-as-boolean lib required tested) :library))
                     (cons (t4-ordered-infer proof-proof-chain lib target (list same boolean)) lib))))
               :library)
       (reversed (t4-ordered-infer proof-proof-symmetric lib target)))
    (cons (t4-ordered-infer proof-proof-chain lib shown (list reversed)) lib)))

(defun t4-ordered-scaled-order-lemma-base-cases (lib scale premises typed-delta
                                                   value mark right delta replies)
  (t4-ordered-with-signs base delta typed-delta replies
    (t4-ordered-scaled-order-lemma-compare
     scale base lib premises typed-delta value mark right delta replies)))

(defun t4-ordered-scaled-order-lemma-with-replies (lib replies)
  (let ((name "RATIONAL-SCALE-ORDER"))
    (if (assoc-equal (proof-sym "SELF-RATIONAL-SCALE-ORDER" "ACL2")
                     (proof-proof-facts (library-library-proof lib)))
        (cons nil lib)
      (let* ((x *library-x*)
             (y *library-y*)
             (factor *library-z*)
             (ta (list *library-rationalp* x))
             (tb (list *library-rationalp* y))
             (tf (list *library-rationalp* factor))
             (guard (proof-ite ta (proof-ite tb tf *proof-false*) *proof-false*)))
        (t4-ordered-with-library
            ((assumed (t4-ordered-infer proof-proof-assume lib guard t))
             (premises (t4-division-pieces lib assumed))
             (left (list *proof-less* (list *proof-times* x factor) (list *proof-times* y factor)))
             (delta (list *proof-plus* x (list *proof-minus* y)))
             (right (proof-ite (t4-ordered-positive factor) (list *proof-less* x y)
                              (proof-ite (proof-eq factor *proof-zero*) *proof-false*
                                         (list *proof-less* y x))))
             (typed-delta (t4-ordered-rational-with-replies lib delta premises replies) :library)
             (split (library-library-axiom lib "DISTRIBUTIVITY" (list factor x (list *proof-minus* y))))
             (opened (library-library-axiom lib "<-ON-OTHERS" (cdr left)))
             (rhs (t4-ordered-side opened 2))
             (difference (proof-term-at rhs 1))
             (distributed (t4-algebra-orient-normalized-with-replies
                           lib split (proof-eq (list *proof-times* delta factor) difference)
                           premises replies)
                          :library)
             (reversed (t4-ordered-infer proof-proof-symmetric lib distributed))
             (value (t4-ordered-infer proof-proof-rewrite lib opened reversed '(1 2 1)))
             (mark (t4-ordered-side value 2))
             (typed (proof-term-at premises 2))
             (cases (t4-ordered-with-signs scale factor typed replies
                      (t4-ordered-scaled-order-lemma-base-cases
                       lib scale premises typed-delta value mark right delta replies))
                    :library)
             (formula (list *library-implies* guard (proof-eq left right)))
             (proof (t4-ordinals-ordinals-imply lib guard cases))
             (updated (library-library-lemma lib name formula proof nil)))
          (cons nil updated))))))

(defun t4-ordered-scaled-order-lemma (lib)
  (let ((result (t4-ordered-scaled-order-lemma-with-replies lib nil)))
    (or (car result) (cdr result))))

(defun t4-ordered-scaled-order-with-replies (lib a b factor premises replies)
  (t4-ordered-with-library
      ((lemma (t4-ordered-scaled-order-lemma-with-replies lib replies) :library)
       (proofs (t4-ordered-rational-arguments lib (list a b factor) premises replies) :library)
       (supported (t4-division-combine lib proofs))
       (rule (library-library-cite lib "RATIONAL-SCALE-ORDER" (list a b factor) nil)))
    (cons (t4-ordered-infer proof-proof-modus-ponens lib rule supported) lib)))

(defun t4-ordered-scaled-order (lib a b factor premises)
  (t4-ordered-scaled-order-with-replies lib a b factor premises nil))

(defund t4-ordered-scale-for-unscaled-with-replies (lib term factor premises replies)
  (cond
   ((and (proof-is-call term *proof-times*) (member-equal factor (cdr term)))
    (t4-ordered-with-library
        ((left (proof-term-at term 1))
         (right (proof-term-at term 2))
         (value (if (equal left factor) right left))
         (raw (if (equal right factor)
                  (t4-ordered-infer proof-proof-reflexive lib term)
                (t4-algebra-commuted lib *proof-times* factor value))))
      (cons (list value raw) lib)))
   ((equal factor term)
    (t4-ordered-with-library
        ((typed (t4-ordered-rational-with-replies lib factor premises replies) :library)
         (num (t4-algebra-number-with-replies lib factor (list typed) replies) :library)
         (unit (t4-algebra-unit-with-replies lib *proof-times* factor (list num) replies) :library)
         (reversed (t4-ordered-infer proof-proof-symmetric lib unit)))
      (cons (list *proof-one* reversed) lib)))
   (t (cons (list nil nil) lib))))

(defun t4-ordered-scale-for-unscaled (lib term factor premises)
  (t4-ordered-scale-for-unscaled-with-replies lib term factor premises nil))

(defund t4-ordered-choose-sign-branch (lib equation sign replies)
  (t4-ordered-with-library ((rhs (t4-ordered-side equation 2)))
    (if (not (proof-is-call rhs *proof-if*))
        (cons nil lib)
      (t4-ordered-with-library
          ((test (proof-term-at rhs 1))
           (step (t4-ordered-sign-test-with-replies lib sign test replies) :library))
        (cons (and step (t4-algebra-choose lib equation step)) lib)))))

(defun t4-ordered-choose-sign-visit (n lib equation sign replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "t4-ordered-choose-sign-visit") lib)
    (t4-ordered-with-library
        ((chosen (t4-ordered-choose-sign-branch lib equation sign replies) :library))
      (if chosen
          (t4-ordered-choose-sign-visit (1- n) lib chosen sign replies)
        (cons equation lib)))))

(defun t4-ordered-choose-sign-with-replies (lib equation sign replies)
  (t4-ordered-choose-sign-visit 1000000 lib equation sign replies))

(defun t4-ordered-choose-sign (lib equation sign)
  (t4-ordered-choose-sign-with-replies lib equation sign nil))

(defun t4-ordered-scaled-comparison-compare (sign lib comparison right premises replies)
  (t4-ordered-with-library
      ((first (t4-ordered-choose-sign-with-replies lib comparison sign replies) :library)
       (reflexive (t4-ordered-infer proof-proof-reflexive lib right))
       (second (t4-ordered-choose-sign-with-replies lib reflexive sign replies) :library)
       (first-value (t4-ordered-side first 2))
       (second-value (t4-ordered-side second 2))
       (same (t4-ordered-identity-with-replies lib first-value second-value premises replies)
             :library)
       (reversed (t4-ordered-infer proof-proof-symmetric lib second)))
    (cons (t4-ordered-infer proof-proof-chain lib first (list same reversed)) lib)))

(defund t4-ordered-scaled-comparison-attempt (lib factor guard comparison right premises replies)
  (t4-ordered-with-library
      ((typed (t4-ordered-rational-with-replies lib factor premises replies) :library)
       (proof (t4-ordered-with-signs sign factor typed replies
                (t4-ordered-scaled-comparison-compare sign lib comparison right premises replies))
              :library))
    (cons (t4-ordinals-ordinals-imply lib guard proof) lib)))

(defund t4-ordered-scaled-comparison-factor (lib factor guard left right a b premises replies)
  (t4-ordered-with-library
      ((scaled-a (t4-ordered-scale-for-unscaled-with-replies lib a factor premises replies)
                 :library)
       (scaled-b (t4-ordered-scale-for-unscaled-with-replies lib b factor premises replies)
                 :library))
    (if (or (not (cadr scaled-a)) (not (cadr scaled-b)))
        (cons nil lib)
      (t4-ordered-with-library
          ((reflexive (t4-ordered-infer proof-proof-reflexive lib left))
           (first (t4-ordered-infer proof-proof-rewrite lib reflexive (cadr scaled-a) '(1 2 1)))
           (shown (t4-ordered-infer proof-proof-rewrite lib first (cadr scaled-b) '(1 2 2)))
           (scaled (t4-ordered-scaled-order-with-replies lib (car scaled-a) (car scaled-b)
                                                          factor premises replies)
                   :library)
           (comparison (t4-ordered-infer proof-proof-chain lib shown (list scaled))))
        (let ((attempt (t4-ordered-scaled-comparison-attempt lib factor guard comparison
                                                              right premises replies)))
          (if (t4-ordered-retry-comparison-p (car attempt))
              (cons nil (cdr attempt))
            attempt))))))

(defun t4-ordered-scaled-comparison-candidates (lib factors guard left right a b premises replies)
  (declare (xargs :measure (acl2-count factors)))
  (if (endp factors)
      (cons nil lib)
    (let ((attempt (t4-ordered-scaled-comparison-factor lib (car factors) guard left right
                                                         a b premises replies)))
      (if (car attempt)
          attempt
        (t4-ordered-scaled-comparison-candidates (cdr attempt) (cdr factors) guard left right
                                                   a b premises replies)))))

(defun t4-ordered-comparison-input (formula scaled)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((goal (proof-term-at formula 2)))
      (if (not (proof-is-call goal *proof-equal*))
          nil
        (proof-with-checked-results
            ((left (if scaled (proof-term-at goal 1) nil)))
          (if (and scaled (not (proof-is-call left *proof-less*)))
              nil
            (proof-with-checked-results
                ((parts (proof-list-of-length (cdr formula) 2))
                 (sides (proof-list-of-length goal 3)))
              (let ((left (cadr sides))
                    (right (caddr sides)))
                (and (if scaled
                         (proof-is-call right *proof-if*)
                       (and (proof-is-call left *proof-less*)
                            (proof-is-call right *proof-less*)))
                     (list (car parts) left right))))))))))

(defun t4-ordered-scaled-comparison-with-replies (lib formula replies)
  (t4-ordered-with-library ((input (t4-ordered-comparison-input formula t)))
    (if (not input)
        (cons nil lib)
      (let ((guard (car input))
            (left (cadr input))
            (right (caddr input)))
        (t4-ordered-with-library ((operands (proof-list-of-length (cdr left) 2)))
          (let* ((a (car operands))
                 (b (cadr operands))
                 (factors (proof-unique (append (and (proof-is-call a *proof-times*) (cdr a))
                                                (and (proof-is-call b *proof-times*) (cdr b))))))
            (if (endp factors)
                (cons nil lib)
              (t4-ordered-with-library
                  ((arithmetic (t4-ordered-request :arithmetic lib nil replies) :library)
                   (assumed (t4-ordered-infer proof-proof-assume lib guard t))
                   (premises (t4-division-pieces lib assumed)))
                (t4-ordered-scaled-comparison-candidates
                 lib factors guard left right a b premises replies)))))))))

(defun t4-ordered-scaled-comparison (lib formula)
  (t4-ordered-scaled-comparison-with-replies lib formula nil))

(defun t4-ordered-has-reciprocal (terms)
  (if (endp terms)
      nil
    (or (proof-is-call (car terms) *t4-algebra-reciprocal*)
        (t4-ordered-has-reciprocal (cdr terms)))))

(defun t4-ordered-has-divided-operand (terms)
  (if (endp terms)
      nil
    (let ((term (car terms)))
      (or (proof-is-call term *t4-algebra-reciprocal*)
          (and (proof-is-call term *proof-times*)
               (t4-ordered-has-reciprocal (cdr term)))
          (t4-ordered-has-divided-operand (cdr terms))))))

(defund t4-ordered-divided-comparison-attempt (lib left right factor sign evidence replies)
  (let ((order (t4-ordered-sign-order sign)))
    (t4-ordered-with-library
        ((args (proof-list-of-length (if (< 0 order) (cdr left) (reverse (cdr left))) 2))
         (scaled (t4-ordered-scaled-order-with-replies
                  lib (car args) (cadr args) factor evidence replies) :library)
         (ordered (t4-ordered-choose-sign-with-replies lib scaled sign replies) :library)
         (lhs (t4-ordered-side ordered 1))
         (compare (t4-ordered-identity-with-replies lib lhs right evidence replies) :library))
      (cons (list ordered compare) lib))))

(defund t4-ordered-divided-comparison-denominator (lib signed guard left right premises replies)
  (t4-ordered-with-library ((test (proof-step-first signed)))
    (if (not (and (proof-is-call test *proof-less*) (member-equal *proof-zero* (cdr test))))
        (cons nil lib)
      (t4-ordered-with-library
          ((order (if (equal (cadr test) *proof-zero*) 1 -1))
           (factor (proof-term-at test (if (< 0 order) 2 1)))
           (sign (t4-ordered-sign factor order signed))
           (nonzero (t4-ordered-nonzero-sign lib sign))
           (evidence (append premises (list nonzero))))
        (let* ((attempt (t4-ordered-divided-comparison-attempt
                         lib left right factor sign evidence replies))
               (result (car attempt))
               (lib (cdr attempt)))
          (cond
           ((t4-ordered-retry-comparison-p result) (cons nil lib))
           ((t4-ordered-interrupted-p result) attempt)
           (t
            (t4-ordered-with-library
                ((reversed (t4-ordered-infer proof-proof-symmetric lib (car result)))
                 (step (t4-ordered-infer proof-proof-chain lib reversed (list (cadr result)))))
              (cons (t4-ordinals-ordinals-imply lib guard step) lib)))))))))

(defun t4-ordered-divided-comparison-candidates (lib candidates guard left right premises replies)
  (declare (xargs :measure (acl2-count candidates)))
  (if (endp candidates)
      (cons nil lib)
    (let ((attempt (t4-ordered-divided-comparison-denominator
                    lib (car candidates) guard left right premises replies)))
      (if (car attempt)
          attempt
        (t4-ordered-divided-comparison-candidates
         (cdr attempt) (cdr candidates) guard left right premises replies)))))

(defun t4-ordered-divided-comparison-with-replies (lib formula replies)
  (t4-ordered-with-library ((input (t4-ordered-comparison-input formula nil)))
    (if (not input)
        (cons nil lib)
      (let ((guard (car input))
            (left (cadr input))
            (right (caddr input)))
        (if (not (t4-ordered-has-divided-operand (cdr left)))
            (cons nil lib)
          (t4-ordered-with-library
              ((arithmetic (t4-ordered-request :arithmetic lib nil replies) :library)
               (assumed (t4-ordered-infer proof-proof-assume lib guard t))
               (premises (t4-division-pieces lib assumed)))
            (t4-ordered-divided-comparison-candidates
             lib premises guard left right premises replies)))))))

(defun t4-ordered-divided-comparison (lib formula)
  (t4-ordered-divided-comparison-with-replies lib formula nil))
