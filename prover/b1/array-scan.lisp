(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-array-scan-null* (proof-cl "NULL"))
(defconst *b1-array-scan-reverse* (proof-cl "REVERSE"))
(defconst *b1-array-scan-revappend* (proof-cl "REVAPPEND"))
(defconst *b1-array-scan-k* (proof-sym "K" "ACL2"))
(defconst *b1-array-scan-acc* (proof-sym "ACC" "ACL2"))
(defconst *b1-array-scan-scan-call*
  (list *b1-arrays-scan* *b1-arrays-name* *b1-arrays-l* *b1-arrays-i* *b1-arrays-j* *b1-arrays-d*))
(defconst *b1-array-scan-next* (library-plus *b1-arrays-i* *proof-one*))
(defconst *b1-array-scan-stop* (list *b1-logic-zp* (library-diff *b1-arrays-j* *b1-arrays-i*)))
(defconst *b1-array-scan-pair* (list *b1-arrays-assoc* *b1-arrays-i* *b1-arrays-l*))
(defconst *b1-array-scan-missing* (proof-eq *b1-array-scan-pair* *proof-false*))
(defconst *b1-array-scan-default-value*
  (proof-eq (list *library-cdr* *b1-array-scan-pair*) *b1-arrays-d*))

(defun b1-array-scan-literal-field (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-array-scan-conjunction (conditions)
  (cond ((endp conditions) '(:failure "failure" ""))
        ((endp (cdr conditions)) (car conditions))
        (t (proof-ite (car conditions) (b1-array-scan-conjunction (cdr conditions)) *proof-false*))))

(defun b1-array-scan-scan-step (lib type-i type-j)
  (let ((proof (library-library-proof lib))
        (types (list type-i type-j))
        (i *b1-arrays-i*)
        (j *b1-arrays-j*)
        (next *b1-array-scan-next*)
        (delta (cadr *b1-array-scan-stop*)))
    (proof-with-checked-results
        ((next-type (library-library-type-of lib next types))
         (continue (proof-proof-assume proof *b1-array-scan-stop* nil))
         (delta-type (library-library-type-of lib delta types))
         (positive-gap (b1-integer-no-zp lib delta continue delta-type))
         (comparison (library-library-comparison lib i j types))
         (inside (proof-proof-transport proof positive-gap comparison))
         (one-positive (proof-proof-prove proof (library-positive *proof-one*) nil nil))
         (advance (library-library-less-from-difference lib i next one-positive types))
         (decrease (library-library-cite lib "GAP-DECREASE" (list j i next)
                                         (list type-j type-i next-type inside advance))))
      (list inside advance decrease next-type))))

(defun b1-array-scan-scan-hypothesis (lib formula decrease bindings evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((next-formula (proof-subst formula bindings))
         (next-condition (proof-term-at next-formula 1))
         (next-guard (b1-logic-bookproof-normalize-proof lib next-condition evidence nil nil nil))
         (shrinks (proof-step-first decrease))
         (given (proof-proof-assume proof (proof-ite shrinks next-formula *proof-true*) t))
         (hypothesis (proof-proof-prove-if proof given decrease)))
      (proof-proof-modus-ponens proof hypothesis next-guard))))

(defun b1-array-scan-prove-scan-prepare (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((ordinal (library-library-cite lib "GAP-ORDINAL" (list *b1-arrays-j* *b1-arrays-i*) nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (fields (b1-logic-bookproof-split-conjuncts lib premise))
         (view (proof-proof-unfold proof *b1-array-scan-scan-call*))
         (value (b1-array-scan-literal-field view 2))
         (selected (proof-proof-if-true proof value))
         (empty (proof-proof-chain proof view (list selected)))
         (types (proof-list-of-length (take (min 2 (len fields)) fields) 2))
         (progress (b1-array-scan-scan-step lib (car types) (cadr types))))
      (list ordinal premise fields empty progress))))

(defun b1-array-scan-prove-scan-consequence (base step lib)
  (library-inherited proof-proof-cases lib *b1-array-scan-stop* base step))

(defun b1-array-scan-prove-scan-bindings (bindings)
  (if (endp bindings)
      nil
    (cons (table-items (car bindings)) (b1-array-scan-prove-scan-bindings (cdr bindings)))))

(defun b1-array-scan-prove-scan (lib formula preparation base step bindings)
  (proof-with-checked-results
      ((consequence (b1-array-scan-prove-scan-consequence base step lib))
       (case (b1-logic-bookproof-prove-implication-with-premise
              lib formula (cadr preparation) consequence)))
    (library-inherited proof-proof-induct lib (car preparation) case formula
                       (list *library-gap* *b1-arrays-j* *b1-arrays-i*)
                       (b1-array-scan-prove-scan-bindings bindings))))

(defun b1-array-scan-scan-paths-tests (lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((missing (proof-proof-assume proof *b1-array-scan-missing* t))
         (present (proof-proof-assume proof *b1-array-scan-missing* nil))
         (default (proof-proof-assume proof *b1-array-scan-default-value* t))
         (retained (proof-proof-assume proof *b1-array-scan-default-value* nil)))
      (list missing present default retained))))

(defun b1-array-scan-scan-paths-reduction (tests lib)
  (proof-with-checked-results
      ((continue (library-inherited proof-proof-assume lib *b1-array-scan-stop* nil)))
    (b1-logic-bookproof-normalize
     lib *b1-array-scan-scan-call* (cons continue tests)
     (list *b1-arrays-scan* *b1-array-scan-null* *b1-logic-eq* *proof-not*) nil nil nil nil)))

(defun b1-array-scan-scan-paths (lib empty same found)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((present (proof-proof-cases proof *b1-array-scan-default-value* same found)))
      (proof-proof-cases proof *b1-array-scan-missing* empty present))))

(defun b1-array-scan-lookup-pair (lib alist present)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((different (b1-array-scan-literal-field present 1))
         (pair (proof-term-at different 1))
         (parts (proof-list-of-length pair 3))
         (test (list *proof-consp* pair))
         (law (proof-proof-fact proof (proof-sym "CONSP-ASSOC-EQUAL" "ACL2")
                                (list (list *b1-arrays-name* (cadr parts))
                                      (list *b1-arrays-l* (caddr parts)))))
         (alternatives (proof-proof-modus-ponens proof law alist))
         (atom (proof-proof-assume proof test nil))
         (absent (proof-proof-prove-if proof alternatives atom))
         (found (proof-proof-cut proof absent present)))
      (proof-proof-front proof found test))))

(defun b1-array-scan-lookup-key (lib pair)
  (proof-with-checked-results
      ((call (b1-array-scan-literal-field pair 1))
       (parts (proof-list-of-length call 3))
       (named (b1-arrays-assoc-returned-key lib))
       (lib (cdr named))
       (proof (library-library-proof lib))
       (law (proof-proof-fact proof (car named)
                              (list (list *library-x* (cadr parts)) (list *library-y* (caddr parts)))))
       (step (proof-proof-modus-ponens proof law pair)))
    (cons step lib)))

(defun b1-array-scan-bounded-list-is-alist (lib bound)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first bound))
         (parts (proof-list-of-length literal 3))
         (items (cadr parts))
         (limit (caddr parts))
         (alist (list *b1-arrays-alistp* items))
         (eqlable (list (proof-sym "EQLABLE-ALISTP" "ACL2") items))
         (rule (b1-logic-bookproof-from-fact
                lib (proof-sym "BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP" "ACL2")
                (list *library-implies* (list *b1-arrays-bounded* items limit) eqlable)))
         (typed (proof-proof-modus-ponens proof rule bound))
         (rule (b1-logic-bookproof-from-fact
                lib (proof-sym "EQLABLE-ALISTP-FORWARD-TO-ALISTP" "ACL2")
                (list *library-implies* eqlable alist))))
      (proof-proof-modus-ponens proof rule typed))))

(defun b1-array-scan-bounded-cons (lib pair bound evidence rules)
  (proof-with-checked-results
      ((view (b1-logic-bookproof-normalize
              lib (list *b1-arrays-bounded* pair bound) evidence
              (list *b1-arrays-bounded* *b1-logic-atom* *b1-logic-eq* *proof-not*) rules nil nil t))
       (value (b1-array-scan-literal-field view 2))
       (step (b1-logic-bookproof-normalize-proof lib value evidence nil nil nil)))
    (library-inherited proof-proof-transport lib step view)))

(defun b1-array-scan-bounded-scan-base (equation fields lib)
  (declare (ignore fields))
  (proof-with-checked-results
      ((empty (b1-logic-bookproof-normalize-proof
               lib (list *b1-arrays-bounded* *proof-false* *b1-arrays-j*) nil
               (list *b1-arrays-bounded* *b1-logic-atom* *b1-array-scan-null*
                     *b1-logic-eq* *proof-not*) nil nil)))
    (library-library-transport-argument lib empty equation 1)))

(defun b1-array-scan-bounded-scan-step-discard (equation lib child)
  (library-library-transport-argument lib child equation 1))

(defun b1-array-scan-bounded-scan-step-keep (equation present retained lib alist type-i
                                                  nonnegative upper child)
  (declare (ignore retained))
  (proof-with-checked-results
      ((cons (b1-array-scan-lookup-pair lib alist present))
       (key (b1-array-scan-lookup-key lib cons))
       (lib (cdr key))
       (ordinary (b1-arrays-integer-key-not-header lib type-i))
       (value (b1-array-scan-literal-field equation 2))
       (kept (b1-array-scan-bounded-cons lib value *b1-arrays-j*
                                        (list cons type-i nonnegative upper child ordinary)
                                        (list (b1-logic-equal-to (car key)))))
       (step (library-library-transport-argument lib kept equation 1)))
    (cons step lib)))

(defun b1-array-scan-bounded-scan-step-paths (lib alist type-i nonnegative upper child)
  (proof-with-checked-results
      ((tests (b1-array-scan-scan-paths-tests lib))
       (missing (car tests))
       (present (cadr tests))
       (default (caddr tests))
       (retained (cadddr tests))
       (empty (b1-array-scan-scan-paths-reduction (list missing) lib))
       (empty (b1-array-scan-bounded-scan-step-discard empty lib child))
       (same (b1-array-scan-scan-paths-reduction (list present default) lib))
       (same (b1-array-scan-bounded-scan-step-discard same lib child))
       (found (b1-array-scan-scan-paths-reduction (list present retained) lib))
       (found (b1-array-scan-bounded-scan-step-keep
               found present retained lib alist type-i nonnegative upper child))
       (lib (cdr found))
       (step (b1-array-scan-scan-paths lib empty same (car found))))
    (cons step lib)))

(defun b1-array-scan-bounded-scan-step (progress fields lib formula)
  (let ((proof (library-library-proof lib))
        (i *b1-arrays-i*)
        (one *proof-one*)
        (next *b1-array-scan-next*))
    (proof-with-checked-results
        ((progress (proof-list-of-length progress 4))
         (fields (proof-list-of-length fields 4))
         (upper (car progress))
         (decrease (caddr progress))
         (next-type (cadddr progress))
         (type-i (car fields))
         (type-j (cadr fields))
         (nonnegative (caddr fields))
         (alist (cadddr fields))
         (one-type (library-library-type-of lib one nil))
         (one-positive (proof-proof-prove proof (library-positive one) nil nil))
         (next-positive (library-library-cite lib "POSITIVE-PLUS-NONNEGATIVE" (list i one)
                                               (list type-i one-type one-positive nonnegative)))
         (commuted (library-library-axiom lib "COMMUTATIVITY-OF-+" (list one i)))
         (next-positive (proof-proof-rewrite proof next-positive commuted '(1 2)))
         (next-lower (library-library-cite lib "POSITIVE-NONNEGATIVE" (list next)
                                          (list next-type next-positive)))
         (child (b1-array-scan-scan-hypothesis lib formula decrease (list (cons i next))
                                               (list next-type type-j next-lower alist))))
      (b1-array-scan-bounded-scan-step-paths lib alist type-i nonnegative upper child))))

(defun b1-array-scan-bounded-scan (lib)
  (let ((name (proof-sym "SELF-COMPRESS11-BOUNDED" "ACL2")))
    (if (assoc-equal name (library-inherited proof-proof-facts lib))
        (cons name lib)
      (let* ((i *b1-arrays-i*)
             (j *b1-arrays-j*)
             (guard (b1-array-scan-conjunction
                     (list (library-integer i) (library-integer j) (proof-neg (library-lt i *proof-zero*))
                           (list *b1-arrays-alistp* *b1-arrays-l*))))
             (formula (list *library-implies* guard (list *b1-arrays-bounded* *b1-array-scan-scan-call* j))))
        (proof-with-checked-results
            ((preparation (b1-array-scan-prove-scan-prepare lib formula))
             (fields (caddr preparation))
             (base (b1-array-scan-bounded-scan-base (cadddr preparation) fields lib))
             (step (b1-array-scan-bounded-scan-step (nth 4 preparation) fields lib formula))
             (lib (cdr step))
             (proof (b1-array-scan-prove-scan lib formula preparation base (car step)
                                             (list (list (cons i *b1-array-scan-next*)))))
             (lib (library-library-lemma lib "COMPRESS11-BOUNDED" formula proof nil)))
          (cons name lib))))))

(defun b1-array-scan-bounded-reverse-base (atom lib formula call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (fields (proof-proof-conjunct proof premise))
         (opened (b1-revappend-open-list lib call (list atom)))
         (step (library-library-transport-argument lib (cadr fields) opened 1)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise step))))

(defun b1-array-scan-bounded-reverse-step-consequence (premise lib before cons hypothesis call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (proof-proof-conjunct proof premise))
         (source (car fields))
         (tail (cadr fields))
         (equation (b1-logic-bookproof-normalize
                    lib before (list cons)
                    (list *b1-arrays-bounded* *b1-logic-atom* *proof-not* *b1-logic-eq*) nil nil nil t))
         (rewritten (proof-proof-rewrite proof source equation '(1)))
         (fields (b1-logic-bookproof-split-conjuncts lib rewritten))
         (fields (proof-list-of-length fields 3))
         (pair (list *proof-cons* (list *library-car* *library-x*) *library-y*))
         (inserted (b1-array-scan-bounded-cons lib pair *b1-arrays-j* (list (car fields) (cadr fields) tail) nil))
         (condition (b1-array-scan-literal-field hypothesis 1))
         (guard (b1-logic-bookproof-normalize-proof lib condition (list (caddr fields) inserted) nil nil nil))
         (rest (proof-proof-modus-ponens proof hypothesis guard))
         (opened (b1-revappend-open-list lib call (list cons))))
      (library-library-transport-argument lib rest opened 1))))

(defun b1-array-scan-bounded-reverse-step (cons hypothesis lib formula before call)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-array-scan-bounded-reverse-step-consequence premise lib before cons hypothesis call)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise step)))

(defun b1-array-scan-bounded-reverse-install (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (j *b1-arrays-j*)
         (bounded *b1-arrays-bounded*)
         (call (list *b1-array-scan-revappend* x y))
         (before (list bounded x j))
         (carried (list bounded y j))
         (formula (list *library-implies* (b1-array-scan-conjunction (list before carried))
                        (list bounded call j))))
    (proof-with-checked-results
        ((prepared (b1-revappend-list-induction-prepare lib formula x y))
         (step (b1-array-scan-bounded-reverse-step (caddr prepared) (cadddr prepared) lib formula before call))
         (atom (proof-proof-assume proof (cadr prepared) nil))
         (base (b1-array-scan-bounded-reverse-base atom lib formula call))
         (step (b1-revappend-list-induction lib prepared base step)))
      (library-library-lemma lib "REVAPPEND-BOUNDED-ALIST" formula step nil))))

(defun b1-array-scan-bounded-reverse (lib original accumulator)
  (let ((name (proof-sym "SELF-REVAPPEND-BOUNDED-ALIST" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (library-inherited proof-proof-facts lib))
                  lib
                (b1-array-scan-bounded-reverse-install lib)))
         (proof (library-library-proof lib))
         (original-literal (proof-step-first original))
         (original-parts (proof-list-of-length original-literal 3))
         (accumulator-literal (proof-step-first accumulator))
         (accumulator-parts (proof-list-of-length accumulator-literal 3))
         (fact (proof-proof-fact proof name
                                (list (list *library-x* (cadr original-parts))
                                      (list *library-y* (cadr accumulator-parts))
                                      (list *b1-arrays-j* (caddr original-parts)))))
         (condition (b1-array-scan-literal-field fact 1))
         (guard (b1-logic-bookproof-normalize-proof lib condition (list original accumulator) nil nil nil))
         (step (proof-proof-modus-ponens proof fact guard)))
      (cons step lib))))

(defun b1-array-scan-alist-not-string (lib alist)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((xs (b1-array-scan-literal-field alist 1))
         (test (list *proof-consp* xs))
         (cons (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (law (proof-proof-fact proof "consp-not-stringp" (list (list *library-x* xs))))
         (yes (proof-proof-modus-ponens proof law cons))
         (literal (proof-step-first alist))
         (normalized (b1-logic-bookproof-normalize
                      lib literal (list atom) (list *b1-arrays-alistp* *b1-logic-atom* *b1-logic-eq* *proof-not*)
                      nil nil nil nil))
         (empty (proof-proof-rewrite proof alist normalized '(1)))
         (no (b1-logic-bookproof-normalize-proof
              lib (proof-neg (list *b1-logic-stringp* *proof-false*)) nil (list *proof-not*) nil nil))
         (back (proof-proof-symmetric proof empty))
         (no (proof-proof-rewrite proof no back '(1 1 1))))
      (proof-proof-cases proof test yes no))))

(defun b1-array-scan-array-scan-fields (lib premise)
  (proof-with-checked-results
      ((literal (proof-step-first premise))
       (parts (proof-list-of-length literal 3))
       (array-name (cadr parts))
       (items (caddr parts))
       (fields (b1-arrays-array-checks lib premise))
       (limit (list *library-car* (list *b1-arrays-dimensions* array-name items)))
       (size (b1-logic-bookproof-normalize
              lib limit nil (list *b1-arrays-dimensions* *b1-arrays-header*) nil nil nil nil))
       (size-field (proof-term-at fields 5))
       (integral (library-library-transport-argument lib size-field size 1))
       (default (list *b1-arrays-default* array-name items))
       (bounded (b1-array-scan-bounded-scan lib))
       (lib (cdr bounded))
       (proof (library-library-proof lib))
       (rule (proof-proof-fact proof (car bounded)
                               (list (list *b1-arrays-name* array-name) (list *b1-arrays-l* items)
                                     (list *b1-arrays-i* *proof-zero*) (list *b1-arrays-j* limit)
                                     (list *b1-arrays-d* default))))
       (integer-zero (library-library-type-of lib *proof-zero* nil))
       (nonnegative-zero (library-library-cite lib "WEAK-REFLEXIVE" (list *proof-zero*) (list integer-zero)))
       (condition (b1-array-scan-literal-field rule 1))
       (alist (proof-term-at fields 1))
       (guard (b1-logic-bookproof-normalize-proof
               lib condition (list integer-zero integral nonnegative-zero alist) nil nil nil))
       (bounded (proof-proof-modus-ponens proof rule guard)))
    (cons (list fields size integral bounded) lib)))

(defun b1-array-scan-valid-compressed-array-consequence-branch
    (value tests lib premise scan forward reverse bound header-cons key size header array-name fields)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib)))
    (if (not (proof-is-call value *proof-cons*))
        (proof-with-checked-results
            ((normalized (b1-logic-bookproof-normalize lib value nil nil nil nil nil nil)))
          (library-library-transport-argument lib premise normalized 2))
      (proof-with-checked-results
          ((parts (proof-list-of-length value 3))
           (tail (caddr parts))
           (valid-tail (if (equal tail scan) forward reverse))
           (complete (b1-array-scan-bounded-cons lib value bound (list header-cons key valid-tail) nil))
           (alist (b1-array-scan-bounded-list-is-alist lib complete))
           (complete (proof-proof-rewrite proof complete size '(1 2)))
           (old (b1-logic-bookproof-normalize lib header nil (list *b1-arrays-header*) nil nil nil nil))
           (after (b1-logic-bookproof-normalize lib (list *b1-arrays-header* array-name value) nil
                                                (list *b1-arrays-header*) nil nil nil nil))
           (back-key (proof-proof-symmetric proof key))
           (matched (b1-arrays-header-at-front lib array-name value back-key))
           (back (proof-proof-symmetric proof after))
           (association (proof-proof-chain proof back (list matched old)))
           (array-type (b1-logic-bookproof-normalize
                        lib (list *b1-arrays-array* array-name value) nil (list *b1-arrays-array*)
                        (list (b1-logic-equal-to association)) nil nil t))
           (guard (b1-array-scan-literal-field array-type 2))
           (result (b1-logic-bookproof-normalize-proof lib guard (append fields (list alist complete)) nil nil nil)))
        (proof-proof-transport proof result array-type)))))

(defun b1-array-scan-valid-compressed-array-consequence-leaves
    (requests lib premise scan forward reverse bound header-cons key size header array-name fields)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((request (car requests))
         (step (b1-array-scan-valid-compressed-array-consequence-branch
                (car request) (cadr request) lib premise scan forward reverse bound header-cons key size header
                array-name fields))
         (rest (b1-array-scan-valid-compressed-array-consequence-leaves
                (cdr requests) lib premise scan forward reverse bound header-cons key size header array-name fields)))
      (cons (cons request step) rest))))

(defun b1-array-scan-valid-compressed-array-consequence (premise lib array-name call)
  (proof-with-checked-results
      ((premise-term (proof-step-first premise))
       (parts (proof-list-of-length premise-term 3))
       (original (caddr parts))
       (array-fields (b1-array-scan-array-scan-fields lib premise))
       (lib (cdr array-fields))
       (proof (library-library-proof lib))
       (fields (car (car array-fields)))
       (size (cadr (car array-fields)))
       (forward (cadddr (car array-fields)))
       (header (list *b1-arrays-header* array-name original))
       (known-cons (b1-arrays-header-exists lib (list *library-implies* premise-term (list *proof-consp* header))))
       (header-cons (proof-proof-modus-ponens proof known-cons premise))
       (key (b1-arrays-header-key-from-cons lib header header-cons))
       (lib (cdr key))
       (forward-term (proof-step-first forward))
       (parts (proof-list-of-length forward-term 3))
       (scan (cadr parts))
       (bound (caddr parts))
       (empty (b1-logic-bookproof-normalize-proof
               lib (list *b1-arrays-bounded* *proof-false* bound) nil
               (list *b1-arrays-bounded* *b1-logic-atom* *b1-array-scan-null* *b1-logic-eq* *proof-not*) nil nil))
       (reverse (b1-array-scan-bounded-reverse lib forward empty))
       (lib (cdr reverse))
       (proof (library-library-proof lib))
       (alist (b1-array-scan-bounded-list-is-alist lib forward))
       (not-string (b1-array-scan-alist-not-string lib alist))
       (reversal (b1-logic-bookproof-normalize lib (list *b1-array-scan-reverse* scan) (list not-string)
                                               (list *b1-array-scan-reverse*) nil nil nil nil))
       (reverse (library-library-transport-argument lib (car reverse) reversal 1))
       (opened (b1-logic-bookproof-normalize lib call nil (list *b1-arrays-compress*) nil nil nil nil))
       (value (b1-array-scan-literal-field opened 2))
       (template (list *b1-arrays-array* array-name *proof-result*))
       (requests (proof-proof-by-value-leaves proof value nil))
       (leaves (b1-array-scan-valid-compressed-array-consequence-leaves
                requests lib premise scan forward reverse bound header-cons (car key) size header array-name fields))
       (result (proof-proof-by-value proof value template leaves nil))
       (step (library-library-transport-argument lib result opened 2)))
    (cons step lib)))

(defun b1-array-scan-valid-compressed-array (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (answer (b1-array-scan-valid-compressed-array-consequence premise lib (cadr claim) (caddr claim)))
       (lib (cdr answer))
       (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car answer))))
    (cons step lib)))

(defun b1-array-scan-source-association (key items default fallback)
  (let ((pair (list *b1-arrays-assoc* key items)))
    (proof-ite (proof-eq pair *proof-false*) fallback
               (proof-ite (proof-eq (list *library-cdr* pair) default) fallback pair))))

(defun b1-array-scan-pair-lookup-equation (lib call comparison key)
  (b1-logic-bookproof-normalize
   lib call (list comparison) (list *b1-arrays-assoc* *b1-logic-endp* *b1-logic-atom* *proof-not*)
   (list (b1-logic-equal-to key)) nil nil nil))

(defun b1-array-scan-scan-lookup-reversed (lib source scan-equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((moved (b1-revappend-lift-argument lib source scan-equation 1))
         (right (b1-array-scan-literal-field moved 2))
         (first-argument (proof-term-at right 1)))
      (if (proof-is-call first-argument *b1-arrays-scan*)
          moved
        (proof-with-checked-results ((opened (b1-revappend-open-list lib right nil)))
          (proof-proof-chain proof moved (list opened)))))))

(defun b1-array-scan-scan-lookup-equation (lib expected scan-equation reversed-order kept)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-list-of-length expected 3)))
      (if reversed-order
          (proof-with-checked-results
              ((moved (b1-array-scan-scan-lookup-reversed lib (caddr parts) scan-equation)))
            (b1-revappend-lift-argument lib expected moved 2))
        (proof-with-checked-results
            ((lookup (b1-revappend-lift-argument lib expected scan-equation 2)))
          (if kept
              (proof-with-checked-results
                  ((kept (proof-list-of-length kept 2))
                   (right (b1-array-scan-literal-field lookup 2))
                   (selected (b1-array-scan-pair-lookup-equation lib right (car kept) (cadr kept))))
                (proof-proof-chain proof lookup (list selected)))
            (proof-with-checked-results ((right (b1-array-scan-literal-field scan-equation 2)))
              (if (equal right *proof-false*)
                  (proof-with-checked-results
                      ((right (b1-array-scan-literal-field lookup 2))
                       (opened (b1-revappend-open-list lib right nil)))
                    (proof-proof-chain proof lookup (list opened)))
                lookup))))))))

(defun b1-array-scan-distinct-ordered-keys (lib strict type-right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first strict))
         (parts (proof-list-of-length literal 3))
         (same (proof-eq (cadr parts) (caddr parts)))
         (assumed (proof-proof-assume proof same t))
         (impossible (proof-proof-rewrite proof strict assumed '(1 1)))
         (irreflexive (library-library-cite lib "WEAK-REFLEXIVE" (list (caddr parts)) (list type-right)))
         (step (proof-proof-cut proof impossible irreflexive)))
      (proof-proof-front proof step (proof-neg same)))))

(defun b1-array-scan-after-successor (lib lower type-i type-k)
  (let ((proof (library-library-proof lib))
        (evidence (list type-i type-k))
        (gap (library-diff *b1-array-scan-k* *b1-arrays-i*)))
    (proof-with-checked-results
        ((comparison (library-library-comparison lib *b1-arrays-i* *b1-array-scan-k* evidence))
         (positive-gap (proof-proof-rewrite proof lower comparison '(1)))
         (gap-type (library-library-type-of lib gap evidence))
         (discrete (b1-arithmetic-integer-discrete lib positive-gap gap-type))
         (sums (b1-arithmetic-number-sums-init lib))
         (lib (b1-arithmetic-number-sums-library sums))
         (discrete-test (b1-array-scan-literal-field discrete 1))
         (comparison (b1-arithmetic-number-sums-comparison-equation
                      sums discrete-test (library-lt *b1-array-scan-k* *b1-array-scan-next*) evidence))
         (step (library-inherited proof-proof-rewrite lib discrete comparison '(1 1))))
      (cons step lib))))

(defun b1-array-scan-scan-association-base (equation fields lib below reversed-order result claim)
  (if below
      (b1-array-scan-scan-lookup-equation lib result equation reversed-order nil)
    (let ((proof (library-library-proof lib))
          (i *b1-arrays-i*)
          (j *b1-arrays-j*)
          (k *b1-array-scan-k*)
          (stop *b1-array-scan-stop*))
      (proof-with-checked-results
          ((fields (proof-list-of-length fields 6))
           (type-i (car fields))
           (type-j (cadr fields))
           (type-k (caddr fields))
           (lower (nth 4 fields))
           (upper (nth 5 fields))
           (interval (library-library-cite lib "WEAK-THEN-LESS" (list i k j)
                                           (list type-i type-k type-j lower upper)))
           (types (list type-i type-j))
           (comparison (library-library-comparison lib i j types))
           (bigger (proof-proof-rewrite proof interval comparison '(1)))
           (typed-gap (library-library-type-of lib (cadr stop) types))
           (normalized (b1-logic-bookproof-normalize lib stop (list bigger typed-gap)
                                                     (list *b1-logic-zp* *proof-not*) nil nil nil nil))
           (outside (b1-logic-bookproof-normalize-proof lib (proof-neg stop) nil (list *proof-not*)
                                                         (list (b1-logic-equal-to normalized)) nil))
           (stopped (proof-proof-assume proof stop t)))
        (b1-logic-bookproof-contradiction lib stopped outside claim)))))

(defun b1-array-scan-scan-association-step-inherit
    (equation bindings next-limits comparison pair-key lib result reversed-order formula decrease new-types)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((child (b1-array-scan-scan-hypothesis lib formula decrease bindings (append new-types next-limits)))
         (child (if (and reversed-order pair-key)
                    (proof-with-checked-results
                        ((acc (assoc-equal *b1-array-scan-acc* bindings)))
                      (if (not acc)
                          '(:failure "failure" "")
                        (proof-with-checked-results
                            ((acc-lookup (list *b1-arrays-assoc* *b1-array-scan-k* (cdr acc)))
                             (changed (b1-array-scan-pair-lookup-equation lib acc-lookup comparison pair-key)))
                          (proof-proof-rewrite-first proof child changed))))
                  child))
         (reduced (b1-array-scan-scan-lookup-equation
                   lib result equation reversed-order (and pair-key (list comparison pair-key)))))
      (proof-proof-chain proof reduced (list child)))))

(defun b1-array-scan-scan-association-step-moving-past-other-discard
    (equation lib ordinary next-limits result reversed-order formula decrease new-types)
  (b1-array-scan-scan-association-step-inherit
   equation ordinary next-limits nil nil lib result reversed-order formula decrease new-types))

(defun b1-array-scan-scan-association-step-moving-past-other-keep
    (equation present retained lib alist extended comparison next-limits result reversed-order formula decrease new-types)
  (declare (ignore retained))
  (proof-with-checked-results
      ((pair (b1-array-scan-lookup-pair lib alist present))
       (pair-key (b1-array-scan-lookup-key lib pair))
       (lib (cdr pair-key))
       (step (b1-array-scan-scan-association-step-inherit
              equation extended next-limits comparison (car pair-key) lib result reversed-order formula decrease new-types)))
    (cons step lib)))

(defun b1-array-scan-scan-association-step-moving-past-other
    (comparison next-limits lib alist ordinary extended result reversed-order formula decrease new-types)
  (proof-with-checked-results
      ((tests (b1-array-scan-scan-paths-tests lib))
       (missing (car tests))
       (present (cadr tests))
       (default (caddr tests))
       (retained (cadddr tests))
       (empty (b1-array-scan-scan-paths-reduction (list missing) lib))
       (empty (b1-array-scan-scan-association-step-moving-past-other-discard
               empty lib ordinary next-limits result reversed-order formula decrease new-types))
       (same (b1-array-scan-scan-paths-reduction (list present default) lib))
       (same (b1-array-scan-scan-association-step-moving-past-other-discard
              same lib ordinary next-limits result reversed-order formula decrease new-types))
       (found (b1-array-scan-scan-paths-reduction (list present retained) lib))
       (found (b1-array-scan-scan-association-step-moving-past-other-keep
               found present retained lib alist extended comparison next-limits
               result reversed-order formula decrease new-types))
       (lib (cdr found))
       (step (b1-array-scan-scan-paths lib empty same (car found))))
    (cons step lib)))

(defun b1-array-scan-scan-association-step-earlier-lookup
    (equation bindings key lib earlier-name new-types earlier same result reversed-order)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((law (proof-proof-fact proof earlier-name (table-items bindings)))
         (condition (b1-array-scan-literal-field law 1))
         (guard (b1-logic-bookproof-normalize-proof lib condition (append new-types (list earlier)) nil nil nil))
         (known (proof-proof-modus-ponens proof law guard))
         (known (if key
                    (proof-with-checked-results
                        ((right (b1-array-scan-literal-field known 2))
                         (fixed (b1-array-scan-pair-lookup-equation lib right same key)))
                      (proof-proof-chain proof known (list fixed)))
                  known))
         (reduced (b1-array-scan-scan-lookup-equation lib result equation reversed-order nil)))
      (proof-proof-chain proof reduced (list known)))))

(defun b1-array-scan-scan-association-step-expected-case (tests lib expected matching)
  (b1-logic-bookproof-normalize lib expected tests nil (list (b1-logic-equal-to matching)) nil nil nil))

(defun b1-array-scan-scan-association-step-if-missing
    (missing other lib ordinary earlier-name new-types earlier same result reversed-order expected matching)
  (let ((proof (library-library-proof lib))
        (tests (cons missing other)))
    (proof-with-checked-results
        ((equation (b1-array-scan-scan-paths-reduction tests lib))
         (lookup (b1-array-scan-scan-association-step-earlier-lookup
                  equation ordinary nil lib earlier-name new-types earlier same result reversed-order))
         (expected (b1-array-scan-scan-association-step-expected-case tests lib expected matching))
         (back (proof-proof-symmetric proof expected)))
      (proof-proof-chain proof lookup (list back)))))

(defun b1-array-scan-scan-association-step-matching
    (lib earlier-name new-types earlier same result reversed-order expected matching alist ordinary extended)
  (proof-with-checked-results
      ((tests (b1-array-scan-scan-paths-tests lib))
       (missing (car tests))
       (present (cadr tests))
       (default (caddr tests))
       (retained (cadddr tests))
       (skipped (b1-array-scan-scan-association-step-if-missing
                 missing nil lib ordinary earlier-name new-types earlier same result reversed-order expected matching))
       (at-default (b1-array-scan-scan-association-step-if-missing
                    present (list default) lib ordinary earlier-name new-types earlier same result reversed-order
                    expected matching))
       (equation (b1-array-scan-scan-paths-reduction (list present retained) lib))
       (pair (b1-array-scan-lookup-pair lib alist present))
       (pair-key (b1-array-scan-lookup-key lib pair))
       (lib (cdr pair-key))
       (proof (library-library-proof lib))
       (kept (if reversed-order
                 (b1-array-scan-scan-association-step-earlier-lookup
                  equation extended (car pair-key) lib earlier-name new-types earlier same result reversed-order)
               (b1-array-scan-scan-lookup-equation lib result equation reversed-order (list same (car pair-key)))))
       (expected (b1-array-scan-scan-association-step-expected-case (list present retained) lib expected matching))
       (back (proof-proof-symmetric proof expected))
       (kept (proof-proof-chain proof kept (list back)))
       (step (b1-array-scan-scan-paths lib skipped at-default kept)))
    (cons step lib)))

(defun b1-array-scan-scan-association-step
    (progress fields lib below reversed-order result formula ordinary extended)
  (let ((proof (library-library-proof lib))
        (i *b1-arrays-i*)
        (k *b1-array-scan-k*)
        (next *b1-array-scan-next*))
    (proof-with-checked-results
        ((progress (proof-list-of-length progress 4))
         (advance (cadr progress))
         (decrease (caddr progress))
         (next-type (cadddr progress))
         (prefix (if (< (len fields) 4)
                     '(:failure "failure" "")
                   (take 4 fields)))
         (type-i (car prefix))
         (type-j (cadr prefix))
         (type-k (caddr prefix))
         (alist (cadddr prefix))
         (interval (nthcdr 4 fields))
         (new-types (list next-type type-j type-k alist)))
      (if below
          (proof-with-checked-results
              ((interval (proof-list-of-length interval 1))
               (smaller (car interval))
               (next-limit (library-library-cite lib "LESS-TRANSITIVE" (list k i next)
                                                 (list type-k type-i next-type smaller advance)))
               (comparison (b1-array-scan-distinct-ordered-keys lib smaller type-i)))
            (b1-array-scan-scan-association-step-moving-past-other
             comparison (list next-limit) lib alist ordinary extended result reversed-order formula decrease new-types))
        (proof-with-checked-results
            ((interval (proof-list-of-length interval 2))
             (lower (car interval))
             (upper (cadr interval))
             (equal-key (proof-eq k i))
             (same (proof-proof-assume proof equal-key t))
             (strict (b1-arithmetic-integer-compare lib k i (list type-k type-i)))
             (strict (proof-proof-discharge proof strict lower))
             (different (proof-proof-assume proof equal-key nil))
             (after-successor (b1-array-scan-after-successor lib strict type-i type-k))
             (lib (cdr after-successor))
             (later (b1-array-scan-scan-association-step-moving-past-other
                     different (list (car after-successor) upper) lib alist ordinary extended
                     result reversed-order formula decrease new-types))
             (lib (cdr later))
             (proof (library-library-proof lib))
             (back (proof-proof-symmetric proof same))
             (earlier (proof-proof-rewrite proof advance back '(1 1)))
             (pair (list *b1-arrays-assoc* k *b1-arrays-l*))
             (matching (b1-revappend-lift-argument lib pair same 1)))
          (cons (list equal-key (car later) same earlier matching alist new-types) lib))))))

(defun b1-array-scan-scan-association-prepare (lib reversed-order below)
  (let* ((suffix (if reversed-order "REVERSE" "FORWARD"))
         (tag (concatenate 'string "COMPRESS11-" (if below "BELOW-" "LOOKUP-") suffix))
         (name (proof-sym (concatenate 'string "SELF-" tag) "ACL2")))
    (if (assoc-equal name (library-inherited proof-proof-facts lib))
        (list name)
      (let* ((i *b1-arrays-i*)
             (j *b1-arrays-j*)
             (k *b1-array-scan-k*)
             (acc *b1-array-scan-acc*)
             (scan *b1-array-scan-scan-call*)
             (source (if reversed-order (list *b1-array-scan-revappend* scan acc) scan))
             (result (list *b1-arrays-assoc* k source))
             (fallback (if reversed-order (list *b1-arrays-assoc* k acc) *proof-false*))
             (common (list (library-integer i) (library-integer j) (library-integer k)
                           (list *b1-arrays-alistp* *b1-arrays-l*)))
             (guards (if below (list (library-lt k i))
                       (list (proof-neg (library-lt k i)) (library-lt k j))))
             (expected (if below fallback
                         (b1-array-scan-source-association k *b1-arrays-l* *b1-arrays-d* fallback)))
             (claim (proof-eq result expected))
             (formula (list *library-implies* (b1-array-scan-conjunction (append common guards)) claim))
             (ordinary (list (cons i *b1-array-scan-next*)))
             (extended (if reversed-order
                           (append ordinary (list (cons acc (list *proof-cons* *b1-array-scan-pair* acc))))
                         ordinary)))
        (proof-with-checked-results
            ((preparation (b1-array-scan-prove-scan-prepare lib formula))
             (fields (caddr preparation))
             (base (b1-array-scan-scan-association-base (cadddr preparation) fields lib below reversed-order result claim))
             (step (b1-array-scan-scan-association-step
                    (nth 4 preparation) fields lib below reversed-order result formula ordinary extended)))
          (list name tag formula ordinary extended result expected preparation base step))))))

(defun b1-array-scan-scan-association-install (work step lib reversed-order)
  (let* ((formula (caddr work))
         (ordinary (cadddr work))
         (bindings (if reversed-order (list ordinary (nth 4 work)) (list ordinary))))
    (proof-with-checked-results
        ((proof (b1-array-scan-prove-scan lib formula (nth 7 work) (nth 8 work) step bindings))
         (lib (library-library-lemma lib (cadr work) formula proof nil)))
      (cons (car work) lib))))

(defun b1-array-scan-scan-association-finish-step (work progress named reversed-order)
  (proof-with-checked-results
      ((have (b1-array-scan-scan-association-step-matching
              (cdr named) (car named) (nth 6 progress) (cadddr progress) (caddr progress)
              (nth 5 work) reversed-order (nth 6 work) (nth 4 progress) (nth 5 progress)
              (cadddr work) (nth 4 work)))
       (lib (cdr have))
       (step (library-inherited proof-proof-cases lib (car progress) (car have) (cadr progress))))
    (b1-array-scan-scan-association-install work step lib reversed-order)))

; The nonmatching branch is proved before the below-range lemma is installed.
(mutual-recursion
 (defun b1-array-scan-scan-association-with-preparation (n work lib reversed-order below)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "b1-array-scan-scan-association-with-preparation"))
         ((failure-p work) work)
         ((endp (cdr work)) (cons (car work) lib))
         (t (let* ((step (nth 9 work))
                   (lib (cdr step)))
              (if below
                  (b1-array-scan-scan-association-install work (car step) lib reversed-order)
                (proof-with-checked-results
                    ((named (b1-array-scan-scan-association (1- n) lib reversed-order t)))
                  (b1-array-scan-scan-association-finish-step work (car step) named reversed-order)))))))
 (defun b1-array-scan-scan-association (n lib reversed-order below)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "b1-array-scan-scan-association")
     (b1-array-scan-scan-association-with-preparation
      (1- n) (b1-array-scan-scan-association-prepare lib reversed-order below) lib reversed-order below))))

(defun b1-array-scan-read-compressed-array-consequence-surviving
    (reversed-order lib ordinary integer-zero integer-limit integer-index fields lower upper index)
  (proof-with-checked-results
      ((bindings (if reversed-order (append ordinary (list (list *b1-array-scan-acc* *proof-false*))) ordinary))
       (named (b1-array-scan-scan-association 1000000 lib reversed-order nil))
       (lib (cdr named))
       (proof (library-library-proof lib))
       (law (proof-proof-fact proof (car named) bindings))
       (condition (b1-array-scan-literal-field law 1))
       (alist (proof-term-at fields 1))
       (guard (b1-logic-bookproof-normalize-proof
               lib condition (list integer-zero integer-limit integer-index alist lower upper) nil nil nil))
       (found (proof-proof-modus-ponens proof law guard))
       (found (if reversed-order
                  (proof-with-checked-results
                      ((empty (b1-revappend-open-list lib (list *b1-arrays-assoc* index *proof-false*) nil)))
                    (proof-proof-rewrite-first proof found empty))
                found)))
    (cons found lib)))

(defun b1-array-scan-read-compressed-array-consequence-branch
    (value tests lib array-name index index-not-header header-key scan forward reverse reverse-open
           original read-guard default original-read)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib))
        (call (list *b1-arrays-read* array-name value index)))
    (if (not (proof-is-call value *proof-cons*))
        (proof-with-checked-results
            ((normalized (b1-logic-bookproof-normalize lib value nil nil nil nil nil nil)))
          (b1-revappend-lift-argument lib call normalized 2))
      (proof-with-checked-results
          ((lookup (b1-array-scan-pair-lookup-equation
                    lib (list *b1-arrays-assoc* index value) index-not-header header-key))
           (tail (proof-term-at value 2))
           (lookup (if (equal tail scan)
                       (proof-proof-chain proof lookup (list forward))
                     (proof-with-checked-results
                         ((changed (proof-proof-rewrite proof lookup reverse-open '(1 2 2))))
                       (proof-proof-chain proof changed (list reverse)))))
           (back (proof-proof-symmetric proof header-key))
           (headers (b1-arrays-header-at-front lib array-name value back))
           (defaults (b1-arrays-field-equation lib *b1-arrays-default* array-name value original headers))
           (rules (list (b1-logic-equal-to read-guard) (b1-logic-equal-to lookup) (b1-logic-equal-to defaults)))
           (test (proof-eq (list *library-cdr* (list *b1-arrays-assoc* index original)) default))
           (same (proof-proof-assume proof test t))
           (goal (proof-eq call original-read))
           (reducers (list *b1-arrays-read* *b1-array-scan-null* *b1-logic-eq* *proof-not*))
           (yes (b1-logic-bookproof-case-proof lib goal (list same) reducers
                                              (append rules (list (b1-logic-equal-to same))) 16))
           (different (proof-proof-assume proof test nil))
           (no (b1-logic-bookproof-case-proof lib goal (list different) reducers rules 16)))
        (proof-proof-cases proof test yes no)))))

(defun b1-array-scan-read-compressed-array-consequence-leaves
    (requests lib array-name index index-not-header header-key scan forward reverse reverse-open
              original read-guard default original-read)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((request (car requests))
         (step (b1-array-scan-read-compressed-array-consequence-branch
                (car request) (cadr request) lib array-name index index-not-header header-key scan forward reverse
                reverse-open original read-guard default original-read))
         (rest (b1-array-scan-read-compressed-array-consequence-leaves
                (cdr requests) lib array-name index index-not-header header-key scan forward reverse
                reverse-open original read-guard default original-read)))
      (cons (cons request step) rest))))

(defun b1-array-scan-read-compressed-array-consequence
    (premise lib array-name original compression index original-read)
  (proof-with-checked-results
      ((premise-fields (b1-logic-bookproof-split-conjuncts lib premise))
       (premise-fields (proof-list-of-length premise-fields 4))
       (array (car premise-fields))
       (integer-index (cadr premise-fields))
       (lower (caddr premise-fields))
       (upper (cadddr premise-fields))
       (array-fields (b1-array-scan-array-scan-fields lib array))
       (lib (cdr array-fields))
       (proof (library-library-proof lib))
       (fields (car (car array-fields)))
       (integer-limit (caddr (car array-fields)))
       (scan-bound (cadddr (car array-fields)))
       (bound (proof-step-first scan-bound))
       (bound (proof-list-of-length bound 3))
       (scan (cadr bound))
       (limit (caddr bound))
       (default (list *b1-arrays-default* array-name original))
       (header (list *b1-arrays-header* array-name original))
       (array-term (proof-step-first array))
       (header-fact (b1-arrays-header-exists lib (list *library-implies* array-term (list *proof-consp* header))))
       (header-cons (proof-proof-modus-ponens proof header-fact array))
       (header-key (b1-arrays-header-key-from-cons lib header header-cons))
       (lib (cdr header-key))
       (index-not-header (b1-arrays-integer-key-not-header lib integer-index))
       (read-guard (b1-arrays-integer-read-guard lib integer-index))
       (ordinary (list (list *b1-arrays-name* array-name) (list *b1-arrays-l* original)
                       (list *b1-arrays-i* *proof-zero*) (list *b1-arrays-j* limit)
                       (list *b1-arrays-d* default) (list *b1-array-scan-k* index)))
       (integer-zero (library-library-type-of lib *proof-zero* nil))
       (forward (b1-array-scan-read-compressed-array-consequence-surviving
                 nil lib ordinary integer-zero integer-limit integer-index fields lower upper index))
       (lib (cdr forward))
       (reverse (b1-array-scan-read-compressed-array-consequence-surviving
                 t lib ordinary integer-zero integer-limit integer-index fields lower upper index))
       (lib (cdr reverse))
       (proof (library-library-proof lib))
       (alist (b1-array-scan-bounded-list-is-alist lib scan-bound))
       (not-string (b1-array-scan-alist-not-string lib alist))
       (reverse-open (b1-logic-bookproof-normalize lib (list *b1-array-scan-reverse* scan) (list not-string)
                                                    (list *b1-array-scan-reverse*) nil nil nil nil))
       (opened (b1-logic-bookproof-normalize lib compression nil (list *b1-arrays-compress*) nil nil nil nil))
       (value (b1-array-scan-literal-field opened 2))
       (template (proof-eq (list *b1-arrays-read* array-name *proof-result* index) original-read))
       (requests (proof-proof-by-value-leaves proof value nil))
       (leaves (b1-array-scan-read-compressed-array-consequence-leaves
                requests lib array-name index index-not-header (car header-key) scan (car forward) (car reverse)
                reverse-open original read-guard default original-read))
       (chosen (proof-proof-by-value proof value template leaves nil))
       (back (proof-proof-symmetric proof opened))
       (step (proof-proof-rewrite-result proof chosen back template *proof-result*)))
    (cons step lib)))

(defun b1-array-scan-read-compressed-array (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (conclusion (proof-list-of-length (caddr parts) 3))
       (read (proof-list-of-length (cadr conclusion) 4))
       (compression (proof-list-of-length (caddr read) 3))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (answer (b1-array-scan-read-compressed-array-consequence
                premise lib (cadr read) (caddr compression) (caddr read) (cadddr read) (caddr conclusion)))
       (lib (cdr answer))
       (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car answer))))
    (cons step lib)))
