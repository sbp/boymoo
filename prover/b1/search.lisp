(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-search-iff* (proof-sym "IFF" "ACL2"))

(defconst *b1-search-small-definitions*
  (list (proof-sym "BOOL-FIX" "ACL2")
        (proof-sym "BOOLEANP" "ACL2")
        (proof-sym "CASE-SPLIT" "ACL2")
        (proof-sym "DOUBLE-REWRITE" "ACL2")
        (proof-sym "FIX" "ACL2")
        (proof-sym "FORCE" "ACL2")
        (proof-sym "HIDE" "ACL2")
        *b1-search-iff*
        (proof-sym "IFIX" "ACL2")
        *library-implies*
        (proof-sym "MV-LIST" "ACL2")
        *library-natp*
        (proof-sym "NFIX" "ACL2")
        (proof-sym "POSP" "ACL2")
        (proof-sym "SYNP" "ACL2")
        (proof-sym "ZIP" "ACL2")
        (proof-sym "ZP" "ACL2")
        (proof-cl "=")
        *b1-logic-atom*
        *b1-logic-endp*
        *b1-logic-eq*
        *b1-logic-eql*
        *proof-not*
        (proof-cl "NULL")))

(mutual-recursion
 (defun b1-search-subterms (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cons term
         (if (and (consp term)
                  (proof-compound term)
                  (not (proof-is-call term *proof-quote*)))
             (b1-search-subterms-arguments (cdr term))
           nil)))
 (defun b1-search-subterms-arguments (arguments)
   (declare (xargs :measure (* 2 (acl2-count arguments))))
   (if (endp arguments)
       nil
     (append (b1-search-subterms (car arguments))
             (b1-search-subterms-arguments (cdr arguments))))))

(defun b1-search-key (term)
  (cond ((integerp term)
         '(:failure "failure" ""))
        ((rationalp term)
         '(:failure "failure" ""))
        ((eq term t)
         '(:failure "failure" ""))
        ((stringp term)
         (if (equal term "")
             '(:failure "failure" "")
           (list (subseq term 0 1) :none)))
        ((consp term)
         (let ((first (cadr term)))
           (list (car term) (if (and (consp first) (proof-compound first))
                               (car first)
                             :none))))
        (t '(:failure "failure" ""))))

(defun b1-search-make-rule (name term path)
  (list :b1-rule name term path))

(defun b1-search-rule-name (rule)
  (cadr rule))

(defun b1-search-rule-term (rule)
  (caddr rule))

(defun b1-search-rule-path (rule)
  (cadddr rule))

(defund b1-search-rule-conjunct (proof result step)
  (proof-with-checked-results
      ((parts (proof-proof-conjunct proof result)))
    (let ((index (if (< step 0) (+ (len parts) step) step)))
      (if (< index 0)
          '(:failure "failure" "")
        (proof-term-at parts index)))))

(defund b1-search-rule-consequence (proof result condition)
  (proof-proof-modus-ponens proof result condition))

(defun b1-search-rule-proof-follow (path proof result condition)
  (if (endp path)
      result
    (if (equal (car path) "implies")
        (proof-with-checked-results
            ((literal (b1-logic-step-first result))
             (term (proof-term-at literal 1)))
          (let ((reply (assoc-equal term condition)))
            (if reply
                (proof-with-checked-results
                    ((step (cdr reply))
                     (next (b1-search-rule-consequence proof result step)))
                  (b1-search-rule-proof-follow (cdr path) proof next condition))
              (list :request term))))
      (proof-with-checked-results
          ((next (b1-search-rule-conjunct proof result (car path))))
        (b1-search-rule-proof-follow (cdr path) proof next condition)))))

(defund b1-search-rule-instance (proof rule bindings)
  (proof-proof-fact proof (b1-search-rule-name rule) (table-items bindings)))

(defun b1-search-rule-proof (rule lib bindings condition)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((result (b1-search-rule-instance proof rule bindings)))
      (b1-search-rule-proof-follow (b1-search-rule-path rule) proof result condition))))

(defun b1-search-make-fact-index (claims equations)
  (list :b1-fact-index claims equations))

(defun b1-search-fact-index-claims (index)
  (cadr index))

(defun b1-search-fact-index-equations (index)
  (caddr index))

(defun b1-search-fact-index-logic-claims (index)
  (b1-search-fact-index-claims index))

(defun b1-search-application-p (term)
  (and (consp term) (proof-compound term) (not (proof-compound (car term)))))

(defun b1-search-fact-index-append-rule (index key rule)
  (table-put index key
               (append (table-get index key nil) (list rule))))

(defun b1-search-fact-index-add-rule (index name term path)
  (if (not (b1-search-application-p term))
      index
    (proof-with-checked-results
        ((key (b1-search-key term)))
      (let* ((rule (b1-search-make-rule name term path))
             (claims (b1-search-fact-index-append-rule
                      (b1-search-fact-index-claims index) key rule))
             (equations (b1-search-fact-index-equations index))
             (index (b1-search-make-fact-index claims equations)))
        (if (not (proof-is-call term *proof-equal*))
            index
          (proof-with-checked-results
              ((left (proof-term-at term 1)))
            (if (not (proof-compound left))
                index
              (proof-with-checked-results
                  ((head (proof-term-at left 0)))
                (if (proof-compound head)
                    index
                  (proof-with-checked-results
                      ((left-text (proof-write left))
                       (right (proof-term-at term 2))
                       (right-text (proof-write right)))
                    (if (<= (length left-text) (length right-text))
                        index
                      (proof-with-checked-results
                          ((key (b1-search-key left)))
                        (b1-search-make-fact-index
                         claims (b1-search-fact-index-append-rule
                                 equations key rule))))))))))))))

(defun b1-search-fact-index-add-collect (n index name term path)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n)
         '(:failure "Fuel" "b1-search-fact-index-add-collect"))
        ((and (< (len path) 6) (proof-is-call term *library-implies*))
         (proof-with-checked-results
             ((child (proof-term-at term 2))
              (index (b1-search-fact-index-add-collect
                      (1- n) index name child (append path (list "implies")))))
           (b1-search-fact-index-add-rule index name term path)))
        ((and (< (len path) 6) (proof-is-call term *proof-if*))
         (proof-with-checked-results
             ((otherwise (proof-term-at term 3)))
           (if (equal otherwise *proof-false*)
               (proof-with-checked-results
                   ((index (b1-search-fact-index-add-collect
                            (1- n) index name (cadr term) (append path (list 0))))
                    (index (b1-search-fact-index-add-collect
                            (1- n) index name (caddr term) (append path (list 1)))))
                 (b1-search-fact-index-add-rule index name term path))
             (b1-search-fact-index-add-rule index name term path))))
        (t (b1-search-fact-index-add-rule index name term path))))

(defun b1-search-fact-index-add (index name clause)
  (if (equal (len clause) 1)
      (b1-search-fact-index-add-collect 1000000 index name (car clause) nil)
    index))

(defun b1-search-fact-index-init-facts (facts definitions index)
  (if (endp facts)
      index
    (if (assoc-equal (caar facts) definitions)
        (b1-search-fact-index-init-facts (cdr facts) definitions index)
      (proof-with-checked-results
          ((index (b1-search-fact-index-add index (caar facts) (cdar facts))))
        (b1-search-fact-index-init-facts (cdr facts) definitions index)))))

(defun b1-search-fact-index-init (lib)
  (let ((proof (library-library-proof lib)))
    (b1-search-fact-index-init-facts
     (proof-proof-facts proof)
     (proof-proof-definitions proof)
     (b1-search-make-fact-index nil nil))))

(defund b1-search-fact-index-candidates (index term)
  (proof-with-checked-results
      ((key (b1-search-key term)))
    (let ((exact (reverse (table-get index key nil))))
      (if (eq (cadr key) :none)
          exact
        (append exact (reverse (table-get index (list (car key) :none) nil)))))))

(defun b1-search-quoted-set-field (text)
  (concatenate 'string "\""
               (text-replace (text-replace text "\\" "\\\\") "\"" "\\\"")
               "\""))

(defun b1-search-definition-keys (definitions)
  (if (endp definitions)
      nil
    (let* ((name (car definitions))
           (text (if (and (equal (car name) "sym") (stringp (cadr name))
                          (stringp (caddr name)) (endp (cdddr name)))
                     (concatenate 'string "(\"sym\" "
                                  (b1-search-quoted-set-field (cadr name)) " "
                                  (b1-search-quoted-set-field (caddr name)) ")")
                   (proof-datum-text name))))
      (cons (list text name) (b1-search-definition-keys (cdr definitions))))))

(defun b1-search-definition-values (keys)
  (if (endp keys)
      nil
    (cons (cadar keys) (b1-search-definition-values (cdr keys)))))

(defun b1-search-attempt-init (lib facts fuel definitions case-context)
  (list :b1-attempt lib facts fuel
        (if (endp definitions)
            *b1-search-small-definitions*
          (b1-search-definition-values
           (seq-sorted (b1-search-definition-keys
                       (proof-unique (append *b1-search-small-definitions* definitions))))))
        case-context))

(defun b1-search-attempt-lib (attempt)
  (cadr attempt))

(defun b1-search-attempt-facts (attempt)
  (caddr attempt))

(defun b1-search-attempt-fuel (attempt)
  (cadddr attempt))

(defun b1-search-attempt-definitions (attempt)
  (nth 4 attempt))

(defun b1-search-attempt-case-context (attempt)
  (nth 5 attempt))

(defun b1-search-attempt-with-lib (attempt lib)
  (list* :b1-attempt lib (cddr attempt)))

(defun b1-search-attempt-proof (attempt)
  (library-library-proof (b1-search-attempt-lib attempt)))

(defund b1-search-attempt-charge (attempt)
  (let* ((fuel (1- (b1-search-attempt-fuel attempt)))
         (attempt (list* :b1-attempt
                         (b1-search-attempt-lib attempt)
                         (b1-search-attempt-facts attempt)
                         fuel
                         (cddddr attempt))))
    (cons (if (< fuel 0)
              '(:failure "SearchBudgetExhausted" "")
            nil)
          attempt)))

(defun b1-search-unproved-p (x)
  (and (failure-p x)
       (or (equal (cadr x) "Unproved")
           (equal (cadr x) "SearchBudgetExhausted"))))

(defun b1-search-retry-p (x)
  (and (failure-p x) (equal (cadr x) "Unproved")))

; A search result carries its Library and remaining budget when a proof fails.
(defmacro b1-search-with-attempt-values (attempt bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (failure-p ,name)
             (cons ,name ,attempt)
           (b1-search-with-attempt-values ,attempt ,(cdr bindings) ,result))))))

(defmacro b1-search-with-attempt-result (attempt binding result)
  `(let* ((b1-search-result ,(cadr binding))
          (,(car binding) (car b1-search-result))
          (,attempt (cdr b1-search-result)))
     (if (failure-p ,(car binding))
         b1-search-result
       ,result)))

(defund b1-search-attempt-evidence (attempt proofs addition)
  (proof-with-checked-results
      ((first (b1-logic-step-first addition)))
    (let ((terms (append proofs (list addition))))
      (if (proof-is-call first *proof-if*)
          (proof-with-checked-results
              ((otherwise (proof-term-at first 3)))
            (if (equal otherwise *proof-false*)
                (proof-with-checked-results
                    ((conjuncts (b1-logic-bookproof-split-conjuncts
                                 (b1-search-attempt-lib attempt) addition)))
                  (append terms conjuncts))
              terms))
        terms))))

(defund b1-search-attempt-selector-formal (attempt head)
  (let* ((definitions (proof-proof-definitions (b1-search-attempt-proof attempt)))
         (definition (table-get definitions head (list nil *proof-nil*))))
    (proof-with-checked-results
        ((definition (proof-list-of-length definition 2)))
      (let ((formals (car definition))
            (body (cadr definition)))
        (if (not (proof-is-call body *proof-if*))
            nil
          (proof-with-checked-results
              ((test (proof-term-at body 1))
               (test (if (proof-is-call test *proof-not*)
                         (proof-term-at test 1)
                       test)))
            (if (not (proof-compound test))
                nil
              (proof-with-checked-results
                  ((operator (proof-term-at test 0)))
                (if (not (member-equal operator
                                       (list *proof-consp* *b1-logic-atom*
                                             *b1-logic-endp*)))
                    nil
                  (proof-with-checked-results
                      ((formal (proof-term-at test 1)))
                    (if (member-equal formal formals)
                        (proof-with-checked-results
                            ((index (seq-index formals formal)))
                          (1+ index))
                      nil)))))))))))

(defun b1-search-has-test (known term)
  (or (assoc-equal term known)
      (assoc-equal (proof-neg term) known)))

(defund b1-search-attempt-can-open (attempt term known)
  (proof-with-checked-results
      ((head (proof-term-at term 0))
       (slot (b1-search-attempt-selector-formal attempt head)))
    (and slot
         (proof-with-checked-results
             ((actual (proof-term-at term slot)))
           (if (or (proof-is-call actual *proof-cons*)
                   (proof-is-call actual *proof-quote*)
                   (b1-search-has-test known (list *proof-consp* actual))
                   (b1-search-has-test known (list *b1-logic-atom* actual))
                   (b1-search-has-test known (list *b1-logic-endp* actual)))
               t
             nil)))))

(defund b1-search-attempt-boolean-type (attempt term)
  (if (not (b1-search-application-p term))
      (cons nil attempt)
    (b1-search-with-attempt-values attempt
        ((slot (b1-search-attempt-selector-formal attempt (car term))))
      (if (not slot)
          (cons nil attempt)
        (b1-search-with-attempt-result attempt
            (charged (b1-search-attempt-charge attempt))
          (let ((result (b1-predicates-boolean-definition
                         (b1-search-attempt-lib attempt) term slot)))
            (cond ((b1-search-unproved-p result) (cons nil attempt))
                  ((failure-p result) (cons result attempt))
                  (t (cons (car result)
                           (b1-search-attempt-with-lib attempt (cdr result)))))))))))

(defun b1-search-attempt-boolean-truth (attempt term known)
  (b1-search-with-attempt-result attempt
      (boolean (b1-search-attempt-boolean-type attempt term))
    (let ((lib (b1-search-attempt-lib attempt)))
      (cons (and boolean
                 (let ((premise (assoc-equal term known)))
                   (if premise
                       (b1-logic-bookproof-boolean-value lib (cdr premise) boolean)
                     '(:failure "failure" ""))))
            attempt))))

(defun b1-search-attempt-structural-rule (attempt known)
  (declare (ignore attempt))
  (list :callback (list :b1-search-structural known)))

(defun b1-search-attempt-rewriting (attempt known)
  (declare (ignore attempt))
  (list :callback (list :b1-search-rewriting known)))

(defun b1-search-attempt-open (attempt term)
  (b1-search-with-attempt-result attempt
      (charged (b1-search-attempt-charge attempt))
    (let* ((lib (b1-search-attempt-lib attempt))
           (association (b1-records-association-step lib term)))
      (if (failure-p association)
          (cons association attempt)
        (let ((attempt (b1-search-attempt-with-lib attempt (cdr association))))
          (cons (or (car association)
                    (proof-proof-unfold (b1-search-attempt-proof attempt) term))
                attempt))))))

(defund b1-search-attempt-structural-rule-rule (term attempt known)
  (if (not (b1-search-application-p term))
      (cons nil attempt)
    (b1-search-with-attempt-values attempt
        ((open (b1-search-attempt-can-open attempt term known)))
      (if open
          (b1-search-attempt-open attempt term)
        (cons nil attempt)))))

(defun b1-search-attempt-truth-of-cons (attempt term known)
  (let ((proof (b1-search-attempt-proof attempt)))
    (proof-with-checked-results
        ((is-cons (or (table-get known (list *proof-consp* term) nil)
                      (and (proof-is-call term *proof-cons*)
                           (proof-proof-fact proof "consp-cons"
                                             (seq-zip (list *library-x* *library-y*)
                                                     (cdr term)))))))
      (and is-cons
           (let ((test (proof-eq term *proof-false*)))
             (proof-with-checked-results
                 ((assume (proof-proof-assume proof test t))
                  (impossible (proof-proof-rewrite proof is-cons assume '(1 1)))
                  (impossible (proof-proof-simplify-first proof impossible nil nil))
                  (not-nil (proof-proof-front proof impossible (proof-neg test)))
                  (nil-or-true (proof-proof-nil-or-true proof term)))
               (proof-proof-cut proof nil-or-true not-nil)))))))

(defun b1-search-attempt-anchors-visit (attempt terms seen)
  (if (endp terms)
      nil
    (let ((term (car terms)))
      (if (not (b1-search-application-p term))
          (b1-search-attempt-anchors-visit attempt (cdr terms) seen)
        (proof-with-checked-results
            ((slot (b1-search-attempt-selector-formal attempt (car term))))
          (if (not slot)
              (b1-search-attempt-anchors-visit attempt (cdr terms) seen)
            (proof-with-checked-results
                ((actual (proof-term-at term slot)))
              (if (or (proof-compound actual) (member-equal actual seen))
                  (b1-search-attempt-anchors-visit attempt (cdr terms) seen)
                (proof-with-checked-results
                    ((remaining (b1-search-attempt-anchors-visit
                                 attempt (cdr terms) (cons actual seen))))
                  (cons actual remaining))))))))))

(defun b1-search-attempt-anchors (attempt formula)
  (b1-search-attempt-anchors-visit attempt (b1-search-subterms formula) nil))

(defun b1-search-bindings-accumulate (pairs bindings)
  (if (endp pairs)
      bindings
    (b1-search-bindings-accumulate
     (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun b1-search-bindings (pairs)
  (b1-search-bindings-accumulate pairs nil))

(defun b1-search-subst-arguments (arguments bindings)
  (if (endp arguments)
      nil
    (proof-with-checked-results
        ((actual (proof-subst (car arguments) bindings))
         (rest (b1-search-subst-arguments (cdr arguments) bindings)))
      (cons actual rest))))

(defun b1-search-attempt-substitutions-pairs (formals actuals variable)
  (if (or (endp formals) (endp actuals))
      nil
    (let* ((formal (car formals))
           (actual (car actuals))
           (rest (b1-search-attempt-substitutions-pairs
                  (cdr formals) (cdr actuals) variable)))
      (if (or (proof-compound formal)
              (equal formal variable)
              (equal formal actual))
          rest
        (cons (list formal actual) rest)))))

(defun b1-search-attempt-substitutions-calls (calls arguments bindings slot variable tail base found)
  (if (endp calls)
      found
    (proof-with-checked-results
        ((actuals (b1-search-subst-arguments
                   (termination-call-actuals (car calls)) bindings))
         (selected (proof-term-at actuals (1- slot))))
      (let* ((pairs (and (equal selected tail)
                         (b1-search-attempt-substitutions-pairs
                          arguments actuals variable)))
             (candidate (and (equal (len pairs) 1) (append base pairs)))
             (found (if (and candidate (not (member-equal candidate found)))
                        (cons candidate found)
                      found)))
        (b1-search-attempt-substitutions-calls
         (cdr calls) arguments bindings slot variable tail base found)))))

(defun b1-search-attempt-substitutions-term (attempt term variable tail base found)
  (if (not (b1-search-application-p term))
      found
    (proof-with-checked-results
        ((slot (b1-search-attempt-selector-formal attempt (car term))))
      (if (not slot)
          found
        (proof-with-checked-results
            ((selected (proof-term-at term slot)))
          (if (not (equal selected variable))
              found
            (let* ((head (car term))
                   (definition (assoc-equal
                                head (proof-proof-definitions
                                      (b1-search-attempt-proof attempt))))
                   (formals (cadr definition))
                   (body (caddr definition))
                   (bindings (b1-search-bindings (seq-zip formals (cdr term)))))
              (proof-with-checked-results
                  ((calls (termination-recursive-calls
                           *termination-all* (list (list head formals body)))))
                (b1-search-attempt-substitutions-calls
                 calls (cdr term) bindings slot variable tail base found)))))))))

(defun b1-search-attempt-substitutions-visit (attempt terms variable tail base found)
  (if (endp terms)
      (reverse found)
    (proof-with-checked-results
        ((found (b1-search-attempt-substitutions-term
                 attempt (car terms) variable tail base found)))
      (b1-search-attempt-substitutions-visit
       attempt (cdr terms) variable tail base found))))

(defun b1-search-attempt-substitutions (attempt formula variable)
  (let* ((tail (list *library-cdr* variable))
         (base (list (list variable tail))))
    (b1-search-attempt-substitutions-visit
     attempt (b1-search-subterms formula) variable tail base (list base))))

(defund b1-search-next-definition-call (n terms definitions)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "b1-search-next-definition-call"))
        ((endp terms) nil)
        (t
         (let ((term (car terms)))
           (cond ((and (consp term) (proof-compound term)
                       (proof-compound (car term)))
                  (proof-with-checked-results
                      ((body (proof-term-at (car term) 2)))
                    (b1-search-next-definition-call
                     (1- n) (append (b1-search-subterms body) (cdr terms)) definitions)))
                 ((and (b1-search-application-p term)
                       (assoc-equal (car term) definitions))
                  (cons (car term) (cdr terms)))
                 (t (b1-search-next-definition-call (1- n) (cdr terms) definitions)))))))

(defund b1-search-definition-calls-visit (n terms definitions target)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-search-definition-calls-visit")
    (proof-with-checked-results
        ((next (b1-search-next-definition-call 1000000 terms definitions)))
      (cond ((not next) nil)
            ((equal (car next) target) t)
            (t
             (proof-with-checked-results
                 ((rest (b1-search-definition-calls-visit
                         (1- n) (cdr next) definitions target)))
               (if (eq target :none)
                   (cons (car next) rest)
                 rest)))))))

(defun b1-search-immediate-definitions-definition-calls (term lib)
  (b1-search-definition-calls-visit
   1000000 (b1-search-subterms term)
   (proof-proof-definitions (library-library-proof lib)) :none))

(defund b1-search-immediate-definition-p (head definitions)
  (proof-with-checked-results
      ((definition (proof-list-of-length (table-get definitions head nil) 2))
       (text (proof-write (cadr definition))))
    (and (<= (length text) 8500)
         (proof-with-checked-results
             ((recursive (b1-search-definition-calls-visit
                          1000000 (b1-search-subterms (cadr definition)) definitions head)))
           (not recursive)))))

(defund b1-search-immediate-definitions-visit (n terms definitions seen)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-search-immediate-definitions-visit")
    (proof-with-checked-results
        ((next (b1-search-next-definition-call 1000000 terms definitions)))
      (if (not next)
          nil
        (let ((head (car next)))
          (if (or (member-equal head seen)
                  (member-equal head *b1-search-small-definitions*))
              (b1-search-immediate-definitions-visit (1- n) (cdr next) definitions seen)
            (proof-with-checked-results
                ((short (b1-search-immediate-definition-p head definitions))
                 (rest (b1-search-immediate-definitions-visit
                        (1- n) (cdr next) definitions (cons head seen))))
              (if short (cons head rest) rest))))))))

(defun b1-search-immediate-definitions (lib formula)
  (b1-search-immediate-definitions-visit
   1000000 (b1-search-subterms formula)
   (proof-proof-definitions (library-library-proof lib)) nil))

; Normalization requests run against the current Library. Replaying a
; saved reply retains the proof and Library of one callback invocation.
(defun b1-search-attempt-normalize-result (attempt result)
  (cond ((failure-p result) (cons result attempt))
        ((b1-logic-branch-p result)
         (cons result (b1-search-attempt-with-lib
                       attempt (b1-logic-branch-library result))))
        (t (cons (car result) (b1-search-attempt-with-lib attempt (cdr result))))))

(defund b1-search-attempt-normalize-structural-proof-call (attempt lib goal known replies)
  (b1-logic-bookproof-normalize-proof-with-library
   lib goal (table-values known) (b1-search-attempt-definitions attempt)
   (list (b1-search-attempt-structural-rule attempt known)) nil replies))

(defun b1-search-attempt-normalize-structural-proof-visit
    (n attempt lib goal known replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "b1-search-attempt-normalize-structural-proof-visit") attempt)
    (let ((result (b1-search-attempt-normalize-structural-proof-call
                   attempt lib goal known replies)))
      (if (not (b1-logic-call-p result))
          (b1-search-attempt-normalize-result attempt result)
        (let* ((attempt (b1-search-attempt-with-lib
                         attempt (b1-logic-call-library result)))
               (reply (b1-search-attempt-structural-rule-rule
                       (b1-logic-call-term result) attempt known))
               (step (car reply))
               (attempt (cdr reply)))
          (if (failure-p step)
              reply
            (b1-search-attempt-normalize-structural-proof-visit
             (1- n) attempt lib goal known
             (append replies (list (cons step (b1-search-attempt-lib attempt)))))))))))

(defun b1-search-attempt-establish-normalize (attempt term known)
  (b1-search-with-attempt-result attempt
      (charged (b1-search-attempt-charge attempt))
    (b1-search-attempt-normalize-structural-proof-visit
     1000000 attempt (b1-search-attempt-lib attempt) term known nil)))

(defund b1-search-attempt-establish-truth (attempt term known)
  (if (and (b1-search-attempt-case-context attempt)
           (proof-is-call term *proof-equal*)
           (member-equal *proof-true* (cdr term)))
      (b1-search-with-attempt-values attempt
          ((actual (proof-term-at term (if (equal (cadr term) *proof-true*) 2 1))))
        (if (not (assoc-equal actual known))
            (cons nil attempt)
          (b1-search-with-attempt-result attempt
              (truth (b1-search-attempt-boolean-truth attempt actual known))
            (cons (if (and truth (equal (cadr term) *proof-true*))
                      (proof-proof-symmetric (b1-search-attempt-proof attempt) truth)
                    truth)
                  attempt))))
    (cons nil attempt)))

(defund b1-search-rule-match (rule term)
  (b1-logic-match (b1-search-rule-term rule) term nil))

(mutual-recursion
 (defun b1-search-attempt-establish-visit (n attempt term known depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "b1-search-attempt-establish-visit") attempt)
     (let ((existing (assoc-equal term known)))
       (if existing
           (cons (cdr existing) attempt)
         (b1-search-with-attempt-result attempt
             (truth (b1-search-attempt-establish-truth attempt term known))
           (if truth
               (cons truth attempt)
             (b1-search-with-attempt-values attempt
                 ((conjunction (and (proof-is-call term *proof-if*)
                                    (proof-term-at term 3))))
               (cond ((equal conjunction *proof-false*)
                      (b1-search-with-attempt-result attempt
                          (left (b1-search-attempt-establish-visit
                                 (1- n) attempt (cadr term) known depth))
                        (b1-search-with-attempt-result attempt
                            (right (b1-search-attempt-establish-visit
                                    (1- n) attempt (caddr term) known depth))
                          (cons (b1-logic-bookproof-normalize-proof
                                 (b1-search-attempt-lib attempt) term (list left right)
                                 nil nil nil)
                                attempt))))
                     ((and (proof-compound term) (consp term) (not (equal depth 0)))
                      (b1-search-with-attempt-values attempt
                          ((rules (b1-search-fact-index-candidates
                                   (b1-search-fact-index-claims
                                    (b1-search-attempt-facts attempt))
                                   term)))
                        (b1-search-attempt-establish-claims
                         (1- n) attempt term known depth rules)))
                     (t (b1-search-attempt-establish-normalize attempt term known))))))))))
 (defun b1-search-attempt-establish-claims (n attempt term known depth rules)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (cons '(:failure "Fuel" "b1-search-attempt-establish-claims") attempt))
         ((endp rules) (b1-search-attempt-establish-normalize attempt term known))
         (t
          (b1-search-with-attempt-values attempt
              ((match (b1-search-rule-match (car rules) term)))
            (if (not (car match))
                (b1-search-attempt-establish-claims
                 (1- n) attempt term known depth (cdr rules))
              (let* ((tried (b1-search-attempt-guarded-rule
                             (1- n) attempt (car rules) (cdr match) known (1- depth)))
                     (step (car tried))
                     (attempt (cdr tried)))
                (if (b1-search-retry-p step)
                    (b1-search-attempt-establish-claims
                     (1- n) attempt term known depth (cdr rules))
                  tried)))))))
 (defun b1-search-attempt-guarded-rule (n attempt rule bindings known depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "b1-search-attempt-guarded-rule") attempt)
     (b1-search-with-attempt-values attempt
         ((step (b1-search-rule-instance (b1-search-attempt-proof attempt) rule bindings)))
       (b1-search-attempt-guarded-path
        (1- n) attempt (b1-search-rule-path rule) step known depth))))
 (defun b1-search-attempt-guarded-path (n attempt path result known depth)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (cons '(:failure "Fuel" "b1-search-attempt-guarded-path") attempt))
         ((endp path) (cons result attempt))
         ((equal (car path) "implies")
          (b1-search-with-attempt-values attempt
              ((literal (b1-logic-step-first result))
               (test (proof-term-at literal 1)))
            (b1-search-with-attempt-result attempt
                (condition (b1-search-attempt-establish-visit
                            (1- n) attempt test known depth))
              (b1-search-with-attempt-values attempt
                  ((next (b1-search-rule-consequence
                          (b1-search-attempt-proof attempt) result condition)))
                (b1-search-attempt-guarded-path
                 (1- n) attempt (cdr path) next known depth)))))
         (t
          (b1-search-with-attempt-values attempt
              ((next (b1-search-rule-conjunct (b1-search-attempt-proof attempt) result (car path))))
            (b1-search-attempt-guarded-path
             (1- n) attempt (cdr path) next known depth))))))

(defund b1-search-attempt-establish (attempt term known depth)
  (b1-search-attempt-establish-visit 1000000 attempt term known depth))

(defund b1-search-attempt-try-guarded-rule (attempt rule bindings known)
  (b1-search-attempt-guarded-rule 1000000 attempt rule bindings known 1))

(defun b1-search-attempt-condition-candidates (attempt candidates known)
  (if (endp candidates)
      (cons nil attempt)
    (b1-search-with-attempt-values attempt
        ((key (b1-search-key (car candidates))))
      (if (not (assoc-equal key (b1-search-fact-index-claims
                                 (b1-search-attempt-facts attempt))))
          (b1-search-attempt-condition-candidates attempt (cdr candidates) known)
        (let ((result (b1-search-attempt-establish attempt (car candidates) known 1)))
          (if (b1-search-retry-p (car result))
              (b1-search-attempt-condition-candidates (cdr result) (cdr candidates) known)
            result))))))

(defun b1-search-attempt-condition (attempt term known)
  (let ((exact (or (table-get known term nil)
                   (table-get known (proof-neg term) nil))))
    (if exact
        (cons exact attempt)
      (b1-search-with-attempt-values attempt
          ((cons-truth (b1-search-attempt-truth-of-cons attempt term known)))
        (cond (cons-truth (cons cons-truth attempt))
              ((and (consp term) (proof-compound term))
               (b1-search-attempt-condition-candidates
                attempt (list term (proof-neg term)) known))
              (t (cons nil attempt)))))))

(defun b1-search-has-compound-arguments (arguments)
  (and (consp arguments)
       (or (proof-compound (car arguments))
           (b1-search-has-compound-arguments (cdr arguments)))))

(defun b1-search-attempt-select-equivalent-test (attempt conditional equivalence)
  (let ((result (b1-logic-bookproof-select-equivalent-test
                 (b1-search-attempt-lib attempt) conditional equivalence)))
    (if (failure-p result)
        (cons result attempt)
      (cons (car result) (b1-search-attempt-with-lib attempt (cdr result))))))

(defund b1-search-attempt-rewrite-test-match (rule test)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr (b1-search-rule-term rule)) 2)))
    (let ((pattern (car parts))
          (result (cadr parts)))
      (if (or (not (proof-compound pattern))
              (not (b1-search-has-compound-arguments (cdr pattern))))
          nil
        (proof-with-checked-results
            ((match (b1-logic-match pattern test nil)))
          (if (not (car match))
              nil
            (proof-with-checked-results
                ((rhs (proof-subst result (cdr match))))
              (if (member-equal test (b1-search-subterms rhs))
                  nil
                (proof-with-checked-results
                    ((text (proof-write rhs)))
                  (and (<= (length text) 3200) match))))))))))

(defun b1-search-attempt-rewrite-test-visit (attempt conditional test known rules)
  (if (endp rules)
      (cons nil attempt)
    (b1-search-with-attempt-values attempt
        ((match (b1-search-attempt-rewrite-test-match (car rules) test)))
      (if (not match)
          (b1-search-attempt-rewrite-test-visit attempt conditional test known (cdr rules))
        (b1-search-with-attempt-result attempt
            (charged (b1-search-attempt-charge attempt))
          (let* ((result (b1-search-attempt-try-guarded-rule
                          attempt (car rules) (cdr match) known))
                 (step (car result))
                 (attempt (cdr result)))
            (cond ((b1-search-retry-p step)
                   (b1-search-attempt-rewrite-test-visit
                    attempt conditional test known (cdr rules)))
                  ((failure-p step) result)
                  (t (b1-search-attempt-select-equivalent-test
                      attempt conditional step)))))))))

(defun b1-search-attempt-rewrite-test (attempt conditional known)
  (b1-search-with-attempt-values attempt
      ((test (proof-term-at conditional 1)))
    (if (or (not (proof-compound test)) (endp test)
            (b1-search-has-test known test))
        (cons nil attempt)
      (b1-search-attempt-rewrite-test-visit
       attempt conditional test known
       (reverse
        (table-get (b1-search-fact-index-claims (b1-search-attempt-facts attempt))
                     (list *b1-search-iff* (car test)) nil))))))

(defun b1-search-attempt-rewriting-evidence (term evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results
        ((literal (b1-logic-step-first (car evidence))))
      (if (not (proof-is-call literal *proof-equal*))
          (b1-search-attempt-rewriting-evidence term (cdr evidence))
        (proof-with-checked-results
            ((parts (proof-list-of-length (cdr literal) 2)))
          (if (not (equal (car parts) term))
              (b1-search-attempt-rewriting-evidence term (cdr evidence))
            (proof-with-checked-results
                ((right (proof-write (cadr parts)))
                 (left (proof-write (car parts))))
              (if (or (< (length right) (length left))
                      (proof-is-call (cadr parts) *proof-quote*))
                  (car evidence)
                (b1-search-attempt-rewriting-evidence term (cdr evidence))))))))))

(defund b1-search-attempt-rewriting-equation-match (rule term)
  (let ((equation (b1-search-rule-term rule)))
    (proof-with-checked-results
        ((left (proof-term-at equation 1))
         (match (b1-logic-match left term nil)))
      (if (not (car match))
          nil
        (proof-with-checked-results
            ((right (proof-term-at equation 2))
             (rhs (proof-subst right (cdr match)))
             (rhs-text (proof-write rhs))
             (term-text (proof-write term)))
          (and (< (length rhs-text) (length term-text)) match))))))

(defun b1-search-attempt-rewriting-equations (attempt term known rules)
  (if (endp rules)
      (cons nil attempt)
    (b1-search-with-attempt-values attempt
        ((match (b1-search-attempt-rewriting-equation-match (car rules) term)))
      (if (not match)
          (b1-search-attempt-rewriting-equations attempt term known (cdr rules))
        (b1-search-with-attempt-result attempt
            (charged (b1-search-attempt-charge attempt))
          (let ((result (b1-search-attempt-try-guarded-rule
                         attempt (car rules) (cdr match) known)))
            (if (b1-search-retry-p (car result))
                (b1-search-attempt-rewriting-equations (cdr result) term known (cdr rules))
              result)))))))

(defun b1-search-attempt-rewriting-after-evidence (attempt term known)
  (b1-search-with-attempt-result attempt
      (equation (if (and (b1-search-attempt-case-context attempt)
                         (proof-is-call term *proof-if*))
                    (b1-search-attempt-rewrite-test attempt term known)
                  (cons nil attempt)))
    (if equation
        (cons equation attempt)
      (b1-search-with-attempt-values attempt
          ((open (b1-search-attempt-can-open attempt term known)))
        (if open
            (b1-search-attempt-open attempt term)
          (b1-search-with-attempt-values attempt
              ((rules (b1-search-fact-index-candidates
                       (b1-search-fact-index-equations
                        (b1-search-attempt-facts attempt))
                       term)))
            (b1-search-attempt-rewriting-equations attempt term known rules)))))))

(defun b1-search-attempt-rewriting-rule (term attempt known)
  (if (or (not (b1-search-application-p term))
          (equal (car term) *proof-quote*))
      (cons nil attempt)
    (let ((opposite (assoc-equal (proof-neg term) known)))
      (if opposite
          (cons (b1-logic-bookproof-false-value (b1-search-attempt-lib attempt)
                                               (cdr opposite))
                attempt)
        (b1-search-with-attempt-result attempt
            (truth (if (and (b1-search-attempt-case-context attempt)
                            (assoc-equal term known))
                       (b1-search-attempt-boolean-truth attempt term known)
                     (cons nil attempt)))
          (if truth
              (cons truth attempt)
            (b1-search-with-attempt-values attempt
                ((evidence (b1-search-attempt-rewriting-evidence
                            term (table-values known))))
              (if evidence
                  (cons evidence attempt)
                (b1-search-attempt-rewriting-after-evidence attempt term known)))))))))

(defund b1-search-attempt-apply-callback (attempt callback term)
  (case (car callback)
    (:b1-search-structural
     (b1-search-attempt-structural-rule-rule term attempt (cadr callback)))
    (:b1-search-rewriting
     (b1-search-attempt-rewriting-rule term attempt (cadr callback)))
    (:b1-search-condition
     (b1-search-attempt-condition attempt term (cadr callback)))
    (:b1-search-equivalent-test
     (b1-search-with-attempt-values attempt
         ((test (and (proof-is-call term *proof-if*) (proof-term-at term 1))))
       (if (and (proof-is-call term *proof-if*) (equal (cadr callback) test))
           (b1-search-attempt-select-equivalent-test attempt term (caddr callback))
         (cons nil attempt))))
    (otherwise
     (cons '(:failure "failure" "") attempt))))

(defun b1-search-attempt-apply-rule (attempt rule term)
  (if (eq (car rule) :callback)
      (b1-search-attempt-apply-callback attempt (cadr rule) term)
    (if (eq (car rule) :b1-search-equivalent-test)
        (b1-search-attempt-apply-callback attempt rule term)
      (cons (b1-logic-apply-rule (b1-search-attempt-lib attempt) rule term) attempt))))

(defun b1-search-attempt-normalize-rules (rules)
  (if (endp rules)
      nil
    (cons (if (eq (caar rules) :b1-search-equivalent-test)
              (list :callback (car rules))
            (car rules))
          (b1-search-attempt-normalize-rules (cdr rules)))))

(defund b1-search-attempt-normalize-call (lib term evidence unfold rules split condition inspect-branches replies)
  (b1-logic-bookproof-normalize-with-library
   lib term evidence unfold rules split condition inspect-branches replies))

(defund b1-search-attempt-normalize-visit (n attempt lib term evidence unfold rules split condition inspect-branches replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "b1-search-attempt-normalize-visit") attempt)
    (let ((result (b1-search-attempt-normalize-call
                   lib term evidence unfold rules split condition inspect-branches replies)))
      (if (not (b1-logic-call-p result))
          (b1-search-attempt-normalize-result attempt result)
        (let* ((attempt (b1-search-attempt-with-lib attempt (b1-logic-call-library result)))
               (reply (b1-search-attempt-apply-callback
                       attempt (b1-logic-call-id result) (b1-logic-call-term result)))
               (step (car reply))
               (attempt (cdr reply)))
          (if (failure-p step)
              reply
            (b1-search-attempt-normalize-visit
             (1- n) attempt lib term evidence unfold rules split condition inspect-branches
             (append replies (list (cons step (b1-search-attempt-lib attempt)))))))))))

(defund b1-search-attempt-normalize-branch (attempt term evidence unfold rules split condition inspect-branches)
  (b1-search-attempt-normalize-visit
   1000000 attempt (b1-search-attempt-lib attempt) term evidence unfold
   (b1-search-attempt-normalize-rules rules) split
   (if (eq (car condition) :b1-search-condition) (list :callback condition) condition)
   inspect-branches nil))

(defund b1-search-attempt-normalize (attempt term evidence unfold rules split condition inspect-branches)
  (let ((result (b1-search-attempt-normalize-branch
                 attempt term evidence unfold rules split condition inspect-branches)))
    (if (b1-logic-branch-p (car result))
        (cons '(:failure "failure" "") (cdr result))
      result)))

(defun b1-search-record-first-evidence (known term step)
  (if (assoc-equal term known) known (table-put known term step)))

(defun b1-search-known-evidence (evidence known)
  (if (endp evidence)
      known
    (proof-with-checked-results
        ((term (b1-logic-step-first (car evidence))))
      (b1-search-known-evidence (cdr evidence)
                                (table-put known term (car evidence))))))

(defund b1-search-attempt-normalized-evidence (attempt result term step known)
  (proof-with-checked-results
      ((simpler (b1-logic-step-at result 2)))
    (if (member-equal simpler (list *proof-true* *proof-false* term))
        known
      (let ((proof (b1-search-attempt-proof attempt)))
        (proof-with-checked-results
            ((rewritten (proof-proof-rewrite proof step result '(1)))
             (reduced (proof-proof-tidy proof rewritten)))
          (table-put known simpler reduced))))))

(defun b1-search-attempt-normalize-evidence-visit (attempt items known)
  (if (endp items)
      (cons known attempt)
    (let ((term (caar items))
          (step (cdar items)))
      (if (or (proof-is-call term *library-implies*)
              (not (proof-compound term))
              (endp term))
          (b1-search-attempt-normalize-evidence-visit attempt (cdr items) known)
        (b1-search-with-attempt-values attempt
            ((open (b1-search-attempt-can-open attempt term known)))
          (if (not (or open
                       (member-equal (car term)
                                     (list *b1-logic-atom* *b1-logic-endp*
                                           *b1-logic-eq* *b1-logic-eql*
                                           (proof-sym "FORCE" "ACL2")
                                           (proof-sym "DOUBLE-REWRITE" "ACL2")))))
              (b1-search-attempt-normalize-evidence-visit attempt (cdr items) known)
            (b1-search-with-attempt-result attempt
                (result (b1-search-attempt-normalize
                         attempt term (table-values known)
                         (b1-search-attempt-definitions attempt)
                         (list (b1-search-attempt-structural-rule attempt known))
                         nil nil nil))
              (b1-search-with-attempt-values attempt
                  ((known (b1-search-attempt-normalized-evidence attempt result term step known)))
                (b1-search-attempt-normalize-evidence-visit attempt (cdr items) known)))))))))

(defun b1-search-attempt-normalize-evidence (attempt known)
  (b1-search-attempt-normalize-evidence-visit attempt known known))

(defund b1-search-attempt-reverse-evidence (attempt term step)
  (cond ((proof-is-call term *proof-equal*)
         (proof-proof-symmetric (b1-search-attempt-proof attempt) step))
        ((proof-is-call term *proof-not*)
         (proof-with-checked-results
             ((body (proof-term-at term 1)))
           (and (proof-is-call body *proof-equal*)
                (b1-reciprocal-reverse-inequality (b1-search-attempt-lib attempt) step))))))

(defun b1-search-attempt-symmetric-evidence (attempt items known)
  (if (endp items)
      known
    (let* ((term (caar items))
           (step (cdar items))
           (reverse (b1-search-attempt-reverse-evidence attempt term step)))
      (proof-with-checked-results
          ((reverse reverse)
           (known (if reverse
                      (proof-with-checked-results
                          ((literal (b1-logic-step-first reverse)))
                        (b1-search-record-first-evidence known literal reverse))
                    known)))
        (b1-search-attempt-symmetric-evidence attempt (cdr items) known)))))

(defun b1-search-attempt-local-rules-transfer
    (attempt step formula known lhs first second)
  (let* ((source (table-get known first nil))
         (negative (table-get known (proof-neg first) nil))
         (lib (b1-search-attempt-lib attempt))
         (proof (library-library-proof lib)))
    (cond ((not (or source negative)) known)
          ((equal first lhs)
           (proof-with-checked-results
               ((equation (proof-proof-unfold proof formula))
                (opened (proof-proof-rewrite proof step equation '(1)))
                (reduced (proof-proof-prove-if proof opened (or source negative))))
             (if source
                 (proof-with-checked-results
                     ((literal (b1-logic-step-first reduced))
                      (selection (proof-proof-if-false proof literal))
                      (contradiction (proof-proof-rewrite proof reduced selection '(1)))
                      (tidied (proof-proof-tidy proof contradiction))
                      (result (proof-proof-front proof tidied second)))
                   (table-put known second result))
               (let ((opposite (proof-neg second)))
                 (proof-with-checked-results
                     ((opened (proof-proof-unfold proof opposite))
                      (reflected (proof-proof-symmetric proof opened))
                      (result (proof-proof-rewrite proof reduced reflected '(1))))
                   (table-put known opposite result))))))
          (source
           (proof-with-checked-results
               ((result (b1-logic-bookproof-forces lib second step (list source)
                                                    (list *b1-search-iff*) nil)))
             (table-put known second result)))
          (t
           (let ((opposite (proof-neg second)))
             (proof-with-checked-results
                 ((assume (proof-proof-assume proof second t))
                  (wrong (b1-logic-bookproof-normalize
                          lib formula (list negative assume) (list *b1-search-iff*)
                          nil nil nil nil))
                  (not-nil (b1-logic-proof-not-nil proof))
                  (reflected (proof-proof-symmetric proof wrong))
                  (assertion (proof-proof-rewrite proof not-nil reflected '(1 1)))
                  (cut (proof-proof-cut proof step assertion))
                  (result (proof-proof-front proof cut opposite)))
               (table-put known opposite result)))))))

(defund b1-search-attempt-local-rules-formula (attempt step known rules)
  (b1-search-with-attempt-values attempt
      ((formula (b1-logic-step-first step)))
    (cond ((proof-is-call formula *proof-equal*)
           (b1-search-with-attempt-values attempt
               ((parts (proof-list-of-length (cdr formula) 2)))
             (let ((rules (if (and (proof-compound (car parts))
                                   (not (member-equal (car parts)
                                                      (b1-search-subterms (cadr parts)))))
                              (cons (b1-logic-equal-to step) rules)
                            rules)))
               (cons (list rules (b1-search-record-first-evidence known formula step)) attempt))))
          ((proof-is-call formula *b1-search-iff*)
           (b1-search-with-attempt-values attempt
               ((parts (proof-list-of-length (cdr formula) 2))
                (known (b1-search-attempt-local-rules-transfer
                        attempt step formula known (car parts) (car parts) (cadr parts)))
                (known (b1-search-attempt-local-rules-transfer
                        attempt step formula known (car parts) (cadr parts) (car parts))))
             (cons (list rules (b1-search-record-first-evidence known formula step)) attempt)))
          (t (cons (list rules (b1-search-record-first-evidence known formula step)) attempt)))))

(defund b1-search-attempt-local-rules-discharge (attempt step known)
  (b1-search-with-attempt-values attempt
      ((literal (b1-logic-step-first step)))
    (if (not (proof-is-call literal *library-implies*))
        (cons step attempt)
      (b1-search-with-attempt-values attempt
          ((test (proof-term-at literal 1)))
        (b1-search-with-attempt-result attempt
            (condition (b1-search-attempt-establish attempt test known 1))
          (cons (proof-proof-modus-ponens (b1-search-attempt-proof attempt)
                                          step condition)
                attempt))))))

(defun b1-search-attempt-local-rules-visit (attempt evidence known rules)
  (declare (xargs :measure (acl2-count evidence)))
  (if (endp evidence)
      (cons (list (reverse rules) known) attempt)
    (let* ((result (b1-search-attempt-local-rules-discharge attempt (car evidence) known))
           (step (car result))
           (attempt (cdr result)))
      (cond ((b1-search-retry-p step)
             (b1-search-attempt-local-rules-visit attempt (cdr evidence) known rules))
            ((failure-p step) result)
            (t
             (b1-search-with-attempt-result attempt
                 (result (b1-search-attempt-local-rules-formula attempt step known rules))
               (b1-search-attempt-local-rules-visit
                attempt (cdr evidence) (cadr result) (car result))))))))

(defun b1-search-attempt-local-rules (attempt evidence known)
  (b1-search-attempt-local-rules-visit attempt evidence known nil))

(defun b1-search-add-conjuncts (parts known)
  (if (endp parts)
      known
    (proof-with-checked-results
        ((term (b1-logic-step-first (car parts))))
      (b1-search-add-conjuncts
       (cdr parts) (b1-search-record-first-evidence known term (car parts))))))

(defun b1-search-attempt-examine-simpler (attempt simpler reduced known)
  (let* ((lib (b1-search-attempt-lib attempt))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((otherwise (and (proof-is-call simpler *proof-if*) (proof-term-at simpler 3))))
      (cond ((equal otherwise *proof-false*)
             (proof-with-checked-results
                 ((parts (b1-logic-bookproof-split-conjuncts lib reduced)))
               (b1-search-add-conjuncts parts known)))
            ((and (proof-is-call simpler *proof-if*)
                  (equal (cddr simpler) (list *proof-false* *proof-true*)))
             (proof-with-checked-results
                 ((unfolded (proof-proof-unfold proof (proof-neg (cadr simpler))))
                  (reflected (proof-proof-symmetric proof unfolded))
                  (negative (proof-proof-rewrite proof reduced reflected '(1)))
                  (literal (b1-logic-step-first negative)))
               (b1-search-record-first-evidence known literal negative)))
            (t (b1-search-record-first-evidence known simpler reduced))))))

(defun b1-search-attempt-examine-reduction (attempt formula term step known rules)
  (b1-search-with-attempt-result attempt
      (charged (b1-search-attempt-charge attempt))
    (b1-search-with-attempt-result attempt
        (equation (b1-search-attempt-normalize
                   attempt term (table-values known)
                   (b1-search-attempt-definitions attempt) rules nil nil nil))
      (b1-search-with-attempt-values attempt
          ((simpler (b1-logic-step-at equation 2)))
        (if (member-equal simpler (list term *proof-true*))
            (cons (list nil known) attempt)
          (let ((proof (b1-search-attempt-proof attempt)))
            (b1-search-with-attempt-values attempt
                ((step (proof-proof-rewrite proof step equation '(1)))
                 (reduced (proof-proof-tidy proof step)))
              (if (equal simpler *proof-false*)
                  (b1-search-with-attempt-values attempt
                      ((closed (proof-proof-subsume proof reduced
                                                   (cons formula (proof-step-clause reduced)))))
                    (cons (list closed known) attempt))
                (b1-search-with-attempt-values attempt
                    ((known (b1-search-attempt-examine-simpler
                             attempt simpler reduced known)))
                  (cons (list nil known) attempt))))))))))

(defund b1-search-attempt-examine-one (attempt formula term step known rules)
  (let ((opposite (table-get known (proof-neg term) nil)))
    (cond (opposite
           (let ((proof (b1-search-attempt-proof attempt)))
             (b1-search-with-attempt-values attempt
                 ((impossible (proof-proof-cut proof step opposite))
                  (closed (proof-proof-subsume proof impossible
                                               (cons formula (proof-step-clause impossible)))))
               (cons (list closed known) attempt))))
          ((proof-compound term)
           (b1-search-with-attempt-values attempt
               ((head (proof-term-at term 0)))
             (if (member-equal head (list *proof-equal* *proof-if* *b1-search-iff*
                                          *library-implies* *proof-not*))
                 (b1-search-attempt-examine-reduction attempt formula term step known rules)
               (cons (list nil known) attempt))))
          (t (cons (list nil known) attempt)))))

(defun b1-search-attempt-examine-rules (rules original-known known)
  ; Rules closed over the known-evidence table see its new entries.
  (if (endp rules)
      nil
    (let* ((rule (car rules))
           (id (cadr rule))
           (rule (if (and (eq (car rule) :callback)
                          (member-eq (car id) '(:b1-search-structural :b1-search-rewriting))
                          (equal (cadr id) original-known))
                     (list :callback (list (car id) known))
                   rule)))
      (cons rule (b1-search-attempt-examine-rules (cdr rules) original-known known)))))

(defun b1-search-attempt-examine-hypotheses-visit (attempt formula items known original-known rules)
  (declare (xargs :measure (acl2-count items)))
  (if (endp items)
      (cons (list nil known) attempt)
    (b1-search-with-attempt-result attempt
        (result (b1-search-attempt-examine-one
                 attempt formula (caar items) (cdar items) known
                 (b1-search-attempt-examine-rules rules original-known known)))
      (if (car result)
          (cons result attempt)
        (b1-search-attempt-examine-hypotheses-visit
         attempt formula (cdr items) (cadr result) original-known rules)))))

(defun b1-search-attempt-examine-hypotheses (attempt formula known rules)
  (b1-search-attempt-examine-hypotheses-visit attempt formula known known known rules))

(defun b1-search-attempt-prove-iff (attempt formula known local)
  (if (not (proof-is-call formula *b1-search-iff*))
      (cons (list known local nil) attempt)
    (b1-search-with-attempt-result attempt
        (arguments (b1-search-attempt-normalize
                    attempt formula (table-values known)
                    (remove-equal *b1-search-iff* (b1-search-attempt-definitions attempt))
                    (append local (list (b1-search-attempt-structural-rule attempt known)))
                    nil (list :b1-search-condition known) t))
      (b1-search-with-attempt-values attempt
          ((normalized (b1-logic-step-at arguments 2))
           (entry (assoc-equal normalized known))
           (proof (and entry
                       (proof-proof-transport (b1-search-attempt-proof attempt)
                                              (cdr entry) arguments))))
        (cons (list known local proof) attempt)))))

(defund b1-search-attempt-prove-context (attempt formula evidence induction)
  (b1-search-with-attempt-values attempt
      ((known (b1-search-known-evidence evidence nil)))
    (b1-search-with-attempt-result attempt
        (known (b1-search-attempt-normalize-evidence attempt known))
      (b1-search-with-attempt-values attempt
          ((known (if (b1-search-attempt-case-context attempt)
                      (b1-search-attempt-symmetric-evidence attempt known known)
                    known)))
        (b1-search-with-attempt-result attempt
            (rules-and-known (b1-search-attempt-local-rules attempt induction known))
          (let ((local (car rules-and-known))
                (known (cadr rules-and-known)))
            (if (not (b1-search-attempt-case-context attempt))
                (cons (list known local nil) attempt)
              (b1-search-with-attempt-result attempt
                  (examined (b1-search-attempt-examine-hypotheses
                             attempt formula known
                             (append local (list (b1-search-attempt-structural-rule
                                                  attempt known)))))
                (if (car examined)
                    (cons (list (cadr examined) local (car examined)) attempt)
                  (b1-search-attempt-prove-iff attempt formula
                                               (cadr examined) local))))))))))

(defund b1-search-attempt-prove-case-test (attempt terms known)
  (cond ((endp terms) (cons nil attempt))
        ((b1-search-has-test known (car terms))
         (b1-search-attempt-prove-case-test attempt (cdr terms) known))
        (t
         (b1-search-with-attempt-result attempt
             (boolean (b1-search-attempt-boolean-type attempt (car terms)))
           (if boolean
               (cons (car terms) attempt)
             (b1-search-attempt-prove-case-test attempt (cdr terms) known))))))

(defund b1-search-attempt-implication-evidence (attempt formula evidence)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise (b1-search-attempt-lib attempt) formula))
       (expanded (b1-search-attempt-evidence attempt evidence premise)))
    (cons premise expanded)))

(defund b1-search-attempt-case-evidence (attempt evidence test holds)
  (proof-with-checked-results
      ((assume (proof-proof-assume (b1-search-attempt-proof attempt) test holds)))
    (b1-search-attempt-evidence attempt evidence assume)))

(mutual-recursion
 (defun b1-search-attempt-prove-visit (n attempt formula evidence induction depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "b1-search-attempt-prove-visit") attempt)
     (b1-search-with-attempt-result attempt
         (charged (b1-search-attempt-charge attempt))
       (if (proof-is-call formula *library-implies*)
           (b1-search-with-attempt-values attempt
               ((implication (b1-search-attempt-implication-evidence attempt formula evidence)))
             (b1-search-with-attempt-result attempt
                 (yes (b1-search-attempt-prove-visit
                       (1- n) attempt (caddr formula) (cdr implication) induction depth))
               (cons (b1-logic-bookproof-prove-implication-with-premise
                      (b1-search-attempt-lib attempt) formula (car implication) yes)
                     attempt)))
         (b1-search-with-attempt-result attempt
             (context (b1-search-attempt-prove-context attempt formula evidence induction))
           (if (caddr context)
               (cons (caddr context) attempt)
             (b1-search-attempt-prove-after-context
              (1- n) attempt formula evidence induction depth (car context) (cadr context))))))))
 (defun b1-search-attempt-prove-after-context (n attempt formula evidence induction depth known local)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "b1-search-attempt-prove-after-context") attempt)
     (let ((entry (assoc-equal formula known)))
       (if entry
           (cons (cdr entry) attempt)
         (let* ((direct (b1-search-attempt-establish attempt formula known 2))
                (attempt (cdr direct)))
           (if (not (b1-search-retry-p (car direct)))
               direct
             (b1-search-with-attempt-result attempt
                 (result (b1-search-attempt-normalize-branch
                          attempt formula (table-values known)
                          (b1-search-attempt-definitions attempt)
                          (append local (list (b1-search-attempt-rewriting attempt known)))
                          t (list :b1-search-condition known) nil))
               (if (b1-logic-branch-p result)
                   (b1-search-attempt-with-cases-visit
                    (1- n) attempt formula evidence induction depth
                    (b1-logic-branch-test result))
                 (b1-search-attempt-prove-after-normalize
                  (1- n) attempt formula evidence induction depth known result)))))))))
 (defun b1-search-attempt-prove-after-normalize (n attempt formula evidence induction depth known result)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "b1-search-attempt-prove-after-normalize") attempt)
     (b1-search-with-attempt-values attempt
         ((conclusion (b1-logic-step-at result 2)))
       (if (equal conclusion *proof-true*)
           (cons (proof-proof-true-from-eq (b1-search-attempt-proof attempt) result) attempt)
         (let* ((established (b1-search-attempt-establish attempt conclusion known 2))
                (step (car established))
                (attempt (cdr established)))
           (cond ((not (failure-p step))
                  (cons (proof-proof-transport
                         (b1-search-attempt-proof attempt) step result)
                        attempt))
                 ((and (b1-search-retry-p step)
                       (b1-search-attempt-case-context attempt)
                       (proof-is-call conclusion *proof-equal*))
                  (b1-search-with-attempt-result attempt
                      (test (b1-search-attempt-prove-case-test attempt (cdr conclusion) known))
                    (if test
                        (b1-search-attempt-with-cases-visit
                         (1- n) attempt formula evidence induction depth test)
                      (cons step attempt))))
                 (t established)))))))
 (defun b1-search-attempt-with-cases-visit (n attempt formula evidence induction depth test)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (cons '(:failure "Fuel" "b1-search-attempt-with-cases-visit") attempt))
         ((<= depth 0)
          (cons '(:failure "Unproved" "") attempt))
         (t
          (b1-search-with-attempt-values attempt
              ((yes-evidence (b1-search-attempt-case-evidence attempt evidence test t)))
            (b1-search-with-attempt-result attempt
                (yes (b1-search-attempt-prove-visit
                      (1- n) attempt formula yes-evidence induction (1- depth)))
              (b1-search-with-attempt-values attempt
                  ((no-evidence (b1-search-attempt-case-evidence attempt evidence test nil)))
                (b1-search-with-attempt-result attempt
                    (no (b1-search-attempt-prove-visit
                         (1- n) attempt formula no-evidence induction (1- depth)))
                  (cons (proof-proof-cases
                         (b1-search-attempt-proof attempt) test yes no)
                        attempt)))))))))

(defund b1-search-attempt-prove (attempt formula evidence induction depth)
  (b1-search-attempt-prove-visit 1000000 attempt formula evidence induction depth))

(defun b1-search-attempt-with-cases (attempt formula evidence induction depth test)
  (b1-search-attempt-with-cases-visit
   1000000 attempt formula evidence induction depth test))

(defun b1-search-prove-in-library (lib facts fuel definitions case-context formula evidence induction depth)
  (let ((result (b1-search-attempt-prove
                 (b1-search-attempt-init lib facts fuel definitions case-context)
                 formula evidence induction depth)))
    (cons (car result) (b1-search-attempt-lib (cdr result)))))

(defmacro b1-search-with-library-values (lib bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (failure-p ,name)
             (cons ,name ,lib)
           (b1-search-with-library-values ,lib ,(cdr bindings) ,result))))))

(defun b1-search-case-on-cons-constructor (lib facts formula variable cons-step hypothesis)
  (let ((proof (library-library-proof lib)))
    (b1-search-with-library-values lib
        ((elimination (library-library-axiom lib "CAR-CDR-ELIM" (list variable)))
         (collapse (proof-proof-modus-ponens proof elimination cons-step))
         (constructor (b1-logic-step-at collapse 1))
         (template (proof-subst formula (list (cons variable *proof-result*))))
         (constructor-goal (proof-subst formula (list (cons variable constructor))))
         (reflected (proof-proof-symmetric proof collapse))
         (literal (b1-logic-step-first hypothesis))
         (hypothesis-template (proof-subst literal (list (cons variable *proof-result*))))
         (constructor-hypothesis (proof-proof-rewrite-result
                                  proof hypothesis reflected hypothesis-template *proof-result*))
         (literal (b1-logic-step-first constructor-hypothesis))
         (reduced (b1-logic-bookproof-normalize lib literal nil nil nil nil nil t))
         (constructor-hypothesis (proof-proof-rewrite
                                  proof constructor-hypothesis reduced '(1))))
      (let* ((result (b1-search-prove-in-library
                      lib facts 220 nil t constructor-goal (list cons-step)
                      (list constructor-hypothesis) 7))
             (step (car result))
             (lib (cdr result)))
        (if (failure-p step)
            result
          (cons (proof-proof-rewrite-result
                 (library-library-proof lib) step collapse template *proof-result*)
                lib))))))

(defun b1-search-case-on-cons (lib facts formula variable cons-step hypothesis)
  (let ((result (b1-search-prove-in-library
                 lib facts 220 nil t formula (list cons-step) (list hypothesis) 7)))
    (if (b1-search-unproved-p (car result))
        (b1-search-case-on-cons-constructor
         (cdr result) facts formula variable cons-step hypothesis)
      result)))

(defun b1-search-induction-prove-step (lib facts formula variable test cons-step hypothesis case-context)
  (if case-context
      (b1-search-case-on-cons lib facts formula variable cons-step hypothesis)
    (b1-search-with-library-values lib
        ((premise (proof-proof-assume (library-library-proof lib) test t)))
      (b1-search-prove-in-library
       lib facts 105 nil nil formula (list premise) (list hypothesis) 3))))

(defund b1-search-induction-variant (lib facts formula variable test cons-step case-context base pairs)
  (let ((induction (b1-induction-tree-induction-init lib formula variable)))
    (b1-search-with-library-values lib
        ((result (b1-induction-tree-induction-hypothesis
                  induction (b1-search-bindings pairs) (list (list test t)))))
      (let* ((hypothesis (car result))
             (induction (cdr result))
             (result (b1-search-induction-prove-step
                      lib facts formula variable test cons-step hypothesis case-context))
             (step (car result))
             (lib (cdr result)))
        (if (failure-p step)
            result
          (b1-search-with-library-values lib
              ((joined (proof-proof-cases (library-library-proof lib) test step base)))
            (cons (b1-induction-tree-induction-finish
                   (b1-induction-tree-induction-with-lib induction lib) joined)
                  lib)))))))

(defun b1-search-induction-variants (lib facts formula variable test cons-step case-context base substitutions)
  (declare (xargs :measure (acl2-count substitutions)))
  (if (endp substitutions)
      (cons nil lib)
    (let ((result (b1-search-induction-variant
                   lib facts formula variable test cons-step case-context base (car substitutions))))
      (if (b1-search-unproved-p (car result))
          (b1-search-induction-variants
           (cdr result) facts formula variable test cons-step case-context base (cdr substitutions))
        result))))

(defund b1-search-induction-anchor (lib facts formula variable case-context)
  (let* ((proof (library-library-proof lib))
         (test (list *proof-consp* variable)))
    (b1-search-with-library-values lib
        ((cons-step (and case-context (proof-proof-assume proof test t))))
      (let* ((trial (b1-search-attempt-init lib facts
                                           (if case-context 140 105) nil case-context))
             (premise (proof-proof-assume proof test nil))
             (result (if (failure-p premise)
                         (cons premise trial)
                       (b1-search-attempt-prove
                        trial formula (list premise) nil (if case-context 7 3))))
             (base (car result))
             (trial (cdr result))
             (lib (b1-search-attempt-lib trial)))
        (cond ((b1-search-unproved-p base) (cons nil lib))
              ((failure-p base) (cons base lib))
              (t
               (b1-search-with-library-values lib
                   ((substitutions (b1-search-attempt-substitutions trial formula variable)))
                 (b1-search-induction-variants
                  lib facts formula variable test cons-step case-context base
                  (seq-slice substitutions 0 3)))))))))

(defun b1-search-induction-anchors (lib facts formula anchors case-context)
  (declare (xargs :measure (acl2-count anchors)))
  (if (endp anchors)
      (cons nil lib)
    (let ((result (b1-search-induction-anchor lib facts formula (car anchors) case-context)))
      (if (car result)
          result
        (b1-search-induction-anchors
         (cdr result) facts formula (cdr anchors) case-context)))))

(defun b1-search-case-induction (lib facts formula anchors)
  (let ((result (b1-search-induction-anchors lib facts formula anchors t)))
    (if (car result)
        result
      (cons '(:failure "Unproved" "") (cdr result)))))

(defun b1-search-automatic-induction (attempt formula)
  (let ((lib (b1-search-attempt-lib attempt))
        (facts (b1-search-attempt-facts attempt)))
    (b1-search-with-library-values lib
        ((anchors (b1-search-attempt-anchors attempt formula)))
      (let* ((anchors (seq-slice anchors 0 2))
             (result (b1-search-induction-anchors lib facts formula anchors nil))
             (lib (cdr result)))
        (if (car result)
            result
          (b1-search-with-library-values lib
              ((text (and anchors (proof-write formula))))
            (let ((result (if (and anchors (<= (length text) 3200))
                              (b1-search-case-induction lib facts formula anchors)
                            (cons nil lib))))
              (if (and (car result) (not (b1-search-unproved-p (car result))))
                  result
                (cons '(:failure "Unproved" "")
                      (cdr result))))))))))

(defun b1-search-automatic (lib facts formula)
  (b1-search-with-library-values lib
      ((text (proof-write formula)))
    (if (> (length text) 10000)
        (cons '(:failure "Unproved" "") lib)
      (let* ((direct (b1-search-attempt-prove
                      (b1-search-attempt-init lib facts 65 nil nil) formula nil nil 3))
             (attempt (cdr direct))
             (lib (b1-search-attempt-lib attempt)))
        (if (not (b1-search-unproved-p (car direct)))
            (cons (car direct) lib)
          (b1-search-with-library-values lib
              ((definitions (b1-search-immediate-definitions lib formula)))
            (if (endp definitions)
                (b1-search-automatic-induction attempt formula)
              (let ((opened (b1-search-prove-in-library
                             lib facts 95 (seq-slice definitions 0 8) nil formula nil nil 3)))
                (if (b1-search-unproved-p (car opened))
                    (b1-search-automatic-induction
                     (b1-search-attempt-with-lib attempt (cdr opened)) formula)
                  opened)))))))))
