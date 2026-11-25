(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-character-lists-explode-atom* (proof-sym "EXPLODE-ATOM" "ACL2"))
(defconst *t3-book-character-lists-pack-list* (proof-sym "PACK-LIST" "ACL2"))
(defconst *t3-book-character-lists-pack-tree* (proof-sym "PACK-TREE" "ACL2"))
(defconst *t3-book-character-lists-string-list* (proof-sym "STRING-LISTP" "ACL2"))

(defun t3-book-character-lists-head-type (lib predicate value evidence)
  (let ((target (list predicate value)))
    (proof-with-checked-results
        ((known (t3-logic-evidence-find evidence target))
         (step (or (car known)
                   (t3-logic-libraryproofs-prove lib target nil nil))))
      (cons step (cdr known)))))

(defun t3-book-character-lists-structural-results-project (proof step index last-index)
  (declare (xargs :measure (nfix index)))
  (cond ((not (zp index))
         (proof-with-checked-results ((parts (proof-proof-conjunct proof step)))
           (t3-book-character-lists-structural-results-project
            proof (cadr parts) (1- index) (1- last-index))))
        ((< 0 last-index)
         (proof-with-checked-results ((parts (proof-proof-conjunct proof step)))
           (car parts)))
        (t step)))

(defun t3-book-character-lists-structural-results-recursive
    (value evidence lib calls index formula measure substitutions)
  (proof-with-checked-results
      ((child (proof-term-at value 1))
       (expected (proof-subst (nth index calls) (list (cons *library-x* child)))))
    (if (not (equal value expected))
        '(:failure "unsupported" "")
      (let* ((child-measure (list *library-count* child))
             (smaller (list *proof-ordinal-less* child-measure measure)))
        (proof-with-checked-results
            ((direct (t3-printing-direct-builtin lib (list smaller) evidence))
             (descent (if (car direct)
                          (list* (car direct) lib (cdr direct))
                        (t3-rational-rational-descent lib child-measure measure (cdr direct)))))
          (if (not (car descent))
              '(:failure "unsupported" "")
            (let* ((lib (cadr descent))
                   (proof (library-library-proof lib))
                   (present (assoc-equal child substitutions))
                   (bindings (if present (cdr present) (list (list *library-x* child))))
                   (substitutions (if present
                                      substitutions
                                    (table-put substitutions child bindings))))
              (proof-with-checked-results
                  ((target (proof-subst formula (list (cons *library-x* child))))
                   (assumed (proof-proof-assume proof (proof-ite smaller target *proof-true*) t))
                   (proved (proof-proof-prove-if proof assumed (car descent)))
                   (step (t3-book-character-lists-structural-results-project
                          proof proved index (1- (len calls)))))
                (list step lib (cddr descent) substitutions)))))))))

(defun t3-book-character-lists-packed-characters-atom-rule (value evidence lib)
  (declare (ignore evidence))
  (library-library-cite lib "T3-EXPLODE-ATOM-CHARACTERS" (seq-slice value 1 2) nil))

(defun t3-book-character-lists-numeral-rule-visit (value evidence lib substitutions pending)
  (proof-with-checked-results
      ((number (proof-term-at value 1))
       (accumulator (proof-term-at value 3))
       (claim (library-library-cite lib "T3-DECIMAL-CHARACTERS" (list number accumulator) nil)))
    (list :visit lib accumulator evidence nil substitutions
          (cons (list :numeral claim) pending))))

(defun t3-book-character-lists-characters-rule (lib value evidence calls substitutions pending)
  (if (not (proof-compound value))
      '(:failure "unsupported" "")
    (proof-with-checked-results ((head (proof-term-at value 0)))
      (let ((rule (cdr (assoc-equal head (car calls)))))
        (case rule
          (:numeral
           (t3-book-character-lists-numeral-rule-visit value evidence lib substitutions pending))
          (:atom
           (proof-with-checked-results
               ((step (t3-book-character-lists-packed-characters-atom-rule value evidence lib)))
             (list :return (list step lib evidence substitutions) pending)))
          (otherwise
           (if (natp rule)
               (proof-with-checked-results
                   ((result (t3-book-character-lists-structural-results-recursive
                             value evidence lib (cadr calls) rule (caddr calls) (cadddr calls)
                             substitutions)))
                 (list :return result pending))
             '(:failure "unsupported" ""))))))))

(defun t3-book-character-lists-characters-visit (lib value evidence calls substitutions pending)
  (let ((formula (list *t3-list-bounds-char-list* value))
        (proof (library-library-proof lib)))
    (proof-with-checked-results ((known (t3-logic-evidence-find evidence formula)))
      (let ((evidence (cdr known)))
        (cond
         ((car known) (list :return (list (car known) lib evidence substitutions) pending))
         ((proof-is-call value *proof-quote*)
          (proof-with-checked-results
              ((step (t3-logic-libraryproofs-prove-formula
                      lib formula
                      (list *t3-list-bounds-char-list* *t3-logic-atom* *proof-not*) nil)))
            (list :return (list step lib evidence substitutions) pending)))
         ((proof-is-call value *t3-list-bounds-coerce*)
          (proof-with-checked-results ((kind (proof-term-at value 2)))
            (if (equal kind *t3-list-bounds-list-type*)
                (proof-with-checked-results
                    ((step (proof-proof-fact
                            proof (proof-sym "CHARACTER-LISTP-COERCE" "ACL2")
                            (list (list (proof-sym "STR" "ACL2") (cadr value))))))
                  (list :return (list step lib evidence substitutions) pending))
              (t3-book-character-lists-characters-rule
               lib value evidence calls substitutions pending))))
         ((proof-is-call value *proof-cons*)
          (proof-with-checked-results
              ((head (proof-term-at value 1))
               (typed (t3-book-character-lists-head-type
                       lib *t3-list-bounds-character* head evidence))
               (tail (proof-term-at value 2)))
            (list :visit lib tail (cdr typed) calls substitutions
                  (cons (list :cons (car typed)) pending))))
         ((proof-is-call value *t3-list-bounds-append*)
          (let ((args (cdr value)))
            (if (endp args)
                (proof-list-of-length nil 2)
              (list :visit lib (car args) evidence calls substitutions
                    (cons (list :append-left args calls) pending)))))
         (t (t3-book-character-lists-characters-rule
             lib value evidence calls substitutions pending)))))))

; The pending constructors retain the already established operand Steps.
(defun t3-book-character-lists-characters-return (result pending)
  (if (endp pending)
      (list :done result)
    (let* ((frame (car pending))
           (rest (cdr pending))
           (step (car result))
           (lib (cadr result))
           (proof (library-library-proof lib))
           (evidence (caddr result))
           (substitutions (cadddr result)))
      (case (car frame)
        (:cons
         (proof-with-checked-results ((combined (t3-list-bounds-char-cons lib (cadr frame) step)))
           (list :return (cons combined (cdr result)) rest)))
        (:numeral
         (proof-with-checked-results ((combined (proof-proof-prove-if proof (cadr frame) step)))
           (list :return (cons combined (cdr result)) rest)))
        (:append-left
         (let ((args (cadr frame))
               (calls (caddr frame)))
           (if (endp (cdr args))
               (proof-list-of-length (list step) 2)
             (list :visit lib (cadr args) evidence calls substitutions
                   (cons (list :append-right args calls step) rest)))))
        (:append-right
         (let ((args (cadr frame)))
           (if (consp (cddr args))
               (list :visit lib (caddr args) evidence (caddr frame) substitutions
                     (cons (list :append-excess) rest))
             (proof-with-checked-results
                 ((claim (library-library-cite lib "T3-CHARACTER-LIST-APPEND" args nil))
                  (both (t3-scan-typed-pair lib (cadddr frame) step))
                  (combined (proof-proof-prove-if proof claim both)))
               (list :return (cons combined (cdr result)) rest)))))
        (otherwise '(:failure "unproved" ""))))))

(defun t3-book-character-lists-characters-next (cursor)
  (if (eq (car cursor) :visit)
      (t3-book-character-lists-characters-visit
       (cadr cursor) (caddr cursor) (cadddr cursor) (nth 4 cursor) (nth 5 cursor) (nth 6 cursor))
    (t3-book-character-lists-characters-return (cadr cursor) (caddr cursor))))

(defun t3-book-character-lists-characters-walk (n cursor)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "t3-book-character-lists-characters"))
        ((failure-p cursor) cursor)
        ((eq (car cursor) :done) (cadr cursor))
        (t (t3-book-character-lists-characters-walk
            (1- n) (t3-book-character-lists-characters-next cursor)))))

(defun t3-book-character-lists-characters (n lib value evidence calls substitutions)
  (t3-book-character-lists-characters-walk n
   (list :visit lib value evidence calls substitutions nil)))

(defun t3-book-character-lists-element-list-visit
    (lib predicate element-type value evidence pending)
  (let ((target (list predicate value)))
    (proof-with-checked-results
        ((known (t3-logic-evidence-find evidence target)))
      (cond
       ((car known) (list :return (car known) (cdr known) pending))
       ((proof-is-call value *proof-quote*)
        (proof-with-checked-results
            ((step (t3-logic-libraryproofs-prove-formula
                    lib target (list predicate *t3-logic-atom* (proof-cl "EQ") *proof-not*) nil)))
          (list :return step (cdr known) pending)))
       ((proof-is-call value *proof-cons*)
        (proof-with-checked-results
            ((head (proof-term-at value 1))
             (typed (t3-book-character-lists-head-type lib element-type head (cdr known)))
             (tail (proof-term-at value 2)))
          (list :visit tail (cdr typed) (cons (list target (car typed)) pending))))
       (t '(:failure "unsupported" ""))))))

(defun t3-book-character-lists-element-list-next (lib predicate element-type cursor)
  (let ((value (cadr cursor))
        (evidence (caddr cursor))
        (pending (cadddr cursor)))
    (cond
     ((eq (car cursor) :visit)
      (t3-book-character-lists-element-list-visit lib predicate element-type value evidence pending))
     ((endp pending) (list :done (cons value evidence)))
     (t
      (let ((proof (library-library-proof lib))
            (frame (car pending)))
        (proof-with-checked-results
            ((equation (t3-book-spines-shallow lib (car frame) (list (cadr frame))))
             (step (proof-proof-transport proof value equation)))
          (list :return step evidence (cdr pending))))))))

(defun t3-book-character-lists-element-list-walk (n lib predicate element-type cursor)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "t3-book-character-lists-element-list"))
        ((failure-p cursor) cursor)
        ((eq (car cursor) :done) (cadr cursor))
        (t (t3-book-character-lists-element-list-walk
            (1- n) lib predicate element-type
            (t3-book-character-lists-element-list-next lib predicate element-type cursor)))))

(defun t3-book-character-lists-element-list-with-evidence
    (lib predicate element-type value evidence)
  (t3-book-character-lists-element-list-walk
   1000000 lib predicate element-type (list :visit value evidence nil)))

(defun t3-book-character-lists-element-list (lib predicate element-type value evidence)
  (proof-with-checked-results
      ((result (t3-book-character-lists-element-list-with-evidence
                lib predicate element-type value evidence)))
    (car result)))

(defun t3-book-character-lists-preserving-elements-leaf
    (value tests lib predicate variable typed hypothesis)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (cons (t3-logic-evidence-find evidence (list *proof-consp* variable)))
         (evidence
          (if (not (car cons))
              (cdr cons)
            (proof-with-checked-results
                ((literal (proof-step-first typed))
                 (equation (t3-book-spines-shallow lib literal (list (car cons))))
                 (reduced (proof-proof-rewrite proof typed equation '(1)))
                 (parts (proof-proof-conjunct proof reduced))
                 (builtin (library-library-builtin lib 3 variable))
                 (decreases (proof-proof-discharge proof builtin (car cons)))
                 (instantiated (proof-proof-prove-if proof hypothesis decreases))
                 (induction (proof-proof-modus-ponens proof instantiated (cadr parts))))
              (t3-logic-evidence-init lib tests
                                      (list (car parts) (cadr parts) induction) nil)))))
      (if (equal predicate *t3-list-bounds-char-list*)
          (proof-with-checked-results
              ((result (t3-book-character-lists-characters 1000000 lib value evidence nil nil)))
            (car result))
        (t3-book-character-lists-element-list
         lib *t3-book-character-lists-string-list* *t3-list-bounds-stringp* value evidence)))))

(defun t3-book-character-lists-by-value-leaf (lib value tests context substitutions)
  (case (car context)
    (:preserving
     (proof-with-checked-results
         ((step (t3-book-character-lists-preserving-elements-leaf
                 value tests lib (cadr context) (caddr context)
                 (cadddr context) (car (cddddr context)))))
       (list step lib substitutions)))
    (otherwise
     (proof-with-checked-results
         ((evidence (t3-logic-evidence-init lib tests (cadr context) nil))
          (result (t3-book-character-lists-characters
                   1000000 lib value evidence (caddr context) substitutions)))
       (list (car result) (cadr result) (cadddr result))))))

(defun t3-book-character-lists-by-value-walk (n cursor template context)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "t3-book-character-lists-by-value"))
        ((failure-p cursor) cursor)
        ((eq (car cursor) :done) (cadr cursor))
        (t (t3-book-character-lists-by-value-walk
            (1- n)
            (t3-printing-by-value-next cursor template
             (t3-book-character-lists-by-value-leaf lib value tests context substitutions))
            template context))))

(defun t3-book-character-lists-by-value (n lib value template tests context substitutions)
  (t3-book-character-lists-by-value-walk
   n (list :visit lib value tests substitutions nil) template context))

(defun t3-book-character-lists-numeral-branch (holds lib decimal test opened)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test holds))
         (body (proof-rewritten-term opened))
         (normalized (t3-logic-libraryproofs-normalize
                      lib body (list decimal assumed) (list *proof-not*))))
      (proof-proof-chain proof opened (list normalized)))))

(defun t3-book-character-lists-numeral (lib)
  (proof-with-checked-results
      ((lib (t3-digit-capacity-floor-interval lib nil))
       (lib (t3-digit-capacity-digit-character lib))
       (decimal (t3-digit-capacity-known-print-base lib *t3-digit-capacity-ten*)))
    (let* ((proof (library-library-proof lib))
           (test (list *t3-logic-zp* *library-x*))
           (call (list *t3-digit-capacity-explode* *library-x*
                       *t3-digit-capacity-ten* *library-y*))
           (accepted (list *t3-list-bounds-char-list* *library-y*))
           (formula (proof-ite accepted (list *t3-list-bounds-char-list* call) *proof-true*))
           (measure (list *library-nfix* *library-x*)))
      (proof-with-checked-results
          ((accumulator (proof-proof-assume proof accepted t))
           (opened (proof-proof-unfold proof call))
           (evidence (t3-logic-evidence-init
                      lib (list (list test nil)) (list decimal) (list *t3-logic-zp*)))
           (numeric (t3-logic-evidence-require evidence (library-integer *library-x*)))
           (entering (t3-logic-evidence-require (cdr numeric) (library-positive *library-x*)))
           (step (t3-book-character-lists-numeral-branch nil lib decimal test opened))
           (value (proof-rewritten-term step))
           (actuals (proof-list-of-length (cdr value) 3))
           (part (car actuals))
           (next-answer (caddr actuals))
           (bound (library-library-cite lib "T3-FLOOR-DECREASE"
                                        (list *library-x* *t3-digit-capacity-ten*)
                                        (list (car numeric) (car entering) decimal)))
           (parts (proof-proof-conjunct proof bound))
           (typed (library-library-cite lib "NATURAL-INTEGER" (list part) (list (car parts))))
           (smaller (library-library-cite lib "NFIX-DECREASE" (list part *library-x*)
                                          (list typed (car numeric) (car entering) (cadr parts))))
           (decrease (proof-step-first smaller))
           (target (proof-subst formula (list (cons *library-x* part)
                                              (cons *library-y* next-answer))))
           (assumed (proof-proof-assume proof (proof-ite decrease target *proof-true*) t))
           (induction (proof-proof-prove-if proof assumed smaller))
           (digit-call (proof-term-at next-answer 1))
           (digit (library-library-cite lib "T3-DIGIT-CHARACTER" (cdr digit-call) nil))
           (new-answer (t3-list-bounds-char-cons lib digit accumulator))
           (recursive (proof-proof-prove-if proof induction new-answer))
           (step-result (library-library-transport-argument lib recursive step 1))
           (base (t3-book-character-lists-numeral-branch t lib decimal test opened))
           (base-value (proof-rewritten-term base))
           (base-proof (t3-book-character-lists-by-value
                        1000000 lib base-value (list *t3-list-bounds-char-list* *proof-result*)
                        nil (list :characters (list accumulator) nil) nil))
           (base-result (library-library-transport-argument lib (car base-proof) base 1))
           (yes (t3-scan-conclusion lib formula base-result))
           (no (t3-scan-conclusion lib formula step-result))
           (joined (proof-proof-cases proof test yes no))
           (ordinal (library-library-cite lib "NFIX-ORDINAL" (list *library-x*) nil))
           (result (proof-proof-induct
                    proof ordinal joined formula measure
                    (list (list (list *library-x* part) (list *library-y* next-answer))))))
        (library-library-lemma lib "T3-DECIMAL-CHARACTERS" formula result nil)))))

(defun t3-book-character-lists-structural-results-formula (calls)
  (if (endp calls)
      '(:failure "missing-proof-input" "")
    (let ((first (list *t3-list-bounds-char-list* (car calls))))
      (if (endp (cdr calls))
          first
        (proof-with-checked-results
            ((rest (t3-book-character-lists-structural-results-formula (cdr calls))))
          (proof-ite first rest *proof-false*))))))

(defun t3-book-character-lists-structural-results-rules (calls index rules)
  (if (endp calls)
      rules
    (proof-with-checked-results ((head (proof-term-at (car calls) 0)))
      (t3-book-character-lists-structural-results-rules
       (cdr calls) (1+ index) (table-put rules head index)))))

(defun t3-book-character-lists-structural-results-case (call context progress)
  (let ((lib (car progress)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold (library-library-proof lib) call))
         (value (proof-rewritten-term equation))
         (proved (t3-book-character-lists-by-value
                  1000000 lib value (list *t3-list-bounds-char-list* *proof-result*)
                  nil context (cadr progress)))
         (step (library-library-transport-argument (cadr proved) (car proved) equation 1)))
      (list (cadr proved) (caddr proved) (cons step (caddr progress))))))

(defun t3-book-character-lists-structural-results-cases (calls context progress)
  (cond ((failure-p progress) progress)
        ((endp calls) (list (reverse (caddr progress)) (car progress) (cadr progress)))
        (t (t3-book-character-lists-structural-results-cases
            (cdr calls) context
            (t3-book-character-lists-structural-results-case (car calls) context progress)))))

(defun t3-book-character-lists-structural-results-join (lib steps)
  (if (endp (cdr steps))
      (car steps)
    (proof-with-checked-results
        ((rest (t3-book-character-lists-structural-results-join lib (cdr steps))))
      (t3-scan-typed-pair lib (car steps) rest))))

(defun t3-book-character-lists-structural-results (lib calls terminal-rules)
  (let ((measure (list *library-count* *library-x*)))
    (proof-with-checked-results
        ((formula (t3-book-character-lists-structural-results-formula calls))
         (rules (t3-book-character-lists-structural-results-rules calls 0 terminal-rules))
         (results (t3-book-character-lists-structural-results-cases
                   calls (list :characters nil (list rules calls formula measure))
                   (list lib nil nil)))
         (step (t3-book-character-lists-structural-results-join (cadr results) (car results)))
         (ordinal (library-library-builtin (cadr results) 1 *library-x*))
         (result (proof-proof-induct
                  (library-library-proof (cadr results)) ordinal step formula measure
                  (table-values (caddr results)))))
      (cons result (cadr results)))))

(defun t3-book-character-lists-packed-characters (lib name formula)
  (proof-with-checked-results
      ((lib (t3-rational-rational-counts lib))
       (lib (t3-list-bounds-append-character-lists lib))
       (lib (t3-book-character-lists-numeral lib))
       (atom (t3-book-character-lists-structural-results
              lib (list (list *t3-book-character-lists-explode-atom*
                              *library-x* *t3-digit-capacity-ten*))
              (list (cons *t3-digit-capacity-explode* :numeral))))
       (claim (proof-step-first (car atom)))
       (lib (library-library-lemma (cdr atom) "T3-EXPLODE-ATOM-CHARACTERS" claim (car atom) nil))
       (packed (t3-book-character-lists-structural-results
                lib (list (list *t3-book-character-lists-pack-list* *library-x*)
                          (list *t3-book-character-lists-pack-tree* *library-x*))
                (list (cons *t3-book-character-lists-explode-atom* :atom))))
       (claim (proof-step-first (car packed)))
       (lib (library-library-lemma (cdr packed) "T3-PACK-CHARACTERS" claim (car packed) nil))
       (call (proof-term-at formula 1))
       (result (library-library-cite lib "T3-PACK-CHARACTERS" (cdr call) nil))
       (parts (proof-proof-conjunct (library-library-proof lib) result))
       (head (proof-term-at call 0))
       (step (cond ((equal head *t3-book-character-lists-pack-list*) (car parts))
                   ((equal head *t3-book-character-lists-pack-tree*) (cadr parts))
                   (t '(:failure "unproved" ""))))
       (entry (proof-proof-entry "theorem" name (list name) (list step))))
    (cons entry lib)))

(defun t3-book-character-lists-preserving-argument (lib formula predicate call variable)
  (let* ((proof (library-library-proof lib))
         (tail (list *library-cdr* variable))
         (measure (list *library-count* variable))
         (pairs (list (list variable tail)))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
    (proof-with-checked-results
        ((typed (proof-proof-assume proof (cadr formula) t))
         (target (proof-subst formula (list (cons variable tail))))
         (hypothesis (proof-proof-assume proof (proof-ite smaller target *proof-true*) t))
         (opened (proof-proof-unfold proof call))
         (lib (if (and (equal predicate *t3-list-bounds-char-list*)
                       (not (assoc-equal (proof-sym "SELF-T3-CHARACTER-LIST-APPEND" "ACL2")
                                         (proof-proof-facts proof))))
                  (t3-list-bounds-append-character-lists lib)
                lib))
         (body (proof-rewritten-term opened))
         (result (t3-book-character-lists-by-value
                  1000000 lib body (list predicate *proof-result*) nil
                  (list :preserving predicate variable typed hypothesis) nil))
         (transported (library-library-transport-argument lib (car result) opened 1))
         (step (t3-book-lemmas-implication lib formula transported))
         (ordinal (library-library-builtin lib 1 variable))
         (induction (proof-proof-induct
                     (library-library-proof lib) ordinal step formula measure (list pairs))))
      (cons induction lib))))

(defun t3-book-character-lists-preserving-elements (lib formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil lib)
    (proof-with-checked-results ((goal (proof-term-at formula 2)))
      (if (not (or (proof-is-call goal *t3-list-bounds-char-list*)
                   (proof-is-call goal *t3-book-character-lists-string-list*)))
          (cons nil lib)
        (proof-with-checked-results
            ((parts (proof-list-of-length goal 2))
             (variable (t3-book-spines-map-parameter lib (cadr parts))))
          (if (or (not variable)
                  (not (equal (cadr formula) (list (car parts) variable))))
              (cons nil lib)
            (t3-book-character-lists-preserving-argument
             lib formula (car parts) (cadr parts) variable)))))))
