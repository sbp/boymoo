(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-mv-nth-recurse* (proof-sym "MV-NTH-EVAL-REC" "ACL2"))
(defconst *t3-book-mv-nth-optimize* (proof-sym "MV-NTH-EVAL-FN" "ACL2"))
(defconst *t3-book-mv-nth-recurrence* (proof-sym "EVAL-FOR-MV-NTH-REC-THM" "ACL2"))
(defconst *t3-book-mv-nth-env* (proof-sym "A" "ACL2"))
(defconst *t3-book-mv-nth-n* (proof-sym "N" "ACL2"))
(defconst *t3-book-mv-nth-term* (proof-sym "TERM" "ACL2"))
(defconst *t3-book-mv-nth-nth* (proof-cl "NTH"))

(defun t3-book-mv-nth-known-application (lib term environment function evidence)
  (let ((rule (cond ((equal function *proof-quote*) 2)
                    ((equal function *t3-book-evaluators-mv-nth*) 8)
                    ((equal function *proof-cons*) 9)
                    (t nil))))
    (if (not rule)
        '(:failure "missing-proof-input" "")
      (let ((name (proof-sym (concatenate 'string "EVAL-FOR-MV-NTH-CONSTRAINT-" (decimal-text rule)) "ACL2"))
            (cons-test (list *proof-consp* term))
            (head-test (proof-eq (list *library-car* term) (proof-quote function)))
            (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((found (t3-logic-evidence-find evidence cons-test))
             (present (or (car found) (t3-logic-libraryproofs-prove-formula lib cons-test nil nil)))
             (found (t3-logic-evidence-find (cdr found) head-test))
             (symbol (or (car found) (t3-logic-libraryproofs-prove-formula lib head-test nil nil)))
             (fact (proof-proof-fact proof name
                                     (list (list *library-x* term)
                                           (list *t3-book-mv-nth-env* environment))))
             (guard (t3-scan-typed-pair lib present symbol))
             (equation (proof-proof-modus-ponens proof fact guard))
             (right (proof-rewritten-term equation))
             (normalized (t3-logic-libraryproofs-normalize lib right nil nil))
             (result (proof-proof-chain proof equation (list normalized))))
          (cons result (cdr found)))))))

(defun t3-book-mv-nth-nth-equivalence-branch (guards through lib target)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((selectors (proof-list-of-length (cdr target) 2))
         (first (t3-book-spines-shallow lib (car selectors) guards))
         (second (t3-book-spines-shallow lib (cadr selectors) guards))
         (reversed (proof-proof-symmetric proof second)))
      (proof-proof-chain proof first (list through reversed)))))

(defun t3-book-mv-nth-nth-equivalence (lib)
  (let* ((proof (library-library-proof lib))
         (tail (list *library-cdr* *library-x*))
         (mv-call (list *t3-book-evaluators-mv-nth* *library-y* *library-x*))
         (target (proof-eq (list *t3-book-mv-nth-nth* *library-y* *library-x*) mv-call))
         (test (list *proof-consp* *library-x*))
         (index (list *t3-logic-zp* *library-y*)))
    (proof-with-checked-results
        ((present (proof-proof-assume proof test t))
         (opened (proof-proof-unfold proof mv-call))
         (shape (proof-rewritten-term opened))
         (otherwise (proof-term-at shape 3))
         (recursion (proof-term-at otherwise 3))
         (child-index (proof-term-at recursion 1))
         (builtin (library-library-builtin lib 3 *library-x*))
         (descent (proof-proof-discharge proof builtin present))
         (claim (proof-step-first descent))
         (smaller (proof-subst target (list (cons *library-x* tail)
                                            (cons *library-y* child-index))))
         (hypothesis (proof-proof-assume proof (proof-ite claim smaller *proof-true*) t))
         (remaining (proof-proof-prove-if proof hypothesis descent))
         (zero (proof-proof-assume proof index t))
         (stay (t3-book-mv-nth-nth-equivalence-branch (list present zero) nil lib target))
         (nonzero (proof-proof-assume proof index nil))
         (recur (t3-book-mv-nth-nth-equivalence-branch (list present nonzero) remaining lib target))
         (absent (proof-proof-assume proof test nil))
         (empty (t3-book-mv-nth-nth-equivalence-branch (list absent) nil lib target))
         (nonempty (proof-proof-cases proof index stay recur))
         (cases (proof-proof-cases proof test nonempty empty))
         (ordinal (library-library-builtin lib 1 *library-x*))
         (result (proof-proof-induct proof ordinal cases target (list *library-count* *library-x*)
                                     (list (list (list *library-x* tail)
                                                 (list *library-y* child-index))))))
      (library-library-lemma lib "T3-NTH-IS-MV-NTH" target result nil))))

(defun t3-book-mv-nth-recurrence-child (lib value premise observation measure formula evidence substitutions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((form (proof-list-of-length value 4))
         (smaller (t3-size-count-descent lib (list *library-count* (caddr form)) measure evidence)))
      (let* ((entry (assoc-equal value substitutions))
             (pairs (if entry
                        (cdr entry)
                      (list (list *t3-book-mv-nth-n* (cadr form))
                            (list *t3-book-mv-nth-term* (caddr form)))))
             (substitutions (if entry substitutions (table-put substitutions value pairs))))
        (proof-with-checked-results
            ((next-case (proof-subst formula (proof-bindings-table pairs nil)))
             (relation (proof-step-first (car smaller)))
             (assumption (proof-proof-assume proof (proof-ite relation next-case *proof-true*) t))
             (ih (proof-proof-prove-if proof assumption (car smaller)))
             (given (proof-proof-chain proof premise (list observation)))
             (correct (proof-proof-modus-ponens proof ih given))
             (reversed (proof-proof-symmetric proof observation))
             (result (proof-proof-chain proof correct (list reversed))))
          (cons result substitutions))))))

(defun t3-book-mv-nth-recurrence-cons (lib value zero premise index-result measure formula evidence substitutions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (t3-book-mv-nth-known-application lib *t3-book-mv-nth-term* *t3-book-mv-nth-env*
                                                 *proof-cons* evidence))
         (original (proof-proof-reflexive proof index-result))
         (observed (t3-book-spines-replace-value lib original (list (car parts))))
         (stayed (proof-proof-assume proof (list *t3-logic-zp* *t3-book-mv-nth-n*) zero))
         (right (proof-rewritten-term observed))
         (shallow (t3-book-spines-shallow lib right (list stayed)))
         (observation (proof-proof-chain proof observed (list shallow))))
      (if zero
          (proof-with-checked-results ((result (proof-proof-symmetric proof observation)))
            (cons result substitutions))
        (t3-book-mv-nth-recurrence-child lib value premise observation measure formula
                                        (cdr parts) substitutions)))))

(defun t3-book-mv-nth-recurrence-quote (lib value index-result evidence substitutions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (t3-book-mv-nth-known-application lib value *t3-book-mv-nth-env* *proof-quote* evidence))
         (source (t3-book-mv-nth-known-application lib *t3-book-mv-nth-term* *t3-book-mv-nth-env*
                                                  *proof-quote* (cdr literal)))
         (original (proof-proof-reflexive proof index-result))
         (observation (t3-book-spines-replace-value lib original (list (car source))))
         (selected (proof-rewritten-term (car literal))))
      (if (proof-is-call selected *t3-book-mv-nth-nth*)
          (proof-with-checked-results
              ((at (proof-term-at selected 2))
               (index (proof-term-at selected 1))
               (equivalence (library-library-cite lib "T3-NTH-IS-MV-NTH" (list at index) nil))
               (reversed (proof-proof-symmetric proof observation))
               (result (proof-proof-chain proof (car literal) (list equivalence reversed))))
            (cons result substitutions))
        (proof-with-checked-results
            ((present (t3-logic-evidence-require
                       (cdr source) (list *proof-consp* (t3-book-evaluators-second *t3-book-mv-nth-term*))))
             (zero (proof-proof-assume proof (list *t3-logic-zp* *t3-book-mv-nth-n*) t))
             (right (proof-rewritten-term observation))
             (head (t3-book-spines-shallow lib right (list (car present) zero)))
             (selected (proof-proof-chain proof observation (list head)))
             (reversed (proof-proof-symmetric proof selected))
             (result (proof-proof-chain proof (car literal) (list reversed))))
          (cons result substitutions))))))

(defun t3-book-mv-nth-recurrence-case (lib value premise index-result measure formula evidence substitutions)
  (let ((zero (equal value (t3-book-evaluators-second *t3-book-mv-nth-term*))))
    (cond
     ((equal value *library-x*) (cons premise substitutions))
     ((or zero (proof-is-call value *t3-book-mv-nth-recurse*))
      (t3-book-mv-nth-recurrence-cons lib value zero premise index-result measure formula evidence substitutions))
     ((proof-is-call value *proof-cons*)
      (proof-with-checked-results ((head (proof-term-at value 1)))
        (if (equal head (proof-quote *proof-quote*))
            (t3-book-mv-nth-recurrence-quote lib value index-result evidence substitutions)
          '(:failure "unsupported" ""))))
     (t '(:failure "unsupported" "")))))

(defun t3-book-mv-nth-recurrence-leaf (raw tests lib premise index-result measure formula template substitutions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (reduced (t3-logic-libraryproofs-normalize lib raw nil nil))
         (value (if reduced (proof-rewritten-term reduced) raw))
         (result (t3-book-mv-nth-recurrence-case lib value premise index-result measure formula evidence substitutions)))
      (if (not reduced)
          result
        (proof-with-checked-results
            ((reversed (proof-proof-symmetric proof reduced))
             (rewritten (proof-proof-rewrite-result proof (car result) reversed template *proof-result*)))
          (cons rewritten (cdr result)))))))

(defund t3-book-mv-nth-recurrence-advance (request lib premise index-result measure formula template substitutions)
  (proof-with-checked-results
      ((leaf (t3-book-mv-nth-recurrence-leaf
              (cadr request) (caddr request) lib premise index-result measure formula template substitutions))
       (next (t3-book-term-collections-by-value-resume lib template request (car leaf))))
    (cons next (cdr leaf))))

(defun t3-book-mv-nth-recurrence-visit (n request lib premise index-result measure formula template substitutions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p request) request)
   ((not (eq (car request) :t3-book-term-collections-leaf))
    (cons request substitutions))
   ((zp n) '(:failure "fuel" "t3-book-mv-nth-recurrence"))
   (t
    (proof-with-checked-results
        ((advanced (t3-book-mv-nth-recurrence-advance
                    request lib premise index-result measure formula template substitutions)))
      (t3-book-mv-nth-recurrence-visit
       (1- n) (car advanced) lib premise index-result measure formula template (cdr advanced))))))

(defun t3-book-mv-nth-recurrence (lib name formula)
  (proof-with-checked-results ((lib (t3-book-mv-nth-nth-equivalence lib)))
    (let ((proof (library-library-proof lib))
          (engine (list *t3-book-mv-nth-recurse* *t3-book-mv-nth-n* *t3-book-mv-nth-term* *library-x*))
          (measure (list *library-count* *t3-book-mv-nth-term*)))
      (proof-with-checked-results
          ((guard (proof-term-at formula 1))
           (premise (proof-proof-assume proof guard t))
           (conclusion (proof-term-at formula 2))
           (index-result (proof-term-at conclusion 2))
           (opened (proof-proof-unfold proof engine))
           (value (proof-rewritten-term opened)))
        (let ((template (proof-eq (list *t3-book-evaluators-eval* *proof-result* *t3-book-mv-nth-env*)
                                  index-result)))
          (proof-with-checked-results
              ((request (t3-book-term-collections-by-value-start lib value nil))
               (cases (t3-book-mv-nth-recurrence-visit
                       1000000 request lib premise index-result measure formula template nil))
               (reversed (proof-proof-symmetric proof opened))
               (derived (proof-proof-rewrite-result proof (car cases) reversed template *proof-result*))
               (step (t3-book-lemmas-implication lib formula derived))
               (ordinal (library-library-builtin lib 1 *t3-book-mv-nth-term*))
               (result (proof-proof-induct proof ordinal step formula measure (table-values (cdr cases))))
               (entry (proof-proof-entry "theorem" name (list name) (list result))))
            (cons entry lib)))))))

(defun t3-book-mv-nth-correctness-leaf (value tests lib)
  (let ((proof (library-library-proof lib)))
    (cond
     ((equal value *library-x*)
      (proof-proof-reflexive proof (list *t3-book-evaluators-eval* *library-x* *t3-book-mv-nth-env*)))
     ((not (proof-is-call value *t3-book-mv-nth-recurse*))
      '(:failure "unsupported" ""))
     (t
      (proof-with-checked-results
          ((evidence (t3-logic-evidence-init lib tests nil nil))
           (applied (t3-book-mv-nth-known-application lib *library-x* *t3-book-mv-nth-env*
                                                     *t3-book-evaluators-mv-nth* evidence))
           (index (t3-book-mv-nth-known-application lib (t3-book-evaluators-second *library-x*)
                                                   *t3-book-mv-nth-env* *proof-quote* (cdr applied)))
           (evaluated (t3-book-spines-replace-value lib (car applied) (list (car index))))
           (form (proof-list-of-length value 4))
           (lemma (proof-proof-fact proof *t3-book-mv-nth-recurrence*
                                    (list (list *t3-book-mv-nth-n* (cadr form))
                                          (list *t3-book-mv-nth-term* (caddr form)))))
           (agrees (proof-proof-modus-ponens proof lemma evaluated))
           (reversed (proof-proof-symmetric proof agrees)))
        (proof-proof-chain proof evaluated (list reversed)))))))

(defund t3-book-mv-nth-correctness-advance (request lib template)
  (proof-with-checked-results
      ((leaf (t3-book-mv-nth-correctness-leaf (cadr request) (caddr request) lib)))
    (t3-book-term-collections-by-value-resume lib template request leaf)))

(defun t3-book-mv-nth-correctness-visit (n request lib template)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p request) request)
   ((not (eq (car request) :t3-book-term-collections-leaf)) request)
   ((zp n) '(:failure "fuel" "t3-book-mv-nth-correctness"))
   (t
    (t3-book-mv-nth-correctness-visit
     (1- n) (t3-book-mv-nth-correctness-advance request lib template) lib template))))

(defun t3-book-mv-nth-correctness (lib name formula)
  (let ((proof (library-library-proof lib))
        (template (proof-eq (list *t3-book-evaluators-eval* *library-x* *t3-book-mv-nth-env*)
                            (list *t3-book-evaluators-eval* *proof-result* *t3-book-mv-nth-env*))))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *t3-book-mv-nth-optimize* *library-x*)))
         (value (proof-rewritten-term opened))
         (request (t3-book-term-collections-by-value-start lib value nil))
         (result (t3-book-mv-nth-correctness-visit 1000000 request lib template))
         (reversed (proof-proof-symmetric proof opened))
         (result (proof-proof-rewrite-result proof result reversed template *proof-result*))
         (literal (proof-step-first result)))
      (if (equal literal formula)
          (proof-proof-entry "theorem" name (list name) (list result))
        '(:failure "unsupported" "")))))
