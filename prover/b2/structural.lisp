(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defun b2-structural-step-term (step position)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first position)))

(defun b2-structural-logical-arguments (args)
  (if (endp args) nil
    (proof-with-checked-results
        ((arg (termination-logical-body (car args)))
         (rest (b2-structural-logical-arguments (cdr args))))
      (cons arg rest))))

(defun b2-structural-recursive-arguments (calls)
  (if (endp calls) nil
    (proof-with-checked-results
        ((args (b2-structural-logical-arguments (termination-call-actuals (car calls))))
         (rest (b2-structural-recursive-arguments (cdr calls))))
      (cons args rest))))

(defun b2-structural-cdr-positions (actuals position tail)
  (if (endp actuals) t
    (proof-with-checked-results ((arg (proof-term-at (car actuals) position)))
      (and (equal arg tail) (b2-structural-cdr-positions (cdr actuals) position tail)))))

(defun b2-structural-other-formals (args formals position skip)
  (or (endp args) (endp formals)
      (and (or (equal position skip) (equal (car args) (car formals)))
           (b2-structural-other-formals (cdr args) (cdr formals) (1+ position) skip))))

(defun b2-structural-unchanged-formals (actuals formals skip)
  (if (endp actuals) t
    (and (b2-structural-other-formals (car actuals) formals 0 skip)
         (b2-structural-unchanged-formals (cdr actuals) formals skip))))

(defun b2-structural-cdr-variable (variable position formals calls found)
  (if (not (b2-tactics-variable variable)) found
    (proof-with-checked-results
        ((formal (proof-term-at formals position))
         (actuals (b2-structural-recursive-arguments calls))
         (tails (b2-structural-cdr-positions actuals position (list *library-cdr* formal))))
      (if (and tails (b2-structural-unchanged-formals actuals formals position))
          (table-put found variable (1+ (table-get found variable 0)))
        found))))

(defun b2-structural-cdr-variables (args position formals calls found)
  (if (endp args) found
    (proof-with-checked-results
        ((next (b2-structural-cdr-variable (car args) position formals calls found)))
      (b2-structural-cdr-variables (cdr args) (1+ position) formals calls next))))

(defun b2-structural-count-call (lib call found)
  (proof-with-checked-results ((name (b2-search-head call)))
    (let ((entry (assoc-equal name (proof-proof-definitions (library-library-proof lib)))))
      (if (not entry) found
        (proof-with-checked-results
            ((definition (proof-list-of-length (cdr entry) 2))
             (size (b2-search-size (cadr definition) 70)))
          (if (>= size 70) found
            (proof-with-checked-results
                ((calls (termination-recursive-calls *termination-all* (list entry))))
              (if calls
                  (b2-structural-cdr-variables (cdr call) 0 (car definition) calls found)
                found))))))))

(defun b2-structural-count-calls (lib calls found)
  (if (endp calls) found
    (proof-with-checked-results ((next (b2-structural-count-call lib (car calls) found)))
      (b2-structural-count-calls lib (cdr calls) next))))

(defun b2-structural-insert-count (entry sorted)
  (if (or (endp sorted) (>= (cdr entry) (cdar sorted)))
      (cons entry sorted)
    (cons (car sorted) (b2-structural-insert-count entry (cdr sorted)))))

(defun b2-structural-sort-counts (counts)
  (if (endp counts) nil
    (b2-structural-insert-count (car counts) (b2-structural-sort-counts (cdr counts)))))

(defun b2-structural-list-variables (lib formula)
  (proof-with-checked-results
      ((calls (b2-search-terms formula))
       (found (b2-structural-count-calls lib calls nil)))
    (seq-slice (table-keys (b2-structural-sort-counts found)) :none 2)))

(defun b2-structural-opening-argument-p (args x)
  (and (consp args)
       (or (equal (car args) x)
           (proof-is-call (car args) *proof-cons*)
           (proof-is-call (car args) *proof-quote*)
           (b2-structural-opening-argument-p (cdr args) x))))

(defun b2-structural-opening-call-p (lib call x)
  (proof-with-checked-results ((name (b2-search-head call)))
    (let ((entry (assoc-equal name (proof-proof-definitions (library-library-proof lib)))))
      (and entry
           (proof-with-checked-results
               ((body (proof-term-at (cdr entry) 1))
                (size (b2-search-size body 80)))
             (and (< size 80) (b2-structural-opening-argument-p (cdr call) x)))))))

(defun b2-structural-collect-openers (calls lib x)
  (if (endp calls) nil
    (proof-with-checked-results
        ((include (b2-structural-opening-call-p lib (car calls) x))
         (rest (b2-structural-collect-openers (cdr calls) lib x)))
      (if include (cons (car calls) rest) rest))))

(defun b2-structural-expand-branch-openers (term lib x)
  (proof-with-checked-results ((calls (b2-search-terms term)))
    (b2-structural-collect-openers calls lib x)))

(defun b2-structural-expand-branch (lib goal x evidence rules)
  (proof-with-checked-results
      ((openers (b2-structural-expand-branch-openers goal lib x))
       (equation (b2-tactics-tactics-normalize lib goal evidence openers rules 200 t)))
    (if (not equation) nil
      (proof-with-checked-results
          ((normal (b2-structural-step-term equation 2))
           (openers (b2-structural-expand-branch-openers normal lib x))
           (further (b2-tactics-tactics-normalize lib normal evidence openers rules 200 t)))
        (proof-proof-chain (library-library-proof lib) equation (list further))))))

(defun b2-structural-open-literal (lib literal x branch)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first literal))
         (negative (proof-is-call first *proof-not*))
         (term (if negative (proof-term-at first 1) first)))
      (if (and (proof-compound term) (member-equal x (cdr term)))
          (proof-with-checked-results ((head (b2-search-head term)))
            (let ((definition (assoc-equal head (proof-proof-definitions proof))))
              (if (not definition) nil
                (proof-with-checked-results
                    ((body (proof-term-at (cdr definition) 1))
                     (size (b2-search-size body 70)))
                  (if (>= size 70) nil
                    (proof-with-checked-results
                        ((equation (b2-tactics-tactics-normalize lib term (list branch) (list term)
                                                                nil 160 nil)))
                      (if equation
                          (proof-with-checked-results
                              ((rewritten (proof-proof-rewrite proof literal equation
                                                               (if negative '(1 1) '(1)))))
                            (proof-proof-tidy proof rewritten))
                        nil)))))))
        nil))))

(defun b2-structural-open-evidence (literals lib x branch)
  (if (endp literals) nil
    (proof-with-checked-results
        ((opened (b2-structural-open-literal lib (car literals) x branch))
         (rest (b2-structural-open-evidence (cdr literals) lib x branch)))
      (if opened (cons opened rest) rest))))

(defun b2-structural-antecedent-evidence (lib antecedent x branch)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list antecedent)))
       (opened (b2-structural-open-evidence (table-values known) lib x branch))
       (evidence (b2-tactics-tactics-evidence lib (list* branch antecedent opened))))
    (table-values evidence)))

(defun b2-structural-usable-instance (lib hypothesis evidence)
  (if (not hypothesis) nil
    (proof-with-checked-results ((first (proof-step-first hypothesis)))
      (if (not (proof-is-call first *library-implies*)) hypothesis
        (proof-with-checked-results ((premise (proof-term-at first 1)))
          (let ((instance
                 (proof-with-checked-results
                     ((search (b2-search-search-init lib 8 nil))
                      (guard (car (b2-search-search-prove search premise evidence 1 0))))
                   (proof-proof-modus-ponens (library-library-proof lib) hypothesis guard))))
            (if (b2-tactics-unproved-p instance) nil instance)))))))

(defun b2-structural-induction-at-prove-branch-finish (goal evidence hypothesis lib x)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((instance (b2-structural-usable-instance lib hypothesis evidence))
         (facts (if instance (append evidence (list instance)) evidence))
         (first (and instance (proof-step-first instance)))
         (rules (and instance (proof-is-call first *proof-equal*) (list instance)))
         (solver (b2-search-search-init lib 12 rules))
         (reduction (b2-structural-expand-branch lib goal x facts rules))
         (target (if reduction (b2-structural-step-term reduction 2) goal))
         (answer (car (b2-search-search-prove solver target facts 2 2))))
      (if reduction (proof-proof-transport proof answer reduction) answer))))

(defun b2-structural-implication-branch (case-step hypothesis lib test goal x)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication lib test goal nil))
       (call (car request))
       (callback-lib (caddr call))
       (evidence (b2-structural-antecedent-evidence callback-lib (cadddr call) x case-step))
       (step (b2-structural-induction-at-prove-branch-finish goal evidence hypothesis callback-lib x))
       (result (b2-tactics-tactics-implication lib test goal (cons step callback-lib))))
    (car result)))

(defun b2-structural-induction-at-prove-branch (case-step hypothesis lib formula x)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
        (b2-structural-implication-branch case-step hypothesis lib (car parts) (cadr parts) x))
    (b2-structural-induction-at-prove-branch-finish formula (list case-step) hypothesis lib x)))

(defun b2-structural-induction-at (lib formula x)
  (proof-with-checked-results
      ((advance-request (b2-tactics-tactics-on-list lib formula x nil nil nil))
       (advance-call (car advance-request))
       (advance-lib (caddr advance-call))
       (advance (b2-structural-induction-at-prove-branch
                 (cadddr advance-call) (car (cddddr advance-call)) advance-lib formula x))
       (advance-result (cons advance advance-lib))
       (base-request (b2-tactics-tactics-on-list lib formula x nil advance-result nil))
       (base-call (car base-request))
       (base-lib (caddr base-call))
       (base (b2-structural-induction-at-prove-branch (cadddr base-call) nil base-lib formula x))
       (result (b2-tactics-tactics-on-list lib formula x (cons base base-lib) advance-result nil)))
    (car result)))

(defun b2-structural-try-inductions (variables lib formula)
  (if (endp variables)
      (b2-tactics-unproved)
    (let ((step (b2-structural-induction-at lib formula (car variables))))
      (if (b2-tactics-unproved-p step)
          (b2-structural-try-inductions (cdr variables) lib formula)
        step))))

(defun b2-structural-list-induction (lib formula)
  (proof-with-checked-results ((size (b2-search-size formula 100)))
    (if (>= size 100)
        (b2-tactics-unproved)
      (proof-with-checked-results ((variables (b2-structural-list-variables lib formula)))
        (b2-structural-try-inductions variables lib formula)))))
