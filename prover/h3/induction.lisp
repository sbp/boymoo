(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h3-induction-request-p (value)
  (and (consp value) (eq (car value) :request)))

(defun h3-induction-request-evidence (request)
  (cadr request))

(defun h3-induction-substitutions (replacements)
  (if (endp replacements)
      nil
    (cons (table-items (caar replacements))
          (h3-induction-substitutions (cdr replacements)))))

(defun h3-induction-hypotheses (lib formula measure replacements)
  (if (endp replacements)
      nil
    (let* ((mapping (caar replacements))
           (decrease (cadar replacements))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
       ((new-formula (proof-subst formula mapping))
        (new-measure (proof-subst measure mapping))
        (first (proof-step-first decrease)))
       (let ((smaller (list *proof-ordinal-less* new-measure measure)))
         (if (not (equal first smaller))
             '(:failure "proof-mismatch" "")
           (proof-with-checked-results
            ((assumption (proof-proof-assume
                          proof (proof-ite smaller new-formula *proof-true*) t))
             (hypothesis (proof-proof-prove-if proof assumption decrease))
             (rest (h3-induction-hypotheses lib formula measure (cdr replacements))))
            (cons (list hypothesis (cdr (proof-step-clause decrease))) rest))))))))

(defun h3-induction-conditions (hypotheses)
  (if (endp hypotheses)
      nil
    (append (cadar hypotheses) (h3-induction-conditions (cdr hypotheses)))))

(defun h3-induction-enabled (hypotheses excluded)
  (cond ((endp hypotheses) nil)
        ((intersectp-equal excluded (cadar hypotheses))
         (h3-induction-enabled (cdr hypotheses) excluded))
        (t (cons (caar hypotheses)
                 (h3-induction-enabled (cdr hypotheses) excluded)))))

(defun h3-induction-well-founded-split
    (guards evidence excluded lib hypotheses replies)
  (declare (xargs :measure (acl2-count guards)))
  (if (endp guards)
      (if (endp replies)
          (cons (list :request
                      (append evidence (h3-induction-enabled hypotheses excluded)))
                nil)
        replies)
    (let* ((test (car guards))
           (proof (library-library-proof lib))
           (positive (proof-proof-assume proof test t)))
      (if (failure-p positive)
          (cons positive replies)
        (let* ((yes-answer (h3-induction-well-founded-split
                            (cdr guards) (append evidence (list positive))
                            (cons test excluded) lib hypotheses replies))
               (yes (car yes-answer)))
          (if (or (failure-p yes) (h3-induction-request-p yes))
              yes-answer
            (let ((negative (proof-proof-assume proof test nil)))
              (if (failure-p negative)
                  (cons negative (cdr yes-answer))
                (let* ((no-answer (h3-induction-well-founded-split
                                   (cdr guards) (append evidence (list negative))
                                   excluded lib hypotheses (cdr yes-answer)))
                       (no (car no-answer)))
                  (if (or (failure-p no) (h3-induction-request-p no))
                      no-answer
                    (cons (proof-proof-cases proof test yes no)
                          (cdr no-answer))))))))))))

(defun h3-induction-well-founded (lib formula measure ordinal replacements prove-case)
  (let ((substitutions (h3-induction-substitutions replacements)))
    (proof-with-checked-results
     ((hypotheses (h3-induction-hypotheses lib formula measure replacements))
      (case (car (h3-induction-well-founded-split
                  (proof-unique (h3-induction-conditions hypotheses))
                  nil nil lib hypotheses prove-case))))
     (if (h3-induction-request-p case)
         case
       (proof-proof-induct (library-library-proof lib)
                           ordinal case formula measure substitutions)))))

(defun h3-induction-decreases (lib variable replacements)
  (if (endp replacements)
      nil
    (let ((reason (cadar replacements)))
      (proof-with-checked-results
       ((decrease (cond ((integerp reason) (library-library-builtin lib reason variable))
                        ((or (eq reason t) (null reason))
                         (proof-proof-fact (library-library-proof lib)
                                           (if reason "built-in-clause-True" "built-in-clause-False")
                                           (list (list *library-x* variable))))
                        (t reason)))
        (rest (h3-induction-decreases lib variable (cdr replacements))))
       (cons (list (caar replacements) decrease) rest)))))

(defun h3-induction-structural-induction (lib formula variable replacements prove-case)
  (proof-with-checked-results
   ((decreases (h3-induction-decreases lib variable replacements))
    (ordinal (library-library-builtin lib 1 variable)))
   (h3-induction-well-founded lib formula (list *library-count* variable)
                             ordinal decreases prove-case)))

