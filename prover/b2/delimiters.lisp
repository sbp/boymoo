(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-delimiters-pre* (proof-sym "TRUE-LISTP-OF-SPLIT-///.PRE-///" "STD"))
(defconst *b2-delimiters-post* (proof-sym "TRUE-LISTP-OF-SPLIT-///.POST-///" "STD"))
(defconst *b2-delimiters-return-values* (proof-sym "SYMBOL-LISTP-OF-LOOK-UP-RETURN-VALS" "STD"))
(defconst *b2-delimiters-logic-mode* (proof-sym "BOOLEANP-OF-LOOK-UP-FORMALS" "STD"))

(defconst *b2-delimiters-delimiter-types*
  (list *b2-delimiters-logic-mode* *b2-delimiters-return-values*
        *b2-delimiters-post* *b2-delimiters-pre*))

(defun b2-delimiters-first (step)
  (if (null step)
      '(:failure "failure" "")
    (proof-step-first step)))

(defun b2-delimiters-delimiter-type-leaf (facts lib call after)
  (proof-with-checked-results
      ((opened (b2-tactics-tactics-normalize lib call facts (list call) nil 1500 nil))
       (opened-first (b2-delimiters-first opened))
       (opened-parts (proof-list-of-length opened-first 3))
       (indexed (b2-projections-projected-value lib (if after 1 0) opened facts))
       (equation (car indexed))
       (literal (b2-delimiters-first equation))
       (value (proof-term-at literal 2)))
    (let* ((lib (cdr indexed))
           (typed (list *b2-list-properties-true-list* value)))
      (proof-with-checked-results
          ((step (b2-tactics-tactics-solve lib typed facts (list typed) nil 0 nil))
           (result (library-library-transport-argument lib step equation 1)))
        (cons result lib)))))

(defun b2-delimiters-delimiter-type-choose-reply (lib test evidence call after answer replies)
  (proof-with-checked-results ((value (car answer)))
    (if (eq (car value) :call)
        (proof-with-checked-results
            ((reply (b2-delimiters-delimiter-type-leaf (nth 4 value) (caddr value) call after))
             (replies (append replies (list reply)))
             (next (b2-tactics-choose lib test evidence replies)))
          (cons next replies))
      (cons answer replies))))

(defun b2-delimiters-delimiter-type-choose (lib test evidence call after)
  (proof-with-checked-results
      ((initial (b2-tactics-choose lib test evidence nil))
       (positive (b2-delimiters-delimiter-type-choose-reply lib test evidence call after initial nil))
       (negative (b2-delimiters-delimiter-type-choose-reply
                  lib test evidence call after (car positive) (cdr positive)))
       (step (caar negative)))
    (cons step (cdar negative))))

(defun b2-delimiters-delimiter-type-base-finish (evidence lib call x after atom)
  (b2-delimiters-delimiter-type-choose
   lib x (cons atom evidence) call after))

(defun b2-delimiters-delimiter-type-base (atom lib call x after antecedent target)
  (if after
      (proof-with-checked-results
          ((request (b2-tactics-tactics-implication lib antecedent target nil))
           (pending (car request))
           (reply (b2-delimiters-delimiter-type-base-finish
                   (list (cadddr pending)) (caddr pending) call x after atom))
           (answer (b2-tactics-tactics-implication lib antecedent target reply))
           (step (car answer)))
        (cons step (cdr answer)))
    (b2-delimiters-delimiter-type-base-finish nil lib call x after atom)))

(defun b2-delimiters-delimiter-type-successor-finish
    (premise lib call x test after antecedent cons-step induction present)
  (proof-with-checked-results
      ((truth (b2-tactics-tactics-from-impossible lib x cons-step nil nil nil 1500 nil)))
    (let ((evidence (list cons-step present truth))
          (proof (library-library-proof lib)))
      (if premise
          (proof-with-checked-results
              ((opened (b2-tactics-tactics-normalize
                        lib antecedent (list cons-step) (list antecedent) nil 1500 nil))
               (literal (b2-delimiters-first opened))
               (rewritten (proof-proof-rewrite proof premise opened '(1)))
               (tail (proof-proof-tidy proof rewritten))
               (inherited (proof-proof-modus-ponens proof induction tail)))
            (b2-delimiters-delimiter-type-choose
             lib test (append evidence (list tail inherited)) call after))
        (b2-delimiters-delimiter-type-choose
         lib test (append evidence (list induction)) call after)))))

(defun b2-delimiters-delimiter-type-successor
    (cons-step induction lib call x test after antecedent target)
  (proof-with-checked-results
      ((present (b2-tactics-tactics-from-impossible
                 lib (proof-neg (proof-eq x *proof-false*)) cons-step nil nil nil 1500 nil)))
    (if after
        (proof-with-checked-results
            ((request (b2-tactics-tactics-implication lib antecedent target nil))
             (pending (car request))
             (reply (b2-delimiters-delimiter-type-successor-finish
                     (cadddr pending) (caddr pending) call x test after antecedent
                     cons-step induction present))
             (answer (b2-tactics-tactics-implication lib antecedent target reply))
             (step (car answer)))
          (cons step (cdr answer)))
      (b2-delimiters-delimiter-type-successor-finish
       nil lib call x test after antecedent cons-step induction present))))

(defun b2-delimiters-delimiter-type (lib formula after)
  (proof-with-checked-results
      ((parts (if after
                  (if (integerp formula)
                      (proof-term-at formula 1)
                    (proof-list-of-length (cdr formula) 2))
                (list nil formula)))
       (target-parts (proof-list-of-length (cadr parts) 2))
       (projection (proof-list-of-length (cadr target-parts) 3))
       (x (proof-term-at (caddr projection) 2)))
    (let* ((antecedent (car parts))
           (target (cadr parts))
           (call (caddr projection))
           (test (proof-eq (list *library-car* x) (proof-quote (proof-cl "///")))))
      (proof-with-checked-results
          ((request (b2-tactics-tactics-on-list lib formula x nil nil nil))
           (pending (car request))
           (advance (b2-delimiters-delimiter-type-successor
                     (cadddr pending) (nth 4 pending) (caddr pending) call x test after
                     antecedent target))
           (request-base (b2-tactics-tactics-on-list lib formula x nil advance nil))
           (pending-base (car request-base))
           (base (b2-delimiters-delimiter-type-base
                  (cadddr pending-base) (caddr pending-base) call x after antecedent target))
           (answer (b2-tactics-tactics-on-list lib formula x base advance nil))
           (step (car answer)))
        (cons step (cdr answer))))))

(defun b2-delimiters-property-lookup-facts (lib signed reversed)
  (cond
   ((failure-p reversed) reversed)
   ((endp signed) (reverse reversed))
   (t
    (let ((fact (proof-with-checked-results ((pair (proof-list-of-length (car signed) 2)))
                  (proof-proof-assume (library-library-proof lib) (car pair) (cadr pair)))))
      (b2-delimiters-property-lookup-facts
       lib (cdr signed) (if (failure-p fact) fact (cons fact reversed)))))))

(defun b2-delimiters-property-lookup-selected (sign evidence lib value goal)
  (if (endp evidence)
      '(:failure "tactic-rejected" "")
    (proof-with-checked-results
        ((literal (b2-tactics-tactics-truth-value lib value sign (car (last evidence)))))
      (if (null literal)
          '(:failure "failure" "")
        (b2-tactics-tactics-solve lib goal (append evidence (list literal)) nil nil 0 nil)))))

(defun b2-delimiters-property-lookup-choose-reply (lib test evidence goal answer replies)
  (proof-with-checked-results ((value (car answer)))
    (if (eq (car value) :call)
        (let ((next-lib (caddr value)))
          (proof-with-checked-results
              ((step (b2-delimiters-property-lookup-selected
                      (cadddr value) (nth 4 value) next-lib test goal))
               (replies (append replies (list (cons step next-lib))))
               (next (b2-tactics-choose lib test evidence replies)))
            (cons next replies)))
      (cons answer replies))))

(defun b2-delimiters-property-lookup-choose (lib test evidence goal)
  (proof-with-checked-results
      ((initial (b2-tactics-choose lib test evidence nil))
       (positive (b2-delimiters-property-lookup-choose-reply lib test evidence goal initial nil))
       (negative (b2-delimiters-property-lookup-choose-reply
                  lib test evidence goal (car positive) (cdr positive))))
    (caar negative)))

(defun b2-delimiters-property-lookup-leaf (value signed lib boolean)
  (proof-with-checked-results ((facts (b2-delimiters-property-lookup-facts lib signed nil)))
    (if boolean
        (let* ((yes (proof-eq value *proof-true*))
               (goal (proof-ite yes yes (proof-eq value *proof-false*))))
          (if (or (equal value *proof-true*) (equal value *proof-false*))
              (b2-tactics-tactics-solve lib goal facts nil nil 0 nil)
            (b2-delimiters-property-lookup-choose lib value facts goal)))
      (b2-tactics-tactics-solve lib (list *b2-list-properties-symbol-list* value)
                               facts (list *b2-list-properties-symbol-list*) nil 0 nil))))

(defund b2-delimiters-property-lookup-node (proof value)
  (cond
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
      (cons :if branches)))
   ((and (proof-compound value) (not (consp value)))
    '(:failure "tactic-rejected" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta proof value))
         (literal (b2-delimiters-first equality))
         (opened (proof-term-at literal 2)))
      (list :lambda equality opened)))
   (t nil)))

(defun b2-delimiters-property-lookup-by-value (n lib value template signed boolean)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b2-delimiters-property-lookup-by-value")
    (let* ((proof (library-library-proof lib))
           (node (b2-delimiters-property-lookup-node proof value)))
      (cond
       ((eq (car node) :if)
        (let ((test (cadr node)))
          (proof-with-checked-results
              ((yes (b2-delimiters-property-lookup-by-value
                     (1- n) lib (caddr node) template
                     (append signed (list (list test t))) boolean))
               (no (b2-delimiters-property-lookup-by-value
                    (1- n) lib (cadddr node) template
                    (append signed (list (list test nil))) boolean))
               (if-true (proof-proof-if-true proof value))
               (syes (proof-proof-symmetric proof if-true))
               (yes-proof (proof-proof-rewrite-result proof yes syes template *proof-result*))
               (if-false (proof-proof-if-false proof value))
               (sno (proof-proof-symmetric proof if-false))
               (no-proof (proof-proof-rewrite-result proof no sno template *proof-result*)))
            (proof-proof-cases proof test yes-proof no-proof))))
       ((eq (car node) :lambda)
        (proof-with-checked-results
            ((step (b2-delimiters-property-lookup-by-value
                    (1- n) lib (caddr node) template signed boolean))
             (reversed (proof-proof-symmetric proof (cadr node))))
          (proof-proof-rewrite-result proof step reversed template *proof-result*)))
       ((failure-p node) node)
       (t
        (proof-with-checked-results
            ((step (b2-delimiters-property-lookup-leaf value signed lib boolean))
             (literal (b2-delimiters-first step))
             (expected (proof-subst template (list (cons *proof-result* value)))))
          (if (equal literal expected)
              step
            '(:failure "tactic-rejected" ""))))))))

(defun b2-delimiters-property-lookup (lib formula boolean)
  (proof-with-checked-results
      ((argument (proof-term-at formula 1))
       (call (if boolean (proof-term-at argument 1) argument))
       (equation (b2-tactics-tactics-normalize
                  lib call nil (list call (proof-sym "HARD-ERROR" "ACL2")) nil 1500 t)))
    (let* ((proof (library-library-proof lib))
           (is-true (proof-eq *proof-result* *proof-true*))
           (template (if boolean
                         (proof-ite is-true is-true (proof-eq *proof-result* *proof-false*))
                       (list *b2-list-properties-symbol-list* *proof-result*))))
      (proof-with-checked-results
          ((literal (b2-delimiters-first equation))
           (value (proof-term-at literal 2))
           (proved (b2-delimiters-property-lookup-by-value
                    1000000 lib value template nil boolean))
           (reversed (proof-proof-symmetric proof equation)))
        (proof-proof-rewrite-result proof proved reversed template *proof-result*)))))

(defun b2-delimiters-delimiter-theorem (lib name formula)
  (if (or (equal name *b2-delimiters-pre*) (equal name *b2-delimiters-post*))
      (b2-delimiters-delimiter-type lib formula (equal name *b2-delimiters-post*))
    (proof-with-checked-results
        ((step (b2-delimiters-property-lookup lib formula (equal name *b2-delimiters-logic-mode*))))
      (cons step lib))))
