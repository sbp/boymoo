(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-association-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *b2-association-assoc-cdr* (proof-sym "ASSOC-EQUAL-CDR" "ACL2"))
(defconst *b2-association-strip* (proof-sym "STRIP-CDRS" "ACL2"))
(defconst *b2-association-pseudo-term* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *b2-association-r-symbol-alist* (proof-sym "R-SYMBOL-ALISTP" "ACL2"))

(defun b2-association-evidence-at (steps term)
  (let ((entry (assoc-equal term steps)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-association-lookup-property-base-on-premise
    (premise lib equation atom conclusion base-calls)
  (let ((proof (library-library-proof lib)))
    (if (not equation)
        '(:failure "failure" "")
      (proof-with-checked-results
          ((reduced (proof-proof-rewrite-first proof premise equation))
           (literal (proof-step-first reduced))
           (normalization (b2-tactics-tactics-normalize lib literal nil nil nil 1500 nil))
           (reduced (if normalization
                        (proof-with-checked-results
                            ((rewritten (proof-proof-rewrite proof reduced normalization '(1))))
                          (proof-proof-tidy proof rewritten))
                      reduced)))
        (b2-tactics-tactics-solve lib conclusion (list atom reduced) base-calls
                                (list equation) 0 nil)))))

(defun b2-association-lookup-property-base
    (atom lib antecedent conclusion lookup base-calls)
  (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize lib lookup (list atom)
                                             (list lookup) nil 1500 nil))
       (request (b2-tactics-tactics-implication lib antecedent conclusion nil))
       (result (b2-association-lookup-property-base-on-premise
                (cadddr (car request)) lib equation atom conclusion base-calls))
       (closed (b2-tactics-tactics-implication lib antecedent conclusion (cons result lib))))
    (car closed)))

(defun b2-association-simplified-evidence (lib evidence)
  (if (endp evidence)
      nil
    (let ((proof (library-library-proof lib)) (step (car evidence)))
      (proof-with-checked-results
          ((literal (proof-step-first step))
           (reduction (b2-tactics-tactics-normalize lib literal nil nil nil 1500 nil))
           (simplified (and reduction
                            (proof-with-checked-results
                                ((rewritten (proof-proof-rewrite proof step reduction '(1))))
                              (proof-proof-tidy proof rewritten))))
           (rest (b2-association-simplified-evidence lib (cdr evidence))))
        (if simplified (cons simplified rest) rest)))))

(defun b2-association-recursive-evidence (lib antecedent steps selected known)
  (if (not (proof-is-call antecedent *proof-if*))
      known
    (proof-with-checked-results
        ((test (proof-term-at antecedent 1))
         (visible (b2-association-evidence-at steps test))
         (literal (proof-step-first visible))
         (normalized (b2-tactics-tactics-normalize lib literal nil nil (list selected) 1500 nil))
         (rewritten (if normalized
                        (proof-proof-rewrite (library-library-proof lib) visible normalized '(1))
                      '(:failure "failure" "")))
         (visible (proof-proof-tidy (library-library-proof lib) rewritten)))
      (append known (list visible)))))

(defun b2-association-lookup-branches
    (lib lookup antecedent conclusion test cons-step hypothesis steps known)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((good (proof-proof-assume proof test t))
         (bad (proof-proof-assume proof test nil))
         (selected (b2-tactics-tactics-normalize lib lookup (list cons-step good)
                                                (list lookup) nil 1500 nil))
         (yes (b2-tactics-tactics-solve lib conclusion (list* cons-step good known)
                                      nil (list selected) 0 nil))
         (selected (b2-tactics-tactics-normalize lib lookup (list cons-step bad)
                                                (list lookup) nil 1500 nil))
         (recursive (b2-association-recursive-evidence lib antecedent steps selected known))
         (literal (proof-step-first hypothesis))
         (condition (proof-term-at literal 1))
         (precondition (b2-tactics-tactics-solve lib condition recursive nil nil 0 nil))
         (result (proof-proof-modus-ponens proof hypothesis precondition))
         (symmetric (if selected
                        (proof-proof-symmetric proof selected)
                      '(:failure "failure" "")))
         (no (proof-proof-rewrite-first proof result symmetric)))
      (proof-proof-cases proof test yes no))))

(defun b2-association-lookup-property-advance-on-premise
    (premise lib lookup source source-defs records antecedent conclusion
             test cons-step hypothesis entry-evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((steps (b2-tactics-tactics-evidence lib (list premise)))
         (alist (b2-association-evidence-at steps source))
         (opened (b2-tactics-tactics-normalize lib source (list cons-step)
                                              source-defs nil 1500 nil))
         (rewritten (if opened
                        (proof-proof-rewrite proof alist opened '(1))
                      '(:failure "failure" "")))
         (per-entry (proof-proof-tidy proof rewritten))
         (entry-steps (b2-tactics-tactics-evidence lib (list per-entry)))
         (simplified (b2-association-simplified-evidence lib (table-values entry-steps))))
      (if (eq entry-evidence :request)
          (list :b2-association-entry-evidence records per-entry)
        (proof-with-checked-results ((extra (cadr entry-evidence)))
          (b2-association-lookup-branches
           lib lookup antecedent conclusion test cons-step hypothesis steps
           (append (table-values entry-steps) simplified extra)))))))

(defun b2-association-lookup-property-advance
    (cons-step hypothesis lib lookup source source-defs records antecedent conclusion entry-evidence)
  (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize lib lookup (list cons-step)
                                              (list lookup) nil 1500 nil))
       (literal (if equation
                    (proof-step-first equation)
                  '(:failure "failure" "")))
       (branch (proof-term-at literal 2))
       (test (proof-term-at branch 1))
       (request (b2-tactics-tactics-implication lib antecedent conclusion nil))
       (result (b2-association-lookup-property-advance-on-premise
                (cadddr (car request)) lib lookup source source-defs records antecedent conclusion
                test cons-step hypothesis entry-evidence)))
    (if (eq (car result) :b2-association-entry-evidence)
        result
      (proof-with-checked-results
          ((closed (b2-tactics-tactics-implication lib antecedent conclusion (cons result lib))))
        (car closed)))))

(defun b2-association-lookup-property
    (lib formula lookup source source-calls base-calls entry-evidence)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (lookup-parts (proof-list-of-length lookup 3)))
    (let ((records (caddr lookup-parts)) (antecedent (cadr parts)) (conclusion (caddr parts)))
      (proof-with-checked-results
          ((request (b2-tactics-tactics-on-list lib formula records nil nil nil))
           (advance (b2-association-lookup-property-advance
                     (cadddr (car request)) (car (cddddr (car request))) lib
                     lookup source (cons source source-calls) records antecedent conclusion
                     entry-evidence)))
        (if (eq (car advance) :b2-association-entry-evidence)
            advance
          (proof-with-checked-results
              ((request (b2-tactics-tactics-on-list lib formula records nil (cons advance lib) nil))
               (base (b2-association-lookup-property-base
                      (cadddr (car request)) lib antecedent conclusion lookup base-calls))
               (closed (b2-tactics-tactics-on-list lib formula records
                                                 (cons base lib) (cons advance lib) nil)))
            (car closed)))))))

(defun b2-association-enabled-runep (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (antecedent (cadr parts))
       (arguments (if (integerp antecedent)
                      '(:failure "tactic-rejected" "")
                    (proof-list-of-length (cdr antecedent) 3)))
       (guard (car arguments))
       (lookup (if (proof-is-call guard *library-car*) (proof-term-at guard 1) guard)))
    (b2-association-lookup-property lib formula lookup (cadr arguments)
                                    nil (list *library-natp*) nil)))

(defun b2-association-pseudo-term-of-assoc (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (argument (proof-term-at (caddr parts) 1))
       (lookup (proof-term-at argument 1))
       (source-call (proof-term-at (cadr parts) 1)))
    (b2-association-lookup-property lib formula lookup (cadr parts) (list source-call)
                                    (list *b2-association-pseudo-term*) nil)))

(defun b2-association-symbol-dereference-on-premise
    (premise lib lookup pred test auxiliary conclusion call name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib (list premise)))
         (positive (proof-proof-assume proof lookup t))
         (negative (proof-proof-assume proof lookup nil))
         (source (b2-association-evidence-at known pred))
         (condition (b2-tactics-tactics-solve lib test (list positive source) nil nil 0 nil))
         (yes (proof-proof-modus-ponens proof auxiliary condition))
         (yes (b2-tactics-tactics-solve lib conclusion (list positive yes) (list call) nil 0 nil))
         (symbol (b2-association-evidence-at known (list *b2-tactics-symbolp* name)))
         (no (b2-tactics-tactics-solve lib conclusion (list negative symbol) (list call) nil 0 nil)))
      (proof-proof-cases proof lookup yes no))))

(defun b2-association-symbol-dereference (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (proof-term-at (caddr parts) 1))
       (args (proof-list-of-length call 3)))
    (let* ((name (cadr args))
           (alist (caddr args))
           (antecedent (cadr parts))
           (conclusion (caddr parts))
           (lookup (list *b2-association-assoc* name alist))
           (pred (list *b2-association-r-symbol-alist* alist))
           (test (proof-ite lookup pred *proof-false*))
           (goal (list *b2-tactics-symbolp* (list *library-cdr* lookup))))
      (proof-with-checked-results
          ((auxiliary (b2-association-lookup-property
                       lib (list *library-implies* test goal) lookup pred nil nil nil))
           (request (b2-tactics-tactics-implication lib antecedent conclusion nil))
           (step (b2-association-symbol-dereference-on-premise
                  (cadddr (car request)) lib lookup pred test auxiliary conclusion call name))
           (closed (b2-tactics-tactics-implication lib antecedent conclusion (cons step lib))))
        (car closed)))))
