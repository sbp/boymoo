(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro b2-reversal-declare-events ()
  '(progn

(defconst *b2-reversal-item* (proof-sym "ITEM" "ACL2"))

(defmacro b2-reversal-on-list (lib formula variable advance base)
  `(proof-with-checked-results
       ((advance-request (b2-tactics-tactics-on-list ,lib ,formula ,variable nil nil nil))
        (advance-step (,(car advance)
                       (cadddr (car advance-request))
                       (car (cddddr (car advance-request)))
                       ,@(cdr advance)))
        (advance-reply (cons advance-step (cdr advance-request)))
        (base-request (b2-tactics-tactics-on-list ,lib ,formula ,variable nil advance-reply nil))
        (base-step (,(car base) (cadddr (car base-request)) ,@(cdr base))))
     (b2-tactics-tactics-on-list ,lib ,formula ,variable
                                (cons base-step (cdr base-request)) advance-reply nil)))

(defmacro b2-reversal-implication (lib antecedent target consequent)
  `(proof-with-checked-results
       ((request (b2-tactics-tactics-implication ,lib ,antecedent ,target nil))
        (step (,(car consequent) (cadddr (car request)) ,@(cdr consequent)))
        (result (b2-tactics-tactics-implication ,lib ,antecedent ,target
                                               (cons step (cdr request)))))
     (car result)))

(defun b2-reversal-reversal-rev (lst fn)
  (list fn lst))

(defun b2-reversal-reversal-app (left right append-symbol)
  (list append-symbol left right))

(defun b2-reversal-known (known term)
  (let ((entry (assoc-equal term known)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-reversal-require-equation (equation)
  (or equation '(:failure "failure" "")))

(defun b2-reversal-reversal-app-equation (left right flag evidence library append-symbol axiom)
  (let ((proof (library-library-proof library))
        (target
         (proof-eq
          (b2-reversal-reversal-app left right append-symbol)
          (proof-ite (list *proof-consp* left)
                     (list *proof-cons* (list *library-car* left)
                           (b2-reversal-reversal-app (list *library-cdr* left) right
                                                     append-symbol))
                     right))))
    (proof-with-checked-results
        ((theorem (b2-tactics-tactics-use-fact library axiom target (list flag) nil nil 0 nil))
         (literal (proof-step-first theorem))
         (rhs (proof-term-at literal 2))
         (normalized (b2-tactics-tactics-normalize library rhs evidence nil nil 1500 nil)))
      (proof-proof-chain proof theorem (list normalized)))))

(defun b2-reversal-reversal-shift-base-consequent
    (flag library atom fn append-symbol axiom x singleton appended shifted)
  (proof-with-checked-results
      ((equation (b2-reversal-reversal-app-equation x singleton flag (list atom)
                                                   library append-symbol axiom))
       (empty (b2-reversal-reversal-app-equation *proof-false* singleton flag nil
                                                library append-symbol axiom)))
    (b2-tactics-tactics-solve
     library shifted (list atom)
     (list (b2-reversal-reversal-rev appended fn)
           (b2-reversal-reversal-rev x fn)
           (b2-reversal-reversal-rev *proof-false* fn))
     (list equation empty) 0 nil)))

(defun b2-reversal-reversal-shift-base
    (atom library fn append-symbol axiom x singleton appended enabled shifted)
  (b2-reversal-implication
   library enabled shifted
   (b2-reversal-reversal-shift-base-consequent
    library atom fn append-symbol axiom x singleton appended shifted)))

(defun b2-reversal-reversal-shift-advance-consequent
    (flag library cons-step hypothesis fn append-symbol axiom
          x singleton appended shifted item tail)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((equation (b2-reversal-reversal-app-equation x singleton flag (list cons-step)
                                                     library append-symbol axiom))
         (tail-eq (proof-proof-modus-ponens proof hypothesis flag))
         (swapped (b2-reversal-reversal-app-equation
                   (list *proof-cons* *b2-reversal-item* (b2-reversal-reversal-rev tail fn))
                   (list *proof-cons* item *proof-false*)
                   flag nil library append-symbol axiom)))
      (b2-tactics-tactics-solve
       library shifted (list cons-step)
       (list (b2-reversal-reversal-rev appended fn) (b2-reversal-reversal-rev x fn))
       (list equation tail-eq swapped) 0 nil))))

(defun b2-reversal-reversal-shift-advance
    (cons-step hypothesis library fn append-symbol axiom
               x singleton appended enabled shifted item tail)
  (b2-reversal-implication
   library enabled shifted
   (b2-reversal-reversal-shift-advance-consequent
    library cons-step hypothesis fn append-symbol axiom x singleton appended shifted item tail)))

(defun b2-reversal-reversal-base-consequent (premise library atom fn x proper conclusion)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((steps (b2-tactics-tactics-evidence library (list premise)))
         (equation (b2-tactics-tactics-normalize library proper (list atom)
                                                 (list proper) nil 1500 nil))
         (established (b2-reversal-known steps proper))
         (equation (b2-reversal-require-equation equation))
         (rewritten (proof-proof-rewrite proof established equation '(1)))
         (is-nil (proof-proof-tidy proof rewritten)))
      (b2-tactics-tactics-solve
       library conclusion (list atom is-nil)
       (list (b2-reversal-reversal-rev (b2-reversal-reversal-rev x fn) fn)
             (b2-reversal-reversal-rev x fn) (b2-reversal-reversal-rev *proof-false* fn))
       nil 0 nil))))

(defun b2-reversal-reversal-base (atom library fn x proper condition conclusion)
  (b2-reversal-implication
   library condition conclusion
   (b2-reversal-reversal-base-consequent library atom fn x proper conclusion)))

(defun b2-reversal-reversal-advance-consequent
    (premise library cons-step hypothesis fn x proper enabled lemma item tail)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((steps (b2-tactics-tactics-evidence library (list premise)))
         (flag (b2-reversal-known steps enabled))
         (equation (b2-tactics-tactics-normalize library proper (list cons-step)
                                                 (list proper) nil 1500 nil))
         (established (b2-reversal-known steps proper))
         (equation (b2-reversal-require-equation equation))
         (rewritten (proof-proof-rewrite proof established equation '(1)))
         (child-proper (proof-proof-tidy proof rewritten))
         (hypothesis-literal (proof-step-first hypothesis))
         (hypothesis-condition (proof-term-at hypothesis-literal 1))
         (hypothesis-test (b2-tactics-tactics-solve library hypothesis-condition
                                                  (list flag child-proper) nil nil 0 nil))
         (tail-eq (proof-proof-modus-ponens proof hypothesis hypothesis-test))
         (step (proof-proof-fact proof lemma
                                 (list (list x (b2-reversal-reversal-rev tail fn))
                                       (list *b2-reversal-item* item))))
         (step (proof-proof-modus-ponens proof step flag))
         (call (b2-reversal-reversal-rev x fn))
         (opened (b2-tactics-tactics-normalize library call (list cons-step)
                                               (list call) nil 1500 nil))
         (opened (b2-reversal-require-equation opened))
         (symmetric (proof-proof-symmetric proof opened))
         (restored (proof-proof-rewrite proof step symmetric '(1 1 1)))
         (restored (proof-proof-rewrite proof restored tail-eq '(1 2 2)))
         (elim (library-library-axiom library "CAR-CDR-ELIM" (list x)))
         (rebuilt (proof-proof-modus-ponens proof elim cons-step)))
      (proof-proof-chain proof restored (list rebuilt)))))

(defun b2-reversal-reversal-advance
    (cons-step hypothesis library fn x proper condition conclusion enabled lemma item tail)
  (b2-reversal-implication
   library condition conclusion
   (b2-reversal-reversal-advance-consequent
    library cons-step hypothesis fn x proper enabled lemma item tail)))

(defun b2-reversal-reversal (library formula)
  (proof-with-checked-results
      ((formula-parts (proof-list-of-length formula 3))
       (condition (cadr formula-parts))
       (conclusion (caddr formula-parts))
       (condition-parts (proof-list-of-length condition 4))
       (enabled (cadr condition-parts))
       (proper (caddr condition-parts))
       (conclusion-parts (proof-list-of-length conclusion 3))
       (outer-call (proof-list-of-length (cadr conclusion-parts) 2))
       (inner (cadr outer-call))
       (x (caddr conclusion-parts))
       (fn (proof-term-at inner 0))
       (definitions (proof-proof-definitions (library-library-proof library)))
       (definition (b2-reversal-known definitions fn))
       (body (proof-term-at definition 1))
       (branch (proof-term-at body 2))
       (append-symbol (proof-term-at branch 0))
       (append-name (proof-term-at append-symbol 2))
       (axiom (proof-sym (concatenate 'string append-name "-DEF") "ACL2"))
       (item (list *library-car* x))
       (tail (list *library-cdr* x))
       (singleton (list *proof-cons* *b2-reversal-item* *proof-false*))
       (appended (b2-reversal-reversal-app x singleton append-symbol))
       (shifted (proof-eq (b2-reversal-reversal-rev appended fn)
                          (list *proof-cons* *b2-reversal-item*
                                (b2-reversal-reversal-rev x fn))))
       (auxiliary (list *library-implies* enabled shifted))
       (fn-name (proof-term-at fn 2))
       (lemma-name (concatenate 'string fn-name "-APPEND-SINGLETON"))
       (auxiliary-proof
        (b2-reversal-on-list
         library auxiliary x
         (b2-reversal-reversal-shift-advance
          library fn append-symbol axiom x singleton appended enabled shifted item tail)
         (b2-reversal-reversal-shift-base
          library fn append-symbol axiom x singleton appended enabled shifted)))
       (lemma (b2-tactics-tactics-add-lemma
               (cdr auxiliary-proof) lemma-name (car auxiliary-proof) :none)))
    (let ((library (cdr lemma))
          (lemma (car lemma)))
      (b2-reversal-on-list
       library formula x
       (b2-reversal-reversal-advance
        library fn x proper condition conclusion enabled lemma item tail)
       (b2-reversal-reversal-base library fn x proper condition conclusion)))))
))
