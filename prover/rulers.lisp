(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *rulers-atom* (proof-cl "ATOM"))
(defconst *rulers-endp* (proof-cl "ENDP"))
(defconst *rulers-test-definitions*
  (list *termination-return-last* *rulers-atom* *rulers-endp*
        (proof-sym "O-FINP" "ACL2") (proof-cl "NULL") (proof-cl "EQ") (proof-cl "EQL")
        (proof-sym "NATP" "ACL2") (proof-sym "ZP" "ACL2")))

(defmacro rulers-let* (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             ,name
           (rulers-let* ,(cdr bindings) ,body))))))

(defun rulers-make-rulers (hypotheses)
  (list :rulers hypotheses))

(defun rulers-rulers-hypotheses (rulers)
  (cadr rulers))

(defun rulers-rulers-init (lib tests extra)
  (rulers-let* ((hypotheses (descent-hypotheses-init lib tests extra)))
    (rulers-make-rulers hypotheses)))

(defun rulers-rulers-proof (rulers)
  (descent-hypotheses-proof (rulers-rulers-hypotheses rulers)))

(defun rulers-rulers-tests (rulers)
  (descent-hypotheses-tests (rulers-rulers-hypotheses rulers)))

(defun rulers-rulers-extra (rulers)
  (descent-hypotheses-extra (rulers-rulers-hypotheses rulers)))

(defun rulers-rulers-found (rulers)
  (descent-hypotheses-found (rulers-rulers-hypotheses rulers)))

(defun rulers-rulers-with-proof (rulers proof)
  (rulers-make-rulers
   (descent-hypotheses-with-proof (rulers-rulers-hypotheses rulers) proof)))

(defun rulers-expand-unfold (proof test holds evidence lambda-call)
  (rulers-let*
   ((equation (if lambda-call (proof-proof-beta proof test) (proof-proof-unfold proof test)))
    (rewritten (proof-proof-rewrite proof evidence equation (if holds '(1) '(1 1))))
    (reduced (proof-proof-tidy proof rewritten))
    (first (proof-step-first equation))
    (body (proof-term-at first 2)))
   (list (list body holds reduced))))

(defun rulers-expand-not (proof test holds evidence)
  (rulers-let*
   ((literal (proof-term-at test 1))
    (evidence (if holds
                  evidence
                (rulers-let* ((negative (proof-proof-assume proof literal nil)))
                  (proof-proof-cut proof negative evidence)))))
   (list (list literal (not holds) evidence))))

(defun rulers-expand-if-false-true (proof test condition yes evidence)
  (rulers-let*
   ((if-false (proof-proof-if-false proof test))
    (impossible (proof-proof-rewrite proof evidence if-false '(1 1)))
    (false-literal (proof-proof-simplify proof (proof-neg *proof-true*) nil (list *proof-not*)))
    (rewritten (proof-proof-rewrite proof impossible false-literal '(1)))
    (impossible (proof-proof-tidy proof rewritten))
    (left (proof-proof-front proof impossible condition))
    (selected (proof-proof-select proof test left))
    (rewritten (proof-proof-rewrite proof evidence selected '(1 1)))
    (right (proof-proof-tidy proof rewritten)))
   (list (list condition t left) (list yes nil right))))

(defun rulers-expand-if-same (proof test condition no evidence)
  (rulers-let*
   ((if-true (proof-proof-if-true proof test))
    (rewritten (proof-proof-rewrite proof evidence if-true '(1 1)))
    (left (proof-proof-tidy proof rewritten))
    (selected (proof-proof-select proof test left))
    (rewritten (proof-proof-rewrite proof evidence selected '(1 1)))
    (right (proof-proof-tidy proof rewritten)))
   (list (list condition nil left) (list no nil right))))

(defun rulers-expand-if (proof test holds evidence)
  (rulers-let* ((args (proof-list-of-length (cdr test) 3)))
    (let ((condition (car args))
          (yes (cadr args))
          (no (caddr args)))
      (cond
       ((and holds (equal no *proof-false*))
        (rulers-let* ((conjuncts (proof-proof-conjunct proof evidence)))
          (list (list condition t (car conjuncts)) (list yes t (cadr conjuncts)))))
       ((and (not holds) (equal no *proof-true*))
        (rulers-expand-if-false-true proof test condition yes evidence))
       ((and (not holds) (equal condition yes))
        (rulers-expand-if-same proof test condition no evidence))
       (t nil)))))

(defun rulers-expand-equal (proof test evidence)
  (rulers-let* ((right (proof-term-at test 2)))
    (if (equal right *proof-false*)
        (rulers-let*
         ((left (proof-term-at test 1))
          (either (proof-proof-nil-or-true proof left))
          (step (proof-proof-cut proof either evidence)))
         (list (list left t step)))
      nil)))

(defun rulers-expansion (proof test holds evidence)
  (if (not (proof-compound test))
      nil
    (rulers-let* ((head (proof-term-at test 0)))
      (let ((lambda-call (proof-compound head)))
        (cond
         ((or lambda-call (member-equal head *rulers-test-definitions*))
          (rulers-expand-unfold proof test holds evidence lambda-call))
         ((equal head *proof-not*) (rulers-expand-not proof test holds evidence))
         ((equal head *proof-if*) (rulers-expand-if proof test holds evidence))
         ((and (equal head *proof-equal*) (not holds))
          (rulers-expand-equal proof test evidence))
         (t nil))))))

(defun rulers-expand-subtree (n proof evidence expansion)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "rulers-expand-subtree"))
   ((failure-p expansion) expansion)
   ((endp expansion) (list evidence))
   ((equal n 1) '(:failure "Fuel" "rulers-expand-subtree"))
   (t
    (let ((first (car expansion))
          (second (cadr expansion)))
      (rulers-let*
       ((left (rulers-expand-subtree (1- n) proof (caddr first)
                                     (rulers-expansion proof (car first) (cadr first) (caddr first))))
        (right (if second
                   (rulers-expand-subtree (1- n) proof (caddr second)
                                          (rulers-expansion proof (car second) (cadr second) (caddr second)))
                 nil)))
       (cons evidence (append left right)))))))

(defun rulers-rulers-expand (n rulers test holds evidence)
  (if (zp n)
      '(:failure "Fuel" "rulers-rulers-expand")
    (let ((proof (descent-proof (rulers-rulers-proof rulers))))
      (rulers-expand-subtree n proof evidence (rulers-expansion proof test holds evidence)))))

(defun rulers-expand-search-visit (proof test holds evidence literal)
  (rulers-let* ((first (proof-step-first evidence)))
    (if (equal first literal)
        (list :found evidence)
      (rulers-expansion proof test holds evidence))))

(defun rulers-expand-search (n proof literal visit)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "rulers-expand-search"))
   ((failure-p visit) visit)
   ((eq (car visit) :found) (cadr visit))
   ((endp visit) nil)
   ((equal n 1) '(:failure "Fuel" "rulers-expand-search"))
   (t
    (let ((first (car visit))
          (second (cadr visit)))
      (rulers-let*
       ((left (rulers-expand-search
               (1- n) proof literal
               (rulers-expand-search-visit proof (car first) (cadr first) (caddr first) literal))))
       (if (or left (not second))
           left
         (rulers-expand-search
          (1- n) proof literal
          (rulers-expand-search-visit proof (car second) (cadr second) (caddr second) literal))))))))

(defun rulers-rulers-expand-first (n rulers test holds evidence literal)
  (if (zp n)
      '(:failure "Fuel" "rulers-rulers-expand-first")
    (let ((proof (descent-proof (rulers-rulers-proof rulers))))
      (rulers-expand-search n proof literal
                            (rulers-expand-search-visit proof test holds evidence literal)))))

(defun rulers-steps-put-new (steps derived)
  (if (endp steps)
      derived
    (rulers-let* ((first (proof-step-first (car steps))))
      (rulers-steps-put-new
       (cdr steps)
       (if (assoc-equal first derived)
           derived
         (table-put derived first (car steps)))))))

(defun rulers-derived-tests (tests rulers proof derived)
  (if (endp tests)
      derived
    (rulers-let*
     ((signed (proof-list-of-length (car tests) 2))
      (term (car signed))
      (holds (cadr signed))
      (evidence (proof-proof-assume proof term holds))
      (steps (rulers-rulers-expand 1000000 rulers term holds evidence))
      (derived (rulers-steps-put-new steps derived)))
     (rulers-derived-tests (cdr tests) rulers proof derived))))

(defun rulers-rulers-derived (rulers)
  (rulers-derived-tests (rulers-rulers-tests rulers) rulers
                        (descent-proof (rulers-rulers-proof rulers)) nil))

(defun rulers-rulers-parent-cons (rulers child evidence child-is-cons)
  (let* ((lib (rulers-rulers-proof rulers))
         (proof (descent-proof lib)))
    (rulers-let*
     ((parts (proof-list-of-length child 2))
      (value (cadr parts))
      (selector (proof-term-at (car parts) 2))
      (completion (library-library-axiom lib (concatenate 'string "COMPLETION-OF-" selector)
                                         (list value)))
      (first (proof-step-first completion))
      (body (proof-term-at first 2))
      (false (proof-proof-if-false proof body))
      (is-nil (proof-proof-chain proof completion (list false)))
      (impossible (proof-proof-rewrite proof evidence is-nil (if child-is-cons '(1 1) '(1))))
      (impossible (if child-is-cons
                      (rulers-let*
                       ((cons-nil (proof-proof-compute proof (list *proof-consp* *proof-false*) *proof-nil*)))
                       (proof-proof-rewrite proof impossible cons-nil '(1)))
                    impossible))
      (tidy (proof-proof-tidy proof impossible)))
     (proof-proof-front proof tidy (list *proof-consp* value)))))

(defun rulers-cons-ancestor-path (rulers child base step child-is-cons)
  (cond
   ((or (failure-p step) (equal child base)) step)
   ((consp (cdr child))
    (rulers-cons-ancestor-path rulers (cadr child) base
                               (rulers-rulers-parent-cons rulers child step child-is-cons) t))
   (t '(:failure "failure" ""))))

(defun rulers-cons-ancestor-in (rulers base derived)
  (if (endp derived)
      nil
    (let ((step (cdar derived)))
      (rulers-let*
       ((term (proof-step-first step))
        (child-is-cons (proof-is-call term *proof-consp*))
        (child (if child-is-cons (proof-term-at term 1) term))
        (edges (terms-selector-edges child base)))
       (if edges
           (rulers-cons-ancestor-path rulers child base step child-is-cons)
         (rulers-cons-ancestor-in rulers base (cdr derived)))))))

(defun rulers-rulers-cons-ancestor (rulers base)
  (rulers-let* ((derived (rulers-rulers-derived rulers)))
    (rulers-cons-ancestor-in rulers base derived)))

(defun rulers-positive-length (proof step first position)
  (rulers-let* ((size (proof-term-at first position)))
    (if (not (proof-is-call size *proof-quote*))
        nil
      (rulers-let* ((number (proof-term-at size 1)))
        (if (not (and (integerp number) (< 0 number)))
            nil
          (rulers-let*
           ((equation (if (equal position 2) step (proof-proof-symmetric proof step)))
            (literal (proof-step-first equation))
            (value (proof-term-at literal 1))
            (opened (proof-proof-simplify proof value nil (list *termination-return-last*)))
            (equation (if opened
                          (rulers-let* ((rewritten (proof-proof-rewrite proof equation opened '(1 1))))
                            (proof-proof-tidy proof rewritten))
                        equation))
            (literal (proof-step-first equation))
            (value (proof-term-at literal 1)))
           (if (proof-is-call value *library-len*) equation nil)))))))

(defun rulers-lengths-in-steps (proof derived)
  (if (endp derived)
      nil
    (let ((step (cdar derived)))
      (rulers-let* ((first (proof-step-first step)))
        (if (not (proof-is-call first *proof-equal*))
            (rulers-lengths-in-steps proof (cdr derived))
          (rulers-let*
           ((left (rulers-positive-length proof step first 1))
            (right (rulers-positive-length proof step first 2))
            (rest (rulers-lengths-in-steps proof (cdr derived))))
           (append (if left (list left) nil) (if right (list right) nil) rest)))))))

(defun rulers-rulers-positive-lengths (rulers)
  (rulers-let* ((derived (rulers-rulers-derived rulers)))
    (rulers-lengths-in-steps (descent-proof (rulers-rulers-proof rulers)) derived)))

(defun rulers-rulers-positive-length-cons (rulers length)
  (let ((proof (descent-proof (rulers-rulers-proof rulers))))
    (rulers-let*
     ((first (proof-step-first length))
      (parts (proof-list-of-length first 3))
      (term (cadr parts))
      (size (caddr parts))
      (opened (proof-proof-unfold proof term))
      (first (proof-step-first opened))
      (body (proof-term-at first 2))
      (false (proof-proof-if-false proof body))
      (zero-if-atom (proof-proof-chain proof opened (list false)))
      (impossible (proof-proof-rewrite proof length zero-if-atom '(1 1)))
      (unequal (proof-proof-compute proof (proof-eq *proof-zero* size) *proof-nil*))
      (impossible (proof-proof-rewrite proof impossible unequal '(1)))
      (tidy (proof-proof-tidy proof impossible))
      (value (proof-term-at term 1)))
     (proof-proof-front proof tidy (list *proof-consp* value)))))

(defun rulers-tail-number (lib proof tail)
  (let ((length-fact (proof-sym "SELF-LEN-NUMBER" "ACL2")))
    (cond
     ((not (member-eq (proof-proof-kind proof) '(:slice :book)))
      (library-library-number lib tail nil))
     ((and (proof-is-call tail *library-len*)
           (assoc-equal length-fact (proof-proof-facts proof)))
      (rulers-let* ((value (proof-term-at tail 1)))
        (proof-proof-fact proof length-fact (list (list *library-x* value)))))
     ((proof-is-call tail *proof-quote*)
      (proof-proof-prove proof (list *library-numberp* tail) nil nil))
     (t (library-library-number lib tail nil)))))

(defun rulers-tail-length-cancel (lib proof tail)
  (rulers-let*
   ((associate (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list *proof-neg-one* *proof-one* tail)))
    (reassociate (proof-proof-symmetric proof associate))
    (zero (proof-proof-compute proof (library-plus *proof-neg-one* *proof-one*) 0))
    (zero-plus (proof-proof-rewrite proof reassociate zero '(1 2 1)))
    (fix (proof-sym "FIX" "ACL2"))
    (number (rulers-tail-number lib proof tail))
    (identity (proof-proof-simplify proof (list fix tail) (list number) (list fix)))
    (unicity (library-library-axiom lib "UNICITY-OF-0" (list tail))))
   (proof-proof-chain proof zero-plus (list unicity identity))))

(defun rulers-rulers-tail-length (rulers length)
  (let* ((lib (rulers-rulers-proof rulers))
         (proof (descent-proof lib)))
    (rulers-let*
     ((first (proof-step-first length))
      (parts (proof-list-of-length first 3))
      (term (cadr parts))
      (size (caddr parts))
      (opened (proof-proof-unfold proof term))
      (first (proof-step-first opened))
      (body (proof-term-at first 2))
      (cons-proof (rulers-rulers-positive-length-cons rulers length))
      (selected (proof-proof-select proof body cons-proof))
      (chain (proof-proof-chain proof opened (list selected)))
      (equation (proof-proof-rewrite proof length chain '(1 1)))
      (first (proof-step-first equation))
      (summation (proof-term-at first 1))
      (tail (proof-term-at summation 2))
      (reflexive (proof-proof-reflexive proof (library-plus *proof-neg-one* summation)))
      (both-sides (proof-proof-rewrite proof reflexive equation '(1 2 2)))
      (cancel (rulers-tail-length-cancel lib proof tail))
      (both-sides (proof-proof-rewrite proof both-sides cancel '(1 1)))
      (number (proof-term-at size 1))
      (smaller (proof-proof-compute proof (library-plus *proof-neg-one* size) (- number 1)))
      (both-sides (proof-proof-rewrite proof both-sides smaller '(1 2))))
     (proof-proof-tidy proof both-sides))))

(defun rulers-length-depth (tail base size depth)
  (cond
   ((equal tail base) (if (< depth size) depth nil))
   ((and (< depth size) (proof-is-call tail *library-cdr*))
    (if (consp (cdr tail))
        (rulers-length-depth (cadr tail) base size (+ depth 1))
      '(:failure "failure" "")))
   (t nil)))

(defun rulers-length-tails (rulers length depth)
  (declare (xargs :measure (nfix depth)))
  (if (or (zp depth) (failure-p length))
      length
    (rulers-length-tails rulers (rulers-rulers-tail-length rulers length) (1- depth))))

(defun rulers-length-cons-in (rulers value lengths)
  (if (endp lengths)
      nil
    (let ((length (car lengths)))
      (rulers-let*
       ((first (proof-step-first length))
        (base (proof-term-at (cadr first) 1))
        (size (proof-term-at (caddr first) 1))
        (depth (rulers-length-depth value base size 0)))
       (if depth
           (rulers-let* ((tail-length (rulers-length-tails rulers length depth)))
             (rulers-rulers-positive-length-cons rulers tail-length))
         (rulers-length-cons-in rulers value (cdr lengths)))))))

(defun rulers-rulers-cons-from-length-test (rulers value)
  (rulers-let* ((lengths (rulers-rulers-positive-lengths rulers)))
    (rulers-length-cons-in rulers value lengths)))

(defun rulers-find-cons (rulers value derived)
  (rulers-let* ((ancestor (rulers-cons-ancestor-in rulers value derived)))
    (if ancestor
        ancestor
      (rulers-let*
       ((lengths (rulers-lengths-in-steps (descent-proof (rulers-rulers-proof rulers)) derived)))
       (rulers-length-cons-in rulers value lengths)))))

(defun rulers-rulers-find (rulers term)
  (rulers-let* ((direct (descent-hypotheses-find (rulers-rulers-hypotheses rulers) term)))
    (let ((next (rulers-make-rulers (cdr direct))))
      (if (car direct)
          (cons (car direct) next)
        (rulers-let* ((derived (rulers-rulers-derived next)))
          (let ((entry (assoc-equal term derived)))
            (cond
             (entry (cons (cdr entry) next))
             ((proof-is-call term *proof-consp*)
              (rulers-let* ((value (proof-term-at term 1))
                             (step (rulers-find-cons next value derived)))
                (if step
                    (cons step
                          (rulers-make-rulers
                           (descent-hypotheses-with-found
                            (cdr direct)
                            (table-put (rulers-rulers-found next) term step))))
                  (cons nil next))))
             (t (cons nil next)))))))))

(defun rulers-rulers-require (rulers term)
  (rulers-let* ((result (rulers-rulers-find rulers term)))
    (if (car result) result (descent-missing-hypothesis term))))

(defun rulers-descent-reply (recipe lib args hypotheses replies request)
  (let* ((term (descent-request-term request))
         (current (rulers-make-rulers (descent-request-hypotheses request)))
         (answer (rulers-rulers-find current term)))
    (if (failure-p answer)
        (cons answer replies)
      (let* ((remember (if (assoc-equal term (rulers-rulers-found (cdr answer))) t nil))
             (replies (table-put replies term (cons (car answer) remember))))
        (cons (descent-query-recipe recipe lib args hypotheses replies) replies)))))

(defun rulers-resolve-descent (n recipe lib args hypotheses pair)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "rulers-resolve-descent")
    (let ((result (car pair)))
      (cond
       ((failure-p result) result)
       ((descent-request-p result)
        (rulers-resolve-descent (1- n) recipe lib args hypotheses
                               (rulers-descent-reply recipe lib args hypotheses (cdr pair) result)))
       (t (cons (car result) (rulers-make-rulers (cdr result))))))))

(defun rulers-descent (recipe lib args rulers)
  (let ((hypotheses (rulers-rulers-hypotheses rulers)))
    (rulers-resolve-descent 1000000 recipe lib args hypotheses
                           (cons (descent-query-recipe recipe lib args hypotheses nil) nil))))

(defun rulers-direct-builtin (lib clause rulers)
  (if rulers
      (rulers-descent :direct-builtin lib (list clause) rulers)
    (descent-direct-builtin lib clause nil)))

(defun rulers-selector-chain (lib child parent rulers)
  (rulers-descent :selector-chain lib (list child parent) rulers))

(defun rulers-selector-decrease (lib goal rulers)
  (rulers-descent :selector-decrease lib (list goal) rulers))

(defun rulers-gap-decrease (lib goal rulers)
  (rulers-descent :gap-decrease lib (list goal) rulers))

(defun rulers-walk-decrease (lib goal rulers)
  (rulers-descent :walk-decrease lib (list goal) rulers))

(defun rulers-run-decrease (lib goal rulers)
  (rulers-descent :run-decrease lib (list goal) rulers))
