(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *termination-proofs-selector-definitions*
  (list *termination-return-last* *rulers-atom* *proof-not*
        (proof-sym "O-FINP" "ACL2")
        (proof-sym "O-FIRST-EXPT" "ACL2")
        (proof-sym "O-RST" "ACL2")))

(defconst *termination-proofs-minimum-formals*
  (list *library-x* *library-y* (proof-sym "U" "ACL2") (proof-sym "V" "ACL2")))

(defconst *termination-proofs-minimum-less* (proof-sym "SELF-MINIMUM-LESS" "ACL2"))

(defun termination-proofs-callback-p (object)
  (and (consp object) (eq (car object) :call)))

(defun termination-proofs-stop-p (object)
  (or (failure-p object) (termination-proofs-callback-p object)))

(defmacro termination-proofs-check (bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding)))
      `(let (,binding)
         (if (failure-p ,name)
             ,name
           (termination-proofs-check ,(cdr bindings) ,body))))))

; Tactic results cannot affect the fuel decrease.
(defmacro termination-proofs-check-in (context bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding)))
      `(let ((,name (hide ,(cadr binding))))
         (if (hide (termination-proofs-stop-p ,name))
             (cons ,name ,context)
           (termination-proofs-check-in ,context ,(cdr bindings) ,body))))))

(defmacro termination-proofs-bind (context binding body)
  `(let* ((termination-proofs-binding-result (hide ,(cadr binding)))
          (,(car binding) (car termination-proofs-binding-result))
          (,context (cdr termination-proofs-binding-result)))
     (if (hide (termination-proofs-stop-p ,(car binding)))
         termination-proofs-binding-result
       ,body)))

(defun termination-proofs-context (lib rulers extra-descent extra-ordinality)
  (list lib rulers extra-descent extra-ordinality))

(defun termination-proofs-context-lib (context)
  (car context))

(defun termination-proofs-context-rulers (context)
  (cadr context))

(defun termination-proofs-context-descent (context)
  (caddr context))

(defun termination-proofs-context-ordinality (context)
  (cadddr context))

(defun termination-proofs-with-rulers (context rulers)
  (termination-proofs-context (termination-proofs-context-lib context)
                              rulers
                              (termination-proofs-context-descent context)
                              (termination-proofs-context-ordinality context)))

(defun termination-proofs-with-lib (context lib)
  (cons lib (cdr context)))

(defun termination-proofs-library-answer (answer context)
  (if (failure-p answer)
      (cons answer context)
    (cons (car answer) (termination-proofs-with-lib context (cdr answer)))))

(defun termination-proofs-rulers-answer (answer context)
  (if (failure-p answer)
      (cons answer context)
    (cons (car answer) (termination-proofs-with-rulers context (cdr answer)))))

(defun termination-proofs-library-and-rulers-answer (answer context)
  (if (failure-p answer)
      (cons answer context)
    (cons (caar answer)
          (termination-proofs-with-rulers
           (termination-proofs-with-lib context (cdr answer)) (cadar answer)))))

(defun termination-proofs-public-result (answer)
  (cons (car answer) (termination-proofs-context-lib (cdr answer))))

(defun termination-proofs-rulers-for-library (context)
  (let ((rulers (termination-proofs-context-rulers context))
        (lib (termination-proofs-context-lib context)))
    (if (or (not rulers) (equal (rulers-rulers-proof rulers) lib))
        rulers
      (rulers-rulers-with-proof rulers lib))))

(defun termination-proofs-structural-decrease-in (goal context)
  (let ((child (cadr goal))
        (parent (caddr goal)))
    (cond
     ((not (eql (len goal) 3))
      (cons *terms-invalid-proof-arity* context))
     ((not (and (proof-is-call child *library-count*)
                (proof-is-call parent *library-count*)))
      (cons nil context))
     ((or (not (consp (cdr parent))) (not (consp (cdr child))))
      (cons '(:failure "failure" "") context))
     (t
      (let ((base (cadr parent)))
        (termination-proofs-check-in context
            ((rulers (termination-proofs-rulers-for-library context)))
          (termination-proofs-bind context
              (cons-proof
               (termination-proofs-rulers-answer
                (rulers-rulers-find rulers (list *proof-consp* base)) context))
            (let* ((lib (termination-proofs-context-lib context))
                   (proof (library-library-proof lib)))
              (termination-proofs-check-in context
                  ((opened (proof-proof-simplify
                            proof (cadr child) (if cons-proof (list cons-proof) nil)
                            *termination-proofs-selector-definitions*))
                   (equation (if opened (proof-step-first opened) nil))
                   (actual (if opened (caddr equation) (cadr child)))
                   (edges (terms-selector-edges actual base)))
                (if (not (and cons-proof edges))
                    (cons nil context)
                  (termination-proofs-bind context
                      (path (termination-proofs-library-and-rulers-answer
                             (selector-proofs-selector-path-descent-with-rulers
                              lib actual edges
                              (termination-proofs-context-rulers context))
                             context))
                    (termination-proofs-check-in context
                        ((rulers (termination-proofs-rulers-for-library context)))
                      (let* ((lib (termination-proofs-context-lib context))
                             (proof (library-library-proof lib))
                             (normal-goal (list *proof-ordinal-less*
                                                (list *library-count* actual)
                                                parent)))
                        (termination-proofs-bind context
                            (step (if path
                                      (cons path context)
                                    (termination-proofs-rulers-answer
                                     (rulers-selector-decrease lib normal-goal rulers)
                                     context)))
                          (termination-proofs-check-in context
                              ((result (if opened
                                           (termination-proofs-check
                                               ((reverse (proof-proof-symmetric proof opened))
                                                (rewrite (proof-proof-rewrite
                                                          proof step reverse '(1 1 1))))
                                             (proof-proof-tidy proof rewrite))
                                         step)))
                            (cons result context))))))))))))))))

(defun termination-proofs-structural-decrease (lib goal rulers)
  (termination-proofs-public-result
   (termination-proofs-structural-decrease-in
    goal (termination-proofs-context lib rulers nil nil))))

(mutual-recursion
 (defun termination-proofs-count-or-length-sum (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((and (consp term) (proof-is-call term *proof-plus*))
     (termination-proofs-count-or-length-sum-list (cdr term)))
    ((or (proof-is-call term *library-count*) (proof-is-call term *library-len*)) t)
    ((proof-is-call term *proof-quote*)
     (if (consp (cdr term))
         (or (eq (cadr term) t) (natp (cadr term)))
       '(:failure "failure" "")))
    (t nil)))

 (defun termination-proofs-count-or-length-sum-list (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       t
     (termination-proofs-check
         ((first (termination-proofs-count-or-length-sum (car terms))))
       (and first (termination-proofs-count-or-length-sum-list (cdr terms)))))))

(defun termination-proofs-length-decrease-in (goal context)
  (let ((child (cadr goal))
        (parent (caddr goal))
        (lib (termination-proofs-context-lib context)))
    (cond
     ((not (eql (len goal) 3))
      (cons *terms-invalid-proof-arity* context))
     ((not (proof-is-call parent *library-len*)) (cons nil context))
     ((not (consp (cdr parent))) (cons '(:failure "failure" "") context))
     ((not (equal child (list *library-len* (list *library-cdr* (cadr parent)))))
      (cons nil context))
     (t
      (termination-proofs-check-in context
          ((rulers (termination-proofs-rulers-for-library context)))
        (termination-proofs-bind context
            (cons-proof (termination-proofs-rulers-answer
                         (rulers-rulers-find rulers (list *proof-consp* (cadr parent)))
                         context))
          (if (not cons-proof)
              (cons nil context)
            (termination-proofs-check-in context
                ((less (library-library-cite lib "LEN-CDR-LESS" (cdr parent)
                                             (list cons-proof)))
                 (comparison (library-library-ordinal-comparison lib child parent))
                 (result (proof-proof-transport (library-library-proof lib)
                                                less comparison)))
              (cons result context)))))))))

(defun termination-proofs-length-decrease (lib goal rulers)
  (car (termination-proofs-length-decrease-in
        goal (termination-proofs-context lib rulers nil nil))))

(defun termination-proofs-required-binding (key bindings)
  (let ((binding (assoc-equal key bindings)))
    (if binding
        (cdr binding)
      '(:failure "failure" ""))))

(defun termination-proofs-minimum-lemma-parent-branch-child-branch
    (smaller tests aligned greater lib integers)
  (termination-proofs-check
      ((literal (proof-step-first aligned))
       (middle (proof-term-at literal 1)))
    (let ((proof (library-library-proof lib)))
      (cond
       ((equal smaller middle) aligned)
       ((endp tests) '(:failure "failure" ""))
       (t
        (termination-proofs-check
            ((test (proof-list-of-length (car (last tests)) 2))
             (smaller-type (termination-proofs-required-binding smaller integers))
             (middle-type (termination-proofs-required-binding middle integers))
             (greater-type (termination-proofs-required-binding greater integers))
             (assumed (proof-proof-assume proof (car test) (cadr test))))
          (library-library-cite lib (if (cadr test) "LESS-TRANSITIVE" "WEAK-THEN-LESS")
                                (list smaller middle greater)
                                (list smaller-type middle-type greater-type assumed aligned))))))))

(defun termination-proofs-minimum-child-leaves (leaves aligned greater lib integers)
  (if (endp leaves)
      nil
    (let ((leaf (car leaves)))
      (termination-proofs-check
          ((step (termination-proofs-minimum-lemma-parent-branch-child-branch
                  (car leaf) (cadr leaf) aligned greater lib integers))
           (rest (termination-proofs-minimum-child-leaves
                  (cdr leaves) aligned greater lib integers)))
        (cons (cons leaf step) rest)))))

(defun termination-proofs-minimum-lemma-parent-branch
    (greater tests lib child-eq comparisons integers)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib))
        (template (list *proof-less* *proof-result* greater)))
    (termination-proofs-check
        ((aligned (termination-proofs-required-binding greater comparisons))
         (equation (proof-step-first child-eq))
         (body (proof-term-at equation 2))
         (leaves (proof-proof-by-value-leaves proof body nil))
         (answers (termination-proofs-minimum-child-leaves leaves aligned greater lib integers))
         (step (lemmas-slice-library-by-value lib body template answers nil)))
      (library-library-transport-argument lib step child-eq 1))))

(defun termination-proofs-minimum-parent-leaves (leaves lib child-eq comparisons integers)
  (if (endp leaves)
      nil
    (let ((leaf (car leaves)))
      (termination-proofs-check
          ((step (termination-proofs-minimum-lemma-parent-branch
                  (car leaf) (cadr leaf) lib child-eq comparisons integers))
           (rest (termination-proofs-minimum-parent-leaves
                  (cdr leaves) lib child-eq comparisons integers)))
        (cons (cons leaf step) rest)))))

(defun termination-proofs-negated-steps (steps)
  (if (endp steps)
      nil
    (termination-proofs-check
        ((first (proof-step-first (car steps)))
         (rest (termination-proofs-negated-steps (cdr steps))))
      (cons (proof-neg first) rest))))

(defun termination-proofs-minimum-lemma (lib)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal *termination-proofs-minimum-less* (proof-proof-facts proof))
        lib
      (let* ((x (car *termination-proofs-minimum-formals*))
             (y (cadr *termination-proofs-minimum-formals*))
             (u (caddr *termination-proofs-minimum-formals*))
             (v (cadddr *termination-proofs-minimum-formals*))
             (child (list *lemmas-min* x y))
             (parent (list *lemmas-min* u v))
             (template (list *proof-less* child *proof-result*)))
        (termination-proofs-check
            ((child-eq (proof-proof-unfold proof child))
             (parent-eq (proof-proof-unfold proof parent))
             (integer-steps (library-library-ints lib *termination-proofs-minimum-formals*))
             (aligned-u (proof-proof-assume proof (library-lt x u) t))
             (aligned-v (proof-proof-assume proof (library-lt y v) t))
             (equation (proof-step-first parent-eq))
             (leaves (proof-proof-by-value-leaves proof (caddr equation) nil))
             (answers (termination-proofs-minimum-parent-leaves
                       leaves lib child-eq (list (cons u aligned-u) (cons v aligned-v))
                       (pairlis$ *termination-proofs-minimum-formals* integer-steps)))
             (step (lemmas-slice-library-by-value lib (caddr equation) template answers nil))
             (less (library-library-transport-argument lib step parent-eq 2))
             (claim (proof-step-first less))
             (guards (termination-proofs-negated-steps
                      (append integer-steps (list aligned-u aligned-v)))))
          (library-library-lemma lib "MINIMUM-LESS" claim less guards))))))

(defun termination-proofs-natural-fuel (operation lib)
  (cons (list :failure "Fuel" operation) lib))

; Complete the natural-number proof requests while retaining the library
; established before any failed request.
(mutual-recursion
 (defun termination-proofs-natural-result (n lib term)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (termination-proofs-natural-fuel "termination-proofs-natural-result" lib)
     (termination-proofs-check-in lib
         ((task (lemmas-natural-prepare lib term)))
       (case (car task)
         (:return (cadr task))
         (:length
          (let ((lib (cadr task)))
            (termination-proofs-bind lib
                (leaves (termination-proofs-natural-results
                         (1- n) lib (caddr (cddddr task)) t))
              (let ((answer (lemmas-natural-finish-length task (cons leaves lib))))
                (if (failure-p answer) (cons answer lib) answer)))))
         (otherwise
          (let ((lib (cadr task))
                (name (caddr task))
                (arguments (cadddr task)))
            (termination-proofs-bind lib
                (evidence (termination-proofs-natural-results (1- n) lib arguments nil))
              (cons (library-library-cite lib name arguments evidence) lib))))))))

 (defun termination-proofs-natural-results (n lib requests leaf-requests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (termination-proofs-natural-fuel "termination-proofs-natural-results" lib))
    ((endp requests) (cons nil lib))
    (t
     (let* ((request (car requests))
            (term (if leaf-requests (car request) request)))
       (termination-proofs-bind lib
           (step (termination-proofs-natural-result (1- n) lib term))
         (termination-proofs-bind lib
             (rest (termination-proofs-natural-results (1- n) lib (cdr requests) leaf-requests))
           (cons (cons (if leaf-requests (cons request step) step) rest) lib))))))))

(defun termination-proofs-type-from-natural-p (lib term)
  (or (proof-is-call term *lemmas-length*)
      (and (or (proof-is-call term *lemmas-nfix*) (proof-is-call term *lemmas-min*))
           (assoc-equal (car term) (proof-proof-definitions (library-library-proof lib))))))

(mutual-recursion
 (defun termination-proofs-type-of-result (n lib term)
   (declare (xargs :measure (nfix n)))
   (let ((head (car term)))
     (cond
      ((zp n) (termination-proofs-natural-fuel "termination-proofs-type-of-result" lib))
      ((termination-proofs-type-from-natural-p lib term)
       (termination-proofs-bind lib
           (natural (termination-proofs-natural-result 1000000 lib term))
         (cons (library-library-cite lib "NATURAL-INTEGER" (list term) (list natural))
               lib)))
      ((and (proof-compound term)
            (member-equal head (list *proof-plus* *proof-times* *proof-minus*)))
       (termination-proofs-check-in lib
           ((arguments (if (equal head *proof-minus*)
                           (termination-proofs-check ((argument (proof-term-at term 1)))
                             (list argument))
                         (cdr term))))
         (termination-proofs-bind lib
             (evidence (termination-proofs-type-of-results (1- n) lib arguments))
           (let ((name (cond ((equal head *proof-plus*) "INTEGER-SUM")
                             ((equal head *proof-times*) "INTEGER-PRODUCT")
                             (t "INTEGER-NEGATION"))))
             (cons (library-library-cite lib name (cdr term) evidence) lib)))))
      (t (cons (library-library-type-of lib term nil) lib)))))

 (defun termination-proofs-type-of-results (n lib terms)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (termination-proofs-natural-fuel "termination-proofs-type-of-results" lib))
    ((endp terms) (cons nil lib))
    (t
     (termination-proofs-bind lib
         (step (termination-proofs-type-of-result (1- n) lib (car terms)))
       (termination-proofs-bind lib
           (rest (termination-proofs-type-of-results (1- n) lib (cdr terms)))
         (cons (cons step rest) lib)))))))

(defun termination-proofs-type-of (term context)
  (let ((lib (termination-proofs-context-lib context)))
    (if (proof-uses-slice-rules-p (library-library-proof lib))
        (termination-proofs-library-answer
         (termination-proofs-type-of-result 1000000 lib term) context)
      (cons (library-library-type-of lib term nil) context))))

(defun termination-proofs-ordinal-comparison (after before context)
  (termination-proofs-bind context
      (after-type (termination-proofs-type-of after context))
    (termination-proofs-bind context
        (before-type (termination-proofs-type-of before context))
      (cons (library-library-cite (termination-proofs-context-lib context)
                                  "FINITE-ORDER" (list after before)
                                  (list after-type before-type))
            context))))

(defun termination-proofs-ordinal-to-less (ordinal after before context)
  (termination-proofs-bind context
      (comparison (termination-proofs-ordinal-comparison after before context))
    (let ((proof (library-library-proof (termination-proofs-context-lib context))))
      (termination-proofs-check-in context
          ((less (proof-proof-rewrite proof ordinal comparison '(1))))
        (cons (proof-proof-tidy proof less) context)))))

(defun termination-proofs-less-to-ordinal (less after before context)
  (termination-proofs-bind context
      (comparison (termination-proofs-ordinal-comparison after before context))
    (cons (proof-proof-transport (library-library-proof (termination-proofs-context-lib context))
                                 less comparison)
          context)))

(defun termination-proofs-minimum-type-evidence (values context)
  (if (endp values)
      (cons nil context)
    (termination-proofs-bind context
        (step (termination-proofs-type-of (car values) context))
      (termination-proofs-bind context
          (rest (termination-proofs-minimum-type-evidence (cdr values) context))
        (cons (cons step rest) context)))))

(defun termination-proofs-minimum-finish (child parent comparisons context)
  (termination-proofs-check-in context
      ((lib (termination-proofs-minimum-lemma (termination-proofs-context-lib context))))
    (let* ((context (termination-proofs-with-lib context lib))
           (values (append (cdr child) (cdr parent))))
      (termination-proofs-bind context
          (types (termination-proofs-minimum-type-evidence values context))
        (let ((lib (termination-proofs-context-lib context)))
          (termination-proofs-check-in context
              ((less (proof-proof-use
                      (library-library-proof lib) *termination-proofs-minimum-less*
                      (seq-zip *termination-proofs-minimum-formals* values)
                      (append types comparisons))))
            (termination-proofs-less-to-ordinal less child parent context)))))))

(defun termination-proofs-sum-finish (child parent bounds context)
  (if (endp bounds)
      (cons nil context)
    (let ((lib (termination-proofs-context-lib context)))
      (termination-proofs-check-in context
          ((less (if (consp (cdr bounds))
                     (library-library-compare-chain lib (car bounds) (cadr bounds))
                   (car bounds))))
        (termination-proofs-less-to-ordinal less child parent context)))))

(defconst *termination-proofs-descent-tactics*
  '((:selector "selector descent")
    (:wrapped "wrapped countdown")
    (:subtraction "positive integer subtraction")
    (:clipped "clipped countdown")
    (:length "length descent")))

(defun termination-proofs-rule-step (rule goal context)
  (case rule
    (:selector (termination-proofs-structural-decrease-in goal context))
    (:length (termination-proofs-length-decrease-in goal context))
    (otherwise
     (let ((lib (termination-proofs-context-lib context)))
       (termination-proofs-check-in context
           ((rulers (termination-proofs-rulers-for-library context)))
         (termination-proofs-library-and-rulers-answer
          (case rule
            (:wrapped (countdowns-wrapped-countdown-with-rulers lib goal rulers))
            (:subtraction (subtraction-subtraction-decrease-with-rulers lib goal rulers))
            (otherwise (countdowns-clipped-decrease-with-rulers lib goal rulers)))
          context))))))

(defun termination-proofs-tactics (tactics goal context)
  (if (endp tactics)
      (cons nil context)
    (termination-proofs-bind context
        (step (termination-proofs-rule-step (caar tactics) goal context))
      (if step
          (cons (list step (cadar tactics)) context)
        (termination-proofs-tactics (cdr tactics) goal context)))))

(defun termination-proofs-descent-reply (step lib rulers)
  (list :descent-reply step lib rulers))

(defun termination-proofs-extra-descent (goal context)
  (termination-proofs-check-in context
      ((rulers (termination-proofs-rulers-for-library context)))
    (let* ((lib (termination-proofs-context-lib context))
           (replies (cdr (termination-proofs-context-descent context)))
           (ordinality (termination-proofs-context-ordinality context)))
      (if (endp replies)
          (cons (list :call :descent lib goal rulers) context)
        (let ((reply (car replies)))
          (if (eq (car reply) :descent-reply)
              (cons (cadr reply)
                    (termination-proofs-context
                     (caddr reply) (cadddr reply) (cons t (cdr replies)) ordinality))
            (cons (car reply)
                  (termination-proofs-context
                   (cdr reply) rulers (cons t (cdr replies)) ordinality))))))))

(defun termination-proofs-fuel (name context)
  (cons (list :failure "Fuel" name) context))

(mutual-recursion
 (defun termination-proofs-prove-decrease-in (n clause context)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (termination-proofs-fuel "termination-proofs-prove-decrease-in" context)
     (let ((goal (car (last clause)))
           (lib (termination-proofs-context-lib context)))
       (termination-proofs-check-in context
           ((rulers (termination-proofs-rulers-for-library context)))
         (termination-proofs-bind context
             (direct (termination-proofs-rulers-answer
                      (rulers-direct-builtin lib clause rulers) context))
           (if direct
               (cons (list direct "built-in clauses") context)
             (termination-proofs-bind context
                 (found (termination-proofs-tactics
                         *termination-proofs-descent-tactics* goal context))
               (if found
                   (cons found context)
                 (termination-proofs-bind context
                     (minimum (termination-proofs-minimum-decrease-in (1- n) clause context))
                   (if minimum
                       (cons (list minimum "minimum descent") context)
                     (termination-proofs-bind context
                         (sum (termination-proofs-sum-decrease-in (1- n) clause context))
                       (if (or sum (not (termination-proofs-context-descent context)))
                           (cons (list sum "additive descent") context)
                         (termination-proofs-bind context
                             (extra (termination-proofs-extra-descent goal context))
                           (cons (list extra "book reduction and comparisons") context))))))))))))))

 (defun termination-proofs-minimum-decrease-in (n clause context)
   (declare (xargs :measure (nfix n)))
   (let* ((goal (car (last clause)))
          (child (cadr goal))
          (parent (caddr goal)))
     (cond
      ((zp n) (termination-proofs-fuel "termination-proofs-minimum-decrease-in" context))
      ((endp clause) (cons '(:failure "failure" "") context))
      ((not (eql (len goal) 3))
       (cons *terms-invalid-proof-arity* context))
      ((not (and (proof-is-call child *lemmas-min*) (proof-is-call parent *lemmas-min*)))
       (cons nil context))
      (t
       (let ((attempt (termination-proofs-minimum-comparisons
                       (1- n) child parent (seq-zip (cdr child) (cdr parent))
                       (butlast clause 1) nil context)))
         (if (terms-proof-fallback-p (car attempt))
             (cons nil (cdr attempt))
           attempt))))))

 (defun termination-proofs-minimum-comparisons
     (n child parent pairs side-literals comparisons context)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (termination-proofs-fuel "termination-proofs-minimum-comparisons" context))
    ((endp pairs) (termination-proofs-minimum-finish child parent (reverse comparisons) context))
    (t
     (let* ((smaller (caar pairs))
            (greater (cadar pairs))
            (clause (append side-literals (list (list *proof-ordinal-less* smaller greater)))))
       (termination-proofs-bind context
           (result (termination-proofs-prove-decrease-in (1- n) clause context))
         (if (not (car result))
             (cons nil context)
           (termination-proofs-bind context
               (less (termination-proofs-ordinal-to-less (car result) smaller greater context))
             (termination-proofs-minimum-comparisons
              (1- n) child parent (cdr pairs) side-literals (cons less comparisons) context))))))))

 (defun termination-proofs-sum-decrease-in (n clause context)
   (declare (xargs :measure (nfix n)))
   (let* ((goal (car (last clause)))
          (child (cadr goal))
          (parent (caddr goal)))
     (cond
      ((zp n) (termination-proofs-fuel "termination-proofs-sum-decrease-in" context))
      ((endp clause) (cons '(:failure "failure" "") context))
      ((not (eql (len goal) 3))
       (cons *terms-invalid-proof-arity* context))
      ((not (and (proof-is-call child *proof-plus*) (proof-is-call parent *proof-plus*)))
       (cons nil context))
      (t
       (termination-proofs-check-in context
           ((child-sum (termination-proofs-count-or-length-sum child))
            (parent-sum (and child-sum (termination-proofs-count-or-length-sum parent))))
         (if (not parent-sum)
             (cons nil context)
           (termination-proofs-sum-bounds
            (1- n) child parent (butlast clause 1) '(1 2) child nil context)))))))

 (defun termination-proofs-sum-bounds
     (n child parent side-literals indices current bounds context)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (termination-proofs-fuel "termination-proofs-sum-bounds" context))
    ((endp indices) (termination-proofs-sum-finish child parent (reverse bounds) context))
    (t
     (let ((index (car indices)))
       (if (or (<= (len child) index) (<= (len parent) index))
           (cons '(:failure "failure" "") context)
         (let ((after (nth index child))
               (before (nth index parent)))
           (if (equal after before)
               (termination-proofs-sum-bounds
                (1- n) child parent side-literals (cdr indices) current bounds context)
             (let ((clause (append side-literals (list (list *proof-ordinal-less* after before)))))
               (termination-proofs-bind context
                   (ordinal (termination-proofs-prove-decrease-in (1- n) clause context))
                 (if (not (car ordinal))
                     (cons nil context)
                   (termination-proofs-bind context
                       (less (termination-proofs-ordinal-to-less (car ordinal) after before context))
                     (let ((lib (termination-proofs-context-lib context))
                           (other (- 3 index)))
                       (termination-proofs-check-in context
                           ((offset (if (< other (len current))
                                        (nth other current)
                                      '(:failure "failure" "")))
                            (bound (descent-shift lib less offset (eql index 2))))
                         (termination-proofs-sum-bounds
                          (1- n) child parent side-literals (cdr indices)
                          (update-nth index before current) (cons bound bounds) context)))))))))))))))

(defun termination-proofs-prove-decrease (lib clause rulers extra-descent)
  (termination-proofs-public-result
   (termination-proofs-prove-decrease-in
    1000000 clause (termination-proofs-context lib rulers extra-descent nil))))

(defun termination-proofs-minimum-decrease (lib clause rulers extra-descent)
  (termination-proofs-public-result
   (termination-proofs-minimum-decrease-in
    1000000 clause (termination-proofs-context lib rulers extra-descent nil))))

(defun termination-proofs-sum-decrease (lib clause rulers extra-descent)
  (termination-proofs-public-result
   (termination-proofs-sum-decrease-in
    1000000 clause (termination-proofs-context lib rulers extra-descent nil))))

(defun termination-proofs-measures (definitions stored-measures measures)
  (if (endp definitions)
      measures
    (let* ((definition (car definitions))
           (name (car definition))
           (stored (assoc-equal name stored-measures)))
      (cond
       ((not (eql (len definition) 3))
        *terms-invalid-proof-arity*)
       ((not stored)
        *terms-unproved*)
       ((< (len (cdr stored)) 2)
        *terms-invalid-proof-arity*)
       ((not (equal (caddr stored) *proof-ordinal-less*))
        *terms-unproved*)
       (t
        (termination-proofs-measures
         (cdr definitions) stored-measures (table-put measures name (cadr stored))))))))

(defun termination-proofs-measure-ordinal (measure context)
  (let ((lib (termination-proofs-context-lib context)))
    (termination-proofs-check-in context
        ((builtin (descent-direct-builtin lib (list (list *proof-ordinalp* measure)) nil)))
      (cond
       ((car builtin) (cons (car builtin) context))
       ((not (consp measure)) (cons '(:failure "failure" "") context))
       ((equal (car measure) *library-gap*)
        (cons (library-library-cite lib "GAP-ORDINAL" (cdr measure) nil) context))
       (t
        (termination-proofs-bind context
            (natural (if (proof-uses-slice-rules-p (library-library-proof lib))
                         (termination-proofs-library-answer
                          (termination-proofs-natural-result 1000000 lib measure) context)
                       (cons (library-library-natural lib measure) context)))
          (cons (library-library-cite (termination-proofs-context-lib context)
                                      "NATURAL-ORDINAL" (list measure) (list natural))
                context)))))))

(defun termination-proofs-extra-ordinality (measure context)
  (let ((extra (termination-proofs-context-ordinality context))
        (missing *terms-missing-measure-ordinality*))
    (cond
     ((not extra) (cons missing context))
     ((endp (cdr extra))
      (cons (list :call :ordinality (termination-proofs-context-lib context) measure)
            context))
     (t
      (let ((reply (cadr extra)))
        (cons (or (car reply) missing)
              (termination-proofs-context
               (cdr reply) (termination-proofs-context-rulers context)
               (termination-proofs-context-descent context) (cons t (cddr extra)))))))))

(defun termination-proofs-ordinality-case (clause context)
  (if (not (consp (cdar clause)))
      (cons '(:failure "failure" "") context)
    (let* ((measure (cadar clause))
           (lib (termination-proofs-context-lib context))
           (nfix (termination-proofs-library-answer (countdowns-nfix-ordinal lib measure)
                                                    context))
           (attempt (if (car nfix)
                        nfix
                      (termination-proofs-measure-ordinal measure (cdr nfix)))))
      (if (terms-proof-fallback-p (car attempt))
          (termination-proofs-extra-ordinality measure (cdr attempt))
        attempt))))

(defun termination-proofs-find-cached (entries clause)
  (cond
   ((endp entries) nil)
   ((subsetp-equal (remove-equal *proof-false* (proof-step-clause (caar entries)))
                   clause)
    (car entries))
   (t (termination-proofs-find-cached (cdr entries) clause))))

(defun termination-proofs-decrease-case (clause call cached context)
  (if cached
      (cons cached context)
    (termination-proofs-check-in context
        ((rulers (rulers-rulers-init (termination-proofs-context-lib context)
                                   (termination-call-tests call) nil)))
      (let ((context (termination-proofs-with-rulers context rulers)))
        (termination-proofs-bind context
            (result (termination-proofs-prove-decrease-in 1000000 clause context))
          (if (car result)
              (cons result context)
            (cons *terms-unproved*
                  context)))))))

(defun termination-proofs-prove-cases (cases proofs seen methods comparisons context)
  (if (endp cases)
      (cons (list (reverse proofs) methods) context)
    (let* ((obligation (car cases))
           (clause (car obligation))
           (call (cadr obligation)))
      (cond
       ((member-equal clause seen)
        (termination-proofs-prove-cases (cdr cases) proofs seen methods comparisons context))
       (call
        (let* ((goal (car (last clause)))
               (entries (cdr (assoc-equal goal comparisons)))
               (cached (termination-proofs-find-cached entries clause)))
          (termination-proofs-bind context
              (result (termination-proofs-decrease-case clause call cached context))
            (termination-proofs-prove-cases
             (cdr cases) (cons (list clause (car result)) proofs) (cons clause seen)
             (add-to-set-equal (cadr result) methods)
             (if cached
                 comparisons
               (table-put comparisons goal (append entries (list result))))
             context))))
       (t
        (termination-proofs-bind context
            (step (termination-proofs-ordinality-case clause context))
          (termination-proofs-prove-cases
           (cdr cases) (cons (list clause step) proofs) (cons clause seen)
           methods comparisons context)))))))

(defun termination-proofs-measure-fields (definitions measures)
  (if (endp definitions)
      nil
    (cons (cdr (assoc-equal (caar definitions) measures))
          (termination-proofs-measure-fields (cdr definitions) measures))))

(defun termination-proofs-build-entry (definitions name measures cases context)
  (termination-proofs-bind context
      (result (termination-proofs-prove-cases cases nil nil nil nil context))
    (let ((fields (cons name (termination-proofs-measure-fields definitions measures))))
      (termination-proofs-bind context
          (finished (termination-proofs-library-answer
                     (lemmas-slice-library-share-proofs (termination-proofs-context-lib context)
                                                      (car result) (table-keys measures))
                     context))
        (termination-proofs-check-in context
            ((entry (proof-proof-entry "measure" name fields finished)))
          (cons (list entry (text-join ", " (seq-sorted (cadr result))) measures)
                context))))))

(defun termination-proofs-termination-proofs (lib data stored-measures extra-descent extra-ordinality)
  (let* ((extenders (car data))
         (definitions (cdr data))
         (context (termination-proofs-context lib nil extra-descent extra-ordinality)))
    (termination-proofs-public-result
     (cond
      ((endp data) (cons *terms-invalid-proof-arity* context))
      ((or (endp definitions) (endp (car definitions)))
       (cons '(:failure "failure" "") context))
      (t
       (termination-proofs-check-in context
           ((measures (termination-proofs-measures definitions stored-measures nil))
            (calls (termination-recursive-calls extenders definitions))
            (cases (termination-obligation-cases definitions measures calls)))
         (termination-proofs-build-entry definitions (caar definitions)
                                        measures cases context)))))))
