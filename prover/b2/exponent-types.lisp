(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-exponent-types-positive* (proof-sym "EXPT-TYPE-PRESCRIPTION-POSITIVE" "ACL2"))
(defconst *b2-exponent-types-nonzero* (proof-sym "EXPT-TYPE-PRESCRIPTION-NONZERO" "ACL2"))
(defconst *b2-exponent-types-integer* (proof-sym "EXPT-TYPE-PRESCRIPTION-INTEGERP" "ACL2"))
(defconst *b2-exponent-types-unit* (proof-sym "EXPT-1" "ACL2"))
(defconst *b2-exponent-types-exponent-types*
  (list *b2-exponent-types-positive* *b2-exponent-types-nonzero*
        *b2-exponent-types-integer* *b2-exponent-types-unit*))

(defun b2-exponent-types-step-term (step position)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first position)))

(defun b2-exponent-types-require (key facts)
  (let ((entry (assoc-equal key facts)))
    (if entry (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-exponent-types-excluded-zero (lib premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first premise))
         (parts (proof-list-of-length first 3))
         (factor (proof-list-of-length (cadr parts) 3))
         (value (cadr factor))
         (inverse (caddr factor))
         (test (proof-eq *proof-zero* inverse))
         (assumption (proof-proof-assume proof test t))
         (symmetric (proof-proof-symmetric proof assumption))
         (reduced (proof-proof-rewrite proof premise symmetric '(1 1 2)))
         (zero (b2-products-zero-product lib value))
         (lib (cdr zero))
         (proof (library-library-proof lib))
         (reduced (proof-proof-rewrite proof reduced (car zero) '(1 1)))
         (false-step (proof-proof-compute proof (proof-eq *proof-zero* *proof-one*) *proof-nil*))
         (rewritten (proof-proof-rewrite proof reduced false-step '(1)))
         (tidy (proof-proof-tidy proof rewritten))
         (step (proof-proof-front proof tidy (proof-neg test))))
      (cons step lib))))

(defun b2-exponent-types-base-information (lib base premise)
  (let ((test (list *library-numberp* base)))
    (proof-with-checked-results
        ((facts (if premise (b2-tactics-tactics-evidence lib (list premise)) nil))
         (rational (table-get facts (list *library-rationalp* base) nil))
         (numerical (if rational (b2-scaling-number-of-rational lib base rational)
                      (table-get facts test nil)))
         (test (proof-neg (proof-eq base *proof-zero*)))
         (nonzero (if rational
                      (proof-with-checked-results ((positive (b2-exponent-types-require (library-positive base) facts)))
                        (b2-tactics-tactics-from-impossible lib test positive nil nil nil 1500 nil))
                    (table-get facts test nil))))
      (list facts rational numerical nonzero))))

(defun b2-exponent-types-signed-evidence (proof signed)
  (if (endp signed) nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car signed) 2))
         (assumption (proof-proof-assume proof (car pair) (cadr pair)))
         (rest (b2-exponent-types-signed-evidence proof (cdr signed))))
      (cons assumption rest))))

(defun b2-exponent-types-subsume-conflict (lib target conflict)
  (proof-proof-subsume (library-library-proof lib) conflict
                       (cons target (proof-step-clause conflict))))

(defun b2-exponent-types-zero-leaf (lib target name base numerical nonzero facts)
  (if (equal name *b2-exponent-types-integer*)
      (b2-tactics-tactics-solve lib target nil nil nil 0 nil)
    (let ((proof (library-library-proof lib))
          (fixed-base (list *b2-products-fix* base)))
      (proof-with-checked-results
          ((fixed (b2-tactics-tactics-normalize lib fixed-base (list numerical)
                                                 (list *b2-products-fix*) nil 1500 nil))
           (test (proof-eq fixed-base *proof-zero*))
           (fact (b2-exponent-types-require test facts))
           (rewrite (proof-proof-rewrite proof fact fixed '(1 1)))
           (vanishes (proof-proof-tidy proof rewrite))
           (conflict (proof-proof-cut proof vanishes nonzero)))
        (b2-exponent-types-subsume-conflict lib target conflict)))))

(defun b2-exponent-types-positive-bound (lib index typed positive-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((builtin (library-library-builtin lib 14 index))
         (typed-bound (proof-proof-discharge proof builtin typed)))
      (proof-proof-discharge proof typed-bound positive-step))))

(defun b2-exponent-types-negative-step (lib index typed nonzip facts)
  (let ((proof (library-library-proof lib))
        (test (library-lt index *proof-zero*)))
    (proof-with-checked-results
        ((distinct (b2-tactics-tactics-from-impossible
                    lib (proof-neg (proof-eq index *proof-zero*)) nonzip nil
                    (list *b2-powers-zip*) nil 1500 nil))
         (nonnegative (proof-proof-assume proof test nil))
         (nonpositive (b2-exponent-types-require (proof-neg (library-positive index)) facts))
         (zero (b2-powers-zero-from-signs lib index typed nonnegative nonpositive))
         (cut (proof-proof-cut proof zero distinct)))
      (proof-proof-front proof cut test))))

(defun b2-exponent-types-decrease (lib index name typed nonzip facts base-facts forward)
  (if forward
      (proof-with-checked-results
          ((bound (b2-exponent-types-positive-bound lib index typed
                                                     (table-get facts (library-positive index) nil))))
        (list bound *proof-neg-one* lib))
    (proof-with-checked-results
        ((negative (b2-exponent-types-negative-step lib index typed nonzip facts)))
      (if (equal name *b2-exponent-types-integer*)
          (proof-with-checked-results
              ((nonnegative (b2-exponent-types-require (proof-neg (library-lt index *proof-zero*)) base-facts))
               (conflict (proof-proof-cut (library-library-proof lib) negative nonnegative)))
            (list :impossible conflict lib))
        (proof-with-checked-results ((bound (b2-powers-below-zero-count lib index typed negative)))
          (list (car bound) *proof-one* (cdr bound)))))))

(defun b2-exponent-types-child-nonnegative (lib index next-index typed facts)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((law (proof-proof-fact proof "integer-discrete" (list (list *library-x* index))))
         (goal (b2-exponent-types-step-term law 1))
         (positive-step (b2-exponent-types-require (library-positive index) facts))
         (solved (b2-tactics-tactics-solve lib goal (list typed positive-step) nil nil 0 nil))
         (discrete (proof-proof-modus-ponens proof law solved)))
      (b2-bounds-prove-integer-bound lib (library-le *proof-zero* next-index) (list typed discrete)))))

(defun b2-exponent-types-child-proof (lib induction inherited)
  (proof-with-checked-results
      ((hypothesis (b2-exponent-types-step-term induction 1))
       (premise (b2-tactics-tactics-solve lib hypothesis inherited nil nil 0 nil)))
    (proof-proof-modus-ponens (library-library-proof lib) induction premise)))

(defun b2-exponent-types-inverse-positive (lib base inverse rational inverse-type base-positive unit)
  (proof-with-checked-results
      ((zero (library-library-rational lib *proof-zero* nil))
       (law (b2-scaling-rational-scale-order lib *proof-zero* inverse base
                                            (list zero inverse-type rational) base-positive))
       (zero-product (b2-products-zero-product (cdr law) base))
       (lib (cdr zero-product))
       (proof (library-library-proof lib))
       (law (proof-proof-rewrite proof (car law) (car zero-product) '(1 1 1)))
       (law (proof-proof-rewrite proof law unit '(1 1 2)))
       (one (b2-tactics-tactics-solve lib (library-positive *proof-one*) nil nil nil 0 nil))
       (rewritten (proof-proof-rewrite proof one law '(1)))
       (step (proof-proof-tidy proof rewritten)))
    (cons step lib)))

(defun b2-exponent-types-positive-product (lib target value factor child base inverse
                                                child-proof rational base-facts unit forward)
  (proof-with-checked-results
      ((parts (proof-proof-conjunct (library-library-proof lib) child-proof))
       (child-type (car parts))
       (child-positive (cadr parts))
       (factor-type (if forward rational
                      (b2-scaling-rational-op lib "unary-/" inverse (list rational))))
       (base-positive (b2-exponent-types-require (library-positive base) base-facts))
       (factor-positive (if forward (cons base-positive lib)
                          (b2-exponent-types-inverse-positive lib base inverse rational factor-type
                                                              base-positive unit)))
       (lib (cdr factor-positive))
       (value-type (b2-scaling-rational-op lib "binary-*" value (list factor-type child-type)))
       (positive (library-library-cite lib "POSITIVE-PRODUCT" (list factor child)
                                        (list factor-type child-type (car factor-positive) child-positive)))
       (step (b2-tactics-tactics-solve lib target (list value-type positive) nil nil 0 nil)))
    (cons step lib)))

(defun b2-exponent-types-base-nonzero (lib base nonzero)
  (let ((proof (library-library-proof lib))
        (test (proof-eq *proof-zero* base)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test t))
         (symmetric (proof-proof-symmetric proof assumed))
         (cut (proof-proof-cut proof symmetric nonzero))
         (step (proof-proof-front proof cut (proof-neg test))))
      (cons step lib))))

(defun b2-exponent-types-fix-factor (lib term type-step)
  (b2-tactics-tactics-normalize lib (list *b2-products-fix* term) (list type-step)
                                (list *b2-products-fix*) nil 1500 nil))

(defun b2-exponent-types-nonzero-product (lib target factor child base inverse next-index
                                               child-proof numerical nonzero unit forward)
  (proof-with-checked-results
      ((factor-type (if forward numerical (b2-products-numeric-closure lib inverse)))
       (factor-nonzero (if forward (b2-exponent-types-base-nonzero lib base nonzero)
                         (b2-exponent-types-excluded-zero lib unit)))
       (child-type (b2-powers-exp-number (cdr factor-nonzero) base next-index))
       (partial (b2-algebra-product-zero-test (cdr child-type) factor child))
       (lib (cdr partial))
       (proof (library-library-proof lib))
       (fixed-factor (b2-exponent-types-fix-factor lib factor factor-type))
       (fixed-child (b2-exponent-types-fix-factor lib child (car child-type)))
       (rewritten (proof-proof-rewrite proof (car partial) fixed-factor '(1 2 1 2)))
       (rule (proof-proof-rewrite proof rewritten fixed-child '(1 2 3 2)))
       (step (b2-tactics-tactics-solve lib target (list (car factor-nonzero) child-proof) nil (list rule) 0 nil)))
    (cons step lib)))

(defun b2-exponent-types-product-result (lib data base-info target value factor child
                                             next-index child-proof forward)
  (let ((name (car data))
        (base (cadr data))
        (facts (car base-info))
        (rational (cadr base-info))
        (numerical (caddr base-info))
        (nonzero (cadddr base-info)))
    (let ((inverse (list *b2-products-recip* base)))
      (proof-with-checked-results
          ((unit (b2-products-reciprocal-identity lib base numerical nonzero)))
        (if (equal name *b2-exponent-types-positive*)
            (b2-exponent-types-positive-product lib target value factor child base inverse
                                                child-proof rational facts unit forward)
          (b2-exponent-types-nonzero-product lib target factor child base inverse next-index
                                             child-proof numerical nonzero unit forward))))))

(defun b2-exponent-types-inductive-result (lib data base-info facts value factor child target
                                               induction next-index typed forward)
  (let* ((name (car data))
         (base (cadr data))
         (index (caddr data))
         (base-facts (car base-info))
         (inherited (table-values base-facts)))
    (cond
     ((equal name *b2-exponent-types-unit*)
      (proof-with-checked-results
          ((step (b2-tactics-tactics-solve lib target nil nil (list induction) 0 nil)))
        (cons step lib)))
     ((equal name *b2-exponent-types-integer*)
      (proof-with-checked-results
          ((bound (b2-exponent-types-child-nonnegative lib index next-index typed facts))
           (child-proof (b2-exponent-types-child-proof lib induction (append inherited (list bound))))
           (base-type (b2-exponent-types-require (library-integer base) base-facts))
           (step (library-library-type-of lib value (list base-type child-proof))))
        (cons step lib)))
     (t
      (proof-with-checked-results ((child-proof (b2-exponent-types-child-proof lib induction inherited)))
        (b2-exponent-types-product-result lib data base-info target value factor child
                                            next-index child-proof forward))))))

(defun b2-exponent-types-with-induction (data base-info facts value factor child target
                                             decrease next-index typed forward bindings)
  (let* ((index (caddr data))
         (property-formula (car (cddddr data)))
         (measure (cadr (cddddr data)))
         (lib (caddr decrease))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((swapped (library-library-axiom lib "COMMUTATIVITY-OF-+" (list (cadr decrease) index)))
         (bound (proof-proof-rewrite proof (car decrease) swapped '(1 1 1)))
         (smaller (proof-proof-tidy proof bound))
         (binding (list (list index next-index)))
         (bindings (if (member-equal binding bindings) bindings (append bindings (list binding))))
         (induction (b2-tactics-tactics-induction-hypothesis lib property-formula measure binding smaller))
         (result (b2-exponent-types-inductive-result lib data base-info facts value factor child target
                                                     induction next-index typed forward)))
      (list (car result) (cdr result) bindings))))

(defun b2-exponent-types-recursive-leaf (lib value target data base-info facts bindings)
  (let ((name (car data))
        (index (caddr data)))
    (proof-with-checked-results
        ((parts (proof-list-of-length (cdr value) 2))
         (factor (car parts))
         (child (cadr parts))
         (next-index (proof-term-at child 2))
         (nonzip (b2-exponent-types-require (proof-neg (list *b2-powers-zip* index)) facts))
         (typed (b2-tactics-tactics-from-impossible lib (library-integer index) nonzip nil
                                                    (list *b2-powers-zip*) nil 1500 nil))
         (forward (if (assoc-equal (library-positive index) facts) t nil))
         (decrease (b2-exponent-types-decrease lib index name typed nonzip facts (car base-info) forward)))
      (if (eq (car decrease) :impossible)
          (proof-with-checked-results ((step (b2-exponent-types-subsume-conflict lib target (cadr decrease))))
            (list step lib bindings))
        (b2-exponent-types-with-induction data base-info facts value factor child target
                                           decrease next-index typed forward bindings)))))

(defun b2-exponent-types-exponent-type-establish-leaf (value signed lib data base-info bindings)
  (let ((name (car data))
        (base (cadr data))
        (template (cadddr data)))
    (proof-with-checked-results
        ((target (proof-subst template (list (cons *proof-result* value))))
         (evidence (b2-exponent-types-signed-evidence (library-library-proof lib) signed))
         (facts (b2-tactics-tactics-evidence lib evidence)))
      (cond
       ((equal value *proof-one*)
        (proof-with-checked-results ((step (b2-tactics-tactics-solve lib target nil nil nil 0 nil)))
          (list step lib bindings)))
       ((equal value *proof-zero*)
        (proof-with-checked-results
            ((step (b2-exponent-types-zero-leaf lib target name base (caddr base-info) (cadddr base-info) facts)))
          (list step lib bindings)))
       (t (b2-exponent-types-recursive-leaf lib value target data base-info facts bindings))))))

(defun b2-exponent-types-case-value (n lib value template tests data base-info bindings)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "b2-exponent-types-case-value"))
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results
        ((branches (proof-list-of-length (cdr value) 3))
         (test (car branches))
         (yes (b2-exponent-types-case-value (1- n) lib (cadr branches) template
                                           (append tests (list (list test t))) data base-info bindings))
         (no (b2-exponent-types-case-value (1- n) (cadr yes) (caddr branches) template
                                          (append tests (list (list test nil))) data base-info (caddr yes)))
         (proof (library-library-proof (cadr no)))
         (step (proof-by-value-join proof value template (car yes) (car no))))
      (list step (cadr no) (caddr no))))
   ((and (proof-compound value) (not (consp value)))
    '(:failure "tactic-rejected" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta (library-library-proof lib) value))
         (opened (b2-exponent-types-step-term equality 2))
         (result (b2-exponent-types-case-value (1- n) lib opened template tests data base-info bindings))
         (proof (library-library-proof (cadr result)))
         (reverse (proof-proof-symmetric proof equality))
         (step (proof-proof-rewrite-result proof (car result) reverse template *proof-result*)))
      (list step (cadr result) (caddr result))))
   (t
    (proof-with-checked-results
        ((leaf (b2-exponent-types-exponent-type-establish-leaf value tests lib data base-info bindings))
         (literal (proof-step-first (car leaf)))
         (target (proof-subst template (list (cons *proof-result* value)))))
      (if (equal literal target) leaf
        '(:failure "tactic-rejected" ""))))))

(defun b2-exponent-types-exponent-type-establish (premise lib data opened)
  (let ((base (cadr data))
        (template (cadddr data)))
    (proof-with-checked-results
        ((base-info (b2-exponent-types-base-information lib base premise))
         (value (if opened (b2-exponent-types-step-term opened 2)
                  '(:failure "failure" "")))
         (result (b2-exponent-types-case-value 1000000 lib value template nil data base-info nil))
         (lib (cadr result))
         (proof (library-library-proof lib))
         (reverse (proof-proof-symmetric proof opened))
         (step (proof-proof-rewrite-result proof (car result) reverse template *proof-result*)))
      (list step lib (caddr result)))))

(defun b2-exponent-types-establish-property (lib antecedent conclusion data opened)
  (if (not antecedent)
      (b2-exponent-types-exponent-type-establish nil lib data opened)
    (proof-with-checked-results
        ((start (b2-tactics-tactics-implication lib antecedent conclusion nil))
         (request (car start))
         (established (b2-exponent-types-exponent-type-establish (cadddr request) (caddr request) data opened))
         (joined (b2-tactics-tactics-implication lib antecedent conclusion
                                                (cons (car established) (cadr established))))
         (step (car joined)))
      (list step (cdr joined) (caddr established)))))

(defun b2-exponent-types-positive-result (lib antecedent goal induction)
  (proof-with-checked-results
      ((start (b2-tactics-tactics-implication lib antecedent goal nil))
       (request (car start))
       (callback-lib (caddr request))
       (proof (library-library-proof callback-lib))
       (consequence (proof-proof-modus-ponens proof induction (cadddr request)))
       (parts (proof-proof-conjunct proof consequence)))
    (b2-tactics-tactics-implication lib antecedent goal (cons (cadr parts) callback-lib))))

(defun b2-exponent-types-power-call (name goal)
  (cond
   ((equal name *b2-exponent-types-positive*) (proof-term-at goal 2))
   ((equal name *b2-exponent-types-nonzero*)
    (proof-with-checked-results ((test (proof-term-at goal 1)))
      (proof-term-at test 2)))
   ((or (equal name *b2-exponent-types-integer*) (equal name *b2-exponent-types-unit*))
    (proof-term-at goal 1))
   (t '(:failure "tactic-rejected" ""))))

(defun b2-exponent-types-template (name)
  (cond
   ((equal name *b2-exponent-types-positive*)
    (b2-powers-and-terms (list (list *library-rationalp* *proof-result*)
                              (library-positive *proof-result*))))
   ((equal name *b2-exponent-types-nonzero*) (proof-neg (proof-eq *proof-zero* *proof-result*)))
   ((equal name *b2-exponent-types-integer*) (library-integer *proof-result*))
   (t (proof-eq *proof-result* *proof-one*))))

(defun b2-exponent-types-exponent-type (lib name formula)
  (proof-with-checked-results
      ((parts (if (equal name *b2-exponent-types-unit*) (list nil formula)
                (proof-list-of-length (cdr formula) 2)))
       (antecedent (car parts))
       (goal (cadr parts))
       (call (b2-exponent-types-power-call name goal))
       (power (proof-list-of-length call 3))
       (base (cadr power))
       (index (caddr power))
       (measure (list *library-count* index))
       (template (b2-exponent-types-template name))
       (conclusion (proof-subst template (list (cons *proof-result* call))))
       (property-formula (if antecedent (list *library-implies* antecedent conclusion) conclusion))
       (unfold (if (equal name *b2-exponent-types-unit*) (list call *b2-products-fix*) (list call)))
       (opened (b2-tactics-tactics-normalize lib call nil unfold nil 1500 t))
       (data (list name base index template property-formula measure))
       (joined (b2-exponent-types-establish-property lib antecedent conclusion data opened))
       (lib (cadr joined))
       (ordinal (library-library-builtin lib 1 index))
       (proof (proof-proof-induct (library-library-proof lib) ordinal (car joined)
                                  property-formula measure (caddr joined))))
    (if (equal name *b2-exponent-types-positive*)
        (b2-exponent-types-positive-result lib antecedent goal proof)
      (cons proof lib))))
