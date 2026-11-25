(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-ordinals-make* (proof-sym "MAKE-ORD" "ACL2"))
(defconst *t4-ordinals-finite* (proof-sym "O-FINP" "ACL2"))
(defconst *t4-ordinals-exponent* (proof-sym "O-FIRST-EXPT" "ACL2"))
(defconst *t4-ordinals-coefficient* (proof-sym "O-FIRST-COEFF" "ACL2"))
(defconst *t4-ordinals-rest* (proof-sym "O-RST" "ACL2"))
(defconst *t4-ordinals-posp* (proof-sym "POSP" "ACL2"))
(defconst *t4-ordinals-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *t4-ordinals-numeric-eq* (proof-cl "="))
(defconst *t4-ordinals-u* (proof-sym "U" "ACL2"))
(defconst *t4-ordinals-v* (proof-sym "V" "ACL2"))
(defconst *t4-ordinals-w* (proof-sym "W" "ACL2"))

(defun t4-ordinals-phase-measure (size phase)
  (list *t4-ordinals-make* *proof-one* (library-plus *proof-one* size) phase))

(defun t4-ordinals-step-right (step)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first 2)))

(defun t4-ordinals-has-lemma (lib name)
  (assoc-equal (library-lemma-name name) (proof-proof-facts (library-library-proof lib))))

(defun t4-ordinals-ordinals-imply (lib antecedent consequent)
  (t4-order-imply lib antecedent consequent))

(defun t4-ordinals-constant-quote (proof head term arg)
  (proof-with-checked-results ((datum (proof-term-at arg 1)))
    (proof-with-checked-results
        ((value
          (cond
           ((equal head (proof-cl "SYMBOLP"))
            (if (null datum)
                (proof-term-at datum 0)
              (if (and (consp datum) (equal (car datum) "sym"))
                  *proof-t*
                *proof-nil*)))
           ((not (proof-compound datum)) *proof-nil*)
           ((equal head *library-car*) (proof-term-at datum 0))
           (t
            (let ((tail (cdr datum)))
              (if (and (consp tail) (endp (cdr tail)))
                  (if (null (car tail))
                      (proof-term-at (car tail) 0)
                    (if (and (consp (car tail)) (equal (caar tail) "dot"))
                        (proof-term-at (car tail) 1)
                      tail))
                (or tail *proof-nil*)))))))
      (proof-proof-compute proof term value))))

(defun t4-ordinals-constant-cons (lib head arg)
  (cond
   ((equal head *library-car*) (library-library-axiom lib "CAR-CONS" (cdr arg)))
   ((equal head *library-cdr*) (library-library-axiom lib "CDR-CONS" (cdr arg)))
   (t
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((boolean (proof-proof-fact proof "booleanp-consp" (list (list *library-x* arg))))
           (truth (proof-proof-fact proof "consp-cons"
                   (seq-zip (list *library-x* *library-y*) (cdr arg)))))
        (list :true-boolean boolean truth))))))

(defund t4-ordinals-constant-action (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (cond
       ((member-equal head (list *library-car* *library-cdr* (proof-cl "SYMBOLP") *proof-consp*))
        (proof-with-checked-results ((arg (proof-term-at term 1)))
          (cond
           ((and (not (equal head *proof-consp*)) (proof-is-call arg *proof-quote*))
            (t4-ordinals-constant-quote proof head term arg))
           ((and (not (equal head (proof-cl "SYMBOLP"))) (proof-is-call arg *proof-cons*))
            (t4-ordinals-constant-cons lib head arg))
           (t (proof-proof-constant-base proof term)))))
       (t (proof-proof-constant-base proof term))))))

(defund t4-ordinals-nonnil-selection (lib reduced)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (and (proof-is-call reduced *proof-if*) (proof-term-at reduced 1))))
      (if (and (proof-is-call test *proof-quote*) (not (equal test *proof-false*)))
          (proof-with-checked-results
              ((disjunction (proof-proof-nil-or-true proof test))
               (computed (proof-proof-compute proof (proof-eq test *proof-false*) *proof-nil*))
               (rewritten (proof-proof-rewrite proof disjunction computed '(1)))
               (nonnil (proof-proof-tidy proof rewritten))
               (opened (proof-proof-select proof reduced nonnil))
               (branch (proof-term-at reduced 2)))
            (list opened branch))
        nil))))

(defun t4-ordinals-true-boolean-value (lib boolean truth)
  (proof-with-checked-results
      ((first (proof-step-first boolean))
       (value (proof-term-at first 1))
       (step (library-library-cite lib "TRUE-BOOLEAN-VALUE" (list value) (list boolean truth))))
    (cons step lib)))

(defund t4-ordinals-true-boolean-assumptions (lib)
  (let* ((proof (library-library-proof lib))
         (is-boolean (list *t4-ordinals-booleanp* *library-x*))
         (is-true (proof-eq *library-x* *proof-true*)))
    (proof-with-checked-results
        ((type (proof-proof-assume proof is-boolean t))
         (not-true (proof-proof-assume proof is-true nil)))
      (list type not-true))))

(defund t4-ordinals-true-boolean-lemma (lib reduced)
  (let* ((proof (library-library-proof lib))
         (is-boolean (list *t4-ordinals-booleanp* *library-x*))
         (is-true (proof-eq *library-x* *proof-true*)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof *library-x* t))
         (literal (proof-step-first reduced))
         (equality (proof-proof-assume proof literal t))
         (step (proof-proof-rewrite proof assumed equality '(1)))
         (contradiction (proof-proof-tidy proof step))
         (contradiction (proof-proof-front proof contradiction (proof-neg literal)))
         (result (proof-proof-cut proof reduced contradiction))
         (result (proof-proof-front proof result is-true)))
      (library-library-lemma lib "TRUE-BOOLEAN-VALUE" is-true result
       (list (proof-neg is-boolean) (proof-neg *library-x*))))))

(defund t4-ordinals-rewrite-first-simplified (lib step equality)
  (if (not equality)
      step
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results ((step (proof-proof-rewrite proof step equality '(1))))
        (proof-proof-tidy proof step)))))

(defund t4-ordinals-chain-result (lib equality next)
  (proof-with-checked-results
      ((step (proof-proof-chain (library-library-proof lib) equality (list next))))
    (cons step lib)))

(mutual-recursion
 (defund t4-ordinals-simplify-visit (n lib term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-ordinals-simplify-visit")
     (proof-with-checked-results
         ((base (t4-ordinals-simplify-base (1- n) lib term evidence definitions))
          (lib (cdr base))
          (equality (car base))
          (reduced (if equality (t4-ordinals-step-right equality) term))
          (selected (t4-ordinals-nonnil-selection lib reduced)))
       (if (not selected)
           base
         (proof-with-checked-results
             ((next (t4-ordinals-simplify-visit (1- n) lib (cadr selected) evidence definitions))
              (opened (t4-ordinals-chain-result (cdr next) (car selected) (car next))))
           (if equality
               (t4-ordinals-chain-result (cdr opened) equality (car opened))
             opened))))))
 (defund t4-ordinals-simplify-base (n lib term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-ordinals-simplify-base"))
      ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
       (cons nil lib))
      ((atom term) (proof-term-at term 0))
      ((or (proof-compound (car term)) (member-equal (car term) definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (next (t4-ordinals-simplify-visit (1- n) lib (cadr expansion) evidence definitions)))
         (t4-ordinals-chain-result (cdr next) (car expansion) (car next))))
      ((proof-is-call term *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (t4-ordinals-simplify-visit (1- n) lib test evidence definitions))
            (lib (cdr first))
            (path (proof-simplify-if-path (library-library-proof lib) term (car first) evidence)))
         (if (eq (car path) :simplify)
             (proof-with-checked-results
                 ((next (t4-ordinals-simplify-visit (1- n) lib (caddr path) evidence definitions)))
               (t4-ordinals-chain-result (cdr next) (cadr path) (car next)))
           (cons path lib))))
      (t
       (proof-with-checked-results
           ((args (t4-ordinals-simplify-arguments (1- n) lib term (cdr term) 1 nil
                   evidence definitions))
            (equality (car args))
            (lib (cdr args))
            (current (if equality (t4-ordinals-step-right equality) term))
            (constant (t4-ordinals-constant-visit (1- n) lib current)))
         (cond ((not (car constant)) args)
               (equality (t4-ordinals-chain-result (cdr constant) equality (car constant)))
               (t constant)))))))
 (defund t4-ordinals-simplify-arguments (n lib term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-ordinals-simplify-arguments"))
    ((endp args) (cons result lib))
    (t
     (proof-with-checked-results
         ((argument (t4-ordinals-simplify-visit (1- n) lib (car args) evidence definitions))
          (lib (cdr argument))
          (next (proof-simplify-argument-result (library-library-proof lib) term index
                 result (car argument))))
       (t4-ordinals-simplify-arguments (1- n) lib term (cdr args) (1+ index)
        next evidence definitions)))))
 (defund t4-ordinals-constant-visit (n lib term)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-ordinals-constant-visit")
     (proof-with-checked-results ((action (t4-ordinals-constant-action lib term)))
       (if (eq (car action) :true-boolean)
           (t4-ordinals-true-boolean-visit (1- n) lib (cadr action) (caddr action))
         (cons action lib)))))
 (defund t4-ordinals-true-boolean-visit (n lib boolean truth)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-ordinals-true-boolean-visit"))
    ((t4-ordinals-has-lemma lib "TRUE-BOOLEAN-VALUE")
     (t4-ordinals-true-boolean-value lib boolean truth))
    (t
     (proof-with-checked-results
         ((assumptions (t4-ordinals-true-boolean-assumptions lib))
          (step (car assumptions))
          (formula (proof-step-first step))
          (simplified (t4-ordinals-simplify-visit (1- n) lib formula (cdr assumptions)
                       (list *t4-ordinals-booleanp* (proof-cl "EQ"))))
          (lib (cdr simplified))
          (reduced (t4-ordinals-rewrite-first-simplified lib step (car simplified)))
          (lib (t4-ordinals-true-boolean-lemma lib reduced)))
       (t4-ordinals-true-boolean-value lib boolean truth))))))

(defun t4-ordinals-ordinals-simplify (lib term evidence definitions)
  (t4-ordinals-simplify-visit 1000000 lib term evidence definitions))

(defun t4-ordinals-ordinals-constant (lib term)
  (t4-ordinals-constant-visit 1000000 lib term))

(defun t4-ordinals-ordinals-true-boolean (lib boolean truth)
  (t4-ordinals-true-boolean-visit 1000000 lib boolean truth))

(defun t4-ordinals-ordinals-simplify-first (lib step evidence definitions)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (simplified (t4-ordinals-ordinals-simplify lib literal evidence definitions))
       (lib (cdr simplified))
       (step (t4-ordinals-rewrite-first-simplified lib step (car simplified))))
    (cons step lib)))

(defund t4-ordinals-prove-premise (lib term evidence)
  (if (equal term *proof-true*)
      (proof-proof-prove (library-library-proof lib) term nil nil)
    (proof-find-evidence evidence (list term))))

(defun t4-ordinals-prove-visit (n lib term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-ordinals-prove-visit")
    (proof-with-checked-results ((premise (t4-ordinals-prove-premise lib term evidence)))
      (if premise
          (cons premise lib)
        (proof-with-checked-results
            ((result (t4-ordinals-ordinals-simplify lib term evidence definitions))
             (lib (cdr result))
             (equality (car result))
             (right (and equality (t4-ordinals-step-right equality))))
          (cond
           ((or (not equality) (equal right term)) (proof-prove-unproved-term term))
           ((equal right *proof-true*)
            (proof-with-checked-results
                ((step (proof-proof-true-from-eq (library-library-proof lib) equality)))
              (cons step lib)))
           (t
            (proof-with-checked-results
                ((next (t4-ordinals-prove-visit (1- n) lib right evidence definitions))
                 (lib (cdr next))
                 (step (proof-proof-transport (library-library-proof lib) (car next) equality)))
              (cons step lib)))))))))

(defun t4-ordinals-ordinals-prove (lib term evidence definitions)
  (t4-ordinals-prove-visit 1000000 lib term evidence definitions))

(mutual-recursion
 (defun t4-ordinals-ordinals-type-of (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *library-nfix*)
     (library-library-cite lib "NFIX-INTEGER" (cdr term) nil))
    ((and (consp term)
          (member-equal (car term) (list *proof-plus* *proof-times* *proof-minus*)))
     (proof-with-checked-results
         ((premise (library-type-evidence (library-integer term) evidence)))
       (if premise
           premise
         (cond
          ((equal (car term) *proof-minus*)
           (if (endp (cdr term))
               (proof-term-at term 1)
             (proof-with-checked-results
                 ((step (t4-ordinals-ordinals-type-of lib (cadr term) evidence)))
               (library-library-cite lib "INTEGER-NEGATION" (cdr term) (list step)))))
          (t
           (proof-with-checked-results
               ((steps (t4-ordinals-type-arguments lib (cdr term) evidence)))
             (library-library-cite lib
              (if (equal (car term) *proof-plus*) "INTEGER-SUM" "INTEGER-PRODUCT")
              (cdr term) steps)))))))
    (t (library-library-type-of lib term evidence))))
 (defun t4-ordinals-type-arguments (lib args evidence)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((step (t4-ordinals-ordinals-type-of lib (car args) evidence))
          (rest (t4-ordinals-type-arguments lib (cdr args) evidence)))
       (cons step rest)))))

(mutual-recursion
 (defun t4-ordinals-ordinals-natural-with-library (lib term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *library-nfix*)
     (proof-with-checked-results ((step (library-library-cite lib "NFIX-NATURAL" (cdr term) nil)))
       (cons step lib)))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results
         ((args (t4-ordinals-natural-arguments lib (cdr term)))
          (lib (cdr args))
          (step (library-library-cite lib "NATURAL-SUM" (cdr term) (car args))))
       (cons step lib)))
    ((or (proof-is-call term *library-count*) (proof-is-call term *library-len*))
     (proof-with-checked-results ((step (library-library-natural lib term)))
       (cons step lib)))
    (t (t4-ordinals-ordinals-prove lib (list *library-natp* term) nil
        (list *library-natp* *proof-not*)))))
 (defun t4-ordinals-natural-arguments (lib args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       (cons nil lib)
     (proof-with-checked-results
         ((first (t4-ordinals-ordinals-natural-with-library lib (car args)))
          (rest (t4-ordinals-natural-arguments (cdr first) (cdr args))))
       (cons (cons (car first) (car rest)) (cdr rest))))))

(defun t4-ordinals-ordinals-natural (lib term)
  (proof-with-checked-results ((result (t4-ordinals-ordinals-natural-with-library lib term)))
    (car result)))

(defund t4-ordinals-minus-expansion (lib argument evidence)
  (cond
   ((and (proof-is-call argument *proof-minus*) (t4-ordinals-has-lemma lib "DOUBLE-NEGATION"))
    (proof-with-checked-results
        ((item (proof-term-at argument 1))
         (typed (t4-ordinals-ordinals-type-of lib item evidence)))
      (library-library-cite lib "DOUBLE-NEGATION" (list item) (list typed))))
   ((and (proof-is-call argument *proof-plus*) (t4-ordinals-has-lemma lib "NEGATE-SUM"))
    (proof-with-checked-results
        ((types (t4-ordinals-type-arguments lib (cdr argument) evidence)))
      (library-library-cite lib "NEGATE-SUM" (cdr argument) types)))
   (t nil)))

(defun t4-ordinals-push-minus (n lib term evidence)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-ordinals-push-minus"))
     ((proof-is-call term *proof-plus*)
      (proof-with-checked-results
          ((step (proof-proof-reflexive proof term))
           (left (proof-term-at term 1))
           (left (t4-ordinals-push-minus (1- n) lib left evidence))
           (step (if left (proof-proof-rewrite proof step left '(1 2 1)) step))
           (right (proof-term-at term 2))
           (right (t4-ordinals-push-minus (1- n) lib right evidence))
           (step (if right (proof-proof-rewrite proof step right '(1 2 2)) step))
           (right (t4-ordinals-step-right step)))
        (and (not (equal right term)) step)))
     ((proof-is-call term *proof-minus*)
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (if (proof-is-call argument *proof-quote*)
            (proof-proof-constant-base proof term)
          (proof-with-checked-results ((step (t4-ordinals-minus-expansion lib argument evidence)))
            (and step
                 (proof-with-checked-results
                     ((right (t4-ordinals-step-right step))
                      (rest (t4-ordinals-push-minus (1- n) lib right evidence)))
                   (proof-proof-chain proof step (list rest))))))))
     (t nil))))

(defun t4-ordinals-linear-remove-zero (lib step name term place evidence)
  (proof-with-checked-results
      ((typed (t4-ordinals-ordinals-type-of lib term evidence))
       (equality (library-library-cite lib name (list term) (list typed)))
       (step (proof-proof-rewrite (library-library-proof lib) step equality place)))
    (list :continue step place)))

(defun t4-ordinals-linear-combine-rewrite (lib step combine a b rest suffix place)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (if suffix
                   (proof-with-checked-results
                       ((tail (proof-term-at rest 2))
                        (assoc-step (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list a b tail)))
                        (symmetric (proof-proof-symmetric proof assoc-step)))
                     (proof-proof-rewrite proof step symmetric place))
                 step))
         (step (proof-proof-rewrite proof step combine
                (if suffix (append place '(1)) place))))
      (list :continue step '(1 2)))))

(defund t4-ordinals-linear-combine-step (lib step place evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first step))
         (node (library-linear-form-get first (cdr place))))
      (if (not (proof-is-call node *proof-plus*))
          (proof-proof-tidy proof step)
        (proof-with-checked-results ((args (proof-list-of-length (cdr node) 2)))
          (let* ((a (car args))
                 (rest (cadr args))
                 (suffix (proof-is-call rest *proof-plus*)))
            (proof-with-checked-results ((b (if suffix (proof-term-at rest 1) rest)))
              (cond
               ((equal a *proof-zero*)
                (t4-ordinals-linear-remove-zero lib step "ADD-ZERO-LEFT" rest place evidence))
               ((and (equal b *proof-zero*) (not suffix))
                (t4-ordinals-linear-remove-zero lib step "ADD-ZERO-RIGHT" a place evidence))
               (t
                (proof-with-checked-results ((combine (library-linear-combine-pair lib a b)))
                  (if combine
                      (t4-ordinals-linear-combine-rewrite lib step combine a b rest suffix place)
                    (list :continue step (append place '(2))))))))))))))

(defun t4-ordinals-linear-combine (n lib step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-ordinals-linear-combine")
    (let ((result (t4-ordinals-linear-combine-step lib step place evidence)))
      (if (eq (car result) :continue)
          (t4-ordinals-linear-combine (1- n) lib (cadr result) (caddr result) evidence)
        result))))

(defun t4-ordinals-linear-form (lib term evidence)
  (proof-with-checked-results
      ((normalized (t4-ordinals-push-minus 1000000 lib term evidence))
       (step (or normalized (proof-proof-reflexive (library-library-proof lib) term)))
       (step (library-linear-reassociate 1000000 lib step '(1 2)))
       (step (library-linear-sort 1000000 lib step '(1 2) nil)))
    (t4-ordinals-linear-combine 1000000 lib step '(1 2) evidence)))

(defun t4-ordinals-linear-equal (lib left right integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((a (t4-ordinals-linear-form lib left integers))
         (b (t4-ordinals-linear-form lib right integers))
         (a-normal (t4-ordinals-step-right a))
         (b-normal (t4-ordinals-step-right b)))
      (if (equal a-normal b-normal)
          (proof-with-checked-results ((back (proof-proof-symmetric proof b)))
            (proof-proof-chain proof a (list back)))
        (proof-with-checked-results
            ((a-text (proof-write a-normal))
             (b-text (proof-write b-normal)))
          '(:failure "search-miss" ""))))))

(defun t4-ordinals-ordinals-distinct (lib strict integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first strict))
         (parts (proof-list-of-length first 3)))
      (let* ((a (cadr parts))
             (b (caddr parts))
             (equality (proof-eq a b))
             (difference (library-diff b b)))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof equality t))
             (reflexive (proof-proof-rewrite proof strict assumed '(1 1)))
             (typed (t4-ordinals-ordinals-type-of lib b integers))
             (delta (t4-ordinals-linear-equal lib difference *proof-zero* (list typed)))
             (axiom (library-library-axiom lib "<-ON-OTHERS" (list b b)))
             (zero (proof-proof-reflexive proof (library-lt difference *proof-zero*)))
             (zero (proof-proof-rewrite proof zero delta '(1 2 1)))
             (false (proof-proof-constant-base proof (library-lt *proof-zero* *proof-zero*)))
             (reduction (proof-proof-chain proof axiom (list zero false)))
             (result (proof-proof-rewrite proof reflexive reduction '(1)))
             (result (proof-proof-tidy proof result)))
          (proof-proof-front proof result (proof-neg equality)))))))

(defun t4-ordinals-ordinals-constructor-view (lib operator term)
  (proof-with-checked-results
      ((opened (proof-proof-unfold (library-library-proof lib) (list operator term)))
       (right (t4-ordinals-step-right opened))
       (reduced (t4-ordinals-ordinals-simplify lib right nil
                 (list *t4-ordinals-finite* *t4-structural-atom* *proof-not* *t4-ordinals-make*))))
    (t4-ordinals-chain-result (cdr reduced) opened (car reduced))))

(defund t4-ordinals-rewrite-selector (lib step operator term)
  (proof-with-checked-results
      ((view (t4-ordinals-ordinals-constructor-view lib operator term))
       (lib (cdr view))
       (step (proof-proof-rewrite-first (library-library-proof lib) step (car view))))
    (cons step lib)))

(defun t4-ordinals-rewrite-selectors (lib step operators term)
  (declare (xargs :measure (acl2-count operators)))
  (if (endp operators)
      (cons step lib)
    (proof-with-checked-results
        ((rewritten (t4-ordinals-rewrite-selector lib step (car operators) term)))
      (t4-ordinals-rewrite-selectors (cdr rewritten) (car rewritten) (cdr operators) term))))

(defund t4-ordinals-rewrite-constructor (lib step term)
  (if (not (proof-is-call term *t4-ordinals-make*))
      '(:failure "inference-mismatch" "")
    (t4-ordinals-rewrite-selectors lib step
     (list *t4-ordinals-finite* *t4-ordinals-exponent* *t4-ordinals-coefficient* *t4-ordinals-rest*)
     term)))

(defun t4-ordinals-view-constructors (lib step constructors)
  (declare (xargs :measure (acl2-count constructors)))
  (if (endp constructors)
      (cons step lib)
    (proof-with-checked-results
        ((rewritten (t4-ordinals-rewrite-constructor lib step (car constructors))))
      (t4-ordinals-view-constructors (cdr rewritten) (car rewritten) (cdr constructors)))))

(defun t4-ordinals-ordinals-view-ordinals (lib goal constructors)
  (proof-with-checked-results
      ((step (proof-proof-unfold (library-library-proof lib) goal)))
    (t4-ordinals-view-constructors lib step constructors)))

(defun t4-ordinals-assumptions (proof terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((first (proof-proof-assume proof (car terms) t))
         (rest (t4-ordinals-assumptions proof (cdr terms))))
      (cons first rest))))

(defun t4-ordinals-ordinal-block-lemma (lib)
  (let* ((x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (box (list *t4-ordinals-make* x y z))
         (assumptions (list (list *library-natp* x) (library-positive x)
                            (library-integer y) (library-positive y) (list *proof-ordinalp* z)
                            (list *proof-ordinal-less* (list *t4-ordinals-exponent* z) x)))
         (goal (list *proof-ordinalp* box)))
    (proof-with-checked-results
        ((steps (t4-ordinals-assumptions (library-library-proof lib) assumptions))
         (type (library-library-cite lib "NATURAL-INTEGER" (list x) (list (car steps))))
         (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list x) (list (car steps))))
         (distinct (t4-ordinals-ordinals-distinct lib (cadr steps) (list type)))
         (requirements (cons ordinal (cons distinct (cddr steps))))
         (opened (t4-ordinals-ordinals-view-ordinals lib goal (list box)))
         (lib (cdr opened))
         (right (t4-ordinals-step-right (car opened)))
         (proved (t4-ordinals-ordinals-prove lib right requirements
                  (list *t4-ordinals-make* *t4-structural-eql* *proof-not* *t4-ordinals-posp*)))
         (lib (cdr proved))
         (step (proof-proof-transport (library-library-proof lib) (car proved) (car opened))))
      (library-library-lemma lib "ORDINAL-BLOCK" goal step (library-guards assumptions)))))

(defun t4-ordinals-ordinals-make-ordinal (lib term exp-nat exp-positive coeff-positive
                                         rest-ordinal exp-order coeff-int)
  (proof-with-checked-results
      ((lib (if (t4-ordinals-has-lemma lib "ORDINAL-BLOCK")
                lib
              (t4-ordinals-ordinal-block-lemma lib)))
       (parts (proof-list-of-length term 4))
       (type (or coeff-int (t4-ordinals-ordinals-type-of lib (caddr parts) nil)))
       (step (library-library-cite lib "ORDINAL-BLOCK" (cdr term)
              (list exp-nat exp-positive type coeff-positive rest-ordinal exp-order))))
    (cons step lib)))

(defun t4-ordinals-order-blocks-requirements (mode)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*)
        (u *t4-ordinals-u*)
        (v *t4-ordinals-v*)
        (w *t4-ordinals-w*))
    (cond
     ((equal mode "EXPONENT") (list (library-integer x) (library-integer u) (library-lt x u)))
     ((equal mode "COEFFICIENT")
      (list (proof-eq x u) (library-integer y) (library-integer v) (library-lt y v)))
     (t (list (proof-eq x u) (proof-eq y v) (list *proof-ordinal-less* z w))))))

(defun t4-ordinals-order-blocks-evidence (lib a b smaller mode exp-equal coeff-equal)
  (if (equal mode "REST")
      (list exp-equal coeff-equal smaller)
    (let ((index (if (equal mode "EXPONENT") 0 1)))
      (proof-with-checked-results
          ((left (proof-term-at a index))
           (typed-left (t4-ordinals-ordinals-type-of lib left nil))
           (right (proof-term-at b index))
           (typed-right (t4-ordinals-ordinals-type-of lib right nil)))
        (let ((evidence (list typed-left typed-right smaller)))
          (if (equal mode "EXPONENT")
              evidence
            (cons exp-equal evidence)))))))

(defun t4-ordinals-order-blocks-tests (lib mode premises)
  (cond
   ((equal mode "EXPONENT")
    (let ((ix (car premises))
          (iu (cadr premises))
          (order (caddr premises)))
      (proof-with-checked-results
          ((finite-order (library-library-cite lib "FINITE-ORDER"
                          (list *library-x* *t4-ordinals-u*) (list ix iu)))
           (distinct (t4-ordinals-ordinals-distinct lib order (list ix iu)))
           (transported (proof-proof-transport (library-library-proof lib) order finite-order)))
        (append premises (list distinct transported)))))
   ((equal mode "COEFFICIENT")
    (proof-with-checked-results
        ((distinct (t4-ordinals-ordinals-distinct lib (cadddr premises)
                    (list (cadr premises) (caddr premises)))))
      (append premises (list distinct))))
   (t premises)))

(defun t4-ordinals-order-blocks-lemma (lib mode required short-name)
  (let* ((box (list *t4-ordinals-make* *library-x* *library-y* *library-z*))
         (next-box (list *t4-ordinals-make* *t4-ordinals-u* *t4-ordinals-v* *t4-ordinals-w*))
         (claim (list *proof-ordinal-less* box next-box)))
    (proof-with-checked-results
        ((premises (t4-ordinals-assumptions (library-library-proof lib) required))
         (tests (t4-ordinals-order-blocks-tests lib mode premises))
         (opened (t4-ordinals-ordinals-view-ordinals lib claim (list box next-box)))
         (lib (cdr opened))
         (right (t4-ordinals-step-right (car opened)))
         (proved (t4-ordinals-ordinals-prove lib right tests
                  (list *proof-not* *t4-ordinals-numeric-eq*)))
         (lib (cdr proved))
         (step (proof-proof-transport (library-library-proof lib) (car proved) (car opened))))
      (library-library-lemma lib short-name claim step (library-guards required)))))

(defun t4-ordinals-ordinals-order-blocks (lib left right smaller exp-equal coeff-equal)
  (let* ((a (cdr left))
         (b (cdr right))
         (mode (cond ((not exp-equal) "EXPONENT")
                     ((not coeff-equal) "COEFFICIENT")
                     (t "REST")))
         (required (t4-ordinals-order-blocks-requirements mode)))
    (proof-with-checked-results
        ((evidence (t4-ordinals-order-blocks-evidence lib a b smaller mode exp-equal coeff-equal)))
      (let* ((variables (list *library-x* *library-y* *library-z*
                              *t4-ordinals-u* *t4-ordinals-v* *t4-ordinals-w*))
             (short-name (concatenate 'string "BLOCK-" mode "-ORDER"))
             (name (library-lemma-name short-name)))
        (proof-with-checked-results
            ((lib (if (t4-ordinals-has-lemma lib short-name)
                      lib
                    (t4-ordinals-order-blocks-lemma lib mode required short-name)))
             (step (proof-proof-use (library-library-proof lib) name
                    (seq-zip variables (append a b)) evidence)))
          (cons step lib))))))

(defun t4-ordinals-ordinals-finite-below-block (lib finite block)
  (proof-with-checked-results
      ((opened (t4-ordinals-ordinals-view-ordinals lib
                (list *proof-ordinal-less* finite block) (list block)))
       (lib (cdr opened))
       (type (t4-ordinals-ordinals-type-of lib finite nil))
       (is-finite (library-library-cite lib "INTEGER-FINITE" (list finite) (list type)))
       (right (t4-ordinals-step-right (car opened)))
       (proved (t4-ordinals-ordinals-prove lib right (list is-finite) (list *proof-not*)))
       (lib (cdr proved))
       (step (proof-proof-transport (library-library-proof lib) (car proved) (car opened))))
    (cons step lib)))

(defun t4-ordinals-comparison (lib a b integers)
  (proof-with-checked-results
      ((a-type (t4-ordinals-ordinals-type-of lib a integers))
       (b-type (t4-ordinals-ordinals-type-of lib b integers)))
    (library-library-cite lib "LESS-DIFFERENCE" (list a b) (list a-type b-type))))

(defun t4-ordinals-ordinal-comparison (lib a b)
  (proof-with-checked-results
      ((a-type (t4-ordinals-ordinals-type-of lib a nil))
       (b-type (t4-ordinals-ordinals-type-of lib b nil)))
    (library-library-cite lib "FINITE-ORDER" (list a b) (list a-type b-type))))

(defun t4-ordinals-number (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
         (axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list term)))
         (typed (t4-ordinals-ordinals-type-of lib term evidence))
         (rational (proof-proof-modus-ponens proof axiom typed)))
      (proof-proof-modus-ponens proof fact rational))))

(defun t4-ordinals-weak-endpoints (weak)
  (proof-with-checked-results
      ((first (proof-step-first weak))
       (parts (proof-list-of-length first 2))
       (order (proof-list-of-length (cadr parts) 3)))
    (list (caddr order) (cadr order))))

(defun t4-ordinals-ordinals--weak-distinct (lib weak distinct ints)
  (proof-with-checked-results ((endpoints (t4-ordinals-weak-endpoints weak)))
    (let* ((a (car endpoints))
           (b (cadr endpoints))
           (proof (library-library-proof lib))
           (delta (library-diff b a))
           (delta-zero (proof-eq delta *proof-zero*))
           (sum (library-plus delta a)))
      (proof-with-checked-results
          ((delta-int (t4-ordinals-ordinals-type-of lib delta ints))
           (identity (proof-proof-reflexive proof sum))
           (assumed (proof-proof-assume proof delta-zero t))
           (exposed (proof-proof-rewrite proof identity assumed '(1 2 1)))
           (linear (t4-ordinals-linear-equal lib sum b ints))
           (linear (proof-proof-symmetric proof linear))
           (a-type (proof-term-at ints 0))
           (zero-left (library-library-cite lib "ADD-ZERO-LEFT" (list a) (list a-type)))
           (same (proof-proof-chain proof linear (list exposed zero-left)))
           (equality (proof-proof-symmetric proof same))
           (unequal (proof-proof-cut proof equality distinct))
           (unequal-delta (proof-proof-front proof unequal (proof-neg delta-zero)))
           (axiom (library-library-axiom lib "<-ON-OTHERS" (list b a)))
           (nonnegative-delta (proof-proof-rewrite proof weak axiom '(1 1)))
           (delta-types (append ints (list delta-int)))
           (negativity (t4-ordinals-comparison lib delta *proof-zero* delta-types))
           (normal (t4-ordinals-linear-equal lib
                    (library-diff *proof-zero* delta) (library-minus delta) delta-types))
           (negativity (proof-proof-rewrite proof negativity normal '(1 2 2)))
           (no-negative (proof-proof-rewrite proof nonnegative-delta negativity '(1 1)))
           (trichotomy (library-library-axiom lib "TRICHOTOMY" (list delta)))
           (conjuncts (proof-proof-conjunct proof trichotomy))
           (number (t4-ordinals-number lib delta (list delta-int)))
           (three (proof-proof-modus-ponens proof (car conjuncts) number))
           (pos (library-positive delta))
           (not-positive (proof-proof-assume proof pos nil))
           (remaining (t4-ordinals-ordinals-simplify-first lib three
                       (list not-positive unequal-delta) nil))
           (lib (cdr remaining))
           (proof (library-library-proof lib))
           (positive-delta (proof-proof-cut proof (car remaining) no-negative))
           (positive-delta (proof-proof-front proof positive-delta pos))
           (comparison (t4-ordinals-comparison lib a b ints))
           (step (proof-proof-transport proof positive-delta comparison)))
        (cons step lib)))))

(defun t4-ordinals-weak-distinct-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (xy (library-lt y x))
         (unequal (proof-eq x y)))
    (proof-with-checked-results
        ((ints (library-library-ints lib (list x y)))
         (weak (proof-proof-assume proof xy nil))
         (distinct (proof-proof-assume proof unequal nil))
         (result (t4-ordinals-ordinals--weak-distinct lib weak distinct ints))
         (x-type (proof-step-first (car ints)))
         (y-type (proof-step-first (cadr ints))))
      (library-library-lemma (cdr result) "WEAK-DISTINCT-LESS" (library-lt x y) (car result)
       (list (proof-neg x-type) (proof-neg y-type) xy unequal)))))

(defun t4-ordinals-ordinals-weak-distinct (lib weak distinct evidence)
  (proof-with-checked-results
      ((endpoints (t4-ordinals-weak-endpoints weak))
       (lib (if (t4-ordinals-has-lemma lib "WEAK-DISTINCT-LESS")
                lib
              (t4-ordinals-weak-distinct-lemma lib)))
       (type-a (t4-ordinals-ordinals-type-of lib (car endpoints) evidence))
       (type-b (t4-ordinals-ordinals-type-of lib (cadr endpoints) evidence))
       (step (library-library-cite lib "WEAK-DISTINCT-LESS" endpoints
              (list type-a type-b weak distinct))))
    (cons step lib)))

(defun t4-ordinals-phase-ordinal-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (generic (t4-ordinals-phase-measure x y))
         (nat-x (list *library-natp* x))
         (nat-y (list *library-natp* y))
         (zero-to-one (library-lt *proof-zero* *proof-one*)))
    (proof-with-checked-results
        ((x-nat (proof-proof-assume proof nat-x t))
         (y-nat (proof-proof-assume proof nat-y t))
         (ix (library-library-cite lib "NATURAL-INTEGER" (list x) (list x-nat)))
         (iy (library-library-cite lib "NATURAL-INTEGER" (list y) (list y-nat)))
         (bound (library-library-cite lib "NATURAL-NONNEGATIVE" (list x) (list x-nat)))
         (pos-coefficient (library-library-cite lib "POSITIVE-ONE-PLUS" (list x) (list ix bound)))
         (finite (library-library-cite lib "INTEGER-FINITE" (list y) (list iy)))
         (opened (proof-proof-unfold proof (list *t4-ordinals-exponent* y)))
         (right (t4-ordinals-step-right opened))
         (selected (proof-proof-select proof right finite))
         (zero-exponent (proof-proof-chain proof opened (list selected)))
         (less (t4-ordinals-ordinals-prove lib zero-to-one nil nil))
         (lib (cdr less))
         (proof (library-library-proof lib))
         (compared (t4-ordinals-ordinal-comparison lib *proof-zero* *proof-one*))
         (exp-less (proof-proof-transport proof (car less) compared))
         (exp-less (library-library-transport-argument lib exp-less zero-exponent 1))
         (natural-phase (library-library-cite lib "NATURAL-ORDINAL" (list y) (list y-nat)))
         (one-natural (t4-ordinals-ordinals-natural-with-library lib *proof-one*))
         (one-positive (t4-ordinals-ordinals-prove (cdr one-natural) zero-to-one nil nil))
         (lib (cdr one-positive))
         (type (t4-ordinals-ordinals-type-of lib (caddr generic) (list ix)))
         (ordinal (t4-ordinals-ordinals-make-ordinal lib generic (car one-natural)
                   (car one-positive) pos-coefficient natural-phase exp-less type)))
      (library-library-lemma (cdr ordinal) "PHASE-ORDINAL" (list *proof-ordinalp* generic)
       (car ordinal) (list (proof-neg nat-x) (proof-neg nat-y))))))

(defun t4-ordinals-ordinals-phase-ordinal (lib term)
  (proof-with-checked-results ((parts (proof-list-of-length term 4)))
    (if (not (equal (cadr parts) *proof-one*))
        '(:failure "inference-mismatch" "")
      (proof-with-checked-results
          ((size (proof-term-at (caddr parts) 2))
           (lib (if (t4-ordinals-has-lemma lib "PHASE-ORDINAL")
                    lib
                  (t4-ordinals-phase-ordinal-lemma lib)))
           (size-natural (t4-ordinals-ordinals-natural-with-library lib size))
           (phase (cadddr parts))
           (phase-natural (t4-ordinals-ordinals-natural-with-library (cdr size-natural) phase))
           (lib (cdr phase-natural))
           (step (library-library-cite lib "PHASE-ORDINAL" (list size phase)
                  (list (car size-natural) (car phase-natural)))))
        (cons step lib)))))

(defund t4-ordinals-phase-measure-reply (request lib)
  (t4-structural-branch-results-resume request
   (t4-ordinals-ordinals-phase-ordinal lib (t4-structural-branch-request-node request))))

(defun t4-ordinals-phase-measure-visit (n result)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-ordinals-phase-measure-visit"))
   ((failure-p result) result)
   ((t4-structural-branch-request-p (car result))
    (t4-ordinals-phase-measure-visit (1- n)
     (t4-ordinals-phase-measure-reply (car result) (cdr result))))
   (t result)))

(defun t4-ordinals-ordinals-phase-measure-ordinal (lib measure)
  (t4-ordinals-phase-measure-visit 1000000
   (t4-structural-branch-results-start lib "ORDINAL-IF" measure
    (list *proof-ordinalp* *proof-result*))))

(defun t4-ordinals-shift-by-one (lib strict)
  (let ((proof (library-library-proof lib))
        (offset *proof-one*))
    (proof-with-checked-results
        ((literal (proof-step-first strict))
         (parts (proof-list-of-length literal 3)))
      (let ((a (cadr parts))
            (b (caddr parts)))
        (proof-with-checked-results
            ((type-a (t4-ordinals-ordinals-type-of lib a nil))
             (type-b (t4-ordinals-ordinals-type-of lib b nil))
             (type-offset (t4-ordinals-ordinals-type-of lib offset nil))
             (shifted (library-library-cite lib "LESS-SHIFT" (list a b offset)
                       (list type-a type-b type-offset strict)))
             (commute-a (library-library-axiom lib "COMMUTATIVITY-OF-+" (list a offset)))
             (shifted (proof-proof-rewrite proof shifted commute-a '(1 1)))
             (commute-b (library-library-axiom lib "COMMUTATIVITY-OF-+" (list b offset)))
             (shifted (proof-proof-rewrite proof shifted commute-b '(1 2))))
          (proof-proof-tidy proof shifted))))))

(defun t4-ordinals-phase-decrease-split (lib left right a b bound phases exp-equal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((size-a (proof-term-at a 2))
                                 (size-b (proof-term-at b 2)))
      (let ((same-size (proof-eq size-a size-b)))
        (proof-with-checked-results
            ((identity (proof-proof-reflexive proof a))
             (assumed (proof-proof-assume proof same-size t))
             (same (proof-proof-rewrite proof identity assumed '(1 2 2)))
             (yes (t4-ordinals-ordinals-order-blocks lib left right phases exp-equal same))
             (lib (cdr yes))
             (different (proof-proof-assume (library-library-proof lib) same-size nil))
             (smaller (t4-ordinals-ordinals-weak-distinct lib bound different nil)))
          (list :compare-phases same-size (car yes) (car smaller) (cdr smaller)))))))

(defund t4-ordinals-phase-decrease-step (lib left right bound)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left-parts (proof-list-of-length left 4))
         (right-parts (proof-list-of-length right 4))
         (exp-equal (proof-proof-reflexive proof *proof-one*))
         (bound-literal (and bound (proof-step-first bound)))
         (bound-head (and bound (proof-term-at bound-literal 0))))
      (if (equal bound-head *proof-less*)
          (proof-with-checked-results ((shifted (t4-ordinals-shift-by-one lib bound)))
            (t4-ordinals-ordinals-order-blocks lib left right shifted exp-equal nil))
        (let ((a (caddr left-parts))
              (b (caddr right-parts))
              (phase-a (cadddr left-parts))
              (phase-b (cadddr right-parts)))
          (proof-with-checked-results
              ((less (t4-ordinals-ordinals-prove lib (library-lt phase-a phase-b) nil nil))
               (lib (cdr less))
               (proof (library-library-proof lib))
               (ordinal (t4-ordinals-ordinal-comparison lib phase-a phase-b))
               (phases (proof-proof-transport proof (car less) ordinal)))
            (if (equal a b)
                (proof-with-checked-results ((same (proof-proof-reflexive proof a)))
                  (t4-ordinals-ordinals-order-blocks lib left right phases exp-equal same))
              (t4-ordinals-phase-decrease-split lib left right a b bound phases exp-equal))))))))

(defun t4-ordinals-phase-decrease-visit (n lib left right bound)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-ordinals-phase-decrease-visit")
    (let ((result (t4-ordinals-phase-decrease-step lib left right bound)))
      (if (not (eq (car result) :compare-phases))
          result
        (proof-with-checked-results
            ((no (t4-ordinals-phase-decrease-visit (1- n) (car (cddddr result))
                  left right (cadddr result)))
             (lib (cdr no))
             (step (proof-proof-cases (library-library-proof lib) (cadr result)
                    (caddr result) (car no))))
          (cons step lib))))))

(defun t4-ordinals-ordinals-phase-decrease (lib left right bound)
  (t4-ordinals-phase-decrease-visit 1000000 lib left right bound))

(defun t4-ordinals-decision-result (step lib evidence)
  (cons step (cons lib evidence)))

(defun t4-ordinals-decision-with-library (step lib new-lib evidence)
  (t4-ordinals-decision-result step new-lib
   (if (equal lib (t4-structural-evidence-proof evidence))
       (t4-structural-evidence-with-proof evidence new-lib)
     evidence)))

(defun t4-ordinals-decide-constant (lib test equality evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((right (t4-ordinals-step-right equality)))
      (if (equal right *proof-true*)
          (proof-with-checked-results ((step (proof-proof-true-from-eq proof equality)))
            (t4-ordinals-decision-result step lib evidence))
        (proof-with-checked-results
            ((result (t4-ordinals-ordinals-prove lib (proof-neg test) nil (list *proof-not*))))
          (t4-ordinals-decision-with-library (car result) lib (cdr result) evidence))))))

(defun t4-ordinals-decide-from-cons (lib test evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((arg (proof-term-at test 1))
         (cons-step (t4-structural-evidence-find evidence (list *proof-consp* arg))))
      (let ((evidence (cdr cons-step)))
        (if (not (car cons-step))
            (t4-ordinals-decision-result nil lib evidence)
          (proof-with-checked-results
              ((assumed (proof-proof-assume proof test t))
               (impossible (proof-proof-rewrite proof (car cons-step) assumed '(1 1)))
               (result (t4-ordinals-ordinals-simplify-first lib impossible nil nil))
               (step (proof-proof-front (library-library-proof (cdr result))
                      (car result) (proof-neg test))))
            (t4-ordinals-decision-with-library step lib (cdr result) evidence)))))))

(defun t4-ordinals-decide-equality (lib test evidence)
  (proof-with-checked-results
      ((right (and (proof-is-call test *proof-equal*) (proof-term-at test 2))))
    (if (not (proof-is-call right *proof-quote*))
        (t4-ordinals-decision-result nil lib evidence)
      (proof-with-checked-results ((constant (t4-ordinals-ordinals-constant lib test)))
        (if (car constant)
            (t4-ordinals-decide-constant (cdr constant) test (car constant) evidence)
          (t4-ordinals-decide-from-cons (cdr constant) test evidence))))))

(defun t4-ordinals-ordinals-decide-test (lib test evidence)
  (proof-with-checked-results ((yes (t4-structural-evidence-find evidence test)))
    (if (car yes)
        (t4-ordinals-decision-result (car yes) lib (cdr yes))
      (proof-with-checked-results
          ((no (t4-structural-evidence-find (cdr yes) (proof-neg test))))
        (if (car no)
            (t4-ordinals-decision-result (car no) lib (cdr no))
          (t4-ordinals-decide-equality lib test (cdr no)))))))

(defun t4-ordinals-request-p (value)
  (and (consp value) (eq (car value) :t4-ordinals-request)))

(defun t4-ordinals-request-left (request)
  (cadr request))

(defun t4-ordinals-request-right (request)
  (caddr request))

(defun t4-ordinals-request-evidence (request)
  (cadddr request))

(defun t4-ordinals-request-library (request)
  (car (cddddr request)))

(defmacro t4-ordinals-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name) (t4-ordinals-request-p ,name))
             ,name
           (t4-ordinals-with-results ,(cdr bindings) ,result))))))

(defund t4-ordinals-measure-branch-opening (lib term test holds decided)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premise (or decided (proof-proof-assume proof test holds)))
         (opened (proof-proof-select proof term premise))
         (value (t4-ordinals-step-right opened)))
      (list premise opened value))))

(defund t4-ordinals-measure-branch-close (lib step equality index premise guard)
  (proof-with-checked-results
      ((step (library-library-transport-argument lib step equality index)))
    (if (member-equal guard (cdr (proof-step-clause step)))
        (proof-proof-discharge (library-library-proof lib) step premise)
      step)))

(defun t4-ordinals-measure-leaf (lib left right evidence replies)
  (cond
   ((endp replies) (list :t4-ordinals-request left right evidence lib))
   ((failure-p (car replies)) (car replies))
   (t replies)))

(mutual-recursion
 (defund t4-ordinals-ordinals-compare-measures-compare (n left right branch-tests lib replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-ordinals-ordinals-compare-measures-compare")
     (proof-with-checked-results ((evidence (t4-structural-evidence-init lib branch-tests nil)))
       (cond
        ((proof-is-call left *proof-if*)
         (t4-ordinals-measure-case (1- n) lib left right branch-tests left 1 evidence replies))
        ((proof-is-call right *proof-if*)
         (t4-ordinals-measure-case (1- n) lib left right branch-tests right 2 evidence replies))
        (t (t4-ordinals-measure-leaf lib left right evidence replies))))))
 (defund t4-ordinals-measure-case (n lib left right tests term index evidence replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-ordinals-measure-case")
     (t4-ordinals-with-results
         ((test (proof-term-at term 1))
          (decision (t4-ordinals-ordinals-decide-test lib test evidence))
          (lib (cadr decision))
          (decided (car decision)))
       (if decided
           (proof-with-checked-results ((literal (proof-step-first decided)))
             (t4-ordinals-ordinals-compare-measures-compare-branch
              (1- n) (equal literal test) left right tests term index test decided lib replies))
         (t4-ordinals-with-results
             ((yes (t4-ordinals-ordinals-compare-measures-compare-branch
                    (1- n) t left right tests term index test nil lib replies))
              (no (t4-ordinals-ordinals-compare-measures-compare-branch
                   (1- n) nil left right tests term index test nil (cdar yes) (cdr yes)))
              (lib (cdar no))
              (step (proof-proof-cases (library-library-proof lib) test (caar yes) (caar no))))
           (cons (cons step lib) (cdr no)))))))
 (defund t4-ordinals-ordinals-compare-measures-compare-branch
     (n holds left right branch-tests term index test decided lib replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-ordinals-ordinals-compare-measures-compare-branch")
     (t4-ordinals-with-results
         ((opening (t4-ordinals-measure-branch-opening lib term test holds decided))
          (new-left (if (equal index 1) (caddr opening) left))
          (new-right (if (equal index 1) right (caddr opening)))
          (tests (append branch-tests (list (list test holds))))
          (result (t4-ordinals-ordinals-compare-measures-compare
                   (1- n) new-left new-right tests lib replies))
          (lib (cdar result))
          (guard (if holds (proof-neg test) test))
          (step (t4-ordinals-measure-branch-close lib (caar result) (cadr opening)
                 index (car opening) guard)))
       (cons (cons step lib) (cdr result))))))

(defun t4-ordinals-ordinals-compare-measures (lib goal tests replies)
  (t4-ordinals-with-results
      ((args (proof-list-of-length (cdr goal) 2))
       (result (t4-ordinals-ordinals-compare-measures-compare
                1000000 (car args) (cadr args) tests lib replies)))
    (car result)))
