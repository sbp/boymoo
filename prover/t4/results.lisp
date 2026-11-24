(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-results-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *t4-results-zp* (proof-sym "ZP" "ACL2"))
(defconst *t4-results-nth* (proof-cl "NTH"))
(defconst *t4-results-endp* (proof-cl "ENDP"))
(defconst *t4-results-atom* (proof-cl "ATOM"))
(defconst *t4-results-true-list* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *t4-results-result-predicates*
  (list (proof-sym "ALISTP" "ACL2")
        (proof-sym "BOOLEANP" "ACL2")
        (proof-sym "CHARACTER-LISTP" "ACL2")
        (proof-sym "INTEGER-LISTP" "ACL2")
        (proof-sym "NAT-LISTP" "ACL2")
        (proof-sym "SYMBOL-LISTP" "ACL2")
        *t4-results-true-list*))

(defconst *t4-results-initial-packages* '("ACL2" "COMMON-LISP" "KEYWORD"))

(defun t4-results-saved-failure-p (value)
  (and (consp value) (eq (car value) :t4-results-saved-failure)))

(defund t4-results-save-failure (value lib)
  (if (failure-p value)
      (list :t4-results-saved-failure value lib)
    value))

(defmacro t4-results-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings)))
      `(t4-relations-with-results (,(car bindings))
         (if (t4-results-saved-failure-p ,name)
             ,name
           (t4-results-with-results ,(cdr bindings) ,result))))))

(defund t4-results-rational-value (value)
  (cond ((integerp value) value)
        ((eq value t) 1)
        ((not (equal (car value) "ratio")) :none)
        (t (proof-with-checked-results ((parts (proof-list-of-length (cdr value) 2)))
             (if (equal (cadr parts) 0)
                 '(:failure "failure" "")
               (/ (car parts) (cadr parts)))))))

(defund t4-results-rational-values (values)
  (if (endp values)
      nil
    (proof-with-checked-results ((value (t4-results-rational-value (car values))))
      (if (eq value :none)
          :none
        (proof-with-checked-results ((rest (t4-results-rational-values (cdr values))))
          (if (eq rest :none) :none (cons value rest)))))))

(defund t4-results-arithmetic-value (head values)
  (proof-with-checked-results ((nums (t4-results-rational-values values)))
    (if (eq nums :none)
        :none
      (proof-with-checked-results
          ((a (proof-term-at nums 0))
           (b (and (not (equal head *proof-minus*)) (proof-term-at nums 1))))
        (if (equal head *proof-less*)
            (if (< a b) *proof-t* *proof-nil*)
          (let ((value (cond ((equal head *proof-plus*) (+ a b))
                             ((equal head *proof-times*) (* a b))
                             (t (- a)))))
            (if (integerp value)
                value
              (list "ratio" (numerator value) (denominator value)))))))))

(defund t4-results-symbol-metadata (head value packages)
  (proof-with-checked-results
      ((tag (cond ((consp value) (car value))
                  ((null value) (proof-term-at value 0))
                  (t nil))))
    (cond
     ((equal head (proof-cl "CHARACTERP"))
      (if (equal tag "char") *proof-t* *proof-nil*))
     ((not (equal tag "sym")) (list "str" ""))
     ((equal head (proof-cl "SYMBOL-NAME"))
      (proof-with-checked-results ((name (proof-term-at value 2))) (list "str" name)))
     (t (proof-with-checked-results ((package (proof-term-at value 1)))
          (if (member-equal package packages) (list "str" package) :none))))))

(defund t4-results-extra-constant (term values packages)
  (let ((head (car term)))
    (cond
     ((equal head *proof-cons*)
      (proof-with-checked-results ((pair (proof-list-of-length values 2)))
        (proof-constant-cons-value (car pair) (cadr pair))))
     ((member-equal head (list (proof-cl "CHARACTERP") (proof-cl "SYMBOL-NAME")
                               (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2")))
      (proof-with-checked-results ((value (proof-term-at values 0)))
        (t4-results-symbol-metadata head value packages)))
     ((member-equal head (list *proof-plus* *proof-times* *proof-minus* *proof-less*))
      (t4-results-arithmetic-value head values))
     (t :none))))

(defund t4-results-constant (lib term packages)
  (proof-with-checked-results ((inherited (t4-ordinals-ordinals-constant lib term)))
    (if (or (car inherited) (not (proof-all-quoted-p (cdr term))))
        inherited
      (let ((lib (cdr inherited)))
        (proof-with-checked-results
            ((values (proof-quoted-values (cdr term)))
             (constant (t4-results-extra-constant term values packages))
             (step (and (not (eq constant :none))
                        (proof-proof-compute (library-library-proof lib) term constant))))
          (cons step lib))))))

(defund t4-results-chain (lib equality step)
  (proof-with-checked-results
      ((joined (proof-proof-chain (library-library-proof lib) equality (list step))))
    (cons joined lib)))

; Simplification calls the constant rule after simplifying the operands.
(mutual-recursion
 (defund t4-results-simplify (n lib term evidence definitions packages)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "t4-results-simplify")
     (proof-with-checked-results
         ((base (t4-results-simplify-core (1- n) lib term evidence definitions packages))
          (lib (cdr base))
          (equality (car base))
          (reduced (if equality (t4-relations-step-right equality) term))
          (selected (t4-ordinals-nonnil-selection lib reduced)))
       (if (not selected)
           base
         (proof-with-checked-results
             ((next (t4-results-simplify (1- n) lib (cadr selected) evidence definitions packages))
              (opened (t4-results-chain (cdr next) (car selected) (car next))))
           (if equality (t4-results-chain (cdr opened) equality (car opened))
             opened))))))

 (defund t4-results-simplify-core (n lib term evidence definitions packages)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-results-simplify-core"))
      ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
       (cons nil lib))
      ((endp term) (proof-term-at term 0))
      ((or (proof-compound (car term)) (member-equal (car term) definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (next (t4-results-simplify (1- n) lib (cadr expansion) evidence definitions packages)))
         (t4-results-chain (cdr next) (car expansion) (car next))))
      ((proof-is-call term *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (t4-results-simplify (1- n) lib test evidence definitions packages))
            (lib (cdr first))
            (path (proof-simplify-if-path (library-library-proof lib) term (car first) evidence)))
         (if (eq (car path) :simplify)
             (proof-with-checked-results
                 ((next (t4-results-simplify (1- n) lib (caddr path) evidence definitions packages)))
               (t4-results-chain (cdr next) (cadr path) (car next)))
           (cons path lib))))
      (t
       (proof-with-checked-results
           ((args (t4-results-simplify-arguments (1- n) lib term (cdr term) 1 nil
                                                 evidence definitions packages))
            (equality (car args))
            (current (if equality (t4-relations-step-right equality) term))
            (constant (t4-results-constant (cdr args) current packages)))
         (cond ((not (car constant)) args)
               (equality (t4-results-chain (cdr constant) equality (car constant)))
               (t constant)))))))

 (defund t4-results-simplify-arguments (n lib term args index result evidence definitions packages)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-results-simplify-arguments"))
    ((endp args) (cons result lib))
    (t
     (proof-with-checked-results
         ((arg (t4-results-simplify (1- n) lib (car args) evidence definitions packages))
          (lib (cdr arg))
          (next (proof-simplify-argument-result (library-library-proof lib) term index
                                                 result (car arg))))
       (t4-results-simplify-arguments (1- n) lib term (cdr args) (1+ index) next
                                      evidence definitions packages))))))

(defund t4-results-prove-visit (n lib term evidence definitions packages)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-results-prove-visit")
    (proof-with-checked-results ((premise (t4-ordinals-prove-premise lib term evidence)))
      (if premise
          (cons premise lib)
        (proof-with-checked-results
            ((result (t4-results-simplify 1000000 lib term evidence definitions packages))
             (lib (cdr result))
             (equality (car result))
             (right (and equality (t4-relations-step-right equality))))
          (cond
           ((or (not equality) (equal right term)) (proof-prove-unproved-term term))
           ((equal right *proof-true*)
            (proof-with-checked-results
                ((step (proof-proof-true-from-eq (library-library-proof lib) equality)))
              (cons step lib)))
           (t (proof-with-checked-results
                  ((next (t4-results-prove-visit (1- n) lib right evidence definitions packages))
                   (lib (cdr next))
                   (step (proof-proof-transport (library-library-proof lib) (car next) equality)))
                (cons step lib)))))))))

(defund t4-results-prove (lib term evidence definitions packages)
  (t4-results-prove-visit 1000000 lib term evidence definitions packages))

(defun t4-results-true-list-cons (lib pair)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opening (proof-proof-unfold proof (list *t4-results-true-list* pair)))
         (cons-step (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdr pair))))
         (body (t4-relations-step-right opening))
         (branch (proof-proof-select proof body cons-step))
         (view (proof-proof-chain proof opening (list branch)))
         (selector (library-library-axiom lib "CDR-CONS" (cdr pair))))
      (proof-proof-rewrite proof view selector '(1 2 1)))))

(defun t4-results-index-at-head (index)
  (cond ((rationalp index) (<= index 0))
        ((eq index t) nil)
        ((consp index)
         '(:failure "failure" ""))
        ((stringp index)
         '(:failure "failure" ""))
        (t
         '(:failure "failure" ""))))

(defund t4-results-unfold-projection-with-library (lib term packages)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((pair (proof-term-at term 2))
         (opening (proof-proof-unfold proof term))
         (cons-step (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdr pair))))
         (body (t4-relations-step-right opening))
         (empty-test (proof-term-at body 1))
         (nonempty (t4-results-prove lib (proof-neg empty-test) (list cons-step)
                                     (list *t4-results-endp* *t4-results-atom* *proof-not*) packages))
         (lib (cdr nonempty))
         (proof (library-library-proof lib))
         (branch (proof-proof-select proof body (car nonempty)))
         (chosen (t4-relations-step-right branch))
         (test (proof-term-at chosen 1))
         (index (proof-term-at (cadr term) 1))
         (at-head (t4-results-index-at-head index))
         (condition (t4-results-prove lib (if at-head test (proof-neg test)) nil
                                      (list *t4-results-zp* *proof-not*) packages))
         (lib (cdr condition))
         (proof (library-library-proof lib))
         (selected (proof-proof-select proof chosen (car condition)))
         (picked (proof-proof-chain proof opening (list branch selected)))
         (selector (library-library-axiom lib (if at-head "CAR-CONS" "CDR-CONS") (cdr pair))))
      (if at-head
          (t4-results-chain lib picked selector)
        (proof-with-checked-results
            ((suffix (t4-relations-step-right picked))
             (offset-term (proof-term-at suffix 1))
             (offset (t4-results-constant lib offset-term packages))
             (lib (cdr offset))
             (proof (library-library-proof lib))
             (shifted (if (car offset)
                          (proof-proof-rewrite proof picked (car offset) '(1 2 1))
                        '(:failure "failure" "")))
             (result (proof-proof-rewrite proof shifted selector '(1 2 2)))
             (step (proof-proof-tidy proof result)))
          (cons step lib))))))

(defun t4-results-unfold-projection (lib term)
  (proof-with-checked-results
      ((result (t4-results-unfold-projection-with-library lib term *t4-results-initial-packages*)))
    (car result)))

(defun t4-results-projection-index-text (index)
  (if (eq index t)
      "True"
    (let ((digits (decimal-text (abs index))))
      (cond ((< 4300 (length digits))
             '(:failure "SearchMiss" ""))
            ((< index 0) (concatenate 'string "NEG-" digits))
            (t digits)))))

(defund t4-results-projection-library (lib name head index packages)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
                     (proof-proof-facts proof))
        lib
      (proof-with-checked-results
          ((proved (t4-results-unfold-projection-with-library
                    lib (list head index (list *proof-cons* *library-x* *library-y*)) packages))
           (literal (proof-step-first (car proved))))
        (library-library-lemma (cdr proved) name literal (car proved) nil)))))

(defund t4-results-projection-with-packages (lib term packages)
  (if (not (proof-compound term))
      (cons nil lib)
    (proof-with-checked-results
        ((head (proof-term-at term 0))
         (index-term (and (member-equal head (list *t4-results-mv-nth* *t4-results-nth*))
                          (proof-term-at term 1)))
         (index (and (proof-is-call index-term *proof-quote*) (proof-term-at index-term 1)))
         (pair (and (or (integerp index) (eq index t)) (proof-term-at term 2))))
      (if (not (proof-is-call pair *proof-cons*))
          (cons nil lib)
        (proof-with-checked-results
            ((offset (t4-results-projection-index-text index))
             (name (concatenate 'string (caddr head) "-CONS-" offset))
             (lib (t4-results-projection-library lib name head index-term packages))
             (result (library-library-cite lib name (cdr pair) nil)))
          (cons result lib))))))

(defun t4-results-projection (lib term)
  (t4-results-projection-with-packages lib term *t4-results-initial-packages*))

(defund t4-results-lambda-application-p (value)
  (and (proof-compound value)
       (proof-with-checked-results ((head (proof-term-at value 0)))
         (proof-compound head))))

(defun t4-results-result-property-beta (n lib raw opening)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-results-result-property-beta")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results ((lambda-p (t4-results-lambda-application-p raw)))
        (if (not lambda-p)
            (list raw opening)
          (proof-with-checked-results
              ((step (proof-proof-beta proof raw))
               (next (if opening (proof-proof-chain proof opening (list step)) step))
               (body (t4-relations-step-right step)))
            (t4-results-result-property-beta (1- n) lib body next)))))))

(defund t4-results-projected-call (term definitions)
  (and (proof-is-call term *t4-results-mv-nth*)
       (proof-with-checked-results
           ((index (proof-term-at term 1))
            (target (and (proof-is-call index *proof-quote*) (proof-term-at term 2)))
            (head (and (proof-is-call index *proof-quote*)
                       (proof-compound target)
                       (proof-term-at target 0))))
         (and (assoc-equal head definitions) target))))

(mutual-recursion
 (defun t4-results-result-property-calls (term definitions)
   (declare (xargs :measure (acl2-count term)))
   (if (or (not (consp term))
           (not (proof-compound term))
           (proof-is-call term *proof-quote*))
       nil
     (proof-with-checked-results
         ((target (t4-results-projected-call term definitions))
          (rest (t4-results-result-property-call-arguments (cdr term) definitions)))
       (if target (cons target rest) rest))))

 (defun t4-results-result-property-call-arguments (terms definitions)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
         ((first (t4-results-result-property-calls (car terms) definitions))
          (rest (t4-results-result-property-call-arguments (cdr terms) definitions)))
       (append first rest)))))

(mutual-recursion
 (defun t4-results-result-property-placeholder (term target)
   (declare (xargs :measure (acl2-count term)))
   (cond ((equal term target) *proof-result*)
         ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
         ((endp term) (proof-term-at term 0))
         (t (proof-with-checked-results
                ((rest (t4-results-result-property-placeholder-arguments (cdr term) target)))
              (cons (car term) rest)))))

 (defun t4-results-result-property-placeholder-arguments (terms target)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
         ((first (t4-results-result-property-placeholder (car terms) target))
          (rest (t4-results-result-property-placeholder-arguments (cdr terms) target)))
       (cons first rest)))))

(defund t4-results-result-property-open (proof value opened)
  (proof-with-checked-results ((lambda-p (t4-results-lambda-application-p value)))
    (let ((head (car value)))
      (cond
       (lambda-p
        (proof-with-checked-results ((step (proof-proof-beta proof value)))
          (cons step opened)))
       ((proof-is-call value *termination-return-last*)
        (proof-with-checked-results ((step (proof-proof-unfold proof value)))
          (cons step opened)))
       ((and (proof-compound value)
             (assoc-equal head (proof-proof-definitions proof))
             (not (member-equal head opened))
             (not (equal head *proof-quote*)))
        (proof-with-checked-results ((step (proof-proof-unfold proof value)))
          (cons step (append opened (list head)))))
       (t (cons nil opened))))))

(defun t4-results-result-property-visit (n value tests opened template paths context)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-results-result-property-visit"))
   ((zp paths) '(:failure "SearchMiss" ""))
   ((proof-is-call value *proof-if*)
    (t4-relations-with-results
        ((parts (proof-list-of-length (cdr value) 3))
         (yes (t4-results-result-property-visit
               (1- n) (cadr parts) (append tests (list (list (car parts) t)))
               opened template (1- paths) context))
         (no (t4-results-result-property-visit
              (1- n) (caddr parts) (append tests (list (list (car parts) nil)))
              opened template (cadr yes) (caddr yes)))
         (proof (library-library-proof (car (caddr no))))
         (step (t4-relations-by-value-if proof value template (car yes) (car no))))
      (list step (cadr no) (caddr no))))
   (t
    (t4-relations-with-results
        ((proof (library-library-proof (car context)))
         (open (t4-results-result-property-open proof value opened)))
      (if (car open)
          (t4-relations-with-results
              ((body (t4-relations-step-right (car open)))
               (inner (t4-results-result-property-visit
                       (1- n) body tests (cdr open) template (1- paths) context))
               (proof (library-library-proof (car (caddr inner))))
               (step (t4-relations-by-value-rewrite proof (car inner) (car open) template)))
            (list step (cadr inner) (caddr inner)))
        (t4-relations-with-results
            ((goal (proof-subst template (list (cons *proof-result* value))))
             (answer (t4-relations-recipe-request context :solve (list goal tests nil 0))))
          (list (car answer) (1- paths) (cdr answer))))))))

(defun t4-results-result-property-query (lib formula replies)
  (let ((proof (library-library-proof lib)))
    (t4-relations-with-results
        ((beta (t4-results-result-property-beta 1000000 lib formula nil))
         (raw (car beta))
         (calls (t4-results-result-property-calls raw (proof-proof-definitions proof))))
      (let ((returns (proof-unique calls)))
        (if (not (equal (len returns) 1))
            (cons nil lib)
          (let ((target (car returns)))
            (t4-relations-with-results
                ((template (t4-results-result-property-placeholder raw target))
                 (root (proof-proof-unfold proof target))
                 (body (t4-relations-step-right root))
                 (visited (t4-results-result-property-visit
                           1000000 body nil (list (car target)) template 48 (cons lib replies)))
                 (lib (car (caddr visited)))
                 (proof (library-library-proof lib))
                 (rewritten (t4-relations-by-value-rewrite proof (car visited) root template))
                 (result (if (cadr beta) (proof-proof-transport proof rewritten (cadr beta))
                           rewritten)))
              (cons result lib))))))))

(defun t4-results-result-property (lib formula)
  (t4-results-result-property-query lib formula nil))

(defun t4-results-guard-and-claim (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-list-of-length (cdr formula) 2)
    (list :none formula)))

(defun t4-results-definition (lib name)
  (let ((entry (assoc-equal name (proof-proof-definitions (library-library-proof lib)))))
    (if entry
        (cdr entry)
      '(:failure "MissingProofInput" ""))))

(defun t4-results-recursive-calls (lib name)
  (proof-with-checked-results
      ((definition (t4-results-definition lib name))
       (parts (proof-list-of-length definition 2))
       (calls (termination-recursive-calls *termination-all* (list (cons name parts)))))
    (list (car parts) calls)))

(defun t4-results-list-projection-invariant-tail-list (tests lib guard obj)
  (if (eq guard :none)
      '(:failure "SearchMiss" "")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((evidence (t4-structural-evidence-init lib tests nil))
           (cons-step (t4-structural-evidence-require evidence (list *proof-consp* obj)))
           (equation (proof-proof-unfold proof guard))
           (body (t4-relations-step-right equation))
           (branch (proof-proof-select proof body (car cons-step)))
           (shape (proof-proof-chain proof equation (list branch)))
           (assumed (proof-proof-assume proof guard t)))
        (proof-proof-rewrite proof assumed shape '(1))))))

(defund t4-results-list-projection-invariant-decrease
    (tests lib guard obj condition decrease)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((evidence (t4-structural-evidence-init lib tests nil))
         (shape (t4-structural-evidence-require evidence (list *proof-consp* obj)))
         (hypothesis (proof-proof-assume proof condition t))
         (smaller (proof-proof-discharge proof decrease (car shape)))
         (result (proof-proof-prove-if proof hypothesis smaller)))
      (if (eq guard :none)
          result
        (proof-with-checked-results
            ((proper-tail (t4-results-list-projection-invariant-tail-list tests lib guard obj)))
          (proof-proof-modus-ponens proof result proper-tail))))))

(defund t4-results-list-projection-rewrite (proof proved projected)
  (proof-with-checked-results
      ((reversed (proof-proof-symmetric proof projected))
       (rewritten (proof-proof-rewrite proof proved reversed '(1 1))))
    (proof-proof-tidy proof rewritten)))

(defund t4-results-field-result (step context)
  (t4-results-with-results ((step (t4-results-save-failure step (car context))))
    (cons step context)))

(defun t4-results-list-projection-invariant-prove-field
    (n value tests context guard obj smaller-field condition decrease)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-results-list-projection-invariant-prove-field")
    (let* ((lib (car context))
           (proof (library-library-proof lib)))
      (t4-results-save-failure
       (cond
        ((equal value *proof-false*)
         (t4-results-field-result
          (proof-proof-prove proof (list *t4-results-true-list* *proof-false*)
                             nil (list *t4-results-true-list* (proof-cl "EQ")))
          context))
        ((equal value (list *library-cdr* obj))
         (t4-results-field-result
          (t4-results-list-projection-invariant-tail-list tests lib guard obj) context))
        ((equal value smaller-field)
         (t4-results-field-result
          (t4-results-list-projection-invariant-decrease tests lib guard obj condition decrease)
          context))
        ((proof-is-call value *proof-cons*)
         (t4-results-with-results
             ((tail (proof-term-at value 2))
              (proved (t4-results-list-projection-invariant-prove-field
                       (1- n) tail tests context guard obj smaller-field condition decrease)))
           (t4-results-field-result
            (proof-with-checked-results ((shape (t4-results-true-list-cons (cadr proved) value)))
              (proof-proof-transport (library-library-proof (cadr proved)) (car proved) shape))
            (cdr proved))))
        (t
         (t4-results-with-results ((selected (t4-results-projection lib value)))
           (let* ((lib (cdr selected))
                  (context (cons lib (cdr context)))
                  (proof (library-library-proof lib)))
             (t4-results-save-failure
              (t4-results-with-results
                  ((projection
                    (or (car selected)
                        (t4-results-with-results
                            ((target (and (proof-is-call value *t4-results-mv-nth*)
                                          (proof-term-at value 2))))
                          (if (not (proof-is-call target *termination-return-last*))
                              '(:failure "SearchMiss" "")
                            (proof-with-checked-results
                                ((opening (proof-proof-unfold proof target))
                                 (reflexive (proof-proof-reflexive proof value)))
                              (proof-proof-rewrite proof reflexive opening '(1 2 2)))))))
                   (next (t4-relations-step-right projection))
                   (proved (t4-results-list-projection-invariant-prove-field
                            (1- n) next tests context guard obj smaller-field condition decrease)))
                (t4-results-field-result
                 (t4-results-list-projection-rewrite (library-library-proof (cadr proved))
                                                     (car proved) projection)
                 (cdr proved)))
              lib)))))
       lib))))

(defun t4-results-reflected-calls-p (calls reflected)
  (or (endp calls)
      (and (equal (termination-call-actuals (car calls)) reflected)
           (t4-results-reflected-calls-p (cdr calls) reflected))))

(defun t4-results-list-projection-object (formals prefix i arguments calls guard)
  (if (endp formals)
      nil
    (let ((reflected (append (reverse prefix)
                             (cons (list *library-cdr* (car formals)) (cdr formals)))))
      (proof-with-checked-results
          ((object (and (t4-results-reflected-calls-p calls reflected)
                        (proof-with-checked-results ((obj (proof-term-at arguments i)))
                          (and (not (proof-compound obj))
                               (not (member-equal obj (seq-slice arguments 0 i)))
                               (not (member-equal obj (nthcdr (1+ i) arguments)))
                               (or (eq guard :none) (equal guard (list *t4-results-true-list* obj)))
                               (list obj))))))
        (if object
            object
          (t4-results-list-projection-object
           (cdr formals) (cons (car formals) prefix) (1+ i) arguments calls guard))))))

(defun t4-results-changed-bindings (previous current)
  (if (or (endp previous) (endp current))
      nil
    (let ((rest (t4-results-changed-bindings (cdr previous) (cdr current))))
      (if (equal (car previous) (car current))
          rest
        (cons (list (car previous) (car current)) rest)))))

(defun t4-results-recursive-applications (calls name bindings)
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((application (proof-subst (cons name (termination-call-actuals (car calls))) bindings))
         (rest (t4-results-recursive-applications (cdr calls) name bindings)))
      (cons application rest))))

(defun t4-results-recursive-changes (applications actuals)
  (if (endp applications)
      nil
    (cons (cons (car applications) (t4-results-changed-bindings actuals (cdar applications)))
          (t4-results-recursive-changes (cdr applications) actuals))))

(defun t4-results-list-result-step-p (changes binding)
  (or (endp changes)
      (and (member-equal binding (cdar changes))
           (t4-results-list-result-step-p (cdr changes) binding))))

(defun t4-results-list-result-argument (actuals kind changes)
  (if (endp actuals)
      nil
    (let* ((argument (car actuals))
           (child (if kind (list kind argument) (library-plus *proof-neg-one* argument))))
      (if (t4-results-list-result-step-p changes (list argument child))
          (list kind argument)
        (t4-results-list-result-argument (cdr actuals) kind changes)))))

(defun t4-results-list-result-measure (kinds actuals changes)
  (if (endp kinds)
      nil
    (or (t4-results-list-result-argument actuals (car kinds) changes)
        (t4-results-list-result-measure (cdr kinds) actuals changes))))

(defun t4-results-list-result-unroll-equality (n lib step target)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-results-list-result-unroll-equality")
    (proof-with-checked-results
        ((right (t4-relations-step-right step))
         (value (proof-term-at right 1)))
      (if (not (proof-is-call value *proof-cons*))
          step
        (proof-with-checked-results ((expected (proof-term-at target 2)))
          (if (equal right expected)
              step
            (proof-with-checked-results
                ((view (t4-results-true-list-cons lib value))
                 (rewritten (proof-proof-rewrite (library-library-proof lib) step view '(1 2))))
              (t4-results-list-result-unroll-equality (1- n) lib rewritten target))))))))

(defund t4-results-list-result-assumption
    (lib bindings formula equality target tests required decrease)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((evidence (t4-structural-evidence-init lib tests nil))
         (known (t4-structural-evidence-require evidence required))
         (smaller (proof-proof-discharge proof decrease (car known)))
         (literal (proof-step-first smaller))
         (case-claim (proof-subst formula (t4-relations-substitution bindings)))
         (assumed (proof-proof-assume proof (proof-ite literal case-claim *proof-true*) t))
         (proved (proof-proof-prove-if proof assumed smaller))
         (step (if equality (t4-results-list-result-unroll-equality 1000000 lib proved target)
                 proved))
         (actual (proof-step-first step)))
      (if (equal actual target)
          step
        '(:failure "InferenceMismatch" "")))))

(defund t4-results-list-result-solve (target tests context)
  (t4-relations-with-results
      ((evidence (t4-structural-evidence-init (car context) tests nil))
       (answer (t4-relations-recipe-request context :equation (list target evidence))))
    (let ((equation (caar answer))
          (context (cdr answer)))
      (if (not equation)
          (t4-relations-recipe-request context :solve (list target tests nil 0))
        (t4-relations-with-results
            ((rhs (t4-relations-step-right equation))
             (proved (t4-relations-recipe-request context :solve (list rhs tests nil 0)))
             (step (proof-proof-transport (library-library-proof (cadr proved))
                                          (car proved) equation)))
          (cons step (cdr proved)))))))

(defun t4-results-list-result-invariant-visit
    (n value tests context template formula equality changes required decrease)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-results-list-result-invariant-visit")
    (let* ((lib (car context))
           (proof (library-library-proof lib))
           (changed (assoc-equal value changes)))
      (t4-relations-with-results ((target (proof-subst template (list (cons *proof-result* value)))))
        (cond
         (changed
          (proof-with-checked-results
              ((step (t4-results-list-result-assumption lib (cdr changed) formula equality
                                                        target tests required decrease)))
            (cons step context)))
         ((proof-is-call value *proof-cons*)
          (t4-relations-with-results
              ((shape (t4-results-true-list-cons lib value))
               (tail (proof-term-at value 2))
               (inner (t4-results-list-result-invariant-visit
                       (1- n) tail tests context template formula equality changes required decrease))
               (proof (library-library-proof (cadr inner)))
               (reversed (proof-proof-symmetric proof shape))
               (step (proof-proof-rewrite proof (car inner) reversed (if equality '(1 1) '(1)))))
            (cons step (cdr inner))))
         ((proof-is-call value *termination-return-last*)
          (t4-relations-with-results
              ((equation (proof-proof-unfold proof value))
               (body (t4-relations-step-right equation))
               (inner (t4-results-list-result-invariant-visit
                       (1- n) body tests context template formula equality changes required decrease))
               (proof (library-library-proof (cadr inner)))
               (step (t4-relations-by-value-rewrite proof (car inner) equation template)))
            (cons step (cdr inner))))
         ((and equality (equal (cadr target) (caddr target)))
          (proof-with-checked-results ((step (proof-proof-reflexive proof (cadr target))))
            (cons step context)))
         (t (t4-results-list-result-solve target tests context)))))))

(defund t4-results-guarded-result-type-known (value tests template context)
  (t4-relations-with-results
      ((expected (proof-subst template (list (cons *proof-result* value))))
       (evidence (t4-structural-evidence-init (car context) tests nil))
       (known (t4-relations-recipe-request context :known (list expected evidence)))
       (result (if (caar known) known
                 (let* ((context (cdr known))
                        (evidence (t4-structural-evidence-with-proof (cdar known) (car context))))
                   (t4-relations-recipe-request context :fact-proof (list expected evidence))))))
    (cons expected result)))

(defund t4-results-by-value-result (step remaining context)
  (t4-results-with-results ((step (t4-results-save-failure step (car context))))
    (list step remaining context)))

(mutual-recursion
 (defun t4-results-by-value (n recipe value tests template arguments remaining context)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof (car context))))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-results-by-value"))
      ((proof-is-call value *proof-if*)
       (t4-results-with-results
           ((parts (proof-list-of-length (cdr value) 3))
            (yes (t4-results-by-value
                  (1- n) recipe (cadr parts) (append tests (list (list (car parts) t)))
                  template arguments remaining context))
            (no (t4-results-by-value
                 (1- n) recipe (caddr parts) (append tests (list (list (car parts) nil)))
                 template arguments (cadr yes) (caddr yes)))
            (proof (library-library-proof (car (caddr no)))))
         (t4-results-by-value-result
          (t4-relations-by-value-if proof value template (car yes) (car no))
          (cadr no) (caddr no))))
      (t
       (t4-results-with-results
           ((lambda-p (t4-results-save-failure (t4-results-lambda-application-p value) (car context))))
         (if lambda-p
             (t4-results-with-results
                 ((equation (proof-proof-beta proof value))
                  (opened (t4-relations-step-right equation))
                  (inner (t4-results-by-value
                          (1- n) recipe opened tests template arguments remaining context))
                  (proof (library-library-proof (car (caddr inner)))))
               (t4-results-by-value-result
                (t4-relations-by-value-rewrite proof (car inner) equation template)
                (cadr inner) (caddr inner)))
           (t4-results-with-results
               ((result
                 (case recipe
                   (:guarded-result-type
                    (t4-results-guarded-result-type-visit
                     (1- n) value tests arguments template remaining context))
                   (:list-projection-invariant
                    (t4-results-with-results
                        ((proved (t4-results-list-projection-invariant-prove-field
                                  1000000 (list *t4-results-mv-nth* (car arguments) value) tests context
                                  (cadr arguments) (caddr arguments) (cadddr arguments)
                                  (nth 4 arguments) (nth 5 arguments))))
                      (list (car proved) remaining (cdr proved))))
                   (otherwise
                    (t4-relations-with-results
                        ((proved (t4-results-list-result-invariant-visit
                                  1000000 value tests context template (car arguments)
                                  (cadr arguments) (caddr arguments) (cadddr arguments)
                                  (nth 4 arguments))))
                      (list (car proved) remaining (cdr proved))))))
                (literal (t4-results-save-failure (proof-step-first (car result)) (car (caddr result))))
                (expected (t4-results-save-failure
                           (proof-subst template (list (cons *proof-result* value)))
                           (car (caddr result)))))
             (if (equal literal expected)
                 result
               (t4-results-save-failure '(:failure "InferenceMismatch" "") (car (caddr result)))))))))))

 (defun t4-results-guarded-result-type-visit (n value tests opened template remaining context)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-results-guarded-result-type-visit"))
    ((zp remaining) '(:failure "SearchMiss" ""))
    (t
     (t4-results-with-results
         ((known (t4-results-guarded-result-type-known value tests template context)))
       (let* ((expected (car known))
              (premise (caadr known))
              (context (cddr known))
              (proof (library-library-proof (car context))))
         (cond
          (premise (list premise (1- remaining) context))
          ((proof-is-call value *proof-quote*)
           (t4-results-with-results
               ((definitions (append *t4-results-result-predicates*
                                     (list *t4-results-atom* (proof-cl "EQ") *proof-not*)))
                (proved (t4-relations-recipe-request context :prove (list expected nil definitions))))
             (list (car proved) (1- remaining) (cdr proved))))
          (t
           (t4-results-with-results
               ((head (and (proof-compound value) (proof-term-at value 0))))
             (if (and (assoc-equal head (proof-proof-definitions proof))
                      (not (member-equal head opened)))
                 (t4-results-with-results
                     ((equation (proof-proof-unfold proof value))
                      (body (t4-relations-step-right equation))
                      (proved (t4-results-by-value
                               (1- n) :guarded-result-type body tests template
                               (append opened (list head)) (1- remaining) context))
                      (proof (library-library-proof (car (caddr proved))))
                      (step (t4-relations-by-value-rewrite proof (car proved) equation template)))
                   (list step (cadr proved) (caddr proved)))
               '(:failure "SearchMiss" "")))))))))))

(defun t4-results-list-projection-proof (context formula guard claim projection obj)
  (t4-results-with-results
      ((arithmetic (t4-relations-recipe-request context :use-arithmetic nil)))
    (let* ((context (cdr arithmetic))
           (lib (car context))
           (proof (library-library-proof lib))
           (bindings (list (list obj (list *library-cdr* obj))))
           (substitution (t4-relations-substitution bindings))
           (index (cadr projection))
           (template (list *t4-results-true-list* (list *t4-results-mv-nth* index *proof-result*))))
      (t4-results-with-results
          ((smaller-field (proof-subst (cadr claim) substitution))
           (decrease (library-library-builtin lib 3 obj))
           (smaller-goal (proof-subst formula substitution))
           (test (proof-step-first decrease))
           (condition (proof-ite test smaller-goal *proof-true*))
           (opening (proof-proof-unfold proof (caddr projection)))
           (body (t4-relations-step-right opening))
           (proved (t4-results-by-value
                    1000000 :list-projection-invariant body nil template
                    (list index guard obj smaller-field condition decrease) 0 context))
           (lib (car (caddr proved)))
           (proof (library-library-proof lib)))
        (t4-results-save-failure
         (proof-with-checked-results
             ((rewritten (t4-relations-by-value-rewrite proof (car proved) opening template))
              (step (if (eq guard :none) rewritten
                      (t4-ordinals-ordinals-imply lib guard rewritten)))
              (ordinal (library-library-builtin lib 1 obj))
              (result (proof-proof-induct proof ordinal step formula
                                          (t4-structural-count obj) (list bindings))))
           (t4-relations-recipe-result (cons result (caddr proved))))
         lib)))))

(defund t4-results-list-projection-invariant-recipe (lib formula recursive replies)
  (t4-relations-with-results
      ((parts (t4-results-guard-and-claim formula))
       (claim (cadr parts))
       (projection (and (proof-is-call claim *t4-results-true-list*) (proof-term-at claim 1))))
    (if (not (proof-is-call projection *t4-results-mv-nth*))
        (cons nil lib)
      (t4-relations-with-results ((projection (proof-list-of-length projection 3)))
        (let ((guard (car parts))
              (index (cadr projection))
              (root (caddr projection)))
          (t4-relations-with-results
              ((name (and (proof-is-call index *proof-quote*)
                          (proof-compound root)
                          (proof-term-at root 0))))
            (if (not (member-equal name recursive))
                (cons nil lib)
              (t4-relations-with-results
                  ((definition (t4-results-recursive-calls lib name))
                   (calls (cadr definition))
                   (object (and calls (t4-results-list-projection-object
                                       (car definition) nil 0 (cdr root) calls guard))))
                (if object
                    (t4-results-list-projection-proof
                     (cons lib replies) formula guard claim projection (car object))
                  (cons nil lib))))))))))

(defun t4-results-list-projection-invariant-query (lib formula recursive replies)
  (let ((result (t4-results-list-projection-invariant-recipe lib formula recursive replies)))
    (if (t4-results-saved-failure-p result) (cadr result) result)))

(defun t4-results-list-projection-invariant (lib formula recursive)
  (t4-results-list-projection-invariant-query lib formula recursive nil))

(defun t4-results-guarded-result-type-template (claim)
  (if (or (not (proof-compound claim)) (proof-is-call claim *proof-quote*))
      nil
    (proof-with-checked-results ((head (proof-term-at claim 0)))
      (cond
       ((or (member-equal head *t4-results-result-predicates*)
            (member-equal head (list *proof-consp* *proof-integerp* (proof-cl "SYMBOLP"))))
        (proof-with-checked-results ((root (proof-term-at claim 1)))
          (list root (list head *proof-result*))))
       ((proof-is-call claim *proof-if*)
        (proof-with-checked-results ((test (proof-term-at claim 1)))
          (if (not (proof-is-call test *proof-equal*))
              nil
            (proof-with-checked-results ((yes (proof-term-at claim 2)))
              (if (not (equal test yes))
                  nil
                (proof-with-checked-results ((truth (proof-term-at test 2)))
                  (if (not (equal truth *proof-true*))
                      nil
                    (proof-with-checked-results
                        ((no (proof-term-at claim 3))
                         (root (proof-term-at test 1)))
                      (and (equal no (proof-eq root *proof-false*))
                        (let ((is-true (proof-eq *proof-result* *proof-true*)))
                          (list root (proof-ite is-true is-true
                                                (proof-eq *proof-result* *proof-false*)))))))))))))
       (t nil)))))

(defun t4-results-guarded-result-type-query (lib formula recursive replies)
  (let ((proof (library-library-proof lib)))
    (t4-relations-with-results
        ((parts (t4-results-guard-and-claim formula))
         (target (t4-results-guarded-result-type-template (cadr parts))))
      (if (not target)
          (cons nil lib)
        (let ((guard (car parts))
              (root (car target))
              (template (cadr target)))
          (t4-relations-with-results
              ((name (and (proof-compound root) (proof-term-at root 0))))
            (if (or (not (assoc-equal name (proof-proof-definitions proof)))
                    (member-equal name recursive))
                (cons nil lib)
              (t4-results-with-results
                  ((opening (proof-proof-unfold proof root))
                   (body (t4-relations-step-right opening))
                   (assumptions (if (or (eq guard :none) (not guard))
                                    nil
                                  (list (list guard t))))
                   (proved (let ((answer (t4-results-by-value
                                          1000000 :guarded-result-type body assumptions template
                                          (list name) 48 (cons lib replies))))
                             (if (t4-results-saved-failure-p answer) (cadr answer) answer)))
                   (lib (car (caddr proved)))
                   (proof (library-library-proof lib))
                   (rewritten (t4-relations-by-value-rewrite proof (car proved) opening template))
                   (result (if (eq guard :none) rewritten
                             (t4-ordinals-ordinals-imply lib guard rewritten))))
                (cons result lib)))))))))

(defun t4-results-guarded-result-type (lib formula recursive)
  (t4-results-guarded-result-type-query lib formula recursive nil))

(defun t4-results-list-result-proof (context root formula equality changes selected)
  (t4-relations-with-results
      ((arithmetic (t4-relations-recipe-request context :use-arithmetic nil)))
    (let* ((context (cdr arithmetic))
           (lib (car context))
           (proof (library-library-proof lib))
           (kind (car selected))
           (argument (cadr selected))
           (number (cond ((equal kind *library-cdr*) 3)
                         ((equal kind *library-car*) 2)
                         (t 9))))
      (t4-relations-with-results
          ((decrease (library-library-builtin lib number argument))
           (sides (proof-list-of-length (cdr (proof-step-clause decrease)) 1))
           (side (car sides))
           (required (if (proof-is-call side *proof-not*) (proof-term-at side 1)
                       (proof-neg side)))
           (measure (t4-structural-count argument))
           (property (list *t4-results-true-list* *proof-result*))
           (template (if equality (proof-eq property (caddr formula)) property))
           (opening (proof-proof-unfold proof root))
           (body (t4-relations-step-right opening))
           (proved (let ((answer (t4-results-by-value
                                  1000000 :list-result-invariant body nil template
                                  (list formula equality changes required decrease) 0 context)))
                     (if (t4-results-saved-failure-p answer) (cadr answer) answer)))
           (lib (car (caddr proved)))
           (proof (library-library-proof lib))
           (rewritten (t4-relations-by-value-rewrite proof (car proved) opening template))
           (ordinal (library-library-builtin lib 1 argument))
           (result (proof-proof-induct proof ordinal rewritten formula
                                       measure (table-values changes))))
        (cons result lib)))))

(defun t4-results-list-result-invariant-query (lib formula recursive replies)
  (let ((equality (proof-is-call formula *proof-equal*)))
    (t4-relations-with-results
        ((claim (if equality (proof-term-at formula 1) formula))
         (true-list (proof-is-call claim *t4-results-true-list*))
         (root (and true-list (proof-term-at claim 1))))
      (cond
       ((or (not true-list) (not (proof-compound root))) (cons nil lib))
       ((endp root) '(:failure "SearchMiss" ""))
       (t
        (let ((name (car root))
              (actuals (cdr root)))
          (if (or (not (member-equal name recursive))
                  (t4-relations-any-compound actuals)
                  (not (equal (len (proof-unique actuals)) (len actuals))))
              (cons nil lib)
            (t4-relations-with-results
                ((rhs (and equality (proof-term-at formula 2))))
              (if (and equality (not (proof-is-call rhs *t4-results-true-list*)))
                  (cons nil lib)
                (t4-relations-with-results
                    ((definition (t4-results-recursive-calls lib name)))
                  (let ((calls (cadr definition)))
                    (if (not calls)
                        (cons nil lib)
                      (t4-relations-with-results
                          ((bindings (t4-relations-substitution (seq-zip (car definition) actuals)))
                           (applications (t4-results-recursive-applications calls name bindings))
                           (changes (t4-results-recursive-changes (proof-unique applications) actuals))
                           (picked (t4-results-list-result-measure
                                    (list *library-cdr* *library-car* nil) actuals changes)))
                        (if picked
                            (t4-results-list-result-proof
                             (cons lib replies) root formula equality changes picked)
                          (cons nil lib)))))))))))))))

(defun t4-results-list-result-invariant (lib formula recursive)
  (t4-results-list-result-invariant-query lib formula recursive nil))

(defun t4-results-query (recipe lib formula recursive replies)
  (case recipe
    (:result-property (t4-results-result-property-query lib formula replies))
    (:list-projection-invariant
     (let ((result (t4-results-list-projection-invariant-recipe lib formula recursive replies)))
       (if (t4-results-saved-failure-p result)
           (cons (cadr result) (caddr result))
         result)))
    (:guarded-result-type (t4-results-guarded-result-type-query lib formula recursive replies))
    (:list-result-invariant (t4-results-list-result-invariant-query lib formula recursive replies))
    (otherwise '(:failure "SearchMiss" ""))))
