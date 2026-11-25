(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *lexicographic-make-ord* (proof-sym "MAKE-ORD" "ACL2"))
(defconst *lexicographic-posp* (proof-sym "POSP" "ACL2"))
(defconst *lexicographic-ordinal-selectors*
  (list *rulers-atom* *proof-not* (proof-cl "EQ") (proof-cl "EQL")
        (proof-sym "O-FINP" "ACL2") (proof-sym "O-RST" "ACL2")
        (proof-sym "O-FIRST-EXPT" "ACL2") (proof-sym "O-FIRST-COEFF" "ACL2")))

(defmacro lexicographic-coefficient-bind (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)))
      `(let ((,name ,(cadar bindings)))
         (cond ((terms-proof-fallback-p ,name) (cons nil lib))
               ((failure-p ,name) ,name)
               (t (lexicographic-coefficient-bind ,(cdr bindings) ,body)))))))

(defun lexicographic-nonnegative-literal (term)
  (if (proof-is-call term *proof-quote*)
      (proof-with-checked-results
       ((value (proof-term-at term 1)))
       (or (eq value t) (natp value)))
    nil))

(defun lexicographic-library-natural (lib term)
  (if (eq (proof-proof-kind (library-library-proof lib)) :base)
      (proof-with-checked-results
       ((step (library-library-natural lib term)))
       (cons step lib))
    (lemmas-slice-library-natural lib term)))

(defun lexicographic-library-type-of (lib term)
  (if (eq (proof-proof-kind (library-library-proof lib)) :base)
      (proof-with-checked-results
       ((step (library-library-type-of lib term nil)))
       (cons step lib))
    (lemmas-slice-library-type-of lib term nil)))

(defun lexicographic-coefficient-bound (lib coefficient)
  (lexicographic-coefficient-bind
   ((left (and (proof-is-call coefficient *proof-plus*) (proof-term-at coefficient 1))))
   (if (equal left *proof-one*)
       (lexicographic-coefficient-bind
        ((addend (proof-term-at coefficient 2))
         (natural (lexicographic-library-natural lib addend))
         (lib (cdr natural))
         (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list addend)
                                            (list (car natural))))
         (integral (lexicographic-library-type-of lib addend))
         (lib (cdr integral))
         (above-zero (library-library-cite lib "POSITIVE-ONE-PLUS" (list addend)
                                           (list (car integral) nonnegative))))
        (cons above-zero lib))
     (lexicographic-coefficient-bind
      ((literal (lexicographic-nonnegative-literal coefficient)))
      (if (not literal)
          (cons nil lib)
        (lexicographic-coefficient-bind
         ((above-zero (proof-proof-prove (library-library-proof lib)
                                         (library-lt *proof-zero* coefficient) nil nil)))
         (cons above-zero lib)))))))

(defun lexicographic-positive-coefficient (lib coefficient)
  (lexicographic-coefficient-bind
   ((integral (lexicographic-library-type-of lib coefficient))
    (lib (cdr integral))
    (bound (lexicographic-coefficient-bound lib coefficient))
    (lib (cdr bound)))
   (if (not (car bound))
       (cons nil lib)
     (lexicographic-coefficient-bind
      ((positive (proof-proof-prove (library-library-proof lib)
                                    (list *lexicographic-posp* coefficient)
                                    (list (car integral) (car bound)) (list *lexicographic-posp*))))
      (cons positive lib)))))

(defun lexicographic-reduce-ordinal (lib value evidence)
  (proof-with-checked-results
   ((definitions (append (list *proof-ordinalp* *proof-ordinal-less* *library-natp*)
                         *lexicographic-ordinal-selectors*))
    (reducer (book-logic-reducer-init lib evidence definitions t 300 360 nil nil))
    (reduction (book-logic-reducer-reduce reducer (list *proof-ordinalp* value) nil))
    (reduced (car reduction))
    (first (and reduced (proof-step-first reduced)))
    (answer (and reduced (proof-term-at first 2))))
   (cons (and reduced (equal answer *proof-true*) reduced) lib)))

(defun lexicographic-finish-ordinal (lib value exponent coefficient tail)
  (proof-with-checked-results
   ((positive (lexicographic-positive-coefficient lib coefficient))
    (lib (cdr positive)))
   (if (not (car positive))
       (cons nil lib)
     (proof-with-checked-results
      ((true-tail (proof-proof-true-from-eq (library-library-proof lib) tail))
       (natural (lexicographic-library-natural lib exponent))
       (lib (cdr natural))
       (natural-exponent (library-library-cite lib "NATURAL-ORDINAL" (list exponent)
                                               (list (car natural)))))
      (lexicographic-reduce-ordinal lib value (list true-tail natural-exponent (car positive)))))))

(defun lexicographic-constructed-ordinal-with-library (lib value)
  (declare (xargs :measure (acl2-count value)))
  (proof-with-checked-results
   ((literal (lexicographic-nonnegative-literal value)))
   (cond
    (literal
     (proof-with-checked-results
      ((natural (lexicographic-library-natural lib value)))
      (lexicographic-reduce-ordinal (cdr natural) value (list (car natural)))))
    ((not (proof-is-call value *proof-cons*)) (cons nil lib))
    ((not (consp (cdr value))) '(:failure "failure" ""))
    ((not (proof-is-call (cadr value) *proof-cons*)) (cons nil lib))
    (t
     (proof-with-checked-results
      ((fields (proof-list-of-length (cdadr value) 2))
       (exponent (car fields))
       (coefficient (cadr fields))
       (ordinal-exponent (lexicographic-nonnegative-literal exponent)))
      (cond
       ((or (not ordinal-exponent) (equal (cadr exponent) 0)) (cons nil lib))
       ((not (consp (cddr value))) '(:failure "failure" ""))
       (t
        (proof-with-checked-results
         ((tail (lexicographic-constructed-ordinal-with-library lib (caddr value)))
          (lib (cdr tail)))
         (if (not (car tail))
             (cons nil lib)
           (lexicographic-finish-ordinal lib value exponent coefficient (car tail)))))))))))

(defun lexicographic-open-constructor (lib value)
  (if (not (proof-compound value))
      (cons nil lib)
    (proof-with-checked-results
     ((head (proof-term-at value 0))
      (definitions (proof-proof-definitions (library-library-proof lib))))
     (if (not (or (assoc-equal head definitions) (proof-is-call value *proof-cons*)))
         (cons nil lib)
       (proof-with-checked-results
        ((reducer (book-logic-reducer-init lib nil (list head *lexicographic-make-ord*)
                                          nil 42 150 nil nil))
         (reduction (book-logic-reducer-reduce reducer value nil))
         (opened (car reduction))
         (first (and opened (proof-step-first opened)))
         (explicit (if opened (proof-term-at first 2) value))
         (result (lexicographic-constructed-ordinal-with-library lib explicit))
         (lib (cdr result)))
        (if (not (and opened (car result)))
            result
          (proof-with-checked-results
           ((proof (library-library-proof lib))
            (reverse (proof-proof-symmetric proof opened))
            (step (proof-proof-rewrite proof (car result) reverse '(1 1 1)))
            (step (proof-proof-tidy proof step)))
           (cons step lib))))))))

(defun lexicographic-ordinal-constructor-equation-with-library (lib formula)
  (if (not (proof-is-call formula *proof-equal*))
      (cons nil lib)
    (proof-with-checked-results
     ((left (proof-term-at formula 1)))
     (if (not (proof-is-call left *proof-ordinalp*))
         (cons nil lib)
       (proof-with-checked-results
        ((right (proof-term-at formula 2)))
        (if (not (equal right *proof-true*))
            (cons nil lib)
          (proof-with-checked-results
           ((value (proof-term-at left 1)))
           (lexicographic-open-constructor lib value))))))))

(defun lexicographic-finish-natural-field (lib equation rulers value natural)
  (if (terms-proof-fallback-p natural)
      (cons (list equation rulers) lib)
    (proof-with-checked-results
     ((natural natural)
      (input-lib lib)
      (lib (cdr natural))
      (clipped (proof-proof-simplify (library-library-proof lib)
                                     (list *library-nfix* value)
                                     (list (car natural)) (list *library-nfix*)))
      (nfix (lemmas-nfix-equation lib value))
      (lib (cdr nfix))
      (rulers (halved-counters-rulers-for-library rulers input-lib lib))
      (step (proof-proof-chain (library-library-proof lib) equation (list (car nfix) clipped))))
     (cons (list step rulers) lib))))

(defun lexicographic-natural-field-with-rulers (lib term rulers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((definitions (halved-counters-counter-definitions
                    *countdowns-counter-wrappers* (proof-proof-definitions proof)))
      (derived (rulers-rulers-derived rulers))
      (reducer (book-logic-reducer-init lib (table-values derived) definitions
                                        nil 32 160 nil nil))
      (argument (proof-term-at term 1))
      (reduction (book-logic-reducer-reduce reducer argument nil))
      (expanded (car reduction))
      (equation (proof-proof-reflexive proof term))
      (equation (if expanded (proof-proof-rewrite proof equation expanded '(1 2 1)) equation))
      (first (proof-step-first equation))
      (clipped (proof-term-at first 2))
      (value (proof-term-at clipped 1)))
     (let ((found (rulers-rulers-find rulers (list *library-natp* value))))
       (if (terms-proof-fallback-p found)
           (cons (list equation rulers) lib)
         (proof-with-checked-results
          ((found found))
          (lexicographic-finish-natural-field
           lib equation (cdr found) value
           (if (car found) (cons (car found) lib) (lexicographic-library-natural lib value)))))))))

(defun lexicographic-transport-fields (lib step after before)
  (proof-with-checked-results
   ((step (library-library-transport-argument lib step after 1)))
   (library-library-transport-argument lib step before 2)))

(defun lexicographic-finish-numeric-descent (lib smaller larger after before rulers extra step)
  (if step
      (proof-with-checked-results
       ((step (lexicographic-transport-fields lib step after before)))
       (cons (list step rulers) lib))
    (proof-with-checked-results
     ((result (termination-proofs-prove-decrease-in
               1000000 (list (list *proof-ordinal-less* smaller larger))
               (termination-proofs-context lib rulers extra nil)))
      (context (cdr result))
      (rulers (termination-proofs-rulers-for-library context))
      (lib (termination-proofs-context-lib context))
      (value (car result)))
     (cond
      ((termination-proofs-callback-p value) (cons (list value rulers) lib))
      ((not (car value)) (cons (list nil rulers) lib))
      (t
       (proof-with-checked-results
        ((ordinal (car value))
         (comparison (halved-counters-library-ordinal-comparison lib smaller larger))
         (rulers (halved-counters-rulers-for-library rulers lib (cdr comparison)))
         (lib (cdr comparison))
         (proof (library-library-proof lib))
         (step (proof-proof-rewrite proof ordinal (car comparison) '(1)))
         (step (proof-proof-tidy proof step))
         (step (lexicographic-transport-fields lib step after before)))
        (cons (list step rulers) lib)))))))

(defun lexicographic-numeric-descent-with-rulers (lib after before rulers extra)
  (proof-with-checked-results
   ((after-first (proof-step-first after))
    (smaller (proof-term-at after-first 2))
    (before-first (proof-step-first before))
    (larger (proof-term-at before-first 2)))
   (if (equal smaller larger)
       (cons (list nil rulers) lib)
     (proof-with-checked-results
      ((comparison (library-lt smaller larger))
       (found (rulers-rulers-find rulers comparison))
       (rulers (cdr found))
       (step (if (car found)
                 (car found)
               (proof-with-checked-results
                ((proof (library-library-proof lib))
                 (constant (proof-proof-constant proof comparison))
                 (literal (and constant (proof-step-first constant)))
                 (answer (and constant (proof-term-at literal 2))))
                (and constant (not (equal answer *proof-false*))
                     (proof-proof-true-from-eq proof constant))))))
      (lexicographic-finish-numeric-descent lib smaller larger after before rulers extra step)))))

(defun lexicographic-descent-terms (lib goal)
  (proof-with-checked-results
   ((goal (proof-list-of-length goal 3)))
   (let ((child (cadr goal))
         (parent (caddr goal)))
     (if (not (and (proof-compound child) (proof-compound parent)
                   (equal (len child) 3) (equal (len parent) 3)
                   (equal (car child) (car parent))
                   (assoc-equal (car child) (proof-proof-definitions (library-library-proof lib)))))
         nil
       (let* ((a (list *lemmas-nfix* (cadr child)))
              (b (list *lemmas-nfix* (caddr child)))
              (x (list *lemmas-nfix* (cadr parent)))
              (y (list *lemmas-nfix* (caddr parent)))
              (first (library-lt a x))
              (same (proof-eq a x))
              (second (library-lt b y))
              (tie (proof-ite same second *proof-false*))
              (order (proof-ite first first tie)))
         (list (list a b) (list x y) first tie order))))))

(defun lexicographic-descent-goal (lib goal)
  (proof-with-checked-results
   ((terms (lexicographic-descent-terms lib goal)))
   (and terms (proof-eq goal (nth 4 terms)))))

(defun lexicographic-compare-fields (lib child parent rulers)
  (proof-with-checked-results
   ((after (lexicographic-natural-field-with-rulers lib child rulers))
    (before (lexicographic-natural-field-with-rulers (cdr after) parent (cadar after))))
   (cons (list (caar after) (caar before) (cadar before)) (cdr before))))

(defun lexicographic-first-descent (lib equation order after before rulers extra)
  (proof-with-checked-results
   ((result (lexicographic-numeric-descent-with-rulers lib after before rulers extra))
    (lib (cdr result))
    (smaller (caar result))
    (rulers (cadar result)))
   (if (or (not smaller) (termination-proofs-callback-p smaller))
       result
     (proof-with-checked-results
      ((proof (library-library-proof lib))
       (selected (proof-proof-select proof order smaller))
       (selected (proof-proof-chain proof equation (list selected)))
       (step (proof-proof-transport proof smaller selected)))
      (cons (list step rulers) lib)))))

(defun lexicographic-tied-descent (lib equation terms after before rulers extra)
  (proof-with-checked-results
   ((proof (library-library-proof lib))
    (reverse (proof-proof-symmetric proof before))
    (equal-step (proof-proof-chain proof after (list reverse)))
    (fields (lexicographic-compare-fields lib (cadar terms) (cadadr terms) rulers))
    (result (lexicographic-numeric-descent-with-rulers
             (cdr fields) (caar fields) (cadar fields) (caddar fields) extra))
    (lib (cdr result))
    (smaller (caar result))
    (rulers (cadar result)))
   (if (or (not smaller) (termination-proofs-callback-p smaller))
       result
     (proof-with-checked-results
      ((first (caddr terms))
       (tie (cadddr terms))
       (order (nth 4 terms))
       (proof (library-library-proof lib))
       (positive (proof-proof-assume proof first t))
       (selected (proof-proof-if-true proof order))
       (yes (proof-proof-transport proof positive selected))
       (not-first (proof-proof-if-false proof order))
       (selected (proof-proof-select proof tie equal-step))
       (selected (proof-proof-chain proof not-first (list selected)))
       (no (proof-proof-transport proof smaller selected))
       (both (proof-proof-cases proof first yes no))
       (step (proof-proof-transport proof both equation)))
      (cons (list step rulers) lib)))))

(defun lexicographic-descent-with-rulers (lib goal rulers equation extra)
  (proof-with-checked-results
   ((terms (lexicographic-descent-terms lib goal)))
    (cond
     ((not terms) (cons (list nil rulers) lib))
     ((terms-unproved-p equation) (cons (list nil rulers) lib))
     ((failure-p equation) equation)
     (t
      (proof-with-checked-results
       ((fields (lexicographic-compare-fields lib (caar terms) (caadr terms) rulers))
        (lib (cdr fields))
        (after (caar fields))
        (before (cadar fields))
        (rulers (caddar fields))
        (after-first (proof-step-first after))
        (after-value (proof-term-at after-first 2))
        (before-first (proof-step-first before))
        (before-value (proof-term-at before-first 2)))
       (if (equal after-value before-value)
           (lexicographic-tied-descent lib equation terms after before rulers extra)
         (lexicographic-first-descent lib equation (nth 4 terms) after before rulers extra)))))))

