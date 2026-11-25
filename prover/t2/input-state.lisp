(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)
(logic)

(defconst *t2-input-state-state* (proof-sym "STATE-P1" "ACL2"))
(defconst *t2-input-state-true-list* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *t2-input-state-global-table* (proof-sym "GLOBAL-TABLE" "ACL2"))
(defconst *t2-input-state-ordered* (proof-sym "ORDERED-SYMBOL-ALISTP" "ACL2"))
(defconst *t2-input-state-open-channels* (proof-sym "OPEN-CHANNELS-P" "ACL2"))
(defconst *t2-input-state-all-bound* (proof-sym "ALL-BOUNDP" "ACL2"))
(defconst *t2-input-state-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *t2-input-state-length* (proof-cl "LENGTH"))
(defconst *t2-input-state-stringp* (proof-cl "STRINGP"))
(defconst *t2-input-state-symbolp* (proof-cl "SYMBOLP"))
(defconst *t2-input-state-max* (proof-cl "MAX"))
(defconst *t2-input-state-eq* (proof-cl "EQ"))
(defconst *t2-input-state-eql* (proof-cl "EQL"))

(defun t2-input-state-formal-symbols (names)
  (if (endp names)
      nil
    (cons (proof-sym (car names) "ACL2")
          (t2-input-state-formal-symbols (cdr names)))))

(defun t2-input-state-instantiate (lib name formals actuals)
  (proof-proof-fact (library-library-proof lib) (proof-sym name "ACL2")
                    (seq-zip (t2-input-state-formal-symbols (text-split formals :none))
                            actuals)))

(defun t2-input-state-tests-visit (n lib proposition find-first term)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t2-input-state-tests-visit")
    (proof-with-checked-results
        ((literal (proof-step-first proposition))
         (otherwise (if (proof-is-call literal *proof-if*)
                        (proof-term-at literal 3)
                      nil)))
      (if (equal otherwise *proof-false*)
          (proof-with-checked-results
              ((parts (t2-arithmetic-arithmetic-conjunct lib proposition)))
            (if find-first
                (proof-with-checked-results ((first (proof-step-first (car parts))))
                  (if (equal first term)
                      (car parts)
                    (t2-input-state-tests-visit (1- n) lib (cadr parts) t term)))
              (proof-with-checked-results
                  ((rest (t2-input-state-tests-visit (1- n) lib (cadr parts) nil nil)))
                (cons (car parts) rest))))
        (cond ((not find-first) (list proposition))
              ((equal literal term) proposition)
              (t '(:failure "failure" "")))))))

(defun t2-input-state-tests (lib proposition)
  (t2-input-state-tests-visit 1000000 lib proposition nil nil))

(defun t2-input-state-tests-first (lib proposition term)
  (t2-input-state-tests-visit 1000000 lib proposition t term))

(defun t2-input-state-closed-boolean (lib term definitions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((simplified (t2-arithmetic-simplify proof term nil definitions))
         (equality (or simplified (t2-book-logic-constant lib term)))
         (literal (if equality
                      (proof-step-first equality)
                    '(:failure "failure" "")))
         (right (proof-term-at literal 2)))
      (if (equal right *proof-true*)
          (proof-proof-true-from-eq proof equality)
        (t2-input-fields-negated-value lib equality)))))

(defun t2-input-state-list-length (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (is-cons (list *proof-consp* x))
         (length-term (list *t2-input-state-length* x)))
    (proof-with-checked-results
        ((is-list (proof-proof-assume proof (list *t2-input-state-true-list* x) t))
         (cons-proof (proof-proof-assume proof is-cons t))
         (non-string (proof-proof-fact proof "consp-not-stringp" (list (list x x))))
         (disjoint (t2-arithmetic-arithmetic-modus-ponens lib non-string cons-proof))
         (opened (proof-proof-unfold proof length-term))
         (list-case (t2-input-fields-select lib opened disjoint))
         (atom-proof (proof-proof-assume proof is-cons nil))
         (is-list-term (proof-step-first is-list))
         (list-definition (proof-proof-unfold proof is-list-term))
         (list-branch (t2-input-fields-select lib list-definition atom-proof))
         (reversed (proof-proof-symmetric proof list-branch))
         (nil-input (proof-proof-transport proof is-list reversed))
         (nil-input (t2-arithmetic-simplify-first
                      proof nil-input nil (list *t2-input-state-eq* *t2-input-state-eql*)))
         (denial (t2-input-state-closed-boolean
                  lib (list *t2-input-state-stringp* *proof-false*) nil))
         (reversed (proof-proof-symmetric proof nil-input))
         (denial (proof-proof-rewrite proof denial reversed '(1 1 1)))
         (atom-case (t2-input-fields-select lib opened denial))
         (conclusion (proof-proof-cases proof is-cons list-case atom-case))
         (claim (proof-step-first conclusion)))
      (library-library-lemma lib "LENGTH-TRUE-LIST" claim conclusion
                             (list (proof-neg is-list-term))))))

(defun t2-input-state-length-after-write (lib slot value old-state is-list original)
  (let* ((proof (library-library-proof lib))
         (updated (list *t2-input-fields-update* slot value old-state)))
    (proof-with-checked-results
        ((keep-list (t2-input-state-instantiate lib "TRUE-LISTP-UPDATE-NTH" "L KEY VAL"
                                              (list old-state slot value)))
         (keep-list (t2-arithmetic-arithmetic-modus-ponens lib keep-list is-list))
         (original-eq (library-library-cite lib "LENGTH-TRUE-LIST" (list old-state)
                                            (list is-list)))
         (exact-len (proof-proof-rewrite proof original original-eq '(1 1)))
         (length-eq (t2-input-state-instantiate lib "LEN-UPDATE-NTH" "X N VAL"
                                              (list old-state slot value)))
         (length-eq (proof-proof-rewrite proof length-eq exact-len '(1 2 2)))
         (literal (proof-step-first length-eq))
         (right (proof-term-at literal 2))
         (reduced (t2-arithmetic-simplify proof right nil
                                         (list *t2-input-state-max* *t2-input-state-nfix*
                                               *proof-not*)))
         (new-length (proof-proof-chain proof length-eq (list reduced)))
         (as-length (library-library-cite lib "LENGTH-TRUE-LIST" (list updated)
                                          (list keep-list)))
         (as-length (proof-proof-chain proof as-length (list new-length))))
      (list keep-list as-length))))

(defun t2-input-state-update-projections (lib old-state updated)
  (proof-with-checked-results ((update (proof-list-of-length updated 4)))
    (list :projections old-state update lib)))

(defun t2-input-state-projection-equation (lib term old-state update index accessor)
  (let ((proof (library-library-proof lib))
        (slot (cadr update))
        (value (caddr update)))
    (proof-with-checked-results
        ((equation (t2-input-state-instantiate lib "NTH-UPDATE-NTH" "M N VAL L"
                                             (list index slot value old-state)))
         (literal (proof-step-first equation))
         (right (proof-term-at literal 2))
         (test (proof-term-at right 1))
         (evidence (t2-input-state-closed-boolean
                    lib test (list *t2-input-state-nfix* *proof-not*)))
         (equation (t2-input-fields-select lib equation evidence)))
      (if (not accessor)
          equation
        (proof-with-checked-results ((equation (proof-proof-chain proof accessor (list equation))))
          (if (equal index slot)
              equation
            (proof-with-checked-results
                ((original (proof-proof-unfold proof (list (car term) old-state)))
                 (original (proof-proof-symmetric proof original)))
              (proof-proof-chain proof equation (list original)))))))))

(defun t2-input-state-update-projections-direct (term lib old-state updated)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((update (proof-list-of-length updated 4)))
      (proof-with-checked-results
          ((projection (if (proof-is-call term *t2-input-fields-nth*)
                          (proof-term-at term 2)
                        :none)))
        (cond
         ((equal projection updated)
          (t2-input-state-projection-equation lib term old-state update (cadr term) nil))
         ((and (equal (len term) 2) (equal (cadr term) updated)
               (assoc-equal (car term) (proof-proof-definitions proof)))
          (proof-with-checked-results
              ((accessor (proof-proof-unfold proof term))
               (literal (proof-step-first accessor))
               (expanded (proof-term-at literal 2)))
            (if (not (proof-is-call expanded *t2-input-fields-nth*))
                nil
              (proof-with-checked-results ((source (proof-term-at expanded 2)))
                (and (equal source updated)
                     (t2-input-state-projection-equation
                      lib term old-state update (cadr expanded) accessor))))))
         ((integerp term) '(:failure "failure" ""))
         (t nil))))))

(defun t2-input-state-state-writes-unaffected-lookup (term lib globals-after globals-before)
  (if (not (proof-is-call term *t2-input-fields-assoc*))
      nil
    (proof-with-checked-results ((table (proof-term-at term 2)))
      (if (not (equal table globals-after))
          nil
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((equation (t2-input-fields-assoc-write lib (cadr term) *library-y*
                                                     *library-z* globals-before))
               (literal (proof-step-first equation))
               (right (proof-term-at literal 2))
               (test (proof-term-at right 1))
               (distinct (proof-proof-assume proof test nil)))
            (t2-input-fields-select lib equation distinct)))))))

(defun t2-input-state-rewrite-call (lib term direct)
  (case (car direct)
    (:projections (t2-input-state-update-projections-direct
                   term (or (cadddr direct) lib) (cadr direct) (caddr direct)))
    (:unaffected-lookup (t2-input-state-state-writes-unaffected-lookup
                         term (or (cadddr direct) lib) (cadr direct) (caddr direct)))
    (otherwise (table-get direct term nil))))

(mutual-recursion
 (defun t2-input-state-rewrite-terms (lib term direct)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
    ((not (consp term)) (t2-input-state-rewrite-call lib term direct))
    (t (let ((proof (library-library-proof lib)))
         (proof-with-checked-results
             ((equation (t2-input-state-rewrite-arguments lib term direct (cdr term) 1 nil))
              (literal (if equation (proof-step-first equation) nil))
              (current (if equation (proof-term-at literal 2) term))
              (transformed (t2-input-state-rewrite-call lib current direct)))
           (if equation
               (proof-proof-chain proof equation (list transformed))
             transformed))))))

 (defun t2-input-state-rewrite-arguments (lib term direct arguments index equation)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       equation
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((replacement (t2-input-state-rewrite-terms lib (car arguments) direct))
            (next (if replacement
                      (proof-with-checked-results
                          ((base (or equation (proof-proof-reflexive proof term))))
                        (proof-proof-rewrite proof base replacement (list 1 2 index)))
                    equation)))
         (t2-input-state-rewrite-arguments lib term direct (cdr arguments) (1+ index) next))))))

(defun t2-input-state-ordered-write (lib table key value ordered key-symbol)
  (proof-with-checked-results
      ((assertion (t2-input-state-instantiate lib "ORDERED-SYMBOL-ALISTP-ADD-PAIR" "GS W5 W6"
                                            (list table key value)))
       (evidence (t2-field-conjunction lib ordered key-symbol)))
    (t2-arithmetic-arithmetic-modus-ponens lib assertion evidence)))

(defun t2-input-state-state-writes-new-channel-table (test previous can-open)
  (declare (ignore previous))
  (proof-with-checked-results ((expected (proof-step-first can-open)))
    (if (equal test expected) can-open '(:failure "failure" ""))))

(defun t2-input-state-state-writes-global-change
    (test previous lib globals-before globals-after symbolic-key)
  (let ((proof (library-library-proof lib))
        (y *library-y*)
        (z *library-z*))
    (cond
     ((proof-is-call test *t2-input-state-ordered*)
      (t2-input-state-ordered-write lib globals-before y z previous symbolic-key))
     ((proof-is-call test *t2-input-state-all-bound*)
      (proof-with-checked-results
          ((keys (proof-term-at test 1))
           (bound (t2-input-state-instantiate
                   lib "ADD-PAIR-PRESERVES-ALL-BOUNDP" "ALIST1 ALIST2 SYM VAL"
                   (list keys globals-before y z))))
        (t2-arithmetic-arithmetic-modus-ponens lib bound previous)))
     (t (proof-with-checked-results
            ((bound (t2-input-fields-bindings lib test))
             (opening (or bound (proof-proof-reflexive proof test)))
             (literal (proof-step-first opening))
             (right (proof-term-at literal 2))
             (unaffected (t2-input-state-rewrite-terms
                          lib right (list :unaffected-lookup globals-after globals-before lib)))
             (opening (proof-proof-chain proof opening (list unaffected)))
             (old (proof-step-first previous))
             (prior (t2-input-fields-bindings lib old))
             (known (if prior (proof-proof-rewrite proof previous prior '(1)) previous)))
          (proof-proof-transport proof known opening))))))

(defun t2-input-state-changed-field (test previous lib recipe)
  (case (car recipe)
    (:new-channel-table
     (t2-input-state-state-writes-new-channel-table test previous (cadr recipe)))
    (:global-change
     (t2-input-state-state-writes-global-change test previous (or (nth 4 recipe) lib)
                                               (cadr recipe) (caddr recipe) (cadddr recipe)))
    (otherwise (table-get recipe (list test previous) nil))))

(defun t2-input-state-renew-fields (lib old-fields new-fields projections changed-field)
  (declare (xargs :measure (acl2-count old-fields)))
  (cond
   ((endp old-fields)
    (if (endp new-fields)
        nil
      '(:failure "failure" "")))
   ((endp new-fields) '(:failure "failure" ""))
   (t (let ((proof (library-library-proof lib))
            (old (car old-fields)))
        (proof-with-checked-results
            ((target (proof-step-first (car new-fields)))
             (equation (t2-input-state-rewrite-terms lib target projections))
             (previous (proof-step-first old))
             (step
              (if (not equation)
                  (if (equal target previous) old '(:failure "failure" ""))
                (proof-with-checked-results
                    ((literal (proof-step-first equation))
                     (right (proof-term-at literal 2)))
                  (if (equal right previous)
                      (proof-proof-transport proof old equation)
                    (proof-with-checked-results
                        ((changed (t2-input-state-changed-field right old lib changed-field))
                         (claim (proof-step-first changed)))
                      (if (equal claim right)
                          (proof-proof-transport proof changed equation)
                        '(:failure "failure" "")))))))
             (rest (t2-input-state-renew-fields lib (cdr old-fields) (cdr new-fields)
                                                projections changed-field)))
          (cons step rest))))))

(defun t2-input-state-checked-old-fields (old-fields old-state)
  (proof-with-checked-results
      ((is-list (proof-term-at old-fields 0))
       (list-test (proof-step-first is-list)))
    (if (not (equal list-test (list *t2-input-state-true-list* old-state)))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((original (proof-term-at old-fields 1))
           (length-test (proof-step-first original))
           (length-term (proof-term-at length-test 1)))
        (if (equal length-term (list *t2-input-state-length* old-state))
            (list is-list original)
          '(:failure "failure" ""))))))

(defun t2-input-state-updated-state (lib index value proof-for-changed-field)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (old-state-test (list *t2-input-state-state* x)))
    (proof-with-checked-results
        ((original (proof-proof-assume proof old-state-test t))
         (test (proof-step-first original))
         (definition (proof-proof-unfold proof test))
         (expanded (proof-proof-rewrite proof original definition '(1)))
         (old-fields (t2-input-state-tests lib expanded))
         (checked (t2-input-state-checked-old-fields old-fields x)))
      (let ((slot (proof-quote index)))
        (proof-with-checked-results
            ((length-facts (t2-input-state-length-after-write
                            lib slot value x (car checked) (cadr checked)))
             (update (list *t2-input-fields-update* slot value x))
             (projections (t2-input-state-update-projections lib x update))
             (definition (proof-proof-unfold proof (list *t2-input-state-state* update)))
             (literal (proof-step-first definition))
             (right (proof-term-at literal 2))
             (proposition (proof-proof-assume proof right t))
             (new-fields (t2-input-state-tests lib proposition))
             (other-fields (t2-input-state-renew-fields
                            lib (cddr old-fields) (cddr new-fields)
                            projections proof-for-changed-field))
             (joint (t2-power-join lib (append length-facts other-fields))))
          (proof-proof-transport proof joint definition))))))

(defun t2-input-state-state-writes (lib)
  (let ((x *library-x*) (y *library-y*) (z *library-z*))
    (proof-with-checked-results
        ((lib (t2-input-state-list-length lib))
         (proof (library-library-proof lib))
         (can-open (proof-proof-assume proof (list *t2-input-state-open-channels* y) t))
         (after-write (t2-input-state-updated-state lib 0 y (list :new-channel-table can-open)))
         (update (proof-proof-unfold proof
                                    (list (proof-sym "UPDATE-OPEN-INPUT-CHANNELS" "ACL2") y x)))
         (after-write (library-library-transport-argument lib after-write update 1))
         (claim (proof-step-first after-write))
         (lib (library-library-lemma lib "STATE-P1-INPUT-TABLE-WRITE" claim after-write
                                     (cdr (proof-step-clause after-write))))
         (proof (library-library-proof lib))
         (globals-before (list *t2-input-state-global-table* x))
         (globals-after (list *t2-input-fields-add-pair* y z globals-before))
         (symbolic-key (proof-proof-assume proof (list *t2-input-state-symbolp* y) t))
         (changed (t2-input-state-updated-state
                   lib 2 globals-after
                   (list :global-change globals-before globals-after symbolic-key lib)))
         (update (proof-proof-unfold proof (list *t2-input-fields-put-global* y z x)))
         (literal (proof-step-first update))
         (right (proof-term-at literal 2))
         (opened (proof-proof-unfold proof right))
         (update (proof-proof-chain proof update (list opened)))
         (changed (library-library-transport-argument lib changed update 1))
         (claim (proof-step-first changed)))
      (library-library-lemma lib "STATE-P1-GLOBAL-WRITE" claim changed
                             (cdr (proof-step-clause changed))))))

(defun t2-input-state-print-discharge (lib step guards assumed)
  (declare (xargs :measure (acl2-count guards)))
  (if (endp guards)
      step
    (proof-with-checked-results
        ((original (proof-step-first assumed))
         (guard (car guards))
         (next
          (if (equal guard (proof-neg original))
              step
            (proof-with-checked-results
                ((needs (if (proof-is-call guard *proof-not*) (proof-term-at guard 1) guard))
                 (given (t2-input-state-closed-boolean lib needs nil)))
              (proof-proof-discharge (library-library-proof lib) step given)))))
      (t2-input-state-print-discharge lib next (cdr guards) assumed))))

(defun t2-input-state-keep-print-state-on-path (value tests lib initial assumed)
  (declare (ignore tests)
           (xargs :measure (acl2-count value)))
  (proof-with-checked-results
      ((literal (proof-step-first initial))
       (first-state (proof-term-at literal 1)))
    (cond
     ((equal value first-state) initial)
     ((not (and (consp value) (proof-is-call value *t2-input-fields-put-global*)))
      '(:failure "failure" ""))
     (t (proof-with-checked-results
            ((fields (proof-list-of-length (cdr value) 3))
             (prior (cadddr value))
             (previous (t2-input-state-keep-print-state-on-path prior nil lib initial assumed))
             (step (library-library-cite lib "STATE-P1-GLOBAL-WRITE"
                                         (list prior (car fields) (cadr fields))
                                         (list previous))))
          (t2-input-state-print-discharge lib step (cdr (proof-step-clause step)) assumed))))))

(defun t2-input-state-print-branches (n lib value template tests initial assumed)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t2-input-state-print-branches")
    (let ((proof (library-library-proof lib)))
      (cond
       ((proof-is-call value *proof-if*)
        (proof-with-checked-results
            ((branches (proof-list-of-length (cdr value) 3))
             (test (car branches))
             (yes (t2-input-state-print-branches
                   (1- n) lib (cadr branches) template (append tests (list (list test t)))
                   initial assumed))
             (no (t2-input-state-print-branches
                  (1- n) lib (caddr branches) template (append tests (list (list test nil)))
                  initial assumed))
             (true-equality (proof-proof-if-true proof value))
             (true-equality (proof-proof-symmetric proof true-equality))
             (yes (proof-proof-rewrite-result proof yes true-equality template *proof-result*))
             (false-equality (proof-proof-if-false proof value))
             (false-equality (proof-proof-symmetric proof false-equality))
             (no (proof-proof-rewrite-result proof no false-equality template *proof-result*)))
          (proof-proof-cases proof test yes no)))
       ((and (proof-compound value) (not (consp value))) '(:failure "failure" ""))
       ((and (proof-compound value) (proof-compound (car value)))
        (proof-with-checked-results
            ((equality (proof-proof-beta proof value))
             (literal (proof-step-first equality))
             (right (proof-term-at literal 2))
             (opened (t2-input-state-print-branches
                      (1- n) lib right template tests initial assumed))
             (reversed (proof-proof-symmetric proof equality)))
          (proof-proof-rewrite-result proof opened reversed template *proof-result*)))
       (t (proof-with-checked-results
              ((step (t2-input-state-keep-print-state-on-path value tests lib initial assumed))
               (claim (proof-step-first step))
               (target (proof-subst template (list (cons *proof-result* value)))))
            (if (equal claim target) step '(:failure "failure" ""))))))))

(defun t2-input-state-keep-print-state (lib)
  (let ((proof (library-library-proof lib))
        (x *library-x*))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof (list *t2-input-state-state* x) t))
         (oracle (t2-input-state-instantiate lib "STATE-P1-READ-ACL2-ORACLE" "STATE" (list x)))
         (initial (t2-arithmetic-arithmetic-modus-ponens lib oracle assumed))
         (literal (proof-step-first initial))
         (state-term (proof-term-at literal 1))
         (read-call (proof-term-at state-term 2)))
      (if (not (equal read-call (list *t2-input-fields-read-oracle* x)))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof (list *t2-input-fields-print-updates* x)))
             (literal (proof-step-first opened))
             (right (proof-term-at literal 2))
             (bindings (t2-input-fields-bindings lib right))
             (opened (proof-proof-chain proof opened (list bindings)))
             (literal (proof-step-first opened))
             (right (proof-term-at literal 2))
             (branches (t2-input-state-print-branches
                        1000000 lib right (list *t2-input-state-state* *proof-result*)
                        nil initial assumed))
             (step (library-library-transport-argument lib branches opened 1))
             (claim (proof-step-first step))
             (original (proof-step-first assumed)))
          (library-library-lemma lib "STATE-P1-PRINT-ORACLE" claim step
                                 (list (proof-neg original))))))))

(defun t2-input-state-build (lib)
  (proof-with-checked-results ((lib (t2-input-state-state-writes lib)))
    (t2-input-state-keep-print-state lib)))
