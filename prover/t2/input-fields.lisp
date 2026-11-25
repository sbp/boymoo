(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)
(logic)

(defconst *t2-input-fields-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *t2-input-fields-zp* (proof-sym "ZP" "ACL2"))
(defconst *t2-input-fields-update* (proof-sym "UPDATE-NTH" "ACL2"))
(defconst *t2-input-fields-channels* (proof-sym "OPEN-INPUT-CHANNELS" "ACL2"))
(defconst *t2-input-fields-put-global* (proof-sym "PUT-GLOBAL" "ACL2"))
(defconst *t2-input-fields-update-global* (proof-sym "UPDATE-GLOBAL-TABLE" "ACL2"))
(defconst *t2-input-fields-oracle-state* (proof-sym "UPDATE-ACL2-ORACLE" "ACL2"))
(defconst *t2-input-fields-read-oracle* (proof-sym "READ-ACL2-ORACLE" "ACL2"))
(defconst *t2-input-fields-print-updates* (proof-sym "IPRINT-ORACLE-UPDATES" "ACL2"))
(defconst *t2-input-fields-read-object* (proof-sym "READ-OBJECT" "ACL2"))
(defconst *t2-input-fields-nth* (proof-cl "NTH"))
(defconst *t2-input-fields-endp* (proof-cl "ENDP"))
(defconst *t2-input-fields-atom* (proof-cl "ATOM"))
(defconst *t2-input-fields-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *t2-input-fields-open-channel* (proof-sym "OPEN-INPUT-CHANNEL-P1" "ACL2"))
(defconst *t2-input-fields-open-any* (proof-sym "OPEN-INPUT-CHANNEL-ANY-P1" "ACL2"))
(defconst *t2-input-fields-type* (proof-sym "TYP" "ACL2"))
(defconst *t2-input-fields-add-pair* (proof-sym "ADD-PAIR" "ACL2"))

(defun t2-input-fields-left (equality)
  (proof-with-checked-results ((literal (proof-step-first equality)))
    (proof-term-at literal 1)))

(defun t2-input-fields-required-step (step)
  (if step
      step
    '(:failure "failure" "")))

(defun t2-input-fields-select (lib equality evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((term (proof-rewritten-term equality))
         (selected (proof-proof-select proof term evidence)))
      (proof-proof-chain proof equality (list selected)))))

(defun t2-input-fields-negated-value (lib equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((value (proof-rewritten-term equation)))
      (if (not (equal value *proof-false*))
          '(:failure "recipe-mismatch" "")
        (proof-with-checked-results
            ((not-nil (proof-proof-not-nil proof))
             (reverse (proof-proof-symmetric proof equation))
             (reduced (proof-proof-rewrite proof not-nil reverse '(1 1))))
          (proof-proof-tidy proof reduced))))))

(defun t2-input-fields-constant-zp (lib index)
  (let* ((proof (library-library-proof lib))
         (value (proof-quote index)))
    (proof-with-checked-results
        ((expanded (proof-proof-unfold proof (list *t2-input-fields-zp* value)))
         (integer (t2-arithmetic-arithmetic-type-of lib value nil))
         (opened (t2-input-fields-select lib expanded integer)))
      (cond ((equal index 0)
             (proof-with-checked-results ((zero (library-library-axiom lib "ZERO" nil)))
               (proof-proof-transport proof zero opened)))
            ((not (< 0 index)) '(:failure "recipe-mismatch" ""))
            (t
             (let ((positive (library-positive value)))
               (proof-with-checked-results
                   ((expanded (proof-proof-unfold proof (proof-neg positive)))
                    (evidence (t2-arithmetic-arithmetic-prove lib positive nil nil))
                    (reduced (t2-input-fields-select lib expanded evidence))
                    (equation (proof-proof-chain proof opened (list reduced))))
                 (t2-input-fields-negated-value lib equation))))))))

(defun t2-input-fields-end-condition (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((opened (proof-proof-unfold proof term)))
      (if (equal (car term) *t2-input-fields-endp*)
          (proof-with-checked-results
              ((body (proof-rewritten-term opened))
               (inner (proof-proof-unfold proof body)))
            (proof-proof-chain proof opened (list inner)))
        opened))))

(defun t2-input-fields-cons-projection-step (lib selector index result args)
  (let ((proof (library-library-proof lib))
        (first (car args))
        (tail (cadr args)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list selector (proof-quote index) result)))
         (cons-proof (proof-proof-fact proof "consp-cons"
                                      (list (list *library-x* first)
                                            (list *library-y* tail))))
         (body (proof-rewritten-term opened))
         (test (proof-term-at body 1))
         (end (t2-input-fields-end-condition lib test))
         (end-body (proof-rewritten-term end))
         (end-opened (proof-proof-unfold proof end-body))
         (end-selected (t2-input-fields-select lib end-opened cons-proof))
         (end (proof-proof-chain proof end (list end-selected)))
         (end-false (t2-input-fields-negated-value lib end))
         (opened (t2-input-fields-select lib opened end-false))
         (zp-proof (t2-input-fields-constant-zp lib index))
         (opened (t2-input-fields-select lib opened zp-proof)))
      (if (equal index 0)
          (proof-with-checked-results
              ((car-cons (library-library-axiom lib "CAR-CONS" args)))
            (proof-proof-chain proof opened (list car-cons)))
        (proof-with-checked-results
            ((body (proof-rewritten-term opened))
             (argument (proof-term-at body 1))
             (constant (t2-book-logic-constant lib argument))
             (constant (t2-input-fields-required-step constant))
             (opened (proof-proof-rewrite proof opened constant '(1 2 1)))
             (cdr-cons (library-library-axiom lib "CDR-CONS" args)))
          (proof-proof-rewrite proof opened cdr-cons '(1 2 2)))))))

(defun t2-input-fields-cons-projection (lib selector index result)
  (declare (xargs :measure (acl2-count result)))
  (if (not (and (consp result)
                (o< (acl2-count (caddr result)) (acl2-count result))
                (proof-is-call result *proof-cons*)))
      '(:failure "recipe-mismatch" "")
    (proof-with-checked-results
        ((args (proof-list-of-length (cdr result) 2))
         (step (t2-input-fields-cons-projection-step lib selector index result args)))
      (if (equal index 0)
          step
        (proof-with-checked-results
            ((part (t2-input-fields-cons-projection lib selector (1- index) (caddr result))))
          (proof-proof-chain (library-library-proof lib) step (list part)))))))

(defun t2-input-fields-rewrite-argument (proof term equation reduced index)
  (proof-with-checked-results
      ((equation (or equation (proof-proof-reflexive proof term))))
    (proof-proof-rewrite proof equation reduced (list 1 2 index))))

(mutual-recursion
 (defun t2-input-fields-bindings-visit (n lib term)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t2-input-fields-bindings"))
    ((not (proof-compound term)) nil)
    ((endp term) '(:failure "failure" ""))
    ((or (proof-compound (car term)) (proof-is-call term *termination-return-last*))
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((reduced (if (proof-compound (car term))
                         (proof-proof-beta proof term)
                       (proof-proof-unfold proof term)))
            (body (proof-rewritten-term reduced))
            (rest (t2-input-fields-bindings-visit (1- n) lib body)))
         (proof-proof-chain proof reduced (list rest)))))
    ((proof-is-call term *proof-quote*) nil)
    (t (t2-input-fields-bindings-arguments (1- n) lib term (cdr term) 1 nil))))

 (defun t2-input-fields-bindings-arguments (n lib term args index equation)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp args) equation)
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t2-input-fields-bindings"))
    (t
     (proof-with-checked-results
         ((reduced (t2-input-fields-bindings-visit (1- n) lib (car args)))
          (equation (if reduced
                        (t2-input-fields-rewrite-argument
                         (library-library-proof lib) term equation reduced index)
                      equation)))
       (t2-input-fields-bindings-arguments (1- n) lib term (cdr args) (1+ index) equation))))))

(defun t2-input-fields-bindings (lib term)
  (t2-input-fields-bindings-visit 1000000 lib term))

(defun t2-input-fields-result-state (channel input)
  (list *t2-input-fields-mv-nth* (proof-quote 2)
        (list *t2-input-fields-read-object* channel input)))

(mutual-recursion
 (defun t2-input-fields-project-cons-fields (lib term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
    ((not (o< (* 2 (acl2-count (cdr term))) (1+ (* 2 (acl2-count term)))))
     '(:failure "failure" ""))
    (t
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((equation (t2-input-fields-project-cons-arguments
                       lib term (cdr term) 1 nil))
            (current (if equation (proof-rewritten-term equation) term))
            (operator (proof-term-at current 0)))
         (if (member-equal operator (list *t2-book-logic-car* *t2-book-logic-cdr*))
             (proof-with-checked-results ((object (proof-term-at current 1)))
               (if (proof-is-call object *proof-cons*)
                   (proof-with-checked-results
                       ((selector (library-library-axiom
                                   lib
                                   (if (equal operator *t2-book-logic-car*)
                                       "CAR-CONS" "CDR-CONS")
                                   (cdr object))))
                     (if equation
                         (proof-proof-chain proof equation (list selector))
                       selector))
                 equation))
           equation))))))

 (defun t2-input-fields-project-cons-arguments (lib term args index equation)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (not (and (consp args)
                 (o< (1+ (* 2 (acl2-count (car args)))) (* 2 (acl2-count args)))
                 (o< (* 2 (acl2-count (cdr args))) (* 2 (acl2-count args)))))
       equation
     (proof-with-checked-results
         ((selected (t2-input-fields-project-cons-fields lib (car args)))
          (equation (if selected
                        (t2-input-fields-rewrite-argument
                         (library-library-proof lib) term equation selected index)
                      equation)))
       (t2-input-fields-project-cons-arguments lib term (cdr args) (1+ index) equation)))))

(defun t2-input-fields-assoc-write (lib query key value table)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact
                proof (proof-sym "ASSOC-ADD-PAIR" "ACL2")
                (seq-zip '(("sym" "ACL2" "SYM1") ("sym" "ACL2" "SYM2")
                          ("sym" "ACL2" "VAL") ("sym" "ACL2" "ALIST"))
                        (list query key value table))))
         (left (t2-input-fields-left fact))
         (left (t2-input-fields-bindings lib left))
         (right (proof-rewritten-term fact))
         (right (t2-input-fields-bindings lib right))
         (left (t2-input-fields-required-step left))
         (rewritten (proof-proof-rewrite proof fact left '(1 1))))
      (proof-proof-chain proof rewritten (list right)))))

(defun t2-input-fields-lookup (lib query channel input reads-value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((slot (library-library-cite lib "READ-OBJECT-INPUT-SLOT"
                                     (list channel input) nil))
         (body (proof-rewritten-term slot))
         (test (proof-term-at body 1))
         (assumption (proof-proof-assume proof test reads-value))
         (new-fields (t2-input-fields-select lib slot assumption))
         (fields (t2-input-fields-left new-fields))
         (table-lookup (list *t2-input-fields-assoc* query fields))
         (identity (proof-proof-reflexive proof table-lookup))
         (rewritten (proof-proof-rewrite proof identity new-fields '(1 2 2))))
      (if (not reads-value)
          (list rewritten test)
        (proof-with-checked-results
            ((updated (proof-rewritten-term new-fields))
             (args (proof-list-of-length (cdr updated) 3))
             (association (t2-input-fields-assoc-write lib query
                                                       (car args) (cadr args) (caddr args)))
             (step (proof-proof-chain proof rewritten (list association))))
          (list step test))))))

(defun t2-input-fields-type-check (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (body (proof-rewritten-term opened))
         (bindings (t2-input-fields-bindings lib body)))
      (proof-proof-chain proof opened (list bindings)))))

(defun t2-input-fields-replace-lookup (lib equation replacement)
  (proof-with-checked-results
      ((body (proof-rewritten-term equation))
       (old (t2-input-fields-left replacement)))
    (proof-proof-rewrite-result (library-library-proof lib) equation replacement
                                (proof-eq *proof-false* body) old)))

(defun t2-input-fields-write-slot (lib index test label)
  (let* ((proof (library-library-proof lib))
         (updated (list *t2-input-fields-update* index *library-x* *library-y*)))
    (proof-with-checked-results
        ((composed (library-library-cite lib "INPUT-SLOT" (list updated) nil))
         (opened (proof-proof-unfold proof updated))
         (expanded (t2-input-fields-select lib opened test))
         (composed (proof-proof-rewrite proof composed expanded '(1 2 1)))
         (body (proof-rewritten-term expanded))
         (first (library-library-axiom lib "CAR-CONS" (cdr body)))
         (composed (proof-proof-chain proof composed (list first))))
      (if (equal index *proof-zero*)
          (proof-with-checked-results ((claim (proof-step-first composed)))
            (library-library-lemma lib label claim composed nil))
        (proof-with-checked-results
            ((slot (library-library-cite lib "INPUT-SLOT" (list *library-y*) nil))
             (reversed (proof-proof-symmetric proof slot))
             (composed (proof-proof-chain proof composed (list reversed)))
             (claim (proof-step-first composed)))
          (library-library-lemma lib label claim composed
                                 (list (list *t2-input-fields-zp* *library-z*))))))))

(defun t2-input-fields-input-slot (lib)
  (let ((proof (library-library-proof lib))
        (branch (list *proof-consp* *library-x*))
        (other (list *t2-input-fields-zp* *library-z*)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof
                                    (list *t2-input-fields-nth* *proof-zero* *library-x*)))
         (body (proof-rewritten-term opened))
         (test (proof-term-at body 1))
         (end (t2-input-fields-end-condition lib test))
         (end-body (proof-rewritten-term end))
         (end-opened (proof-proof-unfold proof end-body))
         (assumption (proof-proof-assume proof branch t))
         (yes (t2-input-fields-select lib end-opened assumption))
         (yes (proof-proof-chain proof end (list yes)))
         (yes (t2-input-fields-negated-value lib yes))
         (yes (t2-input-fields-select lib opened yes))
         (zero (t2-input-fields-constant-zp lib 0))
         (yes (t2-input-fields-select lib yes zero))
         (assumption (proof-proof-assume proof branch nil))
         (no (proof-proof-transport proof assumption end))
         (no (t2-input-fields-select lib opened no))
         (completion (library-library-axiom lib "COMPLETION-OF-CAR" (list *library-x*)))
         (empty (t2-input-fields-select lib completion assumption))
         (empty (proof-proof-symmetric proof empty))
         (no (proof-proof-chain proof no (list empty)))
         (channels (proof-proof-unfold proof (list *t2-input-fields-channels* *library-x*)))
         (first (proof-proof-cases proof branch yes no))
         (direct (proof-proof-chain proof channels (list first)))
         (claim (proof-step-first direct))
         (lib (library-library-lemma lib "INPUT-SLOT" claim direct nil))
         (zero (t2-input-fields-constant-zp lib 0))
         (nonzero (proof-proof-assume (library-library-proof lib) other nil))
         (lib (t2-input-fields-write-slot lib *proof-zero* zero "WRITE-INPUT-SLOT")))
      (t2-input-fields-write-slot lib *library-z* nonzero "WRITE-OTHER-SLOT"))))

(defun t2-input-fields-unchanged-slot (lib equation label index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((body (proof-rewritten-term equation))
         (parts (proof-list-of-length body 4))
         (test (t2-input-fields-constant-zp lib index))
         (unchanged (library-library-cite lib "WRITE-OTHER-SLOT"
                                          (list (caddr parts) (cadddr parts) (cadr parts))
                                          (list test)))
         (reverse (proof-proof-symmetric proof equation))
         (unchanged (proof-proof-rewrite proof unchanged reverse '(1 1 1)))
         (claim (proof-step-first unchanged)))
      (library-library-lemma lib label claim unchanged nil))))

(defun t2-input-fields-other-updates-leaf (n value tests lib projected)
  (declare (xargs :measure (nfix n))
           (ignore tests))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t2-input-fields-other-updates-leaf"))
   ((proof-is-call value *t2-input-fields-put-global*)
    (proof-with-checked-results
        ((outer (library-library-cite lib "INPUT-SLOT-GLOBAL-WRITE" (cdr value) nil))
         (inner (t2-input-fields-other-updates-leaf (1- n) (car (last value))
                                                    nil lib projected)))
      (proof-proof-chain (library-library-proof lib) outer (list inner))))
   ((equal value projected)
    (library-library-cite lib "INPUT-SLOT-ORACLE-READ" (list *library-x*) nil))
   (t '(:failure "failure" ""))))

(defun t2-input-fields-other-updates-by-value (n lib value template tests projected)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t2-input-fields-other-updates-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (t2-input-fields-other-updates-by-value
                 (1- n) lib (cadr branches) template
                 (append tests (list (list (car branches) t))) projected))
           (no (t2-input-fields-other-updates-by-value
                (1- n) lib (caddr branches) template
                (append tests (list (list (car branches) nil))) projected)))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equation (proof-proof-beta proof value))
           (body (proof-rewritten-term equation))
           (opened (t2-input-fields-other-updates-by-value
                    (1- n) lib body template tests projected))
           (reverse (proof-proof-symmetric proof equation)))
        (proof-proof-rewrite-result proof opened reverse template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (t2-input-fields-other-updates-leaf 1000000 value tests lib projected))
           (literal (proof-step-first step))
           (expected (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal expected)
            step
          '(:failure "failure" "")))))))

(defun t2-input-fields-other-updates (lib)
  (let* ((proof (library-library-proof lib))
         (oracle-result (list *t2-input-fields-read-oracle* *library-x*))
         (projected (list *t2-input-fields-mv-nth* (proof-quote 2) oracle-result))
         (claim (proof-eq (list *t2-input-fields-channels* *proof-result*)
                          (list *t2-input-fields-channels* *library-x*))))
    (proof-with-checked-results
        ((global (proof-proof-unfold proof (list *t2-input-fields-put-global*
                                                 *library-x* *library-y* *library-z*)))
         (global-body (proof-rewritten-term global))
         (global-inner (proof-proof-unfold proof global-body))
         (global (proof-proof-chain proof global (list global-inner)))
         (oracle (proof-proof-unfold proof (list *t2-input-fields-oracle-state*
                                                 *library-x* *library-y*)))
         (lib (t2-input-fields-unchanged-slot lib oracle "INPUT-SLOT-ORACLE-WRITE" 4))
         (lib (t2-input-fields-unchanged-slot lib global "INPUT-SLOT-GLOBAL-WRITE" 2)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((equation (proof-proof-unfold proof oracle-result))
             (identity (proof-proof-reflexive proof projected))
             (selected (proof-proof-rewrite proof identity equation '(1 2 2)))
             (body (proof-rewritten-term equation))
             (part (t2-input-fields-cons-projection lib *t2-input-fields-mv-nth* 2 body))
             (selected (proof-proof-chain proof selected (list part)))
             (updated (proof-rewritten-term selected))
             (unchanged (library-library-cite lib "INPUT-SLOT-ORACLE-WRITE" (cdr updated) nil))
             (reverse (proof-proof-symmetric proof selected))
             (unchanged (proof-proof-rewrite proof unchanged reverse '(1 1 1)))
             (literal (proof-step-first unchanged))
             (lib (library-library-lemma lib "INPUT-SLOT-ORACLE-READ" literal unchanged nil)))
          (let ((proof (library-library-proof lib)))
            (proof-with-checked-results
                ((updates (proof-proof-unfold
                           proof (list *t2-input-fields-print-updates* *library-x*)))
                 (body (proof-rewritten-term updates))
                 (reduced (t2-input-fields-bindings lib body))
                 (updates (proof-proof-chain proof updates (list reduced)))
                 (body (proof-rewritten-term updates))
                 (step (t2-input-fields-other-updates-by-value
                        1000000 lib body claim nil projected))
                 (reverse (proof-proof-symmetric proof updates))
                 (step (proof-proof-rewrite proof step reverse '(1 1 1)))
                 (literal (proof-step-first step)))
              (library-library-lemma lib "INPUT-SLOT-PRINT-ORACLE" literal step nil))))))))

(defun t2-input-fields-read-projection (lib chosen index projection)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((identity (proof-proof-reflexive proof projection))
         (answer (proof-proof-rewrite proof identity chosen '(1 2 2)))
         (body (proof-rewritten-term chosen))
         (selected (t2-input-fields-cons-projection lib *t2-input-fields-mv-nth* index body)))
      (proof-proof-chain proof answer (list selected)))))

(defun t2-input-fields-project-read-branch (lib opened preserved test holds flag state-projection)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((branch (proof-proof-assume proof test holds))
         (chosen (t2-input-fields-select lib opened branch))
         (flag-answer (t2-input-fields-read-projection lib chosen 0 flag))
         (negated (proof-proof-unfold proof (proof-neg test)))
         (expected (t2-input-fields-select lib negated branch))
         (actual-value (proof-rewritten-term flag-answer))
         (expected-value (proof-rewritten-term expected))
         (evaluation (t2-arithmetic-arithmetic-prove
                      lib (list *t2-book-logic-iff* actual-value expected-value)
                      nil (list *t2-book-logic-iff*)))
         (reverse (proof-proof-symmetric proof flag-answer))
         (evaluation (proof-proof-rewrite proof evaluation reverse '(1 1)))
         (reverse (proof-proof-symmetric proof expected))
         (evaluation (proof-proof-rewrite proof evaluation reverse '(1 2)))
         (flag-proof (proof-proof-tidy proof evaluation))
         (answer (t2-input-fields-read-projection lib chosen 2 state-projection))
         (projection
          (if holds
              (proof-with-checked-results
                  ((updated (proof-rewritten-term answer))
                   (written (proof-proof-unfold proof updated))
                   (body (proof-rewritten-term written))
                   (args (proof-list-of-length (cddr body) 2))
                   (projection (library-library-cite lib "WRITE-INPUT-SLOT" args nil))
                   (reverse (proof-proof-symmetric proof written)))
                (proof-proof-rewrite proof projection reverse '(1 1 1)))
            preserved))
         (reverse (proof-proof-symmetric proof answer))
         (projection (proof-proof-rewrite proof projection reverse '(1 1 1)))
         (field-proof (proof-proof-tidy proof projection)))
      (list flag-proof field-proof))))

(defun t2-input-fields-project-read (lib)
  (let* ((proof (library-library-proof lib))
         (call (list *t2-input-fields-read-object* *library-x* *library-y*))
         (flag (list *t2-input-fields-mv-nth* *proof-zero* call))
         (state-projection (t2-input-fields-result-state *library-x* *library-y*)))
    (proof-with-checked-results
        ((opened (t2-input-fields-type-check lib call))
         (preserved (library-library-cite lib "INPUT-SLOT-PRINT-ORACLE" (list *library-y*) nil))
         (opened (t2-input-fields-replace-lookup lib opened preserved))
         (body (proof-rewritten-term opened))
         (test (proof-term-at body 1))
         (yes (t2-input-fields-project-read-branch lib opened preserved test t flag state-projection))
         (no (t2-input-fields-project-read-branch lib opened preserved test nil flag state-projection))
         (flagged (proof-proof-cases proof test (car yes) (car no)))
         (lib (library-library-lemma lib "READ-OBJECT-FLAG"
                                     (list *t2-book-logic-iff* flag (proof-neg test))
                                     flagged nil))
         (yes-value (proof-rewritten-term (cadr yes)))
         (no-value (proof-rewritten-term (cadr no))))
      (let ((proof (library-library-proof lib))
            (merged (proof-ite test yes-value no-value)))
        (proof-with-checked-results
            ((yes-test (proof-proof-if-true proof merged))
             (yes (library-library-transport-argument lib (cadr yes) yes-test 2))
             (no-test (proof-proof-if-false proof merged))
             (no (library-library-transport-argument lib (cadr no) no-test 2))
             (step (proof-proof-cases proof test yes no))
             (claim (proof-step-first step)))
          (library-library-lemma lib "READ-OBJECT-INPUT-SLOT" claim step nil))))))

(defun t2-input-fields-preserve-channel-type (lib)
  (let* ((proof (library-library-proof lib))
         (original (list *t2-input-fields-open-channel* *library-x*
                         *t2-input-fields-type* *library-y*))
         (updated (list *t2-input-fields-open-channel* *library-x* *t2-input-fields-type*
                        (t2-input-fields-result-state *library-z* *library-y*)))
         (identical (proof-eq *library-x* *library-z*)))
    (proof-with-checked-results
        ((old-equation (t2-input-fields-type-check lib original))
         (old-proof (proof-proof-assume proof original t))
         (old-proof (proof-proof-rewrite proof old-proof old-equation '(1)))
         (old-proof (proof-proof-tidy proof old-proof))
         (parts (t2-arithmetic-arithmetic-conjunct lib old-proof))
         (opened (t2-input-fields-type-check lib updated))
         (unchanged (t2-input-fields-lookup lib *library-x* *library-z* *library-y* nil))
         (no-read (t2-input-fields-replace-lookup lib opened (car unchanged)))
         (no-read (proof-proof-transport proof old-proof no-read))
         (changed (t2-input-fields-lookup lib *library-x* *library-z* *library-y* t))
         (different (proof-proof-assume proof identical nil))
         (other-key (t2-input-fields-select lib (car changed) different))
         (other-case (t2-input-fields-replace-lookup lib opened other-key))
         (other-case (proof-proof-transport proof old-proof other-case))
         (same (proof-proof-assume proof identical t))
         (same-key (t2-input-fields-select lib (car changed) same))
         (branch (t2-input-fields-replace-lookup lib opened same-key))
         (new-pair (proof-rewritten-term same-key))
         (explicit (proof-proof-fact proof "consp-cons"
                                     (seq-zip (list *library-x* *library-y*) (cdr new-pair))))
         (facts (t2-tactics-ruler-facts-init lib nil nil))
         (facts (t2-tactics-ruler-facts-learn facts explicit))
         (known (t2-tactics-ruler-facts-require facts new-pair))
         (branch (t2-input-fields-select lib branch (car known)))
         (body (proof-rewritten-term branch))
         (fields (t2-input-fields-project-cons-fields lib body))
         (branch (proof-proof-chain proof branch (list fields)))
         (reverse (proof-proof-symmetric proof same))
         (body (proof-rewritten-term branch))
         (branch (proof-proof-rewrite-result proof branch reverse
                                             (proof-eq *proof-false* body) *library-z*))
         (same-case (proof-proof-transport proof (cadr parts) branch))
         (read-case (proof-proof-cases proof identical same-case other-case))
         (step (proof-proof-cases proof (cadr unchanged) read-case no-read))
         (completed (t2-power-implication lib original step))
         (claim (proof-step-first completed)))
      (library-library-lemma lib "READ-OBJECT-CHANNEL-TYPE" claim completed nil))))

(defun t2-input-fields-any-type-holds (lib tests evidence)
  (declare (xargs :measure (acl2-count tests)))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((literal (proof-step-first evidence)))
      (cond
       ((equal tests literal) evidence)
       ((integerp tests) '(:failure "failure" ""))
       ((not (and (consp tests) (o< (acl2-count (cadddr tests)) (acl2-count tests))))
        (proof-list-of-length (cdr tests) 3))
       (t
        (proof-with-checked-results ((parts (proof-list-of-length (cdr tests) 3)))
          (let ((branch (car parts)))
            (cond
             ((not (equal branch (cadr parts))) '(:failure "failure" ""))
             ((equal branch literal)
              (proof-with-checked-results ((selected (proof-proof-select proof tests evidence)))
                (proof-proof-transport proof evidence selected)))
             (t
              (proof-with-checked-results
                  ((assumed (proof-proof-assume proof branch t))
                   (chosen (proof-proof-if-true proof tests))
                   (present (proof-proof-transport proof assumed chosen))
                   (absent (t2-input-fields-any-type-holds lib (cadddr tests) evidence))
                   (chosen (proof-proof-if-false proof tests))
                   (absent (proof-proof-transport proof absent chosen)))
                (proof-proof-cases proof branch present absent)))))))))))

(defun t2-input-fields-preserve-any-channel-by-type (n step lib written)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t2-input-fields-preserve-any-channel-by-type")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results ((term (proof-step-first step)))
        (if (proof-is-call term *t2-input-fields-open-channel*)
            (proof-with-checked-results
                ((type (proof-term-at term 2))
                 (rule (proof-proof-fact proof (proof-sym "SELF-READ-OBJECT-CHANNEL-TYPE" "ACL2")
                                         (list (list *t2-input-fields-type* type))))
                 (present (t2-arithmetic-arithmetic-modus-ponens lib rule step))
                 (tests (proof-rewritten-term written))
                 (present (t2-input-fields-any-type-holds lib tests present)))
              (proof-proof-transport proof present written))
          (proof-with-checked-results
              ((branch (proof-term-at term 1))
               (assumed (proof-proof-assume proof branch t))
               (yes (t2-input-fields-preserve-any-channel-by-type (1- n) assumed lib written))
               (denied (proof-proof-assume proof branch nil))
               (next (proof-proof-prove-if proof step denied))
               (no (t2-input-fields-preserve-any-channel-by-type (1- n) next lib written)))
            (proof-proof-cases proof branch yes no)))))))

(defun t2-input-fields-preserve-any-channel (lib)
  (let* ((proof (library-library-proof lib))
         (original (list *t2-input-fields-open-any* *library-x* *library-y*))
         (updated (list *t2-input-fields-open-any* *library-x*
                        (t2-input-fields-result-state *library-z* *library-y*))))
    (proof-with-checked-results
        ((written (proof-proof-unfold proof updated))
         (original-proof (proof-proof-assume proof original t))
         (opened (proof-proof-unfold proof original))
         (by-read-type (proof-proof-rewrite proof original-proof opened '(1)))
         (result (t2-input-fields-preserve-any-channel-by-type 1000000 by-read-type lib written))
         (step (t2-power-implication lib original result))
         (claim (proof-step-first step)))
      (library-library-lemma lib "READ-OBJECT-ANY-CHANNEL-TYPE" claim step nil))))

(defun t2-input-fields-shorter-contents (lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((found (t2-input-fields-lookup lib *library-x* *library-x* *library-y* t))
         (identity (proof-proof-reflexive proof *library-x*))
         (association (t2-input-fields-select lib (car found) identity))
         (table-lookup (t2-input-fields-left association))
         (new-contents (list *t2-book-logic-cdr* (list *t2-book-logic-cdr* table-lookup)))
         (identity (proof-proof-reflexive proof new-contents))
         (contents (proof-proof-rewrite proof identity association '(1 2 1 1)))
         (updated (proof-rewritten-term contents))
         (fields (t2-input-fields-project-cons-fields lib updated))
         (contents (proof-proof-chain proof contents (list fields)))
         (test (proof-term-at (cadr found) 1))
         (assumption (proof-proof-assume proof (cadr found) t))
         (shorter (library-library-cite lib "LEN-CDR-LESS" (list test) (list assumption)))
         (reverse (proof-proof-symmetric proof contents))
         (shorter (proof-proof-rewrite proof shorter reverse '(1 1 1)))
         (step (t2-power-implication lib (cadr found) shorter))
         (claim (proof-step-first step)))
      (library-library-lemma lib "READ-OBJECT-SHORTER-CONTENTS" claim step nil))))

(defun t2-input-fields-build (lib)
  (proof-with-checked-results
      ((lib (t2-input-fields-input-slot lib))
       (lib (t2-input-fields-other-updates lib))
       (lib (t2-input-fields-project-read lib))
       (lib (t2-input-fields-preserve-channel-type lib))
       (lib (t2-input-fields-preserve-any-channel lib)))
    (t2-input-fields-shorter-contents lib)))
