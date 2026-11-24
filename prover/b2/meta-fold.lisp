(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-meta-fold-bagdiff* (proof-sym "BAGDIFF" "ACL2"))
(defconst *b2-meta-fold-formal-zero* (proof-sym "FORMAL-SOME-ZEROP" "ACL2"))
(defconst *b2-meta-fold-tree* (proof-sym "BINARY-OP_TREE" "ACL2"))
(defconst *b2-meta-fold-simple-tree* (proof-sym "BINARY-OP_TREE-SIMPLE" "ACL2"))
(defconst *b2-meta-fold-u* (proof-sym "U" "ACL2"))

(defun b2-meta-fold-arithmetic-fold-lib (self) (nth 1 self))
(defun b2-meta-fold-arithmetic-fold-evaluator (self) (nth 2 self))
(defun b2-meta-fold-arithmetic-fold-operation (self) (nth 3 self))
(defun b2-meta-fold-arithmetic-fold-simple (self) (nth 4 self))
(defun b2-meta-fold-arithmetic-fold-constant (self) (nth 5 self))
(defun b2-meta-fold-arithmetic-fold-operator-name (self) (nth 6 self))
(defun b2-meta-fold-arithmetic-fold-label (self) (nth 7 self))
(defun b2-meta-fold-arithmetic-fold-fold (self) (nth 8 self))
(defun b2-meta-fold-arithmetic-fold-dispatch (self) (nth 9 self))

(defun b2-meta-fold-arithmetic-fold-with-lib (self lib)
  (list :b2-arithmetic-fold lib
        (b2-meta-fold-arithmetic-fold-evaluator self)
        (b2-meta-fold-arithmetic-fold-operation self)
        (b2-meta-fold-arithmetic-fold-simple self)
        (b2-meta-fold-arithmetic-fold-constant self)
        (b2-meta-fold-arithmetic-fold-operator-name self)
        (b2-meta-fold-arithmetic-fold-label self)
        (b2-meta-fold-arithmetic-fold-fold self)
        (b2-meta-fold-arithmetic-fold-dispatch self)))

(defmacro b2-meta-fold-normalize (lib term evidence unfold branches)
  `(b2-tactics-tactics-normalize ,lib ,term ,evidence ,unfold nil 1500 ,branches))

(defmacro b2-meta-fold-solve (lib goal evidence unfold rules branches)
  `(b2-tactics-tactics-solve ,lib ,goal ,evidence ,unfold ,rules 0 ,branches))

(defun b2-meta-fold-first (step)
  (if (null step)
      '(:failure "failure" "")
    (proof-step-first step)))

(defun b2-meta-fold-first-at (step index)
  (proof-with-checked-results ((literal (b2-meta-fold-first step)))
    (proof-term-at literal index)))

(defun b2-meta-fold-decimal-digit-p (char)
  (and (characterp char) (<= (char-code #\0) (char-code char))
       (<= (char-code char) (char-code #\9))))

(defun b2-meta-fold-decimal-digits (chars value digits)
  (cond ((endp chars) (cons value digits))
        ((b2-meta-fold-decimal-digit-p (car chars))
         (b2-meta-fold-decimal-digits
          (cdr chars) (+ (* 10 value) (- (char-code (car chars)) (char-code #\0)))
          (1+ digits)))
        ((and (eql (car chars) #\_) (posp digits)
              (b2-meta-fold-decimal-digit-p (cadr chars)))
         (b2-meta-fold-decimal-digits (cdr chars) value digits))
        (t nil)))

(defun b2-meta-fold-constraint-index (text)
  (let* ((space (coerce (list #\Space #\Tab #\Newline (code-char 11)
                             (code-char 12) #\Return) 'string))
         (chars (coerce (text-strip text space) 'list))
         (negative (eql (car chars) #\-))
         (digits (if (or negative (eql (car chars) #\+)) (cdr chars) chars))
         (parsed (b2-meta-fold-decimal-digits digits 0 0)))
    (cond ((or (null parsed) (zp (cdr parsed)))
           '(:failure "inapplicable" ""))
          ((< 4300 (cdr parsed))
           '(:failure "inapplicable" ""))
          (negative (- (car parsed)))
          (t (car parsed)))))

(defun b2-meta-fold-arithmetic-fold-constraint-tag (clause)
  (proof-with-checked-results
      ((first (proof-term-at clause 0))
       (test (proof-term-at first 1))
       (comparison (proof-term-at test 2))
       (quoted (proof-term-at comparison 2)))
    (proof-term-at quoted 1)))

(defun b2-meta-fold-arithmetic-fold-init-dispatch-entry (entry prefix dispatch)
  (let ((name (car entry)))
    (proof-with-checked-results ((kind (proof-term-at name 0)))
      (if (not (equal kind "sym"))
          dispatch
        (proof-with-checked-results ((text (proof-term-at name 2)))
          (cond
           ((integerp text)
            '(:failure "failure" ""))
           ((not (stringp text))
            '(:failure "failure" ""))
           ((not (text-starts-with text prefix)) dispatch)
           (t
            (proof-with-checked-results
                ((index (b2-meta-fold-constraint-index (seq-slice text (length prefix) :none))))
              (if (or (= index 2) (<= 8 index))
                  (proof-with-checked-results
                      ((tag (b2-meta-fold-arithmetic-fold-constraint-tag (cdr entry))))
                    (table-put dispatch tag name))
                dispatch)))))))))

(defun b2-meta-fold-arithmetic-fold-init-dispatch (facts prefix dispatch)
  (if (or (endp facts) (failure-p dispatch))
      dispatch
    (b2-meta-fold-arithmetic-fold-init-dispatch
     (cdr facts) prefix (b2-meta-fold-arithmetic-fold-init-dispatch-entry (car facts) prefix dispatch))))

(defun b2-meta-fold-arithmetic-fold-init (lib evaluator operation simple)
  (proof-with-checked-results ((label (proof-term-at evaluator 2)))
    (cond ((integerp label) '(:failure "failure" ""))
          ((not (stringp label))
           '(:failure "failure" ""))
          (t
           (let* ((plus (equal operation *proof-plus*))
                  (constant (if plus *proof-zero* *proof-one*))
                  (operator-name (if plus "+" "*"))
                  (fold (proof-sym (concatenate 'string "B2-" label "-FOLD") "ACL2"))
                  (prefix (concatenate 'string label "-CONSTRAINT-"))
                  (facts (proof-proof-facts (library-library-proof lib))))
             (proof-with-checked-results
                 ((dispatch (b2-meta-fold-arithmetic-fold-init-dispatch facts prefix nil)))
               (list :b2-arithmetic-fold lib evaluator operation simple
                     constant operator-name label fold dispatch)))))))

(defun b2-meta-fold-arithmetic-fold-call (self elements env)
  (list (b2-meta-fold-arithmetic-fold-fold self) elements env))

(defun b2-meta-fold-arithmetic-fold-ev (self term env)
  (list (b2-meta-fold-arithmetic-fold-evaluator self) term env))

(defun b2-meta-fold-arithmetic-fold-tree (self elements)
  (let ((operator (proof-quote (b2-meta-fold-arithmetic-fold-operation self)))
        (constant (b2-meta-fold-arithmetic-fold-constant self)))
    (if (b2-meta-fold-arithmetic-fold-simple self)
        (list *b2-meta-fold-simple-tree* operator constant elements)
      (list *b2-meta-fold-tree* operator constant (proof-quote *b2-products-fix*) elements))))

(defun b2-meta-fold-arithmetic-fold-op (self a b)
  (list (b2-meta-fold-arithmetic-fold-operation self) a b))

(defun b2-meta-fold-arithmetic-fold-install (self)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (fold (b2-meta-fold-arithmetic-fold-fold self)))
    (if (assoc-equal fold (proof-proof-definitions proof))
        self
      (let* ((test (list *proof-consp* *library-x*))
             (head (b2-meta-fold-arithmetic-fold-ev self (list *library-car* *library-x*) *b2-bags-a*))
             (tail (b2-meta-fold-arithmetic-fold-call self (list *library-cdr* *library-x*) *b2-bags-a*))
             (body (proof-ite test (b2-meta-fold-arithmetic-fold-op self head tail)
                              (b2-meta-fold-arithmetic-fold-constant self)))
             (formals (list *library-x* *b2-bags-a*))
             (definitions (list (list fold formals body))))
        (proof-with-checked-results
            ((source (proof-line "define" (cons *termination-all* definitions)))
             (lib (library-library-with-entries
                   lib (append (library-library-entries lib) (list (list "define" fold nil source)))))
             (calls (termination-recursive-calls *termination-all* definitions))
             (result (b2-measures-prove-measure
                      lib definitions calls (list (cons fold (list *library-count* *library-x*))))))
          (let* ((lib (cdr result))
                 (entries (append (library-library-entries lib) (list (car result))))
                 (proof (proof-proof-add-definition (library-library-proof lib) fold formals body)))
            (b2-meta-fold-arithmetic-fold-with-lib
             self (library-library-with-proof (library-library-with-entries lib entries) proof))))))))

(defun b2-meta-fold-arithmetic-fold-fact-name (self kind)
  (concatenate 'string (b2-meta-fold-arithmetic-fold-label self) "-" kind))

(defun b2-meta-fold-arithmetic-fold-has-fact (self kind)
  (let* ((name (proof-sym (concatenate 'string "B2-" (b2-meta-fold-arithmetic-fold-fact-name self kind))
                         "ACL2"))
         (lib (b2-meta-fold-arithmetic-fold-lib self)))
    (if (assoc-equal name (proof-proof-facts (library-library-proof lib))) t nil)))

(defun b2-meta-fold-arithmetic-fold-fact (self kind prove elements)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (name (b2-meta-fold-arithmetic-fold-fact-name self kind))
         (symbol (proof-sym (concatenate 'string "B2-" name) "ACL2")))
    (proof-with-checked-results
        ((self (if (assoc-equal symbol (proof-proof-facts (library-library-proof lib)))
                   self
                 (proof-with-checked-results
                     ((step prove)
                      (added (b2-tactics-tactics-add-lemma lib name step :none)))
                   (b2-meta-fold-arithmetic-fold-with-lib self (cdr added)))))
         (step (proof-proof-fact (library-library-proof (b2-meta-fold-arithmetic-fold-lib self))
                                symbol elements)))
      (cons step self))))

(defun b2-meta-fold-arithmetic-fold-interpret (self term tag evidence)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (constraint (assoc-equal tag (b2-meta-fold-arithmetic-fold-dispatch self))))
    (if (null constraint)
        '(:failure "tactic-rejected" "")
      (proof-with-checked-results
          ((step (proof-proof-fact proof (cdr constraint) (list (list *library-x* term))))
           (condition (b2-meta-fold-first-at step 1))
           (premise (b2-meta-fold-solve lib condition evidence nil nil nil))
           (equation (proof-proof-modus-ponens proof step premise))
           (value (b2-meta-fold-first-at equation 2))
           (normalized (b2-meta-fold-normalize lib value evidence nil t)))
        (proof-proof-chain proof equation (list normalized))))))

(defun b2-meta-fold-arithmetic-fold-rewrite-operands-loop (rules equation proof index)
  (cond ((failure-p equation) equation)
        ((endp rules) (proof-proof-tidy proof equation))
        (t (b2-meta-fold-arithmetic-fold-rewrite-operands-loop
            (cdr rules)
            (if (car rules)
                (proof-proof-rewrite proof equation (car rules) (list 1 2 index))
              equation)
            proof (1+ index)))))

(defun b2-meta-fold-arithmetic-fold-rewrite-operands (self equation rules)
  (b2-meta-fold-arithmetic-fold-rewrite-operands-loop
   rules equation (library-library-proof (b2-meta-fold-arithmetic-fold-lib self)) 1))

(defun b2-meta-fold-arithmetic-fold-evaluate-arguments-rules (args tags self evidence reversed)
  (cond
   ((failure-p reversed) reversed)
   ((or (endp args) (endp tags)) (reverse reversed))
   (t
    (let ((rule (if (car tags)
                    (proof-with-checked-results ((term (proof-term-at (car args) 1)))
                      (b2-meta-fold-arithmetic-fold-interpret self term (car tags) evidence))
                  nil)))
      (b2-meta-fold-arithmetic-fold-evaluate-arguments-rules
       (cdr args) (cdr tags) self evidence (if (failure-p rule) rule (cons rule reversed)))))))

(defun b2-meta-fold-arithmetic-fold-evaluate-arguments (self equation tags evidence)
  (proof-with-checked-results ((right (b2-meta-fold-first-at equation 2)))
    (if (integerp right)
        (proof-term-at right 1)
      (proof-with-checked-results
          ((rules (b2-meta-fold-arithmetic-fold-evaluate-arguments-rules
                   (cdr right) tags self evidence nil)))
        (b2-meta-fold-arithmetic-fold-rewrite-operands self equation rules)))))

(defun b2-meta-fold-arithmetic-fold-identity (self term)
  (library-library-axiom
   (b2-meta-fold-arithmetic-fold-lib self)
   (if (equal (b2-meta-fold-arithmetic-fold-operation self) *proof-plus*)
       "UNICITY-OF-0"
     "UNICITY-OF-1")
   (list term)))

(defun b2-meta-fold-arithmetic-fold-right-identity (self term)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((commute (library-library-axiom
                   lib (concatenate 'string "COMMUTATIVITY-OF-" (b2-meta-fold-arithmetic-fold-operator-name self))
                   (list term (b2-meta-fold-arithmetic-fold-constant self))))
         (identity (b2-meta-fold-arithmetic-fold-identity self term)))
      (proof-proof-chain (library-library-proof lib) commute (list identity)))))

(defun b2-meta-fold-arithmetic-fold-fixed (self term numeric)
  (let ((proof (library-library-proof (b2-meta-fold-arithmetic-fold-lib self))))
    (proof-with-checked-results
        ((equation (proof-proof-unfold proof (list *b2-products-fix* term)))
         (body (b2-meta-fold-first-at equation 2))
         (selected (proof-proof-select proof body numeric)))
      (proof-proof-chain proof equation (list selected)))))

(defun b2-meta-fold-on-list-request (self formula variable advance extra)
  (proof-with-checked-results
      ((answer (b2-tactics-tactics-on-list
                (b2-meta-fold-arithmetic-fold-lib self) formula variable nil
                (and advance
                     (cons (car advance) (b2-meta-fold-arithmetic-fold-lib (cdr advance))))
                extra)))
    (car answer)))

(defun b2-meta-fold-on-list-complete (self formula variable base advance extra)
  (proof-with-checked-results
      ((answer (b2-tactics-tactics-on-list
                (b2-meta-fold-arithmetic-fold-lib self) formula variable
                (cons (car base) (b2-meta-fold-arithmetic-fold-lib (cdr base)))
                (cons (car advance) (b2-meta-fold-arithmetic-fold-lib (cdr advance)))
                extra))
       (step (car answer)))
    (cons step (b2-meta-fold-arithmetic-fold-with-lib self (cdr answer)))))

(defun b2-meta-fold-implication-request (lib condition goal)
  (proof-with-checked-results
      ((answer (b2-tactics-tactics-implication lib condition goal nil)))
    (car answer)))

(defun b2-meta-fold-implication-complete (lib condition goal step next-lib)
  (proof-with-checked-results
      ((answer (b2-tactics-tactics-implication lib condition goal (cons step next-lib)))
       (step (car answer)))
    (cons step (cdr answer))))

(defun b2-meta-fold-arithmetic-fold-number-proof (self call test)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib test))
         (cons-step (car signs))
         (selected (b2-meta-fold-normalize lib call (list cons-step) (list call) nil))
         (value (b2-meta-fold-first-at selected 2))
         (result (b2-products-numeric-closure lib value))
         (yes (library-library-transport-argument lib result selected 1))
         (no (b2-meta-fold-solve lib (list *library-numberp* call) (list (cadr signs))
                                 (list call) nil nil)))
      (proof-proof-cases (library-library-proof lib) test yes no))))

(defun b2-meta-fold-arithmetic-fold-number (self elements)
  (let* ((call (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*))
         (test (list *proof-consp* *library-x*))
         (bindings (list (list *library-x* elements))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "NUMBER")
        (b2-meta-fold-arithmetic-fold-fact self "NUMBER" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-number-proof self call test)))
        (b2-meta-fold-arithmetic-fold-fact self "NUMBER" step bindings)))))

(defun b2-meta-fold-arithmetic-fold-append-value-proof-base
    (atom self formula append-term folded-x unit)
  (proof-with-checked-results
      ((step (b2-meta-fold-solve (b2-meta-fold-arithmetic-fold-lib self) formula (list atom)
                                 (list append-term folded-x) (list unit) nil)))
    (cons step self)))

(defun b2-meta-fold-arithmetic-fold-append-value-proof-advance
    (cons-step induction self formula append-term folded-x folded-y)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((evidence (list cons-step))
         (eq-append (b2-meta-fold-normalize lib append-term evidence (list append-term) nil))
         (value (b2-meta-fold-first-at eq-append 2))
         (openers (list (b2-meta-fold-arithmetic-fold-call self value *b2-bags-a*) folded-x))
         (assoc (library-library-axiom
                 lib (concatenate 'string "ASSOCIATIVITY-OF-"
                                  (b2-meta-fold-arithmetic-fold-operator-name self))
                 (list (b2-meta-fold-arithmetic-fold-ev
                        self (list *library-car* *library-x*) *b2-bags-a*)
                       (b2-meta-fold-arithmetic-fold-call
                        self (list *library-cdr* *library-x*) *b2-bags-a*)
                       folded-y)))
         (step (b2-meta-fold-solve lib formula evidence openers (list eq-append induction assoc) nil)))
      (cons step self))))

(defun b2-meta-fold-arithmetic-fold-append-value-proof
    (self formula append-term folded-x folded-y)
  (proof-with-checked-results
      ((identity (b2-meta-fold-arithmetic-fold-identity self folded-y))
       (number (b2-meta-fold-arithmetic-fold-number self *library-y*))
       (self (cdr number))
       (fixed (b2-meta-fold-arithmetic-fold-fixed self folded-y (car number)))
       (unit (proof-proof-chain
              (library-library-proof (b2-meta-fold-arithmetic-fold-lib self))
              identity (list fixed)))
       (pending (b2-meta-fold-on-list-request self formula *library-x* nil nil))
       (advance (b2-meta-fold-arithmetic-fold-append-value-proof-advance
                 (cadddr pending) (nth 4 pending)
                 (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                 formula append-term folded-x folded-y))
       (pending-base (b2-meta-fold-on-list-request self formula *library-x* advance nil))
       (base (b2-meta-fold-arithmetic-fold-append-value-proof-base
              (cadddr pending-base)
              (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending-base))
              formula append-term folded-x unit)))
    (b2-meta-fold-on-list-complete self formula *library-x* base advance nil)))

(defun b2-meta-fold-arithmetic-fold-append-value (self xs ys)
  (let* ((append-term (list *b2-bags-append* *library-x* *library-y*))
         (left (b2-meta-fold-arithmetic-fold-call self append-term *b2-bags-a*))
         (folded-x (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*))
         (folded-y (b2-meta-fold-arithmetic-fold-call self *library-y* *b2-bags-a*))
         (formula (proof-eq left (b2-meta-fold-arithmetic-fold-op self folded-x folded-y)))
         (bindings (list (list *library-x* xs) (list *library-y* ys))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "APPEND")
        (b2-meta-fold-arithmetic-fold-fact self "APPEND" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-append-value-proof
                  self formula append-term folded-x folded-y)))
        (b2-meta-fold-arithmetic-fold-fact (cdr step) "APPEND" (car step) bindings)))))

(defun b2-meta-fold-arithmetic-fold-tree-value-proof-establish-evaluation
    (self syntax kind evidence)
  (proof-with-checked-results
      ((evaluation (b2-meta-fold-arithmetic-fold-interpret self syntax kind evidence)))
    (if (and (b2-meta-fold-arithmetic-fold-simple self)
             (equal kind (b2-meta-fold-arithmetic-fold-operation self)))
        (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
               (proof (library-library-proof lib)))
          (proof-with-checked-results
              ((part (b2-meta-fold-first-at evaluation 2))
               (reflexive (proof-proof-reflexive
                           proof (list *b2-products-fix*
                                       (b2-meta-fold-arithmetic-fold-ev self syntax *b2-bags-a*))))
               (lifted (proof-proof-rewrite proof reflexive evaluation '(1 2 1)))
               (numeric (b2-products-numeric-closure lib part))
               (fixed (b2-meta-fold-arithmetic-fold-fixed self part numeric))
               (operand (b2-algebra-fixed-operand lib part 2)))
            (proof-proof-chain proof lifted (list fixed operand))))
      evaluation)))

(defun b2-meta-fold-arithmetic-fold-tree-value-proof-establish
    (evidence kind induction self tree formula tail first second)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (simple (b2-meta-fold-arithmetic-fold-simple self))
         (constant (b2-meta-fold-arithmetic-fold-constant self))
         (operation (b2-meta-fold-arithmetic-fold-operation self))
         (plain (or (equal kind *b2-products-fix*) (null kind)))
         (two (and (not simple) (equal kind operation) (null induction))))
    (proof-with-checked-results
        ((equation (b2-meta-fold-normalize lib tree evidence (list tree) nil))
         (syntax (b2-meta-fold-first-at equation 2))
         (evaluation (and kind
                          (b2-meta-fold-arithmetic-fold-tree-value-proof-establish-evaluation
                           self syntax kind evidence)))
         (fixed (and (equal kind *proof-quote*) simple
                     (proof-with-checked-results
                         ((number (b2-meta-fold-solve lib (list *library-numberp* constant)
                                                      nil nil nil nil)))
                       (b2-meta-fold-arithmetic-fold-fixed self constant number))))
         (identity (and plain (b2-meta-fold-arithmetic-fold-right-identity self first)))
         (other (and two (b2-meta-fold-arithmetic-fold-right-identity self second)))
         (operand (and two (b2-algebra-fixed-operand
                            lib (b2-meta-fold-arithmetic-fold-op self first second) 2))))
      (let ((rules (append (list equation)
                           (and kind (list evaluation))
                           (and induction (list induction))
                           (and (equal kind *proof-quote*) simple (list fixed))
                           (and plain (list identity))
                           (and two (list other operand))))
            (openers (append (list (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*))
                             (and (or plain (and (equal kind operation) (null induction)))
                                  (list (b2-meta-fold-arithmetic-fold-call self tail *b2-bags-a*)))
                             (and two (list (b2-meta-fold-arithmetic-fold-call
                                             self (list *library-cdr* tail) *b2-bags-a*))))))
        (b2-meta-fold-solve lib formula evidence openers rules t)))))

(defun b2-meta-fold-arithmetic-fold-tree-value-proof-base (atom self tree formula tail first second)
  (proof-with-checked-results
      ((step (b2-meta-fold-arithmetic-fold-tree-value-proof-establish
              (list atom) *proof-quote* nil self tree formula tail first second)))
    (cons step self)))

(defun b2-meta-fold-arithmetic-fold-tree-value-proof-advance
    (cons-step induction self tree formula tail first second)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (test (list *proof-consp* tail))
         (simple (b2-meta-fold-arithmetic-fold-simple self))
         (operation (b2-meta-fold-arithmetic-fold-operation self)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib test))
         (longer (car signs))
         (single (cadr signs))
         (end (b2-meta-fold-arithmetic-fold-tree-value-proof-establish
               (list cons-step single) (if simple nil *b2-products-fix*) nil
               self tree formula tail first second))
         (more (if simple
                   (b2-meta-fold-arithmetic-fold-tree-value-proof-establish
                    (list cons-step longer) operation induction self tree formula tail first second)
                 (let ((next-test (list *proof-consp* (list *library-cdr* tail))))
                   (proof-with-checked-results
                       ((signs (b2-bags-signed lib next-test))
                        (many (b2-meta-fold-arithmetic-fold-tree-value-proof-establish
                               (list cons-step longer (car signs)) operation induction
                               self tree formula tail first second))
                        (two (b2-meta-fold-arithmetic-fold-tree-value-proof-establish
                              (list cons-step longer (cadr signs)) operation nil
                              self tree formula tail first second)))
                     (proof-proof-cases proof next-test many two)))))
         (step (proof-proof-cases proof test more end)))
      (cons step self))))

(defun b2-meta-fold-arithmetic-fold-tree-value-proof (self tree formula tail first second)
  (proof-with-checked-results
      ((pending (b2-meta-fold-on-list-request self formula *library-x* nil nil))
       (advance (b2-meta-fold-arithmetic-fold-tree-value-proof-advance
                 (cadddr pending) (nth 4 pending)
                 (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                 tree formula tail first second))
       (pending-base (b2-meta-fold-on-list-request self formula *library-x* advance nil))
       (base (b2-meta-fold-arithmetic-fold-tree-value-proof-base
              (cadddr pending-base)
              (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending-base))
              tree formula tail first second)))
    (b2-meta-fold-on-list-complete self formula *library-x* base advance nil)))

(defun b2-meta-fold-arithmetic-fold-tree-value (self elements)
  (let* ((tree (b2-meta-fold-arithmetic-fold-tree self *library-x*))
         (value (b2-meta-fold-arithmetic-fold-ev self tree *b2-bags-a*))
         (left (if (b2-meta-fold-arithmetic-fold-simple self)
                   (list *b2-products-fix* value)
                 value))
         (formula (proof-eq left (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*)))
         (tail (list *library-cdr* *library-x*))
         (first (b2-meta-fold-arithmetic-fold-ev self (list *library-car* *library-x*) *b2-bags-a*))
         (second (b2-meta-fold-arithmetic-fold-ev self (list *library-car* tail) *b2-bags-a*))
         (bindings (list (list *library-x* elements))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "TREE")
        (b2-meta-fold-arithmetic-fold-fact self "TREE" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-tree-value-proof self tree formula tail first second)))
        (b2-meta-fold-arithmetic-fold-fact (cdr step) "TREE" (car step) bindings)))))

(defun b2-meta-fold-arithmetic-fold-fringe-value-proof-hypothesis
    (lib formula measure argument bindings cons-step)
  (proof-with-checked-results
      ((rulers (b2-measures-rulers-init lib (list cons-step)))
       (smaller (b2-measures-rulers-selector-decrease
                 lib (list *proof-ordinal-less* (list *library-count* argument) measure) rulers)))
    (b2-tactics-tactics-induction-hypothesis lib formula measure bindings (car smaller))))

(defun b2-meta-fold-arithmetic-fold-fringe-value-proof-singleton (evidence self fringe formula)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((opened (b2-meta-fold-normalize lib fringe evidence (list fringe) nil))
         (value (b2-meta-fold-first-at opened 2))
         (calls (list (b2-meta-fold-arithmetic-fold-call self value *b2-bags-a*)
                      (b2-meta-fold-arithmetic-fold-call self *proof-false* *b2-bags-a*)))
         (identity (b2-meta-fold-arithmetic-fold-right-identity
                    self (b2-meta-fold-arithmetic-fold-ev self *library-x* *b2-bags-a*))))
      (b2-meta-fold-solve lib formula evidence calls (list opened identity) nil))))

(defun b2-meta-fold-arithmetic-fold-fringe-value-proof (self fringe formula)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (operation (b2-meta-fold-arithmetic-fold-operation self))
         (test (list *proof-consp* *library-x*))
         (maybe (proof-eq (list *library-car* *library-x*) (proof-quote operation)))
         (tail (list *library-cdr* *library-x*))
         (front (list *library-car* tail))
         (back (list *library-car* (list *library-cdr* tail)))
         (measure (list *library-count* *library-x*))
         (front-bindings (list (list *library-x* front)))
         (back-bindings (list (list *library-x* back))))
    (proof-with-checked-results
        ((test-signs (b2-bags-signed lib test))
         (kind-signs (b2-bags-signed lib maybe))
         (cons-step (car test-signs))
         (atom (cadr test-signs))
         (same (car kind-signs))
         (different (cadr kind-signs))
         (front-hypothesis (b2-meta-fold-arithmetic-fold-fringe-value-proof-hypothesis
                            lib formula measure front front-bindings cons-step))
         (back-hypothesis (b2-meta-fold-arithmetic-fold-fringe-value-proof-hypothesis
                           lib formula measure back back-bindings cons-step))
         (left (list *b2-bags-fringe* (proof-quote operation) front))
         (right (list *b2-bags-fringe* (proof-quote operation) back))
         (append-result (b2-meta-fold-arithmetic-fold-append-value self left right))
         (self (cdr append-result))
         (lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (evidence (list cons-step same))
         (applied (b2-meta-fold-arithmetic-fold-interpret self *library-x* operation evidence))
         (original (b2-meta-fold-first-at applied 2))
         (numeric (b2-products-numeric-closure lib original))
         (fix (b2-meta-fold-arithmetic-fold-fixed self original numeric))
         (a (b2-algebra-fixed-operand lib original 1))
         (first (b2-meta-fold-first-at a 2))
         (b (b2-algebra-fixed-operand lib first 2))
         (reflexive (proof-proof-reflexive
                     proof (list *b2-products-fix*
                                 (b2-meta-fold-arithmetic-fold-ev self *library-x* *b2-bags-a*))))
         (evaluation (proof-proof-rewrite proof reflexive applied '(1 2 1)))
         (equation (proof-proof-chain proof evaluation (list fix a b)))
         (yes (b2-meta-fold-solve lib formula evidence (list fringe)
                                 (list (car append-result) front-hypothesis back-hypothesis equation)
                                 nil))
         (other (b2-meta-fold-arithmetic-fold-fringe-value-proof-singleton
                 (list cons-step different) self fringe formula))
         (nonempty (proof-proof-cases proof maybe yes other))
         (empty (b2-meta-fold-arithmetic-fold-fringe-value-proof-singleton
                 (list atom) self fringe formula))
         (case-step (proof-proof-cases proof test nonempty empty))
         (ordinal (library-library-builtin lib 1 *library-x*))
         (step (proof-proof-induct
                proof ordinal case-step formula measure (list front-bindings back-bindings))))
      (cons step self))))

(defun b2-meta-fold-arithmetic-fold-fringe-value (self expression)
  (let* ((operation (b2-meta-fold-arithmetic-fold-operation self))
         (fringe (list *b2-bags-fringe* (proof-quote operation) *library-x*))
         (formula (proof-eq
                   (b2-meta-fold-arithmetic-fold-call self fringe *b2-bags-a*)
                   (list *b2-products-fix*
                         (b2-meta-fold-arithmetic-fold-ev self *library-x* *b2-bags-a*))))
         (bindings (list (list *library-x* expression))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "FRINGE")
        (b2-meta-fold-arithmetic-fold-fact self "FRINGE" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-fringe-value-proof self fringe formula)))
        (b2-meta-fold-arithmetic-fold-fact (cdr step) "FRINGE" (car step) bindings)))))

(defun b2-meta-fold-arithmetic-fold-delete-value-proof-base-impossible (premise lib atom condition goal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((exposed (b2-bags-reduced-premise lib premise (list atom) (list condition) nil))
         (subsumed (proof-proof-subsume proof exposed (cons goal (proof-step-clause exposed)))))
      (proof-proof-tidy proof subsumed))))

(defun b2-meta-fold-arithmetic-fold-delete-value-proof-base (atom self condition goal)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((pending (b2-meta-fold-implication-request lib condition goal))
         (step (b2-meta-fold-arithmetic-fold-delete-value-proof-base-impossible
                (cadddr pending) (caddr pending) atom condition goal))
         (answer (b2-meta-fold-implication-complete lib condition goal step (caddr pending))))
      (cons (car answer) (b2-meta-fold-arithmetic-fold-with-lib self (cdr answer))))))

(defun b2-meta-fold-arithmetic-fold-delete-value-proof-advance-conclude
    (premise self cons-step induction condition deletion folded goal value dropped)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (test (proof-eq *b2-meta-fold-u* (list *library-car* *library-x*)))
         (kind (b2-meta-fold-arithmetic-fold-operator-name self))
         (assoc-name (concatenate 'string "ASSOCIATIVITY-OF-" kind))
         (commute-name (concatenate 'string "COMMUTATIVITY-OF-" kind))
         (item-value (b2-meta-fold-arithmetic-fold-ev self *b2-meta-fold-u* *b2-bags-a*)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib test))
         (same (car signs))
         (different (cadr signs))
         (yes (b2-meta-fold-solve lib goal (list cons-step same) (list deletion folded)
                                  (list same) nil))
         (otherwise (list cons-step different))
         (opened (b2-meta-fold-normalize lib deletion otherwise (list deletion) nil))
         (member-tail (b2-bags-reduced-premise lib premise otherwise (list condition) nil))
         (inherit (proof-proof-modus-ponens proof induction member-tail))
         (assoc (library-library-axiom lib assoc-name (list item-value value dropped)))
         (a (proof-proof-symmetric proof assoc))
         (b (library-library-axiom lib commute-name (list item-value value)))
         (a (proof-proof-rewrite proof a b '(1 2 1)))
         (c (library-library-axiom lib assoc-name (list value item-value dropped)))
         (swap (proof-proof-chain proof a (list c)))
         (opened-value (b2-meta-fold-first-at opened 2))
         (no (b2-meta-fold-solve lib goal otherwise
                                 (list folded
                                       (b2-meta-fold-arithmetic-fold-call self opened-value *b2-bags-a*))
                                 (list opened swap inherit) nil)))
      (proof-proof-cases proof test yes no))))

(defun b2-meta-fold-arithmetic-fold-delete-value-proof-advance
    (cons-step induction self condition deletion folded goal value dropped)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((pending (b2-meta-fold-implication-request lib condition goal))
         (step (b2-meta-fold-arithmetic-fold-delete-value-proof-advance-conclude
                (cadddr pending) (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                cons-step induction condition deletion folded goal value dropped))
         (answer (b2-meta-fold-implication-complete lib condition goal step (caddr pending))))
      (cons (car answer) (b2-meta-fold-arithmetic-fold-with-lib self (cdr answer))))))

(defun b2-meta-fold-arithmetic-fold-delete-value-proof
    (self formula condition deletion folded goal value dropped)
  (proof-with-checked-results
      ((pending (b2-meta-fold-on-list-request self formula *library-x* nil nil))
       (advance (b2-meta-fold-arithmetic-fold-delete-value-proof-advance
                 (cadddr pending) (nth 4 pending)
                 (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                 condition deletion folded goal value dropped))
       (pending-base (b2-meta-fold-on-list-request self formula *library-x* advance nil))
       (base (b2-meta-fold-arithmetic-fold-delete-value-proof-base
              (cadddr pending-base)
              (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending-base)) condition goal)))
    (b2-meta-fold-on-list-complete self formula *library-x* base advance nil)))

(defun b2-meta-fold-arithmetic-fold-delete-value (self item elements)
  (let* ((condition (list *b2-bags-memb* *b2-meta-fold-u* *library-x*))
         (deletion (list *b2-bags-del* *b2-meta-fold-u* *library-x*))
         (folded (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*))
         (goal (proof-eq
                (b2-meta-fold-arithmetic-fold-op
                 self (b2-meta-fold-arithmetic-fold-ev self *b2-meta-fold-u* *b2-bags-a*)
                 (b2-meta-fold-arithmetic-fold-call self deletion *b2-bags-a*))
                folded))
         (formula (list *library-implies* condition goal))
         (tail (list *library-cdr* *library-x*))
         (value (b2-meta-fold-arithmetic-fold-ev self (list *library-car* *library-x*) *b2-bags-a*))
         (dropped (b2-meta-fold-arithmetic-fold-call self (list *b2-bags-del* *b2-meta-fold-u* tail)
                                                    *b2-bags-a*))
         (bindings (list (list *b2-meta-fold-u* item) (list *library-x* elements))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "DELETE")
        (b2-meta-fold-arithmetic-fold-fact self "DELETE" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-delete-value-proof
                  self formula condition deletion folded goal value dropped)))
        (b2-meta-fold-arithmetic-fold-fact (cdr step) "DELETE" (car step) bindings)))))

(defun b2-meta-fold-arithmetic-fold-difference-value-proof-base
    (atom self included difference folded-y goal)
  (let ((call (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*)))
    (proof-with-checked-results
        ((unit (b2-meta-fold-arithmetic-fold-identity self call))
         (number (b2-meta-fold-arithmetic-fold-number self *library-x*))
         (self (cdr number))
         (lib (b2-meta-fold-arithmetic-fold-lib self))
         (fixed (b2-meta-fold-arithmetic-fold-fixed self call (car number)))
         (identity (proof-proof-chain (library-library-proof lib) unit (list fixed)))
         (pending (b2-meta-fold-implication-request lib included goal))
         (step (b2-meta-fold-solve (caddr pending) goal (list atom) (list difference folded-y)
                                  (list identity) nil))
         (answer (b2-meta-fold-implication-complete lib included goal step (caddr pending))))
      (cons (car answer) (b2-meta-fold-arithmetic-fold-with-lib self (cdr answer))))))

(defun b2-meta-fold-arithmetic-fold-difference-value-proof-advance-conclude
    (premise self cons-step induction included difference folded-y goal tail value leftover)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b2-bags-reduced-premise lib premise (list cons-step) (list included) nil))
         (steps (proof-proof-conjunct proof opened))
         (membership (car steps))
         (residue (proof-proof-modus-ponens proof induction (cadr steps)))
         (delete-result (b2-meta-fold-arithmetic-fold-delete-value
                         self (list *library-car* *library-y*) *library-x*))
         (self (cdr delete-result))
         (lib (b2-meta-fold-arithmetic-fold-lib self))
         (deleted (proof-proof-modus-ponens
                   (library-library-proof lib) (car delete-result) membership))
         (assoc (library-library-axiom
                 lib (concatenate 'string "ASSOCIATIVITY-OF-"
                                  (b2-meta-fold-arithmetic-fold-operator-name self))
                 (list value (b2-meta-fold-arithmetic-fold-call self tail *b2-bags-a*) leftover)))
         (step (b2-meta-fold-solve lib goal (list cons-step membership) (list difference folded-y)
                                  (list assoc residue deleted) nil)))
      (cons step self))))

(defun b2-meta-fold-arithmetic-fold-difference-value-proof-advance
    (cons-step induction self included difference folded-y goal tail value leftover)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((pending (b2-meta-fold-implication-request lib included goal))
         (result (b2-meta-fold-arithmetic-fold-difference-value-proof-advance-conclude
                  (cadddr pending) (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                  cons-step induction included difference folded-y goal tail value leftover))
         (answer (b2-meta-fold-implication-complete
                  lib included goal (car result) (b2-meta-fold-arithmetic-fold-lib (cdr result)))))
      (cons (car answer) (b2-meta-fold-arithmetic-fold-with-lib (cdr result) (cdr answer))))))

(defun b2-meta-fold-arithmetic-fold-difference-value-proof
    (self formula included difference folded-y goal after tail value leftover)
  (let ((extra (list (list *library-x* after))))
    (proof-with-checked-results
        ((pending (b2-meta-fold-on-list-request self formula *library-y* nil extra))
         (advance (b2-meta-fold-arithmetic-fold-difference-value-proof-advance
                   (cadddr pending) (nth 4 pending)
                   (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                   included difference folded-y goal tail value leftover))
         (pending-base (b2-meta-fold-on-list-request self formula *library-y* advance extra))
         (base (b2-meta-fold-arithmetic-fold-difference-value-proof-base
                (cadddr pending-base)
                (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending-base))
                included difference folded-y goal)))
      (b2-meta-fold-on-list-complete self formula *library-y* base advance extra))))

(defun b2-meta-fold-arithmetic-fold-difference-value (self whole part)
  (let* ((included (list *b2-bags-subbag* *library-y* *library-x*))
         (difference (list *b2-meta-fold-bagdiff* *library-x* *library-y*))
         (folded-y (b2-meta-fold-arithmetic-fold-call self *library-y* *b2-bags-a*))
         (goal (proof-eq
                (b2-meta-fold-arithmetic-fold-op
                 self folded-y (b2-meta-fold-arithmetic-fold-call self difference *b2-bags-a*))
                (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*)))
         (formula (list *library-implies* included goal))
         (head (list *library-car* *library-y*))
         (after (list *b2-bags-del* head *library-x*))
         (tail (list *library-cdr* *library-y*))
         (value (b2-meta-fold-arithmetic-fold-ev self head *b2-bags-a*))
         (leftover (b2-meta-fold-arithmetic-fold-call self (list *b2-meta-fold-bagdiff* after tail)
                                                      *b2-bags-a*))
         (bindings (list (list *library-x* whole) (list *library-y* part))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "DIFFERENCE")
        (b2-meta-fold-arithmetic-fold-fact self "DIFFERENCE" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-difference-value-proof
                  self formula included difference folded-y goal after tail value leftover)))
        (b2-meta-fold-arithmetic-fold-fact (cdr step) "DIFFERENCE" (car step) bindings)))))

(defun b2-meta-fold-arithmetic-fold-formal-zero-proof-base (atom self nonempty goal)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((pending (b2-meta-fold-implication-request lib nonempty goal))
         (step (b2-meta-fold-solve (caddr pending) goal (list atom (cadddr pending)) nil nil nil))
         (answer (b2-meta-fold-implication-complete lib nonempty goal step (caddr pending))))
      (cons (car answer) (b2-meta-fold-arithmetic-fold-with-lib self (cdr answer))))))

(defun b2-meta-fold-arithmetic-fold-formal-zero-proof-advance-short
    (self evidence call goal folded tail-fold value)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((syntax (b2-meta-fold-normalize lib call evidence (list call) nil))
         (right (b2-meta-fold-first-at syntax 2))
         (comparison (b2-meta-fold-arithmetic-fold-interpret self right *proof-equal* evidence))
         (comparison (b2-meta-fold-arithmetic-fold-evaluate-arguments
                      self comparison (list *proof-quote* *b2-products-fix*) evidence))
         (unit (b2-meta-fold-arithmetic-fold-right-identity self value)))
      (b2-meta-fold-solve lib goal evidence (list folded tail-fold) (list syntax comparison unit) nil))))

(defun b2-meta-fold-arithmetic-fold-formal-zero-proof-advance-duplicate
    (self cons-step longer hit recursive test call goal folded head tail value tail-zero head-zero)
  (proof-with-checked-results
      ((deleted (b2-meta-fold-arithmetic-fold-delete-value self head tail))
       (self (cdr deleted))
       (lib (b2-meta-fold-arithmetic-fold-lib self))
       (same-value (proof-proof-modus-ponens (library-library-proof lib) (car deleted) hit))
       (collapsed (b2-algebra-product-zero-test
                   lib value (b2-meta-fold-arithmetic-fold-call
                              self (list *b2-bags-del* head tail) *b2-bags-a*)))
       (lib (cdr collapsed))
       (self (b2-meta-fold-arithmetic-fold-with-lib self lib))
       (proof (library-library-proof lib))
       (signs (b2-bags-signed lib head-zero))
       (yes-head (car signs))
       (no-head (cadr signs))
       (reversed (proof-proof-symmetric proof same-value))
       (tail-has-zero (b2-meta-fold-solve lib tail-zero (list yes-head)
                                         nil (list reversed (car collapsed)) nil))
       (right (b2-meta-fold-first-at test 2))
       (merge (proof-eq right tail-zero))
       (positive (b2-meta-fold-solve lib merge (list yes-head tail-has-zero) nil nil nil))
       (negative (b2-meta-fold-solve lib merge (list no-head) nil nil nil))
       (ignore-duplicate (proof-proof-cases proof head-zero positive negative))
       (combined (proof-proof-chain proof test (list ignore-duplicate)))
       (step (b2-meta-fold-solve lib goal (list cons-step longer hit)
                                 (list call folded) (list recursive combined) nil)))
    (cons step self)))

(defun b2-meta-fold-arithmetic-fold-formal-zero-proof-advance-different
    (self evidence call goal folded recursive test)
  (let ((lib (b2-meta-fold-arithmetic-fold-lib self)))
    (proof-with-checked-results
        ((opened (b2-meta-fold-normalize lib call evidence (list call) nil))
         (value (b2-meta-fold-first-at opened 2))
         (term (b2-meta-fold-arithmetic-fold-interpret self value *proof-if* evidence))
         (right (b2-meta-fold-first-at term 2))
         (branches (if (integerp right)
                       (proof-term-at right 1)
                     (proof-list-of-length (cdr right) 3)))
         (condition (proof-term-at (car branches) 1))
         (comparison (b2-meta-fold-arithmetic-fold-interpret self condition *proof-equal* evidence))
         (comparison (b2-meta-fold-arithmetic-fold-evaluate-arguments
                      self comparison (list *proof-quote* *b2-products-fix*) evidence))
         (then (proof-term-at (cadr branches) 1))
         (truth (b2-meta-fold-arithmetic-fold-interpret self then *proof-quote* evidence))
         (rewritten (b2-meta-fold-arithmetic-fold-rewrite-operands self term (list comparison truth))))
      (b2-meta-fold-solve lib goal evidence (list folded) (list opened rewritten recursive test) t))))

(defun b2-meta-fold-arithmetic-fold-formal-zero-proof-advance
    (cons-step induction self call goal nonempty folded head tail value tail-fold tail-zero head-zero repeats)
  (let* ((lib (b2-meta-fold-arithmetic-fold-lib self))
         (has-tail (list *proof-consp* tail)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib has-tail))
         (longer (car signs))
         (singleton (cadr signs))
         (stop (b2-meta-fold-arithmetic-fold-formal-zero-proof-advance-short
                self (list cons-step singleton) call goal folded tail-fold value))
         (test-result (b2-algebra-product-zero-test lib value tail-fold))
         (self (b2-meta-fold-arithmetic-fold-with-lib self (cdr test-result)))
         (number (b2-meta-fold-arithmetic-fold-number self tail))
         (self (cdr number))
         (lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (fixed (b2-meta-fold-arithmetic-fold-fixed self tail-fold (car number)))
         (test (proof-proof-rewrite proof (car test-result) fixed '(1 2 3 2)))
         (test (proof-proof-tidy proof test))
         (recursive (proof-proof-modus-ponens proof induction longer))
         (repeat-signs (b2-bags-signed lib repeats))
         (hit (car repeat-signs))
         (miss (cadr repeat-signs))
         (duplicated (b2-meta-fold-arithmetic-fold-formal-zero-proof-advance-duplicate
                      self cons-step longer hit recursive test call goal folded
                      head tail value tail-zero head-zero))
         (self (cdr duplicated))
         (lib (b2-meta-fold-arithmetic-fold-lib self))
         (proof (library-library-proof lib))
         (separated (b2-meta-fold-arithmetic-fold-formal-zero-proof-advance-different
                     self (list cons-step longer miss) call goal folded recursive test))
         (long (proof-proof-cases proof repeats (car duplicated) separated))
         (result (proof-proof-cases proof has-tail long stop))
         (pending (b2-meta-fold-implication-request lib nonempty goal))
         (answer (b2-meta-fold-implication-complete lib nonempty goal result (caddr pending))))
      (cons (car answer) (b2-meta-fold-arithmetic-fold-with-lib self (cdr answer))))))

(defun b2-meta-fold-arithmetic-fold-formal-zero-proof
    (self formula call goal nonempty folded head tail value tail-fold tail-zero head-zero repeats)
  (proof-with-checked-results
      ((pending (b2-meta-fold-on-list-request self formula *library-x* nil nil))
       (advance (b2-meta-fold-arithmetic-fold-formal-zero-proof-advance
                 (cadddr pending) (nth 4 pending)
                 (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending))
                 call goal nonempty folded head tail value tail-fold tail-zero head-zero repeats))
       (pending-base (b2-meta-fold-on-list-request self formula *library-x* advance nil))
       (base (b2-meta-fold-arithmetic-fold-formal-zero-proof-base
              (cadddr pending-base)
              (b2-meta-fold-arithmetic-fold-with-lib self (caddr pending-base))
              nonempty goal)))
    (b2-meta-fold-on-list-complete self formula *library-x* base advance nil)))

(defun b2-meta-fold-arithmetic-fold-formal-zero (self elements)
  (let* ((call (list *b2-meta-fold-formal-zero* *library-x*))
         (evaluated (b2-meta-fold-arithmetic-fold-ev self call *b2-bags-a*))
         (folded (b2-meta-fold-arithmetic-fold-call self *library-x* *b2-bags-a*))
         (nonempty (list *proof-consp* *library-x*))
         (goal (proof-eq evaluated (proof-eq *proof-zero* folded)))
         (formula (list *library-implies* nonempty goal))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (value (b2-meta-fold-arithmetic-fold-ev self head *b2-bags-a*))
         (tail-fold (b2-meta-fold-arithmetic-fold-call self tail *b2-bags-a*))
         (tail-zero (proof-eq *proof-zero* tail-fold))
         (head-zero (proof-eq *proof-zero* (list *b2-products-fix* value)))
         (repeats (list *b2-bags-memb* head tail))
         (bindings (list (list *library-x* elements))))
    (if (b2-meta-fold-arithmetic-fold-has-fact self "ZERO-TEST")
        (b2-meta-fold-arithmetic-fold-fact self "ZERO-TEST" nil bindings)
      (proof-with-checked-results
          ((step (b2-meta-fold-arithmetic-fold-formal-zero-proof
                  self formula call goal nonempty folded head tail value tail-fold tail-zero head-zero repeats)))
        (b2-meta-fold-arithmetic-fold-fact (cdr step) "ZERO-TEST" (car step) bindings)))))
