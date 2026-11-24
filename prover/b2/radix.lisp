(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-radix-digit* (proof-sym "DIGIT-TO-CHAR" "ACL2"))
(defconst *b2-radix-zp* (proof-sym "ZP" "ACL2"))

(defun b2-radix-digit-character-leaf (value tests lib name formal)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((head (proof-term-at value 0)))
      (if (equal head (proof-cl "CODE-CHAR"))
          (let* ((fact (proof-sym "CODE-CHAR-TYPE" "ACL2"))
                 (entry (assoc-equal fact (proof-proof-facts proof))))
            (if entry
                (proof-with-checked-results ((pattern (proof-term-at (cdr entry) 0)))
                  (b2-tactics-tactics-exact lib fact pattern (list *b2-tactics-characterp* value)))
              '(:failure "tactic-rejected" "")))
        (proof-with-checked-results ((arg (proof-term-at value 1)))
          (proof-proof-fact proof name (list (list formal arg))))))))

(defun b2-radix-digit-character-leaves (requests lib name formal direct)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (value (car request))
           (step (if direct
                     (b2-tactics-tactics-solve lib (list *b2-tactics-characterp* value)
                                               nil nil nil 0 nil)
                   (b2-radix-digit-character-leaf value (cadr request) lib name formal)))
           (entry (cons request step)))
      (if (failure-p step)
          (list entry)
        (cons entry (b2-radix-digit-character-leaves (cdr requests) lib name formal direct))))))

(defun b2-radix-digit-character-open (lib call name formal direct)
  (let ((proof (library-library-proof lib))
        (template (list *b2-tactics-characterp* *proof-result*)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (first (proof-step-first opened))
         (value (proof-term-at first 2))
         (requests (proof-proof-by-value-leaves proof value nil))
         (leaves (b2-radix-digit-character-leaves requests lib name formal direct))
         (step (proof-proof-by-value proof value template leaves nil))
         (reverse (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite-result proof step reverse template *proof-result*))))

(defun b2-radix-digit-character (lib call)
  (let* ((proof (library-library-proof lib))
         (definition (assoc-equal *b2-radix-digit* (proof-proof-definitions proof)))
         (name (proof-sym "B2-DIGIT-CHARACTER" "ACL2")))
    (if (not definition)
        '(:failure "tactic-rejected" "")
      (proof-with-checked-results
          ((formals (proof-list-of-length (cadr definition) 1))
           (formal (car formals))
           (lib (if (assoc-equal name (proof-proof-facts proof))
                    lib
                  (proof-with-checked-results
                      ((digit (list *b2-radix-digit* formal))
                       (step (b2-radix-digit-character-open lib digit name formal t))
                       (added (b2-tactics-tactics-add-lemma lib "DIGIT-CHARACTER" step :none)))
                    (cdr added))))
           (head (proof-term-at call 0))
           (step (if (equal head *b2-radix-digit*)
                     (proof-with-checked-results ((arg (proof-term-at call 1)))
                       (proof-proof-fact (library-library-proof lib) name
                                         (list (list formal arg))))
                   (b2-radix-digit-character-open lib call name formal nil))))
        (cons step lib)))))

(defun b2-radix-character-accumulator-bindings (args next-args)
  (cond ((or (endp args) (endp next-args)) nil)
        ((equal (car args) (car next-args))
         (b2-radix-character-accumulator-bindings (cdr args) (cdr next-args)))
        (t (cons (list (car args) (car next-args))
                 (b2-radix-character-accumulator-bindings (cdr args) (cdr next-args))))))

(defun b2-radix-character-accumulator-base (halted lib pred property-of-result call)
  (proof-with-checked-results
      ((pending (b2-tactics-tactics-implication lib pred property-of-result nil))
       (request (car pending))
       (step (b2-tactics-tactics-solve (caddr request) property-of-result
                                       (list halted (cadddr request)) (list call) nil 0 nil)))
    (b2-tactics-tactics-implication lib pred property-of-result (cons step (cdr pending)))))

(defun b2-radix-character-accumulator-advance-consequent (step lib hypothesis digit-proof equation)
  (proof-with-checked-results
      ((first (proof-step-first hypothesis))
       (extended (proof-term-at first 1))
       (inherited (b2-tactics-tactics-solve lib extended (list step digit-proof)
                                            (list extended) nil 0 nil))
       (result (proof-proof-modus-ponens (library-library-proof lib) hypothesis inherited)))
    (library-library-transport-argument lib result equation 1)))

(defun b2-radix-character-accumulator-advance (nonzero hypothesis lib pred property-of-result
                                             digit-proof equation)
  (declare (ignore nonzero))
  (proof-with-checked-results
      ((pending (b2-tactics-tactics-implication lib pred property-of-result nil))
       (request (car pending))
       (step (b2-radix-character-accumulator-advance-consequent
               (cadddr request) (caddr request) hypothesis digit-proof equation)))
    (b2-tactics-tactics-implication lib pred property-of-result (cons step (cdr pending)))))

(defun b2-radix-character-accumulator (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (pred (cadr parts))
         (property-of-result (caddr parts))
         (call (proof-term-at property-of-result 1))
         (length-term (proof-term-at call 2))
         (test (list *b2-radix-zp* length-term))
         (running (proof-proof-assume proof test nil))
         (equation (b2-tactics-tactics-normalize lib call (list running) (list call) nil 1500 nil))
         (first (if equation (proof-step-first equation)
                  '(:failure "failure" "")))
         (next-call (proof-term-at first 2))
         (bindings (b2-radix-character-accumulator-bindings (cdr call) (cdr next-call)))
         (last-arg (proof-term-at next-call (max 0 (1- (len next-call)))))
         (digit (proof-term-at last-arg 1))
         (digit-proof (b2-radix-digit-character lib digit))
         (lib (cdr digit-proof))
         (digit-proof (car digit-proof))
         (smaller (library-library-builtin lib 9 length-term))
         (pending (b2-tactics-tactics-by-induction lib formula length-term test smaller
                                                   bindings nil nil nil))
         (request (car pending))
         (advance (b2-radix-character-accumulator-advance
                   (cadddr request) (car (cddddr request)) (caddr request)
                   pred property-of-result digit-proof equation))
         (pending (b2-tactics-tactics-by-induction lib formula length-term test smaller
                                                   bindings nil advance nil))
         (request (car pending))
         (base (b2-radix-character-accumulator-base (cadddr request) (caddr request)
                                                   pred property-of-result call)))
      (b2-tactics-tactics-by-induction lib formula length-term test smaller
                                       bindings base advance nil))))
