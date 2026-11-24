(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro b2-arithmetic-declare-events ()
  '(progn

(defconst *b2-arithmetic-zp* (proof-sym "ZP" "ACL2"))
(defconst *b2-arithmetic-factorial* (proof-sym "FACTORIAL" "ACL2"))

(defun b2-arithmetic-require (key table)
  (let ((found (assoc-equal key table)))
    (if found
        (cdr found)
      '(:failure "tactic-rejected" ""))))

(defun b2-arithmetic-factorial-positive-base (halted lib formula term)
  (b2-tactics-tactics-solve lib formula (list halted) (list term) nil 0 nil))

(defun b2-arithmetic-factorial-positive-advance (running hypothesis lib formula n term child)
  (let ((proof (library-library-proof lib))
        (zp (list *b2-arithmetic-zp*)))
    (proof-with-checked-results
     ((int-n (b2-tactics-tactics-from-impossible lib (library-integer n) running
                                                nil zp nil 1500 nil))
      (pos-n (b2-tactics-tactics-from-impossible lib (library-positive n) running
                                                (list int-n) zp nil 1500 nil))
      (child-types (proof-proof-conjunct proof hypothesis))
      (int-child (car child-types))
      (pos-child (cadr child-types))
      (unfolded (b2-tactics-tactics-normalize lib term (list running) (list term) nil 1500 nil))
      (first (proof-step-first unfolded))
      (rhs (proof-term-at first 2))
      (operands (proof-list-of-length rhs 3))
      (left (cadr operands))
      (right (caddr operands))
      (product (list *proof-times* left right))
      (types (list int-n int-child))
      (int-product (library-library-type-of lib product types))
      (by-term (table-put (list (cons n pos-n)) (list *b2-arithmetic-factorial* child) pos-child))
      (left-rational (library-library-rational lib left types))
      (right-rational (library-library-rational lib right types))
      (left-positive (b2-arithmetic-require left by-term))
      (right-positive (b2-arithmetic-require right by-term))
      (pos-product (library-library-cite lib "POSITIVE-PRODUCT" (list left right)
                                         (list left-rational right-rational left-positive right-positive)))
      (head (proof-term-at formula 0))
      (typed (proof-step-first int-product))
      (positive (proof-step-first pos-product))
      (result (b2-tactics-tactics-solve lib (list head typed positive *proof-false*)
                                       (list int-product pos-product) nil nil 0 nil))
      (folded (proof-proof-symmetric proof unfolded)))
     (proof-proof-rewrite-first proof result folded))))

(defun b2-arithmetic-factorial-positive (lib formula)
  (proof-with-checked-results
   ((typed (proof-term-at formula 1))
    (term (proof-term-at typed 1))
    (call (proof-list-of-length term 2))
    (n (cadr call))
    (test (list *b2-arithmetic-zp* n))
    (smaller (library-library-builtin lib 9 n))
    (first (proof-step-first smaller))
    (lhs (proof-term-at first 1))
    (child (proof-term-at lhs 1))
    (bindings (list (list n child)))
    (advance-request (b2-tactics-tactics-by-induction
                      lib formula n test smaller bindings nil nil nil))
    (arguments (car advance-request))
    (advance (b2-arithmetic-factorial-positive-advance
              (cadddr arguments) (car (cddddr arguments)) (cdr advance-request) formula n term child))
    (advance-reply (cons advance (cdr advance-request)))
    (base-request (b2-tactics-tactics-by-induction
                   lib formula n test smaller bindings nil advance-reply nil))
    (base (b2-arithmetic-factorial-positive-base
           (cadddr (car base-request)) (cdr base-request) formula term))
    (result (b2-tactics-tactics-by-induction
             lib formula n test smaller bindings (cons base (cdr base-request)) advance-reply nil)))
   (car result)))

(defun b2-arithmetic-factorial-properties (lib name formula)
  (let ((theorem (proof-sym "FACTORIAL-POSITIVE-INTEGER" "ACL2")))
    (if (equal name theorem)
        (b2-arithmetic-factorial-positive lib formula)
      (let ((proof (library-library-proof lib))
            (nonnegative (equal name (proof-sym "FACTORIAL-NON-NEGATIVE" "ACL2"))))
        (proof-with-checked-results
         ((term (if nonnegative
                    (proof-with-checked-results ((comparison (proof-term-at formula 1)))
                      (proof-term-at comparison 1))
                  (proof-term-at formula 2)))
          (clause (b2-arithmetic-require theorem (proof-proof-facts proof)))
          (pattern (proof-term-at clause 0))
          (typed-pattern (proof-term-at pattern 1))
          (term-pattern (proof-term-at typed-pattern 1))
          (proved (b2-tactics-tactics-exact lib theorem term-pattern term))
          (parts (proof-proof-conjunct proof proved)))
         (if nonnegative
             (proof-with-checked-results
              ((discrete (proof-proof-fact proof "integer-discrete" (list (list *library-x* term)))))
              (proof-proof-modus-ponens proof discrete proved))
           (proof-with-checked-results
            ((lower-bound (library-library-cite lib "POSITIVE-NONNEGATIVE" (list term) parts)))
            (b2-tactics-tactics-solve lib formula (list (car parts) lower-bound)
                                     (list (proof-cl "ABS") (proof-cl "MINUSP")) nil 0 nil))))))))
))
