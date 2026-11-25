(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-floor-translation-add-floor* '("sym" "ACL2" "FLOOR-+"))
(defconst *b2-floor-translation-add-mod* '("sym" "ACL2" "MOD-+"))
(defconst *b2-floor-translation-add-basic*
  '(("sym" "ACL2" "CANCEL-FLOOR-+-BASIC") ("sym" "ACL2" "CANCEL-MOD-+-BASIC")))
(defconst *b2-floor-translation-add-three*
  '(("sym" "ACL2" "CANCEL-FLOOR-+-3") ("sym" "ACL2" "CANCEL-MOD-+-3")))
(defconst *b2-floor-translation-rewrite-mod*
  '(("sym" "ACL2" "REWRITE-FLOOR-MOD") ("sym" "ACL2" "REWRITE-MOD-MOD")))
(defconst *b2-floor-translation-translations*
  (append (list (car *b2-floor-translation-add-three*)
                (car *b2-floor-translation-add-basic*)
                (cadr *b2-floor-translation-add-three*)
                (cadr *b2-floor-translation-add-basic*)
                *b2-floor-translation-add-floor* *b2-floor-translation-add-mod*)
          *b2-floor-translation-rewrite-mod*))
(defconst *b2-floor-translation-rational-ops*
  (list (cons *proof-plus* "binary-+")
        (cons *proof-times* "binary-*")
        (cons *proof-minus* "unary--")
        (cons *b2-products-recip* "unary-/")))
(defconst *b2-floor-translation-rem* '("sym" "COMMON-LISP" "REM"))

(mutual-recursion
 (defun b2-floor-translation-rational-type-run (n lib term known solver)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b2-floor-translation-rational-type-run")
     (let ((rational (assoc-equal (list *library-rationalp* term) known)))
       (cond (rational (cons (cdr rational) solver))
             ((or (assoc-equal (list *proof-integerp* term) known)
                  (proof-is-call term *proof-quote*))
              (proof-with-checked-results
                  ((result (library-library-rational lib term (table-values known))))
                (cons result solver)))
             ((or (proof-is-call term *b2-floor-intervals-floor*)
                  (proof-is-call term *b2-numeric-types-truncate*))
              (proof-with-checked-results
                  ((parts (proof-list-of-length term 3))
                   (typed (b2-numeric-types-types-quotient-integer solver
                                                                  (car parts) (cadr parts) (caddr parts)))
                   (lib (b2-numeric-types-types-lib (cdr typed)))
                   (result (library-library-rational lib term (list (car typed)))))
                (cons result (cdr typed))))
             ((or (proof-is-call term *b2-floor-intervals-mod*)
                  (proof-is-call term *b2-floor-translation-rem*))
              (proof-with-checked-results
                  ((opened (proof-proof-unfold (library-library-proof lib) term))
                   (equation (proof-step-first opened))
                   (expansion (proof-term-at equation 2))
                   (typed (b2-floor-translation-rational-type-run (1- n) lib expansion known solver))
                   (lib (b2-numeric-types-types-lib (cdr typed)))
                   (result (library-library-transport-argument lib (car typed) opened 1)))
                (cons result (cdr typed))))
             (t (proof-with-checked-results
                    ((head (proof-term-at term 0)))
                  (let ((operation (assoc-equal head *b2-floor-translation-rational-ops*)))
                    (if operation
                        (proof-with-checked-results
                            ((evidence (b2-floor-translation-rational-type-parts (1- n) lib (cdr term) known solver))
                             (lib (b2-numeric-types-types-lib (cdr evidence)))
                             (result (b2-scaling-rational-op lib (cdr operation) term (car evidence))))
                          (cons result (cdr evidence)))
                      '(:failure "tactic-rejected" "")))))))))

 (defun b2-floor-translation-rational-type-parts (n lib terms known solver)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b2-floor-translation-rational-type-parts"))
         ((endp terms) (cons nil solver))
         (t (proof-with-checked-results
                ((first (b2-floor-translation-rational-type-run (1- n) lib (car terms) known solver))
                 (lib (b2-numeric-types-types-lib (cdr first)))
                 (rest (b2-floor-translation-rational-type-parts (1- n) lib (cdr terms) known (cdr first))))
              (cons (cons (car first) (car rest)) (cdr rest)))))))

(defun b2-floor-translation-rational-type (lib term known solver)
  (b2-floor-translation-rational-type-run
   1000000 lib term known (b2-numeric-types-types-with-library solver lib)))

(defun b2-floor-translation-unique-integer-prove-too-far
    (before after strict upper lower lib sure kinds goal)
  (proof-with-checked-results
      ((reaches (b2-butlast-integer-after-successor lib strict kinds))
       (ratio-type (b2-quotient-algebra-required-evidence sure (list *library-rationalp* *library-x*)))
       (successor-type (library-library-rational lib (library-plus *proof-one* before) kinds))
       (after-type (library-library-rational lib after kinds))
       (upper (b2-quotient-algebra-required-evidence sure upper))
       (outside (b2-rational-order-rational-order-chain lib upper reaches
                                                       (list ratio-type successor-type after-type)))
       (lower (b2-quotient-algebra-required-evidence sure lower)))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((contradiction (proof-proof-cut proof outside lower)))
        (proof-proof-subsume proof contradiction (cons goal (proof-step-clause contradiction)))))))

(defun b2-floor-translation-unique-integer-prove-branch-reverse
    (later facts lib sure kinds goal two lo)
  (if later
      (b2-floor-translation-unique-integer-prove-too-far
       *library-z* *library-y* (car (last facts)) two lo lib sure kinds goal)
    (let ((delta (library-diff *library-y* *library-z*))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((negative (library-library-axiom lib "<-ON-OTHERS" (list *library-y* *library-z*)))
           (positive (library-library-comparison lib *library-z* *library-y* kinds))
           (nr (proof-proof-rewrite proof (nth (- (len facts) 2) facts) negative '(1 1)))
           (nr (proof-proof-tidy proof nr))
           (np (proof-proof-rewrite proof (car (last facts)) positive '(1 1)))
           (np (proof-proof-tidy proof np))
           (typed (library-library-type-of lib delta kinds))
           (zero (b2-powers-zero-from-signs lib delta typed nr np))
           (reduced (b2-tactics-tactics-linear-equal
                     lib (library-plus delta *library-z*) *library-y* kinds))
           (reduced (proof-proof-rewrite proof reduced zero '(1 1 1)))
           (unit (library-library-cite lib "ADD-ZERO-LEFT" (list *library-z*) (list (cadr kinds))))
           (result (proof-proof-rewrite proof reduced unit '(1 1)))
           (result (proof-proof-tidy proof result)))
        (proof-proof-symmetric proof result)))))

(defun b2-floor-translation-unique-integer-prove-branch
    (earlier cases lib sure kinds goal one two lo hi)
  (if earlier
      (b2-floor-translation-unique-integer-prove-too-far
       *library-y* *library-z* (car (last cases)) one hi lib sure kinds goal)
    (let ((test (library-lt *library-z* *library-y*)))
      (proof-with-checked-results
          ((request (b2-tactics-choose lib test cases nil))
           (first (b2-floor-translation-unique-integer-prove-branch-reverse
                   (nth 3 (car request)) (nth 4 (car request)) (cdr request) sure kinds goal two lo))
           (first (cons first (cdr request)))
           (next (b2-tactics-choose lib test cases (list first))))
        (if (eq (caar next) :call)
            (proof-with-checked-results
                ((second (b2-floor-translation-unique-integer-prove-branch-reverse
                          (nth 3 (car next)) (nth 4 (car next)) (cdr next) sure kinds goal two lo))
                 (result (b2-tactics-choose lib test cases (list first (cons second (cdr next))))))
              (car result))
          (car next))))))

(defun b2-floor-translation-unique-integer-prove (premise lib goal one two lo hi)
  (let ((test (library-lt *library-y* *library-z*)))
    (proof-with-checked-results
        ((sure (b2-tactics-tactics-evidence lib (list premise)))
         (typed-y (b2-quotient-algebra-required-evidence sure (library-integer *library-y*)))
         (typed-z (b2-quotient-algebra-required-evidence sure (library-integer *library-z*)))
         (kinds (list typed-y typed-z))
         (request (b2-tactics-choose lib test nil nil))
         (first (b2-floor-translation-unique-integer-prove-branch
                 (nth 3 (car request)) (nth 4 (car request)) (cdr request) sure kinds goal one two lo hi))
         (first (cons first (cdr request)))
         (next (b2-tactics-choose lib test nil (list first))))
      (if (eq (caar next) :call)
          (proof-with-checked-results
              ((second (b2-floor-translation-unique-integer-prove-branch
                        (nth 3 (car next)) (nth 4 (car next)) (cdr next) sure kinds goal one two lo hi)))
            (b2-tactics-choose lib test nil (list first (cons second (cdr next)))))
        next))))

(defun b2-floor-translation-add-unique-integer (lib)
  (let* ((one (library-lt *library-x* (library-plus *proof-one* *library-y*)))
         (two (library-lt *library-x* (library-plus *proof-one* *library-z*)))
         (lo (proof-neg (library-lt *library-x* *library-y*)))
         (hi (proof-neg (library-lt *library-x* *library-z*)))
         (goal (proof-eq *library-y* *library-z*)))
    (proof-with-checked-results
        ((condition (b2-powers-and-terms
                     (list (list *library-rationalp* *library-x*) (library-integer *library-y*)
                           (library-integer *library-z*) lo one hi two)))
         (request (b2-tactics-tactics-implication lib condition goal nil))
         (reply (b2-floor-translation-unique-integer-prove
                 (nth 3 (car request)) (cdr request) goal one two lo hi))
         (implication (b2-tactics-tactics-implication lib condition goal reply))
         (added (b2-tactics-tactics-add-lemma (cdr implication) "FLOOR-UNIQUE" (car implication) :none)))
      (cdr added))))

(defun b2-floor-translation-unique-integer
    (lib ratio first second ratio-type first-type second-type first-bounds second-bounds)
  (let ((name (proof-sym "B2-FLOOR-UNIQUE" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b2-floor-translation-add-unique-integer lib))))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((fact (proof-proof-fact proof name (list (list *library-x* ratio) (list *library-y* first)
                                                     (list *library-z* second))))
             (formula (proof-step-first fact))
             (condition (proof-term-at formula 1))
             (guard-step (b2-tactics-tactics-solve
                          lib condition (append (list ratio-type first-type second-type)
                                                first-bounds second-bounds) nil nil 0 nil))
             (result (proof-proof-modus-ponens proof fact guard-step)))
          (cons result lib))))))

(defun b2-floor-translation-ratio (a b)
  (b2-products-product a (list *b2-products-recip* b)))

(defun b2-floor-translation-divide-add (lib a b divisor)
  (let ((reciprocal (list *b2-products-recip* divisor))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((former (library-library-axiom lib "COMMUTATIVITY-OF-*"
                                       (list (library-plus a b) reciprocal)))
         (distributed (library-library-axiom lib "DISTRIBUTIVITY" (list reciprocal a b)))
         (rule (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal a)))
         (distributed (proof-proof-rewrite proof distributed rule '(1 2 1)))
         (rule (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal b)))
         (distributed (proof-proof-rewrite proof distributed rule '(1 2 2))))
      (proof-proof-chain proof former (list distributed)))))

(defun b2-floor-translation-shift-floor (lib a b divisor offset typed-offset shift known solver)
  (let* ((x (b2-floor-translation-ratio a divisor))
         (y (b2-floor-translation-ratio b divisor))
         (q (list *b2-floor-intervals-floor* a divisor))
         (p (list *b2-floor-intervals-floor* b divisor))
         (expected (library-plus offset p)))
    (proof-with-checked-results
        ((base-type (b2-numeric-types-types-floor
                     (b2-numeric-types-types-with-library solver lib) b divisor))
         (floor-type (b2-numeric-types-types-floor (cdr base-type) a divisor))
         (lib (b2-numeric-types-types-lib (cdr floor-type)))
         (typed (library-library-type-of lib expected (list typed-offset (car base-type))))
         (rational (b2-floor-translation-rational-type-parts 1000000 lib (list a b divisor x)
                                                             known (cdr floor-type)))
         (types (car rational))
         (lib (b2-numeric-types-types-lib (cdr rational)))
         (first (b2-floor-intervals-floor-interval lib a divisor (car types) (caddr types)))
         (second (b2-floor-intervals-floor-interval (cdr first) b divisor (cadr types) (caddr types)))
         (lib (cdr second)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((add-low (b2-algebra-cancel-common-shift lib offset y p))
             (add-high (b2-algebra-cancel-common-shift lib offset y (library-plus *proof-one* p)))
             (add-low (proof-proof-symmetric proof add-low))
             (lifted (proof-proof-rewrite proof (caar second) add-low '(1 1)))
             (lifted (proof-proof-tidy proof lifted))
             (reverse (proof-proof-symmetric proof shift))
             (lifted (proof-proof-rewrite proof lifted reverse '(1 1 1)))
             (lifted (proof-proof-tidy proof lifted))
             (strict (proof-proof-transport proof (cadar second) add-high))
             (reverse (proof-proof-symmetric proof shift))
             (strict (proof-proof-rewrite proof strict reverse '(1 1)))
             (swap (library-library-cite lib "ADD-SWAP" (list offset *proof-one* p) nil))
             (strict (proof-proof-rewrite proof strict swap '(1 2)))
             (strict (proof-proof-tidy proof strict))
             (result (b2-floor-translation-unique-integer lib x q expected (cadddr types)
                                                           (car floor-type) typed (car first)
                                                           (list lifted strict))))
          (cons (car result) (b2-numeric-types-types-with-library (cdr rational) (cdr result))))))))

(defun b2-floor-translation-remainder-as-product (lib a d known solver remainder)
  (let* ((q (list (if (equal remainder *b2-floor-intervals-mod*)
                     *b2-floor-intervals-floor*
                   *b2-numeric-types-truncate*) a d))
         (r (b2-floor-translation-ratio a d)))
    (proof-with-checked-results
        ((ra (b2-floor-translation-rational-type lib a known solver))
         (rd (b2-floor-translation-rational-type-run 1000000
               (b2-numeric-types-types-lib (cdr ra)) d known (cdr ra)))
         (lib (b2-numeric-types-types-lib (cdr rd)))
         (nonzero (b2-quotient-algebra-require-nonzero lib d known))
         (restores (b2-floor-intervals-scaled-dividend lib a d (car ra) (car rd) nonzero))
         (multiplied (library-library-axiom lib "DISTRIBUTIVITY" (list d r (library-minus q))))
         (negative-factor (b2-fraction-reduction-negative-factor lib d q))
         (lib (cdr negative-factor)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((multiplied (proof-proof-rewrite proof multiplied (car negative-factor) '(1 2 2)))
             (multiplied (proof-proof-rewrite proof multiplied restores '(1 2 1)))
             (opened (proof-proof-unfold proof (list remainder a d)))
             (swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (list q d)))
             (opened (proof-proof-rewrite proof opened swap '(1 2 2 1)))
             (multiplied (proof-proof-tidy proof multiplied))
             (multiplied (proof-proof-symmetric proof multiplied))
             (result (proof-proof-chain proof opened (list multiplied))))
          (cons result (b2-numeric-types-types-with-library (cdr rd) lib)))))))

(defun b2-floor-translation-shifted-value (lib operation a b divisor offset typed shifted known solver)
  (proof-with-checked-results
      ((floor (b2-floor-translation-shift-floor lib a b divisor offset typed shifted known solver)))
    (if (equal operation *b2-floor-intervals-floor*)
        floor
      (proof-with-checked-results
          ((lib (b2-numeric-types-types-lib (cdr floor)))
           (first (b2-floor-translation-remainder-as-product lib a divisor known (cdr floor)
                                                             *b2-floor-intervals-mod*))
           (lib (b2-numeric-types-types-lib (cdr first)))
           (last (b2-floor-translation-remainder-as-product lib b divisor known (cdr first)
                                                            *b2-floor-intervals-mod*))
           (lib (b2-numeric-types-types-lib (cdr last))))
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((first (proof-proof-rewrite proof (car first) (car floor) '(1 2 2 2 1)))
               (first (proof-proof-rewrite proof first shifted '(1 2 2 1)))
               (remove (b2-algebra-cancel-shift-difference lib offset (b2-floor-translation-ratio b divisor)
                                                           (list *b2-floor-intervals-floor* b divisor)))
               (first (proof-proof-rewrite proof first remove '(1 2 2)))
               (reverse (proof-proof-symmetric proof (car last)))
               (result (proof-proof-chain proof first (list reverse))))
            (cons result (cdr last))))))))

(defun b2-floor-translation-integer-multiple-p (literal known inverse)
  (if (proof-is-call literal *proof-equal*)
      (proof-with-checked-results
          ((left (proof-term-at literal 1)))
        (if (assoc-equal (list *proof-integerp* left) known)
            (proof-with-checked-results
                ((right (proof-term-at literal 2)))
              (if (proof-is-call right *proof-times*)
                  (proof-with-checked-results
                      ((factor (proof-term-at right 2)))
                    (equal factor inverse))
                nil))
          nil))
    nil))

(defun b2-floor-translation-integer-multiple-items (entries known inverse)
  (if (endp entries)
      '(:failure "failure" "")
    (proof-with-checked-results
        ((matches (b2-floor-translation-integer-multiple-p (caar entries) known inverse)))
      (if matches
          (cdar entries)
        (b2-floor-translation-integer-multiple-items (cdr entries) known inverse)))))

(defun b2-floor-translation-integer-multiple (known divisor)
  (b2-floor-translation-integer-multiple-items known known (list *b2-products-recip* divisor)))

(defun b2-floor-translation-cancel-addition-shift (lib a b divisor increment offset restore)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((args (proof-list-of-length (seq-slice a 1 :none) 2))
         (split (b2-floor-translation-divide-add lib (car args) (cadr args) divisor)))
      (cond ((equal (car args) increment)
             (proof-with-checked-results
                 ((shifted (proof-proof-rewrite proof split restore '(1 2 1))))
               (proof-proof-tidy proof shifted)))
            ((equal (cadr args) increment)
             (proof-with-checked-results
                 ((shifted (proof-proof-rewrite proof split restore '(1 2 2)))
                  (swap (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                               (list (b2-floor-translation-ratio b divisor) offset))))
               (proof-proof-chain proof shifted (list swap))))
            (t (proof-with-checked-results
                   ((inner (proof-list-of-length (cadr args) 3)))
                 (let* ((w (car args))
                        (x (cadr inner))
                        (rw (b2-floor-translation-ratio w divisor))
                        (rx (b2-floor-translation-ratio x divisor)))
                   (proof-with-checked-results
                       ((nested (b2-floor-translation-divide-add lib x increment divisor))
                        (shifted (proof-proof-rewrite proof split nested '(1 2 2)))
                        (shifted (proof-proof-rewrite proof shifted restore '(1 2 2 2)))
                        (swap (library-library-axiom lib "COMMUTATIVITY-OF-+" (list rx offset)))
                        (shifted (proof-proof-rewrite proof shifted swap '(1 2 2)))
                        (swap (library-library-cite lib "ADD-SWAP" (list rw offset rx) nil))
                        (shifted (proof-proof-chain proof shifted (list swap)))
                        (divided (b2-floor-translation-divide-add lib w x divisor))
                        (reverse (proof-proof-symmetric proof divided))
                        (shifted (proof-proof-rewrite proof shifted reverse '(1 2 2))))
                     (proof-proof-tidy proof shifted)))))))))

(defun b2-floor-translation-cancel-addition-equations (equations lib divisor offset increment restore known solver)
  (if (endp equations)
      (cons nil solver)
    (proof-with-checked-results
        ((equation (proof-list-of-length (car equations) 3))
         (call (proof-list-of-length (cadr equation) 3))
         (operation (car call))
         (a (cadr call))
         (original (caddr equation))
         (base (if (equal operation *b2-floor-intervals-floor*) (proof-term-at original 2) original))
         (b (proof-term-at base 1))
         (shifted (b2-floor-translation-cancel-addition-shift lib a b divisor increment offset restore))
         (typed (b2-quotient-algebra-required-evidence known (list *proof-integerp* offset)))
         (first (b2-floor-translation-shifted-value lib operation a b divisor offset typed shifted known solver))
         (lib (b2-numeric-types-types-lib (cdr first)))
         (rest (b2-floor-translation-cancel-addition-equations
                (cdr equations) lib divisor offset increment restore known (cdr first))))
      (cons (cons (car first) (car rest)) (cdr rest)))))

(defun b2-floor-translation-cancel-addition (lib formula known solver)
  (let ((equations (if (proof-is-call formula *proof-if*)
                       (seq-slice formula 1 3)
                     (list formula))))
    (proof-with-checked-results
        ((equation (proof-term-at equations 0))
         (equation (proof-list-of-length equation 3))
         (call (proof-list-of-length (cadr equation) 3))
         (divisor (caddr call))
         (given (b2-floor-translation-integer-multiple known divisor))
         (given-first (proof-step-first given))
         (given-first (proof-list-of-length given-first 3))
         (offset (cadr given-first))
         (scaled (proof-list-of-length (caddr given-first) 3))
         (increment (cadr scaled))
         (restore (proof-proof-symmetric (library-library-proof lib) given))
         (outputs (b2-floor-translation-cancel-addition-equations
                   equations lib divisor offset increment restore known solver))
         (lib (b2-numeric-types-types-lib (cdr outputs)))
         (result (b2-tactics-tactics-solve lib formula (car outputs) nil nil 0 nil)))
      (cons result (cdr outputs)))))

(defun b2-floor-translation-regroup-sum (lib a b c d)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list a b (library-plus c d))))
         (swap (library-library-cite lib "ADD-SWAP" (list b c d) nil))
         (equation (proof-proof-rewrite proof equation swap '(1 2 2)))
         (association (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list a c (library-plus b d))))
         (reverse (proof-proof-symmetric proof association)))
      (proof-proof-chain proof equation (list reverse)))))

(defun b2-floor-translation-divided-remainder (lib a d known solver)
  (let* ((remainder (list *b2-floor-intervals-mod* a d))
         (quotient (list *b2-floor-intervals-floor* a d))
         (before (b2-floor-translation-ratio a d))
         (after (b2-floor-translation-ratio remainder d))
         (part (library-diff before quotient)))
    (proof-with-checked-results
        ((expressed (b2-floor-translation-remainder-as-product
                     lib a d known solver *b2-floor-intervals-mod*))
         (lib (b2-numeric-types-types-lib (cdr expressed)))
         (proof (library-library-proof lib))
         (reduced (b2-algebra-congruence lib (car expressed) after '(1)))
         (swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (list d part)))
         (reduced (proof-proof-rewrite proof reduced swap '(1 2 1)))
         (rational (b2-floor-translation-rational-type lib part known (cdr expressed)))
         (new-known (table-put known (list *library-rationalp* part) (car rational)))
         (lib (b2-numeric-types-types-lib (cdr rational)))
         (proof (library-library-proof lib))
         (cancel (b2-quotient-algebra-cancel-to-value lib part d new-known))
         (entry (proof-proof-chain proof reduced (list cancel)))
         (equation (b2-algebra-congruence lib entry (library-plus quotient after) '(2)))
         (swap (library-library-cite lib "ADD-SWAP" (list quotient before (library-minus quotient)) nil))
         (equation (proof-proof-chain proof equation (list swap)))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list quotient)))
         (equation (proof-proof-rewrite proof equation inverse '(1 2 2)))
         (rat (b2-floor-translation-rational-type lib before known (cdr rational)))
         (lib (b2-numeric-types-types-lib (cdr rat)))
         (proof (library-library-proof lib))
         (swap (library-library-axiom lib "COMMUTATIVITY-OF-+" (list before *proof-zero*)))
         (numeric (b2-scaling-number-of-rational lib before (car rat)))
         (unit (b2-fraction-reduction-sum-unit lib before numeric))
         (removed (proof-proof-chain proof swap (list unit)))
         (result (proof-proof-chain proof equation (list removed)))
         (result (proof-proof-symmetric proof result)))
      (cons result (cdr rat)))))

(defun b2-floor-translation-add-remainders (lib formula known solver)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (proof-list-of-length (cadr parts) 3))
       (args (proof-list-of-length (seq-slice (cadr call) 1 :none) 2)))
    (let* ((op (car call))
           (a (cadr call))
           (d (caddr call))
           (x (car args))
           (y (cadr args))
           (qx (list *b2-floor-intervals-floor* x d))
           (qy (list *b2-floor-intervals-floor* y d))
           (mx (list *b2-floor-intervals-mod* x d))
           (my (list *b2-floor-intervals-mod* y d))
           (b (library-plus mx my)))
      (proof-with-checked-results
          ((equation (b2-floor-translation-divide-add lib x y d))
           (left (b2-floor-translation-divided-remainder lib x d known solver))
           (lib (b2-numeric-types-types-lib (cdr left)))
           (equation (proof-proof-rewrite (library-library-proof lib) equation (car left) '(1 2 1)))
           (right (b2-floor-translation-divided-remainder lib y d known (cdr left)))
           (lib (b2-numeric-types-types-lib (cdr right)))
           (proof (library-library-proof lib))
           (equation (proof-proof-rewrite proof equation (car right) '(1 2 2)))
           (paired (b2-floor-translation-regroup-sum lib qx (b2-floor-translation-ratio mx d)
                                                     qy (b2-floor-translation-ratio my d)))
           (shifted (proof-proof-chain proof equation (list paired)))
           (division (b2-floor-translation-divide-add lib mx my d))
           (reverse (proof-proof-symmetric proof division))
           (shifted (proof-proof-rewrite proof shifted reverse '(1 2 2)))
           (shifted (proof-proof-tidy proof shifted))
           (offset (library-plus qx qy))
           (typed-x (b2-numeric-types-types-floor (cdr right) x d))
           (typed-y (b2-numeric-types-types-floor (cdr typed-x) y d))
           (lib (b2-numeric-types-types-lib (cdr typed-y)))
           (typed (library-library-type-of lib offset (list (car typed-x) (car typed-y))))
           (result (b2-floor-translation-shifted-value lib op a b d offset typed shifted known (cdr typed-y))))
        (if (equal op *b2-floor-intervals-floor*)
            (proof-with-checked-results
                ((lib (b2-numeric-types-types-lib (cdr result)))
                 (commuted (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                                 (list offset (list *b2-floor-intervals-floor* b d))))
                 (step (proof-proof-chain (library-library-proof lib) (car result) (list commuted))))
              (cons step (cdr result)))
          result)))))

(defun b2-floor-translation-divided-mod (lib formula known solver)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (proof-list-of-length (cadr parts) 3))
       (a (cadr call))
       (args (proof-list-of-length a 3)))
    (let* ((op (car call))
           (d (caddr call))
           (x (cadr args))
           (divisor (caddr args))
           (q (list *b2-floor-intervals-floor* x divisor))
           (reciprocal (list *b2-products-recip* d))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((given (b2-floor-translation-integer-multiple known d))
           (given-first (proof-step-first given))
           (index (proof-term-at given-first 1))
           (raw (proof-proof-unfold proof a))
           (raw-eq (proof-step-first raw))
           (expression (proof-term-at raw-eq 2))
           (opposite (proof-term-at expression 2))
           (factor (proof-term-at opposite 1))
           (quotient (b2-algebra-congruence lib raw (b2-floor-translation-ratio a d) '(1)))
           (division (b2-floor-translation-divide-add lib x (library-minus factor) d))
           (quotient (proof-proof-chain proof quotient (list division)))
           (negative-first (b2-fraction-reduction-negative-first lib factor reciprocal))
           (lib (cdr negative-first))
           (proof (library-library-proof lib))
           (quotient (proof-proof-rewrite proof quotient (car negative-first) '(1 2 2)))
           (association (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list q divisor reciprocal)))
           (quotient (proof-proof-rewrite proof quotient association '(1 2 2 1)))
           (reverse (proof-proof-symmetric proof given))
           (quotient (proof-proof-rewrite proof quotient reverse '(1 2 2 1 2)))
           (swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (list q index)))
           (quotient (proof-proof-rewrite proof quotient swap '(1 2 2 1)))
           (offset (library-minus (b2-products-product index q)))
           (swap (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                       (list (b2-floor-translation-ratio x d) offset)))
           (shifted (proof-proof-chain proof quotient (list swap)))
           (typed-index (b2-quotient-algebra-required-evidence known (list *proof-integerp* index)))
           (typed-q (b2-numeric-types-types-floor (b2-numeric-types-types-with-library solver lib) x divisor))
           (lib (b2-numeric-types-types-lib (cdr typed-q)))
           (int-offset (library-library-type-of lib offset (list typed-index (car typed-q))))
           (translated (b2-floor-translation-shifted-value lib op a x d offset int-offset
                                                           shifted known (cdr typed-q))))
        (if (equal op *b2-floor-intervals-floor*)
            (proof-with-checked-results
                ((lib (b2-numeric-types-types-lib (cdr translated)))
                 (swap (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                              (list offset (list *b2-floor-intervals-floor* x d))))
                 (result (proof-proof-chain (library-library-proof lib) (car translated) (list swap))))
              (cons result (cdr translated)))
          translated)))))

(defun b2-floor-translation-floor-translation-theorem-establish (premise lib name result solver)
  (proof-with-checked-results
      ((known (b2-quotient-algebra-with-forced lib premise))
       (result (cond ((member-equal name *b2-floor-translation-rewrite-mod*)
                      (b2-floor-translation-divided-mod lib result known solver))
                     ((or (equal name *b2-floor-translation-add-floor*)
                          (equal name *b2-floor-translation-add-mod*))
                      (b2-floor-translation-add-remainders lib result known solver))
                     (t (b2-floor-translation-cancel-addition lib result known solver)))))
    (cons (car result) (b2-numeric-types-types-lib (cdr result)))))

(defun b2-floor-translation-floor-translation-theorem (lib name formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (result (caddr parts))
       (solver (b2-numeric-types-types-init lib))
       (request (b2-tactics-tactics-implication lib condition result nil))
       (reply (b2-floor-translation-floor-translation-theorem-establish
               (nth 3 (car request)) (cdr request) name result solver)))
    (b2-tactics-tactics-implication lib condition result reply)))
