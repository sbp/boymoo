(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-shapes-head (term)
  (if (and (proof-compound term) (consp term))
      (car term)
    :none))

(defun b1-shapes-check-indexable (term)
  (and (or (eq term :none) (eq term t) (rationalp term))
       '(:failure "failure" "")))

(defun b1-shapes-at (term index)
  (or (b1-shapes-check-indexable term)
      (if (stringp term)
          (if (< index (length term))
              (subseq term index (1+ index))
            '(:failure "failure" ""))
        (proof-term-at term index))))

(defun b1-shapes-tail (term)
  (or (b1-shapes-check-indexable term)
      (if (stringp term) (seq-slice term 1 :none) (cdr term))))

(defun b1-shapes-split-goal (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results
       ((test (b1-shapes-at formula 1))
        (goal (b1-shapes-at formula 2)))
       (list test goal))
    (list :none formula)))

(defun b1-shapes-conjuncts (test)
  (cond
   ((eq test :none) nil)
   ((proof-is-call test *proof-if*)
    (cond
     ((not (consp (cdddr test))) '(:failure "failure" ""))
     ((equal (cadddr test) *proof-false*)
      (proof-with-checked-results
       ((rest (b1-shapes-conjuncts (caddr test))))
       (cons (cadr test) rest)))
     (t (list test))))
   (t (list test))))

(defun b1-shapes-any-conjunct-call (test operator)
  (cond
   ((eq test :none) nil)
   ((proof-is-call test *proof-if*)
    (cond
     ((not (consp (cdddr test))) '(:failure "failure" ""))
     ((equal (cadddr test) *proof-false*)
      (or (proof-is-call (cadr test) operator)
          (b1-shapes-any-conjunct-call (caddr test) operator)))
     (t (proof-is-call test operator))))
   (t (proof-is-call test operator))))

(defconst *b1-shapes-list-operations*
  (list
   (cons *proof-cons* 'b1-abstract-lists-abstract-list-cons)
   (cons *library-cdr* 'b1-abstract-lists-abstract-list-cdr)
   (cons *b1-revappend-append* 'b1-abstract-lists-abstract-list-append)
   (cons *b1-revappend-rev* 'b1-abstract-lists-reuse-abstract-list)
   (cons (proof-cl "REVERSE") 'b1-abstract-lists-abstract-list-reverse)
   (cons (proof-cl "NTHCDR") 'b1-abstract-lists-abstract-list-nthcdr)
   (cons (proof-sym "MAKE-LIST-AC" "ACL2") 'b1-abstract-lists-abstract-make-list)
   (cons (proof-sym "PUT-NTH" "ACL2") 'b1-abstract-lists-abstract-list-put-nth)
   (cons (proof-cl "BUTLAST") 'b1-abstract-lists-abstract-list-butlast)
   (cons (proof-cl "TAKE") 'b1-abstract-lists-abstract-list-bounded-operation)
   (cons (proof-sym "TAKE" "ACL2") 'b1-abstract-lists-abstract-list-bounded-operation)
   (cons (proof-sym "UPDATE-NTH" "ACL2") 'b1-abstract-lists-abstract-list-bounded-operation)
   (cons (proof-cl "SUBSEQ") 'b1-abstract-lists-abstract-list-subseq)
   (cons (proof-cl "LAST") 'b1-abstract-lists-reuse-abstract-list)
   (cons (proof-sym "FIRSTN" "ACL2") 'b1-abstract-lists-reuse-abstract-list)
   (cons (proof-sym "NTH-SEG" "ACL2") 'b1-abstract-lists-reuse-abstract-list)
   (cons (proof-sym "PUT-SEG" "ACL2") 'b1-abstract-lists-reuse-abstract-list)
   (cons (proof-sym "REMOVE-EQUAL" "ACL2") 'b1-abstract-lists-reuse-abstract-list)
   (cons (proof-sym "REMOVE-DUPLICATES-EQUAL" "ACL2")
         'b1-abstract-lists-reuse-abstract-list)))

(defun b1-shapes-source-type (lib node index)
  (proof-with-checked-results
   ((signature (b1-abstract-lists-list-signature lib (b1-shapes-head node) index)))
   (and signature (list node signature))))

(defun b1-shapes-source-types (lib test index)
  (cond
   ((eq test :none) nil)
   ((and (proof-is-call test *proof-if*) (not (consp (cdddr test))))
    '(:failure "failure" ""))
   ((and (proof-is-call test *proof-if*) (equal (cadddr test) *proof-false*))
    (proof-with-checked-results
     ((typed (b1-shapes-source-type lib (cadr test) index))
      (rest (b1-shapes-source-types lib (caddr test) index)))
     (if typed (cons typed rest) rest)))
   (t (proof-with-checked-results
       ((typed (b1-shapes-source-type lib test index)))
       (and typed (list typed))))))

(defun b1-shapes-abstract-list-member-recipe (nodes)
  (cond
   ((endp nodes) nil)
   ((proof-is-call (car nodes) *b1-revappend-member*)
    'b1-abstract-lists-abstract-list-member)
   ((proof-is-call (car nodes) *b1-set-laws-memberp*)
    'b1-abstract-lists-abstract-list-memberp)
   (t (b1-shapes-abstract-list-member-recipe (cdr nodes)))))

(defun b1-shapes-abstract-list-recipe-with-index (lib test goal subject index)
  (declare (ignore goal))
  (proof-with-checked-results
   ((source-types (b1-shapes-source-types lib test index)))
   (if (and (proof-is-call subject *b1-printing-true-listp*) source-types)
       'b1-abstract-lists-abstract-list-proper
     (proof-with-checked-results
      ((signature (b1-abstract-lists-list-signature lib (b1-shapes-head subject) index)))
      (if signature
          (proof-with-checked-results
           ((arg (b1-shapes-at subject (car signature))))
           (cdr (assoc-equal (b1-shapes-head arg) *b1-shapes-list-operations*)))
        (and source-types
             (proof-with-checked-results
              ((nodes (b1-shapes-conjuncts test)))
              (or (b1-shapes-abstract-list-member-recipe nodes)
                  (and (proof-is-call subject (proof-sym "INITIAL-SUBLISTP-EQUAL" "ACL2"))
                       'b1-abstract-lists-abstract-list-initial-sublist)
                  (let ((position (car (cadar source-types))))
                    (and (proof-compound subject)
                         (< position (len subject))
                         (let ((operation (b1-shapes-head (nth position subject))))
                           (cond
                            ((equal operation *library-car*) 'b1-abstract-lists-abstract-list-car)
                            ((equal operation (proof-cl "NTH")) 'b1-abstract-lists-abstract-list-nth)
                            (t nil)))))))))))))

(defun b1-shapes-revappend-recipe (test goal subject)
  (or
   (and (proof-is-call goal *b1-revappend-iff*)
        (or
         (and (proof-is-call subject *b1-revappend-rev*)
              'b1-revappend-revappend-nonempty)
         (and (proof-is-call subject *b1-revappend-member*)
              (proof-with-checked-results
               ((right (b1-shapes-at subject 2)))
               (and (proof-is-call right *b1-revappend-rev*) 'b1-revappend-member-of-revappend)))
         (and (proof-is-call subject *b1-revappend-intersection*)
              (proof-with-checked-results
               ((left (b1-shapes-at subject 1)))
               (if (proof-is-call left *b1-revappend-rev*)
                   'b1-revappend-intersects-reversed-first
                 (proof-with-checked-results
                  ((right (b1-shapes-at subject 2)))
                  (and (proof-is-call right *b1-revappend-rev*)
                       'b1-revappend-intersects-reversed-second)))))))
   (and (proof-is-call goal *proof-equal*)
        (eq test :none)
        (or
         (and (proof-is-call subject *b1-revappend-rev*)
              (proof-with-checked-results
               ((left (b1-shapes-at subject 1)))
               (cond
                ((proof-is-call left *b1-revappend-fix*) 'b1-revappend-revappend-of-list-fix)
                ((proof-is-call left *b1-revappend-rev*) 'b1-revappend-reversed-twice)
                (t (proof-with-checked-results
                    ((right (b1-shapes-at subject 2)))
                    (and (proof-is-call right *b1-revappend-append*)
                         'b1-revappend-accumulator-commutation))))))
         (and (proof-compound subject)
              (equal (len subject) 2)
              (proof-is-call (cadr subject) *b1-revappend-rev*)
              (let ((operator (b1-shapes-head subject)))
                (cond
                 ((equal operator *library-car*) 'b1-revappend-car-of-revappend)
                 ((equal operator *library-cdr*) 'b1-revappend-cdr-of-revappend)
                 ((equal operator *proof-consp*) 'b1-revappend-consp-of-revappend)
                 ((equal operator *library-len*) 'b1-revappend-length-of-revappend)
                 ((equal operator *b1-revappend-fix*) 'b1-revappend-accumulator-commutation)
                 (t nil))))))))

(defun b1-shapes-association-recipe (test subject)
  (proof-with-checked-results
   ((typed (b1-shapes-any-conjunct-call test *b1-typed-alists-alist*)))
   (cond
    ((not typed) nil)
    ((proof-is-call subject (proof-sym "ALISTP" "ACL2")) 'b1-typed-alists-alist-type-is-alist)
    ((proof-is-call subject *b1-typed-alists-alist*)
     (proof-with-checked-results
      ((arg (b1-shapes-at subject 1)))
      (let ((operator (b1-shapes-head arg)))
        (cond
         ((equal operator (proof-cl "ACONS")) 'b1-typed-alists-alist-type-acons)
         ((or (equal operator (proof-sym "PAIRLIS$" "ACL2"))
              (equal operator (proof-sym "BIND-ALL-EQUAL" "ACL2")))
          'b1-typed-alists-paired-alist-type)
         ((member-equal operator (list *b1-revappend-append*
                                       (proof-sym "BIND-EQUAL" "ACL2")
                                       (proof-sym "REMBIND-EQUAL" "ACL2")
                                       (proof-sym "DOMAIN-RESTRICT-EQUAL" "ACL2")
                                       (proof-sym "BIND-PAIRS-EQUAL" "ACL2")))
          'b1-typed-alists-typed-alist-recursion)
         (t nil)))))
    ((member-equal (b1-shapes-head subject)
                   (list (proof-sym "DOMAIN-TYPE" "ACL2")
                         (proof-sym "RANGE-TYPE" "ACL2")))
     (proof-with-checked-results
      ((arg (b1-shapes-at subject 1)))
      (let ((operator (b1-shapes-head arg)))
        (cond
         ((member-equal operator (list (proof-sym "DOMAIN" "ACL2") (proof-sym "RANGE" "ACL2")))
          'b1-typed-alists-alist-projection-type)
         ((member-equal operator (list (proof-sym "COLLECT-BOUND-EQUAL" "ACL2")
                                       (proof-sym "ALL-BINDINGS-EQUAL" "ACL2")))
          'b1-typed-alists-types-of-bound-entries)
         (t nil)))))
    (t nil))))

(defconst *b1-shapes-set-operations*
  (list *b1-set-laws-union* *b1-set-laws-difference* *b1-revappend-intersection*))

(defconst *b1-shapes-member-operations*
  (append *b1-shapes-set-operations*
          (list (proof-sym "REMOVE-EQUAL" "ACL2")
                (proof-sym "REMOVE1-EQUAL" "ACL2")
                (proof-sym "REMOVE-DUPLICATES-EQUAL" "ACL2"))))

(defun b1-shapes-set-member-recipe (test goal subject)
  (proof-with-checked-results
   ((items (b1-shapes-at subject 2)))
   (let ((operation (b1-shapes-head items)))
     (cond
      ((and (proof-is-call goal *b1-revappend-iff*) (equal operation *b1-revappend-fix*))
       'b1-membership-member-of-fixed-list-iff)
      ((and (proof-is-call goal *proof-equal*) (equal operation *b1-revappend-fix*))
       'b1-membership-member-of-fixed-list)
      ((and (member-equal (b1-shapes-head goal) (list *proof-equal* *b1-revappend-iff*))
            (member-equal operation *b1-shapes-member-operations*))
       'b1-membership-member-of-set-operation)
      ((not (eq test :none))
       (proof-with-checked-results
        ((item (b1-shapes-at subject 1)))
        (and (proof-is-call item (proof-cl "NTH"))
             (proof-with-checked-results
              ((array (b1-shapes-at item 2)))
              (and (equal array items) 'b1-membership-member-at-index)))))
      (t nil)))))

(defun b1-shapes-set-subset-transitive (test goal)
  (proof-with-checked-results
   ((first (b1-shapes-at test 1))
    (second (b1-shapes-at test 2)))
   (and (proof-is-call first *b1-set-laws-subset*)
        (proof-is-call second *b1-set-laws-subset*)
        (proof-with-checked-results
         ((middle (b1-shapes-at first 2))
          (start (b1-shapes-at second 1)))
         (and (equal middle start)
              (proof-with-checked-results
               ((arguments (b1-shapes-tail goal))
                (left (b1-shapes-at first 1))
                (right (b1-shapes-at second 2)))
               (and (equal arguments (list left right))
                    'b1-set-laws-subset-transitive)))))))

(defun b1-shapes-set-subset-recipe (test goal subject)
  (or
   (and (eq test :none)
        (proof-with-checked-results
         ((left (b1-shapes-at subject 1))
          (right (b1-shapes-at subject 2)))
         (and (equal left right) 'b1-set-laws-subset-reflexive)))
   (and (proof-is-call goal *proof-equal*)
        (proof-with-checked-results
         ((right (b1-shapes-at subject 2)))
         (and (member-equal (b1-shapes-head right) *b1-shapes-set-operations*)
              'b1-set-laws-subset-of-set-operation)))
   (and (proof-is-call test *proof-if*)
        (b1-shapes-set-subset-transitive test goal))))

(defun b1-shapes-set-recipe (test goal subject)
  (or
   (and (proof-is-call subject *b1-list-sets-intersect*)
        (proof-is-call goal *proof-equal*)
        (proof-with-checked-results
         ((left (b1-shapes-at subject 1)))
         (and (proof-is-call left *b1-revappend-append*)
              'b1-list-sets-appended-first-intersection)))
   (and (proof-is-call subject *b1-list-sets-intersect*)
        (proof-is-call goal *b1-revappend-iff*)
        (proof-with-checked-results
         ((right (b1-shapes-at subject 2)))
         (and (proof-is-call right *proof-cons*)
              'b1-list-sets-intersection-with-extended-second)))
   (and (proof-is-call subject *b1-revappend-member*)
        (b1-shapes-set-member-recipe test goal subject))
   (and (proof-is-call subject *b1-set-laws-memberp*)
        (equal (b1-shapes-head goal) *proof-equal*)
        (proof-with-checked-results
         ((items (b1-shapes-at subject 2)))
         (and (member-equal (b1-shapes-head items)
                            (append *b1-shapes-set-operations* (list *b1-set-laws-adjoin*)))
              'b1-set-laws-memberp-of-set-operation)))
   (and (proof-is-call subject *b1-set-laws-setp*)
        (proof-with-checked-results
         ((items (b1-shapes-at subject 1)))
         (and (member-equal (b1-shapes-head items) *b1-shapes-set-operations*)
              'b1-set-laws-setp-under-operation)))
   (and (proof-is-call subject *b1-set-laws-subset*)
        (b1-shapes-set-subset-recipe test goal subject))
   (and (proof-is-call goal *b1-set-laws-set-equal*)
        (proof-with-checked-results
         ((known (b1-shapes-any-conjunct-call test *b1-set-laws-set-equal*)))
         (and known 'b1-set-laws-set-equal-law)))
   (and (proof-is-call goal *proof-not*)
        (proof-with-checked-results
         ((negative (b1-shapes-at goal 1)))
         (and (proof-is-call negative *b1-revappend-member*)
              (proof-with-checked-results
               ((items (b1-shapes-at negative 2)))
               (and (equal items *proof-false*) 'b1-membership-member-nil)))))
   (and (proof-is-call test *b1-revappend-member*)
        (proof-with-checked-results
         ((items (b1-shapes-at test 2)))
         (cond
          ((equal goal (list *proof-consp* items)) 'b1-membership-member-requires-cons)
          ((equal goal (list *b1-printing-true-listp* test)) 'b1-membership-member-proper)
          (t nil))))))

(defun b1-shapes-equality-of-fixes (lib term)
  (let* ((definitions (proof-proof-definitions (library-library-proof lib)))
         (definition (assoc-equal (b1-shapes-head term) definitions)))
    (and definition
         (not (eq (cdr definition) :none))
         (proof-with-checked-results
          ((parts (proof-list-of-length (cdr definition) 2)))
          (let ((body (cadr parts)))
            (and (member-equal (b1-shapes-head body)
                               (list *proof-equal* *b1-logic-eq* *b1-logic-eql*))
                 (proof-with-checked-results
                  ((left (b1-shapes-at body 1)))
                  (and (proof-compound left)
                       (proof-with-checked-results
                        ((right (b1-shapes-at body 2)))
                        (equal (b1-shapes-head left) (b1-shapes-head right)))))))))))

(defun b1-shapes-congruence-contrapositive-consequence (hypothesis lib equality conclusion)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((cut (proof-proof-cut proof equality hypothesis)))
     (proof-proof-front proof cut conclusion))))

(defun b1-shapes-congruence-contrapositive (lib formula)
  (proof-with-checked-results
   ((parts (proof-list-of-length formula 3))
    (alias-term (b1-shapes-at (caddr parts) 1))
    (alias-arguments (b1-shapes-tail alias-term))
    (alias-operands (proof-list-of-length alias-arguments 2))
    (premise-term (b1-shapes-at (cadr parts) 1))
    (premise-arguments (b1-shapes-tail premise-term))
    (premise-operands (proof-list-of-length premise-arguments 2)))
   (let ((proof (library-library-proof lib))
         (old (car alias-operands))
         (left (car premise-operands))
         (right (cadr premise-operands))
         (conclusion (caddr parts)))
     (proof-with-checked-results
      ((alias (proof-proof-assume proof alias-term t))
       (identity (proof-proof-reflexive proof left))
       (equality (proof-proof-rewrite-result proof identity alias (proof-eq *proof-result* left) old))
       (first (proof-step-first equality)))
      (and (equal first (proof-eq left right))
           (proof-with-checked-results
            ((hypothesis (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (b1-shapes-congruence-contrapositive-consequence
                           hypothesis lib equality conclusion)))
            (b1-logic-bookproof-prove-implication-with-premise lib formula hypothesis consequence)))))))

(defconst *b1-shapes-numerator* (proof-cl "NUMERATOR"))
(defconst *b1-shapes-denominator* (proof-cl "DENOMINATOR"))
(defconst *b1-shapes-inverse* (proof-sym "UNARY-/" "ACL2"))

(defun b1-shapes-all-calls (terms operator)
  (or (endp terms)
      (and (proof-is-call (car terms) operator)
           (b1-shapes-all-calls (cdr terms) operator))))

(defun b1-shapes-any-call (terms operator)
  (and (consp terms)
       (or (proof-is-call (car terms) operator)
           (b1-shapes-any-call (cdr terms) operator))))

(defun b1-shapes-negated-comparison-p (term)
  (and (proof-is-call term *proof-not*)
       (proof-with-checked-results
        ((negated (b1-shapes-at term 1)))
        (proof-is-call negated *proof-less*))))

(defun b1-shapes-exponent-recipe-signed (lib formula sign)
  (b1-powers-exponent-addition-goal lib formula sign))

(defun b1-shapes-exponent-guard-recipe (test)
  (proof-with-checked-results
   ((guards (b1-shapes-conjuncts test)))
   (and (equal (len guards) 4)
        (if (proof-is-call (cadr guards) *library-numberp*)
            'b1-powers-exponents-add-two
          (proof-with-checked-results
           ((first (b1-shapes-negated-comparison-p (car guards))))
           (and first
                (proof-with-checked-results
                 ((second (b1-shapes-negated-comparison-p (cadr guards))))
                 (and second
                      (proof-with-checked-results
                       ((bound (b1-shapes-at (cadar guards) 2)))
                       (list :exponent-addition-goal
                             (if (equal bound *proof-zero*) 1 -1)))))))))))

(defun b1-shapes-exponent-recipe (test goal)
  (cond
   ((proof-is-call goal *proof-less*)
    (proof-with-checked-results
     ((operands (proof-list-of-length (cdr goal) 2)))
     (let ((first (car operands)) (second (cadr operands)))
       (cond
        ((and (equal first *proof-zero*) (proof-is-call second *b1-quotient-expt*))
         'b1-parity-even-power-positive)
        ((and (equal second *proof-zero*) (proof-is-call first *b1-quotient-expt*))
         'b1-parity-odd-power-negative)
        ((and (proof-is-call first *b1-quotient-expt*)
              (proof-is-call second *b1-quotient-expt*))
         (proof-with-checked-results
          ((first-base (b1-shapes-at first 1))
           (second-base (b1-shapes-at second 1)))
          (and (equal first-base second-base) 'b1-monotone-increasing-power)))
        (t nil)))))
   ((proof-is-call goal *proof-equal*)
    (proof-with-checked-results
     ((operands (proof-list-of-length (cdr goal) 2)))
     (let ((left (car operands)) (right (cadr operands)))
       (cond
        ((and (proof-is-call left *proof-times*)
              (b1-shapes-all-calls (cdr left) *b1-quotient-expt*)
              (proof-is-call right *proof-if*))
         'b1-powers-exponent-addition-goal)
        ((proof-is-call left *b1-quotient-expt*)
         (proof-with-checked-results
          ((base (b1-shapes-at left 1)))
          (if (proof-is-call base *proof-times*)
              'b1-parity-negated-base
            (proof-with-checked-results
             ((exponent (b1-shapes-at left 2)))
             (and (proof-is-call exponent *proof-plus*)
                  (cond
                   ((proof-is-call right *proof-if*) 'b1-powers-exponent-addition-goal)
                   ((and (proof-is-call right *proof-times*)
                         (b1-shapes-all-calls (cdr right) *b1-quotient-expt*))
                    (b1-shapes-exponent-guard-recipe test))
                   (t nil)))))))
        (t nil)))))
   (t nil)))

(defun b1-shapes-remainder-premise-p (test)
  (and (proof-is-call test *proof-if*)
       (proof-with-checked-results
        ((first (b1-shapes-at test 1)))
        (and (proof-is-call first *proof-equal*)
             (proof-with-checked-results
              ((right (b1-shapes-at first 2)))
              (proof-is-call right *b1-modular-mod*))))))

(defun b1-shapes-arithmetic-comparison-recipe (test goal subject comparison)
  (or
   (and (proof-is-call test *proof-integerp*)
        (proof-compound comparison)
        (proof-with-checked-results
         ((value (b1-shapes-at comparison 1)))
         (and (proof-is-call value *b1-modular-mod*) 'b1-modular-remainder-consequence)))
   (and (proof-is-call goal *proof-not*)
        (proof-is-call comparison *proof-integerp*)
        (proof-is-call test *proof-if*)
        (proof-with-checked-results
         ((value (b1-shapes-at comparison 1)))
         (and (equal (seq-slice test 1 3)
                     (list (library-lt *proof-zero* value) (library-lt value *proof-one*)))
              'b1-integer-open-unit-interval)))
   (and (proof-is-call goal *proof-integerp*)
        (proof-with-checked-results
         ((value (b1-shapes-at subject 1)))
         (and (proof-is-call value *proof-times*)
              (proof-with-checked-results
               ((premise (b1-shapes-remainder-premise-p test)))
               (and premise 'b1-modular-exact-remainder-integral)))))))

(defun b1-shapes-arithmetic-numerator-recipe (test subject right)
  (proof-with-checked-results
   ((arg (b1-shapes-at subject 1)))
   (or
    (and (equal arg right)
         (cond
          ((proof-is-call test *proof-integerp*) 'b1-arithmetic-numerator-when-integer)
          ((proof-is-call test *proof-if*) 'b1-numerators-unit-denominator)
          (t nil)))
    (and (proof-is-call arg *proof-minus*)
         (proof-with-checked-results
          ((value (b1-shapes-at arg 1)))
          (and (equal right (list *proof-minus* (list *b1-shapes-numerator* value)))
               'b1-reduced-numerator-minus)))
    (and (proof-is-call arg *b1-shapes-inverse*)
         (proof-is-call right (proof-cl "SIGNUM"))
         'b1-numerators-reciprocal-numerator)
    (and (member-equal (b1-shapes-head arg) (list *proof-plus* *proof-times*))
         (proof-is-call right *proof-minus*)
         (proof-with-checked-results
          ((value (b1-shapes-at right 1)))
          (and (proof-is-call value *b1-shapes-numerator*)
               'b1-numerators-numerator-distribute-sign))))))

(defun b1-shapes-arithmetic-denominator-recipe (test subject right)
  (if (and (proof-is-call test *proof-integerp*) (equal right *proof-one*))
      'b1-arithmetic-denominator-when-integer
    (proof-with-checked-results
     ((arg (b1-shapes-at subject 1)))
     (and (proof-is-call arg *proof-minus*)
          (proof-with-checked-results
           ((value (b1-shapes-at arg 1)))
           (and (equal right (list *b1-shapes-denominator* value))
                'b1-reduced-denominator-minus))))))

(defun b1-shapes-arithmetic-equality-recipe (test subject right)
  (proof-with-checked-results
   ((operands (proof-list-of-length (cdr subject) 2)))
   (let ((first (car operands)) (second (cadr operands)))
     (cond
      ((and (eq test :none)
            (proof-is-call first *b1-shapes-denominator*)
            (equal second *proof-one*))
       'b1-arithmetic-denominator-one)
      ((and (eq test :none)
            (equal second (list *b1-shapes-numerator* first))
            (equal right (list *proof-integerp* first)))
       'b1-numerators-equal-numerator)
      ((and (proof-is-call right *proof-if*)
            (proof-is-call first *proof-times*)
            (equal second *proof-one*))
       'b1-arithmetic-inverse-uniqueness)
      ((and (proof-is-call right *proof-if*)
            (proof-is-call second *b1-shapes-inverse*)
            (not (eq test :none)))
       'b1-division-reciprocal-equality)
      ((and (proof-is-call right *proof-if*) (proof-is-call second *proof-times*))
       (proof-with-checked-results
        ((factor (b1-shapes-at second 1)))
        (and (proof-is-call factor *b1-shapes-inverse*) 'b1-division-multiply-division-equality)))
      (t nil)))))

(defun b1-shapes-arithmetic-product-recipe (subject)
  (proof-with-checked-results
   ((second (b1-shapes-at subject 2))
    (first (b1-shapes-at subject 1)))
   (cond
    ((equal second (list *b1-shapes-denominator* first)) 'b1-arithmetic-times-denominator)
    ((b1-shapes-any-call (b1-search-subterms subject) *b1-shapes-inverse*)
     'b1-division-product-with-inverse)
    (t nil))))

(defun b1-shapes-arithmetic-less-recipe (test subject right)
  (proof-with-checked-results
   ((first (b1-shapes-at subject 1)))
   (or
    (and (proof-is-call first *b1-shapes-numerator*)
         (proof-with-checked-results
          ((second (b1-shapes-at subject 2)))
          (and (equal second *proof-zero*)
               (proof-is-call right *proof-if*)
               'b1-numerators-negative-numerator)))
    (and (not (eq test :none))
         (b1-shapes-any-call (b1-search-subterms subject) *b1-shapes-inverse*)
         (cond
          ((proof-is-call right *proof-less*) 'b1-division-divide-positive)
          ((proof-is-call right *proof-if*) 'b1-division-divide-by-sign)
          (t nil))))))

(defun b1-shapes-arithmetic-rounding-recipe (subject right)
  (proof-with-checked-results
   ((arg (b1-shapes-at subject 1)))
   (cond
    ((and (proof-is-call arg *proof-plus*) (proof-is-call right *proof-if*))
     (if (proof-is-call subject *b1-quotient-floor*) 'b1-floor-sum-floor-sum 'b1-floor-sum-mod-sum))
    ((proof-is-call arg *b1-modular-mod*)
     (if (proof-is-call subject *b1-quotient-floor*) 'b1-floor-rewrite-floor-mod 'b1-floor-rewrite-mod-mod))
    (t nil))))

(defun b1-shapes-arithmetic-recipe (test goal subject)
  (proof-with-checked-results
   ((right (if (proof-is-call goal *proof-equal*) (b1-shapes-at goal 2) :none)))
   (or
    (and (not (eq test :none))
         (or (proof-is-call goal *proof-not*)
             (member-equal (b1-shapes-head goal) (list *proof-less* *proof-integerp*)))
         (proof-with-checked-results
          ((comparison (if (proof-is-call goal *proof-not*) (b1-shapes-at goal 1) goal)))
          (b1-shapes-arithmetic-comparison-recipe test goal subject comparison)))
    (and (not (eq test :none)) (b1-shapes-exponent-recipe test goal))
    (and (not (eq right :none))
         (or
          (and (proof-is-call subject *b1-shapes-numerator*)
               (b1-shapes-arithmetic-numerator-recipe test subject right))
          (and (proof-is-call subject *b1-shapes-denominator*)
               (b1-shapes-arithmetic-denominator-recipe test subject right))
          (and (proof-is-call subject *proof-equal*)
               (b1-shapes-arithmetic-equality-recipe test subject right))
          (and (proof-is-call subject *proof-times*)
               (proof-is-call right *proof-if*)
               (b1-shapes-arithmetic-product-recipe subject))
          (and (proof-is-call subject *proof-less*)
               (b1-shapes-arithmetic-less-recipe test subject right))
          (and (member-equal (b1-shapes-head subject) (list *b1-quotient-floor* *b1-modular-mod*))
               (b1-shapes-arithmetic-rounding-recipe subject right))
          (and (proof-is-call right *b1-quotient-floor*)
               (proof-is-call subject *proof-times*)
               (proof-with-checked-results
                ((premise (b1-shapes-remainder-premise-p test)))
                (and premise 'b1-modular-exact-remainder-quotient))))))))

(defun b1-shapes-bit-predicate-p (operator)
  (member-equal operator (list *proof-integerp* *library-natp* *b1-fixer-laws-bitp*)))

(defun b1-shapes-lambda-bit-operation-recipe (definitions formula)
  (let ((function (b1-shapes-head formula)))
    (and (not (eq function :none))
         (proof-compound function)
         (equal (len formula) 2)
         (proof-with-checked-results
          ((body (b1-shapes-at function 2)))
          (and (b1-shapes-bit-predicate-p (b1-shapes-head body))
               (assoc-equal (b1-shapes-head (cadr formula)) definitions)
               'b1-bit-types-bit-operation-type)))))

(defun b1-shapes-defined-bit-operation-recipe (definitions test goal)
  (and (eq test :none)
       (b1-shapes-bit-predicate-p (b1-shapes-head goal))
       (proof-with-checked-results
        ((term (b1-shapes-at goal 1)))
        (and (assoc-equal (b1-shapes-head term) definitions)
             (if (and (equal (b1-shapes-head goal) *library-natp*)
                      (proof-is-call term *b1-bit-length-length*))
                 '(:natural-bit-length)
               'b1-bit-types-bit-operation-type)))))

(defun b1-shapes-theorem-recipes-natural-bit-length (lib claim)
  (proof-with-checked-results
   ((length-call (b1-shapes-at claim 1))
    (arg (b1-shapes-at length-call 1)))
   (b1-bit-length-natural-bit-length lib arg)))

(defun b1-shapes-pack-recipe (test goal)
  (and (eq test :none)
       (equal (b1-shapes-head goal) *b1-printing-characters*)
       (proof-with-checked-results
        ((term (b1-shapes-at goal 1)))
        (and (member-equal (b1-shapes-head term)
                           (list *b1-printing-pack-list* *b1-printing-pack-tree*))
             'b1-printing-pack-character-lists))))

(defun b1-shapes-mismatch-bits (test terms)
  (if (endp terms)
      nil
    (cons (list *b1-mismatch-logbitp* test (car terms))
          (b1-shapes-mismatch-bits test (cdr terms)))))

(defun b1-shapes-mismatch-hypothesis-recipes (test goal)
  (proof-with-checked-results
   ((has-mismatch (b1-shapes-any-conjunct-call test *b1-mismatch-mismatch*)))
   (and has-mismatch
        (proof-with-checked-results
         ((comparison (if (proof-is-call goal *proof-not*) (b1-shapes-at goal 1) goal)))
         (append
          (and (proof-is-call comparison *proof-less*)
               (b1-shapes-any-call (cdr comparison) *b1-mismatch-max*)
               '(b1-mismatch-mismatch-bound))
          (and (proof-is-call test *b1-mismatch-mismatch*)
               (proof-is-call goal *proof-not*)
               (proof-is-call comparison *proof-equal*)
               (equal (cdr comparison) (b1-shapes-mismatch-bits test (cdr test)))
               '(b1-mismatch-mismatch-correct)))))))

(defun b1-shapes-inequality-recipes (definitions test goal)
  (and (proof-is-call test *proof-not*)
       (proof-with-checked-results
        ((premise (b1-shapes-at test 1)))
        (and (proof-is-call premise *proof-equal*)
             (proof-with-checked-results
              ((congruence
                (and (proof-is-call goal *proof-not*)
                     (proof-with-checked-results
                      ((negated (b1-shapes-at goal 1)))
                      (and (proof-is-call negated *proof-equal*)
                           'b1-shapes-congruence-contrapositive)))))
              (append
               (and congruence (list congruence))
               (and (proof-compound (b1-shapes-head goal))
                    (b1-shapes-all-calls (cdr premise) *b1-quotient-ifix*)
                    (assoc-equal *b1-mismatch-mismatch* definitions)
                    '(b1-mismatch-mismatch-wrapped-index))))))))

(defun b1-shapes-mismatch-recipes (definitions test goal subject)
  (proof-with-checked-results
   ((exists-recipe
     (and (proof-is-call goal *b1-revappend-iff*)
          (proof-is-call subject *b1-mismatch-mismatch*)
          'b1-mismatch-mismatch-exists))
    (integer-recipe
     (and (proof-is-call goal *b1-revappend-iff*)
          (proof-is-call subject *proof-integerp*)
          (proof-with-checked-results
           ((value (b1-shapes-at subject 1)))
           (and (proof-is-call value *b1-mismatch-mismatch*)
                'b1-bit-length-mismatch-is-integer))))
    (hypothesis-recipes (b1-shapes-mismatch-hypothesis-recipes test goal))
    (fixed-recipe
     (and (not (eq test :none))
          (proof-is-call goal *proof-equal*)
          (b1-shapes-all-calls (cdr goal) *b1-quotient-ifix*)
          (assoc-equal *b1-mismatch-mismatch* definitions)
          'b1-mismatch-equal-fixed-by-bits))
    (inequality-recipes (b1-shapes-inequality-recipes definitions test goal)))
   (append
    (remove-equal nil (list exists-recipe integer-recipe))
    hypothesis-recipes
    (and fixed-recipe (list fixed-recipe))
    inequality-recipes)))

(defun b1-shapes-equality-equivalence-recipe (lib formula)
  (and (proof-is-call formula *proof-if*)
       (proof-with-checked-results
        ((guard (b1-shapes-at formula 1)))
        (and (proof-is-call guard *b1-fixer-laws-booleanp*)
             (proof-with-checked-results
              ((term (b1-shapes-at guard 1))
               (equality (b1-shapes-equality-of-fixes lib term)))
              (and equality 'b1-fixer-laws-equality-equivalence))))))

(defun b1-shapes-maybe-recognizer-recipe (definitions goal subject)
  (and (proof-is-call goal *proof-equal*)
       (proof-with-checked-results
        ((right (b1-shapes-at goal 2)))
        (and (proof-is-call right *proof-if*)
             (proof-with-checked-results
              ((otherwise-term (b1-shapes-at right 3)))
              (and (proof-is-call otherwise-term *proof-not*)
                   (let ((definition (assoc-equal (b1-shapes-head subject) definitions)))
                     (and definition
                          (not (eq (cdr definition) :none))
                          (proof-with-checked-results
                           ((body (b1-shapes-at (cdr definition) 1)))
                           (and (proof-is-call body *proof-if*)
                                'b1-fixer-laws-maybe-recognizer))))))))))

(defun b1-shapes-fixer-recipes (lib definitions formula test goal subject)
  (proof-with-checked-results
   ((identity (and (proof-is-call test *b1-fixer-laws-bitp*)
                   (proof-is-call goal *proof-equal*)
                   (equal (b1-shapes-head subject) (proof-sym "BFIX$INLINE" "ACL2"))
                   'b1-fixer-laws-bit-fix-identity))
    (equivalence (b1-shapes-equality-equivalence-recipe lib formula))
    (fixed (and (proof-is-call goal *proof-equal*)
                (proof-with-checked-results
                 ((equality (b1-shapes-equality-of-fixes lib test)))
                 (and equality 'b1-fixer-laws-fixed-congruence))))
    (maybe-recipe (b1-shapes-maybe-recognizer-recipe definitions goal subject)))
   (remove-equal nil (list identity equivalence fixed maybe-recipe))))

(defun b1-shapes-numeric-fold-recipe (goal)
  (and (equal (b1-shapes-head goal) (proof-sym "REAL/RATIONALP" "ACL2"))
       (proof-with-checked-results
        ((arg (b1-shapes-at goal 1)))
        (and (member-equal (b1-shapes-head arg)
                           (list (proof-sym "MAXLIST" "ACL2")
                                 (proof-sym "MINLIST" "ACL2")
                                 (proof-sym "SUM" "ACL2")))
             'b1-list-types-numeric-fold-type))))

(defun b1-shapes-numeric-sort-recipe (goal listp-head)
  (and (equal (b1-shapes-head goal) listp-head)
       (proof-with-checked-results
        ((arg (b1-shapes-at goal 1)))
        (and (proof-is-call arg (proof-sym "NUMERIC-SORT" "ACL2"))
             'b1-list-types-numeric-sort-type))))

(defun b1-shapes-numeric-insert-recipe (test goal listp-head)
  (and (proof-is-call goal listp-head)
       (proof-with-checked-results
        ((arg (b1-shapes-at goal 1)))
        (and (proof-is-call arg (proof-sym "NUMERIC-INSERT" "ACL2"))
             (proof-with-checked-results
              ((known (b1-shapes-any-conjunct-call test listp-head)))
              (and known 'b1-list-types-numeric-insert-type))))))

(defun b1-shapes-numeric-recipes (test goal)
  (let* ((listp-head (proof-sym "REAL/RATIONAL-LISTP" "ACL2"))
         (typed (proof-is-call test listp-head)))
    (proof-with-checked-results
     ((fold-recipe (and typed (b1-shapes-numeric-fold-recipe goal)))
      (sort-recipe (and typed (b1-shapes-numeric-sort-recipe goal listp-head)))
      (insert-recipe (b1-shapes-numeric-insert-recipe test goal listp-head)))
     (append (and fold-recipe (list fold-recipe))
             (and sort-recipe (list sort-recipe))
             (and insert-recipe (list insert-recipe))))))

(defun b1-shapes-tree-recipe (goal subject)
  (and (proof-is-call subject *b1-xdoc-types-tree*)
       (proof-is-call goal *proof-equal*)
       (proof-with-checked-results
        ((arg (b1-shapes-at subject 1)))
        (cond
         ((proof-is-call arg *proof-cons*) 'b1-xdoc-types-tree-cons)
         ((member-equal (b1-shapes-head arg)
                        (list *b1-xdoc-types-make-tag* *b1-xdoc-types-make-directive*))
          'b1-xdoc-types-tree-constructor)
         (t 'b1-xdoc-types-tree-tag-wrapper)))))

(defun b1-shapes-tree-alist-recipe (goal subject)
  (and (proof-is-call subject *b1-xdoc-types-tree-alist*)
       (proof-is-call goal *proof-equal*)
       (proof-with-checked-results
        ((arg (b1-shapes-at subject 1)))
        (and (proof-is-call arg (proof-cl "ACONS")) 'b1-xdoc-types-tree-alist-cons))))

(defun b1-shapes-list-type-recipe (test goal source target)
  (and (proof-is-call test source)
       (proof-with-checked-results
        ((arg (b1-shapes-at test 1)))
        (and (equal goal (list target arg)) 'b1-xdoc-types-list-type-implication))))

(defun b1-shapes-string-recipe (definitions goal)
  (and (proof-is-call goal *b1-logic-stringp*)
       (proof-with-checked-results
        ((arg (b1-shapes-at goal 1)))
        (let ((operator (b1-shapes-head arg)))
          (and (proof-compound arg)
               (assoc-equal operator definitions)
               (if (equal operator (proof-sym "MV-NTH" "ACL2"))
                   'b1-xdoc-types-mv-string-result
                 (proof-with-checked-results
                  ((package (b1-shapes-at operator 1)))
                  (and (equal package "XDOC") 'b1-xdoc-types-string-result))))))))

(defun b1-shapes-xdoc-recipes (definitions test goal subject)
  (proof-with-checked-results
   ((tree (b1-shapes-tree-recipe goal subject))
    (tree-alist (b1-shapes-tree-alist-recipe goal subject))
    (trees (b1-shapes-list-type-recipe test goal *b1-xdoc-types-trees* *b1-printing-true-listp*))
    (strings (b1-shapes-list-type-recipe test goal (proof-sym "STRING-LISTP" "ACL2")
                                         *b1-xdoc-types-trees*))
    (string-result (b1-shapes-string-recipe definitions goal)))
   (append (and tree (list tree))
           (and tree-alist (list tree-alist))
           (and trees (list trees))
           (and strings (list strings))
           (and string-result (list string-result)))))

(defun b1-shapes-primary-recipes (lib test goal subject index)
  (proof-with-checked-results
   ((list-recipe (b1-shapes-abstract-list-recipe-with-index lib test goal subject index))
    (revappend-recipe (b1-shapes-revappend-recipe test goal subject))
    (association-recipe (b1-shapes-association-recipe test subject))
    (set-recipe (b1-shapes-set-recipe test goal subject))
    (arithmetic-recipe (b1-shapes-arithmetic-recipe test goal subject)))
   (remove-equal nil (list list-recipe revappend-recipe association-recipe
                           set-recipe arithmetic-recipe))))

(defun b1-shapes-type-recipes (definitions formula test goal)
  (proof-with-checked-results
   ((lambda-bit-recipe (b1-shapes-lambda-bit-operation-recipe definitions formula))
    (bit-recipe (b1-shapes-defined-bit-operation-recipe definitions test goal))
    (pack-recipe (b1-shapes-pack-recipe test goal)))
   (remove-equal nil (list lambda-bit-recipe bit-recipe pack-recipe))))

(defun b1-shapes-theorem-recipes-with-index (lib formula index)
  (proof-with-checked-results
   ((parts (b1-shapes-split-goal formula)))
   (let* ((test (car parts))
          (goal (cadr parts))
          (definitions (proof-proof-definitions (library-library-proof lib))))
     (proof-with-checked-results
      ((subject (if (member-equal (b1-shapes-head goal) (list *proof-equal* *b1-revappend-iff*))
                    (b1-shapes-at goal 1)
                  goal))
       (primary-recipes (b1-shapes-primary-recipes lib test goal subject index))
       (type-recipes (b1-shapes-type-recipes definitions formula test goal))
       (mismatch-recipes (b1-shapes-mismatch-recipes definitions test goal subject))
       (fixer-recipes (b1-shapes-fixer-recipes lib definitions formula test goal subject))
       (numeric-recipes (b1-shapes-numeric-recipes test goal))
       (xdoc-recipes (b1-shapes-xdoc-recipes definitions test goal subject)))
      (append primary-recipes type-recipes mismatch-recipes
              fixer-recipes numeric-recipes xdoc-recipes)))))

(defun b1-shapes-witness-arities (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
     ((function (proof-list-of-length (car functions) 2))
      (arities (b1-shapes-witness-arities (cdr functions))))
     (cons (cadr function) arities))))

(defun b1-shapes-witness-list-type (first functions)
  (proof-with-checked-results
   ((left (b1-shapes-at first 1)))
   (and (proof-is-call left (caadr functions))
        (proof-with-checked-results
         ((right (b1-shapes-at first 2)))
         (and (proof-is-call right *proof-if*)
              (proof-with-checked-results
               ((guard (b1-shapes-at right 1)))
               (and (proof-is-call guard *b1-logic-atom*)
                    'b1-witnesses-list-type-witness)))))))

(defun b1-shapes-witness-alist-type (functions formulas)
  (proof-with-checked-results
   ((displayed (b1-shapes-at (caddr formulas) 1)))
   (and (proof-is-call displayed *b1-revappend-iff*)
        (proof-with-checked-results
         ((left (b1-shapes-at displayed 1)))
         (and (proof-is-call left (car (nth 4 functions)))
              'b1-witnesses-alist-type-witness)))))

(defun b1-shapes-witness-evaluator (functions formulas)
  (proof-with-checked-results
   ((formula (b1-shapes-at (cadr formulas) 1))
    (parts (proof-list-of-length formula 3)))
   (and (proof-is-call (cadr parts) *b1-logic-symbolp*)
        (proof-is-call (caddr parts) *proof-equal*)
        (proof-with-checked-results
         ((left (b1-shapes-at (caddr parts) 1)))
         (and (proof-is-call left (caar functions)) 'b1-witnesses-evaluator-witness)))))

(defun b1-shapes-witness-recipe (functions formulas)
  (proof-with-checked-results
   ((arities (b1-shapes-witness-arities functions))
    (first-pair (b1-shapes-at formulas 0))
    (first (b1-shapes-at first-pair 1)))
   (or
    (and (equal (len arities) 2)
         (equal (len formulas) 3)
         (proof-is-call first *b1-revappend-iff*)
         (b1-shapes-witness-list-type first functions))
    (and (equal arities '(1 1 1 1 1))
         (equal (len formulas) 7)
         (b1-shapes-witness-alist-type functions formulas))
    (and (equal arities '(2 2))
         (<= 8 (len formulas))
         (b1-shapes-witness-evaluator functions formulas)))))
