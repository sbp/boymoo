(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *library-x* (proof-sym "X" "ACL2"))
(defconst *library-y* (proof-sym "Y" "ACL2"))
(defconst *library-z* (proof-sym "Z" "ACL2"))
(defconst *library-natp* (proof-sym "NATP" "ACL2"))
(defconst *library-numberp* (proof-sym "ACL2-NUMBERP" "ACL2"))
(defconst *library-o-finp* (proof-sym "O-FINP" "ACL2"))
(defconst *library-count* (proof-sym "ACL2-COUNT" "ACL2"))
(defconst *library-len* (proof-sym "LEN" "ACL2"))
(defconst *library-car* (proof-cl "CAR"))
(defconst *library-cdr* (proof-cl "CDR"))
(defconst *library-rationalp* (proof-cl "RATIONALP"))
(defconst *library-nfix* (proof-sym "SELF-NFIX" "ACL2"))
(defconst *library-gap* (proof-sym "SELF-GAP" "ACL2"))
(defconst *library-implies* (proof-sym "IMPLIES" "ACL2"))

(defun library-plus (a b)
  (list *proof-plus* a b))

(defun library-minus (a)
  (list *proof-minus* a))

(defun library-diff (a b)
  (library-plus a (library-minus b)))

(defun library-lt (a b)
  (list *proof-less* a b))

(defun library-le (a b)
  (proof-neg (library-lt b a)))

(defun library-positive (a)
  (library-lt *proof-zero* a))

(defun library-nonnegative (a)
  (proof-neg (library-lt a *proof-zero*)))

(defun library-guards (terms)
  (if (endp terms)
      nil
    (cons (proof-neg (car terms)) (library-guards (cdr terms)))))

(defun library-integer (term)
  (list *proof-integerp* term))

(defun library-make-library (proof entries)
  (list :library proof entries))

(defun library-library-init (proof)
  (library-make-library proof nil))

(defun library-library-proof (library)
  (cadr library))

(defun library-library-entries (library)
  (caddr library))

(defun library-library-with-proof (library proof)
  (library-make-library proof (library-library-entries library)))

(defun library-library-with-entries (library entries)
  (library-make-library (library-library-proof library) entries))

(defun library-lemma-name (name)
  (proof-sym (concatenate 'string "SELF-" name) "ACL2"))

(defun library-library-lemma (library name claim step conditions)
  (let* ((proof (library-library-proof library))
         (name (library-lemma-name name))
         (clause (cons claim conditions))
         (facts (proof-proof-facts proof)))
    (proof-with-checked-results
     ((step (proof-proof-subsume proof step clause))
      (entry (proof-proof-entry "lemma" name (cons name clause) (list step))))
     (if (assoc-equal name facts)
         '(:failure "assertion" "")
       (library-make-library
        (proof-proof-with-facts proof (table-put facts name clause))
        (append (library-library-entries library) (list entry)))))))

(defun library-library-definition (library name formals body)
  (proof-with-checked-results
   ((proof (proof-proof-add-definition (library-library-proof library)
                                      name formals body))
    (source (proof-line "define" (list *proof-nil* (list name formals body)))))
   (library-make-library proof
                         (append (library-library-entries library)
                                 (list (list "define" name nil source))))))

(defun library-library-axiom (library name args)
  (proof-proof-fact (library-library-proof library)
                    (proof-sym name "ACL2")
                    (seq-zip (list *library-x* *library-y* *library-z*) args)))

(defun library-library-builtin (library number term)
  (proof-proof-fact (library-library-proof library)
                    (concatenate 'string "built-in-clause-" (decimal-text number))
                    (list (list *library-x* term))))

(defun library-library-cite (library name args evidence)
  (proof-proof-use (library-library-proof library)
                   (library-lemma-name name)
                   (seq-zip (list *library-x* *library-y* *library-z*) args)
                   evidence))

(defun library-library-ints (library terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
     ((step (proof-proof-assume (library-library-proof library)
                                (library-integer (car terms)) t))
      (rest (library-library-ints library (cdr terms))))
     (cons step rest))))

(defun library-type-evidence (literal evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((first (proof-step-first (car evidence))))
      (if (equal first literal)
          (car evidence)
        (library-type-evidence literal (cdr evidence))))))

(defun library-missing-integer (term)
  (proof-with-checked-results ((text (proof-write term)))
    (list :failure "value"
          (concatenate 'string "Missing integer premise for " text))))

(mutual-recursion
 (defun library-library-type-of (library term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let ((literal (library-integer term)))
     (proof-with-checked-results ((premise (library-type-evidence literal evidence)))
       (cond
        (premise premise)
        ((atom term) (library-missing-integer term))
        ((and (proof-is-call term *proof-quote*) (endp (cdr term)))
         '(:failure "index" ""))
        ((and (proof-is-call term *proof-quote*) (integerp (cadr term)))
         (proof-proof-prove (library-library-proof library) literal nil nil))
        ((or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*))
         (proof-with-checked-results ((steps (library-type-arguments library (cdr term) evidence)))
           (library-library-cite library
                                 (if (equal (car term) *proof-plus*)
                                     "INTEGER-SUM" "INTEGER-PRODUCT")
                                 (cdr term) steps)))
        ((proof-is-call term *proof-minus*)
         (if (endp (cdr term))
             '(:failure "index" "")
           (proof-with-checked-results ((step (library-library-type-of library (cadr term) evidence)))
             (library-library-cite library "INTEGER-NEGATION" (cdr term) (list step)))))
        ((proof-is-call term *library-count*)
         (library-library-cite library "COUNT-INTEGER" (cdr term) nil))
        ((proof-is-call term *library-len*)
         (library-library-cite library "LEN-INTEGER" (cdr term) nil))
        (t (library-missing-integer term))))))

 (defun library-type-arguments (library args evidence)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (library-library-type-of library (car args) evidence))
       (rest (library-type-arguments library (cdr args) evidence)))
      (cons step rest)))))

(mutual-recursion
 (defun library-library-natural (library term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *library-count*)
     (library-library-cite library "COUNT-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-len*)
     (library-library-cite library "LEN-NATURAL" (cdr term) nil))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results ((steps (library-natural-arguments library (cdr term))))
       (library-library-cite library "NATURAL-SUM" (cdr term) steps)))
    (t (proof-proof-prove (library-library-proof library)
                          (list *library-natp* term) nil (list *library-natp* *proof-not*)))))

 (defun library-natural-arguments (library args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (library-library-natural library (car args)))
       (rest (library-natural-arguments library (cdr args))))
      (cons step rest)))))

(defun library-library-rational (library term evidence)
  (proof-with-checked-results
   ((axiom (library-library-axiom library "INTEGER-IMPLIES-RATIONAL" (list term)))
    (type-step (library-library-type-of library term evidence)))
   (proof-proof-modus-ponens (library-library-proof library) axiom type-step)))

(defun library-library-number (library term evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
      (rational (library-library-rational library term evidence)))
     (proof-proof-modus-ponens proof fact rational))))

(defun library-library-transport-argument (library step equality index)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((symmetric (proof-proof-symmetric proof equality))
      (changed (proof-proof-rewrite proof step symmetric (list 1 index))))
     (proof-proof-tidy proof changed))))

(defmacro library-inherited (method library &rest args)
  `(,method (library-library-proof ,library) ,@args))

(defun library-integer-closure-lemmas (library both recipes)
  (declare (xargs :measure (acl2-count recipes)))
  (if (endp recipes)
      library
    (let* ((recipe (car recipes))
           (head (car recipe))
           (axiom (cadr recipe))
           (name (caddr recipe))
           (x *library-x*)
           (y *library-y*))
      (proof-with-checked-results
       ((fact (library-inherited proof-proof-fact library axiom nil))
        (step (library-inherited proof-proof-modus-ponens library fact both))
        (library (library-library-lemma library name (library-integer (list head x y)) step
                                        (library-guards (list (library-integer x)
                                                              (library-integer y))))))
       (library-integer-closure-lemmas library both (cdr recipes))))))

(defun library-library-logic-and-types (library)
  (let* ((x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (conditional (proof-ite x y z))
         (integer-x (library-integer x))
         (integer-y (library-integer y))
         (nat (list *library-natp* x))
         (cons-test (list *proof-consp* x))
         (ordinal (list *proof-ordinalp* x))
         (ordinal-lt (list *proof-ordinal-less* x y))
         (nfix (list *library-nfix* x))
         (gap (list *library-gap* x y)))
    (proof-with-checked-results
     ((middle (library-inherited proof-proof-excluded-middle library x))
      (library (library-library-lemma library "EXCLUDED-MIDDLE" (proof-neg x) middle (list x)))
      (when-false (library-inherited proof-proof-if-false library conditional))
      (library (library-library-lemma library "IF-FALSE" (proof-eq conditional z) when-false (list x)))
      (when-true (library-inherited proof-proof-if-true library conditional))
      (library (library-library-lemma library "IF-TRUE" (proof-eq conditional y) when-true
                                      (list (proof-neg x))))
      (integers (library-library-ints library (list x y)))
      (both (library-inherited proof-proof-prove library
                               (proof-ite integer-x integer-y *proof-false*) integers nil))
      (library (library-integer-closure-lemmas
                library both (list (list *proof-plus* "integerp-binary-+" "INTEGER-SUM")
                                   (list *proof-times* "integerp-binary-*" "INTEGER-PRODUCT"))))
      (negation (library-inherited proof-proof-fact library "integerp-unary--" nil))
      (step (library-inherited proof-proof-modus-ponens library negation (car integers)))
      (library (library-library-lemma library "INTEGER-NEGATION" (library-integer (library-minus x))
                                      step (list (proof-neg integer-x))))

      (nat-hyp (library-inherited proof-proof-assume library nat t))
      (opened (library-inherited proof-proof-unfold library nat))
      (nat-open (library-inherited proof-proof-rewrite library nat-hyp opened '(1)))
      (nat-parts (library-inherited proof-proof-conjunct library nat-open))
      (library (library-library-lemma library "NATURAL-INTEGER" integer-x (car nat-parts)
                                      (list (proof-neg nat))))
      (library (library-library-lemma library "NATURAL-NONNEGATIVE" (library-nonnegative x)
                                      (cadr nat-parts) (list (proof-neg nat))))
      (neg-x (library-inherited proof-proof-assume library (library-lt x *proof-zero*) nil))
      (bounded (library-inherited proof-proof-prove library nat (list (car integers) neg-x)
                                  (list *library-natp*)))
      (library (library-library-lemma library "NATURAL-FROM-BOUNDS" nat bounded
                                      (list (proof-neg integer-x) (library-lt x *proof-zero*))))

      (consp-fact (library-inherited proof-proof-fact library "consp-not-acl2-numberp" nil))
      (consp-hyp (library-inherited proof-proof-assume library cons-test t))
      (nonnumber (library-inherited proof-proof-modus-ponens library consp-fact consp-hyp))
      (numeric (library-inherited proof-proof-assume library (list *library-numberp* x) t))
      (finite (library-inherited proof-proof-cut library numeric nonnumber))
      (finite (library-inherited proof-proof-front library finite (proof-neg cons-test)))
      (number-finite (library-inherited proof-proof-prove library (list *library-o-finp* x)
                                        (list finite) (list *library-o-finp* (proof-cl "ATOM"))))
      (numeric-first (proof-step-first numeric))
      (library (library-library-lemma library "NUMBER-FINITE" (list *library-o-finp* x)
                                      number-finite (list (proof-neg numeric-first))))
      (number-x (library-library-number library x (list (car integers))))
      (integer-finite (library-library-cite library "NUMBER-FINITE" (list x) (list number-x)))
      (library (library-library-lemma library "INTEGER-FINITE" (list *library-o-finp* x)
                                      integer-finite (list (proof-neg integer-x))))

      (x-finite (library-library-cite library "INTEGER-FINITE" (list x) (list (car nat-parts))))
      (natural-ordinal (library-inherited proof-proof-prove library ordinal (list x-finite nat-hyp)
                                          (list *proof-ordinalp*)))
      (library (library-library-lemma library "NATURAL-ORDINAL" ordinal natural-ordinal
                                      (list (proof-neg nat))))
      (x-finite (library-library-cite library "INTEGER-FINITE" (list x) (list (car integers))))
      (y-finite (library-library-cite library "INTEGER-FINITE" (list y) (list (cadr integers))))
      (finite-order (library-inherited proof-proof-simplify library ordinal-lt (list x-finite y-finite)
                                       (list *proof-ordinal-less* *proof-not*)))
      (library (library-library-lemma library "FINITE-ORDER" (proof-eq ordinal-lt (library-lt x y))
                                      finite-order (library-guards (list integer-x integer-y))))

      (library (library-library-definition library *library-nfix* (list x) (proof-ite nat x *proof-zero*)))
      (good-eq (library-inherited proof-proof-simplify library nfix (list nat-hyp) (list *library-nfix*)))
      (good (library-library-transport-argument library nat-hyp good-eq 1))
      (zero-natural (library-inherited proof-proof-prove library (list *library-natp* *proof-zero*)
                                        nil (list *library-natp* *proof-not*)))
      (not-natural (library-inherited proof-proof-assume library nat nil))
      (bad-eq (library-inherited proof-proof-simplify library nfix (list not-natural) (list *library-nfix*)))
      (bad (library-library-transport-argument library zero-natural bad-eq 1))
      (cases (library-inherited proof-proof-cases library nat good bad))
      (library (library-library-lemma library "NFIX-NATURAL" (list *library-natp* nfix) cases nil))
      (fixed (library-inherited proof-proof-fact library (library-lemma-name "NFIX-NATURAL") nil))
      (nfix-integer (library-library-cite library "NATURAL-INTEGER" (list nfix) (list fixed)))
      (library (library-library-lemma library "NFIX-INTEGER" (library-integer nfix) nfix-integer nil))
      (nfix-ordinal (library-library-cite library "NATURAL-ORDINAL" (list nfix) (list fixed)))
      (library (library-library-lemma library "NFIX-ORDINAL" (list *proof-ordinalp* nfix) nfix-ordinal nil))
      (library (library-library-definition library *library-gap* (list x y)
                                           (list *library-nfix* (library-diff x y))))
      (difference-ordinal (library-library-cite library "NFIX-ORDINAL" (list (library-diff x y)) nil))
      (opened (library-inherited proof-proof-unfold library gap))
      (gap-ordinal (library-library-transport-argument library difference-ordinal opened 1)))
     (library-library-lemma library "GAP-ORDINAL" (list *proof-ordinalp* gap) gap-ordinal nil))))

(defun library-library-push-minus (n library term evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "library-library-push-minus")
    (let ((proof (library-library-proof library)))
      (cond
       ((proof-is-call term *proof-plus*)
        (proof-with-checked-results
         ((result (proof-proof-reflexive proof term))
          (left (proof-term-at term 1))
          (left-step (library-library-push-minus (1- n) library left evidence))
          (result (if left-step
                      (proof-proof-rewrite proof result left-step '(1 2 1))
                    result))
          (right (proof-term-at term 2))
          (right-step (library-library-push-minus (1- n) library right evidence))
          (result (if right-step
                      (proof-proof-rewrite proof result right-step '(1 2 2))
                    result))
          (first (proof-step-first result))
          (right (proof-term-at first 2)))
         (if (equal right term) nil result)))
       ((proof-is-call term *proof-minus*)
        (proof-with-checked-results ((argument (proof-term-at term 1)))
          (if (proof-is-call argument *proof-quote*)
              (proof-proof-constant proof term)
            (let ((facts (proof-proof-facts proof)))
              (proof-with-checked-results
               ((result
                 (cond
                  ((and (proof-is-call argument *proof-minus*)
                        (assoc-equal (library-lemma-name "DOUBLE-NEGATION") facts))
                   (proof-with-checked-results
                    ((item (proof-term-at argument 1))
                     (type-step (library-library-type-of library item evidence)))
                    (library-library-cite library "DOUBLE-NEGATION"
                                          (list item) (list type-step))))
                  ((and (proof-is-call argument *proof-plus*)
                        (assoc-equal (library-lemma-name "NEGATE-SUM") facts))
                   (proof-with-checked-results
                    ((steps (library-type-arguments library (cdr argument) evidence)))
                    (library-library-cite library "NEGATE-SUM" (cdr argument) steps)))
                  (t nil))))
               (if (not result)
                   nil
                 (proof-with-checked-results
                  ((first (proof-step-first result))
                   (right (proof-term-at first 2))
                   (rest (library-library-push-minus (1- n) library right evidence)))
                  (proof-proof-chain proof result (list rest)))))))))
       (t nil)))))

(defun library-linear-form-key (term)
  (cond
   ((proof-is-call term *proof-quote*) (list 0 "" 0))
   ((proof-is-call term *proof-minus*)
    (proof-with-checked-results ((arg (proof-term-at term 1))
                   (text (proof-write arg)))
      (list 1 text 1)))
   (t (proof-with-checked-results ((text (proof-write term)))
        (list 1 text 0)))))

(defun library-linear-key<= (a b)
  (or (< (car a) (car b))
      (and (equal (car a) (car b))
           (or (string< (cadr a) (cadr b))
               (and (equal (cadr a) (cadr b))
                    (<= (caddr a) (caddr b)))))))

(defun library-linear-form-get (root place)
  (declare (xargs :measure (acl2-count place)))
  (if (endp place)
      root
    (proof-with-checked-results ((child (proof-term-at root (car place))))
      (library-linear-form-get child (cdr place)))))

(defun library-linear-reassociate (n library step place)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "library-linear-reassociate")
    (proof-with-checked-results
     ((first (proof-step-first step))
      (node (library-linear-form-get first (cdr place))))
     (if (not (proof-is-call node *proof-plus*))
         step
       (proof-with-checked-results ((left (proof-term-at node 1)))
         (if (proof-is-call left *proof-plus*)
             (proof-with-checked-results
              ((pair (proof-list-of-length (cdr left) 2))
               (right (proof-term-at node 2))
               (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+"
                                                  (list (car pair) (cadr pair) right)))
               (step (proof-proof-rewrite (library-library-proof library) step assoc-step place)))
              (library-linear-reassociate (1- n) library step place))
           (library-linear-reassociate (1- n) library step (append place '(2)))))))))

(defun library-linear-sort (n library step place changed)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "library-linear-sort")
    (proof-with-checked-results
     ((first (proof-step-first step))
      (node (library-linear-form-get first (cdr place))))
     (if (not (proof-is-call node *proof-plus*))
         (if changed
             (library-linear-sort (1- n) library step '(1 2) nil)
           step)
       (proof-with-checked-results ((pair (proof-list-of-length (cdr node) 2)))
         (let* ((a (car pair))
                (rest (cadr pair))
                (suffix (proof-is-call rest *proof-plus*)))
           (proof-with-checked-results
            ((b (if suffix (proof-term-at rest 1) rest))
             (key-a (library-linear-form-key a))
             (key-b (library-linear-form-key b)))
            (if (library-linear-key<= key-a key-b)
                (library-linear-sort (1- n) library step (append place '(2)) changed)
              (proof-with-checked-results
               ((swap (if suffix
                          (proof-with-checked-results ((tail (proof-term-at rest 2)))
                            (library-library-cite library "ADD-SWAP" (list a b tail) nil))
                        (library-library-axiom library "COMMUTATIVITY-OF-+" (list a b))))
                (step (proof-proof-rewrite (library-library-proof library) step swap place)))
               (library-linear-sort (1- n) library step (append place '(2)) t))))))))))

(defun library-linear-combine-pair (library a b)
  (let ((proof (library-library-proof library)))
    (cond
     ((and (proof-is-call a *proof-quote*) (proof-is-call b *proof-quote*))
      (proof-proof-constant proof (library-plus a b)))
     ((equal b (library-minus a))
      (library-library-axiom library "INVERSE-OF-+" (list a)))
     ((equal a (library-minus b))
      (proof-with-checked-results
       ((swap (library-library-axiom library "COMMUTATIVITY-OF-+" (list a b)))
        (inverse (library-library-axiom library "INVERSE-OF-+" (list b))))
       (proof-proof-chain proof swap (list inverse))))
     (t nil))))

(defun library-linear-remove-zero (library step name term place evidence)
  (proof-with-checked-results
   ((type-step (library-library-type-of library term evidence))
    (zero-step (library-library-cite library name (list term) (list type-step))))
   (proof-proof-rewrite (library-library-proof library) step zero-step place)))

(defun library-linear-combine (n library step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "library-linear-combine")
    (proof-with-checked-results
     ((first (proof-step-first step))
      (node (library-linear-form-get first (cdr place))))
     (if (not (proof-is-call node *proof-plus*))
         (proof-proof-tidy (library-library-proof library) step)
       (proof-with-checked-results ((pair (proof-list-of-length (cdr node) 2)))
         (let* ((a (car pair))
                (rest (cadr pair))
                (suffix (proof-is-call rest *proof-plus*))
                (proof (library-library-proof library)))
           (proof-with-checked-results ((b (if suffix (proof-term-at rest 1) rest)))
             (cond
              ((equal a *proof-zero*)
               (proof-with-checked-results ((step (library-linear-remove-zero library step "ADD-ZERO-LEFT"
                                                                rest place evidence)))
                 (library-linear-combine (1- n) library step place evidence)))
              ((and (equal b *proof-zero*) (not suffix))
               (proof-with-checked-results ((step (library-linear-remove-zero library step "ADD-ZERO-RIGHT"
                                                                a place evidence)))
                 (library-linear-combine (1- n) library step place evidence)))
              (t
               (proof-with-checked-results ((combine (library-linear-combine-pair library a b)))
                 (if (not combine)
                     (library-linear-combine (1- n) library step (append place '(2)) evidence)
                   (proof-with-checked-results
                    ((step (if suffix
                               (proof-with-checked-results
                                ((tail (proof-term-at rest 2))
                                 (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+"
                                                                    (list a b tail)))
                                 (symmetric (proof-proof-symmetric proof assoc-step)))
                                (proof-proof-rewrite proof step symmetric place))
                             step))
                     (step (proof-proof-rewrite proof step combine
                                                (if suffix (append place '(1)) place))))
                    (library-linear-combine (1- n) library step '(1 2) evidence)))))))))))))

(defun library-library-linear-form (library term evidence)
  (proof-with-checked-results
   ((step (library-library-push-minus 1000000 library term evidence))
    (step (if step step (proof-proof-reflexive (library-library-proof library) term)))
    (step (library-linear-reassociate 1000000 library step '(1 2)))
    (step (library-linear-sort 1000000 library step '(1 2) nil)))
   (library-linear-combine 1000000 library step '(1 2) evidence)))

(defun library-library-linear-equal (library left right integers)
  (proof-with-checked-results
   ((a (library-library-linear-form library left integers))
    (b (library-library-linear-form library right integers))
    (a-first (proof-step-first a))
    (b-first (proof-step-first b))
    (a-normal (proof-term-at a-first 2))
    (b-normal (proof-term-at b-first 2)))
   (if (equal a-normal b-normal)
       (let ((proof (library-library-proof library)))
         (proof-with-checked-results ((symmetric (proof-proof-symmetric proof b)))
           (proof-proof-chain proof a (list symmetric))))
     (proof-with-checked-results ((a-text (proof-write a-normal))
                    (b-text (proof-write b-normal)))
       (list :failure "value"
             (concatenate 'string "('Different sum normal forms', "
                          "b" (text-quoted a-text) ", b" (text-quoted b-text) ")"))))))

(defun library-library-comparison (library a b integers)
  (proof-with-checked-results
   ((a-type (library-library-type-of library a integers))
    (b-type (library-library-type-of library b integers)))
   (library-library-cite library "LESS-DIFFERENCE" (list a b) (list a-type b-type))))

(defun library-library-less-from-difference (library a b positive-difference integers)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((compare (library-library-comparison library a b integers))
      (first (proof-step-first positive-difference))
      (term (proof-term-at first 2))
      (delta (library-library-linear-equal library (library-diff b a) term integers))
      (compare (proof-proof-rewrite proof compare delta '(1 2 2))))
     (proof-proof-transport proof positive-difference compare))))

(defun library-library-weak-from-difference (library a b nonnegative-difference integers)
  (proof-with-checked-results
   ((compare (library-library-axiom library "<-ON-OTHERS" (list b a)))
    (first (proof-step-first nonnegative-difference))
    (bound (proof-term-at first 1))
    (term (proof-term-at bound 1))
    (delta (library-library-linear-equal library (library-diff b a) term integers))
    (compare (proof-proof-rewrite (library-library-proof library) compare delta '(1 2 1))))
   (library-library-transport-argument library nonnegative-difference compare 1)))

(defun library-additive-identities-inverse-unique (a b sum-zero integers library)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus a) a)))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list a)))
      (cancel (proof-proof-chain proof commute (list inverse)))
      (b-type (library-library-type-of library b integers))
      (step (library-library-cite library "ADD-ZERO-LEFT" (list b) (list b-type)))
      (cancel (proof-proof-symmetric proof cancel))
      (step (proof-proof-rewrite proof step cancel '(1 1 1)))
      (step (proof-proof-symmetric proof step))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list (library-minus a) a b)))
      (step (proof-proof-chain proof step (list assoc-step)))
      (step (proof-proof-rewrite proof step sum-zero '(1 2 2)))
      (negative-type (library-library-type-of library (library-minus a) integers))
      (zero-right (library-library-cite library "ADD-ZERO-RIGHT" (list (library-minus a))
                                        (list negative-type))))
     (proof-proof-chain proof step (list zero-right)))))

(defun library-library-additive-identities (library)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*)
        (zero *proof-zero*)
        (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((ints (library-library-ints library (list x)))
      (left-zero (library-library-axiom library "UNICITY-OF-0" (list x)))
      (x-number (library-library-number library x ints))
      (fixed (library-inherited proof-proof-simplify library (list fix x) (list x-number) (list fix)))
      (left-zero (library-inherited proof-proof-chain library left-zero (list fixed)))
      (library (library-library-lemma library "ADD-ZERO-LEFT" (proof-eq (library-plus zero x) x)
                                      left-zero (list (proof-neg (library-integer x)))))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x zero)))
      (right-zero (library-inherited proof-proof-chain library commute (list left-zero)))
      (library (library-library-lemma library "ADD-ZERO-RIGHT" (proof-eq (library-plus x zero) x)
                                      right-zero (list (proof-neg (library-integer x)))))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list x y z)))
      (step (library-inherited proof-proof-symmetric library assoc-step))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x y)))
      (step (library-inherited proof-proof-rewrite library step commute '(1 2 1)))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list y x z)))
      (step (library-inherited proof-proof-chain library step (list assoc-step)))
      (library (library-library-lemma library "ADD-SWAP"
                                      (proof-eq (library-plus x (library-plus y z))
                                                (library-plus y (library-plus x z))) step nil))

      (inverse (library-library-axiom library "INVERSE-OF-+" (list x)))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus x) x)))
      (reverse (library-inherited proof-proof-chain library commute (list inverse)))
      (involution (library-additive-identities-inverse-unique (library-minus x) x reverse ints library))
      (involution (library-inherited proof-proof-symmetric library involution))
      (library (library-library-lemma library "DOUBLE-NEGATION"
                                      (proof-eq (library-minus (library-minus x)) x)
                                      involution (list (proof-neg (library-integer x)))))
      (ints (library-library-ints library (list x y))))
     (let ((a (library-plus x y))
           (b (library-plus (library-minus x) (library-minus y))))
       (proof-with-checked-results
        ((zero-sum (library-library-linear-equal library (library-plus a b) zero ints))
         (distribute (library-additive-identities-inverse-unique a b zero-sum ints library))
         (distribute (library-inherited proof-proof-symmetric library distribute)))
        (library-library-lemma library "NEGATE-SUM" (proof-eq (library-minus a) b) distribute
                               (library-guards (list (library-integer x) (library-integer y)))))))))
