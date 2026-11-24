(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *countdowns-counter-wrappers*
  (list *termination-return-last* (proof-sym "THE-CHECK" "ACL2")
        (proof-sym "LNFIX$INLINE" "ACL2")))

;; The value of an intermediate proof can be a failure. The accompanying
;; library retains the lemmas already established when a caller catches it.
(defmacro countdowns-bind (lib bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings))
          (form (cadar bindings))
          (kind (caddar bindings)))
      (if (eq kind :library)
          `(let* ((,name ,form)
                  (,lib (cdr ,name))
                  (,name (car ,name)))
             (if (failure-p ,name)
                 (cons ,name ,lib)
               (countdowns-bind ,lib ,(cdr bindings) ,body)))
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name ,lib)
             (countdowns-bind ,lib ,(cdr bindings) ,body)))))))

(mutual-recursion
 (defun countdowns-natural-visit (n lib term)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "countdowns-natural-visit") lib))
    ((eq (proof-proof-kind (library-library-proof lib)) :base)
     (cons (library-library-natural lib term) lib))
    (t
     (countdowns-bind lib ((task (lemmas-natural-prepare lib term)))
       (case (car task)
         (:return (cadr task))
         (:length
          (countdowns-bind lib
           ((leaves (countdowns-natural-leaves (1- n) (cadr task) (caddr (cddddr task))) :library)
            (result (lemmas-natural-finish-length task (cons leaves lib))))
           result))
         (otherwise
          (let ((terms (cadddr task)))
            (countdowns-bind lib
             ((steps (countdowns-natural-arguments (1- n) (cadr task) terms) :library))
             (cons (library-library-cite lib (caddr task) terms steps) lib)))))))))

 (defun countdowns-natural-arguments (n lib terms)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "countdowns-natural-arguments") lib))
    ((endp terms) (cons nil lib))
    (t
     (countdowns-bind lib
      ((step (countdowns-natural-visit (1- n) lib (car terms)) :library)
       (rest (countdowns-natural-arguments (1- n) lib (cdr terms)) :library))
      (cons (cons step rest) lib)))))

 (defun countdowns-natural-leaves (n lib requests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "countdowns-natural-leaves") lib))
    ((endp requests) (cons nil lib))
    (t
     (countdowns-bind lib
      ((step (countdowns-natural-visit (1- n) lib (caar requests)) :library)
       (rest (countdowns-natural-leaves (1- n) lib (cdr requests)) :library))
      (cons (cons (cons (car requests) step) rest) lib))))))

(defun countdowns-natural (lib term)
  (countdowns-natural-visit 1000000 lib term))

(defun countdowns-natural-type-p (lib term)
  (or (proof-is-call term *lemmas-length*)
      (and (proof-compound term)
           (member-equal (car term) (list *lemmas-nfix* *lemmas-min*))
           (assoc-equal (car term) (proof-proof-definitions (library-library-proof lib))))))

(mutual-recursion
 (defun countdowns-type-of (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (if (eq (proof-proof-kind (library-library-proof lib)) :base)
       (cons (library-library-type-of lib term evidence) lib)
     (countdowns-bind lib ((premise (proof-find-evidence evidence (list (library-integer term)))))
       (cond
        (premise (cons premise lib))
        ((countdowns-natural-type-p lib term)
         (countdowns-bind lib ((natural (countdowns-natural lib term) :library))
           (cons (library-library-cite lib "NATURAL-INTEGER" (list term) (list natural)) lib)))
        ((and (consp term) (or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*)))
         (countdowns-bind lib ((steps (countdowns-integer-steps lib (cdr term) evidence) :library))
           (cons (library-library-cite lib
                                      (if (equal (car term) *proof-plus*) "INTEGER-SUM" "INTEGER-PRODUCT")
                                      (cdr term) steps)
                 lib)))
        ((and (consp term) (proof-is-call term *proof-minus*))
         (if (endp (cdr term))
             (cons '(:failure "failure" "") lib)
           (countdowns-bind lib ((step (countdowns-type-of lib (cadr term) evidence) :library))
             (cons (library-library-cite lib "INTEGER-NEGATION" (cdr term) (list step)) lib))))
        (t (cons (library-library-type-of lib term evidence) lib))))))

 (defun countdowns-integer-steps (lib terms evidence)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       (cons nil lib)
     (countdowns-bind lib
      ((typed (countdowns-type-of lib (car terms) evidence) :library)
       (rest (countdowns-integer-steps lib (cdr terms) evidence) :library))
      (cons (cons typed rest) lib)))))

(defun countdowns-nfix-ordinal (lib measure)
  (if (not (proof-is-call measure *lemmas-nfix*))
      (cons nil lib)
    (proof-with-checked-results
     ((ordinal (library-library-cite lib "NFIX-ORDINAL" (cdr measure) nil))
      (value (proof-term-at measure 1))
      (equation (lemmas-nfix-equation lib value))
      (step (library-library-transport-argument (cdr equation) ordinal (car equation) 1)))
     (cons step (cdr equation)))))

(defun countdowns-negate-sum-identities (lib balanced index values numbers)
  (declare (xargs :measure (acl2-count values)))
  (cond
   ((endp values) balanced)
   ((endp numbers) balanced)
   (t
    (let ((proof (library-library-proof lib))
          (fix (proof-sym "FIX" "ACL2"))
          (value (car values)))
      (proof-with-checked-results
       ((zero (library-library-axiom lib "UNICITY-OF-0" (list value)))
        (simplified (proof-proof-simplify proof (list fix value) (list (car numbers)) (list fix)))
        (identity (proof-proof-chain proof zero (list simplified)))
        (balanced (proof-proof-rewrite proof balanced identity (list 1 index))))
       (countdowns-negate-sum-identities lib balanced (1+ index) (cdr values) (cdr numbers)))))))

(defun countdowns-negate-sum-lemma (lib)
  (let ((proof (library-library-proof lib))
        (name "NEGATE-TOTAL-SUM"))
    (if (assoc-equal (proof-sym "SELF-NEGATE-TOTAL-SUM" "ACL2") (proof-proof-facts proof))
        lib
      (let* ((x *library-x*)
             (y *library-y*)
             (a (library-minus x))
             (b (library-minus y))
             (summation (library-plus x y))
             (distributed (library-plus a b))
             (opposite (library-minus summation)))
        (proof-with-checked-results
         ((cancellation (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list x y distributed)))
          (swap (library-library-cite lib "ADD-SWAP" (list y a b) nil))
          (cancellation (proof-proof-rewrite proof cancellation swap '(1 2 2)))
          (paired (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list x a (library-plus y b))))
          (paired (proof-proof-symmetric proof paired))
          (cancellation (proof-proof-chain proof cancellation (list paired)))
          (inverse-x (library-library-axiom lib "INVERSE-OF-+" (list x)))
          (cancellation (proof-proof-rewrite proof cancellation inverse-x '(1 2 1)))
          (inverse-y (library-library-axiom lib "INVERSE-OF-+" (list y)))
          (cancellation (proof-proof-rewrite proof cancellation inverse-y '(1 2 2)))
          (zero (proof-proof-compute proof (library-plus *proof-zero* *proof-zero*) 0))
          (cancellation (proof-proof-chain proof cancellation (list zero)))
          (reverse-sum (library-library-axiom lib "COMMUTATIVITY-OF-+" (list opposite summation)))
          (inverse-sum (library-library-axiom lib "INVERSE-OF-+" (list summation)))
          (inverse (proof-proof-chain proof reverse-sum (list inverse-sum)))
          (balanced (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list opposite summation distributed)))
          (balanced (proof-proof-rewrite proof balanced inverse '(1 1 1)))
          (balanced (proof-proof-rewrite proof balanced cancellation '(1 2 2)))
          (reverse-zero (library-library-axiom lib "COMMUTATIVITY-OF-+" (list opposite *proof-zero*)))
          (balanced (proof-proof-rewrite proof balanced reverse-zero '(1 2)))
          (sum-number (library-library-cite lib "SUM-NUMBER" (list a b) nil))
          (negation-number (library-library-cite lib "NEGATION-NUMBER" (list summation) nil))
          (balanced (countdowns-negate-sum-identities lib balanced 1 (list distributed opposite)
                                                     (list sum-number negation-number)))
          (step (proof-proof-symmetric proof balanced)))
         (library-library-lemma lib name (proof-eq opposite distributed) step nil))))))

(defun countdowns-shift-sum (lib after left right offset inner on-right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((initial (proof-proof-reflexive proof after))
      (shifted (proof-proof-rewrite proof initial inner (if on-right '(1 2 2) '(1 2 1))))
      (shifted (if on-right
                   shifted
                 (proof-with-checked-results
                  ((association (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list left offset right)))
                   (shifted (proof-proof-chain proof shifted (list association)))
                   (commutation (library-library-axiom lib "COMMUTATIVITY-OF-+" (list offset right))))
                  (proof-proof-rewrite proof shifted commutation '(1 2 2)))))
      (association (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list left right offset)))
      (inverse (proof-proof-symmetric proof association))
      (step (proof-proof-chain proof shifted (list inverse))))
     (cons step lib))))

(defun countdowns-shift-negation (lib after argument unit inner)
  (proof-with-checked-results
   ((lib (countdowns-negate-sum-lemma lib)))
   (let ((proof (library-library-proof lib))
         (offset (proof-quote (- unit))))
     (proof-with-checked-results
      ((initial (proof-proof-reflexive proof after))
       (shifted (proof-proof-rewrite proof initial inner '(1 2 1)))
       (sum (library-library-cite lib "NEGATE-TOTAL-SUM" (list argument offset) nil))
       (shifted (proof-proof-chain proof shifted (list sum)))
       (computed (proof-proof-compute proof (library-minus offset) unit))
       (result (proof-proof-rewrite proof shifted computed '(1 2 2)))
       (step (proof-proof-tidy proof result)))
      (cons step lib)))))

(defun countdowns-unit-shift (lib after before unit)
  (declare (xargs :measure (acl2-count after)))
  (let ((offset (proof-quote unit)))
    (cond
     ((equal after (library-plus before offset))
      (proof-with-checked-results ((step (proof-proof-reflexive (library-library-proof lib) after)))
        (cons step lib)))
     ((equal after (library-plus offset before))
      (proof-with-checked-results
       ((step (library-library-axiom lib "COMMUTATIVITY-OF-+" (list offset before))))
       (cons step lib)))
     ((and (proof-is-call after *proof-plus*) (proof-is-call before *proof-plus*))
      (proof-with-checked-results
       ((arguments (proof-list-of-length (cdr before) 2)))
       (if (and (consp after) (consp (cdr after)) (consp (cddr after)))
           (let ((left (car arguments))
                 (right (cadr arguments)))
             (proof-with-checked-results
              ((inner (if (equal left (cadr after))
                          (countdowns-unit-shift lib (caddr after) right unit)
                        (cons nil lib))))
              (if (car inner)
                  (countdowns-shift-sum (cdr inner) after left right offset (car inner) t)
                (let ((lib (cdr inner)))
                  (if (equal right (caddr after))
                      (proof-with-checked-results
                       ((inner (countdowns-unit-shift lib (cadr after) left unit)))
                       (if (car inner)
                           (countdowns-shift-sum (cdr inner) after left right offset (car inner) nil)
                         inner))
                    (cons nil lib))))))
         '(:failure "failure" ""))))
     ((and (proof-is-call after *proof-minus*) (proof-is-call before *proof-minus*))
      (if (and (consp after) (consp (cdr after)))
          (proof-with-checked-results
           ((argument (proof-term-at before 1))
            (inner (countdowns-unit-shift lib (cadr after) argument (- unit))))
           (if (car inner)
               (countdowns-shift-negation (cdr inner) after argument unit (car inner))
             inner))
        '(:failure "failure" "")))
     (t (cons nil lib)))))

(defun countdowns-nfix-step-lemma (lib)
  (let ((proof (library-library-proof lib))
        (name "NFIX-UNIT-DECREASE"))
    (if (assoc-equal (proof-sym "SELF-NFIX-UNIT-DECREASE" "ACL2") (proof-proof-facts proof))
        lib
      (let* ((x *library-x*)
             (after (library-plus x *proof-neg-one*))
             (goal (list *proof-ordinal-less* (list *lemmas-nfix* after) (list *lemmas-nfix* x))))
        (proof-with-checked-results
         ((int-x (proof-proof-assume proof (library-integer x) t))
          (pos-x (proof-proof-assume proof (library-positive x) t))
          (order (library-library-axiom lib "<-ON-OTHERS" (list after x)))
          (difference (library-library-linear-equal lib (library-diff after x) *proof-neg-one* (list int-x)))
          (comparison (proof-proof-rewrite proof order difference '(1 2 1)))
          (unit-order (proof-proof-prove proof (library-lt *proof-neg-one* *proof-zero*) nil nil))
          (smaller (proof-proof-transport proof unit-order comparison))
          (after-type (countdowns-type-of lib after (list int-x)))
          (lib (cdr after-type))
          (after-type (car after-type))
          (strict (library-library-cite lib "NFIX-DECREASE" (list after x)
                                        (list after-type int-x pos-x smaller)))
          (after-equation (lemmas-nfix-equation lib after))
          (lib (cdr after-equation))
          (strict (library-library-transport-argument lib strict (car after-equation) 1))
          (x-equation (lemmas-nfix-equation lib x))
          (lib (cdr x-equation))
          (strict (library-library-transport-argument lib strict (car x-equation) 2)))
         (library-library-lemma lib name goal strict
                                (list (proof-neg (proof-step-first int-x))
                                      (proof-neg (proof-step-first pos-x)))))))))

(defun countdowns-comparison (lib lower upper evidence)
  (countdowns-bind lib
   ((typed (countdowns-integer-steps lib (list lower upper) evidence) :library))
   (cons (library-library-cite lib "LESS-DIFFERENCE" (list lower upper) typed) lib)))

(defun countdowns-negation-citation (lib argument evidence)
  (let ((facts (proof-proof-facts (library-library-proof lib))))
    (cond
     ((and (proof-is-call argument *proof-minus*)
           (assoc-equal (proof-sym "SELF-DOUBLE-NEGATION" "ACL2") facts))
      (countdowns-bind lib
       ((term (proof-term-at argument 1))
        (typed (countdowns-type-of lib term evidence) :library))
       (cons (library-library-cite lib "DOUBLE-NEGATION" (list term) (list typed)) lib)))
     ((and (proof-is-call argument *proof-plus*)
           (assoc-equal (proof-sym "SELF-NEGATE-SUM" "ACL2") facts))
      (countdowns-bind lib
       ((typed (countdowns-integer-steps lib (cdr argument) evidence) :library))
       (cons (library-library-cite lib "NEGATE-SUM" (cdr argument) typed) lib)))
     (t (cons nil lib)))))

(defun countdowns-push-minus (n lib term evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "countdowns-push-minus") lib)
    (let ((proof (library-library-proof lib)))
      (cond
       ((proof-is-call term *proof-plus*)
        (countdowns-bind lib
         ((result (proof-proof-reflexive proof term))
          (left (proof-term-at term 1))
          (left (countdowns-push-minus (1- n) lib left evidence) :library)
          (result (if left
                      (proof-proof-rewrite (library-library-proof lib) result left '(1 2 1))
                    result))
          (right (proof-term-at term 2))
          (right (countdowns-push-minus (1- n) lib right evidence) :library)
          (result (if right
                      (proof-proof-rewrite (library-library-proof lib) result right '(1 2 2))
                    result))
          (literal (proof-step-first result))
          (reduced (proof-term-at literal 2)))
         (cons (if (equal reduced term) nil result) lib)))
       ((proof-is-call term *proof-minus*)
        (countdowns-bind lib ((argument (proof-term-at term 1)))
          (if (proof-is-call argument *proof-quote*)
              (cons (proof-proof-constant proof term) lib)
            (countdowns-bind lib ((result (countdowns-negation-citation lib argument evidence) :library))
              (if (not result)
                  (cons nil lib)
                (countdowns-bind lib
                 ((literal (proof-step-first result))
                  (right (proof-term-at literal 2))
                  (rest (countdowns-push-minus (1- n) lib right evidence) :library))
                 (cons (proof-proof-chain (library-library-proof lib) result (list rest)) lib)))))))
       (t (cons nil lib))))))

(defun countdowns-linear-remove-zero (lib step name term place evidence)
  (countdowns-bind lib
   ((typed (countdowns-type-of lib term evidence) :library)
    (zero-step (library-library-cite lib name (list term) (list typed))))
   (cons (proof-proof-rewrite (library-library-proof lib) step zero-step place) lib)))

(defun countdowns-linear-combine (n lib step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "countdowns-linear-combine") lib)
    (let ((proof (library-library-proof lib)))
      (countdowns-bind lib
       ((first (proof-step-first step))
        (node (library-linear-form-get first (cdr place))))
       (if (not (proof-is-call node *proof-plus*))
           (cons (proof-proof-tidy proof step) lib)
         (countdowns-bind lib ((pair (proof-list-of-length (cdr node) 2)))
           (let* ((a (car pair))
                  (rest (cadr pair))
                  (suffix (proof-is-call rest *proof-plus*)))
             (countdowns-bind lib ((b (if suffix (proof-term-at rest 1) rest)))
               (cond
                ((equal a *proof-zero*)
                 (countdowns-bind lib
                  ((step (countdowns-linear-remove-zero lib step "ADD-ZERO-LEFT" rest place evidence) :library))
                  (countdowns-linear-combine (1- n) lib step place evidence)))
                ((and (equal b *proof-zero*) (not suffix))
                 (countdowns-bind lib
                  ((step (countdowns-linear-remove-zero lib step "ADD-ZERO-RIGHT" a place evidence) :library))
                  (countdowns-linear-combine (1- n) lib step place evidence)))
                (t
                 (countdowns-bind lib ((combine (library-linear-combine-pair lib a b)))
                   (if (not combine)
                       (countdowns-linear-combine (1- n) lib step (append place '(2)) evidence)
                     (countdowns-bind lib
                      ((step (if suffix
                                 (proof-with-checked-results
                                  ((tail (proof-term-at rest 2))
                                   (association (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list a b tail)))
                                   (inverse (proof-proof-symmetric proof association)))
                                  (proof-proof-rewrite proof step inverse place))
                               step))
                       (step (proof-proof-rewrite proof step combine (if suffix (append place '(1)) place))))
                      (countdowns-linear-combine (1- n) lib step '(1 2) evidence))))))))))))))

(defun countdowns-linear-form (lib term evidence)
  (countdowns-bind lib
   ((opened (countdowns-push-minus 1000000 lib term evidence) :library)
    (step (or opened (proof-proof-reflexive (library-library-proof lib) term)))
    (step (library-linear-reassociate 1000000 lib step '(1 2)))
    (step (library-linear-sort 1000000 lib step '(1 2) nil)))
   (countdowns-linear-combine 1000000 lib step '(1 2) evidence)))

(defun countdowns-linear-equal (lib left right evidence)
  (countdowns-bind lib
   ((a (countdowns-linear-form lib left evidence) :library)
    (b (countdowns-linear-form lib right evidence) :library)
    (a-first (proof-step-first a))
    (b-first (proof-step-first b))
    (a-normal (proof-term-at a-first 2))
    (b-normal (proof-term-at b-first 2)))
   (if (equal a-normal b-normal)
       (let ((proof (library-library-proof lib)))
         (countdowns-bind lib ((inverse (proof-proof-symmetric proof b)))
           (cons (proof-proof-chain proof a (list inverse)) lib)))
     ;; A comparison with distinct normal forms cannot prove the identity.
     (cons nil lib))))

(defun countdowns-gap-proofs (lib value lower upper difference evidence)
  (countdowns-bind lib
   ((ordered (countdowns-comparison lib lower upper evidence) :library)
    (form (countdowns-linear-form lib (library-diff value difference) evidence) :library)
    (literal (proof-step-first form))
    (remainder (proof-term-at literal 2))
    (natural (countdowns-natural lib remainder) :library)
    (identity (countdowns-linear-equal lib (library-plus difference remainder) value evidence) :library))
   (cons (list ordered remainder natural identity) lib)))

(defun countdowns-positive-gap-candidate (lib value evidence premise)
  (proof-with-checked-results ((literal (proof-step-first premise)))
    (if (not (proof-is-call literal *proof-less*))
        (cons nil lib)
      (proof-with-checked-results ((literal (proof-list-of-length literal 3)))
        (let* ((lower (cadr literal))
               (upper (caddr literal))
               (difference (library-diff upper lower))
               (attempt (countdowns-gap-proofs lib value lower upper difference evidence))
               (lib (cdr attempt))
               (parts (car attempt)))
          (cond
           ((terms-proof-fallback-p parts) (cons nil lib))
           ((failure-p parts) parts)
           ((not (cadddr parts)) (cons nil lib))
           (t
            (let ((ordered (car parts))
                  (remainder (cadr parts))
                  (natural (caddr parts))
                  (identity (cadddr parts)))
              (proof-with-checked-results
               ((difference-type (countdowns-type-of lib difference evidence))
                (lib (cdr difference-type))
                (difference-type (car difference-type))
                (remainder-type (library-library-cite lib "NATURAL-INTEGER" (list remainder) (list natural)))
                (bound (library-library-cite lib "NATURAL-NONNEGATIVE" (list remainder) (list natural)))
                (strict (proof-proof-rewrite (library-library-proof lib) premise ordered '(1)))
                (growth (library-library-cite lib "POSITIVE-PLUS-NONNEGATIVE" (list remainder difference)
                                               (list remainder-type difference-type strict bound)))
                (result (proof-proof-rewrite (library-library-proof lib) growth identity '(1 2)))
                (step (proof-proof-tidy (library-library-proof lib) result)))
               (cons step lib))))))))))

(defun countdowns-positive-gap-derived (lib value evidence derived)
  (declare (xargs :measure (acl2-count derived)))
  (if (endp derived)
      (cons nil lib)
    (proof-with-checked-results
     ((result (countdowns-positive-gap-candidate lib value evidence (cdar derived))))
     (if (car result)
         result
       (countdowns-positive-gap-derived (cdr result) value evidence (cdr derived))))))

(defun countdowns-positive-gap (lib value evidence rulers)
  (proof-with-checked-results ((derived (rulers-rulers-derived rulers)))
    (countdowns-positive-gap-derived lib value evidence derived)))

(mutual-recursion
 (defun countdowns-clip-naturals (lib term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *lemmas-nfix*)
     (proof-with-checked-results ((value (proof-term-at term 1)))
       (let* ((natural (countdowns-natural lib value))
              (lib (cdr natural))
              (step (car natural)))
         (cond
          ((terms-proof-fallback-p step) (cons nil lib))
          ((failure-p step) step)
          (t
           (proof-with-checked-results
            ((identity (proof-proof-simplify (library-library-proof lib) (list *library-nfix* value)
                                             (list step) (list *library-nfix*)))
             (equation (lemmas-nfix-equation lib value))
             (lib (cdr equation))
             (step (proof-proof-chain (library-library-proof lib) (car equation) (list identity))))
            (cons step lib)))))))
    ((and (consp term) (or (proof-is-call term *proof-plus*) (proof-is-call term *proof-minus*)))
     (countdowns-clip-arguments lib (cdr term) term 1 nil))
    (t (cons nil lib))))

 (defun countdowns-clip-arguments (lib arguments term index proof)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       (cons proof lib)
     (proof-with-checked-results
      ((equality (countdowns-clip-naturals lib (car arguments))))
      (let ((lib (cdr equality)))
        (proof-with-checked-results
         ((proof (if (car equality)
                     (proof-with-checked-results
                      ((initial (or proof (proof-proof-reflexive (library-library-proof lib) term))))
                      (proof-proof-rewrite (library-library-proof lib) initial (car equality)
                                           (list 1 2 index)))
                   proof)))
         (countdowns-clip-arguments lib (cdr arguments) term (1+ index) proof)))))))

(defun countdowns-present-wrappers (names definitions)
  (cond ((endp names) nil)
        ((assoc-equal (car names) definitions)
         (cons (car names) (countdowns-present-wrappers (cdr names) definitions)))
        (t (countdowns-present-wrappers (cdr names) definitions))))

(defun countdowns-wrapper-definitions (lib)
  (countdowns-present-wrappers *countdowns-counter-wrappers*
                               (proof-proof-definitions (library-library-proof lib))))

(defun countdowns-counter-shift (lib child parent)
  (proof-with-checked-results ((shifted (countdowns-unit-shift lib child parent -1)))
    (if (car shifted)
        shifted
      (let ((lib (cdr shifted)))
        (proof-with-checked-results
         ((opened (proof-proof-simplify (library-library-proof lib) child nil
                                        (countdowns-wrapper-definitions lib)))
          (value (if opened (caddr (proof-step-first opened)) child))
          (clipped (countdowns-clip-naturals lib value))
          (value (if (car clipped) (caddr (proof-step-first (car clipped))) value))
          (shifted (countdowns-unit-shift (cdr clipped) value parent -1)))
         (if (not (car shifted))
             shifted
           (let ((lib (cdr shifted)))
             (proof-with-checked-results
              ((initial (or opened (proof-proof-reflexive (library-library-proof lib) child)))
               (step (proof-proof-chain (library-library-proof lib) initial
                                        (list (car clipped) (car shifted)))))
              (cons step lib)))))))))

(defun countdowns-update-rulers (rulers initial-lib lib)
  (if (equal (rulers-rulers-proof rulers) initial-lib)
      (rulers-rulers-with-proof rulers lib)
    rulers))

(defun countdowns-wrapped-countdown-with-rulers (lib goal rulers)
  (proof-with-checked-results ((goal (proof-list-of-length goal 3)))
    (let ((child (cadr goal))
          (parent (caddr goal)))
      (if (not (and (proof-is-call child *library-count*) (proof-is-call parent *library-count*)))
          (cons (list nil rulers) lib)
        (proof-with-checked-results
         ((parent (proof-term-at parent 1))
          (positive (rulers-rulers-find rulers (proof-neg (list (proof-sym "ZP" "ACL2") parent)))))
         (let ((rulers (cdr positive)))
           (if (not (car positive))
               (cons (list nil rulers) lib)
             (proof-with-checked-results
              ((child (proof-term-at child 1))
               (shifted (countdowns-counter-shift lib child parent)))
              (let* ((rulers (countdowns-update-rulers rulers lib (cdr shifted)))
                     (lib (cdr shifted))
                     (proof (library-library-proof lib)))
                (if (not (car shifted))
                    (cons (list nil rulers) lib)
                  (proof-with-checked-results
                   ((builtin (library-library-builtin lib 8 parent))
                    (strict (proof-proof-discharge proof builtin (car positive)))
                    (inverse (proof-proof-symmetric proof (car shifted)))
                    (result (proof-proof-rewrite proof strict inverse '(1 1 1)))
                    (step (proof-proof-tidy proof result)))
                   (cons (list step rulers) lib))))))))))))

(defun countdowns-wrapped-countdown (lib goal rulers)
  (proof-with-checked-results ((result (countdowns-wrapped-countdown-with-rulers lib goal rulers)))
    (cons (caar result) (cdr result))))

(defun countdowns-clipped-simplify-tests (lib value definitions derived integral positive-value)
  (declare (xargs :measure (acl2-count derived)))
  (if (endp derived)
      (list integral positive-value)
    (let ((premise (cdar derived)))
      (proof-with-checked-results ((literal (proof-step-first premise)))
        (if (or (proof-is-call literal *proof-integerp*) (proof-is-call literal *proof-less*))
            (proof-with-checked-results
             ((simplified (proof-proof-simplify-first (library-library-proof lib) premise nil definitions))
              (literal (proof-step-first simplified)))
             (countdowns-clipped-simplify-tests
              lib value definitions (cdr derived)
              (if (equal literal (library-integer value)) simplified integral)
              (if (equal literal (library-positive value)) simplified positive-value)))
          (countdowns-clipped-simplify-tests lib value definitions (cdr derived) integral positive-value))))))

(defun countdowns-integer-evidence (derived)
  (if (endp derived)
      nil
    (let ((premise (cdar derived)))
      (proof-with-checked-results
       ((literal (proof-step-first premise))
        (rest (countdowns-integer-evidence (cdr derived))))
       (if (proof-is-call literal *proof-integerp*) (cons premise rest) rest)))))

(defun countdowns-clipped-evidence (lib value integral positive-value rulers)
  (if (and integral positive-value)
      (cons (list integral positive-value) lib)
    (proof-with-checked-results
     ((derived (rulers-rulers-derived rulers))
      (simplified (countdowns-clipped-simplify-tests lib value (countdowns-wrapper-definitions lib)
                                                     derived integral positive-value)))
     (let ((integral (car simplified))
           (positive-value (cadr simplified)))
       (if (and integral positive-value)
           (cons (list integral positive-value) lib)
         (proof-with-checked-results ((types (countdowns-integer-evidence derived)))
           (let* ((typed (if integral (cons integral lib) (countdowns-type-of lib value types)))
                  (lib (cdr typed))
                  (integral (car typed)))
             (cond
              ((terms-proof-fallback-p integral) (cons (list nil positive-value) lib))
              ((failure-p integral) integral)
              (t
               (proof-with-checked-results
                ((positive-value (if positive-value
                                     (cons positive-value lib)
                                   (countdowns-positive-gap lib value types rulers))))
                (cons (list integral (car positive-value)) (cdr positive-value))))))))))))

(defun countdowns-clipped-decrease-with-rulers (lib goal rulers)
  (proof-with-checked-results ((goal (proof-list-of-length goal 3)))
    (let ((child (cadr goal))
          (parent (caddr goal)))
      (if (not (and (proof-is-call child *lemmas-nfix*) (proof-is-call parent *lemmas-nfix*)))
          (cons (list nil rulers) lib)
        (proof-with-checked-results
         ((value (proof-term-at parent 1))
          (child (proof-term-at child 1))
          (shifted (countdowns-counter-shift lib child value))
          (rulers (countdowns-update-rulers rulers lib (cdr shifted)))
          (lib (cdr shifted)))
         (if (not (car shifted))
             (cons (list nil rulers) lib)
           (proof-with-checked-results
            ((integral (rulers-rulers-find rulers (library-integer value)))
             (positive-value (rulers-rulers-find (cdr integral) (library-positive value)))
             (rulers (cdr positive-value))
             (evidence (countdowns-clipped-evidence lib value (car integral) (car positive-value) rulers))
             (rulers (countdowns-update-rulers rulers lib (cdr evidence)))
             (lib (cdr evidence)))
            (if (not (and (caar evidence) (cadar evidence)))
                (cons (list nil rulers) lib)
              (proof-with-checked-results
               ((updated (countdowns-nfix-step-lemma lib))
                (strict (library-library-cite updated "NFIX-UNIT-DECREASE" (list value) (car evidence)))
                (inverse (proof-proof-symmetric (library-library-proof updated) (car shifted)))
                (result (proof-proof-rewrite (library-library-proof updated) strict inverse '(1 1 1)))
                (step (proof-proof-tidy (library-library-proof updated) result)))
               (cons (list step (countdowns-update-rulers rulers lib updated)) updated))))))))))

(defun countdowns-clipped-decrease (lib goal rulers)
  (proof-with-checked-results ((result (countdowns-clipped-decrease-with-rulers lib goal rulers)))
    (cons (caar result) (cdr result))))
