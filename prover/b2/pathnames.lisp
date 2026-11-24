(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-pathnames-length* (proof-cl "LENGTH"))
(defconst *b2-pathnames-stringp* (proof-cl "STRINGP"))
(defconst *b2-pathnames-subseq* (proof-cl "SUBSEQ"))
(defconst *b2-pathnames-take* (proof-sym "TAKE" "ACL2"))
(defconst *b2-pathnames-zp* (proof-sym "ZP" "ACL2"))
(defconst *b2-pathnames-string* (proof-quote (proof-cl "STRING")))
(defconst *b2-pathnames-list* (proof-quote (proof-cl "LIST")))
(defconst *b2-pathnames-cancel* (proof-sym "CANCEL-DOT-DOTS" "ACL2"))
(defconst *b2-pathnames-parent* (proof-sym "GET-PARENT-DIRECTORY" "ACL2"))
(defconst *b2-pathnames-merge* (proof-sym "MERGE-USING-DOT-DOT" "ACL2"))

(defmacro b2-pathnames-normalize (lib term &optional evidence unfold rules)
  `(b2-tactics-tactics-normalize ,lib ,term ,evidence ,unfold ,rules 1500 nil))

(defmacro b2-pathnames-solve (lib goal &optional evidence unfold rules)
  `(b2-tactics-tactics-solve ,lib ,goal ,evidence ,unfold ,rules 0 nil))

(defmacro b2-pathnames-from-impossible (lib goal premise &optional evidence unfold)
  `(b2-tactics-tactics-from-impossible ,lib ,goal ,premise ,evidence ,unfold
                                      nil 1500 nil))

(defmacro b2-pathnames-use-fact (lib name target &optional evidence)
  `(b2-tactics-tactics-use-fact ,lib ,name ,target ,evidence nil nil 0 nil))

(defun b2-pathnames-first (step)
  (if step
      (proof-step-first step)
    '(:failure "failure" "")))

(defun b2-pathnames-length (term)
  (list *b2-pathnames-length* term))

(defun b2-pathnames-path-plan-doubled (term)
  (library-plus term term))

(defun b2-pathnames-plan-arguments (definitions arguments)
  (if (endp definitions)
      arguments
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3)))
     (b2-pathnames-plan-arguments
      (cdr definitions)
      (table-put arguments (car definition) (cadr definition))))))

(defun b2-pathnames-plan-formals (name arity arguments)
  (let ((entry (assoc-equal name arguments)))
    (if entry
        (proof-list-of-length (cdr entry) arity)
      '(:failure "tactic-rejected" ""))))

(defun b2-pathnames-path-plan (definitions)
  (proof-with-checked-results
   ((arguments (b2-pathnames-plan-arguments definitions nil))
    (full (b2-pathnames-plan-formals *b2-pathnames-cancel* 1 arguments))
    (parent (b2-pathnames-plan-formals *b2-pathnames-parent* 1 arguments))
    (merge (b2-pathnames-plan-formals *b2-pathnames-merge* 2 arguments)))
   (let ((p (b2-pathnames-length (car merge)))
         (s (b2-pathnames-length (cadr merge))))
     (list
      (cons *b2-pathnames-cancel*
            (b2-pathnames-path-plan-doubled (b2-pathnames-length (car full))))
      (cons *b2-pathnames-parent*
            (library-plus *proof-one*
                          (b2-pathnames-path-plan-doubled
                           (b2-pathnames-length (car parent)))))
      (cons *b2-pathnames-merge*
            (library-plus *proof-one*
                          (b2-pathnames-path-plan-doubled (library-plus p s))))))))

(defun b2-pathnames-support-take-base-consequent (nat-n stop lib n goal taken)
  (proof-with-checked-results
   ((typed (library-library-cite lib "NATURAL-INTEGER" (list n) (list nat-n)))
    (not-negative (library-library-cite lib "NATURAL-NONNEGATIVE"
                                        (list n) (list nat-n)))
    (not-positive (b2-pathnames-from-impossible lib (proof-neg (library-positive n))
                                                stop (list typed)
                                                (list *b2-pathnames-zp*)))
    (zero (b2-powers-zero-from-signs lib n typed not-negative not-positive)))
   (b2-pathnames-solve lib goal (list stop zero)
                       (list taken *b2-pathnames-take*
                             *b2-pathnames-zp* *library-len*))))

(defun b2-pathnames-support-take-base (stop lib n natural goal taken)
  (proof-with-checked-results
   ((nat-n (proof-proof-assume (library-library-proof lib) natural t))
    (consequent (b2-pathnames-support-take-base-consequent nat-n stop lib n goal taken)))
   (b2-tactics-tactics-implication lib natural goal (cons consequent lib))))

(defun b2-pathnames-support-take-advance-consequent
    (nat-n running hypothesis lib n child-n taken)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((typed (library-library-cite lib "NATURAL-INTEGER" (list n) (list nat-n)))
      (pos (b2-pathnames-from-impossible lib (library-positive n) running
                                         (list typed) (list *b2-pathnames-zp*)))
      (discrete (b2-pathnames-use-fact lib '("str" "integer-discrete")
                                       (proof-neg (library-lt n *proof-one*))
                                       (list typed pos)))
      (eq-lt (library-library-axiom lib "<-ON-OTHERS" (list n *proof-one*)))
      (bound (proof-proof-rewrite proof discrete eq-lt '(1 1)))
      (bound (proof-proof-simplify-first proof bound nil nil))
      (commutes (library-library-axiom lib "COMMUTATIVITY-OF-+" (list n *proof-neg-one*)))
      (bound (proof-proof-rewrite proof bound commutes '(1 1 1)))
      (bound (proof-proof-tidy proof bound))
      (child-type (library-library-type-of lib child-n (list typed)))
      (nat-child (library-library-cite lib "NATURAL-FROM-BOUNDS" (list child-n)
                                        (list child-type bound)))
      (result (proof-proof-modus-ponens proof hypothesis nat-child))
      (opened (b2-pathnames-normalize lib (list *library-len* taken) (list running)
                                     (list taken *library-len*) (list result)))
      (literal (b2-pathnames-first opened))
      (rhs (proof-term-at literal 2))
      (linear (b2-tactics-tactics-linear-equal lib rhs n (list typed))))
     (proof-proof-chain proof opened (list linear)))))

(defun b2-pathnames-support-take-advance (running hypothesis lib n natural goal child-n taken)
  (proof-with-checked-results
   ((nat-n (proof-proof-assume (library-library-proof lib) natural t))
    (consequent (b2-pathnames-support-take-advance-consequent
                 nat-n running hypothesis lib n child-n taken)))
   (b2-tactics-tactics-implication lib natural goal (cons consequent lib))))

(defun b2-pathnames-support-take (lib)
  (let* ((n *library-x*)
         (sequence *library-y*)
         (taken (list *b2-pathnames-take* n sequence))
         (natural (list *library-natp* n))
         (goal (proof-eq (list *library-len* taken) n))
         (formula (list *library-implies* natural goal))
         (test (list *b2-pathnames-zp* n))
         (child-n (library-plus *proof-neg-one* n))
         (bindings (list (list n child-n) (list sequence (list *library-cdr* sequence)))))
    (proof-with-checked-results
     ((smaller (library-library-builtin lib 9 n))
      (request (b2-tactics-tactics-by-induction lib formula n test smaller bindings
                                                nil nil nil))
      (advance (b2-pathnames-support-take-advance (cadddr (car request))
                                                  (car (cddddr (car request)))
                                                  (caddr (car request))
                                                  n natural goal child-n taken))
      (request (b2-tactics-tactics-by-induction lib formula n test smaller bindings
                                                nil advance nil))
      (base (b2-pathnames-support-take-base (cadddr (car request)) (caddr (car request))
                                            n natural goal taken))
      (proof (b2-tactics-tactics-by-induction lib formula n test smaller bindings
                                              base advance nil))
      (lemma (b2-tactics-tactics-add-lemma (cdr proof) "LENGTH-TAKE" (car proof) :none)))
     (cdr lemma))))

(defun b2-pathnames-support-length-natural (value tests lib)
  (declare (ignore tests))
  (library-library-natural lib value))

(defun b2-pathnames-length-natural-leaves (requests lib)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (reply (b2-pathnames-support-length-natural (car request) (cadr request) lib)))
      (cons (cons request reply)
            (if (failure-p reply)
                nil
              (b2-pathnames-length-natural-leaves (cdr requests) lib))))))

(defun b2-pathnames-support-length-base (atom-step lib length-same mapped)
  (proof-with-checked-results
   ((step (b2-pathnames-solve lib length-same (list atom-step)
                             (list mapped *library-len*))))
   (cons step lib)))

(defun b2-pathnames-support-length-advance (cons-step hypothesis lib length-same mapped)
  (let ((proof (library-library-proof lib))
        (test (list *b2-tactics-characterp* (list *library-car* *library-x*))))
    (proof-with-checked-results
     ((yes (proof-proof-assume proof test t))
      (no (proof-proof-assume proof test nil))
      (a (b2-pathnames-solve lib length-same (list cons-step yes)
                              (list mapped *library-len*) (list hypothesis)))
      (b (b2-pathnames-solve lib length-same (list cons-step no)
                              (list mapped *library-len*) (list hypothesis)))
      (step (proof-proof-cases proof test a b)))
     (cons step lib))))

(defun b2-pathnames-length-coerce (lib)
  (let ((mapped (list *b2-lists-make-chars* *library-x*))
        (coerce (list *b2-tactics-coerce* *library-x* *b2-pathnames-string*)))
    (proof-with-checked-results
     ((pred (b2-lists-mapped-recognizer lib (list *b2-lists-char-list* mapped)))
      (length-same (proof-eq (list *library-len* mapped) (list *library-len* *library-x*)))
      (request (b2-tactics-tactics-on-list lib length-same *library-x* nil nil nil))
      (advance (b2-pathnames-support-length-advance (cadddr (car request))
                                                    (car (cddddr (car request)))
                                                    (caddr (car request))
                                                    length-same mapped))
      (request (b2-tactics-tactics-on-list lib length-same *library-x* nil advance nil))
      (base (b2-pathnames-support-length-base (cadddr (car request))
                                              (caddr (car request)) length-same mapped))
      (preserved (b2-tactics-tactics-on-list lib length-same *library-x* base advance nil))
      (lib (cdr preserved))
      (proof (library-library-proof lib))
      (completed (library-library-axiom lib "COMPLETION-OF-COERCE"
                                         (list *library-x* *b2-pathnames-string*)))
      (literal (proof-step-first completed))
      (rhs (proof-term-at literal 2))
      (normal (b2-pathnames-normalize lib rhs))
      (completed (proof-proof-chain proof completed (list normal)))
      (literal (proof-step-first completed))
      (coerced (proof-term-at literal 2))
      (inverse (b2-pathnames-use-fact
                lib (proof-sym "COERCE-INVERSE-1" "ACL2")
                (proof-eq (list *b2-tactics-coerce* coerced *b2-pathnames-list*) mapped)
                (list pred)))
      (reverse (proof-proof-symmetric proof completed))
      (inverse (proof-proof-rewrite proof inverse reverse '(1 1 1)))
      (inverse (proof-proof-tidy proof inverse))
      (string-step (b2-pathnames-use-fact lib '("str" "stringp-coerce")
                                         (list *b2-pathnames-stringp* coerce)))
      (term (b2-pathnames-length coerce))
      (length-equation (b2-pathnames-normalize lib term (list string-step) (list term)))
      (length-equation (proof-proof-rewrite proof length-equation inverse '(1 2 1)))
      (result (proof-proof-chain proof length-equation (list (car preserved))))
      (lemma (b2-tactics-tactics-add-lemma lib "LENGTH-COERCE" result :none)))
     (cdr lemma))))

(defun b2-pathnames-support-length (lib)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal (proof-sym "B2-LENGTH-NATURAL" "ACL2") (proof-proof-facts proof))
        lib
      (let ((template (list *library-natp* *proof-result*)))
        (proof-with-checked-results
         ((opened (proof-proof-unfold proof (b2-pathnames-length *library-x*)))
          (literal (proof-step-first opened))
          (value (proof-term-at literal 2))
          (requests (proof-proof-by-value-leaves proof value nil))
          (natural (proof-proof-by-value proof value template
                                         (b2-pathnames-length-natural-leaves requests lib)
                                         nil))
          (reverse (proof-proof-symmetric proof opened))
          (step (proof-proof-rewrite-result proof natural reverse template *proof-result*))
          (lemma (b2-tactics-tactics-add-lemma lib "LENGTH-NATURAL" step :none))
          (lib (b2-pathnames-length-coerce (cdr lemma))))
         (b2-pathnames-support-take lib))))))

(mutual-recursion
 (defun b2-pathnames-path-ordinal-natural (term lib)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *b2-pathnames-length*)
     (proof-with-checked-results ((arg (proof-term-at term 1)))
       (proof-proof-fact (library-library-proof lib)
                         (proof-sym "B2-LENGTH-NATURAL" "ACL2")
                         (list (list *library-x* arg)))))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results
      ((steps (b2-pathnames-path-ordinal-natural-args (cdr term) lib)))
      (library-library-cite lib "NATURAL-SUM" (cdr term) steps)))
    (t (library-library-natural lib term))))

 (defun b2-pathnames-path-ordinal-natural-args (terms lib)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (b2-pathnames-path-ordinal-natural (car terms) lib))
       (rest (b2-pathnames-path-ordinal-natural-args (cdr terms) lib)))
      (cons first rest)))))

(defun b2-pathnames-path-ordinal (lib measure)
  (proof-with-checked-results
   ((lib (b2-pathnames-support-length lib))
    (natural (b2-pathnames-path-ordinal-natural measure lib))
    (step (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural))))
   (cons step lib)))

(mutual-recursion
 (defun b2-pathnames-length-terms (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((proof-is-call term *b2-pathnames-length*) (list term))
         ((null term) '(:failure "tactic-rejected" ""))
         ((and (consp term) (proof-compound term)
               (member-equal (car term) (list *proof-plus* *proof-minus* *proof-less*)))
          (b2-pathnames-length-terms-args (cdr term)))
         (t nil)))

 (defun b2-pathnames-length-terms-args (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (b2-pathnames-length-terms (car terms)))
       (rest (b2-pathnames-length-terms-args (cdr terms))))
      (append first rest)))))

(defun b2-pathnames-extend-sources (pending sources)
  (if (endp pending)
      sources
    (proof-with-checked-results ((term (proof-term-at (car pending) 1)))
      (if (proof-is-call term *b2-pathnames-subseq*)
          (proof-with-checked-results
           ((new (b2-pathnames-length-terms-args (cddr term))))
           (b2-pathnames-extend-sources (cdr pending) (append sources new)))
        (b2-pathnames-extend-sources (cdr pending) sources)))))

(defun b2-pathnames-written-sources (sources)
  (if (endp sources)
      nil
    (proof-with-checked-results
     ((text (proof-write (car sources)))
      (rest (b2-pathnames-written-sources (cdr sources))))
     (cons (list text (car sources)) rest))))

(defun b2-pathnames-insert-source (source ordered)
  (if (and (consp ordered) (string< (caar ordered) (car source)))
      (cons (car ordered) (b2-pathnames-insert-source source (cdr ordered)))
    (cons source ordered)))

(defun b2-pathnames-sort-sources (sources)
  (if (endp sources)
      nil
    (b2-pathnames-insert-source (car sources)
                                (b2-pathnames-sort-sources (cdr sources)))))

(defun b2-pathnames-source-naturals (lib ordered-sources)
  (if (endp ordered-sources)
      nil
    (let ((term (cadar ordered-sources)))
      (proof-with-checked-results
       ((arg (proof-term-at term 1))
        (natural (proof-proof-fact (library-library-proof lib)
                                   (proof-sym "B2-LENGTH-NATURAL" "ACL2")
                                   (list (list *library-x* arg))))
        (rest (b2-pathnames-source-naturals lib (cdr ordered-sources))))
       (cons (cons term natural) rest)))))

(defun b2-pathnames-source-types (lib naturals)
  (if (endp naturals)
      nil
    (proof-with-checked-results
     ((step (library-library-cite lib "NATURAL-INTEGER" (list (caar naturals))
                                  (list (cdar naturals))))
      (rest (b2-pathnames-source-types lib (cdr naturals))))
     (cons step rest))))

(defun b2-pathnames-natural-fact-types (lib facts)
  (if (endp facts)
      nil
    (let ((term (caar facts)))
      (if (proof-is-call term *library-natp*)
          (proof-with-checked-results
           ((arg (proof-term-at term 1))
            (step (library-library-cite lib "NATURAL-INTEGER" (list arg)
                                        (list (cdar facts))))
            (rest (b2-pathnames-natural-fact-types lib (cdr facts))))
           (cons step rest))
        (b2-pathnames-natural-fact-types lib (cdr facts))))))

(defun b2-pathnames-integer-fact-types (facts)
  (if (endp facts)
      nil
    (proof-with-checked-results
     ((head (proof-term-at (caar facts) 0))
      (rest (b2-pathnames-integer-fact-types (cdr facts))))
     (if (equal head *proof-integerp*) (cons (cdar facts) rest) rest))))

(defun b2-pathnames-pathcomparison-init (lib goal evidence)
  (proof-with-checked-results ((facts (b2-tactics-tactics-evidence lib evidence)))
    (if (integerp goal)
        '(:failure "tactic-rejected" "")
      (proof-with-checked-results
       ((sources (b2-pathnames-length-terms-args (cdr goal)))
        (sources (proof-unique sources))
        (sources (b2-pathnames-extend-sources sources sources))
        (written (b2-pathnames-written-sources (proof-unique sources)))
        (naturals (b2-pathnames-source-naturals lib (b2-pathnames-sort-sources written)))
        (source-types (b2-pathnames-source-types lib naturals))
        (natural-types (b2-pathnames-natural-fact-types lib facts))
        (integer-types (b2-pathnames-integer-fact-types facts)))
       (list :b2-pathnames-pathcomparison lib goal facts naturals
             (append source-types natural-types integer-types))))))

(defun b2-pathnames-pathcomparison-lib (self)
  (cadr self))

(defun b2-pathnames-pathcomparison-goal (self)
  (caddr self))

(defun b2-pathnames-pathcomparison-facts (self)
  (cadddr self))

(defun b2-pathnames-pathcomparison-naturals (self)
  (car (cddddr self)))

(defun b2-pathnames-pathcomparison-types (self)
  (cadr (cddddr self)))

(defun b2-pathnames-pathcomparison-require (self term)
  (let ((entry (assoc-equal term (b2-pathnames-pathcomparison-facts self))))
    (if entry
        (cdr entry)
      (b2-tactics-unproved))))

(defun b2-pathnames-pathcomparison-at-least-zero (self term)
  (let ((lib (b2-pathnames-pathcomparison-lib self)))
    (proof-with-checked-results
     ((natural (or (table-get (b2-pathnames-pathcomparison-naturals self) term nil)
                   (table-get (b2-pathnames-pathcomparison-facts self)
                                (list *library-natp* term) nil)
                   (library-library-natural lib term))))
     (library-library-cite lib "NATURAL-NONNEGATIVE" (list term) (list natural)))))

(defun b2-pathnames-pathcomparison-integer (self term)
  (library-library-type-of (b2-pathnames-pathcomparison-lib self)
                           term (b2-pathnames-pathcomparison-types self)))

(defun b2-pathnames-suffix-lower-bound (self start stop)
  (if (equal start *proof-zero*)
      (b2-pathnames-pathcomparison-at-least-zero self stop)
    (proof-with-checked-results
     ((left (and (proof-is-call start *proof-plus*) (proof-term-at start 1))))
     (if (equal left *proof-one*)
         (proof-with-checked-results
          ((right (proof-term-at start 2))
           (ordered (b2-pathnames-pathcomparison-require self (library-lt right stop))))
          (b2-butlast-integer-after-successor
           (b2-pathnames-pathcomparison-lib self)
           ordered (b2-pathnames-pathcomparison-types self)))
       (b2-pathnames-pathcomparison-require self (proof-neg (library-lt stop start)))))))

(defun b2-pathnames-suffix-take-length (self taken amount natural)
  (let* ((lib (b2-pathnames-pathcomparison-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((list-arg (proof-term-at taken 2))
      (take-length (proof-proof-fact proof (proof-sym "B2-LENGTH-TAKE" "ACL2")
                                     (list (list *library-x* amount)
                                           (list *library-y* list-arg))))
      (take-length (proof-proof-modus-ponens proof take-length natural))
      (count-arg (proof-term-at taken 1)))
     (if (equal count-arg amount)
         take-length
       (proof-with-checked-results
        ((normalized (b2-tactics-tactics-linear-equal
                      lib amount count-arg (b2-pathnames-pathcomparison-types self)))
         (rewritten (proof-proof-rewrite proof take-length normalized '(1 1 1 1))))
        (proof-proof-tidy proof rewritten))))))

(defun b2-pathnames-pathcomparison-suffix-length (self term)
  (let* ((lib (b2-pathnames-pathcomparison-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((subseq (proof-term-at term 1))
      (parts (proof-list-of-length subseq 4))
      (source (cadr parts))
      (start (caddr parts))
      (stop (cadddr parts))
      (string-step (b2-pathnames-pathcomparison-require self
                                                      (list *b2-pathnames-stringp* source)))
      (stop-int (b2-pathnames-pathcomparison-integer self stop))
      (stop-true (b2-pathnames-from-impossible lib stop stop-int))
      (lower (b2-pathnames-suffix-lower-bound self start stop))
      (amount (library-diff stop start))
      (comparison (library-library-axiom lib "<-ON-OTHERS" (list stop start)))
      (sign (proof-proof-rewrite proof lower comparison '(1 1)))
      (sign (proof-proof-tidy proof sign))
      (amount-int (b2-pathnames-pathcomparison-integer self amount))
      (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list amount)
                                     (list amount-int sign)))
      (sliced (b2-pathnames-normalize lib subseq (list string-step stop-true)
                                     (list *b2-pathnames-subseq* (proof-sym "SUBSEQ-LIST" "ACL2"))))
      (literal (b2-pathnames-first sliced))
      (coerce (proof-term-at literal 2))
      (taken (proof-term-at coerce 1))
      (coerced-length (proof-proof-fact proof (proof-sym "B2-LENGTH-COERCE" "ACL2")
                                        (list (list *library-x* taken))))
      (take-length (b2-pathnames-suffix-take-length self taken amount natural))
      (result (proof-proof-chain proof coerced-length (list take-length)))
      (reverse (proof-proof-symmetric proof sliced))
      (result (proof-proof-rewrite proof result reverse '(1 1 1))))
     (proof-proof-tidy proof result))))

(defun b2-pathnames-additive-cancel (self actuals before)
  (let* ((lib (b2-pathnames-pathcomparison-lib self))
         (proof (library-library-proof lib))
         (types (b2-pathnames-pathcomparison-types self)))
    (proof-with-checked-results
     ((arg (proof-term-at actuals 0))
      (a (b2-pathnames-length arg))
      (b (proof-term-at before 1))
      (small (b2-pathnames-pathcomparison-require self (library-lt a b)))
      (compare (library-library-comparison lib a b types))
      (delta (proof-proof-rewrite proof small compare '(1))))
     (library-library-cite lib "POSITIVE-SUM" (list (library-diff b a) (library-diff b a))
                           (list delta delta)))))

(defun b2-pathnames-additive-merge (self parent)
  (let* ((lib (b2-pathnames-pathcomparison-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((arg (proof-term-at parent 1))
      (old (b2-pathnames-length arg))
      (new (b2-pathnames-length parent))
      (bound (b2-pathnames-pathcomparison-require self (proof-neg (library-lt old new))))
      (difference (library-diff old new))
      (comparison (library-library-axiom lib "<-ON-OTHERS" (list old new)))
      (bound (proof-proof-rewrite proof bound comparison '(1 1)))
      (bound (proof-proof-tidy proof bound))
      (typed-a (b2-pathnames-pathcomparison-integer self difference))
      (typed-b (b2-pathnames-pathcomparison-integer self difference))
      (double (library-library-cite lib "NONNEGATIVE-SUM"
                                     (list difference difference)
                                     (list typed-a typed-b bound bound)))
      (sum (library-plus difference difference))
      (six (proof-quote 6))
      (sum-typed (b2-pathnames-pathcomparison-integer self sum))
      (six-typed (library-library-type-of lib six nil))
      (six-positive (b2-pathnames-solve lib (library-positive six))))
     (library-library-cite lib "POSITIVE-PLUS-NONNEGATIVE" (list sum six)
                           (list sum-typed six-typed six-positive double)))))

(defun b2-pathnames-additive-parent (self length-s)
  (let ((lib (b2-pathnames-pathcomparison-lib self))
        (three (proof-quote 3)))
    (proof-with-checked-results
     ((lower (b2-pathnames-pathcomparison-require self (proof-neg (library-lt length-s three))))
      (zero-typed (library-library-type-of lib *proof-zero* nil))
      (three-typed (library-library-type-of lib three nil))
      (length-typed (b2-pathnames-pathcomparison-integer self length-s))
      (three-positive (b2-pathnames-solve lib (library-positive three)))
      (positive-s (library-library-cite lib "LESS-THEN-WEAK" (list *proof-zero* three length-s)
                                        (list zero-typed three-typed length-typed
                                              three-positive lower))))
     (library-library-cite lib "POSITIVE-SUM" (list length-s length-s) (list positive-s positive-s)))))

(defun b2-pathnames-additive-normalized (self after before)
  (let ((lib (b2-pathnames-pathcomparison-lib self)))
    (proof-with-checked-results
     ((normal (b2-tactics-tactics-linear-form lib (library-diff before after)
                                             (b2-pathnames-pathcomparison-types self)))
      (literal (b2-pathnames-first normal))
      (normalized (proof-term-at literal 2)))
     (b2-pathnames-solve lib (library-positive normalized)))))

(defun b2-pathnames-pathcomparison-additive-bound (self call after before)
  (let ((caller (termination-call-caller call))
        (callee (termination-call-callee call)))
    (cond
     ((and (equal caller *b2-pathnames-cancel*) (equal callee *b2-pathnames-cancel*))
      (b2-pathnames-additive-cancel self (termination-call-actuals call) before))
     ((and (equal caller *b2-pathnames-merge*) (equal callee *b2-pathnames-merge*))
      (proof-with-checked-results ((parent (proof-term-at (termination-call-actuals call) 0)))
        (if (proof-is-call parent *b2-pathnames-parent*)
            (b2-pathnames-additive-merge self parent)
          (b2-pathnames-additive-normalized self after before))))
     ((and (equal caller *b2-pathnames-merge*) (equal callee *b2-pathnames-parent*))
      (proof-with-checked-results
       ((sum (proof-term-at before 2))
        (left (proof-term-at sum 1))
        (length-s (proof-term-at left 2)))
       (if (proof-is-call length-s *b2-pathnames-length*)
           (b2-pathnames-additive-parent self length-s)
         (b2-pathnames-additive-normalized self after before))))
     (t (b2-pathnames-additive-normalized self after before)))))

(defun b2-pathnames-comparison-rule (self term)
  (proof-with-checked-results ((value (proof-term-at term 1)))
    (if (proof-is-call value *b2-pathnames-subseq*)
        (b2-pathnames-pathcomparison-suffix-length self term)
      (proof-with-checked-results
       ((equation (b2-pathnames-normalize
                   (b2-pathnames-pathcomparison-lib self) term
                   (table-values (b2-pathnames-pathcomparison-facts self))
                   (list term *library-len*))))
       (if equation
           (proof-with-checked-results
            ((literal (proof-step-first equation))
             (rhs (proof-term-at literal 2)))
            (and (proof-is-call rhs *proof-quote*) equation))
         nil)))))

(defun b2-pathnames-comparison-rules (self naturals)
  (if (endp naturals)
      nil
    (proof-with-checked-results
     ((first (b2-pathnames-comparison-rule self (caar naturals)))
      (rest (b2-pathnames-comparison-rules self (cdr naturals))))
     (if first (cons first rest) rest))))

(defun b2-pathnames-pathcomparison-prove (self call)
  (let* ((lib (b2-pathnames-pathcomparison-lib self))
         (proof (library-library-proof lib))
         (goal (b2-pathnames-pathcomparison-goal self)))
    (proof-with-checked-results
     ((rules (b2-pathnames-comparison-rules self (b2-pathnames-pathcomparison-naturals self)))
      (equation (b2-pathnames-normalize lib goal nil nil rules))
      (literal (if equation (proof-step-first equation) nil))
      (normal (if equation (proof-term-at literal 2) goal))
      (parts (proof-list-of-length normal 3))
      (after (cadr parts))
      (before (caddr parts))
      (bound (b2-pathnames-pathcomparison-additive-bound self call after before))
      (comparison (b2-tactics-tactics-less-from-difference
                   lib after before bound (b2-pathnames-pathcomparison-types self)))
      (after-int (b2-pathnames-pathcomparison-integer self after))
      (before-int (b2-pathnames-pathcomparison-integer self before))
      (order (library-library-cite lib "FINITE-ORDER" (list after before)
                                   (list after-int before-int)))
      (proved (proof-proof-transport proof comparison order)))
     (if equation (proof-proof-transport proof proved equation) proved))))
