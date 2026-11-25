(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-search-wrappers*
  '(("sym" "ACL2" "CASE-SPLIT") ("sym" "ACL2" "FORCE")
    ("sym" "ACL2" "HIDE") ("sym" "ACL2" "SYNP")))

(mutual-recursion
 (defun b2-search-terms (term)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((not (proof-compound term)) (list term))
         ((endp term) (proof-term-at term 0))
         ((equal (car term) *proof-quote*) (list term))
         (t (proof-with-checked-results ((args (b2-search-terms-args (cdr term))))
              (cons term args)))))
 (defun b2-search-terms-args (args)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((first (b2-search-terms (car args)))
       (rest (b2-search-terms-args (cdr args))))
      (append first rest)))))

(mutual-recursion
 (defun b2-search-size (term limit)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((<= limit 1) limit)
         ((not (proof-compound term)) 1)
         ((endp term) (proof-term-at term 0))
         ((equal (car term) *proof-quote*) 1)
         (t (proof-with-checked-results
             ((count (b2-search-size-args (cdr term) (1- limit))))
             (1+ count)))))
 (defun b2-search-size-args (args limit)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       0
     (proof-with-checked-results ((count (b2-search-size (car args) limit)))
       (if (>= count limit)
           count
         (proof-with-checked-results
          ((rest (b2-search-size-args (cdr args) (- limit count))))
          (+ count rest)))))))

(defun b2-search-head (term)
  (if (proof-compound term)
      (proof-term-at term 0)
    :none))

(defun b2-search-beta-predicate (term)
  (proof-with-checked-results ((operator (b2-search-head term)))
    (if (and (proof-compound operator) (equal (len term) 2))
        (proof-with-checked-results ((lambda-form (proof-list-of-length operator 3)))
          (let ((formals (cadr lambda-form))
                (body (caddr lambda-form)))
            (cond ((integerp formals)
                   '(:failure "tactic-rejected" ""))
                  ((and (equal (len formals) 1)
                        (proof-compound body)
                        (equal (cdr body) formals))
                   (list (car body) (cadr term)))
                  (t nil))))
      nil)))

(defun b2-search-guards (term)
  (declare (xargs :measure (acl2-count term)))
  (if (proof-is-call term *proof-if*)
      (proof-with-checked-results ((other (proof-term-at term 3)))
        (if (equal other *proof-false*)
            (proof-with-checked-results
             ((left (b2-search-guards (cadr term)))
              (right (b2-search-guards (caddr term))))
             (append left right))
          (list term)))
    (list term)))

(mutual-recursion
 (defun b2-search-boolean-test (term)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((proof-is-call term *proof-if*)
          (proof-with-checked-results ((test (proof-term-at term 1)))
            (if (proof-is-call (cadr term) *proof-if*)
                (b2-search-boolean-test (cadr term))
              test)))
         ((not (proof-compound term)) :none)
         ((endp term) (proof-term-at term 0))
         ((equal (car term) *proof-quote*) :none)
         (t (b2-search-boolean-test-args (cdr term)))))
 (defun b2-search-boolean-test-args (args)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       :none
     (let ((test (b2-search-boolean-test (car args))))
       (if (eq test :none)
           (b2-search-boolean-test-args (cdr args))
         test)))))

(defun b2-search-make-search (lib index equations beta-paths fuel rules path)
  (list :b2-search lib index equations beta-paths fuel rules path))

(defun b2-search-search-lib (search) (nth 1 search))
(defun b2-search-search-index (search) (nth 2 search))
(defun b2-search-search-equations (search) (nth 3 search))
(defun b2-search-search-beta-paths (search) (nth 4 search))
(defun b2-search-search-fuel (search) (nth 5 search))
(defun b2-search-search-rules (search) (nth 6 search))
(defun b2-search-search-path (search) (nth 7 search))

(defun b2-search-search-with-lib (search lib)
  (update-nth 1 lib search))

(defun b2-search-search-with-fuel (search fuel)
  (update-nth 5 fuel search))

(defun b2-search-search-with-path (search path)
  (update-nth 7 path search))

(defun b2-search-proof (search)
  (library-library-proof (b2-search-search-lib search)))

(defun b2-search-bucket-append (index key row)
  (table-put index key (append (table-get index key nil) (list row))))

(defun b2-search-index-equation (search name formula target)
  (if (not (proof-is-call target *proof-equal*))
      search
    (proof-with-checked-results
     ((left (proof-term-at target 1))
      (operator (b2-search-head left)))
     (if (member-equal operator (list :none *proof-equal* *proof-if* *proof-quote*))
         search
       (update-nth 3
                   (b2-search-bucket-append (b2-search-search-equations search)
                                           operator (list name formula left))
                   search)))))

(defun b2-search-index-formula (search name formula)
  (proof-with-checked-results ((operator (b2-search-head formula)))
    (let* ((row (list name formula))
           (index (b2-search-bucket-append (b2-search-search-index search)
                                          operator row))
           (search (update-nth 2 index search)))
      (if (proof-is-call formula *library-implies*)
          (proof-with-checked-results
           ((target (proof-term-at formula 2))
            (target-head (b2-search-head target)))
           (let ((search (update-nth 2 (b2-search-bucket-append index target-head row)
                                     search)))
             (b2-search-index-equation search name formula target)))
        (b2-search-index-equation search name formula formula)))))

(defun b2-search-note-beta-path (search name place)
  (update-nth 4 (table-put (b2-search-search-beta-paths search) name place) search))

(defun b2-search-index-fact (search name clause)
  (if (assoc-equal name (proof-proof-definitions (b2-search-proof search)))
      search
    (proof-with-checked-results
     ((formula (proof-term-at clause 0))
      (reduced (b2-search-beta-predicate formula)))
     (cond (reduced
            (b2-search-index-formula (b2-search-note-beta-path search name '(1))
                                     name reduced))
           ((proof-is-call formula *library-implies*)
            (proof-with-checked-results
             ((target (proof-term-at formula 2))
              (reduced (b2-search-beta-predicate target)))
             (if reduced
                 (b2-search-index-formula (b2-search-note-beta-path search name '(1 2))
                                          name (list (car formula) (cadr formula) reduced))
               (b2-search-index-formula search name formula))))
           (t (b2-search-index-formula search name formula))))))

(defun b2-search-index-facts (facts search)
  (if (endp facts)
      search
    (proof-with-checked-results
     ((search (b2-search-index-fact search (caar facts) (cdar facts))))
     (b2-search-index-facts (cdr facts) search))))

(defun b2-search-search-init (lib fuel rules)
  (let ((search (b2-search-make-search lib nil nil nil fuel rules nil)))
    (b2-search-index-facts (proof-proof-facts (b2-search-proof search)) search)))

(defun b2-search-search-short-definition (search operator)
  (let ((entry (assoc-equal operator (proof-proof-definitions (b2-search-proof search)))))
    (if (not entry)
        nil
      (proof-with-checked-results
       ((body (proof-term-at (cdr entry) 1))
        (count (b2-search-size body 85)))
       (< count 85)))))

(defun b2-search-constructed-arg-p (args)
  (and (consp args)
       (or (proof-is-call (car args) *proof-cons*)
           (proof-is-call (car args) *proof-quote*)
           (b2-search-constructed-arg-p (cdr args)))))

(defund b2-search-add-option (term search definitions)
  (proof-with-checked-results
   ((operator (b2-search-head term))
    (short (and (not (eq operator :none))
                (b2-search-search-short-definition search operator))))
   (if (not short)
       definitions
     (let ((roots (car definitions))
           (names (cadr definitions)))
       (list (if (or (member-equal operator *b2-search-wrappers*)
                     (b2-search-constructed-arg-p (cdr term)))
                 (cons term roots)
               roots)
             (if (member-equal operator names) names (cons operator names)))))))

(mutual-recursion
 (defun b2-search-option-subtree (term search definitions)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (proof-with-checked-results ((definitions (b2-search-add-option term search definitions)))
     (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
         definitions
       (b2-search-option-arguments (cdr term) search definitions))))
 (defun b2-search-option-arguments (args search definitions)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       definitions
     (proof-with-checked-results
      ((definitions (b2-search-option-subtree (car args) search definitions)))
      (b2-search-option-arguments (cdr args) search definitions)))))

(defun b2-search-option-focus (goal names)
  (let ((operand (if (< 1 (len goal)) (cadr goal) :none)))
    (cond ((and (proof-is-call goal *proof-equal*)
                (proof-compound operand)
                (equal (len operand) 2))
           (proof-with-checked-results ((operator (b2-search-head (cadr operand))))
             (and (member-equal operator names) (list (cadr operand)))))
          ((equal (len goal) 2)
           (proof-with-checked-results ((operator (b2-search-head operand)))
             (and (member-equal operator names) (list operand))))
          (t nil))))

(defun b2-search-options-definitions (search goal)
  (proof-with-checked-results ((definitions (b2-search-option-subtree goal search '(nil nil))))
    (list (proof-unique (reverse (car definitions))) (reverse (cadr definitions)))))

(defun b2-search-name-options (goal names)
  (if (endp names)
      nil
    (proof-with-checked-results ((focus (b2-search-option-focus goal names)))
      (append (and focus (list (list focus nil)))
              (list (list names nil))
              (and (<= (len names) 4) (list (list names t)))))))

(defun b2-search-rejected-step-p (value)
  (or (b2-tactics-unproved-p value)
      (and (failure-p value) (member-equal (cadr value) '("value" "inapplicable")))))

(defun b2-search-unfold-premise-p (search operator term)
  (if (member-equal operator *b2-search-wrappers*)
      t
    (proof-with-checked-results ((short (b2-search-search-short-definition search operator)))
      (if short
          (proof-with-checked-results ((name (proof-term-at operator 2)))
            (and (text-ends-with name '("P" "QUIV")) (<= (len term) 3)))
        nil))))

(defun b2-search-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun b2-search-extend-rewrite (proof step equation operator)
  (cond ((b2-tactics-unproved-p equation) nil)
        ((failure-p equation) equation)
        ((not equation) nil)
        (t
         (proof-with-checked-results
          ((literal (b2-search-step-right equation))
           (head (b2-search-head literal)))
          (if (or (equal head *proof-if*)
                  (equal head *proof-equal*)
                  (member-equal operator *b2-search-wrappers*))
              (proof-with-checked-results
               ((rewritten (proof-proof-rewrite proof step equation '(1)))
                (tidied (proof-proof-tidy proof rewritten)))
               (list tidied))
            nil)))))

(defun b2-search-extend-step (search term step operator)
  (let ((lib (b2-search-search-lib search))
        (proof (b2-search-proof search)))
    (cond
     ((equal operator *library-natp*)
      (proof-with-checked-results
       ((integer (library-library-cite lib "NATURAL-INTEGER" (cdr term) (list step)))
        (nonnegative
         (library-library-cite lib "NATURAL-NONNEGATIVE" (cdr term) (list step))))
       (list integer nonnegative)))
     (t
      (proof-with-checked-results ((unfold (b2-search-unfold-premise-p search operator term)))
        (if unfold
            (b2-search-extend-rewrite
             proof step (b2-tactics-tactics-normalize lib term nil (list term) nil 100 nil)
             operator)
          nil))))))

(defun b2-search-extend-known (known search)
  (if (endp known)
      nil
    (let ((term (caar known)))
      (proof-with-checked-results
       ((added (if (proof-compound term)
                   (proof-with-checked-results ((operator (b2-search-head term)))
                     (b2-search-extend-step search term (cdar known) operator))
                 nil))
        (rest (b2-search-extend-known (cdr known) search)))
       (append added rest)))))

(defun b2-search-search-extend (search premise)
  (proof-with-checked-results
   ((known (b2-tactics-tactics-evidence (b2-search-search-lib search) (list premise)))
    (derived (b2-search-extend-known known search)))
   (cons premise derived)))

(defun b2-search-match-known (items operator condition bound)
  (if (endp items)
      bound
    (proof-with-checked-results
     ((head (b2-search-head (caar items)))
      (matched (and (equal head operator)
                    (b2-tactics-match condition (caar items) bound))))
     (if (car matched)
         (cdr matched)
       (b2-search-match-known (cdr items) operator condition bound)))))

(defun b2-search-bind-guard (condition known bound)
  (proof-with-checked-results ((instantiated (proof-subst condition bound)))
    (if (assoc-equal instantiated known)
        bound
      (proof-with-checked-results ((operator (b2-search-head instantiated)))
        (if (eq operator :none)
            bound
          (b2-search-match-known known operator condition bound))))))

(defun b2-search-bind-guards (condition known bound)
  (declare (xargs :measure (acl2-count condition)))
  (if (proof-is-call condition *proof-if*)
      (proof-with-checked-results ((other (proof-term-at condition 3)))
        (if (equal other *proof-false*)
            (proof-with-checked-results
             ((bound (b2-search-bind-guards (cadr condition) known bound)))
             (b2-search-bind-guards (caddr condition) known bound))
          (b2-search-bind-guard condition known bound)))
    (b2-search-bind-guard condition known bound)))

(defun b2-search-search-bindings (search pattern goal formula known)
  (declare (ignore search))
  (proof-with-checked-results ((matched (b2-tactics-match pattern goal nil)))
    (cond ((not (car matched)) :none)
          ((not (proof-is-call formula *library-implies*)) (cdr matched))
          (t (proof-with-checked-results ((condition (proof-term-at formula 1)))
               (b2-search-bind-guards condition known (cdr matched)))))))

(mutual-recursion
 (defun b2-search-any-term (term test value)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((if (eq test :contains)
              (equal term value)
            (and (b2-tactics-variable term) (not (assoc-equal term value))))
          t)
         ((not (proof-compound term)) nil)
         ((endp term) (proof-term-at term 0))
         ((equal (car term) *proof-quote*) nil)
         (t (b2-search-any-term-args (cdr term) test value))))
 (defun b2-search-any-term-args (args test value)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (and (consp args)
        (or (b2-search-any-term (car args) test value)
            (b2-search-any-term-args (cdr args) test value)))))

(defun b2-search-all-quoted-p (args)
  (if (endp args)
      t
    (and (proof-is-call (car args) *proof-quote*)
         (b2-search-all-quoted-p (cdr args)))))

(defund b2-search-rewrite-unfold-name (term search)
  (proof-with-checked-results ((head (b2-search-head term)))
    (if (member-equal head *b2-search-wrappers*)
        (list head)
      (proof-with-checked-results ((short (b2-search-search-short-definition search head)))
        (and short (<= (len term) 3) (b2-search-all-quoted-p (cdr term)) (list head))))))

(mutual-recursion
 (defun b2-search-rewrite-unfolds (term search)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (proof-with-checked-results
    ((names (b2-search-rewrite-unfold-name term search))
     (args (if (and (proof-compound term) (not (proof-is-call term *proof-quote*)))
               (b2-search-rewrite-unfold-arguments (cdr term) search)
             nil)))
    (append names args)))
 (defun b2-search-rewrite-unfold-arguments (args search)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((first (b2-search-rewrite-unfolds (car args) search))
       (rest (b2-search-rewrite-unfold-arguments (cdr args) search)))
      (append first rest)))))

(defun b2-search-rewrite-discharge (search equation evidence)
  (let ((lib (b2-search-search-lib search))
        (proof (b2-search-proof search)))
    (proof-with-checked-results
     ((literal (proof-step-first equation))
      (condition (proof-term-at literal 1))
      (head (b2-search-head condition))
      (short (b2-search-search-short-definition search head))
      (premise (b2-tactics-tactics-solve lib condition evidence
                                        (and short (list condition)) nil 0 nil)))
     (proof-proof-modus-ponens proof equation premise))))

(defun b2-search-rewrite-attempt (search goal evidence position equation conditional)
  (let ((lib (b2-search-search-lib search))
        (proof (b2-search-proof search)))
    (proof-with-checked-results
     ((equation (if conditional
                    (b2-search-rewrite-discharge search equation evidence)
                  equation))
      (reflexive (proof-proof-reflexive proof goal))
      (rewritten (proof-proof-rewrite proof reflexive equation (list 1 2 position)))
      (reduction (proof-proof-tidy proof rewritten))
      (normal (b2-search-step-right reduction))
      (unfolds (b2-search-rewrite-unfolds normal search))
      (answer (b2-tactics-tactics-solve lib normal evidence
                                        (proof-unique unfolds) nil 0 t)))
     (proof-proof-transport proof answer reduction))))

(defun b2-search-rewrite-row (search goal evidence known position side row)
  (let* ((proof (b2-search-proof search))
         (name (car row))
         (formula (cadr row))
         (pattern (caddr row))
         (conditional (proof-is-call formula *library-implies*))
         (fact (assoc-equal name (proof-proof-facts proof))))
    (cond ((not fact) '(:failure "tactic-rejected" ""))
          ((not (equal (len (cdr fact)) 1)) nil)
          (t
           (proof-with-checked-results
            ((bindings (b2-search-search-bindings search pattern side
                                                 (and conditional formula) known)))
            (if (eq bindings :none)
                nil
              (proof-with-checked-results
               ((target (if conditional (proof-term-at formula 2) formula))
                (right (proof-term-at target 2))
                (unbound (b2-search-any-term right :unbound bindings)))
               (if unbound
                   nil
                 (proof-with-checked-results
                  ((equation (proof-proof-fact proof name (table-items bindings))))
                  (let ((step (b2-search-rewrite-attempt search goal evidence position
                                                        equation conditional)))
                    (if (b2-tactics-unproved-p step) nil step)))))))))))

(defun b2-search-rewrite-rows (rows search goal evidence known position side)
  (if (endp rows)
      nil
    (or (b2-search-rewrite-row search goal evidence known position side (car rows))
        (b2-search-rewrite-rows (cdr rows) search goal evidence known position side))))

(defun b2-search-rewrite-side (search goal evidence known position)
  (proof-with-checked-results
   ((side (proof-term-at goal position))
    (operator (b2-search-head side)))
   (b2-search-rewrite-rows (table-get (b2-search-search-equations search) operator nil)
                           search goal evidence known position side)))

(defun b2-search-search-rewrite-test (search goal evidence known)
  (and (proof-is-call goal *proof-equal*)
       (or (b2-search-rewrite-side search goal evidence known 1)
           (b2-search-rewrite-side search goal evidence known 2))))

(defun b2-search-natural-constant (lib term rewritten)
  (proof-with-checked-results
   ((current (if rewritten (b2-search-step-right rewritten) term))
    (constant (b2-tactics-tactics-constant lib current)))
   (cond ((not constant) rewritten)
         (rewritten (proof-proof-chain (library-library-proof lib) rewritten (list constant)))
         (t constant))))

; Ground proof steps use the B2 constant evaluator.
(mutual-recursion
 (defun b2-search-natural-simplify (n lib term)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib))
         (operator (car term)))
     (cond ((zp n) '(:failure "fuel" "b2-search-natural-simplify"))
           ((or (not (proof-compound term)) (equal operator *proof-quote*)) nil)
           ((endp term) (proof-term-at term 0))
           ((or (proof-compound operator)
                (member-equal operator (list *library-natp* *proof-not*)))
            (proof-with-checked-results
             ((opened (proof-simplify-expansion proof term))
              (next (b2-search-natural-simplify (1- n) lib (cadr opened))))
             (proof-proof-chain proof (car opened) (list next))))
           ((equal operator *proof-if*)
            (proof-with-checked-results
             ((test (proof-term-at term 1))
              (first (b2-search-natural-simplify (1- n) lib test))
              (path (proof-simplify-if-path proof term first nil)))
             (if (eq (car path) :simplify)
                 (proof-with-checked-results
                  ((next (b2-search-natural-simplify (1- n) lib (caddr path))))
                  (proof-proof-chain proof (cadr path) (list next)))
               path)))
           (t
            (proof-with-checked-results
             ((rewritten (b2-search-natural-simplify-args (1- n) lib term (cdr term) 1 nil)))
             (b2-search-natural-constant lib term rewritten))))))

 (defun b2-search-natural-simplify-args (n lib term args index result)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b2-search-natural-simplify-args"))
         ((endp args) result)
         (t
          (proof-with-checked-results
           ((equality (b2-search-natural-simplify (1- n) lib (car args)))
            (result (proof-simplify-argument-result (library-library-proof lib) term
                                                     index result equality)))
           (b2-search-natural-simplify-args (1- n) lib term (cdr args) (1+ index) result))))))

(defund b2-search-natural-proof-step (lib term)
  (let ((proof (library-library-proof lib)))
    (if (equal term *proof-true*)
        (proof-proof-prove proof term nil nil)
      (proof-with-checked-results
       ((equation (b2-search-natural-simplify 1000000 lib term))
        (right (and equation (b2-search-step-right equation))))
       (cond ((or (not equation) (equal right term)) (proof-prove-unproved-term term))
             ((equal right *proof-true*) (proof-proof-true-from-eq proof equation))
             (t (list :transport right equation)))))))

(defun b2-search-natural-prove (n lib term)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "b2-search-natural-prove")
    (let ((result (b2-search-natural-proof-step lib term)))
      (if (eq (car result) :transport)
          (proof-with-checked-results ((step (b2-search-natural-prove (1- n) lib (cadr result))))
            (proof-proof-transport (library-library-proof lib) step (caddr result)))
        result))))

(mutual-recursion
 (defun b2-search-natural-type (lib term)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((or (proof-is-call term *library-count*) (proof-is-call term *library-len*))
          (library-library-natural lib term))
         ((proof-is-call term *proof-plus*)
          (proof-with-checked-results ((steps (b2-search-natural-type-args lib (cdr term))))
            (library-library-cite lib "NATURAL-SUM" (cdr term) steps)))
         (t (b2-search-natural-prove 1000000 lib (list *library-natp* term)))))
 (defun b2-search-natural-type-args (lib args)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (b2-search-natural-type lib (car args)))
       (rest (b2-search-natural-type-args lib (cdr args))))
      (cons step rest)))))

(defun b2-search-natural (lib term evidence)
  (let ((step (b2-search-natural-type lib term)))
    (if (b2-search-rejected-step-p step)
        (proof-with-checked-results
         ((typed (library-library-type-of lib term evidence))
          (bound (b2-bounds-prove-integer-bound lib (proof-neg (library-lt term *proof-zero*))
                                              evidence)))
         (library-library-cite lib "NATURAL-FROM-BOUNDS" (list term) (list typed bound)))
      step)))

(defun b2-search-sum-side-p (sides)
  (and (consp sides)
       (proof-with-checked-results ((head (b2-search-head (car sides))))
         (or (member-equal head (list *proof-plus* *proof-minus*))
             (b2-search-sum-side-p (cdr sides))))))

(defun b2-search-integer-sides (lib sides evidence)
  (if (endp sides)
      nil
    (proof-with-checked-results ((typed (library-library-type-of lib (car sides) evidence)))
      (b2-search-integer-sides lib (cdr sides) evidence))))

(defun b2-search-linear-sides (lib sides evidence)
  (proof-with-checked-results
   ((integer-check (b2-search-integer-sides lib sides evidence)))
   (if (equal (len sides) 2)
       (b2-tactics-tactics-linear-equal lib (car sides) (cadr sides) evidence)
     '(:failure "tactic-rejected" ""))))

(defun b2-search-arithmetic-step (lib goal evidence)
  (cond ((proof-is-call goal *proof-integerp*)
         (proof-with-checked-results ((term (proof-term-at goal 1)))
           (library-library-type-of lib term evidence)))
        ((proof-is-call goal *library-rationalp*)
         (proof-with-checked-results ((term (proof-term-at goal 1)))
           (library-library-rational lib term evidence)))
        ((proof-is-call goal *library-numberp*)
         (proof-with-checked-results
          ((term (proof-term-at goal 1))
           (head (b2-search-head term)))
          (if (member-equal head (list *proof-plus* *proof-times* *proof-minus* *b2-products-recip*))
              (b2-products-numeric-closure lib term)
            (library-library-number lib term evidence))))
        ((proof-is-call goal *library-natp*)
         (proof-with-checked-results ((term (proof-term-at goal 1)))
           (b2-search-natural lib term evidence)))
        ((proof-is-call goal *proof-equal*)
         (proof-with-checked-results ((sum (b2-search-sum-side-p (cdr goal))))
           (and sum (b2-search-linear-sides lib (cdr goal) evidence))))
        (t
         (proof-with-checked-results ((comparison (b2-bounds-comparison goal)))
           (and comparison
                (proof-with-checked-results ((size (b2-search-size goal 45)))
                  (and (< size 45) (b2-bounds-prove-integer-bound lib goal evidence))))))))

(defun b2-search-search-arithmetic (search goal known)
  (let ((step (b2-search-arithmetic-step (b2-search-search-lib search)
                                        goal (table-values known))))
    (if (b2-search-rejected-step-p step) nil step)))

(defun b2-search-normalize (search goal evidence unfold branches)
  (b2-tactics-tactics-normalize (b2-search-search-lib search) goal evidence unfold
                                (b2-search-search-rules search) 220 branches))

(defun b2-search-substitute-one (search goal evidence subterms old new equation reversed)
  (and (member-equal old subterms)
       (proof-with-checked-results ((occurs (b2-search-any-term new :contains old)))
         (and (not occurs)
              (not (proof-is-call old *proof-quote*))
              (proof-with-checked-results
               ((rule (if reversed
                          (proof-proof-symmetric (b2-search-proof search) equation)
                        equation)))
               (let ((answer (b2-tactics-tactics-solve (b2-search-search-lib search)
                                                       goal evidence nil (list rule) 0 nil)))
                 (if (b2-tactics-unproved-p answer) nil answer)))))))

(defun b2-search-substitute-row (search goal evidence subterms current equation)
  (and (proof-is-call current *proof-equal*)
       (proof-with-checked-results
        ((old (proof-term-at current 1))
         (new (proof-term-at current 2)))
        (and (not (equal old new))
             (proof-with-checked-results ((operands (proof-list-of-length (cdr current) 2)))
               (or (b2-search-substitute-one search goal evidence subterms old new equation nil)
                   (b2-search-substitute-one search goal evidence subterms new old equation t)))))))

(defun b2-search-substitute-rows (known search goal evidence subterms)
  (and (consp known)
       (or (b2-search-substitute-row search goal evidence subterms (caar known) (cdar known))
           (b2-search-substitute-rows (cdr known) search goal evidence subterms))))

(defun b2-search-search-substitute-equal (search goal evidence known)
  (proof-with-checked-results ((subterms (b2-search-terms goal)))
    (b2-search-substitute-rows known search goal evidence subterms)))

(defun b2-search-find-facts (search goal)
  (proof-with-checked-results ((head (b2-search-head goal)))
    (table-get (b2-search-search-index search) head nil)))

(defun b2-search-fact-patterns (template)
  (if (proof-is-call template *proof-equal*)
      (proof-with-checked-results
       ((right (proof-term-at template 2))
        (left (proof-term-at template 1)))
       (list (list template nil) (list (proof-eq right left) t)))
    (list (list template nil))))

(defun b2-search-beta-fact (proof step place)
  (if (not place)
      step
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (application (if (equal (len place) 1) literal (proof-term-at literal 2)))
      (beta (proof-proof-beta proof application))
      (rewritten (proof-proof-rewrite proof step beta place)))
     (proof-proof-tidy proof rewritten))))

(defun b2-search-match-fact (search name pattern goal guard known)
  (proof-with-checked-results
   ((bindings (b2-search-search-bindings search pattern goal guard known)))
   (if (eq bindings :none)
       nil
     (let ((proof (b2-search-proof search)))
       (proof-with-checked-results
        ((step (proof-proof-fact proof name (table-items bindings))))
        (b2-search-beta-fact proof step
                             (table-get (b2-search-search-beta-paths search) name nil)))))))

(defun b2-search-discharge-sides (proof step sides known)
  (if (endp sides)
      step
    (let ((side (car sides)))
      (if (not (member-equal side (cdr (proof-step-clause step))))
          (b2-search-discharge-sides proof step (cdr sides) known)
        (proof-with-checked-results
         ((literal (if (proof-is-call side *proof-not*)
                       (proof-term-at side 1)
                     (proof-neg side))))
         (let ((evidence (table-get known literal nil)))
           (if (not evidence)
               (b2-tactics-unproved)
             (proof-with-checked-results ((step (proof-proof-discharge proof step evidence)))
               (b2-search-discharge-sides proof step (cdr sides) known)))))))))

(defun b2-search-finish-fact (search step reversep)
  (let ((step (if (and reversep (not (failure-p step)))
                  (proof-proof-symmetric (b2-search-proof search) step)
                step)))
    (cons (if (b2-search-rejected-step-p step) nil step) search)))

(defun b2-search-active-path-p (path goal keys)
  (and (consp path)
       (or (and (equal goal (caar path))
                (subsetp-equal keys (cadar path))
                (subsetp-equal (cadar path) keys))
           (b2-search-active-path-p (cdr path) goal keys))))

(defun b2-search-normalized-choice (search equation known collected)
  (cond ((failure-p equation) equation)
        ((not equation) collected)
        (t
         (proof-with-checked-results ((normal (b2-search-step-right equation)))
           (cond ((member-equal normal (cadr collected)) collected)
                 ((assoc-equal normal known)
                  (proof-proof-transport (b2-search-proof search)
                                          (table-get known normal nil) equation))
                 ((proof-is-call normal *proof-quote*)
                  (if (equal normal *proof-false*)
                      collected
                    (proof-with-checked-results
                     ((step (b2-tactics-tactics-prove-ground (b2-search-search-lib search)
                                                              normal)))
                     (proof-proof-transport (b2-search-proof search) step equation))))
                 (t (list :choices (cons normal (cadr collected))
                          (cons (list normal equation) (caddr collected)))))))))

(defun b2-search-collect-options (options search goal evidence known collected)
  (if (or (endp options) (not (eq (car collected) :choices)))
      collected
    (let* ((equation (b2-search-normalize search goal evidence (caar options) (cadar options)))
           (collected (if (b2-tactics-unproved-p equation)
                          collected
                        (b2-search-normalized-choice search equation known collected))))
      (b2-search-collect-options (cdr options) search goal evidence known collected))))

(defun b2-search-collect-definitions (search goal evidence known collected)
  (proof-with-checked-results ((definitions (b2-search-options-definitions search goal)))
    (let* ((roots (car definitions))
           (collected (if roots
                          (b2-search-collect-options (list (list roots nil))
                                                      search goal evidence known collected)
                        collected)))
      (if (eq (car collected) :choices)
          (proof-with-checked-results
           ((options (b2-search-name-options goal (cadr definitions))))
           (b2-search-collect-options options search goal evidence known collected))
        collected))))

(defun b2-search-collect-choices (search goal evidence known)
  (let* ((base (b2-search-normalize search goal evidence nil nil))
         (collected (list :choices (list goal) nil)))
    (if (b2-tactics-unproved-p base)
        collected
      (let ((collected (b2-search-normalized-choice search base known collected)))
        (if (eq (car collected) :choices)
            (b2-search-collect-definitions search goal evidence known collected)
          collected)))))

(defun b2-search-size-keys (choices index)
  (if (endp choices)
      nil
    (proof-with-checked-results
     ((size (b2-search-size (caar choices) 300))
      (rest (b2-search-size-keys (cdr choices) (1+ index))))
     (cons (cons size (cons index (car choices))) rest))))

(defun b2-search-first-splits (count ordered)
  (if (or (zp count) (endp ordered))
      nil
    (cons (cddar ordered) (b2-search-first-splits (1- count) (cdr ordered)))))

(defun b2-search-ordered-splits (goal choices)
  (proof-with-checked-results ((keyed (b2-search-size-keys choices 0)))
    (append (b2-search-first-splits 3 (seq-sorted keyed)) (list (list goal nil)))))

(defun b2-search-transport-choice (search step equation)
  (if (or (failure-p step) (not equation))
      step
    (proof-proof-transport (b2-search-proof search) step equation)))

(defmacro b2-search-with-checked-results (search bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (name (car binding)))
      `(let (,binding)
         (if (failure-p ,name)
             (cons ,name ,search)
           (b2-search-with-checked-results ,search ,(cdr bindings) ,result))))))

(mutual-recursion
 (defun b2-search-prove-goal (n search goal evidence depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-prove-goal") search)
     (let* ((fuel (1- (b2-search-search-fuel search)))
            (search (b2-search-search-with-fuel search fuel))
            (lib (b2-search-search-lib search)))
       (if (< fuel 0)
           (cons (b2-tactics-unproved) search)
         (b2-search-with-checked-results search
          ((known (b2-tactics-tactics-evidence lib evidence)))
          (if (assoc-equal goal known)
              (cons (table-get known goal nil) search)
            (b2-search-with-checked-results search
             ((impossible (b2-tactics-tactics-contradiction lib goal known)))
             (cond (impossible (cons impossible search))
                   ((and (proof-is-call goal *proof-quote*) (not (equal goal *proof-false*)))
                    (cons (b2-tactics-tactics-prove-ground lib goal) search))
                   (t
                    (let ((path (b2-search-search-path search))
                          (keys (table-keys known)))
                      (if (b2-search-active-path-p path goal keys)
                          (cons (b2-tactics-unproved) search)
                        (let ((result
                               (b2-search-infer-goal
                                (1- n) (b2-search-search-with-path
                                        search (cons (list goal keys) path))
                                goal evidence known depth splits)))
                          (cons (car result) (b2-search-search-with-path (cdr result) path))))))))))))))

 (defun b2-search-infer-goal (n search goal evidence known depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-infer-goal") search)
     (let* ((attempt (b2-search-structured-goal (1- n) search goal evidence depth splits))
            (step (car attempt))
            (search (cdr attempt)))
       (if (and step (not (b2-tactics-unproved-p step)))
           attempt
         (b2-search-infer-rest (1- n) search goal evidence known depth splits)))))

 (defun b2-search-structured-goal (n search goal evidence depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-structured-goal") search)
     (let ((proof (b2-search-proof search))
           (lib (b2-search-search-lib search)))
       (cond
        ((and (proof-is-call goal *library-implies*) (> depth 0))
         (b2-search-with-checked-results search
          ((formula (proof-list-of-length goal 3))
           (premise (proof-proof-assume proof (cadr formula) t))
           (extended (b2-search-search-extend search premise)))
          (let* ((condition (cadr formula))
                 (target (caddr formula))
                 (answer (b2-search-prove-goal
                          (1- n) search target (append evidence extended) (1- depth) splits))
                 (step (car answer))
                 (search (cdr answer)))
            (if (failure-p step)
                answer
              (let ((result (b2-tactics-tactics-implication lib condition target (cons step lib))))
                (cons (if (failure-p result) result (car result)) search))))))
        ((proof-is-call goal *proof-if*)
         (b2-search-with-checked-results search ((other (proof-term-at goal 3)))
           (if (and (equal other *proof-false*) (> depth 0))
               (let* ((test (b2-search-prove-goal (1- n) search (cadr goal) evidence
                                                   (1- depth) splits))
                      (search (cdr test)))
                 (if (failure-p (car test))
                     test
                   (let* ((value (b2-search-prove-goal (1- n) search (caddr goal) evidence
                                                        (1- depth) splits))
                          (search (cdr value)))
                     (b2-search-with-checked-results search
                      ((step (car value))
                       (selection (proof-proof-select proof goal (car test))))
                      (cons (proof-proof-transport proof step selection) search)))))
             (cons nil search))))
        (t (cons nil search))))))

 (defun b2-search-fact-with-fuel (n search goal known depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-fact-with-fuel") search)
     (b2-search-with-checked-results search ((rows (b2-search-find-facts search goal)))
       (b2-search-fact-rows (1- n) rows search goal known depth splits nil))))

 (defun b2-search-fact-rows (n rows search goal known depth splits tried)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (cons '(:failure "fuel" "b2-search-fact-rows") search))
         ((endp rows) (cons nil search))
         (t
          (let ((name (caar rows))
                (formula (cadar rows)))
            (if (member-equal name tried)
                (b2-search-fact-rows (1- n) (cdr rows) search goal known depth splits tried)
              (let ((conditional (and (proof-is-call formula *library-implies*)
                                      (not (proof-is-call goal *library-implies*)))))
                (b2-search-with-checked-results search
                 ((template (if conditional (proof-term-at formula 2) formula))
                  (variants (b2-search-fact-patterns template)))
                 (let ((attempt
                        (b2-search-fact-variants (1- n) variants search name goal known
                                                  (and conditional formula) depth splits)))
                   (if (car attempt)
                       attempt
                     (b2-search-fact-rows (1- n) (cdr rows) (cdr attempt) goal known
                                           depth splits (cons name tried)))))))))))

 (defun b2-search-fact-variants (n variants search name goal known guard depth splits)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) (cons '(:failure "fuel" "b2-search-fact-variants") search))
         ((endp variants) (cons nil search))
         (t
          (b2-search-with-checked-results search
           ((step (b2-search-match-fact search name (caar variants) goal guard known)))
           (let ((attempt
                  (if step
                      (b2-search-try-fact (1- n) search step known guard (cadar variants) depth splits)
                    (cons nil search))))
             (if (car attempt)
                 attempt
               (b2-search-fact-variants (1- n) (cdr variants) (cdr attempt) name goal known
                                         guard depth splits)))))))

 (defun b2-search-try-fact (n search step known guard reversep depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-try-fact") search)
     (let* ((proof (b2-search-proof search))
            (step (b2-search-discharge-sides proof step (cdr (proof-step-clause step)) known)))
       (cond ((or (failure-p step) (not guard))
              (b2-search-finish-fact search step reversep))
             ((<= depth 0) (cons nil search))
             (t
              (b2-search-with-checked-results search
               ((first (proof-step-first step))
                (condition (proof-term-at first 1)))
               (let* ((premise (b2-search-prove-goal
                                (1- n) search condition (table-values known)
                                (1- depth) (min splits 1)))
                      (search (cdr premise))
                      (step (if (failure-p (car premise))
                                (car premise)
                              (proof-proof-modus-ponens proof step (car premise)))))
                 (b2-search-finish-fact search step reversep))))))))

 (defun b2-search-infer-rest (n search goal evidence known depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-infer-rest") search)
     (let* ((exact (b2-search-fact-with-fuel (1- n) search goal known 0 splits))
            (search (cdr exact)))
       (if (car exact)
           exact
         (let ((step (or (b2-search-search-substitute-equal search goal evidence known)
                         (b2-search-search-rewrite-test search goal evidence known)
                         (b2-search-search-arithmetic search goal known))))
           (if step
               (cons step search)
             (let ((collected (b2-search-collect-choices search goal evidence known)))
               (if (eq (car collected) :choices)
                   (b2-search-infer-normalized (1- n) search goal evidence known depth splits
                                               (reverse (caddr collected)))
                 (cons collected search)))))))))

 (defun b2-search-infer-normalized (n search goal evidence known depth splits choices)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-infer-normalized") search)
     (let* ((direct (b2-search-fact-with-fuel (1- n) search goal known depth splits))
            (search (cdr direct)))
       (if (car direct)
           direct
         (let* ((answer (b2-search-use-choices (1- n) choices search evidence known depth splits))
                (search (cdr answer)))
           (cond
            ((car answer) answer)
            ((and (not (equal splits 0)) (>= (b2-search-search-fuel search) 2))
             (b2-search-with-checked-results search
              ((ordered (b2-search-ordered-splits goal choices)))
              (b2-search-split-choices (1- n) ordered search evidence known depth splits)))
            (t (cons (b2-tactics-unproved) search))))))))

 (defun b2-search-use-choices (n choices search evidence known depth splits)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "b2-search-use-choices") search))
    ((endp choices) (cons nil search))
    (t
     (let* ((current (caar choices))
            (equation (cadar choices))
            (arithmetic (b2-search-search-arithmetic search current known))
            (answer (if arithmetic
                        (cons arithmetic search)
                      (b2-search-fact-with-fuel (1- n) search current known (min depth 1) splits)))
            (search (cdr answer))
            (step (or (car answer) (b2-search-search-rewrite-test search current evidence known))))
       (if step
           (cons (b2-search-transport-choice search step equation) search)
         (b2-search-use-choices (1- n) (cdr choices) search evidence known depth splits))))))

 (defun b2-search-split-choices (n choices search evidence known depth splits)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "b2-search-split-choices") search))
    ((endp choices)
     (cons (b2-tactics-unproved) search))
    (t
     (let ((current (caar choices))
           (equation (cadar choices)))
       (b2-search-with-checked-results search ((test (b2-search-boolean-test current)))
         (let ((answer (if (or (eq test :none) (assoc-equal test known)
                               (assoc-equal (proof-neg test) known))
                           (cons nil search)
                         (b2-search-try-split
                          (1- n) search current equation test evidence depth splits))))
           (if (and (car answer) (not (b2-tactics-unproved-p (car answer))))
               answer
             (b2-search-split-choices (1- n) (cdr choices) (cdr answer) evidence known
                                       depth splits))))))))

 (defun b2-search-try-split (n search current equation test evidence depth splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "b2-search-try-split") search)
     (let ((proof (b2-search-proof search)))
       (b2-search-with-checked-results search ((positive (proof-proof-assume proof test t)))
         (let* ((yes (b2-search-prove-goal (1- n) search current (append evidence (list positive))
                                           depth (1- splits)))
                (search (cdr yes)))
           (b2-search-with-checked-results search
            ((yes-step (car yes))
             (negative (proof-proof-assume proof test nil)))
            (let* ((no (b2-search-prove-goal (1- n) search current
                                              (append evidence (list negative)) depth (1- splits)))
                   (search (cdr no)))
              (b2-search-with-checked-results search
               ((no-step (car no))
                (result (proof-proof-cases proof test yes-step no-step)))
               (cons (b2-search-transport-choice search result equation) search))))))))))

(defun b2-search-search-fact (search goal known depth splits)
  (b2-search-fact-with-fuel 1000000 search goal known depth splits))

(defun b2-search-search-prove (search goal evidence depth splits)
  (b2-search-prove-goal 1000000 search goal evidence depth splits))

(defun b2-search-search-theorem (lib formula)
  (proof-with-checked-results ((size (b2-search-size formula 600)))
    (if (>= size 600)
        (b2-tactics-unproved)
      (proof-with-checked-results ((search (b2-search-search-init lib 32 nil)))
        (car (b2-search-search-prove search formula nil 3 3))))))
