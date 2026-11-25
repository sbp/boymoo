(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-booklogic-zp* (proof-sym "ZP" "ACL2"))

(defconst *t4-booklogic-countdown*
  (list (proof-cl "NTHCDR") (proof-cl "UPDATE-NTH")
        (proof-sym "TAKE" "ACL2") (proof-cl "NTH")
        (proof-sym "MV-NTH" "ACL2")))

(defconst *t4-booklogic-term-shape-failure*
  '(:failure "failure" ""))

(mutual-recursion
 (defund t4-booklogic-term-size (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) 1)
         ((endp term) *t4-booklogic-term-shape-failure*)
         ((proof-is-call term *proof-quote*) 1)
         (t (proof-with-checked-results
                ((first (t4-booklogic-term-size (car term)))
                 (rest (t4-booklogic-term-sizes (cdr term))))
              (+ 1 first rest)))))
 (defund t4-booklogic-term-sizes (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       0
     (proof-with-checked-results
         ((first (t4-booklogic-term-size (car terms)))
          (rest (t4-booklogic-term-sizes (cdr terms))))
       (+ first rest)))))

(mutual-recursion
 (defund t4-booklogic-match (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond ((not (proof-compound pattern))
          (let ((old (assoc-equal pattern bindings)))
            (if old
                (cons (equal (cdr old) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((endp pattern) *t4-booklogic-term-shape-failure*)
         ((proof-is-call pattern *proof-quote*) (cons (equal pattern term) bindings))
         ((or (not (proof-compound term))
              (not (equal (len pattern) (len term)))
              (not (equal (car pattern) (car term))))
          (cons nil bindings))
         (t (t4-booklogic-match-arguments (cdr pattern) (cdr term) bindings))))
 (defund t4-booklogic-match-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
         ((matched (t4-booklogic-match (car patterns) (car terms) bindings)))
       (if (car matched)
           (t4-booklogic-match-arguments (cdr patterns) (cdr terms) (cdr matched))
         matched)))))

(mutual-recursion
 (defund t4-booklogic-free-variables (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (list term))
         ((endp term) *t4-booklogic-term-shape-failure*)
         ((proof-is-call term *proof-quote*) nil)
         (t (proof-with-checked-results
                ((vars (t4-booklogic-free-variables-arguments (cdr term))))
              (proof-unique vars)))))
 (defund t4-booklogic-free-variables-arguments (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (t4-booklogic-free-variables (car args)))
          (rest (t4-booklogic-free-variables-arguments (cdr args))))
       (append first rest)))))

(mutual-recursion
 (defund t4-booklogic-calls-function (term name)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) nil)
         ((endp term) *t4-booklogic-term-shape-failure*)
         ((proof-is-call term *proof-quote*) nil)
         ((equal (car term) name) t)
         (t (t4-booklogic-calls-function-arguments (cdr term) name))))
 (defund t4-booklogic-calls-function-arguments (args name)
   (declare (xargs :measure (acl2-count args)))
   (and (consp args)
        (or (t4-booklogic-calls-function (car args) name)
            (t4-booklogic-calls-function-arguments (cdr args) name)))))

(defund t4-booklogic-constructor-result-search (n term)
  (declare (xargs :measure (nfix n)))
  (cond ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-booklogic-constructor-result-search"))
        ((proof-is-call term *termination-return-last*)
         (t4-booklogic-constructor-result-search (1- n) (car (last term))))
        ((not (proof-compound term)) nil)
        ((endp term) *t4-booklogic-term-shape-failure*)
        ((proof-compound (car term))
         (proof-with-checked-results ((body (proof-term-at (car term) 2)))
           (t4-booklogic-constructor-result-search (1- n) body)))
        (t (proof-is-call term *proof-cons*))))

(defund t4-booklogic-constructor-result (term)
  (t4-booklogic-constructor-result-search 1000000 term))

(mutual-recursion
 (defund t4-booklogic-has-constructor-result (term)
   (declare (xargs :measure (acl2-count term)))
   (if (proof-is-call term *proof-if*)
       (and (consp (cdr term))
            (t4-booklogic-has-constructor-result-arms (cddr term)))
     (t4-booklogic-constructor-result term)))
 (defund t4-booklogic-has-constructor-result-arms (arms)
   (declare (xargs :measure (acl2-count arms)))
   (and (consp arms)
        (or (t4-booklogic-has-constructor-result (car arms))
            (t4-booklogic-has-constructor-result-arms (cdr arms))))))

(defund t4-booklogic-rule-key (term)
  (proof-with-checked-results
      ((head (proof-term-at term 0))
       (discriminator (cond ((endp (cdr term)) :none)
                            ((proof-compound (cadr term))
                             (proof-term-at (cadr term) 0))
                            (t :none))))
    (list head discriminator)))

(defund t4-booklogic-candidates (rules term)
  (proof-with-checked-results ((key (t4-booklogic-rule-key term)))
    (let ((exact (table-get rules key nil)))
      (if (eq (cadr key) :none)
          exact
        (append exact (table-get rules (list (car key) :none) nil))))))

(defund t4-booklogic-conjuncts (formula path)
  (declare (xargs :measure (acl2-count formula)))
  (if (proof-is-call formula *proof-if*)
      (proof-with-checked-results ((otherwise-branch (proof-term-at formula 3)))
        (if (and (consp (cdr formula)) (consp (cddr formula))
                 (equal otherwise-branch *proof-false*))
            (proof-with-checked-results
                ((left (t4-booklogic-conjuncts (cadr formula) (append path '(0))))
                 (right (t4-booklogic-conjuncts (caddr formula) (append path '(1)))))
              (append left right))
          (list (list formula path))))
    (list (list formula path))))

(defun t4-booklogic-booklogic-library (book)
  (nth 1 book))

(defun t4-booklogic-booklogic-with-library (book value)
  (update-nth 1 value book))

(defun t4-booklogic-booklogic-rules (book)
  (nth 2 book))

(defun t4-booklogic-booklogic-with-rules (book value)
  (update-nth 2 value book))

(defun t4-booklogic-booklogic-projected-rules (book)
  (nth 3 book))

(defun t4-booklogic-booklogic-with-projected-rules (book value)
  (update-nth 3 value book))

(defun t4-booklogic-booklogic-equalities (book)
  (nth 4 book))

(defun t4-booklogic-booklogic-with-equalities (book value)
  (update-nth 4 value book))

(defun t4-booklogic-booklogic-rule-heads (book)
  (nth 5 book))

(defun t4-booklogic-booklogic-with-rule-heads (book value)
  (update-nth 5 value book))

(defun t4-booklogic-booklogic-equality-heads (book)
  (nth 6 book))

(defun t4-booklogic-booklogic-with-equality-heads (book value)
  (update-nth 6 value book))

(defun t4-booklogic-booklogic-premises (book)
  (nth 7 book))

(defun t4-booklogic-booklogic-with-premises (book value)
  (update-nth 7 value book))

(defun t4-booklogic-booklogic-enabled (book)
  (nth 8 book))

(defun t4-booklogic-booklogic-with-enabled (book value)
  (update-nth 8 value book))

(defun t4-booklogic-booklogic-enhanced (book)
  (nth 9 book))

(defun t4-booklogic-booklogic-with-enhanced (book value)
  (update-nth 9 value book))

(defun t4-booklogic-booklogic-chaining (book)
  (nth 10 book))

(defun t4-booklogic-booklogic-with-chaining (book value)
  (update-nth 10 value book))

(defun t4-booklogic-booklogic-project-returns (book)
  (nth 11 book))

(defun t4-booklogic-booklogic-with-project-returns (book value)
  (update-nth 11 value book))

(defun t4-booklogic-booklogic-evaluate-syntax (book)
  (nth 12 book))

(defun t4-booklogic-booklogic-with-evaluate-syntax (book value)
  (update-nth 12 value book))

(defun t4-booklogic-booklogic-evaluators (book)
  (nth 13 book))

(defun t4-booklogic-booklogic-with-evaluators (book value)
  (update-nth 13 value book))

(defun t4-booklogic-booklogic-packages (book)
  (nth 14 book))

(defun t4-booklogic-booklogic-with-packages (book value)
  (update-nth 14 value book))

(defun t4-booklogic-booklogic-mutual (book)
  (nth 15 book))

(defun t4-booklogic-booklogic-with-mutual (book value)
  (update-nth 15 value book))

(defun t4-booklogic-booklogic-recursive (book)
  (nth 16 book))

(defun t4-booklogic-booklogic-with-recursive (book value)
  (update-nth 16 value book))

(defun t4-booklogic-booklogic-total-remaining (book)
  (nth 17 book))

(defun t4-booklogic-booklogic-with-total-remaining (book value)
  (update-nth 17 value book))

(defun t4-booklogic-booklogic-arithmetic (book)
  (nth 18 book))

(defun t4-booklogic-booklogic-with-arithmetic (book value)
  (update-nth 18 value book))

(defun t4-booklogic-booklogic-remaining (book)
  (nth 19 book))

(defun t4-booklogic-booklogic-with-remaining (book value)
  (update-nth 19 value book))

(defun t4-booklogic-booklogic-proof (book)
  (library-library-proof (t4-booklogic-booklogic-library book)))

(defun t4-booklogic-booklogic-entries (book)
  (library-library-entries (t4-booklogic-booklogic-library book)))

(defun t4-booklogic-booklogic-with-proof (book proof)
  (t4-booklogic-booklogic-with-library
   book (library-library-with-proof (t4-booklogic-booklogic-library book) proof)))

(defund t4-booklogic-definitions (book)
  (proof-proof-definitions (t4-booklogic-booklogic-proof book)))

(defund t4-booklogic-lookup-tree-from-sorted (n entries count)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t4-booklogic-lookup-tree-from-sorted"))
   ((zp count) (cons nil entries))
   (t
    (let ((left-count (floor count 2)))
      (proof-with-checked-results
          ((left (t4-booklogic-lookup-tree-from-sorted (1- n) entries left-count))
           (right (t4-booklogic-lookup-tree-from-sorted
                   (1- n) (cddr left) (- (1- count) left-count))))
        (cons (list (cadr left) (car left) (car right)) (cdr right)))))))

(defun t4-booklogic-lookup-tree (entries)
  (proof-with-checked-results
      ((result (t4-booklogic-lookup-tree-from-sorted
                1000000 (acl2::merge-sort-lexorder entries) (len entries))))
    (car result)))

(defun t4-booklogic-lookup-entry (key tree)
  (if (endp tree)
      nil
    (let ((entry (car tree)))
      (cond ((equal key (car entry)) entry)
            ((acl2::lexorder key (car entry))
             (t4-booklogic-lookup-entry key (cadr tree)))
            (t (t4-booklogic-lookup-entry key (caddr tree)))))))

(defund t4-booklogic-set-lookup-entry (entry tree)
  (if (endp tree)
      (list entry nil nil)
    (let ((root (car tree))
          (left (cadr tree))
          (right (caddr tree)))
      (cond ((equal (car entry) (car root)) (list entry left right))
            ((acl2::lexorder (car entry) (car root))
             (list root (t4-booklogic-set-lookup-entry entry left) right))
            (t (list root left (t4-booklogic-set-lookup-entry entry right)))))))

(defund t4-booklogic-definition-index (book)
  (nth 20 book))

(defund t4-booklogic-with-definition-index (book index)
  (update-nth 20 index book))

(defund t4-booklogic-sized-definition (definition)
  (let* ((body (caddr definition))
         (size (t4-booklogic-term-size body)))
    (and (not (failure-p size))
         (cons (car definition) (cons body size)))))

(defund t4-booklogic-definition-size-entries (definitions)
  (if (endp definitions)
      nil
    (let ((entry (t4-booklogic-sized-definition (car definitions)))
          (rest (t4-booklogic-definition-size-entries (cdr definitions))))
      (if entry (cons entry rest) rest))))

(defun t4-booklogic-booklogic-cache-definition-sizes (book)
  (proof-with-checked-results
      ((index (t4-booklogic-lookup-tree
               (t4-booklogic-definition-size-entries (t4-booklogic-definitions book)))))
    (t4-booklogic-with-definition-index book index)))

(defun t4-booklogic-booklogic-extend-definition-sizes (book definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      book
    (let* ((entry (t4-booklogic-sized-definition (car definitions)))
           (book (if entry
                     (t4-booklogic-with-definition-index
                      book (t4-booklogic-set-lookup-entry entry (t4-booklogic-definition-index book)))
                   book)))
      (t4-booklogic-booklogic-extend-definition-sizes book (cdr definitions)))))

(defund t4-booklogic-definition-size (book definition)
  (let* ((body (caddr definition))
         (cached (t4-booklogic-lookup-entry (car definition) (t4-booklogic-definition-index book))))
    ; Auxiliary definitions can replace a name during a proof attempt.
    (if (and cached (equal body (cadr cached)))
        (cddr cached)
      (t4-booklogic-term-size body))))

(defund t4-booklogic-adjoin (value values)
  (if (member-equal value values) values (append values (list value))))

(defund t4-booklogic-index-append (index key rule)
  (table-put index key (append (table-get index key nil) (list rule))))

(defund t4-booklogic-strip-implications (term)
  (declare (xargs :measure (acl2-count term)))
  (cond ((not (proof-is-call term *library-implies*)) term)
        ((and (consp (cdr term)) (consp (cddr term)))
         (t4-booklogic-strip-implications (caddr term)))
        (t *t4-booklogic-term-shape-failure*)))

(defund t4-booklogic-index-projection (index name path term)
  (proof-with-checked-results ((key (t4-booklogic-rule-key term)))
    (t4-booklogic-index-append index key (list name path term))))

(defund t4-booklogic-index-projections (parts name index)
  (if (endp parts)
      index
    (let* ((part (caar parts))
           (path (cadar parts)))
      (if (and path (proof-compound part))
          (proof-with-checked-results ((head (proof-term-at part 0)))
            (if (equal head *proof-quote*)
                (t4-booklogic-index-projections (cdr parts) name index)
              (proof-with-checked-results
                  ((next (t4-booklogic-index-projection index name path part))
                   (tail (t4-booklogic-strip-implications part))
                   (next (if (and (not (equal tail part)) (proof-compound tail))
                             (proof-with-checked-results ((head (proof-term-at tail 0)))
                               (if (member-equal head (list *proof-if* *proof-quote*))
                                   next
                                 (t4-booklogic-index-projection next name path tail)))
                           next)))
                (t4-booklogic-index-projections (cdr parts) name next))))
        (t4-booklogic-index-projections (cdr parts) name index)))))

(defund t4-booklogic-index-premise (book name conclusion)
  (if (not (proof-is-call conclusion *library-implies*))
      book
    (proof-with-checked-results
        ((args (proof-list-of-length (cdr conclusion) 2)))
      (let ((premise (car args))
            (result (cadr args)))
        (if (not (proof-compound premise))
            book
          (proof-with-checked-results ((head (proof-term-at premise 0)))
            (if (or (equal head *proof-if*) (not (proof-compound result))
                    (proof-is-call result *library-implies*))
                book
              (proof-with-checked-results
                  ((result-vars (t4-booklogic-free-variables result))
                   (premise-vars (t4-booklogic-free-variables premise)))
                (if (not (subsetp-equal result-vars premise-vars))
                    book
                  (proof-with-checked-results ((size (t4-booklogic-term-size result)))
                    (if (> size 25)
                        book
                      (t4-booklogic-booklogic-with-premises
                       book
                       (t4-booklogic-index-append
                        (t4-booklogic-booklogic-premises book)
                        head (list name premise))))))))))))))

(defund t4-booklogic-index-rule (book name term)
  (proof-with-checked-results ((key (t4-booklogic-rule-key term)))
    (t4-booklogic-booklogic-with-rules
     book (t4-booklogic-index-append (t4-booklogic-booklogic-rules book)
                                    key (list name term)))))

(defund t4-booklogic-index-conclusion (book name term)
  (if (not (proof-compound term))
      book
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (if (member-equal head (list *proof-if* *proof-quote*))
          book
        (proof-with-checked-results ((indexed (t4-booklogic-index-rule book name term)))
          (t4-booklogic-booklogic-with-rule-heads
           indexed (t4-booklogic-adjoin head (t4-booklogic-booklogic-rule-heads indexed))))))))

(defund t4-booklogic-index-equality (book name term)
  (if (not (proof-is-call term *proof-equal*))
      book
    (proof-with-checked-results ((left (proof-term-at term 1)))
      (if (not (proof-compound left))
          book
        (proof-with-checked-results
            ((sides (proof-list-of-length (cdr term) 2))
             (head (proof-term-at left 0)))
          (if (equal head *proof-quote*)
              book
            (let ((right (cadr sides)))
              (proof-with-checked-results
                  ((right-vars (t4-booklogic-free-variables right))
                   (left-vars (t4-booklogic-free-variables left)))
                (if (not (subsetp-equal right-vars left-vars))
                    book
                  (proof-with-checked-results
                      ((left-size (t4-booklogic-term-size left))
                       (right-size (t4-booklogic-term-size right))
                       (expands (and (<= left-size right-size)
                                     (t4-booklogic-calls-function right head))))
                    (if expands
                        book
                      (proof-with-checked-results ((key (t4-booklogic-rule-key left)))
                        (let ((book (t4-booklogic-booklogic-with-equalities
                                     book (t4-booklogic-index-append
                                           (t4-booklogic-booklogic-equalities book)
                                           key (list name left)))))
                          (t4-booklogic-booklogic-with-equality-heads
                           book (t4-booklogic-adjoin
                                 head (t4-booklogic-booklogic-equality-heads book))))))))))))))))

(defun t4-booklogic-booklogic-index-fact (book name clause)
  (if (or (not (equal (len clause) 1))
          (assoc-equal name (t4-booklogic-definitions book)))
      book
    (let ((conclusion (car clause)))
      (proof-with-checked-results
          ((book (if (proof-is-call conclusion *library-implies*)
                     (t4-booklogic-index-rule book name conclusion)
                   book))
           (parts (t4-booklogic-conjuncts conclusion nil))
           (projected (t4-booklogic-index-projections
                       parts name (t4-booklogic-booklogic-projected-rules book)))
           (book (t4-booklogic-index-premise
                  (t4-booklogic-booklogic-with-projected-rules book projected)
                  name conclusion))
           (tail (t4-booklogic-strip-implications conclusion))
           (book (t4-booklogic-index-conclusion book name tail)))
        (t4-booklogic-index-equality book name tail)))))

(defund t4-booklogic-index-facts (facts book)
  (if (endp facts)
      book
    (proof-with-checked-results
        ((book (t4-booklogic-booklogic-index-fact book (caar facts) (cdar facts))))
      (t4-booklogic-index-facts (cdr facts) book))))

(defun t4-booklogic-booklogic-init-with-proof (proof)
  (let* ((library (library-library-init proof))
         (evaluators (t4-evaluation-evaluation-rules-init))
         (book (list :t4-booklogic library
                     nil nil nil nil nil nil
                     nil nil nil nil nil
                     evaluators '("ACL2" "COMMON-LISP" "KEYWORD") nil nil :none nil :none)))
    (t4-booklogic-index-facts (proof-proof-facts proof) book)))

(defun t4-booklogic-booklogic-init (prefix)
  (let* ((ground (proof-proof-init))
         (facts (table-update (proof-proof-facts ground) (proof-proof-facts prefix)))
         (definitions (table-update (proof-proof-definitions ground)
                                     (proof-proof-definitions prefix))))
    (t4-booklogic-booklogic-init-with-proof
     (proof-make-proof facts definitions (proof-proof-primitives ground)))))

(defun t4-booklogic-booklogic-use-arithmetic (book)
  (if (t4-booklogic-booklogic-arithmetic book)
      book
    (proof-with-checked-results
        ((library (library-library-build (t4-booklogic-booklogic-library book))))
      (t4-booklogic-booklogic-with-arithmetic
       (t4-booklogic-booklogic-with-library book library) t))))

(defund t4-booklogic-step-limit-result (book)
  (let ((remaining (t4-booklogic-booklogic-remaining book))
        (total (t4-booklogic-booklogic-total-remaining book)))
    (if (eq remaining :none)
        (cons '(:failure "failure" "") book)
      (let* ((remaining (1- remaining))
             (total (if (eq total :none) :none (1- total)))
             (book (t4-booklogic-booklogic-with-total-remaining
                    (t4-booklogic-booklogic-with-remaining book remaining) total)))
        (cons (and (or (< remaining 0) (and (not (eq total :none)) (< total 0)))
                   '(:failure "search-miss" ""))
              book)))))

(defund t4-booklogic-search-miss-p (value)
  (and (failure-p value) (member-equal (cadr value) '("search-miss" "value"))))

(defund t4-booklogic-step-at (step index)
  (proof-with-checked-results ((term (proof-step-first step)))
    (proof-term-at term index)))

(defund t4-booklogic-all-quoted-p (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *proof-quote*)
           (t4-booklogic-all-quoted-p (cdr terms)))))

(defund t4-booklogic-quoted-values (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((value (proof-term-at (car terms) 1))
         (rest (t4-booklogic-quoted-values (cdr terms))))
      (cons value rest))))

(defund t4-booklogic-rational-data-p (values)
  (or (endp values)
      (let ((value (car values)))
        (and (or (integerp value) (eq value t)
                 (and (consp value) (equal (car value) "ratio")))
             (t4-booklogic-rational-data-p (cdr values))))))

(defund t4-booklogic-rational-value (value)
  (cond ((integerp value) value)
        ((eq value t) 1)
        (t
         (proof-with-checked-results ((parts (proof-list-of-length (cdr value) 2)))
           (if (equal (cadr parts) 0)
               '(:failure "failure" "")
             (/ (car parts) (cadr parts)))))))

(defund t4-booklogic-rational-values (values)
  (if (endp values)
      nil
    (proof-with-checked-results
        ((value (t4-booklogic-rational-value (car values)))
         (rest (t4-booklogic-rational-values (cdr values))))
      (cons value rest))))

(defund t4-booklogic-rational-datum (value)
  (if (integerp value)
      value
    (list "ratio" (numerator value) (denominator value))))

(defund t4-booklogic-compute-rational (proof term values)
  (if (not (t4-booklogic-rational-data-p values))
      nil
    (proof-with-checked-results ((nums (t4-booklogic-rational-values values)))
      (let ((head (car term)))
        (proof-with-checked-results
            ((a (proof-term-at nums 0))
             (b (if (equal head *proof-minus*) nil (proof-term-at nums 1))))
          (proof-proof-compute
           proof term
           (cond ((equal head *proof-less*) (if (< a b) *proof-t* *proof-nil*))
                 ((equal head *proof-plus*) (t4-booklogic-rational-datum (+ a b)))
                 ((equal head *proof-times*) (t4-booklogic-rational-datum (* a b)))
                 (t (t4-booklogic-rational-datum (- a))))))))))

(defund t4-booklogic-compute-constant (book term values)
  (let ((proof (t4-booklogic-booklogic-proof book))
        (head (car term)))
    (cond
     ((equal head *proof-cons*)
      (if (equal (len values) 2)
          (proof-proof-compute proof term
                               (proof-constant-cons-value (car values) (cadr values)))
        '(:failure "search-miss" "")))
     ((member-equal head (list (proof-cl "CHARACTERP") (proof-cl "SYMBOLP")
                               (proof-cl "SYMBOL-NAME")
                               (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2")))
      (proof-with-checked-results
          ((value (proof-term-at values 0))
           (tag (if (consp value) (car value)
                  (if (null value) *t4-booklogic-term-shape-failure* nil))))
        (cond
         ((equal head (proof-cl "CHARACTERP"))
          (proof-proof-compute proof term (if (equal tag "char") *proof-t* *proof-nil*)))
         ((equal head (proof-cl "SYMBOLP"))
          (proof-proof-compute proof term (if (equal tag "sym") *proof-t* *proof-nil*)))
         ((equal head (proof-cl "SYMBOL-NAME"))
          (proof-with-checked-results
              ((name (if (equal tag "sym") (proof-term-at value 2) "")))
            (proof-proof-compute proof term (list "str" name))))
         ((not (equal tag "sym"))
          (proof-proof-compute proof term (list "str" "")))
         (t (proof-with-checked-results ((pkg (proof-term-at value 1)))
              (and (member-equal pkg (t4-booklogic-booklogic-packages book))
                   (proof-proof-compute proof term (list "str" pkg))))))))
     ((member-equal head (list *proof-plus* *proof-times* *proof-minus* *proof-less*))
      (t4-booklogic-compute-rational proof term values))
     (t nil))))

(defun t4-booklogic-booklogic-constant (book term)
  (proof-with-checked-results
      ((inherited (t4-ordinals-ordinals-constant (t4-booklogic-booklogic-library book) term)))
    (let ((book (t4-booklogic-booklogic-with-library book (cdr inherited))))
      (if (or (car inherited) (not (t4-booklogic-all-quoted-p (cdr term))))
          (cons (car inherited) book)
        (proof-with-checked-results
            ((values (t4-booklogic-quoted-values (cdr term)))
             (result (t4-booklogic-compute-constant book term values)))
          (cons result book))))))

(mutual-recursion
 (defun t4-booklogic-booklogic-branch-test (book term)
   (declare (xargs :measure (acl2-count term)) (ignorable book))
   (cond ((not (proof-compound term)) nil)
         ((endp term) *t4-booklogic-term-shape-failure*)
         ((proof-is-call term *proof-quote*) nil)
         ((member-equal (car term) (list *proof-if* *proof-not*))
          (if (consp (cdr term))
              (or (t4-booklogic-booklogic-branch-test book (cadr term)) (cadr term))
            *t4-booklogic-term-shape-failure*))
         (t (t4-booklogic-branch-test-arguments book (cdr term)))))
 (defund t4-booklogic-branch-test-arguments (book args)
   (declare (xargs :measure (acl2-count args)))
   (and (consp args)
        (or (t4-booklogic-booklogic-branch-test book (car args))
            (t4-booklogic-branch-test-arguments book (cdr args))))))

(defund t4-booklogic-adapt-argument (book term arg index)
  (cond
   ((not (proof-compound arg)) nil)
   ((endp arg) *t4-booklogic-term-shape-failure*)
   ((proof-is-call arg *proof-quote*) nil)
   (t
    (let* ((head (car arg))
           (definition (assoc-equal head (t4-booklogic-definitions book)))
           (proof (t4-booklogic-booklogic-proof book)))
      (proof-with-checked-results
          ((opening (cond ((proof-compound head) (proof-proof-beta proof arg))
                          (definition
                           (proof-with-checked-results
                               ((size (t4-booklogic-definition-size book definition)))
                             (and (<= size 100) (proof-proof-unfold proof arg))))
                          (t nil))))
        (and opening
             (proof-with-checked-results
                 ((value (t4-booklogic-step-at opening 2))
                  (reflexive (proof-proof-reflexive proof term))
                  (equation (proof-proof-rewrite proof reflexive opening (list 1 2 index)))
                  (tidy (proof-proof-tidy proof equation)))
               (list (update-nth index value term) tidy))))))))

(defund t4-booklogic-adapt-arguments (book term args index)
  (if (endp args)
      nil
    (proof-with-checked-results
        ((first (t4-booklogic-adapt-argument book term (car args) index))
         (rest (t4-booklogic-adapt-arguments book term (cdr args) (1+ index))))
      (if first (cons first rest) rest))))

(defund t4-booklogic-step-map (steps map)
  (if (endp steps)
      map
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (t4-booklogic-step-map (cdr steps) (table-put map literal (car steps))))))

(defund t4-booklogic-consequence-for-rule (book rule term item knowledge)
  (proof-with-checked-results ((matched (t4-booklogic-match (cadr rule) term nil)))
    (if (not (car matched))
        knowledge
      (let ((proof (t4-booklogic-booklogic-proof book)))
        (proof-with-checked-results
            ((fact (proof-proof-fact proof (car rule) (table-items (cdr matched))))
             (antecedent-result (t4-booklogic-step-at fact 2)))
          (if (assoc-equal antecedent-result knowledge)
              knowledge
            (proof-with-checked-results
                ((result (proof-proof-modus-ponens proof fact item))
                 (literal (proof-step-first result)))
              (table-put knowledge literal result))))))))

(defund t4-booklogic-consequence-rules (book rules term item knowledge)
  (cond ((endp rules) (cons nil knowledge))
        ((>= (len knowledge) 28) (cons t knowledge))
        (t (proof-with-checked-results
               ((next (t4-booklogic-consequence-for-rule book (car rules) term item knowledge)))
             (t4-booklogic-consequence-rules book (cdr rules) term item next)))))

(defund t4-booklogic-consequences (book original knowledge)
  (if (endp original)
      (cons (table-values knowledge) book)
    (let ((term (caar original)))
      (if (not (proof-compound term))
          (t4-booklogic-consequences book (cdr original) knowledge)
        (proof-with-checked-results ((head (proof-term-at term 0)))
          (let* ((premises (t4-booklogic-booklogic-premises book))
                 (entry (assoc-equal head premises))
                 (book (if entry book
                         (t4-booklogic-booklogic-with-premises
                          book (table-put premises head nil)))))
            (proof-with-checked-results
                ((result (t4-booklogic-consequence-rules book (cdr entry) term
                                                       (cdar original) knowledge)))
              (if (car result)
                  (cons (table-values (cdr result)) book)
                (t4-booklogic-consequences book (cdr original) (cdr result))))))))))

(defund t4-booklogic-evidence-values (evidence)
  (append (table-values (t4-structural-evidence-extra evidence))
          (table-values (t4-structural-evidence-found evidence))))

(defun t4-booklogic-booklogic-consequences (book evidence)
  (proof-with-checked-results
      ((knowledge (t4-booklogic-step-map (t4-booklogic-evidence-values evidence) nil))
       (result (t4-booklogic-consequences book knowledge knowledge)))
    (list (car result) (cdr result) evidence)))

(defund t4-booklogic-evidence-after-library (evidence prior current)
  (if (and evidence (not (equal prior current))
           (equal (t4-structural-evidence-proof evidence) prior))
      (t4-structural-evidence-with-proof evidence current)
    evidence))

(defund t4-booklogic-find (book evidence term)
  (let ((found (t4-structural-evidence-find evidence term)))
    (if (failure-p found)
        (list found book evidence)
      (list (car found) book (cdr found)))))

; Search results carry the current BookLogic and the caller's updated context.
(defund t4-booklogic-proof-result (result book evidence)
  (list result book evidence))

(defund t4-booklogic-library-result (result book evidence)
  (if (failure-p result)
      (list result book evidence)
    (let ((library (cdr result)))
      (list (car result) (t4-booklogic-booklogic-with-library book library)
            (t4-booklogic-evidence-after-library
             evidence (t4-booklogic-booklogic-library book) library)))))

(defund t4-booklogic-book-result (result book evidence)
  (if (failure-p result)
      (list result book evidence)
    (let ((updated (cdr result)))
      (list (car result) updated
            (t4-booklogic-evidence-after-library
             evidence (t4-booklogic-booklogic-library book)
             (t4-booklogic-booklogic-library updated))))))

(defund t4-booklogic-return-result (result)
  (if (failure-p (car result)) (car result) result))

(defund t4-booklogic-return-pair (result)
  (if (failure-p (car result)) (car result) (cons (car result) (cadr result))))

(defmacro t4-booklogic-return (value)
  `(t4-booklogic-proof-result ,value book evidence))

(defmacro t4-booklogic-try (name form body)
  `(let* ((step-result ,form)
          (,name (car step-result))
          (book (cadr step-result))
          (evidence (caddr step-result)))
     (declare (ignorable book evidence ,name))
     ,body))

(defmacro t4-booklogic-bind (name form body)
  `(let* ((step-result ,form)
          (,name (car step-result))
          (book (cadr step-result))
          (evidence (caddr step-result)))
     (declare (ignorable book evidence ,name))
     (if (failure-p ,name) step-result ,body)))

(defmacro t4-booklogic-check (bindings result)
  (if (endp bindings)
      result
    `(let ((checked-value ,(cadar bindings)))
       (if (failure-p checked-value)
           (t4-booklogic-return checked-value)
         (let ((,(caar bindings) checked-value))
           (declare (ignorable ,(caar bindings)))
           (t4-booklogic-check ,(cdr bindings) ,result))))))

(defmacro t4-booklogic-proof (function &rest args)
  `(,function (t4-booklogic-booklogic-proof book) ,@args))

(defmacro t4-booklogic-library (function &rest args)
  `(,function (t4-booklogic-booklogic-library book) ,@args))

(defund t4-booklogic-arithmetic-result (book evidence)
  (let ((updated (t4-booklogic-booklogic-use-arithmetic book)))
    (if (failure-p updated)
        (list updated book evidence)
      (list nil updated (t4-booklogic-evidence-after-library
                         evidence (t4-booklogic-booklogic-library book)
                         (t4-booklogic-booklogic-library updated))))))

(defund t4-booklogic-open-conjunct (n book step path)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-booklogic-open-conjunct"))
   ((endp path) step)
   (t (proof-with-checked-results
          ((conjuncts (t4-booklogic-proof proof-proof-conjunct step))
           (next (proof-term-at conjuncts (car path))))
        (t4-booklogic-open-conjunct (1- n) book next (cdr path))))))

(defund t4-booklogic-negated-quoted-proof (book term)
  (if (equal term *proof-false*)
      (t4-booklogic-proof proof-proof-not-nil)
    (proof-with-checked-results
        ((choice (t4-booklogic-proof proof-proof-nil-or-true term))
         (equation (t4-booklogic-proof proof-proof-compute
                                      (proof-eq term *proof-false*) *proof-nil*))
         (rewritten (t4-booklogic-proof proof-proof-rewrite choice equation '(1))))
      (t4-booklogic-proof proof-proof-tidy rewritten))))

(defund t4-booklogic-denied-equation (book term denied)
  (proof-with-checked-results
      ((possible (t4-booklogic-proof proof-proof-nil-or-true term))
       (positive (t4-booklogic-proof proof-proof-front possible term)))
    (t4-booklogic-proof proof-proof-cut positive denied)))

(defund t4-booklogic-fuel (name book evidence)
  (list (list :failure "fuel" name) book evidence))

; The simplifier uses the current BookLogic to evaluate constant terms.
(mutual-recursion
 (defund t4-booklogic-simplify (n book term premises definitions evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-simplify" book evidence)
     (t4-booklogic-bind first
         (t4-booklogic-simplify-base (1- n) book term premises definitions evidence)
       (t4-booklogic-check
           ((reduced (if first (t4-booklogic-step-at first 2) term))
            (test (and (proof-is-call reduced *proof-if*) (proof-term-at reduced 1))))
         (if (not (and (proof-is-call test *proof-quote*) (not (equal test *proof-false*))))
             (t4-booklogic-return first)
           (t4-booklogic-check
               ((nonnil (t4-booklogic-negated-quoted-proof book test))
                (selected (t4-booklogic-proof proof-proof-select reduced nonnil))
                (right (proof-term-at reduced 2)))
             (t4-booklogic-bind next
                 (t4-booklogic-simplify (1- n) book right premises definitions evidence)
               (t4-booklogic-check
                   ((opened (t4-booklogic-proof proof-proof-chain selected (list next))))
                 (t4-booklogic-return
                  (if first (t4-booklogic-proof proof-proof-chain first (list opened))
                    opened))))))))))

 (defund t4-booklogic-simplify-base (n book term premises definitions evidence)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-simplify-base" book evidence))
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
     (t4-booklogic-return nil))
    ((endp term) (t4-booklogic-return *t4-booklogic-term-shape-failure*))
    ((or (proof-compound (car term)) (member-equal (car term) definitions))
     (t4-booklogic-check ((expansion (t4-booklogic-proof proof-simplify-expansion term)))
       (t4-booklogic-bind next
           (t4-booklogic-simplify (1- n) book (cadr expansion) premises definitions evidence)
         (t4-booklogic-return (t4-booklogic-proof proof-proof-chain (car expansion) (list next))))))
    ((proof-is-call term *proof-if*)
     (t4-booklogic-check ((test (proof-term-at term 1)))
       (t4-booklogic-bind first
           (t4-booklogic-simplify (1- n) book test premises definitions evidence)
         (t4-booklogic-check ((path (t4-booklogic-proof proof-simplify-if-path term first premises)))
           (if (not (eq (car path) :simplify))
               (t4-booklogic-return path)
             (t4-booklogic-bind next
                 (t4-booklogic-simplify (1- n) book (caddr path) premises definitions evidence)
               (t4-booklogic-return (t4-booklogic-proof proof-proof-chain (cadr path)
                                                        (list next)))))))))
    (t (t4-booklogic-simplify-arguments (1- n) book term (cdr term) 1 nil
                                        premises definitions evidence))))

 (defund t4-booklogic-simplify-arguments (n book term args index first premises definitions evidence)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-simplify-arguments" book evidence))
    ((endp args)
     (t4-booklogic-check ((current (if first (t4-booklogic-step-at first 2) term)))
       (t4-booklogic-bind constant
           (t4-booklogic-book-result (t4-booklogic-booklogic-constant book current)
                                     book evidence)
         (t4-booklogic-return
          (cond ((not constant) first)
                (first (t4-booklogic-proof proof-proof-chain first (list constant)))
                (t constant))))))
    (t
     (t4-booklogic-bind argument
         (t4-booklogic-simplify (1- n) book (car args) premises definitions evidence)
       (t4-booklogic-check
           ((next (t4-booklogic-proof proof-simplify-argument-result term index first argument)))
         (t4-booklogic-simplify-arguments (1- n) book term (cdr args) (1+ index) next
                                           premises definitions evidence))))))
 )

(defund t4-booklogic-prove (n book term premises definitions evidence)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-prove" book evidence))
   ((equal term *proof-true*)
    (t4-booklogic-return (t4-booklogic-proof proof-proof-prove term nil nil)))
   (t
    (t4-booklogic-check ((premise (proof-find-evidence premises (list term))))
      (if premise
          (t4-booklogic-return premise)
        (t4-booklogic-bind equality
            (t4-booklogic-simplify 1000000 book term premises definitions evidence)
          (t4-booklogic-check ((right (and equality (t4-booklogic-step-at equality 2))))
            (cond
             ((or (not equality) (equal right term))
              (t4-booklogic-return (proof-prove-unproved-term term)))
             ((equal right *proof-true*)
              (t4-booklogic-return (t4-booklogic-proof proof-proof-true-from-eq equality)))
             (t
              (t4-booklogic-bind result
                  (t4-booklogic-prove (1- n) book right premises definitions evidence)
                (t4-booklogic-return
                 (t4-booklogic-proof proof-proof-transport result equality))))))))))))

(defund t4-booklogic-consp-cons (book term)
  (t4-booklogic-proof proof-proof-fact "consp-cons"
                      (seq-zip (list *library-x* *library-y*) (cdr term))))

(defund t4-booklogic-known-pair (book term pair)
  (let ((empty (proof-eq term *proof-false*)))
    (proof-with-checked-results
        ((assumed (t4-booklogic-proof proof-proof-assume empty t))
         (impossible (t4-booklogic-proof proof-proof-rewrite pair assumed '(1 1)))
         (computed (t4-booklogic-proof proof-proof-compute
                                       (list *proof-consp* *proof-false*) *proof-nil*))
         (impossible (t4-booklogic-proof proof-proof-rewrite impossible computed '(1)))
         (impossible (t4-booklogic-proof proof-proof-tidy impossible))
         (possible (t4-booklogic-proof proof-proof-nil-or-true term))
         (negative (t4-booklogic-proof proof-proof-front impossible (proof-neg empty))))
      (t4-booklogic-proof proof-proof-cut possible negative))))

(defund t4-booklogic-count-constructor-comparison (book whole part pair evidence)
  (t4-booklogic-check ((sides (proof-list-of-length (cdr pair) 2)))
    (let* ((left (car sides))
           (right (cadr sides))
           (left-p (equal part (list *library-count* left))))
      (if (and (not left-p) (not (equal part (list *library-count* right))))
          (t4-booklogic-return nil)
        (t4-booklogic-bind arithmetic (t4-booklogic-arithmetic-result book evidence)
            (t4-booklogic-check
                ((cons-step (t4-booklogic-consp-cons book pair))
                 (builtin (t4-booklogic-library library-library-builtin
                                                (if left-p 2 3) pair))
                 (smaller (t4-booklogic-proof proof-proof-discharge builtin cons-step))
                 (value (t4-booklogic-library library-library-axiom
                                              (if left-p "CAR-CONS" "CDR-CONS") sides))
                 (smaller (t4-booklogic-proof proof-proof-rewrite smaller value '(1 1 1)))
                 (ordinal (t4-booklogic-library library-library-ordinal-comparison part whole))
                 (integer (t4-booklogic-proof proof-proof-rewrite smaller ordinal '(1))))
              (t4-booklogic-return (t4-booklogic-library library-library-as-weak integer))))))))

(mutual-recursion
 (defund t4-booklogic-known (n book term evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-known" book evidence)
     (t4-booklogic-bind direct (t4-booklogic-find book evidence term)
       (cond
        (direct (t4-booklogic-return direct))
        ((equal term *proof-true*)
         (t4-booklogic-return (t4-booklogic-proof proof-proof-prove *proof-true* nil nil)))
        ((proof-is-call term *proof-consp*)
         (t4-booklogic-check ((arg (proof-term-at term 1)))
           (if (proof-is-call arg *proof-quote*)
               (t4-booklogic-bind constant
                   (t4-booklogic-book-result
                    (t4-booklogic-booklogic-constant book term) book evidence)
                 (t4-booklogic-check ((right (t4-booklogic-step-at constant 2)))
                   (if (equal right *proof-true*)
                       (t4-booklogic-return
                        (t4-booklogic-proof proof-proof-true-from-eq constant))
                     (t4-booklogic-known-after-quote (1- n) book term evidence))))
             (t4-booklogic-known-after-quote (1- n) book term evidence))))
        (t (t4-booklogic-known-after-quote (1- n) book term evidence))))))

 (defund t4-booklogic-known-after-quote (n book term evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-known-after-quote" book evidence)
     (cond
      ((proof-is-call term *proof-not*)
       (t4-booklogic-check ((arg (proof-term-at term 1)))
         (if (proof-is-call arg *proof-less*)
             (t4-booklogic-try result (t4-booklogic-count-comparison (1- n) book term evidence)
               (t4-booklogic-return
                (if (t4-booklogic-search-miss-p result) nil result)))
           (t4-booklogic-known-with-shape (1- n) book term evidence))))
      ((and (proof-is-call term *proof-consp*) (proof-is-call (cadr term) *proof-cons*))
       (t4-booklogic-return (t4-booklogic-consp-cons book (cadr term))))
      ((member-equal (and (proof-compound term) (car term))
                     (list *proof-integerp* *library-natp*))
       (t4-booklogic-check ((arg (proof-term-at term 1)))
         (if (or (proof-is-call arg *library-len*) (proof-is-call arg *library-count*))
             (t4-booklogic-bind arithmetic (t4-booklogic-arithmetic-result book evidence)
               (t4-booklogic-return
                (if (equal (car term) *proof-integerp*)
                    (t4-booklogic-library t4-ordinals-ordinals-type-of arg nil)
                  (t4-booklogic-library t4-ordinals-ordinals-natural arg))))
           (t4-booklogic-known-with-shape (1- n) book term evidence))))
      (t (t4-booklogic-known-with-shape (1- n) book term evidence)))))

 (defund t4-booklogic-known-with-shape (n book term evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-known-with-shape" book evidence)
     (t4-booklogic-bind pair
         (if (proof-is-call term *proof-cons*)
             (t4-booklogic-return (t4-booklogic-consp-cons book term))
           (t4-booklogic-find book evidence (list *proof-consp* term)))
       (cond
        (pair (t4-booklogic-return (t4-booklogic-known-pair book term pair)))
        ((proof-is-call term *proof-if*)
         (t4-booklogic-check ((otherwise-branch (proof-term-at term 3)))
           (if (not (equal otherwise-branch *proof-false*))
               (t4-booklogic-return nil)
             (t4-booklogic-bind left (t4-booklogic-known (1- n) book (cadr term) evidence)
               (t4-booklogic-bind right
                   (t4-booklogic-known (1- n) book (caddr term) evidence)
                 (if (and left right)
                     (t4-booklogic-prove 1000000 book term (list left right) nil evidence)
                   (t4-booklogic-return nil)))))))
        (t (t4-booklogic-return nil))))))

 (defund t4-booklogic-count-comparison (n book term evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-count-comparison" book evidence)
     (t4-booklogic-check
         ((test (if (proof-is-call term *proof-not*) (proof-term-at term 1) nil)))
       (if (not (proof-is-call test *proof-less*))
           (t4-booklogic-return nil)
         (t4-booklogic-check ((parts (proof-list-of-length test 3)))
           (let ((whole (cadr parts))
                 (part (caddr parts)))
             (cond
              ((and (proof-is-call whole *library-count*) (equal part *proof-zero*))
               (t4-booklogic-bind arithmetic (t4-booklogic-arithmetic-result book evidence)
                 (t4-booklogic-check
                     ((natural (t4-booklogic-library t4-ordinals-ordinals-natural whole)))
                   (t4-booklogic-return
                    (t4-booklogic-library library-library-cite "NATURAL-NONNEGATIVE"
                                         (list whole) (list natural))))))
              ((equal whole part)
               (t4-booklogic-bind arithmetic (t4-booklogic-arithmetic-result book evidence)
                 (t4-booklogic-check
                     ((integer (t4-booklogic-library t4-ordinals-ordinals-type-of part nil)))
                   (t4-booklogic-return
                    (t4-booklogic-library library-library-cite "WEAK-REFLEXIVE"
                                         (list part) (list integer))))))
              ((not (and (proof-is-call whole *library-count*)
                         (proof-is-call part *library-count*)))
               (t4-booklogic-return nil))
              (t
               (t4-booklogic-check ((obj (proof-term-at whole 1)))
                 (if (proof-is-call obj *proof-cons*)
                     (t4-booklogic-count-constructor-comparison book whole part obj evidence)
                   (if (not (proof-compound obj))
                       (t4-booklogic-return nil)
                     (t4-booklogic-check ((head (proof-term-at obj 0)))
                       (if (member-equal head (list *proof-if* *proof-quote*))
                           (t4-booklogic-return nil)
                         (t4-booklogic-check ((arg (proof-term-at part 1)))
                           (t4-booklogic-count-projections
                            (1- n) book obj arg (list *library-car* *library-cdr*)
                            '("COUNT-CAR-WEAK" "COUNT-CDR-WEAK") evidence)))))))))))))))

 (defund t4-booklogic-count-projections (n book obj part selectors names evidence)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-count-projections" book evidence))
    ((endp selectors) (t4-booklogic-return nil))
    (t
     (let ((goal (proof-eq (list (car selectors) obj) part)))
       (t4-booklogic-bind value (t4-booklogic-fact-proof (1- n) book goal evidence)
         (if (not value)
             (t4-booklogic-count-projections (1- n) book obj part
                                             (cdr selectors) (cdr names) evidence)
           (t4-booklogic-bind arithmetic (t4-booklogic-arithmetic-result book evidence)
             (t4-booklogic-check
                 ((bound (t4-booklogic-library library-library-cite (car names) (list obj) nil)))
               (t4-booklogic-return
                (t4-booklogic-proof proof-proof-rewrite-first bound value))))))))))

 (defund t4-booklogic-discharge-known (n book step evidence seen)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-discharge-known" book evidence)
     (t4-booklogic-check ((literal (proof-step-first step)))
       (if (not (proof-is-call literal *library-implies*))
           (t4-booklogic-return step)
         (t4-booklogic-check ((antecedent (proof-term-at literal 1)))
           (if (member-equal antecedent seen)
               (t4-booklogic-return nil)
             (t4-booklogic-bind test (t4-booklogic-known (1- n) book antecedent evidence)
               (if test
                   (t4-booklogic-check
                       ((next (t4-booklogic-proof proof-proof-modus-ponens step test)))
                     (t4-booklogic-discharge-known (1- n) book next evidence (cons antecedent seen)))
                 (t4-booklogic-discharge-negated-equality
                  (1- n) book step antecedent evidence (cons antecedent seen))))))))))

 (defund t4-booklogic-discharge-negated-equality (n book step antecedent evidence seen)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-discharge-negated-equality" book evidence)
     (t4-booklogic-check
         ((inner (if (proof-is-call antecedent *proof-not*)
                     (proof-term-at antecedent 1) nil)))
       (if (not (proof-is-call inner *proof-equal*))
           (t4-booklogic-return nil)
         (t4-booklogic-bind equation
             (t4-booklogic-book-result
              (t4-booklogic-booklogic-constant book inner) book evidence)
           (t4-booklogic-check ((right (and equation (t4-booklogic-step-at equation 2))))
             (if (not (equal right *proof-false*))
                 (t4-booklogic-return nil)
               (t4-booklogic-check
                   ((not-nil (t4-booklogic-proof proof-proof-not-nil))
                    (test (t4-booklogic-library library-library-transport-argument
                                                not-nil equation 1))
                    (next (t4-booklogic-proof proof-proof-modus-ponens step test)))
                 (t4-booklogic-discharge-known (1- n) book next evidence seen)))))))))

 (defund t4-booklogic-rule-proof (n book term evidence rule projected mode)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-rule-proof" book evidence)
     (let ((pattern (if projected (caddr rule) (cadr rule))))
       (t4-booklogic-check ((matched (t4-booklogic-match pattern term nil)))
         (if (not (car matched))
             (t4-booklogic-return nil)
           (t4-booklogic-check
               ((fact (t4-booklogic-proof proof-proof-fact (car rule) (table-items (cdr matched))))
                (start (if projected (t4-booklogic-open-conjunct 1000000 book fact (cadr rule))
                         fact))
                (literal (proof-step-first start)))
             (if (and (eq mode :fact) (equal literal term))
                 (t4-booklogic-return start)
               (t4-booklogic-bind result
                   (t4-booklogic-discharge-known (1- n) book start evidence nil)
                 (if (not result)
                     (t4-booklogic-return nil)
                   (t4-booklogic-check
                       ((actual (case mode
                                  (:equation (t4-booklogic-step-at result 2))
                                  (:adapt-equation (t4-booklogic-step-at result 1))
                                  (otherwise (proof-step-first result)))))
                     (t4-booklogic-return
                      (and (if (eq mode :equation)
                               (not (equal actual term))
                             (equal actual term))
                           result))))))))))))

 (defund t4-booklogic-rule-search (n book term evidence rules projected mode)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-rule-search" book evidence))
    ((endp rules) (t4-booklogic-return nil))
    (t (t4-booklogic-bind result
           (t4-booklogic-rule-proof (1- n) book term evidence (car rules) projected mode)
         (if result (t4-booklogic-return result)
           (t4-booklogic-rule-search (1- n) book term evidence (cdr rules) projected mode))))))

 (defund t4-booklogic-adapted-search (n book term args index evidence mode)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-adapted-search" book evidence))
    ((endp args) (t4-booklogic-return nil))
    (t
     (t4-booklogic-check ((pair (t4-booklogic-adapt-argument book term (car args) index)))
       (if (not pair)
           (t4-booklogic-adapted-search (1- n) book term (cdr args) (1+ index) evidence mode)
         (let ((adapted (car pair))
               (opening (cadr pair))
               (index-map (if (eq mode :adapt-fact)
                              (t4-booklogic-booklogic-rules book)
                            (t4-booklogic-booklogic-equalities book))))
           (t4-booklogic-check ((rules (t4-booklogic-candidates index-map adapted)))
             (t4-booklogic-bind result (t4-booklogic-rule-search (1- n) book adapted evidence
                                                                rules nil mode)
               (if result
                   (t4-booklogic-return
                    (if (eq mode :adapt-fact)
                        (t4-booklogic-proof proof-proof-transport result opening)
                      (t4-booklogic-proof proof-proof-chain opening (list result))))
                 (t4-booklogic-adapted-search (1- n) book term (cdr args)
                                             (1+ index) evidence mode))))))))))

 (defund t4-booklogic-extra-proof (n book term evidence steps)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-extra-proof" book evidence))
    ((endp steps) (t4-booklogic-return nil))
    (t
     (let ((step (car steps)))
       (t4-booklogic-check ((literal (proof-step-first step))
                           (conclusion (t4-booklogic-strip-implications literal)))
         (t4-booklogic-bind result
             (if (and (equal conclusion term) (not (equal conclusion literal)))
                 (t4-booklogic-discharge-known (1- n) book step evidence nil)
               (t4-booklogic-return nil))
           (if result (t4-booklogic-return result)
             (t4-booklogic-extra-proof (1- n) book term evidence (cdr steps)))))))))

 (defund t4-booklogic-fact-proof (n book term evidence)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-fact-proof" book evidence))
    ((not (proof-compound term)) (t4-booklogic-return nil))
    (t
     (t4-booklogic-check ((rules (t4-booklogic-candidates (t4-booklogic-booklogic-rules book) term)))
       (t4-booklogic-bind result
           (t4-booklogic-rule-search (1- n) book term evidence rules nil :fact)
         (if result (t4-booklogic-return result)
           (t4-booklogic-check
               ((projected (t4-booklogic-candidates
                            (t4-booklogic-booklogic-projected-rules book) term)))
             (t4-booklogic-bind result
                 (t4-booklogic-rule-search (1- n) book term evidence projected t :fact)
               (if result (t4-booklogic-return result)
                 (t4-booklogic-bind extra
                     (t4-booklogic-extra-proof (1- n) book term evidence
                                              (table-values (t4-structural-evidence-extra evidence)))
                   (if (or extra
                           (not (and (t4-booklogic-booklogic-enhanced book)
                                     (member-equal (car term)
                                                   (t4-booklogic-booklogic-rule-heads book)))))
                       (t4-booklogic-return extra)
                     (t4-booklogic-adapted-search
                      (1- n) book term (cdr term) 1 evidence :adapt-fact))))))))))))

 (defund t4-booklogic-evidence-equation (n book term evidence steps)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-evidence-equation" book evidence))
    ((endp steps) (t4-booklogic-return nil))
    (t
     (t4-booklogic-bind equality
         (t4-booklogic-discharge-known (1- n) book (car steps) evidence nil)
       (t4-booklogic-check ((literal (and equality (proof-step-first equality)))
                           (sides (and (proof-is-call literal *proof-equal*)
                                       (proof-list-of-length (cdr literal) 2))))
         (if (and sides (equal (car sides) term) (not (equal (car sides) (cadr sides))))
             (t4-booklogic-return equality)
           (t4-booklogic-evidence-equation (1- n) book term evidence (cdr steps))))))))

 (defund t4-booklogic-equation (n book term evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-equation" book evidence)
     (t4-booklogic-bind equality
         (t4-booklogic-evidence-equation (1- n) book term evidence
                                        (t4-booklogic-evidence-values evidence))
       (if (or equality (not (t4-booklogic-booklogic-enhanced book))
               (not (proof-compound term)))
           (t4-booklogic-return equality)
         (t4-booklogic-check ((head (proof-term-at term 0)))
           (if (not (member-equal head (t4-booklogic-booklogic-equality-heads book)))
               (t4-booklogic-return nil)
             (t4-booklogic-check
                 ((rules (t4-booklogic-candidates
                          (t4-booklogic-booklogic-equalities book) term)))
               (t4-booklogic-bind direct
                   (t4-booklogic-rule-search (1- n) book term evidence rules nil :equation)
                 (if direct (t4-booklogic-return direct)
                   (t4-booklogic-adapted-search
                    (1- n) book term (cdr term) 1 evidence :adapt-equation))))))))))
 )

(defund t4-booklogic-fresh-evidence (book tests extra)
  (t4-booklogic-library t4-structural-evidence-init tests extra))

(defund t4-booklogic-evaluation-recipe (kind book library args evidence replies)
  (let ((rules (t4-booklogic-booklogic-evaluators book)))
    (case kind
      (:equation
       (t4-evaluation-evaluation-rules-equation rules library (car args) evidence replies))
      (:reapply
       (t4-evaluation-evaluation-rules-reapply rules library (car args) (cadr args)
                                               (caddr args) (cadddr args) replies))
      (otherwise '(:failure "search-miss" "")))))

(defund t4-booklogic-evaluation-reply (book request)
  (let* ((library (t4-evaluation-request-library request))
         (book (t4-booklogic-booklogic-with-library book library))
         (args (t4-evaluation-request-arguments request))
         (evidence (cadr args)))
    (case (t4-evaluation-request-operation request)
      (:known (t4-booklogic-known 1000000 book (car args) evidence))
      (:find (t4-booklogic-find book evidence (car args)))
      (:prove (t4-booklogic-prove 1000000 book (car args) (cadr args) (caddr args) nil))
      (otherwise (list '(:failure "search-miss" "") book nil)))))

(defund t4-booklogic-evaluation-reply-value (operation result)
  (let ((value (car result))
        (library (t4-booklogic-booklogic-library (cadr result))))
    (cond ((failure-p value) value)
          ((member-eq operation '(:known :find))
           (cons value (cons library (caddr result))))
          (t (cons value library)))))

(defund t4-booklogic-evaluation-replay (n kind book library args original-evidence replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-evaluation-replay" book original-evidence)
    (let ((value (t4-booklogic-evaluation-recipe kind book library args original-evidence replies)))
      (cond
       ((t4-evaluation-request-p value)
        (let* ((response (t4-booklogic-evaluation-reply book value))
               (reply (t4-booklogic-evaluation-reply-value
                       (t4-evaluation-request-operation value) response)))
          (if (failure-p reply)
              response
            (t4-booklogic-evaluation-replay (1- n) kind (cadr response) library args
                                            original-evidence (append replies (list reply))))))
       ((failure-p value) (list value book original-evidence))
       ((eq kind :equation)
        (t4-booklogic-library-result (cons (car value) (cadr value)) book (cddr value)))
       (t (t4-booklogic-library-result value book original-evidence))))))

(defund t4-booklogic-evaluator-equation (book term evidence)
  (t4-booklogic-evaluation-replay 1000000 :equation book
                                 (t4-booklogic-booklogic-library book) (list term) evidence nil))

(defund t4-booklogic-evaluator-reapply (book args)
  (t4-booklogic-evaluation-replay 1000000 :reapply book
                                 (t4-booklogic-booklogic-library book) args nil nil))

(defund t4-booklogic-count-item (item items)
  (if (endp items)
      0
    (+ (if (equal item (car items)) 1 0)
       (t4-booklogic-count-item item (cdr items)))))

(defund t4-booklogic-local-unfold (book term evidence opened)
  (let* ((head (car term))
         (definition (assoc-equal head (t4-booklogic-definitions book))))
    (if (not (and definition (< (t4-booklogic-count-item head opened) 2)))
        (t4-booklogic-return nil)
      (let ((body (caddr definition)))
        (t4-booklogic-check
            ((open (or (member-equal head (t4-booklogic-booklogic-enabled book))
                       (proof-with-checked-results ((size (t4-booklogic-definition-size book definition)))
                         (or (<= size 80)
                             (and (t4-booklogic-booklogic-enhanced book)
                                  (t4-booklogic-constructor-result body)))))))
          (t4-booklogic-return (and open (t4-booklogic-proof proof-proof-unfold term))))))))

(defund t4-booklogic-known-or-denied (book term evidence)
  (t4-booklogic-bind known (t4-booklogic-known 1000000 book term evidence)
    (if known (t4-booklogic-return known)
      (t4-booklogic-find book evidence (proof-neg term)))))

(defund t4-booklogic-local-count (book term evidence opened)
  (let ((head (car term))
        (args (cdr term)))
    (cond
     ((equal head *library-count*)
      (t4-booklogic-check ((arg (proof-term-at args 0)))
        (if (proof-is-call arg *proof-quote*)
            (t4-booklogic-local-unfold book term evidence opened)
          (t4-booklogic-return nil))))
     ((equal head *proof-not*)
      (t4-booklogic-check ((arg (proof-term-at args 0)))
        (t4-booklogic-bind fact (t4-booklogic-known-or-denied book arg evidence)
          (if (or fact (proof-is-call arg *proof-quote*))
              (t4-booklogic-local-unfold book term evidence opened)
            (t4-booklogic-return nil)))))
     (t (t4-booklogic-local-unfold book term evidence opened)))))

(defund t4-booklogic-local-not-nil (book term evidence opened)
  (let ((args (cdr term)))
    (if (not (member-equal *proof-false* args))
        (t4-booklogic-local-count book term evidence opened)
      (let ((reversed (equal (car args) *proof-false*)))
        (t4-booklogic-check ((arg (proof-term-at args (if reversed 1 0))))
          (t4-booklogic-bind value (t4-booklogic-known 1000000 book arg evidence)
            (if (not value)
                (t4-booklogic-local-count book term evidence opened)
              (t4-booklogic-check
                  ((assumed (t4-booklogic-proof proof-proof-assume term t))
                   (assumed (if reversed (t4-booklogic-proof proof-proof-symmetric assumed)
                              assumed))
                   (impossible (t4-booklogic-proof proof-proof-rewrite value assumed '(1)))
                   (impossible (t4-booklogic-proof proof-proof-tidy impossible))
                   (false (t4-booklogic-proof proof-proof-front impossible (proof-neg term))))
                (t4-booklogic-return (t4-booklogic-denied-equation book term false))))))))))

(defund t4-booklogic-local-cons-equality (book term evidence opened)
  (t4-booklogic-check ((right (proof-term-at term 2)))
    (if (not (proof-is-call right *proof-cons*))
        (t4-booklogic-local-not-nil book term evidence opened)
      (t4-booklogic-check ((sides (proof-list-of-length (cdr term) 2)))
        (let* ((left (car sides))
               (constructed (proof-is-call left *proof-cons*)))
          (t4-booklogic-bind cons-step
              (if constructed (t4-booklogic-return nil)
                (t4-booklogic-known 1000000 book (list *proof-consp* left) evidence))
            (if (not (or constructed cons-step))
                (t4-booklogic-local-not-nil book term evidence opened)
              (t4-booklogic-check
                  ((left-pair (if cons-step
                                  (list (list *library-car* left) (list *library-cdr* left))
                                (proof-list-of-length (cdr left) 2)))
                   (vars (list (proof-sym "X1" "ACL2") (proof-sym "Y1" "ACL2")
                               (proof-sym "X2" "ACL2") (proof-sym "Y2" "ACL2")))
                   (fact (t4-booklogic-proof proof-proof-fact (proof-sym "CONS-EQUAL" "ACL2")
                                             (seq-zip vars (append left-pair (cdr right))))))
                (if (not cons-step)
                    (t4-booklogic-return fact)
                  (t4-booklogic-check
                      ((axiom (t4-booklogic-library library-library-axiom "CAR-CDR-ELIM"
                                                     (list left)))
                       (rebuild (t4-booklogic-proof proof-proof-modus-ponens axiom cons-step)))
                    (t4-booklogic-return
                     (t4-booklogic-proof proof-proof-rewrite fact rebuild '(1 1 1)))))))))))))

(defund t4-booklogic-local-recreate-cons (book term evidence opened)
  (t4-booklogic-check ((head (proof-term-at term 1)))
    (if (not (proof-is-call head *library-car*))
        (t4-booklogic-local-count book term evidence opened)
      (t4-booklogic-check ((tail (proof-term-at term 2))
                          (obj (proof-term-at head 1)))
        (if (not (equal tail (list *library-cdr* obj)))
            (t4-booklogic-local-count book term evidence opened)
          (t4-booklogic-bind cons-step
              (t4-booklogic-known 1000000 book (list *proof-consp* obj) evidence)
            (if (not cons-step)
                (t4-booklogic-local-count book term evidence opened)
              (t4-booklogic-check
                  ((axiom (t4-booklogic-library library-library-axiom "CAR-CDR-ELIM" (list obj))))
                (t4-booklogic-return
                 (t4-booklogic-proof proof-proof-modus-ponens axiom cons-step))))))))))

(defund t4-booklogic-local-selector (book term evidence opened)
  (t4-booklogic-check ((arg (proof-term-at term 1)))
    (t4-booklogic-bind denied (t4-booklogic-find book evidence (proof-neg (list *proof-consp* arg)))
      (if (not denied)
          (t4-booklogic-local-count book term evidence opened)
        (t4-booklogic-check
            ((name (if (equal (car term) *library-car*) "COMPLETION-OF-CAR" "COMPLETION-OF-CDR"))
             (completion (t4-booklogic-library library-library-axiom name (list arg)))
             (body (t4-booklogic-step-at completion 2))
             (selected (t4-booklogic-proof proof-proof-select body denied)))
          (t4-booklogic-return
           (t4-booklogic-proof proof-proof-chain completion (list selected))))))))

(defund t4-booklogic-local-special (book term evidence opened)
  (let ((head (car term)))
    (cond ((member-equal head (list *library-car* *library-cdr*))
           (t4-booklogic-local-selector book term evidence opened))
          ((equal head *proof-cons*) (t4-booklogic-local-recreate-cons book term evidence opened))
          ((equal head *proof-equal*) (t4-booklogic-local-cons-equality book term evidence opened))
          (t (t4-booklogic-local-count book term evidence opened)))))

(defund t4-booklogic-local-equation (book term evidence opened)
  (t4-booklogic-bind projected
      (if (t4-booklogic-booklogic-project-returns book)
          (t4-booklogic-library-result
           (t4-booklogic-library t4-results-projection-with-packages
                                 term (t4-booklogic-booklogic-packages book))
           book evidence)
        (t4-booklogic-return nil))
    (if projected (t4-booklogic-return projected)
      (t4-booklogic-bind constant
          (t4-booklogic-book-result
           (t4-booklogic-booklogic-constant book term) book evidence)
        (if constant (t4-booklogic-return constant)
          (t4-booklogic-bind equation (t4-booklogic-equation 1000000 book term evidence)
            (if equation (t4-booklogic-return equation)
              (t4-booklogic-check ((head (proof-term-at term 0)))
                (t4-booklogic-bind evaluated
                    (if (and (t4-booklogic-booklogic-evaluate-syntax book)
                             (< (t4-booklogic-count-item head opened) 3))
                        (t4-booklogic-evaluator-equation book term evidence)
                      (t4-booklogic-return nil))
                  (if evaluated (t4-booklogic-return evaluated)
                    (t4-booklogic-local-special book term evidence opened)))))))))))

(defund t4-booklogic-limit-context (book evidence)
  (let ((limit (t4-booklogic-step-limit-result book)))
    (list (car limit) (cdr limit) evidence)))

(defund t4-booklogic-rewrite-reflexive (book term previous equality place)
  (proof-with-checked-results
      ((first (or previous (t4-booklogic-proof proof-proof-reflexive term))))
    (t4-booklogic-proof proof-proof-rewrite first equality place)))

(defund t4-booklogic-normalize-identical-branches (book term first branch test)
  (proof-with-checked-results
      ((start (or first (t4-booklogic-proof proof-proof-reflexive term)))
       (yes (t4-booklogic-proof proof-proof-if-true branch))
       (no (t4-booklogic-proof proof-proof-if-false branch))
       (same (t4-booklogic-proof proof-proof-cases test yes no)))
    (t4-booklogic-proof proof-proof-chain start (list same))))

(mutual-recursion
 (defund t4-booklogic-normalize (n book term evidence opened force-open)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-normalize" book evidence)
     (t4-booklogic-bind limit (t4-booklogic-limit-context book evidence)
       (if (proof-is-call term *proof-quote*)
           (t4-booklogic-return nil)
         (t4-booklogic-bind denied (t4-booklogic-find book evidence (proof-neg term))
           (if denied
               (t4-booklogic-return (t4-booklogic-denied-equation book term denied))
             (t4-booklogic-bind equal (t4-booklogic-equation 1000000 book term evidence)
               (if equal
                   (t4-booklogic-check
                       ((chain (and (t4-booklogic-booklogic-chaining book)
                                    (proof-with-checked-results
                                        ((right (t4-booklogic-step-at equal 2))
                                         (new-size (t4-booklogic-term-size right))
                                         (old-size (t4-booklogic-term-size term)))
                                      (< new-size old-size)))))
                     (if chain
                         (t4-booklogic-normalize-chain (1- n) book evidence opened equal)
                       (t4-booklogic-return equal)))
                 (t4-booklogic-normalize-after-equation
                  (1- n) book term evidence opened force-open)))))))))

 (defund t4-booklogic-normalize-after-equation (n book term evidence opened force-open)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-normalize-after-equation" book evidence)
     (t4-booklogic-bind selected
         (if (t4-booklogic-booklogic-project-returns book)
             (t4-booklogic-library-result
              (t4-booklogic-library t4-results-projection-with-packages
                                    term (t4-booklogic-booklogic-packages book))
              book evidence)
           (t4-booklogic-return nil))
       (if selected
           (t4-booklogic-normalize-chain (1- n) book evidence opened selected)
         (t4-booklogic-bind proven
             (if (and (t4-booklogic-booklogic-chaining book) (not force-open)
                      (proof-compound term))
                 (t4-booklogic-find book evidence term)
               (t4-booklogic-return nil))
           (if (or proven (not (proof-compound term)))
               (t4-booklogic-return nil)
             (t4-booklogic-normalize-compound (1- n) book term evidence opened)))))))

 (defund t4-booklogic-normalize-chain (n book evidence opened first)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-normalize-chain" book evidence)
     (t4-booklogic-check ((right (t4-booklogic-step-at first 2)))
       (t4-booklogic-bind tail (t4-booklogic-normalize (1- n) book right evidence opened nil)
         (t4-booklogic-return (t4-booklogic-proof proof-proof-chain first (list tail)))))))

 (defund t4-booklogic-normalize-compound (n book term evidence opened)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-normalize-compound" book evidence)
     (t4-booklogic-check ((head (proof-term-at term 0)))
       (cond
        ((or (proof-compound head) (equal head *termination-return-last*))
         (t4-booklogic-check
             ((first (if (proof-compound head)
                         (t4-booklogic-proof proof-proof-beta term)
                       (t4-booklogic-proof proof-proof-unfold term))))
           (t4-booklogic-normalize-chain (1- n) book evidence opened first)))
        ((equal head *proof-if*)
         (t4-booklogic-normalize-if (1- n) book term evidence opened))
        (t
         (t4-booklogic-bind direct
             (t4-booklogic-book-result
              (t4-booklogic-booklogic-constant book term) book evidence)
           (t4-booklogic-check ((right (and direct (t4-booklogic-step-at direct 2))))
             (if (and direct (not (equal right term)))
                 (t4-booklogic-normalize-chain (1- n) book evidence opened direct)
               (t4-booklogic-normalize-arguments (1- n) book term (cdr term)
                                                 evidence opened 1 nil)))))))))

 (defund t4-booklogic-normalize-if (n book term evidence opened)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-normalize-if" book evidence)
     (t4-booklogic-check ((test (proof-term-at term 1)))
       (t4-booklogic-bind test
           (t4-booklogic-normalize (1- n) book test evidence opened nil)
         (t4-booklogic-check
             ((first (and test (t4-booklogic-rewrite-reflexive book term nil test '(1 2 1))))
              (branch (if first (t4-booklogic-step-at first 2) term))
              (test (proof-term-at branch 1)))
           (t4-booklogic-bind decision (t4-booklogic-known-or-denied book test evidence)
             (t4-booklogic-check
                 ((decision (or decision
                                (and (proof-is-call test *proof-quote*)
                                     (t4-booklogic-negated-quoted-proof book test)))))
               (if decision
                   (t4-booklogic-check ((selected (t4-booklogic-proof proof-proof-select
                                                                     branch decision)))
                     (t4-booklogic-bind tail
                         (t4-booklogic-normalize-chain (1- n) book evidence opened selected)
                       (t4-booklogic-return
                        (if first (t4-booklogic-proof proof-proof-chain first (list tail)) tail))))
                 (t4-booklogic-check
                     ((yes (proof-term-at branch 2))
                      (no (proof-term-at branch 3)))
                   (t4-booklogic-return
                    (if (equal yes no)
                        (t4-booklogic-normalize-identical-branches book term first branch test)
                      first)))))))))))

 (defund t4-booklogic-normalize-arguments (n book term args evidence opened index first)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-normalize-arguments" book evidence))
    ((endp args)
     (t4-booklogic-check ((current (if first (t4-booklogic-step-at first 2) term)))
       (t4-booklogic-bind reduced (t4-booklogic-local-equation book current evidence opened)
         (t4-booklogic-check ((right (and reduced (t4-booklogic-step-at reduced 2))))
           (if (or (not reduced) (equal right current))
               (t4-booklogic-return first)
             (let ((keep (append opened (list (car term)))))
               (t4-booklogic-bind reduction
                   (t4-booklogic-normalize-chain (1- n) book evidence keep reduced)
                 (t4-booklogic-return
                  (if first (t4-booklogic-proof proof-proof-chain first (list reduction))
                    reduction)))))))))
    (t
     (t4-booklogic-bind simplified
         (t4-booklogic-normalize (1- n) book (car args) evidence opened nil)
       (t4-booklogic-check
           ((first (if simplified
                       (t4-booklogic-rewrite-reflexive book term first simplified (list 1 2 index))
                     first)))
         (t4-booklogic-normalize-arguments (1- n) book term (cdr args) evidence opened
                                           (1+ index) first))))))
 )

(defund t4-booklogic-arithmetic-types (n book vars evidence types)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-arithmetic-types" book evidence)
    (if (endp vars)
        (t4-booklogic-return (reverse types))
      (let ((var (car vars)))
        (t4-booklogic-bind integer (t4-booklogic-find book evidence (library-integer var))
          (t4-booklogic-bind integer
              (if integer (t4-booklogic-return integer)
                (t4-booklogic-bind natural
                    (t4-booklogic-find book evidence (list *library-natp* var))
                  (t4-booklogic-return
                   (and natural (t4-booklogic-library library-library-cite
                                                       "NATURAL-INTEGER" (list var) (list natural))))))
            (t4-booklogic-arithmetic-types (1- n) book (cdr vars) evidence
                                          (if integer (cons integer types) types))))))))

(defund t4-booklogic-arithmetic-validate (n book terms types)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-booklogic-arithmetic-validate")
    (if (endp terms)
        nil
      (let ((integer (t4-booklogic-library t4-ordinals-ordinals-type-of (car terms) types)))
        (if (failure-p integer)
            integer
          (t4-booklogic-arithmetic-validate (1- n) book (cdr terms) types))))))

(defund t4-booklogic-some-call-p (terms head)
  (and (consp terms)
       (or (proof-is-call (car terms) head)
           (t4-booklogic-some-call-p (cdr terms) head))))

(defund t4-booklogic-arithmetic-equation (book formula evidence)
  (if (not (and (proof-is-call formula *proof-equal*)
                (or (t4-booklogic-some-call-p (cdr formula) *proof-plus*)
                    (t4-booklogic-some-call-p (cdr formula) *proof-minus*))))
      (t4-booklogic-return nil)
    (t4-booklogic-bind arithmetic (t4-booklogic-arithmetic-result book evidence)
      (t4-booklogic-check ((vars (t4-booklogic-free-variables formula)))
        (t4-booklogic-bind types (t4-booklogic-arithmetic-types 1000000 book vars evidence nil)
          (let ((value
                 (proof-with-checked-results
                     ((checked (t4-booklogic-arithmetic-validate 1000000 book (cdr formula) types))
                      (sides (proof-list-of-length (cdr formula) 2)))
                   (if checked checked
                     (t4-booklogic-library library-library-linear-equal
                                           (car sides) (cadr sides) types)))))
            (t4-booklogic-return
             (if (t4-booklogic-search-miss-p value) nil value))))))))

(defund t4-booklogic-premise-add (book premise)
  (proof-with-checked-results ((literal (proof-step-first premise)))
    (if (and (proof-is-call literal *proof-if*)
             (equal (cadddr literal) *proof-false*))
        (t4-booklogic-proof proof-proof-conjunct premise)
      nil)))

(defund t4-booklogic-normalize-premise (n book tests pending known visited)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-normalize-premise" book known))
   ((or (endp pending) (>= (len visited) 8)) (list nil book known))
   (t
    (let ((premise (car pending))
          (evidence known))
      (t4-booklogic-check ((literal (proof-step-first premise)))
        (cond
         ((equal literal *proof-false*) (t4-booklogic-return premise))
         ((equal literal (proof-neg *proof-true*))
          (t4-booklogic-check ((value (t4-booklogic-proof proof-proof-prove *proof-true* nil nil)))
            (t4-booklogic-return (t4-booklogic-proof proof-proof-cut value premise))))
         ((member-equal literal visited)
          (t4-booklogic-normalize-premise (1- n) book tests (cdr pending) known visited))
         (t
          (t4-booklogic-check ((context (t4-booklogic-fresh-evidence book tests known)))
            (t4-booklogic-try reduction
                (t4-booklogic-normalize 1000000 book literal context nil
                                        (t4-booklogic-booklogic-chaining book))
              (let ((evidence known))
                (t4-booklogic-check
                    ((reduction reduction)
                     (right (and reduction (t4-booklogic-step-at reduction 2)))
                     (changed (and reduction (not (equal right literal))))
                     (premise (if changed
                                  (proof-with-checked-results
                                      ((rewritten (t4-booklogic-proof proof-proof-rewrite
                                                                       premise reduction '(1))))
                                    (t4-booklogic-proof proof-proof-tidy rewritten))
                                premise)))
                  (let* ((known (if changed (append known (list premise)) known))
                         (evidence known))
                    (t4-booklogic-check ((value (proof-step-first premise)))
                      (cond
                       ((and changed (equal value *proof-false*)) (t4-booklogic-return premise))
                       ((not (t4-booklogic-booklogic-chaining book)) (t4-booklogic-return nil))
                       (t
                        (t4-booklogic-check
                            ((parts (t4-booklogic-premise-add book premise))
                             (literals (t4-booklogic-step-map known nil)))
                          (t4-booklogic-normalize-premise
                           (1- n) book tests (append (cdr pending) parts)
                           (if (assoc-equal value literals) known (append known (list premise)))
                           (cons literal visited))))))))))))))))))

(defund t4-booklogic-solve-premises (n book tests earlier known)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-solve-premises" book known)
    (if (endp tests)
        (list nil book known)
      (let* ((test (caar tests))
             (sign (cadar tests))
             (evidence known))
        (if (not (proof-compound test))
            (t4-booklogic-solve-premises (1- n) book (cdr tests) (cons (car tests) earlier) known)
          (t4-booklogic-check ((step (t4-booklogic-proof proof-proof-assume test sign)))
            (t4-booklogic-bind contradiction
                (t4-booklogic-normalize-premise
                 1000000 book (append (reverse earlier) (cdr tests)) (list step) known nil)
              (if contradiction
                  (t4-booklogic-return contradiction)
                (t4-booklogic-solve-premises (1- n) book (cdr tests) (cons (car tests) earlier)
                                             evidence)))))))))

(defund t4-booklogic-solve-contradictions (n book tests evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-solve-contradictions" book evidence)
    (if (endp tests)
        (t4-booklogic-return nil)
      (let ((literal (caar tests))
            (positive (cadar tests)))
        (t4-booklogic-bind contradiction
            (t4-booklogic-find book evidence (if positive (proof-neg literal) literal))
          (if (not contradiction)
              (t4-booklogic-solve-contradictions (1- n) book (cdr tests) evidence)
            (t4-booklogic-check ((hypothesis (t4-booklogic-proof proof-proof-assume literal positive)))
              (t4-booklogic-return
               (if positive
                   (t4-booklogic-proof proof-proof-cut hypothesis contradiction)
                 (t4-booklogic-proof proof-proof-cut contradiction hypothesis))))))))))

(defund t4-booklogic-solve-fact (book formula evidence)
  (t4-booklogic-bind known (t4-booklogic-known 1000000 book formula evidence)
    (if known (t4-booklogic-return known)
      (t4-booklogic-fact-proof 1000000 book formula evidence))))

(defund t4-booklogic-solve-subsumed (book formula contradiction)
  (t4-booklogic-proof proof-proof-subsume contradiction
                      (cons formula (proof-step-clause contradiction))))

(defund t4-booklogic-solve-transport (book result normalized)
  (if normalized (t4-booklogic-proof proof-proof-transport result normalized) result))

(defund t4-booklogic-solve-test-seen-p (test tests)
  (and (consp tests)
       (or (equal test (caar tests))
           (t4-booklogic-solve-test-seen-p test (cdr tests)))))

(mutual-recursion
 (defund t4-booklogic-solve (n book formula tests extra depth)
   (declare (xargs :measure (nfix n)))
   (let ((evidence nil))
     (if (not (o< (nfix (1- n)) (nfix n)))
         (t4-booklogic-fuel "t4-booklogic-solve" book evidence)
       (t4-booklogic-bind limit (t4-booklogic-limit-context book evidence)
         (t4-booklogic-check ((evidence (t4-booklogic-fresh-evidence book tests extra)))
           (t4-booklogic-bind proved (t4-booklogic-solve-fact book formula evidence)
             (cond
              (proved (t4-booklogic-return proved))
              ((>= depth 7) (t4-booklogic-return '(:failure "search-miss" "")))
              ((proof-is-call formula *library-implies*)
               (t4-booklogic-check ((parts (proof-list-of-length (cdr formula) 2)))
                 (let ((antecedent (car parts)))
                   (t4-booklogic-bind answer
                       (t4-booklogic-solve (1- n) book (cadr parts)
                                           (append tests (list (list antecedent t))) extra (1+ depth))
                     (t4-booklogic-return
                      (t4-booklogic-library t4-ordinals-ordinals-imply antecedent answer))))))
              ((and (t4-booklogic-booklogic-chaining book) (proof-is-call formula *proof-if*)
                    (equal (cadddr formula) *proof-false*))
               (t4-booklogic-bind left
                   (t4-booklogic-solve (1- n) book (cadr formula) tests extra (1+ depth))
                 (t4-booklogic-bind right
                     (t4-booklogic-solve (1- n) book (caddr formula) tests extra (1+ depth))
                   (t4-booklogic-prove 1000000 book formula (list left right) nil evidence))))
              (t
               (t4-booklogic-try immediate
                   (t4-booklogic-count-comparison 1000000 book formula evidence)
                 (if (and immediate (not (t4-booklogic-search-miss-p immediate)))
                     (t4-booklogic-return immediate)
                   (t4-booklogic-solve-under-tests (1- n) book formula tests extra depth)))))))))))

 (defund t4-booklogic-solve-under-tests (n book formula tests extra depth)
   (declare (xargs :measure (nfix n)))
   (let ((evidence nil))
     (if (not (o< (nfix (1- n)) (nfix n)))
         (t4-booklogic-fuel "t4-booklogic-solve-under-tests" book evidence)
       (t4-booklogic-bind contradiction (t4-booklogic-solve-premises 1000000 book tests nil extra)
         (if contradiction
             (t4-booklogic-return (t4-booklogic-solve-subsumed book formula contradiction))
           (t4-booklogic-check ((evidence (t4-booklogic-fresh-evidence book tests evidence)))
             (t4-booklogic-bind found (t4-booklogic-find book evidence formula)
               (t4-booklogic-bind known
                   (if (t4-booklogic-booklogic-enhanced book)
                       (let ((answer (t4-booklogic-booklogic-consequences book evidence)))
                         (if (failure-p answer)
                             (t4-booklogic-return answer)
                           (let ((book (cadr answer)))
                             (t4-booklogic-check
                                 ((evidence (t4-booklogic-fresh-evidence book tests (car answer))))
                               (t4-booklogic-return nil)))))
                     (t4-booklogic-return nil))
                 (t4-booklogic-bind contradiction
                     (t4-booklogic-solve-contradictions 1000000 book tests evidence)
                   (if contradiction
                       (t4-booklogic-return (t4-booklogic-solve-subsumed book formula contradiction))
                     (t4-booklogic-bind normalized
                         (t4-booklogic-normalize 1000000 book formula evidence nil nil)
                       (t4-booklogic-check
                           ((goal (if normalized (t4-booklogic-step-at normalized 2) formula)))
                         (t4-booklogic-solve-normalized
                          (1- n) book goal normalized evidence tests extra depth)))))))))))))

 (defund t4-booklogic-solve-normalized (n book goal normalized evidence tests extra depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-solve-normalized" book evidence)
     (t4-booklogic-bind result (t4-booklogic-solve-fact book goal evidence)
       (t4-booklogic-bind result
           (if result (t4-booklogic-return result)
             (t4-booklogic-arithmetic-equation book goal evidence))
         (if result
             (t4-booklogic-return (t4-booklogic-solve-transport book result normalized))
           (let ((normalized-evidence evidence))
             (t4-booklogic-try congruent
                 (t4-booklogic-congruence (1- n) book goal tests extra depth)
               (let ((evidence normalized-evidence))
                 (t4-booklogic-check
                     ((result (if (t4-booklogic-search-miss-p congruent) nil
                                congruent)))
                   (if result
                       (t4-booklogic-return (t4-booklogic-solve-transport book result normalized))
                     (t4-booklogic-try comparison
                         (t4-booklogic-count-comparison 1000000 book goal evidence)
                       (t4-booklogic-check
                           ((result (if (t4-booklogic-search-miss-p comparison) nil
                                      comparison)))
                         (if result
                             (t4-booklogic-return
                              (t4-booklogic-solve-transport book result normalized))
                           (t4-booklogic-solve-branches
                            (1- n) book goal normalized tests extra depth))))))))))))))

 (defund t4-booklogic-solve-branches (n book goal normalized tests extra depth)
   (declare (xargs :measure (nfix n)))
   (let ((evidence nil))
     (if (not (o< (nfix (1- n)) (nfix n)))
         (t4-booklogic-fuel "t4-booklogic-solve-branches" book evidence)
       (t4-booklogic-check ((test (t4-booklogic-booklogic-branch-test book goal)))
         (if (or (not test) (t4-booklogic-solve-test-seen-p test tests))
             (t4-booklogic-return '(:failure "search-miss" ""))
           (t4-booklogic-bind yes
               (t4-booklogic-solve (1- n) book goal (append tests (list (list test t)))
                                   extra (1+ depth))
             (t4-booklogic-bind no
                 (t4-booklogic-solve (1- n) book goal (append tests (list (list test nil)))
                                     extra (1+ depth))
               (t4-booklogic-check ((result (t4-booklogic-proof proof-proof-cases test yes no)))
                 (t4-booklogic-return (t4-booklogic-solve-transport book result normalized))))))))))

 (defund t4-booklogic-congruence (n book formula tests extra depth)
   (declare (xargs :measure (nfix n)))
   (let ((evidence nil))
     (if (not (o< (nfix (1- n)) (nfix n)))
         (t4-booklogic-fuel "t4-booklogic-congruence" book evidence)
       (if (not (proof-is-call formula *proof-equal*))
           (t4-booklogic-return nil)
         (t4-booklogic-check ((sides (proof-list-of-length (cdr formula) 2)))
           (let ((left (car sides))
                 (right (cadr sides)))
             (if (not (and (proof-compound left) (proof-compound right)))
                 (t4-booklogic-return nil)
               (t4-booklogic-check ((head (proof-term-at left 0)))
                 (if (equal head *proof-quote*)
                     (t4-booklogic-return nil)
                   (t4-booklogic-check ((other (proof-term-at right 0)))
                     (if (or (not (equal head other)) (not (equal (len left) (len right))))
                         (t4-booklogic-return nil)
                       (t4-booklogic-check ((same (t4-booklogic-proof proof-proof-reflexive left)))
                         (t4-booklogic-congruence-arguments
                          (1- n) book (cdr left) (cdr right) tests extra depth 1 same)))))))))))))

 (defund t4-booklogic-congruence-arguments (n book left right tests extra depth index equality)
   (declare (xargs :measure (nfix n)))
   (let ((evidence nil))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-congruence-arguments" book evidence))
      ((endp left) (t4-booklogic-return (t4-booklogic-proof proof-proof-tidy equality)))
      ((equal (car left) (car right))
       (t4-booklogic-congruence-arguments
        (1- n) book (cdr left) (cdr right) tests extra depth (1+ index) equality))
      (t
       (t4-booklogic-bind proved
           (t4-booklogic-solve (1- n) book (proof-eq (car left) (car right)) tests extra (1+ depth))
         (t4-booklogic-check
             ((rewritten (t4-booklogic-proof proof-proof-rewrite equality proved (list 1 2 index))))
           (t4-booklogic-congruence-arguments
            (1- n) book (cdr left) (cdr right) tests extra depth (1+ index) rewritten)))))))
 )

(defun t4-booklogic-booklogic-solve-with-book (book formula tests extra depth)
  (let ((result (t4-booklogic-solve 1000000 book formula tests extra depth)))
    (cons (car result) (cadr result))))

(defund t4-booklogic-binding-table (bindings table)
  (if (endp bindings)
      table
    (t4-booklogic-binding-table (cdr bindings)
                                (table-put table (caar bindings) (cadar bindings)))))

(defund t4-booklogic-induction-hypotheses (n book formula obj selectors countdown bindings)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-booklogic-induction-hypotheses")
    (if (endp selectors)
        (list nil nil)
      (let* ((selector (car selectors))
             (smaller (if countdown (list *proof-plus* *proof-neg-one* obj)
                        (list selector obj)))
             (mapping (if (eq bindings :none) (list (list obj smaller)) bindings))
             (number (cond (countdown 9) ((equal selector *library-car*) 2) (t 3))))
        (proof-with-checked-results
            ((decrease (t4-booklogic-library library-library-builtin number obj))
             (literal (proof-step-first decrease))
             (instance (proof-subst formula (t4-booklogic-binding-table mapping nil)))
             (condition (proof-ite literal instance *proof-true*))
             (assumed (t4-booklogic-proof proof-proof-assume condition t))
             (hypothesis (t4-booklogic-proof proof-proof-prove-if assumed decrease))
             (tail (t4-booklogic-induction-hypotheses (1- n) book formula obj (cdr selectors)
                                                    countdown bindings)))
          (list (cons hypothesis (car tail)) (cons mapping (cadr tail))))))))

(defund t4-booklogic-induction (book formula obj selectors countdown bindings)
  (let* ((test (list (if countdown *t4-booklogic-zp* *proof-consp*) obj))
         (shrinking (not countdown))
         (measure (list *library-count* obj))
         (book (t4-booklogic-booklogic-with-remaining book 2100)))
    (t4-booklogic-bind base
        (t4-booklogic-solve 1000000 book formula (list (list test (not shrinking))) nil 0)
      (t4-booklogic-check
          ((hypotheses (t4-booklogic-induction-hypotheses 1000000
                        book formula obj selectors countdown bindings)))
        (t4-booklogic-bind case-step
            (t4-booklogic-solve 1000000 book formula (list (list test shrinking))
                                (car hypotheses) 0)
          (t4-booklogic-check
              ((cases (if shrinking
                          (t4-booklogic-proof proof-proof-cases test case-step base)
                        (t4-booklogic-proof proof-proof-cases test base case-step)))
               (ordinal (t4-booklogic-library library-library-builtin 1 obj)))
            (t4-booklogic-return
             (t4-booklogic-proof proof-proof-induct ordinal cases formula
                                   measure (cadr hypotheses)))))))))

(defund t4-booklogic-variable-arguments-p (args)
  (or (endp args)
      (and (not (proof-compound (car args)))
           (t4-booklogic-variable-arguments-p (cdr args)))))

(defund t4-booklogic-call-changes (formals actuals args changes)
  (if (or (endp formals) (endp actuals) (endp args))
      changes
    (let ((formal (car formals))
          (actual (car actuals))
          (arg (car args)))
      (proof-with-checked-results
          ((value (cond
                   ((equal actual formal) arg)
                   ((proof-is-call actual *library-cdr*)
                    (proof-with-checked-results ((base (proof-term-at actual 1)))
                      (if (equal base formal) (list *library-cdr* arg) :none)))
                   (t :none))))
        (let ((old (assoc-equal arg changes)))
          (if (or (eq value :none) (and old (not (equal (cdr old) value))))
              :none
            (t4-booklogic-call-changes (cdr formals) (cdr actuals) (cdr args)
                                       (if old changes (table-put changes arg value)))))))))

(defund t4-booklogic-changed-bindings (changes)
  (cond ((endp changes) nil)
        ((equal (caar changes) (cdar changes))
         (t4-booklogic-changed-bindings (cdr changes)))
        (t (cons (list (caar changes) (cdar changes))
                 (t4-booklogic-changed-bindings (cdr changes))))))

(defund t4-booklogic-synchronized-calls (calls formals args)
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((changes (t4-booklogic-call-changes formals
                                            (termination-call-actuals (car calls)) args nil))
         (changed (and (not (eq changes :none)) (t4-booklogic-changed-bindings changes)))
         (rest (t4-booklogic-synchronized-calls (cdr calls) formals args)))
      (if (> (len changed) 1) (cons changed rest) rest))))

(defund t4-booklogic-synchronized-head (book name args)
  (if (not (and (member-equal name (t4-booklogic-booklogic-recursive book))
                (t4-booklogic-variable-arguments-p args)))
      nil
    (let ((definition (assoc-equal name (t4-booklogic-definitions book))))
      (if (not definition)
          '(:failure "missing-proof-input" "")
        (proof-with-checked-results
            ((fields (proof-list-of-length (cdr definition) 2))
             (calls (termination-recursive-calls *termination-all* (list definition))))
          (t4-booklogic-synchronized-calls calls (car fields) args))))))

(mutual-recursion
 (defun t4-booklogic-booklogic-synchronized-selectors (book formula)
   (declare (xargs :measure (acl2-count formula)))
   (cond ((not (proof-compound formula)) nil)
         ((proof-is-call formula *proof-quote*) nil)
         ((endp formula) '(:failure "search-miss" ""))
         (t (proof-with-checked-results
                ((here (t4-booklogic-synchronized-head book (car formula) (cdr formula)))
                 (rest (t4-booklogic-synchronized-arguments book (cdr formula))))
              (append here rest)))))
 (defund t4-booklogic-synchronized-arguments (book args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (t4-booklogic-booklogic-synchronized-selectors book (car args)))
          (rest (t4-booklogic-synchronized-arguments book (cdr args))))
       (append first rest)))))

(defund t4-booklogic-variables-in (args)
  (cond ((endp args) nil)
        ((proof-compound (car args)) (t4-booklogic-variables-in (cdr args)))
        (t (cons (car args) (t4-booklogic-variables-in (cdr args))))))

(mutual-recursion
 (defun t4-booklogic-booklogic-induction-variables (book term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) nil)
    ((endp term) *t4-booklogic-term-shape-failure*)
    ((proof-is-call term *proof-quote*) nil)
    (t
     (proof-with-checked-results
         ((rest (t4-booklogic-induction-arguments book (cdr term))))
       (if (member-equal (car term) (t4-booklogic-booklogic-recursive book))
           (append (t4-booklogic-variables-in (cdr term)) rest)
         rest)))))
 (defund t4-booklogic-induction-arguments (book args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (t4-booklogic-booklogic-induction-variables book (car args)))
          (rest (t4-booklogic-induction-arguments book (cdr args))))
       (append first rest)))))

(defund t4-booklogic-mutual-goals (head obj names)
  (if (endp names)
      nil
    (cons (list head (list (car names) obj))
          (t4-booklogic-mutual-goals head obj (cdr names)))))

(defund t4-booklogic-mutual-joint (goals)
  (cond ((endp goals) *t4-booklogic-term-shape-failure*)
        ((endp (cdr goals)) (car goals))
        (t (proof-ite (car goals) (t4-booklogic-mutual-joint (cdr goals)) *proof-false*))))

(defund t4-booklogic-mutual-select (n book formula goals proof-step)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-booklogic-mutual-select")
    (if (endp (cdr goals))
        proof-step
      (proof-with-checked-results
          ((parts (t4-booklogic-proof proof-proof-conjunct proof-step)))
        (if (equal (car goals) formula)
            (car parts)
          (t4-booklogic-mutual-select (1- n) book formula (cdr goals) (cadr parts)))))))

(defund t4-booklogic-mutual-result (book formula)
  (let* ((evidence nil)
         (call (cadr formula))
         (group (assoc-equal (car call) (t4-booklogic-booklogic-mutual book))))
    (if (not (and (proof-compound formula) (equal (len formula) 2)
                  (proof-compound call) (equal (len call) 2)
                  (not (proof-compound (cadr call))) group))
        (t4-booklogic-return nil)
      (let* ((obj (cadr call))
             (goals (t4-booklogic-mutual-goals (car formula) obj (cdr group))))
        (t4-booklogic-check ((joint (t4-booklogic-mutual-joint goals)))
          (t4-booklogic-bind step
              (t4-booklogic-induction book joint obj (list *library-car* *library-cdr*) nil :none)
            (t4-booklogic-return (t4-booklogic-mutual-select 1000000 book formula goals step))))))))

(defund t4-booklogic-boolean-true (n book step)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-booklogic-boolean-true")
    (proof-with-checked-results ((formula (proof-step-first step)))
      (cond
       ((proof-is-call formula *proof-equal*)
        (proof-with-checked-results
            ((right (proof-term-at formula 2))
             (same (t4-booklogic-proof proof-proof-fact "equal-same"
                                       (list (list *library-x* right))))
             (symmetric (t4-booklogic-proof proof-proof-symmetric step)))
          (t4-booklogic-proof proof-proof-rewrite same symmetric '(1 1 1))))
       ((proof-is-call formula *proof-if*)
        (proof-with-checked-results ((otherwise-branch (proof-term-at formula 3)))
          (if (not (equal otherwise-branch *proof-false*))
              '(:failure "search-miss" "")
            (proof-with-checked-results
                ((parts (t4-booklogic-proof proof-proof-conjunct step))
                 (selected (t4-booklogic-proof proof-proof-select formula (car parts)))
                 (tail (t4-booklogic-boolean-true (1- n) book (cadr parts))))
              (t4-booklogic-proof proof-proof-chain selected (list tail))))))
       (t '(:failure "search-miss" ""))))))

(defund t4-booklogic-constructor-fields (term)
  (declare (xargs :measure (acl2-count term)))
  (if (not (proof-is-call term *proof-if*))
      (list term)
    (proof-with-checked-results ((otherwise-branch (proof-term-at term 3)))
      (if (and (consp (cdr term)) (consp (cddr term))
               (equal otherwise-branch *proof-false*))
          (proof-with-checked-results ((tail (t4-booklogic-constructor-fields (caddr term))))
            (cons (cadr term) tail))
        (list term)))))

(defund t4-booklogic-constructor-projections (fields values obj)
  (if (endp fields)
      nil
    (let ((field (car fields)))
      (if (not (proof-is-call field *proof-equal*))
          :none
        (proof-with-checked-results ((right (proof-term-at field 2))
                                    (left (proof-term-at field 1)))
          (if (not (and (equal right (car values)) (proof-compound left)
                        (equal (len left) 2) (equal (cadr left) obj)))
              :none
            (proof-with-checked-results
                ((rest (t4-booklogic-constructor-projections (cdr fields) (cdr values) obj)))
              (if (eq rest :none) :none (cons (car left) rest)))))))))

(defund t4-booklogic-selector-terms (heads obj)
  (if (endp heads)
      nil
    (cons (list (car heads) obj) (t4-booklogic-selector-terms (cdr heads) obj))))

(defund t4-booklogic-constructor-from-left (n book heads values constructed assumed evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-constructor-from-left" book evidence)
    (if (endp heads)
        (t4-booklogic-return nil)
      (let ((goal (proof-eq (list (car heads) constructed) (car values))))
        (t4-booklogic-bind selector (t4-booklogic-fact-proof 1000000 book goal evidence)
          (if (not selector)
              (t4-booklogic-return :none)
            (t4-booklogic-check
                ((symmetric (t4-booklogic-proof proof-proof-symmetric assumed))
                 (instance (t4-booklogic-proof proof-proof-rewrite selector symmetric '(1 1 1))))
              (t4-booklogic-bind tail
                  (t4-booklogic-constructor-from-left (1- n) book (cdr heads) (cdr values) constructed
                                                     assumed evidence)
                (t4-booklogic-return (if (eq tail :none) :none (cons instance tail)))))))))))

(defund t4-booklogic-constructor-from-right (n book fields assumed step index)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-booklogic-constructor-from-right")
    (if (endp fields)
        step
      (proof-with-checked-results
          ((parts (if (endp (cdr fields)) (list assumed nil)
                    (t4-booklogic-proof proof-proof-conjunct assumed)))
           (rewrite (t4-booklogic-proof proof-proof-rewrite step (car parts) (list 1 1 index))))
        (t4-booklogic-constructor-from-right (1- n) book (cdr fields) (cadr parts) rewrite (1+ index))))))

(defund t4-booklogic-constructor-finish (book guard left right yes fields reconstruction)
  (proof-with-checked-results
      ((right-holds (t4-booklogic-proof proof-proof-assume right t))
       (reconstruction (t4-booklogic-constructor-from-right 1000000 book fields right-holds
                                                          reconstruction 1))
       (left-false (t4-booklogic-proof proof-proof-assume left nil))
       (symmetric (t4-booklogic-proof proof-proof-symmetric reconstruction))
       (cut (t4-booklogic-proof proof-proof-cut symmetric left-false))
       (right-false (t4-booklogic-proof proof-proof-front cut (proof-neg right)))
       (left-nil (t4-booklogic-denied-equation book left left-false))
       (right-nil (t4-booklogic-denied-equation book right right-false))
       (right-nil (t4-booklogic-proof proof-proof-symmetric right-nil))
       (no (t4-booklogic-proof proof-proof-chain left-nil (list right-nil)))
       (result (t4-booklogic-proof proof-proof-cases left yes no)))
    (if guard (t4-booklogic-library t4-ordinals-ordinals-imply guard result) result)))

(defund t4-booklogic-constructor-prove (book guard left right fields heads obj constructed)
  (let ((evidence nil)
        (original (cons (car constructed) (t4-booklogic-selector-terms heads obj))))
    (t4-booklogic-check
        ((evidence (t4-booklogic-fresh-evidence book (and guard (list (list guard t))) nil)))
      (t4-booklogic-bind reconstruction
          (t4-booklogic-fact-proof 1000000 book (proof-eq original obj) evidence)
        (if (not reconstruction)
            (t4-booklogic-return nil)
          (t4-booklogic-check ((left-holds (t4-booklogic-proof proof-proof-assume left t)))
            (t4-booklogic-bind from-left
                (t4-booklogic-constructor-from-left 1000000 book heads (cdr constructed)
                                                   constructed left-holds evidence)
              (if (eq from-left :none)
                  (t4-booklogic-return nil)
                (t4-booklogic-bind right-true
                    (t4-booklogic-prove 1000000 book right from-left nil evidence)
                  (t4-booklogic-check
                      ((left-value (t4-booklogic-boolean-true 1000000 book left-holds))
                       (right-value (t4-booklogic-boolean-true 1000000 book right-true))
                       (right-value (t4-booklogic-proof proof-proof-symmetric right-value))
                       (yes (t4-booklogic-proof proof-proof-chain left-value (list right-value))))
                    (t4-booklogic-return
                     (t4-booklogic-constructor-finish book guard left right yes fields
                                                     reconstruction))))))))))))

(defund t4-booklogic-constructor-equality (book formula)
  (let ((evidence nil))
    (t4-booklogic-check
        ((guard (and (proof-is-call formula *library-implies*) (proof-term-at formula 1)))
         (claim (if guard (proof-term-at formula 2) formula))
         (left (and (proof-is-call claim *proof-equal*) (proof-term-at claim 1))))
      (if (not (proof-is-call left *proof-equal*))
          (t4-booklogic-return nil)
        (t4-booklogic-check
            ((sides (proof-list-of-length (cdr claim) 2))
             (parts (proof-list-of-length (cdr left) 2)))
          (let ((obj (car parts))
                (constructed (cadr parts))
                (right (cadr sides)))
            (if (not (proof-compound constructed))
                (t4-booklogic-return nil)
              (t4-booklogic-check ((head (proof-term-at constructed 0)))
                (if (equal head *proof-quote*)
                    (t4-booklogic-return nil)
                  (t4-booklogic-check ((fields (t4-booklogic-constructor-fields right)))
                    (if (not (equal (len fields) (len (cdr constructed))))
                        (t4-booklogic-return nil)
                      (t4-booklogic-check
                          ((projections (t4-booklogic-constructor-projections
                                         fields (cdr constructed) obj)))
                        (if (eq projections :none)
                            (t4-booklogic-return nil)
                          (t4-booklogic-constructor-prove
                           book guard left right fields projections obj constructed))))))))))))))

(defund t4-booklogic-reconstruct-branches (book guard call obj shape source product body)
  (let ((evidence nil))
    (t4-booklogic-check
        ((assumed (t4-booklogic-proof proof-proof-assume guard t))
         (property (t4-booklogic-proof proof-proof-rewrite assumed source '(1)))
         (yes-cons (t4-booklogic-proof proof-proof-assume shape t))
         (no-cons (t4-booklogic-proof proof-proof-assume shape nil))
         (found (t4-booklogic-proof proof-proof-prove-if property yes-cons))
         (pieces (t4-booklogic-proof proof-proof-conjunct found))
         (selected (t4-booklogic-proof proof-proof-select body (car pieces)))
         (axiom (t4-booklogic-library library-library-axiom "CAR-CDR-ELIM" (list obj)))
         (yes-eq (t4-booklogic-proof proof-proof-modus-ponens axiom yes-cons))
         (yes (t4-booklogic-proof proof-proof-chain product (list selected yes-eq)))
         (obj-false (t4-booklogic-proof proof-proof-prove-if property no-cons))
         (obj-nil (t4-booklogic-denied-equation book obj obj-false))
         (evidence (t4-booklogic-fresh-evidence book (list (list shape nil))
                                                (list obj-false obj-nil))))
      (t4-booklogic-bind no (t4-booklogic-normalize 1000000 book call evidence nil nil)
        (t4-booklogic-check ((right (and no (t4-booklogic-step-at no 2))))
          (if (not (equal right *proof-false*))
              (t4-booklogic-return nil)
            (t4-booklogic-check
                ((symmetric (t4-booklogic-proof proof-proof-symmetric obj-nil))
                 (no (t4-booklogic-proof proof-proof-chain no (list symmetric)))
                 (cases (t4-booklogic-proof proof-proof-cases shape yes no)))
              (t4-booklogic-return
               (t4-booklogic-library t4-ordinals-ordinals-imply guard cases)))))))))

(defund t4-booklogic-reconstruct-definitions (book guard call obj)
  (let ((evidence nil))
    (t4-booklogic-check
        ((source (t4-booklogic-proof proof-proof-unfold guard))
         (product (t4-booklogic-proof proof-proof-unfold call))
         (pattern (t4-booklogic-step-at source 2))
         (body (t4-booklogic-step-at product 2))
         (shape (list *proof-consp* obj)))
      (if (not (proof-is-call pattern *proof-if*))
          (t4-booklogic-return nil)
        (t4-booklogic-check ((test (proof-term-at pattern 1)))
          (if (not (equal test shape))
              (t4-booklogic-return nil)
            (t4-booklogic-check ((atom-case (proof-term-at pattern 3))
                                 (pair-case (proof-term-at pattern 2)))
              (if (not (and (equal atom-case (proof-neg obj))
                            (proof-is-call pair-case *proof-if*)
                            (equal (cddr pair-case) (list *proof-true* *proof-false*))))
                  (t4-booklogic-return nil)
                (let ((item (list *proof-cons* (list *library-car* obj) (list *library-cdr* obj))))
                  (if (equal body (proof-ite (cadr pair-case) item *proof-false*))
                      (t4-booklogic-reconstruct-branches book guard call obj shape source product body)
                    (t4-booklogic-return nil)))))))))))

(defund t4-booklogic-reconstruct-pair (book formula)
  (let ((evidence nil))
    (t4-booklogic-check
        ((claim (and (proof-is-call formula *library-implies*) (proof-term-at formula 2))))
      (if (not (proof-is-call claim *proof-equal*))
          (t4-booklogic-return nil)
        (t4-booklogic-check
            ((parts (proof-list-of-length (cdr formula) 2))
             (sides (proof-list-of-length (cdr claim) 2)))
          (let ((guard (car parts))
                (call (car sides))
                (obj (cadr sides)))
            (if (not (proof-compound guard))
                (t4-booklogic-return nil)
              (t4-booklogic-check ((guard-head (proof-term-at guard 0)))
                (if (not (and (assoc-equal guard-head (t4-booklogic-definitions book))
                              (proof-compound call)))
                    (t4-booklogic-return nil)
                  (t4-booklogic-check ((head (proof-term-at call 0)))
                    (if (and (assoc-equal head (t4-booklogic-definitions book))
                             (equal (cdr call) (list (list *library-car* obj)
                                                     (list *library-cdr* obj))))
                        (t4-booklogic-reconstruct-definitions book guard call obj)
                      (t4-booklogic-return nil))))))))))))

(defund t4-booklogic-nonempty-argument-result (book premise argument impossible)
  (proof-with-checked-results
      ((assumed (t4-booklogic-proof proof-proof-assume premise t))
       (contradiction (t4-booklogic-proof proof-proof-cut assumed impossible))
       (clause (cons argument (remove-equal argument (proof-step-clause contradiction))))
       (result (t4-booklogic-proof proof-proof-subsume contradiction clause)))
    (t4-booklogic-library t4-ordinals-ordinals-imply premise result)))

(defund t4-booklogic-nonempty-argument-contradiction (book substituted)
  (let ((evidence nil))
    (t4-booklogic-check
        ((value (t4-booklogic-step-at substituted 2))
         (evidence (t4-booklogic-fresh-evidence book nil nil)))
      (t4-booklogic-bind reduced (t4-booklogic-normalize 1000000 book value evidence nil nil)
        (t4-booklogic-check ((right (and reduced (t4-booklogic-step-at reduced 2))))
          (if (equal right *proof-false*)
              (t4-booklogic-check
                  ((not-nil (t4-booklogic-proof proof-proof-not-nil))
                   (chain (t4-booklogic-proof proof-proof-chain substituted (list reduced)))
                   (symmetric (t4-booklogic-proof proof-proof-symmetric chain)))
                (t4-booklogic-return (t4-booklogic-proof proof-proof-rewrite
                                                       not-nil symmetric '(1 1))))
            (t4-booklogic-bind solved (t4-booklogic-solve 1000000 book (proof-neg value) nil nil 0)
              (t4-booklogic-check ((symmetric (t4-booklogic-proof proof-proof-symmetric substituted)))
                (t4-booklogic-return (t4-booklogic-proof proof-proof-rewrite
                                                       solved symmetric '(1 1)))))))))))

(defund t4-booklogic-nonempty-argument (book formula)
  (let ((evidence nil))
    (if (not (proof-is-call formula *library-implies*))
        (t4-booklogic-return nil)
      (t4-booklogic-check ((parts (proof-list-of-length (cdr formula) 2)))
        (let ((premise (car parts))
              (argument (cadr parts)))
          (if (proof-compound argument)
              (t4-booklogic-return nil)
            (t4-booklogic-check ((vars (t4-booklogic-free-variables premise)))
              (if (not (member-equal argument vars))
                  (t4-booklogic-return nil)
                (t4-booklogic-check
                    ((possible (t4-booklogic-proof proof-proof-nil-or-true argument))
                     (positive (t4-booklogic-proof proof-proof-front possible argument))
                     (negative (t4-booklogic-proof proof-proof-assume argument nil))
                     (is-nil (t4-booklogic-proof proof-proof-cut positive negative))
                     (reflexive (t4-booklogic-proof proof-proof-reflexive premise))
                     (substituted (t4-booklogic-proof proof-proof-rewrite-result reflexive is-nil
                                                      (proof-eq *proof-true* premise) argument)))
                  (t4-booklogic-bind impossible
                      (t4-booklogic-nonempty-argument-contradiction book substituted)
                    (t4-booklogic-return
                     (t4-booklogic-nonempty-argument-result book premise argument impossible))))))))))))

(defund t4-booklogic-implies-cons (book formula)
  (let ((evidence nil))
    (t4-booklogic-check
        ((pair (and (proof-is-call formula *library-implies*) (proof-term-at formula 2))))
      (if (not (proof-is-call pair *proof-consp*))
          (t4-booklogic-return nil)
        (t4-booklogic-check
            ((parts (proof-list-of-length (cdr formula) 2))
             (premise (car parts))
             (evidence (t4-booklogic-fresh-evidence book (list (list pair nil)) nil)))
          (t4-booklogic-bind reduced (t4-booklogic-normalize 1000000 book premise evidence nil nil)
            (t4-booklogic-check ((right (and reduced (t4-booklogic-step-at reduced 2))))
              (if (not (equal right *proof-false*))
                  (t4-booklogic-return nil)
                (t4-booklogic-check
                    ((assumed (t4-booklogic-proof proof-proof-assume premise t))
                     (rewritten (t4-booklogic-proof proof-proof-rewrite assumed reduced '(1)))
                     (contradiction (t4-booklogic-proof proof-proof-tidy rewritten))
                     (claim (cons pair (remove-equal pair (proof-step-clause contradiction))))
                     (step (t4-booklogic-proof proof-proof-subsume contradiction claim)))
                  (t4-booklogic-return
                   (t4-booklogic-library t4-ordinals-ordinals-imply premise step)))))))))))

(defun t4-booklogic-test-steps (n book tests)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-booklogic-test-steps"))
   ((endp tests) nil)
   (t (proof-with-checked-results
          ((parts (proof-list-of-length (car tests) 2))
           (first (t4-booklogic-proof proof-proof-assume (car parts) (cadr parts)))
           (rest (t4-booklogic-test-steps (1- n) book (cdr tests))))
        (cons first rest)))))

(mutual-recursion
 (defund t4-booklogic-nonempty-result-visit (n value tests opened book limit)
   (declare (xargs :measure (nfix n)))
   (let ((evidence limit))
     (cond
      ((not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-nonempty-result-visit" book limit))
      ((<= limit 0) (t4-booklogic-return '(:failure "search-miss" "")))
      (t
       (let ((limit (1- limit)))
         (t4-booklogic-check ((evidence (t4-booklogic-fresh-evidence book tests nil)))
           (t4-booklogic-bind known (t4-booklogic-known 1000000 book value evidence)
             (cond
              (known (list known book limit))
              ((proof-is-call value *proof-if*)
               (t4-booklogic-nonempty-result-if (1- n) book value tests opened evidence limit))
              ((proof-compound value)
               (t4-booklogic-check ((head (proof-term-at value 0)))
                 (if (and (assoc-equal head (t4-booklogic-definitions book))
                          (not (member-equal head opened)))
                     (t4-booklogic-check
                         ((equation (t4-booklogic-proof proof-proof-unfold value))
                          (right (t4-booklogic-step-at equation 2)))
                       (t4-booklogic-bind result
                           (t4-booklogic-nonempty-result-visit
                            (1- n) right tests (append opened (list head)) book limit)
                         (t4-booklogic-return
                          (t4-booklogic-proof proof-proof-transport result equation))))
                   (let ((result (t4-booklogic-solve 1000000 book value tests nil 0)))
                     (list (car result) (cadr result) limit)))))
              (t
               (let ((result (t4-booklogic-solve 1000000 book value tests nil 0)))
                 (list (car result) (cadr result) limit)))))))))))

 (defund t4-booklogic-nonempty-result-if (n book value tests opened evidence limit)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (t4-booklogic-fuel "t4-booklogic-nonempty-result-if" book limit)
     (t4-booklogic-check
         ((test (proof-term-at value 1))
          (premises (t4-booklogic-test-steps 1000000 book tests))
          (definitions (list *proof-not* (proof-cl "NULL") (proof-cl "ENDP") (proof-cl "ATOM"))))
       (t4-booklogic-bind reduction
           (t4-booklogic-simplify 1000000 book test premises definitions evidence)
         (t4-booklogic-check
             ((opened-if (and reduction
                              (t4-booklogic-rewrite-reflexive book value nil reduction '(1 2 1))))
              (branch (if opened-if (t4-booklogic-step-at opened-if 2) value))
              (test (proof-term-at branch 1)))
           (t4-booklogic-bind decision
               (if (equal test *proof-false*)
                   (t4-booklogic-return (t4-booklogic-proof proof-proof-not-nil))
                 (t4-booklogic-known-or-denied book test evidence))
             (let ((evidence limit))
               (t4-booklogic-bind result
                   (if decision
                       (t4-booklogic-check
                           ((equation (t4-booklogic-proof proof-proof-select branch decision))
                            (right (t4-booklogic-step-at equation 2)))
                         (t4-booklogic-bind result
                             (t4-booklogic-nonempty-result-visit
                              (1- n) right tests opened book limit)
                           (t4-booklogic-return
                            (t4-booklogic-proof proof-proof-transport result equation))))
                     (t4-booklogic-bind yes
                         (t4-booklogic-nonempty-result-branch
                          (1- n) book branch test t tests opened limit)
                       (t4-booklogic-bind no
                           (t4-booklogic-nonempty-result-branch
                            (1- n) book branch test nil tests opened evidence)
                         (t4-booklogic-return (t4-booklogic-proof proof-proof-cases test yes no)))))
                 (t4-booklogic-return (t4-booklogic-solve-transport book result opened-if))))))))))

 (defund t4-booklogic-nonempty-result-branch (n book branch test sign tests opened limit)
   (declare (xargs :measure (nfix n)))
   (let ((evidence limit))
     (if (not (o< (nfix (1- n)) (nfix n)))
         (t4-booklogic-fuel "t4-booklogic-nonempty-result-branch" book limit)
       (t4-booklogic-check ((value (proof-term-at branch (if sign 2 3))))
         (t4-booklogic-bind result
             (t4-booklogic-nonempty-result-visit
              (1- n) value (append tests (list (list test sign))) opened book limit)
           (t4-booklogic-check
               ((selected (if sign
                              (t4-booklogic-proof proof-proof-if-true branch)
                            (t4-booklogic-proof proof-proof-if-false branch))))
             (t4-booklogic-return (t4-booklogic-proof proof-proof-transport result selected))))))))
 )

(defund t4-booklogic-nonempty-result (book formula)
  (let ((evidence nil))
    (if (not (proof-is-call formula *library-implies*))
        (t4-booklogic-return nil)
      (t4-booklogic-check ((parts (proof-list-of-length (cdr formula) 2)))
        (let ((guard (car parts))
              (goal (cadr parts)))
          (if (not (proof-compound goal))
              (t4-booklogic-return nil)
            (t4-booklogic-check ((head (proof-term-at goal 0)))
              (let ((definition (assoc-equal head (t4-booklogic-definitions book))))
                (if (not definition)
                    (t4-booklogic-return nil)
                  (t4-booklogic-check
                      ((constructor (t4-booklogic-has-constructor-result (caddr definition))))
                    (if (not constructor)
                        (t4-booklogic-return nil)
                      (t4-booklogic-bind result
                          (t4-booklogic-nonempty-result-visit
                           1000000 goal (list (list guard t)) nil book 36)
                        (t4-booklogic-return
                         (t4-booklogic-library t4-ordinals-ordinals-imply guard result))))))))))))))

(defconst *t4-booklogic-theorem-tactics*
  '(:strict-order
    :list-equivalence :equivalence-conjunction :character-results
    :tree-order-equivalence :strict-tree-order
    :nonempty-argument :implies-cons :nonempty-result
    :list-projection-invariant :guarded-result-type :recognizer-implication
    :list-result-invariant
    :recursive-transformer :projection-transformer :evaluation-fold
    :list-typing :binding-evaluation :substitution-evaluation
    :evaluated-clause-map :evaluated-clause-result
    :put-membership :duplicate-membership :substitution-map :hash-set-operation
    :scalar-result :tree-constructor :typed-list-transform :projected-list-type
    :reordered-recognizer :optional-recognizer :list-selector-type :append-type
    :arithmetic-identity :arithmetic-test :field-identity
    :product-sign-theorem :scaled-comparison :divided-comparison
    :record-preservation :record-read :record-sufficiency :record-update-law))

(defund t4-booklogic-tactic-recipe (recipe book lib formula replies)
  (let* ((recursive (t4-booklogic-booklogic-recursive book))
         (rules (t4-booklogic-booklogic-evaluators book))
         (functions (t4-evaluation-evaluation-rules-functions rules))
         (reapplications (t4-evaluation-evaluation-rules-reapplications rules)))
    (case recipe
      (:strict-order (t4-order-strict-order lib formula replies))
      ((:list-equivalence :equivalence-conjunction)
       (t4-relations-query recipe lib formula replies))
      (:tree-order-equivalence
       (t4-treeorder-tree-order-equivalence lib formula recursive replies))
      (:strict-tree-order (t4-treeorder-strict-tree-order lib formula recursive replies))
      ((:list-projection-invariant :guarded-result-type :list-result-invariant :result-property)
       (t4-results-query recipe lib formula recursive replies))
      (:recursive-transformer (t4-mvmeta-recursive-transformer-with-replies lib formula replies))
      (:projection-transformer (t4-mvmeta-projection-transformer-with-replies lib formula replies))
      (:evaluation-fold (t4-evaluation-evaluation-fold lib formula rules replies))
      (:list-typing (t4-syntax-lists-list-typing lib formula recursive replies))
      (:binding-evaluation (t4-syntax-lists-binding-evaluation lib formula functions replies))
      (:substitution-evaluation
       (t4-syntax-lists-substitution-evaluation lib formula functions reapplications replies))
      (:evaluated-clause-map
       (t4-syntax-lists-evaluated-clause-map lib formula recursive functions replies))
      (:evaluated-clause-result
       (t4-syntax-lists-evaluated-clause-result lib formula reapplications replies))
      ((:put-membership :duplicate-membership :substitution-map :hash-set-operation)
       (t4-hash-lists-query recipe lib formula recursive replies))
      (:scalar-result (t4-constructors-scalar-result-with-library lib formula replies))
      (:tree-constructor (t4-constructors-tree-constructor-with-library lib formula replies))
      ((:typed-list-transform :projected-list-type :list-selector-type :append-type)
       (t4-list-types-query-with-library recipe lib (list formula recursive) replies))
      (:reordered-recognizer
       (t4-constructors-reordered-recognizer-with-library lib formula replies))
      (:optional-recognizer
       (t4-constructors-optional-recognizer-with-library lib formula recursive replies))
      (:arithmetic-identity (t4-algebra-arithmetic-identity-with-replies lib formula replies))
      (:arithmetic-test (t4-algebra-arithmetic-test-with-replies lib formula replies))
      (:field-identity (t4-field-field-identity-with-replies lib formula replies))
      (:product-sign-theorem (t4-ordered-product-sign-theorem-with-replies lib formula replies))
      (:scaled-comparison (t4-ordered-scaled-comparison-with-replies lib formula replies))
      (:divided-comparison (t4-ordered-divided-comparison-with-replies lib formula replies))
      (:record-preservation (t4-records-record-preservation-with-replies lib formula replies))
      (:record-read (t4-records-record-read-with-replies lib formula replies))
      (:record-sufficiency (t4-record-laws-record-sufficiency-with-library lib formula replies))
      (:record-update-law (t4-record-laws-record-update-law-with-library lib formula replies))
      (otherwise '(:failure "search-miss" "")))))

(defund t4-booklogic-recipe-request (recipe result)
  (cond
   ((t4-order-request-p result)
    (list :order (t4-order-request-operation result) (t4-order-request-arguments result)
          (t4-order-request-library result) result))
   ((t4-treeorder-request-p result)
    (list :treeorder (t4-treeorder-request-method result) (t4-treeorder-request-args result)
          (t4-treeorder-request-lib result) result))
   ((t4-evaluation-request-p result)
    (list :evaluation (t4-evaluation-request-operation result)
          (t4-evaluation-request-arguments result) (t4-evaluation-request-library result) result))
   ((eq (car result) :t4-request)
    (list :ordered (cadr result) (caddr result) (cadddr result) result))
   ((and (consp (car result)) (eq (caar result) :call))
    (let ((request (car result)))
      (cond
       ((member-eq recipe '(:list-typing :binding-evaluation :substitution-evaluation
                            :evaluated-clause-map :evaluated-clause-result))
        (list :syntax (cadr request) (caddr request) (cdr result) request))
       ((member-eq recipe '(:recursive-transformer :projection-transformer))
        (list :mvmeta (cadr request) (cdddr request) (caddr request) request))
       (t (list :keyed (cadr request) (cdddr request) (caddr request) request)))))
   (t nil)))

(defund t4-booklogic-tactic-fact (book mode term supplied)
  (let ((evidence supplied))
    (if (member-eq mode '(:order :treeorder :evaluation :syntax))
        (t4-booklogic-check ((evidence (t4-booklogic-fresh-evidence book nil supplied)))
          (t4-booklogic-fact-proof 1000000 book term evidence))
      (t4-booklogic-fact-proof 1000000 book term evidence))))

(defund t4-booklogic-tactic-evaluation (book term tests extra)
  (let ((evidence nil))
    (t4-booklogic-check ((evidence (t4-booklogic-fresh-evidence book tests extra)))
      (t4-booklogic-evaluator-equation book term evidence))))

(defund t4-booklogic-recognizer-replay (n book lib formula replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-recognizer-replay" book nil)
    (let ((result (t4-recognizers-recognizer-implication-with-replies
                   lib formula (t4-booklogic-booklogic-recursive book) replies)))
      (if (not (eq (car result) :t4-request))
          (t4-booklogic-library-result result book nil)
        (let* ((args (caddr result))
               (book (t4-booklogic-booklogic-with-library book (cadddr result))))
          (t4-booklogic-bind proof-step
              (t4-booklogic-prove 1000000 book (car args) (cadr args) (caddr args) nil)
            (let ((reply (cons proof-step (t4-booklogic-booklogic-library book))))
              (t4-booklogic-recognizer-replay
               (1- n) book lib formula (append replies (list reply))))))))))

(defund t4-booklogic-recognizer-implication (book formula)
  (t4-booklogic-recognizer-replay 1000000 book (t4-booklogic-booklogic-library book) formula nil))

(defund t4-booklogic-tactic-reply (book mode operation args)
  (let ((evidence nil)
        (first (car args))
        (second (cadr args))
        (third (caddr args)))
    (case operation
      ((:use-arithmetic :arithmetic) (t4-booklogic-arithmetic-result book nil))
      (:known (t4-booklogic-known 1000000 book first second))
      (:find (t4-booklogic-find book second first))
      (:fact-proof (t4-booklogic-tactic-fact book mode first second))
      (:fact-proof-evidence (t4-booklogic-fact-proof 1000000 book first second))
      (:equation (t4-booklogic-equation 1000000 book first second))
      (:constant
       (t4-booklogic-book-result (t4-booklogic-booklogic-constant book first) book nil))
      (:prove (t4-booklogic-prove 1000000 book first second third nil))
      (:simplify (t4-booklogic-simplify 1000000 book first second third nil))
      (:solve (t4-booklogic-solve 1000000 book first second third (cadddr args)))
      (:evaluate (t4-booklogic-evaluator-equation book first second))
      (:evaluation (t4-booklogic-tactic-evaluation book first second nil))
      (:evaluator-equation (t4-booklogic-tactic-evaluation book first nil second))
      (:evaluator-reapply (t4-booklogic-evaluator-reapply book args))
      (:match (t4-booklogic-return (t4-booklogic-match first second nil)))
      (:boolean-true (t4-booklogic-return (t4-booklogic-boolean-true 1000000 book first)))
      (:recognizer-implication (t4-booklogic-recognizer-implication book first))
      (otherwise (t4-booklogic-return '(:failure "search-miss" ""))))))

(defund t4-booklogic-paired-failure-p (recipe)
  (member-eq recipe '(:scalar-result :tree-constructor :reordered-recognizer
                      :optional-recognizer :record-sufficiency :record-update-law
                      :typed-list-transform :projected-list-type :list-selector-type :append-type
                      :put-membership :duplicate-membership :substitution-map :hash-set-operation)))

(defund t4-booklogic-tactic-reply-form (recipe mode operation response)
  (let* ((value (car response))
         (lib (t4-booklogic-booklogic-library (cadr response)))
         (evidence (caddr response)))
    (cond
     ((eq mode :keyed) (cons value lib))
     ((eq mode :mvmeta)
      (cons (if (and (not (failure-p value)) (member-eq operation '(:known :evaluate)))
                (list value evidence)
              value)
            lib))
     ((failure-p value)
      (if (or (eq mode :syntax) (t4-booklogic-paired-failure-p recipe))
          (cons value lib)
        value))
     ((and (eq mode :order) (eq operation :match)) value)
     ((eq mode :evaluation)
      (case operation
        (:use-arithmetic lib)
        ((:known :find) (cons value (cons lib evidence)))
        (otherwise (cons value lib))))
     ((and (eq mode :ordered) (member-eq operation '(:known :fact-proof :equation)))
      (cons (cons value evidence) lib))
     (t (cons value lib)))))

(defund t4-booklogic-tactic-replay (n recipe book original-lib formula replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (t4-booklogic-fuel "t4-booklogic-tactic-replay" book nil)
    (let* ((result (t4-booklogic-tactic-recipe recipe book original-lib formula replies))
           (request (t4-booklogic-recipe-request recipe result)))
      (if (not request)
          (t4-booklogic-library-result result book nil)
        (let* ((mode (car request))
               (operation (cadr request))
               (args (caddr request))
               (book (t4-booklogic-booklogic-with-library book (cadddr request)))
               (response (t4-booklogic-tactic-reply book mode operation args))
               (reply (t4-booklogic-tactic-reply-form recipe mode operation response))
               (replies (if (member-eq mode '(:keyed :mvmeta))
                            (table-put replies (nth 4 request) reply)
                          (append replies (list reply)))))
          (t4-booklogic-tactic-replay (1- n) recipe (cadr response) original-lib formula replies))))))

(defund t4-booklogic-character-results (book formula)
  (let ((evidence nil)
        (mutual (t4-booklogic-booklogic-mutual book)))
    (t4-booklogic-check
        ((build (and (not (t4-booklogic-booklogic-arithmetic book))
                     (t4-booklogic-library t4-printing-character-results-arithmetic-needed-p
                                           formula mutual))))
      (t4-booklogic-bind arithmetic
          (if build (t4-booklogic-arithmetic-result book nil) (t4-booklogic-return nil))
        (t4-booklogic-library-result
         (t4-booklogic-library t4-printing-character-results
                               formula mutual (t4-booklogic-booklogic-arithmetic book)) book nil)))))

(defund t4-booklogic-run-tactic (recipe book formula)
  (case recipe
    (:character-results (t4-booklogic-character-results book formula))
    (:nonempty-argument (t4-booklogic-nonempty-argument book formula))
    (:implies-cons (t4-booklogic-implies-cons book formula))
    (:nonempty-result (t4-booklogic-nonempty-result book formula))
    (:recognizer-implication (t4-booklogic-recognizer-implication book formula))
    (otherwise
     (t4-booklogic-tactic-replay 1000000 recipe book
                                (t4-booklogic-booklogic-library book) formula nil))))

(defund t4-booklogic-search-failure-p (value recursion)
  (and (failure-p value)
       (or (member-equal (cadr value) '("search-miss" "inference-mismatch" "value" "assertion"))
           (and recursion (equal (cadr value) "recursion")))))

(defund t4-booklogic-solver-trial (book formula)
  (t4-booklogic-bind step (t4-booklogic-solve 1000000 book formula nil nil 0)
    (t4-booklogic-return (t4-booklogic-proof proof-proof-subsume step (list formula)))))

(defund t4-booklogic-theorem-solver-attempts (n book formula enabled attempts)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-theorem-solver-attempts" book nil))
   ((endp attempts) (list nil book nil))
   (t
    (let* ((enhanced (caar attempts))
           (book (t4-booklogic-booklogic-with-enhanced book enhanced))
           (book (t4-booklogic-booklogic-with-enabled book (and enhanced (proof-unique enabled))))
           (book (t4-booklogic-booklogic-with-remaining book (cadar attempts))))
      (t4-booklogic-try step (t4-booklogic-solver-trial book formula)
        (if (t4-booklogic-search-failure-p step nil)
            (t4-booklogic-theorem-solver-attempts (1- n) book formula enabled (cdr attempts))
          (t4-booklogic-return step)))))))

(defund t4-booklogic-theorem-opening (book goal)
  (proof-with-checked-results
      ((head (and (proof-compound goal) (proof-term-at goal 0))))
    (cond
     ((and (proof-compound goal) (proof-compound head))
      (t4-booklogic-proof proof-proof-beta goal))
     ((proof-is-call goal *library-implies*)
      (proof-with-checked-results ((claim (proof-term-at goal 2)))
        (if (not (proof-compound claim))
            nil
          (proof-with-checked-results ((head (proof-term-at claim 0)))
            (and (proof-compound head)
                 (proof-with-checked-results
                     ((reflexive (t4-booklogic-proof proof-proof-reflexive goal))
                      (beta (t4-booklogic-proof proof-proof-beta claim)))
                   (t4-booklogic-proof proof-proof-rewrite reflexive beta '(1 2 2))))))))
     (t nil))))

(defund t4-booklogic-theorem-tactic-attempts (n book formula goal opening tactics)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-theorem-tactic-attempts" book nil))
   ((endp tactics) (list nil book nil))
   (t
    (t4-booklogic-try step (t4-booklogic-run-tactic (car tactics) book goal)
      (let ((value
             (if (or (not step) (failure-p step))
                 step
               (proof-with-checked-results
                   ((result (if opening (t4-booklogic-proof proof-proof-transport step opening)
                              step)))
                 (t4-booklogic-proof proof-proof-subsume result (list formula))))))
        (if (or (not value) (t4-booklogic-search-failure-p value nil))
            (t4-booklogic-theorem-tactic-attempts (1- n) book formula goal opening (cdr tactics))
          (t4-booklogic-return value)))))))

(defund t4-booklogic-theorem-reconstruct (book formula)
  (t4-booklogic-bind constructed (t4-booklogic-constructor-equality book formula)
    (t4-booklogic-bind answer
        (if constructed (t4-booklogic-return constructed)
          (t4-booklogic-reconstruct-pair book formula))
      (t4-booklogic-return
       (and answer (t4-booklogic-proof proof-proof-subsume answer (list formula)))))))

(defund t4-booklogic-combined-bindings (groups)
  (if (endp groups)
      nil
    (append (car groups) (t4-booklogic-combined-bindings (cdr groups)))))

(defund t4-booklogic-induct-on-group (n book formula bindings objects)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-induct-on-group" book nil))
   ((or (endp objects) (<= (t4-booklogic-booklogic-total-remaining book) 0))
    (list nil book nil))
   (t
    (t4-booklogic-try result
        (t4-booklogic-induction book formula (caar objects) (list *library-cdr*) nil bindings)
      (if (t4-booklogic-search-failure-p result t)
          (t4-booklogic-induct-on-group (1- n) book formula bindings (cdr objects))
        (t4-booklogic-return result))))))

(defund t4-booklogic-induct-on-groups (n book formula groups)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (t4-booklogic-fuel "t4-booklogic-induct-on-groups" book nil))
   ((endp groups) (list nil book nil))
   (t
    (t4-booklogic-bind result
        (t4-booklogic-induct-on-group 1000000 book formula (car groups) (seq-slice (car groups) 0 2))
      (if result (t4-booklogic-return result)
        (t4-booklogic-induct-on-groups (1- n) book formula (cdr groups)))))))

(defund t4-booklogic-induct-synchronized (book formula)
  (let ((evidence nil))
    (t4-booklogic-check ((groups (t4-booklogic-booklogic-synchronized-selectors book formula)))
      (if (endp groups)
          (t4-booklogic-return nil)
        (let* ((groups (proof-unique groups))
               (combined (proof-unique (t4-booklogic-combined-bindings groups)))
               (work (proof-unique (cons combined groups)))
               (book (t4-booklogic-booklogic-with-chaining book t)))
          (t4-booklogic-try result (t4-booklogic-induct-on-groups 1000000 book formula work)
            (list result (t4-booklogic-booklogic-with-chaining book nil) nil)))))))

(defund t4-booklogic-countdown-formula-p (formula names)
  (if (endp names)
      nil
    (or (t4-booklogic-calls-function formula (car names))
        (t4-booklogic-countdown-formula-p formula (cdr names)))))

(defund t4-booklogic-induct-with-selectors (n book formula obj choices)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n)))
    (t4-booklogic-fuel "t4-booklogic-induct-with-selectors" book nil))
   ((or (endp choices) (<= (t4-booklogic-booklogic-total-remaining book) 0))
    (list nil book nil))
   (t
    (t4-booklogic-try result (t4-booklogic-induction book formula obj (car choices) nil :none)
      (if (t4-booklogic-search-failure-p result t)
          (t4-booklogic-induct-with-selectors (1- n) book formula obj (cdr choices))
        (t4-booklogic-return result))))))

(defund t4-booklogic-induct-on-variables (n book formula variables countdown)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n)))
    (t4-booklogic-fuel "t4-booklogic-induct-on-variables" book nil))
   ((endp variables) (list nil book nil))
   (t
    (let ((obj (car variables)))
      (t4-booklogic-bind selected
          (t4-booklogic-induct-with-selectors
           1000000 book formula obj (list (list *library-cdr*) (list *library-car* *library-cdr*)))
        (cond
         (selected (t4-booklogic-return selected))
         (countdown
          (t4-booklogic-try result (t4-booklogic-induction book formula obj (list nil) t :none)
            (if (t4-booklogic-search-failure-p result t)
                (t4-booklogic-induct-on-variables (1- n) book formula (cdr variables) countdown)
              (t4-booklogic-return result))))
         (t (t4-booklogic-induct-on-variables (1- n) book formula (cdr variables) countdown))))))))

(defund t4-booklogic-induct-theorem (book formula variables)
  (t4-booklogic-try mutual (t4-booklogic-mutual-result book formula)
    (t4-booklogic-check ((mutual (if (t4-booklogic-search-failure-p mutual t) nil mutual)))
      (if mutual
          (t4-booklogic-return mutual)
        (t4-booklogic-bind synchronized (t4-booklogic-induct-synchronized book formula)
          (if synchronized
              (t4-booklogic-return synchronized)
            (t4-booklogic-check
                ((countdown (t4-booklogic-countdown-formula-p formula *t4-booklogic-countdown*)))
              (t4-booklogic-induct-on-variables 1000000 book formula (seq-slice variables 0 2)
                                                 countdown))))))))

(defund t4-booklogic-theorem-induction (book formula)
  (let ((evidence nil))
    (t4-booklogic-check ((variables (t4-booklogic-booklogic-induction-variables book formula)))
      (if (endp variables)
          (t4-booklogic-return nil)
        (t4-booklogic-check ((size (t4-booklogic-term-size formula)))
          (if (<= size 125)
              (t4-booklogic-induct-theorem book formula (proof-unique variables))
            (t4-booklogic-return nil)))))))

(defund t4-booklogic-proof-budget (book budget)
  (t4-booklogic-booklogic-with-remaining
   (t4-booklogic-booklogic-with-total-remaining book budget) budget))

(defund t4-booklogic-theorem-projected-attempt (book formula)
  (t4-booklogic-bind projected (t4-booklogic-run-tactic :result-property book formula)
    (t4-booklogic-return
     (and projected (t4-booklogic-proof proof-proof-subsume projected (list formula))))))

(defund t4-booklogic-theorem-projected (book formula)
  (let* ((book (t4-booklogic-proof-budget book 900))
         (book (t4-booklogic-booklogic-with-chaining book t))
         (book (t4-booklogic-booklogic-with-project-returns book t)))
    (t4-booklogic-try result (t4-booklogic-theorem-projected-attempt book formula)
      (list (if (t4-booklogic-search-failure-p result t) nil result)
            (t4-booklogic-booklogic-with-chaining
             (t4-booklogic-booklogic-with-project-returns book nil) nil)
            nil))))

(defund t4-booklogic-enable-syntax-head (book term)
  (if (not (proof-compound term))
      book
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (let ((definition (assoc-equal head (t4-booklogic-definitions book))))
        (if (not definition)
            book
          (proof-with-checked-results ((size (t4-booklogic-definition-size book definition)))
            (if (> size 350)
                book
              (t4-booklogic-booklogic-with-enabled
               book (t4-booklogic-adjoin head (t4-booklogic-booklogic-enabled book))))))))))

(defund t4-booklogic-enable-syntax (book terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      (list nil book nil)
    (let ((updated (t4-booklogic-enable-syntax-head book (car terms))))
      (if (failure-p updated)
          (list updated book nil)
        (t4-booklogic-enable-syntax updated (cdr terms))))))

(defund t4-booklogic-theorem-syntax (book formula)
  (let ((evidence nil))
    (t4-booklogic-check
        ((syntax (t4-evaluation-evaluation-rules-syntax-terms
                  (t4-booklogic-booklogic-evaluators book) formula)))
      (if (endp syntax)
          (t4-booklogic-return '(:failure "search-miss" ""))
        (let* ((book (t4-booklogic-booklogic-with-evaluate-syntax book t))
               (book (t4-booklogic-booklogic-with-chaining book t)))
          (t4-booklogic-bind enabled (t4-booklogic-enable-syntax book syntax)
            (let ((book (t4-booklogic-proof-budget book 3800)))
              (t4-booklogic-try solved (t4-booklogic-solver-trial book formula)
                (list (if (t4-booklogic-search-failure-p solved t)
                          '(:failure "search-miss" "")
                        solved)
                      (t4-booklogic-booklogic-with-chaining
                       (t4-booklogic-booklogic-with-evaluate-syntax book nil) nil)
                      nil)))))))))

(defund t4-booklogic-theorem-after-tactics (book formula)
  (t4-booklogic-bind reconstructed (t4-booklogic-theorem-reconstruct book formula)
    (if reconstructed
        (t4-booklogic-return reconstructed)
      (t4-booklogic-bind inductive (t4-booklogic-theorem-induction book formula)
        (if inductive
            (t4-booklogic-return inductive)
          (t4-booklogic-bind projected (t4-booklogic-theorem-projected book formula)
            (if projected (t4-booklogic-return projected)
              (t4-booklogic-theorem-syntax book formula))))))))

(defund t4-booklogic-theorem-after-solver (book formula)
  (let* ((book (t4-booklogic-booklogic-with-remaining book 1000))
         (evidence nil))
    (t4-booklogic-check
        ((opening (t4-booklogic-theorem-opening book formula))
         (goal (if opening (t4-booklogic-step-at opening 2) formula)))
      (t4-booklogic-bind result
          (t4-booklogic-theorem-tactic-attempts
           1000000 book formula goal opening *t4-booklogic-theorem-tactics*)
        (if result (t4-booklogic-return result)
          (t4-booklogic-theorem-after-tactics book formula))))))

(defund t4-booklogic-theorem (book formula enabled)
  (let* ((book (t4-booklogic-booklogic-with-chaining book nil))
         (book (t4-booklogic-booklogic-with-project-returns book nil))
         (book (t4-booklogic-booklogic-with-evaluate-syntax book nil))
         (book (t4-booklogic-booklogic-with-total-remaining book 4000)))
    (t4-booklogic-bind proved
        (t4-booklogic-theorem-solver-attempts 1000000 book formula enabled '((nil 1800) (t 1400)))
      (if proved (t4-booklogic-return proved)
        (t4-booklogic-theorem-after-solver book formula)))))

(defun t4-booklogic-booklogic-theorem-with-book (book formula enabled)
  (let ((result (t4-booklogic-theorem book formula enabled)))
    (cons (car result) (cadr result))))

