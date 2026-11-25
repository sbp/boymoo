(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-printing-nthcdr* (proof-cl "NTHCDR"))
(defconst *t3-printing-take* (proof-sym "TAKE" "ACL2"))

(defun t3-printing-size-of (value)
  (list *library-count* value))

(defun t3-printing-nil-count-bound-with-evidence (lib parent evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((zero (t3-trees-folded-count lib *proof-false* evidence))
         (nonnegative (t3-logic-evidence-nonnegative
                       (cdr zero) (t3-printing-size-of parent)))
         (back (proof-proof-symmetric proof (car zero)))
         (rewritten (proof-proof-rewrite proof (car nonnegative) back '(1 1 2)))
         (step (proof-proof-tidy proof rewritten)))
      (cons step (cdr nonnegative)))))

(defun t3-printing-nil-count-bound (lib parent evidence)
  (proof-with-checked-results
      ((bound (t3-printing-nil-count-bound-with-evidence lib parent evidence)))
    (car bound)))

(defun t3-printing-direct-builtin (lib clause evidence)
  (t3-size-direct-builtin lib clause evidence))

(defun t3-printing-index-decrease-with-evidence (lib new old evidence)
  (let ((goal (list *proof-ordinal-less* (t3-printing-size-of new) (t3-printing-size-of old))))
    (proof-with-checked-results ((direct (t3-printing-direct-builtin lib (list goal) evidence)))
      (if (car direct)
          direct
        '(:failure "unsupported" "")))))

(defun t3-printing-by-value-rewrite (lib step equality template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((back (proof-proof-symmetric proof equality)))
      (proof-proof-rewrite-result proof step back template *proof-result*))))

(defun t3-printing-by-value-join (lib value template test yes no)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((true-eq (proof-proof-if-true proof value))
         (yes (t3-printing-by-value-rewrite lib yes true-eq template))
         (false-eq (proof-proof-if-false proof value))
         (no (t3-printing-by-value-rewrite lib no false-eq template)))
      (proof-proof-cases proof test yes no))))

; A pending branch records its return path and the tests at that branch.
(defun t3-printing-by-value-visit (lib value tests substitutions pending)
  (cond
   ((and (proof-compound value) (not (consp value)))
    '(:failure "failure" ""))
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
      (let ((test (car branches)))
        (list :visit lib (cadr branches) (append tests (list (list test t))) substitutions
              (cons (list :if-yes value test (caddr branches) tests) pending)))))
   ((and (proof-compound value)
         (or (member-equal (car value) *t3-logic-wrappers*)
             (proof-compound (car value))))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((equation (if (member-equal (car value) *t3-logic-wrappers*)
                         (proof-proof-unfold proof value)
                       (proof-proof-beta proof value)))
           (opened (proof-rewritten-term equation)))
        (list :visit lib opened tests substitutions (cons (list :rewrite equation) pending)))))
   (t (list :leaf lib value tests substitutions pending))))

(defun t3-printing-by-value-return (lib step substitutions pending template)
  (if (endp pending)
      (list :done (list step lib substitutions))
    (let ((frame (car pending))
          (rest (cdr pending)))
      (case (car frame)
        (:rewrite
         (proof-with-checked-results
             ((step (t3-printing-by-value-rewrite lib step (cadr frame) template)))
           (list :return lib step nil substitutions rest)))
        (:if-yes
         (let ((value (cadr frame))
               (test (caddr frame))
               (no (cadddr frame))
               (tests (nth 4 frame)))
           (list :visit lib no (append tests (list (list test nil))) substitutions
                 (cons (list :if-no value test step) rest))))
        (otherwise
         (proof-with-checked-results
             ((step (t3-printing-by-value-join
                     lib (cadr frame) template (caddr frame) (cadddr frame) step)))
           (list :return lib step nil substitutions rest)))))))

(defun t3-printing-by-value-check-leaf (result value template pending)
  (proof-with-checked-results
      ((result result)
       (literal (proof-step-first (car result)))
       (target (proof-subst template (list (cons *proof-result* value)))))
    (if (equal literal target)
        (list :return (cadr result) (car result) nil (caddr result) pending)
      '(:failure "failure" ""))))

; A leaf function returns its Step, Library and induction substitutions.
(defmacro t3-printing-by-value-next (cursor template leaf)
  `(let ((lib (cadr ,cursor))
          (value (caddr ,cursor))
          (tests (cadddr ,cursor))
          (substitutions (nth 4 ,cursor))
          (pending (nth 5 ,cursor)))
     (case (car ,cursor)
       (:visit (t3-printing-by-value-visit lib value tests substitutions pending))
       (:leaf (t3-printing-by-value-check-leaf ,leaf value ,template pending))
       (otherwise (t3-printing-by-value-return lib value substitutions pending ,template)))))

(defun t3-printing-reflexive-bound (lib term)
  (let ((size (t3-printing-size-of term)))
    (proof-with-checked-results ((typed (t3-logic-libraryproofs-type-of lib size nil)))
      (library-library-cite lib "WEAK-REFLEXIVE" (list size) (list typed)))))

(defun t3-printing-nthcdr-tail-bound-leaf (value tests lib goal substitutions)
  (proof-with-checked-results
      ((evidence (t3-logic-evidence-init lib tests nil nil)))
    (cond
     ((equal value *library-x*)
      (proof-with-checked-results
          ((step (t3-printing-reflexive-bound lib (list *library-cdr* *library-x*))))
        (list step lib substitutions)))
     ((not (proof-is-call value *t3-printing-nthcdr*))
      '(:failure "failure" ""))
     (t
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((actual-x (proof-term-at value 2))
             (actual-y (proof-term-at value 1))
             (order (t3-printing-index-decrease-with-evidence lib actual-y *library-y* evidence))
             (decrease (proof-step-first (car order)))
             (target (proof-subst goal (list (cons *library-x* actual-x)
                                            (cons *library-y* actual-y))))
             (smaller (proof-proof-assume proof (proof-ite decrease target *proof-true*) t))
             (ih (proof-proof-prove-if proof smaller (car order)))
             (tail (t3-size-count-bound lib (list *library-cdr* actual-x)
                                        (list *library-cdr* *library-x*) (cdr order)))
             (step (t3-size-chain lib ih (car tail) nil)))
          (list step lib
                (append substitutions
                        (list (list (list *library-x* actual-x) (list *library-y* actual-y)))))))))))

(defun t3-printing-take-bound-leaf (value tests lib template goal within substitutions)
  (let ((proof (library-library-proof lib))
        (cons-term (list *proof-consp* *library-x*))
        (len-term (list *library-len* *library-x*)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil (list *t3-logic-zp*)))
         (formula (proof-subst template (list (cons *proof-result* value)))))
      (if (equal value *proof-false*)
          (proof-with-checked-results
              ((bound (t3-printing-nil-count-bound lib *library-x* evidence))
               (step (t3-scan-conclusion lib formula bound)))
            (list step lib substitutions))
        (proof-with-checked-results
            ((n-positive (t3-logic-evidence-require evidence (library-lt *proof-zero* *library-y*)))
             (n-type (t3-logic-evidence-integer (cdr n-positive) *library-y*))
             (atom (proof-proof-assume proof cons-term nil))
             (length (t3-logic-libraryproofs-simplify lib len-term (list atom) (list *library-len*)))
             (within-assumed (proof-proof-assume proof within t))
             (cant (proof-proof-rewrite proof within-assumed length '(1 1 1)))
             (impossible (proof-proof-cut proof (car n-positive) cant))
             (actual-cons (proof-proof-front proof impossible cons-term))
             (recurrence (proof-term-at value 2))
             (actuals (proof-list-of-length (cdr recurrence) 2))
             (order (t3-printing-index-decrease-with-evidence
                     lib (car actuals) *library-y* (cdr n-type)))
             (decrease (proof-step-first (car order)))
             (target (proof-subst goal (list (cons *library-x* (cadr actuals))
                                            (cons *library-y* (car actuals)))))
             (smaller (proof-proof-assume proof (proof-ite decrease target *proof-true*) t))
             (ih (proof-proof-prove-if proof smaller (car order)))
             (lengths (proof-proof-unfold proof len-term))
             (length-body (proof-rewritten-term lengths))
             (select (proof-proof-select proof length-body actual-cons))
             (length (proof-proof-chain proof lengths (list select)))
             (within-assumed (proof-proof-assume proof within t))
             (parent-bound (proof-proof-rewrite proof within-assumed length '(1 1 1)))
             (first (proof-rewritten-term length))
             (comparison (library-library-axiom lib "<-ON-OTHERS" (list first *library-y*)))
             (weak (proof-proof-rewrite proof parent-bound comparison '(1 1)))
             (proper (library-library-weak-from-difference
                      lib (car actuals) (list *library-len* (cadr actuals))
                      weak (list (car n-type))))
             (child-bound (proof-proof-prove-if proof ih proper))
             (extended (t3-size-shift lib child-bound
                                      (t3-printing-size-of (list *library-car* *library-x*)) t nil))
             (extended (t3-size-shift lib extended *proof-one* t nil))
             (left (t3-trees-count-cons lib value (cdr order)))
             (right-evidence (t3-logic-evidence-init lib nil (list actual-cons) nil))
             (right (t3-trees-count-cons lib *library-x* right-evidence))
             (left-back (proof-proof-symmetric proof (car left)))
             (extended (proof-proof-rewrite proof extended left-back '(1 1 2)))
             (right-back (proof-proof-symmetric proof (car right)))
             (extended (proof-proof-rewrite proof extended right-back '(1 1 1)))
             (step (t3-scan-conclusion lib formula extended)))
          (list step lib
                (append substitutions
                        (list (list (list *library-x* (cadr actuals))
                                    (list *library-y* (car actuals)))))))))))

(defun t3-printing-taken-head-leaf (value tests lib parent)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (selector (or (t3-logic-libraryproofs-normalize lib (list *library-car* value) nil nil)
                       '(:failure "failure" "")))
         (field (proof-rewritten-term selector))
         (bound (if (equal field *proof-false*)
                    (t3-printing-nil-count-bound-with-evidence lib parent evidence)
                  (t3-size-count-bound lib field parent evidence)))
         (selected (proof-proof-symmetric proof selector))
         (rewritten (proof-proof-rewrite proof (car bound) selected '(1 1 2 1))))
      (proof-proof-tidy proof rewritten))))

(defun t3-printing-printing-count-leaf (value tests lib parent tail)
  (declare (ignore tests))
  (cond
   ((equal value parent) (t3-printing-reflexive-bound lib tail))
   ((not (proof-is-call value *t3-printing-nthcdr*))
    '(:failure "unsupported" ""))
   (t
    (proof-with-checked-results ((source (proof-term-at value 2)))
      (if (not (equal source parent))
          '(:failure "unsupported" "")
        (library-library-cite lib "T3-NTHCDR-TAIL-COUNT" (list parent (cadr value)) nil))))))

(defun t3-printing-prefix-leaf (value tests lib prefix take)
  (if (equal value prefix)
      take
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (bound (t3-size-count-bound lib value prefix evidence)))
      (t3-size-chain lib (car bound) take nil))))

(defun t3-printing-by-value-leaf (lib value template tests context substitutions)
  (case (car context)
    (:nthcdr (t3-printing-nthcdr-tail-bound-leaf value tests lib (cadr context) substitutions))
    (:take (t3-printing-take-bound-leaf
            value tests lib template (cadr context) (caddr context) substitutions))
    (otherwise
     (proof-with-checked-results
         ((step (case (car context)
                  (:head (t3-printing-taken-head-leaf value tests lib (cadr context)))
                  (:suffix (t3-printing-printing-count-leaf value tests lib
                                                           (cadr context) (caddr context)))
                  (otherwise (t3-printing-prefix-leaf value tests lib
                                                     (cadr context) (caddr context))))))
       (list step lib substitutions)))))

(defun t3-printing-by-value-walk (n cursor template context)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "t3-printing-by-value"))
        ((failure-p cursor) cursor)
        ((eq (car cursor) :done) (cadr cursor))
        (t (t3-printing-by-value-walk
            (1- n)
            (t3-printing-by-value-next cursor template
             (t3-printing-by-value-leaf lib value template tests context substitutions))
            template context))))

(defun t3-printing-by-value (n lib value template tests context substitutions)
  (t3-printing-by-value-walk n (list :visit lib value tests substitutions nil) template context))

(defun t3-printing-nthcdr-tail-bound (lib)
  (let* ((proof (library-library-proof lib))
         (form (list *t3-printing-nthcdr* *library-y* *library-x*))
         (tail-size (t3-printing-size-of (list *library-cdr* *library-x*)))
         (goal (library-le (t3-printing-size-of (list *library-cdr* form)) tail-size))
         (template (library-le (t3-printing-size-of (list *library-cdr* *proof-result*))
                               tail-size))
         (measure (t3-printing-size-of *library-y*)))
    (proof-with-checked-results
        ((source (proof-proof-unfold proof form))
         (opened (proof-rewritten-term source))
         (result (t3-printing-by-value 1000000 lib opened template nil (list :nthcdr goal) nil))
         (rewritten (t3-printing-by-value-rewrite lib (car result) source template))
         (ordinal (library-library-builtin lib 1 *library-y*))
         (induction (proof-proof-induct proof ordinal rewritten goal measure (caddr result))))
      (library-library-lemma lib "T3-NTHCDR-TAIL-COUNT" goal induction nil))))

(defun t3-printing-take-bound (lib)
  (let* ((proof (library-library-proof lib))
         (form (list *t3-printing-take* *library-y* *library-x*))
         (measure (t3-printing-size-of *library-y*))
         (within (library-le *library-y* (list *library-len* *library-x*)))
         (template (proof-ite within
                              (library-le (t3-printing-size-of *proof-result*)
                                          (t3-printing-size-of *library-x*))
                              *proof-true*)))
    (proof-with-checked-results
        ((goal (proof-subst template (list (cons *proof-result* form))))
         (opened (proof-proof-unfold proof form))
         (body (proof-rewritten-term opened))
         (result (t3-printing-by-value 1000000 lib body template nil
                                       (list :take goal within) nil))
         (rewritten (t3-printing-by-value-rewrite lib (car result) opened template))
         (ordinal (library-library-builtin lib 1 *library-y*))
         (induction (proof-proof-induct proof ordinal rewritten goal measure (caddr result))))
      (library-library-lemma lib "T3-TAKE-COUNT" goal induction nil))))

(defun t3-printing-zero-index (lib length evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reduced (library-library-axiom lib "<-ON-OTHERS" (list length *proof-false*)))
         (minus (proof-proof-compute proof (list *proof-minus* *proof-false*) 0))
         (reduced (proof-proof-rewrite proof reduced minus '(1 2 1 2)))
         (typed (t3-logic-libraryproofs-type-of lib length nil))
         (add-zero (library-library-cite lib "ADD-ZERO-RIGHT" (list length) (list typed)))
         (reduced (proof-proof-rewrite proof reduced add-zero '(1 2 1)))
         (nonnegative (t3-logic-evidence-nonnegative evidence length)))
      (library-library-transport-argument lib (car nonnegative) reduced 1))))

(defun t3-printing-bounded-index (lib index length tests)
  (declare (xargs :measure (acl2-count index)))
  (let ((target (library-le index length)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (known (t3-logic-evidence-find evidence target)))
      (cond
       ((car known) (car known))
       ((equal index *proof-false*) (t3-printing-zero-index lib length (cdr known)))
       ((not (proof-is-call index *proof-if*))
        '(:failure "unsupported" ""))
       ((and (consp index) (consp (cdr index)) (consp (cddr index))
             (consp (cdddr index)) (endp (cddddr index)))
        (let ((proof (library-library-proof lib))
              (test (cadr index)))
          (proof-with-checked-results
              ((yes (t3-printing-bounded-index lib (caddr index) length
                                               (append tests (list (list test t)))))
               (no (t3-printing-bounded-index lib (cadddr index) length
                                              (append tests (list (list test nil)))))
               (true-eq (proof-proof-if-true proof index))
               (back (proof-proof-symmetric proof true-eq))
               (yes (proof-proof-rewrite proof yes back '(1 1 2)))
               (false-eq (proof-proof-if-false proof index))
               (back (proof-proof-symmetric proof false-eq))
               (no (proof-proof-rewrite proof no back '(1 1 2)))
               (yes (proof-proof-tidy proof yes))
               (no (proof-proof-tidy proof no)))
            (proof-proof-cases proof test yes no))))
       (t (proof-list-of-length (cdr index) 3))))))

(defun t3-printing-taken-head (lib term parent)
  (proof-with-checked-results
      ((opened (proof-proof-unfold (library-library-proof lib) term)))
    (let ((template (library-le (t3-printing-size-of (list *library-car* *proof-result*))
                                (t3-printing-size-of parent))))
      (proof-with-checked-results
          ((body (proof-rewritten-term opened))
           (result (t3-printing-by-value 1000000 lib body template nil (list :head parent) nil)))
        (t3-printing-by-value-rewrite lib (car result) opened template)))))

(defun t3-printing-head-prefix (child tail)
  (and (proof-is-call child *library-car*)
    (proof-with-checked-results ((prefix (proof-term-at child 1)))
      (and (proof-is-call prefix *t3-printing-take*)
        (proof-with-checked-results ((source (proof-term-at prefix 2)))
          (and (equal source tail) prefix))))))

(defun t3-printing-suffix (child)
  (and (proof-is-call child *library-cdr*)
    (proof-with-checked-results ((arg (proof-term-at child 1)))
      (and (proof-is-call arg *proof-if*) arg))))

(defun t3-printing-prefix (child)
  (and (proof-is-call child *proof-if*)
    (proof-with-checked-results ((no (proof-term-at child 3)))
      (and (proof-is-call no *t3-printing-take*)
        (and (equal (caddr child) (list *library-cdr* no)) no)))))

(defun t3-printing-finish-count (lib parent tail weak evidence)
  (proof-with-checked-results
      ((tail-bound (t3-size-count-bound lib tail parent evidence))
       (step (t3-size-chain lib weak (car tail-bound) nil)))
    (cons (list step (cdr tail-bound)) lib)))

(defun t3-printing-printing-count-suffix (lib suffix parent tail evidence)
  (proof-with-checked-results
      ((updated (if (assoc-equal (proof-sym "SELF-T3-NTHCDR-TAIL-COUNT" "ACL2")
                                 (proof-proof-facts (library-library-proof lib)))
                    lib
                  (t3-printing-nthcdr-tail-bound lib)))
       (result (t3-printing-by-value
                1000000 updated suffix
                (library-le (t3-printing-size-of (list *library-cdr* *proof-result*))
                            (t3-printing-size-of tail))
                nil (list :suffix parent tail) nil)))
    (t3-printing-finish-count updated parent tail (car result)
                             (if (equal lib (t3-logic-evidence-lib evidence))
                                 (t3-logic-evidence-with-lib evidence updated)
                               evidence))))

(defun t3-printing-printing-count-prefix (lib child prefix parent tail evidence)
  (proof-with-checked-results
      ((updated (if (assoc-equal (proof-sym "SELF-T3-TAKE-COUNT" "ACL2")
                                 (proof-proof-facts (library-library-proof lib)))
                    lib
                  (t3-printing-take-bound lib)))
       (actuals (proof-list-of-length (cdr prefix) 2)))
    (let ((index (car actuals))
          (source (cadr actuals)))
      (if (not (equal source tail))
          '(:failure "unsupported" "")
        (proof-with-checked-results
            ((within (t3-printing-bounded-index updated index (list *library-len* source) nil))
             (claim (library-library-cite updated "T3-TAKE-COUNT" (list source index) nil))
             (take (proof-proof-prove-if (library-library-proof updated) claim within))
             (result (t3-printing-by-value
                      1000000 updated child
                      (library-le (t3-printing-size-of *proof-result*) (t3-printing-size-of tail))
                      nil (list :prefix prefix take) nil)))
          (t3-printing-finish-count updated parent tail (car result)
                                   (if (equal lib (t3-logic-evidence-lib evidence))
                                       (t3-logic-evidence-with-lib evidence updated)
                                     evidence)))))))

(defun t3-printing-printing-count-with-evidence (lib child parent evidence)
  (let ((tail (list *library-cdr* parent)))
    (proof-with-checked-results ((head-prefix (t3-printing-head-prefix child tail)))
      (if head-prefix
          (proof-with-checked-results ((weak (t3-printing-taken-head lib head-prefix tail)))
            (t3-printing-finish-count lib parent tail weak evidence))
        (proof-with-checked-results ((suffix (t3-printing-suffix child)))
          (if suffix
              (t3-printing-printing-count-suffix lib suffix parent tail evidence)
            (proof-with-checked-results ((prefix (t3-printing-prefix child)))
              (if prefix
                  (t3-printing-printing-count-prefix lib child prefix parent tail evidence)
                '(:failure "unsupported" "")))))))))

