(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-equivalence-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(defun h2-equivalence-boolean-case (search test value holds)
  (h2-book-logic-with-results search
      (((boolean search) (h2-book-logic-derive search (list *h2-equivalence-booleanp* value)
                                               "BOOLEANP" nil nil 1 "" nil nil 80))
       (lib (h2-search-search-library search))
       (proof (library-library-proof lib))
       (assumed (proof-proof-assume proof test holds))
       (equality (h2-ordering-equality-value search test assumed))
       (step (library-library-transport-argument lib boolean equality 1)))
    (cons step search)))

(defun h2-equivalence-equality-boolean (search)
  (let* ((lib (h2-search-search-library search))
         (proof (library-library-proof lib))
         (name (proof-sym "SELF-H2-BOOLEANP-OF-EQUAL" "ACL2")))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name search)
      (let ((test (proof-eq *library-x* *library-y*)))
        (h2-book-logic-with-results search
            (((yes search) (h2-equivalence-boolean-case search test *proof-true* t))
             ((no search) (h2-equivalence-boolean-case search test *proof-false* nil))
             (proof (h2-book-logic-proof search))
             (claim (list *h2-equivalence-booleanp* test))
             (step (proof-proof-cases proof test yes no))
             (search (h2-book-logic-add-lemma search "H2-BOOLEANP-OF-EQUAL" claim step nil)))
          (cons name search))))))

(defun h2-equivalence-opening-to-equal (lib term)
  (if (not (proof-compound term))
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results ((head (proof-term-at term 0)))
        (if (not (assoc-equal head (proof-proof-definitions proof)))
            nil
          (proof-with-checked-results
              ((logical (h2-book-logic-logical-equation lib term))
               (value (h2-book-logic-first-at logical 2)))
            (and (proof-is-call value *proof-equal*) logical)))))))

(defun h2-equivalence-laws (term reversed)
  (declare (xargs :measure (acl2-count term)))
  (if (and (consp term) (proof-is-call term *proof-if*))
      (proof-with-checked-results ((otherwise (proof-term-at term 3)))
        (if (equal otherwise *proof-false*)
            (h2-equivalence-laws (caddr term) (cons (cadr term) reversed))
          (cons (reverse reversed) term)))
    (cons (reverse reversed) term)))

(defun h2-equivalence-open-terms (lib terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((first (h2-equivalence-opening-to-equal lib (car terms)))
         (rest (h2-equivalence-open-terms lib (cdr terms))))
      (cons first rest))))

(defun h2-equivalence-equations (steps)
  (if (endp steps)
      nil
    (proof-with-checked-results
        ((first (h2-book-logic-first-at (car steps) 2))
         (rest (h2-equivalence-equations (cdr steps))))
      (cons first rest))))

(defun h2-equivalence-compatible-laws-p (r s1 s2 t1 t2 t3)
  (proof-with-checked-results ((r1 (proof-term-at r 1)) (r2 (proof-term-at r 2)))
    (and (equal r1 r2)
         (proof-with-checked-results
             ((s2-right (proof-term-at s2 2)) (s2-left (proof-term-at s2 1)))
           (and (equal (cdr s1) (list s2-right s2-left))
                (proof-with-checked-results
                    ((t1-right (proof-term-at t1 2)) (t2-left (proof-term-at t2 1)))
                  (and (equal t1-right t2-left)
                       (proof-with-checked-results
                           ((t1-left (proof-term-at t1 1)) (t2-right (proof-term-at t2 2)))
                         (equal (cdr t3) (list t1-left t2-right))))))))))

(defun h2-equivalence-prove-laws (search formula symmetry transitivity premise opened boolean reflexive)
  (h2-book-logic-with-results search
      (((name search) (h2-equivalence-equality-boolean search))
       (lib (h2-search-search-library search))
       (proof (library-library-proof lib))
       (typed (proof-proof-fact proof name (seq-zip (list *library-x* *library-y*) (cdr boolean))))
       (boolean (library-library-transport-argument lib typed (car opened) 1))
       (term (proof-term-at reflexive 1))
       (equal-step (proof-proof-reflexive proof term))
       (refl (proof-proof-transport proof equal-step (cadr opened)))
       (symmetry-test (proof-term-at symmetry 1))
       (assumed (proof-proof-assume proof symmetry-test t))
       (step (proof-proof-rewrite proof assumed (caddr opened) '(1)))
       (swapped (proof-proof-symmetric proof step))
       (consequence (proof-proof-transport proof swapped (cadddr opened)))
       (symm (h2-search-search-introduce search symmetry consequence))
       (assumed (proof-proof-assume proof premise t))
       (arguments (proof-proof-conjunct proof assumed))
       (first (proof-proof-rewrite proof (car arguments) (nth 4 opened) '(1)))
       (second (proof-proof-rewrite proof (cadr arguments) (nth 5 opened) '(1)))
       (chained (proof-proof-chain proof first (list second)))
       (consequence (proof-proof-transport proof chained (nth 6 opened)))
       (trans (h2-search-search-introduce search transitivity consequence))
       (step (proof-proof-prove proof formula (list boolean refl symm trans) nil)))
    (cons step search)))

(defun h2-equivalence-check-laws (search formula symmetry transitivity premise terms)
  (let ((lib (h2-search-search-library search)))
    (h2-book-logic-with-results search ((opened (h2-equivalence-open-terms lib terms)))
      (if (member-equal nil opened)
          (cons nil search)
        (h2-book-logic-with-results search
            ((equations (h2-equivalence-equations opened))
             (equations (proof-list-of-length equations 7))
             (boolean (car equations))
             (reflexive (cadr equations))
             (compatible
              (h2-equivalence-compatible-laws-p reflexive (nth 2 equations) (nth 3 equations)
                                                (nth 4 equations) (nth 5 equations) (nth 6 equations))))
          (if compatible
              (h2-equivalence-prove-laws search formula symmetry transitivity premise
                                         opened boolean reflexive)
            (cons nil search)))))))

(defun h2-equivalence-equality-equivalence (search formula)
  (h2-book-logic-with-results search ((result (h2-equivalence-laws formula nil)))
    (let* ((laws (car result))
           (transitivity (cdr result))
           (boolean (car laws))
           (reflexive (cadr laws))
           (symmetry (caddr laws)))
      (if (and (equal (len laws) 3)
               (proof-is-call boolean *h2-equivalence-booleanp*)
               (proof-is-call symmetry *library-implies*)
               (proof-is-call transitivity *library-implies*))
          (h2-book-logic-with-results search ((premise (proof-term-at transitivity 1)))
            (if (not (proof-is-call premise *proof-if*))
                (cons nil search)
              (h2-book-logic-with-results search ((otherwise (proof-term-at premise 3)))
                (if (not (equal otherwise *proof-false*))
                    (cons nil search)
                  (h2-book-logic-with-results search
                      ((typed (proof-term-at boolean 1))
                       (conclusion (proof-term-at transitivity 2))
                       (terms (append (list typed reflexive) (cdr symmetry)
                                      (list (cadr premise) (caddr premise) conclusion))))
                    (h2-equivalence-check-laws search formula symmetry transitivity premise terms))))))
        (cons nil search)))))

(defun h2-equivalence-changes (left right index)
  (if (or (endp left) (endp right))
      nil
    (let* ((same (equal (car left) (car right)))
           (rest (h2-equivalence-changes (cdr left) (cdr right) (1+ index))))
      (if same rest (cons index rest)))))

(defun h2-equivalence-index-candidates (index target)
  (if (endp index)
      nil
    (proof-with-checked-results
        ((first (h2-search-head (cadr target)))
         (second (h2-search-head (caddr target))))
      (let ((fn (car target)))
        (append (table-get index (list fn first second) nil)
                (and second (table-get index (list fn first nil) nil))
                (and first (table-get index (list fn nil second) nil))
                (and first second (table-get index (list fn nil nil) nil))
                (table-get index (list nil) nil))))))

(defun h2-equivalence-canonical-proof
    (proof formula premise opening index name left-bindings right-bindings)
  (proof-with-checked-results
      ((fact (proof-proof-fact proof name (table-items left-bindings)))
       (first (proof-proof-symmetric proof fact))
       (assumed (proof-proof-assume proof premise t))
       (assumption (proof-proof-rewrite proof assumed opening '(1)))
       (middle (proof-proof-rewrite proof first assumption (list 1 2 index)))
       (last (proof-proof-fact proof name (table-items right-bindings)))
       (step (proof-proof-chain proof middle (list last))))
    (h2-search-search-introduce proof formula step)))

(defun h2-equivalence-canonical-candidates
    (candidates proof formula premise opening index target right-target)
  (if (endp candidates)
      nil
    (proof-with-checked-results ((entry (proof-list-of-length (car candidates) 2)))
      (let* ((name (car entry))
             (pattern (cadr entry))
             (fact (assoc-equal name (proof-proof-facts proof))))
        (if (not fact)
            '(:failure "failure" "")
          (proof-with-checked-results
              ((left-bindings (and (equal (len (cdr fact)) 1) (h2-search-match pattern target nil)))
               (right-bindings (and (car left-bindings) (h2-search-match pattern right-target nil))))
            (if (car right-bindings)
                (h2-equivalence-canonical-proof proof formula premise opening index name
                                                (cdr left-bindings) (cdr right-bindings))
              (h2-equivalence-canonical-candidates (cdr candidates) proof formula premise
                                                   opening index target right-target))))))))

(defun h2-equivalence-canonical-indexes
    (indexes proof formula premise opening index target right-target)
  (if (endp indexes)
      nil
    (proof-with-checked-results
        ((candidates (h2-equivalence-index-candidates (car indexes) target))
         (step (h2-equivalence-canonical-candidates candidates proof formula premise opening
                                                    index target right-target)))
      (or step (h2-equivalence-canonical-indexes (cdr indexes) proof formula premise opening
                                                 index target right-target)))))

(defun h2-equivalence-canonical-fixed (lib formula premise left right index indexes)
  (proof-with-checked-results ((opening (h2-equivalence-opening-to-equal lib premise)))
    (if (not opening)
        nil
      (proof-with-checked-results
          ((body (h2-book-logic-first-at opening 2))
           (fixed (proof-list-of-length (cdr body) 2))
           (left-fixed (append (seq-slice left 0 index) (list (car fixed))
                               (seq-slice left (1+ index) :none)))
           (right-fixed (append (seq-slice right 0 index) (list (cadr fixed))
                                (seq-slice right (1+ index) :none))))
        (h2-equivalence-canonical-indexes indexes (library-library-proof lib) formula premise
                                         opening index (proof-eq left-fixed left)
                                         (proof-eq right-fixed right))))))

(defun h2-equivalence-canonical-changes (lib formula premise left right indexes)
  (if (and (proof-compound left) (proof-compound right) (equal (len left) (len right)))
      (proof-with-checked-results
          ((left-head (proof-term-at left 0)) (right-head (proof-term-at right 0)))
        (if (equal left-head right-head)
            (let* ((changes (h2-equivalence-changes left right 0))
                   (index (car changes)))
              (and (equal (len changes) 1)
                   (equal (list (nth index left) (nth index right)) (cdr premise))
                   (h2-equivalence-canonical-fixed lib formula premise left right index indexes)))
          nil))
    nil))

(defun h2-equivalence-canonical-argument (lib formula book-formulas library-formulas)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((conclusion (proof-term-at formula 2)))
      (if (not (proof-is-call conclusion *proof-equal*))
          nil
        (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
          (let ((premise (car parts)))
            (if (and (proof-compound premise) (equal (len premise) 3))
                (proof-with-checked-results ((args (proof-list-of-length (cdr conclusion) 2)))
                  (h2-equivalence-canonical-changes lib formula premise (car args) (cadr args)
                                                     (list book-formulas library-formulas)))
              nil)))))))
