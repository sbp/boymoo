(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-tactics-iff* (proof-sym "IFF" "ACL2"))
(defconst *h4-book-tactics-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h4-book-tactics-logic*
  (append *h4-book-measures-selectors*
          (list *proof-not* *library-implies* *h4-book-tactics-booleanp*
                *h4-book-tactics-iff*)))
(defconst *h4-book-tactics-consp-cons* "consp-cons")
(defconst *h4-book-tactics-cons-equal-variables*
  (list (proof-sym "X1" "ACL2") (proof-sym "Y1" "ACL2")
        (proof-sym "X2" "ACL2") (proof-sym "Y2" "ACL2")))
(defconst *h4-book-tactics-recursive* (list *library-car* *library-cdr*))
(defconst *h4-book-tactics-equal-symmetry* (proof-sym "H4-EQUAL-SYMMETRY" "ACL2"))

(mutual-recursion
 (defun h4-book-tactics-terms (term)
   (declare (xargs :measure (acl2-count term)))
   (if (and (consp term) (proof-compound term) (not (proof-is-call term *proof-quote*)))
       (cons term (h4-book-tactics-argument-terms (cdr term)))
     (list term)))
 (defun h4-book-tactics-argument-terms (arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (append (h4-book-tactics-terms (car arguments))
             (h4-book-tactics-argument-terms (cdr arguments))))))

(mutual-recursion
 (defun h4-book-tactics-count-terms (term remaining)
   (declare (xargs :measure (acl2-count term)))
   (cond ((zp remaining) 0)
         ((and (consp term) (proof-compound term)
               (not (proof-is-call term *proof-quote*)))
          (h4-book-tactics-count-arguments (cdr term) (1- remaining)))
         (t (1- remaining))))
 (defun h4-book-tactics-count-arguments (arguments remaining)
   (declare (xargs :measure (acl2-count arguments)))
   (if (or (endp arguments) (zp remaining))
       remaining
     (h4-book-tactics-count-arguments
      (cdr arguments) (h4-book-tactics-count-terms (car arguments) remaining)))))

(defun h4-book-tactics-size (term limit)
  (cond ((eq limit :none) (len (h4-book-tactics-terms term)))
        ((null limit) 0)
        ((eq limit t) 1)
        ((and (natp limit) (<= limit 9223372036854775807))
         (- limit (h4-book-tactics-count-terms term limit)))
        (t '(:failure "failure" ""))))

(defun h4-book-tactics-smaller (first second)
  (let ((a (h4-book-tactics-size first 150))
        (b (h4-book-tactics-size second 150)))
    (cond ((< a b) t)
          ((and (equal a b) (< a 150))
           (proof-with-checked-results ((left (proof-write first))
                                        (right (proof-write second)))
             (if (string< left right) t nil)))
          (t nil))))

(defun h4-book-tactics-datum-length (datum)
  (cond ((stringp datum) (length datum))
        ((or (consp datum) (null datum)) (len datum))
        (t '(:failure "failure" ""))))

; Each pending datum is counted before its children, from right to left.
(mutual-recursion
 (defun h4-book-tactics-fit-datum (datum budget)
   (declare (xargs :measure (acl2-count datum)))
   (cond ((not (integerp budget)) budget)
         ((<= budget 0) nil)
         ((and (consp datum) (proof-compound datum))
          (h4-book-tactics-fit-datum
           (car datum) (h4-book-tactics-fit-children (cdr datum) (1- budget))))
         ((and (consp datum) (equal (car datum) "dot"))
          (if (consp (cdr datum))
              (h4-book-tactics-fit-datum (cadr datum) (1- budget))
            '(:failure "failure" "")))
         ((and (consp datum) (equal (car datum) "str"))
          (proof-with-checked-results ((payload (proof-term-at datum 1))
                                       (size (h4-book-tactics-datum-length payload)))
            (- (1- budget) (floor size 20))))
         (t (1- budget))))
 (defun h4-book-tactics-fit-children (children budget)
   (declare (xargs :measure (acl2-count children)))
   (cond ((or (endp children) (not (integerp budget))) budget)
         ((<= budget 0) nil)
         (t (h4-book-tactics-fit-datum
             (car children) (h4-book-tactics-fit-children (cdr children) budget))))))

(defund h4-book-tactics-fits (datum budget)
  (let ((budget (cond ((eq budget t) 1) ((null budget) 0) (t budget))))
    (proof-with-checked-results ((remaining (h4-book-tactics-fit-datum datum budget)))
      (and (integerp remaining) (<= 0 remaining)))))

(defun h4-book-tactics-term-key (term)
  (proof-with-checked-results ((length (h4-book-tactics-datum-length term))
                               (head (proof-term-at term 0)))
    (if (and (> length 1) (proof-compound (cadr term)))
        (proof-with-checked-results ((first-head (proof-term-at (cadr term) 0)))
          (list head first-head))
      (list head nil))))

(defun h4-book-tactics-make-rule (source conclusion path local clause)
  (list :h4-book-tactics-rule source conclusion path local clause))

(defun h4-book-tactics-rule-source (rule) (cadr rule))
(defun h4-book-tactics-rule-conclusion (rule) (caddr rule))
(defun h4-book-tactics-rule-path (rule) (cadddr rule))
(defun h4-book-tactics-rule-local (rule) (nth 4 rule))
(defun h4-book-tactics-rule-clause (rule) (nth 5 rule))

(defun h4-book-tactics-rule-view (source formula path local clause)
  (if (not (proof-compound formula))
      nil
    (proof-with-checked-results ((head (proof-term-at formula 0)))
      (and (not (proof-compound head))
           (list (h4-book-tactics-make-rule source formula path local clause))))))

(defun h4-book-tactics-views (source formula path local clause)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((proof-is-call formula *library-implies*)
    (if (consp (cddr formula))
        (h4-book-tactics-views source (caddr formula) (append path '(0)) local clause)
      '(:failure "failure" "")))
   (t
    (proof-with-checked-results
        ((root (h4-book-tactics-rule-view source formula path local clause)))
      (cond
       ((proof-is-call formula *proof-if*)
        (cond ((not (consp (cdddr formula))) '(:failure "failure" ""))
              ((equal (cadddr formula) *proof-false*)
               (proof-with-checked-results
                   ((left (h4-book-tactics-views source (cadr formula)
                                               (append path '(1)) local clause))
                    (right (h4-book-tactics-views source (caddr formula)
                                                (append path '(2)) local clause)))
                 (append root left right)))
              (t root)))
       ((proof-is-call formula *h4-book-tactics-iff*)
        (proof-with-checked-results
            ((right (proof-term-at formula 2))
             (forward (h4-book-tactics-rule-view source right (append path '(3)) local clause))
             (backward (h4-book-tactics-rule-view source (cadr formula)
                                                  (append path '(4)) local clause)))
          (append root forward backward)))
       (t root))))))

(defun h4-book-tactics-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(mutual-recursion
 (defun h4-book-tactics-canonical-comparisons-visit (term position library equality)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
     (cons term equality))
    ((endp term) '(:failure "failure" ""))
    (t
     (proof-with-checked-results
         ((visited (h4-book-tactics-canonical-comparisons-arguments
                    (cdr term) position 1 library equality)))
       (let* ((arguments (car visited))
              (equality (cdr visited))
              (call (cons (car term) arguments))
              (proof (library-library-proof library)))
         (if (not (proof-is-call call *proof-equal*))
             (cons call equality)
           (proof-with-checked-results
               ((right (proof-term-at arguments 1))
                (swap (h4-book-tactics-smaller right (car arguments))))
             (if (not swap)
                 (cons call equality)
               (proof-with-checked-results
                   ((rule (proof-proof-fact proof *h4-book-tactics-equal-symmetry*
                                            (seq-zip (list *library-x* *library-y*) arguments)))
                    (changed (proof-proof-rewrite proof equality rule position))
                    (result (h4-book-tactics-step-right rule)))
                 (cons result changed))))))))))
 (defun h4-book-tactics-canonical-comparisons-arguments
     (arguments position index library equality)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       (cons nil equality)
     (proof-with-checked-results
         ((first (h4-book-tactics-canonical-comparisons-visit
                  (car arguments) (append position (list index)) library equality))
          (rest (h4-book-tactics-canonical-comparisons-arguments
                 (cdr arguments) position (1+ index) library (cdr first))))
       (cons (cons (car first) (car rest)) (cdr rest))))))

(defun h4-book-tactics-canonical-comparisons (library equality)
  (proof-with-checked-results ((value (h4-book-tactics-step-right equality))
                               (fits (h4-book-tactics-fits value 2500)))
    (if (not fits)
        equality
      (proof-with-checked-results
          ((result (h4-book-tactics-canonical-comparisons-visit value '(1 2) library equality)))
        (cdr result)))))

(defun h4-book-tactics-equality-symmetry-same (evidence library reflexive)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((left (proof-proof-rewrite proof reflexive evidence '(1 1 2)))
         (right (proof-proof-rewrite proof reflexive evidence '(1 1 1)))
         (symmetric (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list symmetric)))))

(defun h4-book-tactics-equality-symmetry-distinct (evidence library reverse)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof reverse t))
         (symmetric (proof-proof-symmetric proof assumed))
         (impossible (proof-proof-cut proof symmetric evidence))
         (other (proof-proof-front proof impossible (proof-neg reverse)))
         (left (h4-tactics-tactics-nil-value library evidence))
         (right (h4-tactics-tactics-nil-value library other))
         (backward (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list backward)))))

(defun h4-book-tactics-equality-symmetry-boolean-value (value library predicate)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((identity (proof-proof-reflexive proof predicate))
         (lifted (proof-proof-rewrite proof identity value '(1 2 1)))
         (branch (h4-book-tactics-step-right lifted))
         (reduced (h4-tactics-tactics-normalize library branch nil *h4-book-tactics-logic* nil nil)))
      (proof-proof-chain proof lifted (list reduced)))))

(defun h4-book-tactics-equality-symmetry (library)
  (let* ((proof (library-library-proof library))
         (test (proof-eq *library-x* *library-y*))
         (reverse (proof-eq *library-y* *library-x*)))
    (proof-with-checked-results
        ((reflexive (proof-proof-fact proof "equal-same" nil))
         (assumed (proof-proof-assume proof test t))
         (same (h4-book-tactics-equality-symmetry-same assumed library reflexive))
         (denied (proof-proof-assume proof test nil))
         (distinct (h4-book-tactics-equality-symmetry-distinct denied library reverse))
         (symmetric (h4-tactics-tactics-case-of library (proof-eq test reverse) test same distinct))
         (entry (h4-tactics-tactics-local-lemma library *h4-book-tactics-equal-symmetry* symmetric)))
      (let* ((library (cdr entry))
             (proof (library-library-proof library))
             (predicate (list *h4-book-tactics-booleanp* test)))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof test t))
             (true-value (proof-proof-rewrite proof reflexive assumed '(1 1 2)))
             (yes (h4-book-tactics-equality-symmetry-boolean-value true-value library predicate))
             (denied (proof-proof-assume proof test nil))
             (nil-value (h4-tactics-tactics-nil-value library denied))
             (no (h4-book-tactics-equality-symmetry-boolean-value nil-value library predicate))
             (boolean (h4-tactics-tactics-case-of library (proof-eq predicate *proof-true*) test yes no))
             (entry (h4-tactics-tactics-local-lemma library "BOOLEANP-EQUAL" boolean)))
          (cdr entry))))))

(defun h4-book-tactics-guarded-alias-proof-alias (term library)
  (if (not (proof-compound term))
      nil
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (let* ((proof (library-library-proof library))
             (definition (assoc-equal head (proof-proof-definitions proof)))
             (body (caddr definition)))
        (if (or (proof-compound head) (not definition) (not (proof-compound body)))
            nil
          (proof-with-checked-results ((body-head (proof-term-at body 0)))
            (if (or (proof-compound body-head)
                    (member-equal body-head (list head *proof-if* *proof-quote*)))
                nil
              (proof-with-checked-results ((fits (h4-book-tactics-fits body 80)))
                (and fits (proof-proof-unfold proof term))))))))))

(defun h4-book-tactics-guarded-alias-changes (arguments index library)
  (declare (xargs :measure (acl2-count arguments)))
  (if (endp arguments)
      nil
    (proof-with-checked-results
        ((change (h4-book-tactics-guarded-alias-proof-alias (car arguments) library))
         (rest (h4-book-tactics-guarded-alias-changes (cdr arguments) (1+ index) library)))
      (if change (cons (list index change) rest) rest))))

(defun h4-book-tactics-guarded-alias-outcomes (changes proof goal outcomes)
  (declare (xargs :measure (acl2-count changes)))
  (if (endp changes)
      outcomes
    (proof-with-checked-results
        ((identity (proof-proof-reflexive proof goal))
         (changed (proof-proof-rewrite proof identity (cadar changes) (list 1 2 (caar changes))))
         (value (h4-book-tactics-step-right changed)))
      (h4-book-tactics-guarded-alias-outcomes
       (cdr changes) proof goal (table-put outcomes value changed)))))

(defun h4-book-tactics-guarded-alias-guards (guards pattern name outcomes library formula)
  (declare (xargs :measure (acl2-count guards)))
  (if (endp guards)
      nil
    (proof-with-checked-results
        ((literal (proof-step-first (car guards)))
         (match (h4-tactics-match-term pattern literal nil))
         (instance (and (car match)
                        (proof-proof-fact (library-library-proof library)
                                          name (table-items (cdr match)))))
         (value (and instance (h4-book-tactics-step-right instance)))
         (reduction (and instance (h4-tactics-tactics-normalize library value nil nil nil nil)))
         (normal (and reduction (h4-book-tactics-step-right reduction))))
      (let ((outcome (and reduction (assoc-equal normal outcomes)))
            (proof (library-library-proof library)))
        (if (not outcome)
            (h4-book-tactics-guarded-alias-guards
             (cdr guards) pattern name outcomes library formula)
          (proof-with-checked-results
              ((consequence (h4-tactics-tactics-modus-ponens library instance (car guards)))
               (rewritten (proof-proof-rewrite proof consequence reduction '(1)))
               (restored (if (cdr outcome)
                             (proof-proof-transport proof rewritten (cdr outcome))
                           rewritten)))
            (h4-tactics-tactics-imply library formula restored)))))))

(defun h4-book-tactics-guarded-alias-clause (clause guards name outcomes library formula goal)
  (if (not (and (equal (len clause) 1) (proof-is-call (car clause) *library-implies*)))
      nil
    (proof-with-checked-results ((parts (proof-list-of-length (car clause) 3)))
      (let ((result (caddr parts)))
        (if (not (proof-compound result))
            nil
          (proof-with-checked-results
              ((head (proof-term-at result 0))
               (eligible (or (equal head *proof-if*)
                             (proof-with-checked-results ((goal-head (proof-term-at goal 0)))
                               (equal head goal-head)))))
            (if (not eligible)
                nil
              (proof-with-checked-results ((fits (h4-book-tactics-fits clause 400)))
                (and fits
                     (h4-book-tactics-guarded-alias-guards
                      guards (cadr parts) name outcomes library formula))))))))))

(defun h4-book-tactics-guarded-alias-facts (facts guards outcomes library formula goal)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      nil
    (proof-with-checked-results
        ((step (h4-book-tactics-guarded-alias-clause (cdar facts) guards (caar facts)
                                                    outcomes library formula goal)))
      (or step (h4-book-tactics-guarded-alias-facts
                (cdr facts) guards outcomes library formula goal)))))

(defun h4-book-tactics-guarded-alias-proof (library formula)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((fits (h4-book-tactics-fits formula 400)))
      (if (not fits)
          nil
        (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
          (let ((guard (cadr parts))
                (goal (caddr parts))
                (proof (library-library-proof library)))
            (if (not (proof-compound goal))
                nil
              (proof-with-checked-results
                  ((premise (h4-book-tactics-guarded-alias-proof-alias guard library))
                   (changes (h4-book-tactics-guarded-alias-changes (cdr goal) 1 library)))
                (if (not (or premise changes))
                    nil
                  (proof-with-checked-results
                      ((given (proof-proof-assume proof guard t))
                       (alternative (and premise (proof-proof-rewrite proof given premise '(1))))
                       (outcomes (h4-book-tactics-guarded-alias-outcomes
                                  changes proof goal (list (cons goal nil)))))
                    (h4-book-tactics-guarded-alias-facts
                     (proof-proof-facts proof) (if premise (list given alternative) (list given))
                     outcomes library formula goal)))))))))))

(defun h4-book-tactics-book-search-p (search) (cadr search))
(defun h4-book-tactics-book-search-literal-rules (search) (caddr search))
(defun h4-book-tactics-book-search-equations (search) (cadddr search))
(defun h4-book-tactics-book-search-remaining (search) (nth 4 search))
(defun h4-book-tactics-book-search-matches (search) (nth 5 search))
(defun h4-book-tactics-book-search-given (search) (nth 6 search))
(defun h4-book-tactics-book-search-extended-rules (search) (nth 7 search))
(defun h4-book-tactics-book-search-lookup-history (search) (nth 8 search))
(defun h4-book-tactics-book-search-scope (search) (nth 9 search))
(defun h4-book-tactics-book-search-hypotheses-replies (search) (nth 10 search))
(defun h4-book-tactics-book-search-unrestricted-rewrite (search) (nth 11 search))

(defun h4-book-tactics-book-search-with-budgets (search remaining matches)
  (update-nth 5 matches (update-nth 4 remaining search)))

(defun h4-book-tactics-book-search-with-matches (search matches)
  (update-nth 5 matches search))

(defun h4-book-tactics-book-search-with-remaining (search remaining)
  (update-nth 4 remaining search))

(defun h4-book-tactics-book-search-with-given (search given)
  (update-nth 6 given search))

(defun h4-book-tactics-book-search-with-extended (search extended)
  (update-nth 8 nil (update-nth 7 extended search)))

(defun h4-book-tactics-book-search-with-lookup-history (search history)
  (update-nth 8 history search))

(defun h4-book-tactics-book-search-with-scope (search scope)
  (update-nth 9 scope search))

(defun h4-book-tactics-book-search-begin-lookup-scope (search)
  (let ((scope (1+ (h4-book-tactics-book-search-scope search))))
    (cons (list :lookup scope) (h4-book-tactics-book-search-with-scope search scope))))

(defun h4-book-tactics-book-search-with-hooks (search hypotheses-replies unrestricted-rewrite)
  (update-nth 11 unrestricted-rewrite (update-nth 10 hypotheses-replies search)))

(defun h4-book-tactics-hypotheses-request-p (result)
  (and (consp result) (eq (car result) :h4-book-tactics-hypotheses-request)))

(defun h4-book-tactics-hypotheses-request-premises (result) (cadr result))

(defund h4-book-tactics-stopped-p (result)
  (or (failure-p result) (h4-book-tactics-hypotheses-request-p result)))

; The fuel proof depends on the call count and is independent of proof results.
(defmacro h4-book-tactics-with-search-result (binding body)
  (let ((result (car binding))
        (search (cadr binding))
        (call (caddr binding)))
    `(let* ((h4-book-tactics-returned (hide ,call))
            (,result (car h4-book-tactics-returned))
            (,search (cdr h4-book-tactics-returned)))
       (if (hide (h4-book-tactics-stopped-p ,result))
           h4-book-tactics-returned
         ,body))))

(defmacro h4-book-tactics-with-search-value (binding body)
  (let ((value (car binding))
        (call (cadr binding))
        (search (caddr binding)))
    `(let ((,value (hide ,call)))
       (if (hide (h4-book-tactics-stopped-p ,value))
           (cons ,value ,search)
         ,body))))

; An ordered map uses AVL nodes of the form (association left right height).
(defun h4-book-tactics-tree-height (tree)
  (if (consp tree) (cadddr tree) 0))

(defun h4-book-tactics-tree-node (entry left right)
  (list entry left right
        (1+ (max (h4-book-tactics-tree-height left) (h4-book-tactics-tree-height right)))))

(defun h4-book-tactics-tree-before-p (key other)
  (if (and (stringp key) (stringp other))
      (string< key other)
    (lexorder key other)))

(defun h4-book-tactics-tree-entry (key tree)
  (cond ((endp tree) nil)
        ((equal key (caar tree)) (car tree))
        ((h4-book-tactics-tree-before-p key (caar tree))
         (h4-book-tactics-tree-entry key (cadr tree)))
        (t (h4-book-tactics-tree-entry key (caddr tree)))))

(defun h4-book-tactics-tree-rotate-right (entry left right)
  (h4-book-tactics-tree-node
   (car left) (cadr left) (h4-book-tactics-tree-node entry (caddr left) right)))

(defun h4-book-tactics-tree-rotate-left (entry left right)
  (h4-book-tactics-tree-node
   (car right) (h4-book-tactics-tree-node entry left (cadr right)) (caddr right)))

(defun h4-book-tactics-tree-balance (entry left right)
  (let ((left-height (h4-book-tactics-tree-height left))
        (right-height (h4-book-tactics-tree-height right)))
    (cond
     ((< (1+ right-height) left-height)
      (h4-book-tactics-tree-rotate-right
       entry
       (if (< (h4-book-tactics-tree-height (cadr left))
              (h4-book-tactics-tree-height (caddr left)))
           (h4-book-tactics-tree-rotate-left (car left) (cadr left) (caddr left))
         left)
       right))
     ((< (1+ left-height) right-height)
      (h4-book-tactics-tree-rotate-left
       entry left
       (if (< (h4-book-tactics-tree-height (caddr right))
              (h4-book-tactics-tree-height (cadr right)))
           (h4-book-tactics-tree-rotate-right (car right) (cadr right) (caddr right))
         right)))
     (t (h4-book-tactics-tree-node entry left right)))))

(defun h4-book-tactics-tree-put (key value tree)
  (cond
   ((endp tree) (h4-book-tactics-tree-node (cons key value) nil nil))
   ((equal key (caar tree)) (cons (cons key value) (cdr tree)))
   ((h4-book-tactics-tree-before-p key (caar tree))
    (h4-book-tactics-tree-balance
     (car tree) (h4-book-tactics-tree-put key value (cadr tree)) (caddr tree)))
   (t (h4-book-tactics-tree-balance
       (car tree) (cadr tree) (h4-book-tactics-tree-put key value (caddr tree))))))

(defun h4-book-tactics-index-rule (index key rule)
  (table-put index key (cons rule (table-get index key nil))))

(defun h4-book-tactics-key-rule (rule)
  (let ((formula (h4-book-tactics-rule-conclusion rule)))
    (proof-with-checked-results
        ((key (h4-book-tactics-term-key formula))
         (equal-p (equal (car formula) *proof-equal*))
         (left (and equal-p (proof-term-at formula 1)))
         (equation-key (and equal-p (proof-compound left) (h4-book-tactics-term-key left))))
      (list rule key equation-key))))

(defun h4-book-tactics-index-keyed-rule (keyed literal-rules equations)
  (let ((rule (car keyed))
        (literal-key (cadr keyed))
        (equation-key (caddr keyed)))
    (cons (h4-book-tactics-index-rule literal-rules literal-key rule)
          (if equation-key (h4-book-tactics-index-rule equations equation-key rule) equations))))

(defun h4-book-tactics-index-rules (rules literal-rules equations)
  (declare (xargs :measure (acl2-count rules)))
  (if (endp rules)
      (cons literal-rules equations)
    (proof-with-checked-results ((keyed (h4-book-tactics-key-rule (car rules))))
      (let ((indexes (h4-book-tactics-index-keyed-rule keyed literal-rules equations)))
        (h4-book-tactics-index-rules (cdr rules) (car indexes) (cdr indexes))))))

(defun h4-book-tactics-key-rules (rules)
  (if (endp rules)
      nil
    (proof-with-checked-results
        ((keyed (h4-book-tactics-key-rule (car rules)))
         (rest (h4-book-tactics-key-rules (cdr rules))))
      (cons keyed rest))))

(defun h4-book-tactics-fact-views (name clause)
  (proof-with-checked-results ((fits (and clause (h4-book-tactics-fits clause 800))))
    (and fits (h4-book-tactics-views name (car clause) nil nil (not (equal (len clause) 1))))))

(defun h4-book-tactics-remember-template (name clause templates)
  (let ((entry (h4-book-tactics-tree-entry name templates)))
    (if (and entry (equal clause (cadr entry)))
        templates
      (let ((keyed (proof-with-checked-results ((rules (h4-book-tactics-fact-views name clause)))
                     (h4-book-tactics-key-rules rules))))
        (h4-book-tactics-tree-put name (cons clause keyed) templates)))))

(defun h4-book-tactics-prepare-templates (facts definitions templates)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      templates
    (let ((name (caar facts))
          (clause (cdar facts)))
      (h4-book-tactics-prepare-templates
       (cdr facts) definitions
       (if (and clause (not (assoc-equal name definitions)))
           (h4-book-tactics-remember-template name clause templates)
         templates)))))

(defun h4-book-tactics-template-entry (name clause tables)
  (if (endp tables)
      nil
    (let ((entry (h4-book-tactics-tree-entry name (car tables))))
      (if (and entry (equal (cadr entry) clause))
          entry
        (h4-book-tactics-template-entry name clause (cdr tables))))))

(defun h4-book-tactics-index-keyed-rules (rules literal-rules equations)
  (if (endp rules)
      (cons literal-rules equations)
    (let ((indexes (h4-book-tactics-index-keyed-rule (car rules) literal-rules equations)))
      (h4-book-tactics-index-keyed-rules (cdr rules) (car indexes) (cdr indexes)))))

(defun h4-book-tactics-index-fact (name clause literal-rules equations tables)
  (let ((entry (h4-book-tactics-template-entry name clause tables)))
    (if entry
      (proof-with-checked-results
          ((rules (cddr entry)))
        (h4-book-tactics-index-keyed-rules rules literal-rules equations))
      (proof-with-checked-results ((rules (h4-book-tactics-fact-views name clause)))
        (h4-book-tactics-index-rules rules literal-rules equations)))))

(defun h4-book-tactics-index-facts-with-templates (facts definitions literal-rules equations tables)
  (if (endp facts)
      (cons literal-rules equations)
    (let ((name (caar facts))
          (clause (cdar facts)))
      (proof-with-checked-results
          ((indexes (if (and clause (not (assoc-equal name definitions)))
                        (h4-book-tactics-index-fact name clause literal-rules equations tables)
                      (cons literal-rules equations))))
        (h4-book-tactics-index-facts-with-templates
         (cdr facts) definitions (car indexes) (cdr indexes) tables)))))

(defun h4-book-tactics-index-facts (facts definitions literal-rules equations)
  (h4-book-tactics-index-facts-with-templates facts definitions literal-rules equations nil))

(defun h4-book-tactics-index-in-rule-order (index)
  (declare (xargs :measure (acl2-count index)))
  (if (endp index)
      nil
    (cons (cons (caar index) (reverse (cdar index)))
          (h4-book-tactics-index-in-rule-order (cdr index)))))

(defun h4-book-tactics-book-search-init-with-templates (library tables)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((indexes (h4-book-tactics-index-facts-with-templates
                   (reverse (proof-proof-facts proof)) (proof-proof-definitions proof)
                   nil nil tables)))
      (list :h4-book-tactics-book-search library
            (h4-book-tactics-index-in-rule-order (car indexes))
            (h4-book-tactics-index-in-rule-order (cdr indexes))
            0 0 nil t nil 0 :default nil))))

(defun h4-book-tactics-book-search-init (library)
  (h4-book-tactics-book-search-init-with-templates library nil))

(defun h4-book-tactics-countdown-actuals (formals actuals tests)
  (declare (xargs :measure (acl2-count formals)))
  (if (or (endp formals) (endp actuals))
      nil
    (let ((formal (car formals)))
      (or (and (member-equal (list (list *h4-book-arithmetic-zp* formal) nil) tests)
               (or (equal (car actuals) (library-plus formal *proof-neg-one*))
                   (equal (car actuals) (library-plus *proof-neg-one* formal))))
          (h4-book-tactics-countdown-actuals (cdr formals) (cdr actuals) tests)))))

(defun h4-book-tactics-countdown-calls (calls formals)
  (declare (xargs :measure (acl2-count calls)))
  (and (consp calls)
       (or (h4-book-tactics-countdown-actuals formals
                                             (termination-call-actuals (car calls))
                                             (termination-call-tests (car calls)))
           (h4-book-tactics-countdown-calls (cdr calls) formals))))

(defun h4-book-tactics-book-search-recursion (search head)
  (let* ((library (h4-book-tactics-book-search-p search))
         (proof (library-library-proof library))
         (definition (assoc-equal head (proof-proof-definitions proof))))
    (if (not definition)
        '(:failure "failure" "")
      (let* ((formals (cadr definition))
             (definitions (list (list head formals (caddr definition)))))
        (proof-with-checked-results
            ((calls (termination-recursive-calls *termination-all* definitions))
             (plan (and calls (not (h4-book-tactics-countdown-calls calls formals))
                        (termination-selector-plan definitions calls)))
             (selected (table-get plan head nil))
             (index (and selected (seq-index formals selected))))
          (list calls index))))))

(defun h4-book-tactics-book-search-known-shape (search term evidence)
  (declare (ignore search))
  (let ((shape (list *proof-consp* term)))
    (or (proof-is-call term *proof-cons*)
        (proof-is-call term *proof-quote*)
        (if (or (assoc-equal shape evidence)
                (assoc-equal (proof-neg shape) evidence)) t nil))))

(defun h4-book-tactics-book-search-expandable (search term evidence)
  (proof-with-checked-results
      ((head (proof-term-at term 0))
       (recursion (h4-book-tactics-book-search-recursion search head)))
    (let ((index (cadr recursion)))
      (or (null index)
          (proof-with-checked-results ((argument (proof-term-at term (1+ index))))
            (h4-book-tactics-book-search-known-shape search argument evidence))))))

(defun h4-book-tactics-evidence-set (evidence step overwrite)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (if (or overwrite (not (assoc-equal literal evidence)))
        (table-put evidence literal step)
      evidence)))

(defun h4-book-tactics-evidence-update (evidence steps)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      evidence
    (proof-with-checked-results ((added (h4-book-tactics-evidence-set evidence (car steps) t)))
      (h4-book-tactics-evidence-update added (cdr steps)))))

(defun h4-book-tactics-hypothesis-definition (search literal evidence)
  (if (not (proof-compound literal))
      nil
    (proof-with-checked-results ((head (proof-term-at literal 0)))
      (if (proof-compound head)
          nil
        (let* ((proof (library-library-proof (h4-book-tactics-book-search-p search)))
               (definition (assoc-equal head (proof-proof-definitions proof)))
               (body (caddr definition)))
          (proof-with-checked-results
              ((fits (h4-book-tactics-fits literal 650))
               (fits-body (and fits definition
                               (not (member-equal head *h4-book-tactics-logic*))
                               (h4-book-tactics-fits body 650))))
            (and fits-body
                 (< (h4-book-tactics-size body 150) 75)
                 (h4-book-tactics-book-search-expandable search literal evidence))))))))

(defun h4-book-tactics-hypotheses-extra (steps search evidence)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      nil
    (let* ((library (h4-book-tactics-book-search-p search))
           (proof (library-library-proof library))
           (step (car steps)))
      (proof-with-checked-results
          ((first (proof-step-first step))
           (negative (proof-is-call first *proof-not*))
           (literal (if negative (proof-term-at first 1) first))
           (eligible (h4-book-tactics-hypothesis-definition search literal evidence))
           (opened (and eligible (proof-proof-unfold proof literal)))
           (value (and opened (h4-book-tactics-step-right opened)))
           (reduction (and opened
                           (h4-tactics-tactics-normalize library value (table-values evidence)
                                                         *h4-book-tactics-logic* nil nil)))
           (chain (and opened (proof-proof-chain proof opened (list reduction))))
           (extra (and opened (proof-proof-rewrite proof step chain (if negative '(1 1) '(1)))))
           (rest (h4-book-tactics-hypotheses-extra (cdr steps) search evidence)))
        (if extra (cons extra rest) rest)))))

(defun h4-book-tactics-hypothesis-negative (proof step term evidence)
  (cond
   ((proof-is-call term *proof-equal*)
    (proof-with-checked-results ((parts (proof-list-of-length term 3)))
      (let* ((left (cadr parts))
             (right (caddr parts))
             (reverse (proof-neg (proof-eq right left))))
        (if (assoc-equal reverse evidence)
            evidence
          (proof-with-checked-results
              ((equation (proof-proof-fact proof *h4-book-tactics-equal-symmetry*
                                           (list (list *library-x* left) (list *library-y* right))))
               (reversed (proof-proof-rewrite proof step equation '(1 1))))
            (table-put evidence reverse reversed))))))
   ((proof-is-call term *proof-less*)
    (proof-with-checked-results ((left (proof-term-at term 1)))
      (if (not (equal left *proof-zero*))
          evidence
        (proof-with-checked-results ((subject (proof-term-at term 2)))
          (let ((natural (table-get evidence (list *library-natp* subject) nil)))
            (if (not natural)
                evidence
              (proof-with-checked-results
                  ((zero (proof-proof-use proof *h4-book-arithmetic-natural-nonpositive-zero*
                                          (list (list *library-x* subject)) (list natural step))))
                (h4-book-tactics-evidence-set evidence zero t))))))))
   (t evidence)))

(defun h4-book-tactics-hypothesis-consp (library proof step literal evidence)
  (proof-with-checked-results ((subject (proof-term-at literal 1)))
    (if (assoc-equal subject evidence)
        evidence
      (proof-with-checked-results
          ((negative (proof-proof-assume proof subject nil))
           (as-nil (h4-tactics-tactics-nil-value library negative))
           (changed (proof-proof-rewrite proof step as-nil '(1 1)))
           (constant (proof-proof-compute proof (list *proof-consp* *proof-false*) *proof-nil*))
           (impossible (proof-proof-rewrite proof changed constant '(1)))
           (tidied (proof-proof-tidy proof impossible))
           (front (proof-proof-front proof tidied subject)))
        (table-put evidence subject front)))))

(defun h4-book-tactics-hypothesis-less (proof step literal evidence)
  (proof-with-checked-results ((right (proof-term-at literal 2)))
    (if (not (proof-is-call right *library-len*))
        evidence
      (proof-with-checked-results ((parts (proof-list-of-length literal 3))
                                   (length-call (proof-list-of-length right 2)))
        (let* ((subscript (cadr parts))
               (subject (cadr length-call))
               (natural (table-get evidence (list *library-natp* subscript) nil)))
          (if (not natural)
              evidence
            (proof-with-checked-results
                ((pair (proof-proof-use proof *h4-book-arithmetic-index-in-bounds*
                                        (list (list *library-x* subscript) (list *library-y* subject))
                                        (list natural step))))
              (h4-book-tactics-evidence-set evidence pair nil))))))))

(defun h4-book-tactics-hypothesis-consequences (library step evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results ((literal (proof-step-first step)))
      (cond
       ((proof-is-call literal *proof-equal*)
        (proof-with-checked-results ((right (proof-term-at literal 2)))
          (let ((reverse (proof-eq right (cadr literal))))
            (if (assoc-equal reverse evidence)
                evidence
              (proof-with-checked-results ((symmetric (proof-proof-symmetric proof step)))
                (table-put evidence reverse symmetric))))))
       ((proof-is-call literal *proof-not*)
        (proof-with-checked-results ((child (proof-term-at literal 1)))
          (h4-book-tactics-hypothesis-negative proof step child evidence)))
       ((proof-is-call literal *proof-consp*)
        (h4-book-tactics-hypothesis-consp library proof step literal evidence))
       ((proof-is-call literal *h4-book-arithmetic-zp*)
        (proof-with-checked-results ((subject (proof-term-at literal 1)))
          (let ((natural (table-get evidence (list *library-natp* subject) nil)))
            (if (not natural)
                evidence
              (proof-with-checked-results
                  ((zero (proof-proof-use proof *h4-book-arithmetic-natural-countdown-zero*
                                          (list (list *library-x* subject)) (list natural step))))
                (h4-book-tactics-evidence-set evidence zero t))))))
       ((proof-is-call literal *proof-less*)
        (h4-book-tactics-hypothesis-less proof step literal evidence))
       (t evidence)))))

(defun h4-book-tactics-hypotheses-consequences (steps library evidence)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      evidence
    (proof-with-checked-results
        ((added (h4-book-tactics-hypothesis-consequences library (car steps) evidence)))
      (h4-book-tactics-hypotheses-consequences (cdr steps) library added))))

(defun h4-book-tactics-book-search-hypotheses (search premises)
  (let ((library (h4-book-tactics-book-search-p search)))
    (proof-with-checked-results
        ((expanded (h4-book-measures-expand-evidence library premises))
         (evidence (h4-book-tactics-evidence-update nil expanded))
         (extra (h4-book-tactics-hypotheses-extra (table-values evidence) search evidence))
         (additions (and extra (h4-book-measures-expand-evidence library extra)))
         (increased (h4-book-tactics-evidence-update evidence additions)))
      (h4-book-tactics-hypotheses-consequences (table-values increased) library increased))))

(defund h4-book-tactics-book-search-iff-direction (search fact premise direction)
  (let* ((library (h4-book-tactics-book-search-p search))
         (proof (library-library-proof library)))
    (proof-with-checked-results
        ((literal (proof-step-first fact))
         (left (proof-term-at literal 1))
         (equation (proof-proof-unfold proof literal))
         (opened (proof-proof-rewrite proof fact equation '(1))))
      (if (equal direction 3)
          (proof-with-checked-results ((branch (proof-proof-prove-if proof opened premise))
                                       (conjuncts (h4-tactics-tactics-conjunct library branch)))
            (car conjuncts))
        (proof-with-checked-results ((hypothesis (proof-proof-assume proof left nil))
                                     (otherwise (proof-proof-prove-if proof opened hypothesis))
                                     (contradiction (proof-proof-prove-if proof otherwise premise)))
          (proof-proof-front proof contradiction left))))))

(defund h4-book-tactics-book-search-candidates (index term)
  (proof-with-checked-results ((key (h4-book-tactics-term-key term)))
    (let ((first (cadr key)))
      (append (table-get index key nil)
              (if (or (null first) (equal first 0) (equal first ""))
                  nil
                (table-get index (list (car key) nil) nil))))))

(defund h4-book-tactics-extended-path-p (path)
  (declare (xargs :measure (acl2-count path)))
  (and (consp path)
       (or (> (car path) 2) (h4-book-tactics-extended-path-p (cdr path)))))

(defund h4-book-tactics-rule-match (rule term rewrite)
  (let ((conclusion (h4-book-tactics-rule-conclusion rule)))
    (proof-with-checked-results ((pattern (if rewrite (proof-term-at conclusion 1) conclusion)))
      (if (h4-book-tactics-rule-local rule)
          (cons (equal pattern term) nil)
        (h4-tactics-match-term pattern term nil)))))

(defund h4-book-tactics-rewrite-allowed-p (rule term bindings)
  (proof-with-checked-results
      ((right (proof-term-at (h4-book-tactics-rule-conclusion rule) 2))
       (replacement (proof-subst right bindings))
       (smaller (h4-book-tactics-smaller replacement term)))
    (or smaller
        (and (h4-book-tactics-rule-local rule)
             (not (member-equal term (h4-book-tactics-terms replacement)))))))

(defund h4-book-tactics-bindings-fit-p (bindings)
  (declare (xargs :measure (acl2-count bindings)))
  (if (endp bindings)
      t
    (proof-with-checked-results ((fits (h4-book-tactics-fits (cdar bindings) 400)))
      (and fits (h4-book-tactics-bindings-fit-p (cdr bindings))))))

(defund h4-book-tactics-lookup-obvious (search goal)
  (let ((proof (library-library-proof (h4-book-tactics-book-search-p search))))
    (cond
     ((proof-is-call goal *proof-consp*)
      (proof-with-checked-results ((argument (proof-term-at goal 1)))
        (and (proof-is-call argument *proof-cons*)
             (proof-proof-fact proof *h4-book-tactics-consp-cons*
                               (seq-zip (list *library-x* *library-y*) (cdr argument))))))
     ((proof-is-call goal *proof-equal*)
      (proof-with-checked-results ((right (proof-term-at goal 2)))
        (and (equal (cadr goal) right) (proof-proof-reflexive proof right))))
     (t nil))))

(mutual-recursion
 (defun h4-book-tactics-lookup-loop (n search goal evidence depth scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-lookup-loop") search)
     (let* ((given (assoc-equal goal evidence))
            (key (list scope goal depth))
            (cached (and (not given)
                         (assoc-equal key (h4-book-tactics-book-search-lookup-history search)))))
       (cond (given (cons (cdr given) search))
             (cached (cons (cdr cached) search))
             (t
              (h4-book-tactics-with-search-result
                  (result search (h4-book-tactics-lookup-rule-loop (1- n) search goal evidence depth scope))
                (cons result
                      (h4-book-tactics-book-search-with-lookup-history
                       search (table-put (h4-book-tactics-book-search-lookup-history search)
                                           key result)))))))))

 (defun h4-book-tactics-lookup-rule-loop (n search goal evidence depth scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-lookup-rule-loop") search)
     (let* ((library (h4-book-tactics-book-search-p search))
            (proof (library-library-proof library)))
       (cond
      ((equal goal *proof-true*) (cons (proof-proof-prove proof *proof-true* nil nil) search))
      ((not (proof-compound goal)) (cons nil search))
      (t
       (h4-book-tactics-with-search-value (head (proof-term-at goal 0) search)
         (if (or (proof-compound head) (equal goal *proof-false*))
             (cons nil search)
           (h4-book-tactics-with-search-value
               (tail (and (equal head *proof-if*) (proof-term-at goal 3)) search)
             (if (and (equal tail *proof-false*) (> depth 0))
                 (h4-book-tactics-with-search-result
                     (first search (h4-book-tactics-lookup-loop (1- n) search (cadr goal)
                                                                evidence (1- depth) scope))
                   (h4-book-tactics-with-search-result
                       (second search (if first
                                          (h4-book-tactics-lookup-loop (1- n) search (caddr goal)
                                                                       evidence (1- depth) scope)
                                        (cons nil search)))
                     (if second
                         (cons (h4-tactics-tactics-conjunction library goal first second) search)
                       (h4-book-tactics-lookup-remainder-loop (1- n) search goal evidence depth scope))))
               (h4-book-tactics-lookup-remainder-loop (1- n) search goal evidence depth scope))))))))))

 (defun h4-book-tactics-lookup-remainder-loop (n search goal evidence depth scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-lookup-remainder-loop") search)
     (h4-book-tactics-with-search-value (obvious (h4-book-tactics-lookup-obvious search goal) search)
       (if obvious
           (cons obvious search)
         (h4-book-tactics-with-search-value (fits (h4-book-tactics-fits goal 900) search)
           (if (not fits)
               (cons nil search)
             (h4-book-tactics-with-search-result
                 (local search (h4-book-tactics-lookup-local-loop (1- n) search goal evidence depth
                                                                 scope evidence))
               (if local
                   (cons local search)
                 (h4-book-tactics-with-search-value
                     (rules (h4-book-tactics-book-search-candidates
                             (h4-book-tactics-book-search-literal-rules search) goal) search)
                   (h4-book-tactics-try-rules-loop (1- n) search rules goal evidence depth
                                                   nil scope nil))))))))))

 (defun h4-book-tactics-lookup-local-loop (n search goal evidence depth scope entries)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "Fuel" "h4-book-tactics-lookup-local-loop") search))
    ((endp entries) (cons nil search))
    (t
     (let ((step (cdar entries)))
       (h4-book-tactics-with-search-value (literal (proof-step-first step) search)
         (h4-book-tactics-with-search-value
             (rules (and (proof-is-call literal *library-implies*)
                         (h4-book-tactics-views step literal nil t nil)) search)
           (h4-book-tactics-with-search-result
               (found search (h4-book-tactics-try-rules-loop (1- n) search rules goal evidence depth
                                                             nil scope t))
             (if found
                 (cons found search)
               (h4-book-tactics-lookup-local-loop (1- n) search goal evidence depth scope
                                                 (cdr entries))))))))))

 (defun h4-book-tactics-try-rules-loop (n search rules term evidence depth rewrite scope same-head)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "Fuel" "h4-book-tactics-try-rules-loop") search))
    ((endp rules) (cons nil search))
    (t
     (let ((rule (car rules)))
       (h4-book-tactics-with-search-result
           (found search (if (and same-head
                                  (not (equal (car (h4-book-tactics-rule-conclusion rule)) (car term))))
                             (cons nil search)
                           (h4-book-tactics-instantiate-loop (1- n) search rule term
                                                             evidence depth rewrite scope)))
         (if found
             (cons found search)
           (h4-book-tactics-try-rules-loop (1- n) search (cdr rules) term evidence depth
                                           rewrite scope same-head)))))))

 (defun h4-book-tactics-instantiate-loop (n search rule term evidence depth rewrite scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-instantiate-loop") search)
     (let ((unrestricted (h4-book-tactics-book-search-unrestricted-rewrite search)))
       (h4-book-tactics-with-search-value
           (direct (and rewrite unrestricted
                        (equal (h4-book-tactics-rule-source rule) unrestricted)
                        (proof-with-checked-results
                            ((left (proof-term-at (h4-book-tactics-rule-conclusion rule) 1)))
                          (h4-tactics-match-term left term nil))) search)
         (cond
          ((car direct)
           (h4-book-tactics-replay-loop (1- n) search rule (cdr direct) evidence depth scope))
          ((and (not (h4-book-tactics-book-search-extended-rules search))
                (or (h4-book-tactics-rule-clause rule)
                    (h4-book-tactics-extended-path-p (h4-book-tactics-rule-path rule))))
           (cons nil search))
          (t
           (let* ((matches (1- (h4-book-tactics-book-search-matches search)))
                  (search (h4-book-tactics-book-search-with-matches search matches)))
             (if (< matches 0)
                 (cons '(:failure "Unproved" "") search)
               (h4-book-tactics-with-search-value (match (h4-book-tactics-rule-match rule term rewrite) search)
                 (if (not (car match))
                     (cons nil search)
                   (h4-book-tactics-with-search-value
                       (allowed (or (not rewrite)
                                    (h4-book-tactics-rewrite-allowed-p rule term (cdr match))) search)
                     (if allowed
                         (h4-book-tactics-replay-loop (1- n) search rule (cdr match) evidence depth scope)
                       (cons nil search)))))))))))))

 (defun h4-book-tactics-replay-loop (n search rule bindings evidence depth scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-replay-loop") search)
     (let* ((library (h4-book-tactics-book-search-p search))
            (proof (library-library-proof library))
            (source (h4-book-tactics-rule-source rule)))
       (h4-book-tactics-with-search-value (fits (h4-book-tactics-bindings-fit-p bindings) search)
         (if (not fits)
             (cons nil search)
           (h4-book-tactics-with-search-value
               (step (if (h4-book-tactics-rule-local rule)
                         source
                       (proof-proof-fact proof source (table-items bindings))) search)
             (let ((clause (proof-step-clause step)))
               (h4-book-tactics-with-search-value (fits (h4-book-tactics-fits clause 1600) search)
                 (if (not fits)
                     (cons nil search)
                   (h4-book-tactics-with-search-result
                       (found search (if (h4-book-tactics-rule-clause rule)
                                         (h4-book-tactics-replay-sides-loop (1- n) search step
                                                                          (cdr clause) evidence depth scope)
                                       (cons step search)))
                     (if (not found)
                         (cons nil search)
                       (h4-book-tactics-replay-path-loop (1- n) search found (h4-book-tactics-rule-path rule)
                                                         evidence depth scope))))))))))))

 (defun h4-book-tactics-replay-sides-loop (n search step sides evidence depth scope)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "Fuel" "h4-book-tactics-replay-sides-loop") search))
    ((endp sides) (cons step search))
    ((not (member-equal (car sides) (cdr (proof-step-clause step))))
     (h4-book-tactics-replay-sides-loop (1- n) search step (cdr sides) evidence depth scope))
    ((equal depth 0) (cons nil search))
    (t
     (let ((side (car sides)))
       (h4-book-tactics-with-search-value
           (positive (and (proof-is-call side *proof-not*) (proof-term-at side 1)) search)
         (h4-book-tactics-with-search-result
             (first search (if (proof-is-call side *proof-not*)
                               (h4-book-tactics-lookup-loop (1- n) search positive evidence (1- depth) scope)
                             (cons nil search)))
           (h4-book-tactics-with-search-result
               (hypothesis search (if first
                                      (cons first search)
                                    (h4-book-tactics-lookup-loop (1- n) search (proof-neg side)
                                                                 evidence (1- depth) scope)))
             (if (not hypothesis)
                 (cons nil search)
               (h4-book-tactics-with-search-value
                   (discharged (proof-proof-discharge (library-library-proof (h4-book-tactics-book-search-p search))
                                                       step hypothesis) search)
                 (h4-book-tactics-replay-sides-loop (1- n) search discharged (cdr sides)
                                                   evidence depth scope))))))))))

 (defun h4-book-tactics-replay-path-loop (n search step path evidence depth scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-replay-path-loop") search)
     (if (endp path)
         (cons step search)
       (let ((library (h4-book-tactics-book-search-p search))
             (direction (car path)))
         (cond
          ((member-equal direction '(1 2))
           (h4-book-tactics-with-search-value (conjuncts (h4-tactics-tactics-conjunct library step) search)
             (h4-book-tactics-replay-path-loop (1- n) search (nth (1- direction) conjuncts)
                                              (cdr path) evidence depth scope)))
          ((equal depth 0) (cons nil search))
          (t
           (h4-book-tactics-with-search-value
               (goal (proof-with-checked-results ((literal (proof-step-first step)))
                       (proof-term-at literal (if (member-equal direction '(0 3)) 1 2))) search)
             (h4-book-tactics-with-search-result
                 (premise search (h4-book-tactics-lookup-loop (1- n) search goal evidence (1- depth) scope))
               (if (not premise)
                   (cons nil search)
                 (h4-book-tactics-with-search-value
                     (next (if (equal direction 0)
                               (h4-tactics-tactics-modus-ponens library step premise)
                             (h4-book-tactics-book-search-iff-direction search step premise direction)) search)
                   (h4-book-tactics-replay-path-loop (1- n) search next (cdr path)
                                                    evidence depth scope))))))))))))

(defun h4-book-tactics-book-search-lookup-scoped (search goal evidence depth scope)
  (h4-book-tactics-lookup-loop 1000000 search goal evidence depth (list :external scope)))

(defun h4-book-tactics-book-search-replay-scoped (search rule bindings evidence depth scope)
  (h4-book-tactics-replay-loop 1000000 search rule bindings evidence depth (list :external scope)))

(defun h4-book-tactics-book-search-lookup (search goal evidence depth)
  (h4-book-tactics-book-search-lookup-scoped search goal evidence depth evidence))

(defun h4-book-tactics-book-search-lookup-rule (search goal evidence depth)
  (h4-book-tactics-lookup-rule-loop 1000000 search goal evidence depth (list :external evidence)))

(defun h4-book-tactics-book-search-instantiate (search rule term evidence depth rewrite)
  (h4-book-tactics-instantiate-loop 1000000 search rule term evidence depth rewrite (list :external evidence)))

(defun h4-book-tactics-book-search-replay (search rule bindings evidence depth)
  (h4-book-tactics-book-search-replay-scoped search rule bindings evidence depth evidence))

(defun h4-book-tactics-reduction-equality (step proof)
  (proof-with-checked-results ((formula (proof-step-first step)))
    (if (not (proof-is-call formula *proof-equal*))
        nil
      (proof-with-checked-results ((right (proof-term-at formula 2)))
        (if (equal (cadr formula) right)
            nil
          (proof-with-checked-results ((parts (proof-list-of-length formula 3))
                                       (smaller (h4-book-tactics-smaller right (cadr parts))))
            (if smaller step (proof-proof-symmetric proof step))))))))

(defun h4-book-tactics-reduction-equalities (steps proof)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      nil
    (proof-with-checked-results ((first (h4-book-tactics-reduction-equality (car steps) proof))
                                 (rest (h4-book-tactics-reduction-equalities (cdr steps) proof)))
      (if first (cons first rest) rest))))

(defun h4-book-tactics-protect-compounds (terms protected)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      protected
    (h4-book-tactics-protect-compounds
     (cdr terms) (if (proof-compound (car terms)) (add-to-set-equal (car terms) protected) protected))))

(defun h4-book-tactics-reduction-protected (steps protected)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      protected
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-tactics-reduction-protected
       (cdr steps) (h4-book-tactics-protect-compounds (h4-book-tactics-terms literal) protected)))))

(defun h4-book-tactics-reduction-index-equations (rules index)
  (declare (xargs :measure (acl2-count rules)))
  (if (endp rules)
      index
    (let* ((rule (car rules))
           (formula (h4-book-tactics-rule-conclusion rule)))
      (proof-with-checked-results
          ((equation (proof-is-call formula *proof-equal*))
           (left (and equation (proof-term-at formula 1)))
           (call (and equation (proof-compound left)))
           (head (and call (proof-term-at left 0))))
        (h4-book-tactics-reduction-index-equations
         (cdr rules) (if call (h4-book-tactics-index-rule index head rule) index))))))

(defun h4-book-tactics-reduction-local-equations (steps index)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      (h4-book-tactics-index-in-rule-order index)
    (let ((step (car steps)))
      (proof-with-checked-results
          ((literal (proof-step-first step))
           (views (and (proof-is-call literal *library-implies*)
                       (h4-book-tactics-views step literal nil t nil)))
           (indexed (h4-book-tactics-reduction-index-equations views index)))
        (h4-book-tactics-reduction-local-equations (cdr steps) indexed)))))

(defun h4-book-tactics-reduction-selector (library term evidence)
  (let ((head (car term))
        (proof (library-library-proof library)))
    (if (not (member-equal head *h4-book-tactics-recursive*))
        nil
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (if (proof-is-call argument *proof-cons*)
            (library-library-axiom library (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
                                   (cdr argument))
          (let ((atom (table-get evidence (proof-neg (list *proof-consp* argument)) nil)))
            (if (not atom)
                nil
              (proof-with-checked-results
                  ((step (library-library-axiom library (if (equal head *library-car*)
                                                           "COMPLETION-OF-CAR" "COMPLETION-OF-CDR")
                                                (list argument)))
                   (branch (h4-book-tactics-step-right step))
                   (selection (proof-proof-select proof branch atom)))
                (proof-proof-chain proof step (list selection))))))))))

(defun h4-book-tactics-cons-arguments-p (arguments)
  (declare (xargs :measure (acl2-count arguments)))
  (or (endp arguments)
      (and (proof-is-call (car arguments) *proof-cons*)
           (h4-book-tactics-cons-arguments-p (cdr arguments)))))

(defun h4-book-tactics-reduction-cons-equality (proof term)
  (if (and (proof-is-call term *proof-equal*)
           (h4-book-tactics-cons-arguments-p (cdr term)))
      (proof-with-checked-results ((right (proof-term-at term 2)))
        (proof-proof-fact proof (proof-sym "CONS-EQUAL" "ACL2")
                          (seq-zip *h4-book-tactics-cons-equal-variables*
                                  (append (cdadr term) (cdr right)))))
    nil))

(defun h4-book-tactics-unfolding-total (unfolding)
  (declare (xargs :measure (acl2-count unfolding)))
  (if (endp unfolding)
      0
    (+ (cdar unfolding) (h4-book-tactics-unfolding-total (cdr unfolding)))))

(defun h4-book-tactics-reduction-unfold (term search evidence protected unfolding)
  (let* ((head (car term))
         (proof (library-library-proof (h4-book-tactics-book-search-p search)))
         (definition (assoc-equal head (proof-proof-definitions proof)))
         (body (caddr definition))
         (opened (table-get unfolding head 0)))
    (if (not (and definition (not (member-equal head *h4-book-tactics-logic*))
                  (not (member-equal term protected)) (< opened 6)
                  (< (h4-book-tactics-unfolding-total unfolding) 18)
                  (< (h4-book-tactics-size body 150) 125)))
        (list nil search unfolding)
      (let* ((fits (h4-book-tactics-fits body 650))
             (allowed (and fits (if (failure-p fits) fits
                                  (h4-book-tactics-book-search-expandable search term evidence)))))
        (cond ((failure-p allowed) (list allowed search unfolding))
              (allowed (list (proof-proof-unfold proof term) search
                             (table-put unfolding head (1+ opened))))
              (t (list nil search unfolding)))))))

(defun h4-book-tactics-reduction-try-equations
    (term search evidence local-equations scope)
  (h4-book-tactics-with-search-value
      (rules (h4-book-tactics-book-search-candidates
              (h4-book-tactics-book-search-equations search) term) search)
    (h4-book-tactics-with-search-result
        (local search (h4-book-tactics-try-rules-loop
                       1000000 search (table-get local-equations (car term) nil)
                       term evidence 4 t scope nil))
      (if local
          (cons local search)
        (h4-book-tactics-try-rules-loop 1000000 search rules term evidence 2 t scope nil)))))

(defun h4-book-tactics-reduction-obvious (library term evidence)
  (proof-with-checked-results ((selector (h4-book-tactics-reduction-selector library term evidence)))
    (or selector
        (h4-book-tactics-reduction-cons-equality (library-library-proof library) term))))

(defun h4-book-tactics-reduction-eligible-p (term)
  (proof-with-checked-results ((head (proof-term-at term 0))
                               (fits (h4-book-tactics-fits term 1000)))
    (and fits
         (or (not (equal head *h4-book-arithmetic-zp*))
             (proof-with-checked-results ((argument (proof-term-at term 1)))
               (proof-is-call argument *proof-quote*))))))

(defun h4-book-tactics-book-search-reduction-provide
    (term search evidence local-equations protected unfolding scope)
  (let* ((library (h4-book-tactics-book-search-p search))
         (eligible (h4-book-tactics-reduction-eligible-p term)))
    (cond
     ((failure-p eligible) (list eligible search unfolding))
     ((not eligible) (list nil search unfolding))
     (t
      (let ((obvious (h4-book-tactics-reduction-obvious library term evidence)))
        (if obvious
            (list obvious search unfolding)
          (let* ((matched (h4-book-tactics-reduction-try-equations term search evidence local-equations scope))
                 (result (car matched))
                 (search (cdr matched)))
            (if result
                (list result search unfolding)
              (h4-book-tactics-reduction-unfold term search evidence protected unfolding)))))))))

(defun h4-book-tactics-reduction-loop
    (n search formula evidence scope equalities local-equations protected unfolding replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "h4-book-tactics-reduction-loop") search)
    (let* ((library (h4-book-tactics-book-search-p search))
           (equation (hide (h4-tactics-tactics-normalize
                            library formula (table-values evidence) *h4-book-tactics-logic*
                            equalities (cons :h4-tactics-ordered-provider (reverse replies))))))
      (cond
       ((hide (failure-p equation)) (cons equation search))
       ((hide (h4-tactics-request-p equation))
        (let* ((provided (hide (h4-book-tactics-book-search-reduction-provide
                                (h4-tactics-request-term equation) search evidence local-equations
                                protected unfolding scope)))
               (result (car provided))
               (search (cadr provided)))
          (if (hide (failure-p result))
              (cons result search)
            (h4-book-tactics-reduction-loop
             (1- n) search formula evidence scope equalities local-equations protected
             (caddr provided) (cons result replies)))))
       (t (cons (h4-book-tactics-canonical-comparisons library equation) search))))))

(defun h4-book-tactics-reduction-in-scope (search formula evidence scope)
  (let* ((steps (table-values evidence))
         (proof (library-library-proof (h4-book-tactics-book-search-p search))))
    (h4-book-tactics-with-search-value
        (equalities (h4-book-tactics-reduction-equalities steps proof) search)
      (h4-book-tactics-with-search-value (protected (h4-book-tactics-reduction-protected steps nil) search)
        (h4-book-tactics-with-search-value
            (local-equations (h4-book-tactics-reduction-local-equations steps nil) search)
          (h4-book-tactics-reduction-loop 1000000 search formula evidence scope equalities
                                           local-equations protected nil nil))))))

(defun h4-book-tactics-book-search-reduction (search formula evidence)
  (h4-book-tactics-reduction-in-scope search formula evidence (list :external evidence)))

(defun h4-book-tactics-book-search-induction-rule (actual formal)
  (cond ((equal actual (list *library-car* formal)) (list *proof-consp* t 2))
        ((equal actual (list *library-cdr* formal)) (list *proof-consp* t 3))
        ((equal actual (library-plus formal *proof-neg-one*))
         (list *h4-book-arithmetic-zp* nil 8))
        ((equal actual (library-plus *proof-neg-one* formal))
         (list *h4-book-arithmetic-zp* nil 9))
        (t nil)))

(defun h4-book-tactics-induction-rules (calls index formal)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((actual (proof-term-at (termination-call-actuals (car calls)) index))
         (rest (h4-book-tactics-induction-rules (cdr calls) index formal)))
      (cons (h4-book-tactics-book-search-induction-rule actual formal) rest))))

(defun h4-book-tactics-induction-rules-agree-p (rules test holds)
  (declare (xargs :measure (acl2-count rules)))
  (or (endp rules)
      (and (car rules) (equal (caar rules) test) (equal (cadar rules) holds)
           (h4-book-tactics-induction-rules-agree-p (cdr rules) test holds))))

(defun h4-book-tactics-induction-changes (arguments actuals bindings changes)
  (declare (xargs :measure (acl2-count arguments)))
  (if (or (endp arguments) (endp actuals))
      changes
    (let ((before (car arguments)))
      (proof-with-checked-results
          ((change (if (or (proof-compound before) (assoc-equal before changes))
                       before
                     (proof-subst (car actuals) bindings))))
        (h4-book-tactics-induction-changes
         (cdr arguments) (cdr actuals) bindings
         (if (equal before change) changes (table-put changes before change)))))))

(defun h4-book-tactics-induction-cases (calls rules index argument arguments bindings)
  (declare (xargs :measure (acl2-count calls)))
  (if (or (endp calls) (endp rules))
      (cons nil nil)
    (let ((actuals (termination-call-actuals (car calls)))
          (builtin (caddar rules)))
      (proof-with-checked-results
          ((actual (proof-term-at actuals index))
           (child (proof-subst actual bindings))
           (changes (h4-book-tactics-induction-changes
                     arguments actuals bindings (list (cons argument child))))
           (rest (h4-book-tactics-induction-cases (cdr calls) (cdr rules) index argument
                                                 arguments bindings)))
        (cons (cons (list builtin (table-items changes)) (car rest))
              (cons (list builtin (list (list argument child))) (cdr rest)))))))

(defun h4-book-tactics-induction-options-at-index (index formals calls term bindings)
  (proof-with-checked-results ((argument (proof-term-at term (1+ index))))
    (if (proof-compound argument)
        nil
      (proof-with-checked-results
          ((formal (proof-term-at formals index))
           (rules (h4-book-tactics-induction-rules calls index formal)))
        (let ((test (caar rules))
              (holds (cadar rules)))
          (if (not (h4-book-tactics-induction-rules-agree-p rules test holds))
              nil
            (proof-with-checked-results
                ((cases (h4-book-tactics-induction-cases calls rules index argument (cdr term) bindings)))
              (list (list argument (list test argument) holds (proof-unique (car cases)))
                    (list argument (list test argument) holds (proof-unique (cdr cases)))))))))))

(defun h4-book-tactics-induction-options-at-indices (indices formals calls term bindings)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      nil
    (proof-with-checked-results
        ((first (h4-book-tactics-induction-options-at-index (car indices) formals calls term bindings))
         (rest (h4-book-tactics-induction-options-at-indices (cdr indices) formals calls term bindings)))
      (append first rest))))

(defun h4-book-tactics-bindings-map (pairs bindings)
  (declare (xargs :measure (acl2-count pairs)))
  (if (endp pairs)
      bindings
    (h4-book-tactics-bindings-map (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun h4-book-tactics-induction-options-at-term (search term definitions)
  (if (not (proof-compound term))
      nil
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (let ((definition (and (not (proof-compound head)) (assoc-equal head definitions))))
        (if (not definition)
            nil
          (proof-with-checked-results ((recursion (h4-book-tactics-book-search-recursion search head)))
            (let ((calls (car recursion))
                  (structural (cadr recursion))
                  (formals (cadr definition)))
              (if (not calls)
                  nil
                (h4-book-tactics-induction-options-at-indices
                 (if structural (list structural) (seq-range 0 (len formals) 1))
                 formals calls term (h4-book-tactics-bindings-map (seq-zip formals (cdr term)) nil))))))))))

(defun h4-book-tactics-induction-options-at-terms (search terms definitions)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((first (h4-book-tactics-induction-options-at-term search (car terms) definitions))
         (rest (h4-book-tactics-induction-options-at-terms search (cdr terms) definitions)))
      (append first rest))))

(defun h4-book-tactics-book-search-induction-options (search formula)
  (let* ((proof (library-library-proof (h4-book-tactics-book-search-p search)))
         (definitions (proof-proof-definitions proof)))
    (proof-with-checked-results
        ((options (h4-book-tactics-induction-options-at-terms
                   search (h4-book-tactics-terms formula) definitions)))
      (proof-unique options))))

(defun h4-book-tactics-countdown-candidates (options)
  (declare (xargs :measure (acl2-count options)))
  (cond ((endp options) nil)
        ((and (proof-is-call (cadar options) *h4-book-arithmetic-zp*)
              (equal (len (cadddr (car options))) 1))
         (cons (car options) (h4-book-tactics-countdown-candidates (cdr options))))
        (t (h4-book-tactics-countdown-candidates (cdr options)))))

(defun h4-book-tactics-countdown-compatible-p (bindings extra)
  (declare (xargs :measure (acl2-count extra)))
  (if (endp extra)
      t
    (let ((entry (assoc-equal (caar extra) bindings)))
      (and (or (not entry) (equal (cdr entry) (cadar extra)))
           (h4-book-tactics-countdown-compatible-p bindings (cdr extra))))))

(defun h4-book-tactics-countdown-plan (option others best)
  (declare (xargs :measure (acl2-count others)))
  (if (endp others)
      best
    (let* ((other (car others))
           (case (car (cadddr option)))
           (bindings (h4-book-tactics-bindings-map (cadr case) nil))
           (extra (cadr (car (cadddr other))))
           (compatible (and (not (equal (car option) (car other)))
                            (h4-book-tactics-countdown-compatible-p bindings extra)))
           (changes (and compatible (h4-book-tactics-bindings-map extra bindings)))
           (best-count (len (cadr (car (cadddr best))))))
      (h4-book-tactics-countdown-plan
       option (cdr others)
       (if (and compatible (or (not best) (> (len changes) best-count)))
           (list (car option) (cadr option) (caddr option)
                 (list (list (car case) (table-items changes))))
         best)))))

(defun h4-book-tactics-countdown-plans (options candidates best)
  (declare (xargs :measure (acl2-count options)))
  (if (endp options)
      best
    (h4-book-tactics-countdown-plans
     (cdr options) candidates (h4-book-tactics-countdown-plan (car options) candidates best))))

(defun h4-book-tactics-book-search-synchronized-countdown (options)
  (let ((candidates (h4-book-tactics-countdown-candidates options)))
    (h4-book-tactics-countdown-plans candidates candidates nil)))

(defun h4-book-tactics-solve-hypotheses (search premises)
  (let ((replies (h4-book-tactics-book-search-hypotheses-replies search)))
    (if (eq replies :default)
        (h4-book-tactics-book-search-hypotheses search premises)
      (let ((reply (assoc-equal premises replies)))
        (if reply
            (cdr reply)
          (list :h4-book-tactics-hypotheses-request premises))))))

(defun h4-book-tactics-solve-contradiction (entries evidence formula proof)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      nil
    (let ((opposite (assoc-equal (proof-neg (caar entries)) evidence)))
      (if (not opposite)
          (h4-book-tactics-solve-contradiction (cdr entries) evidence formula proof)
        (proof-with-checked-results ((contradiction (proof-proof-cut proof (cdar entries) (cdr opposite))))
          (proof-proof-subsume proof contradiction (cons formula (proof-step-clause contradiction))))))))

(defun h4-book-tactics-solve-evidence-answer (evidence formula proof)
  (let ((false (assoc-equal *proof-false* evidence)))
    (if false
        (proof-proof-subsume proof (cdr false) (cons formula (cdr (proof-step-clause (cdr false)))))
      (h4-book-tactics-solve-contradiction evidence evidence formula proof))))

(defun h4-book-tactics-equal-shared-test (value splits)
  (if (or (equal splits 0) (not (proof-is-call value *proof-equal*)))
      nil
    (proof-with-checked-results ((parts (proof-list-of-length value 3)))
      (let ((left (cadr parts))
            (right (caddr parts)))
        (if (not (and (proof-is-call left *proof-if*) (proof-is-call right *proof-if*)))
            nil
          (proof-with-checked-results ((test (proof-term-at left 1))
                                       (other (proof-term-at right 1)))
            (and (equal test other) (list test))))))))

(defun h4-book-tactics-arithmetic-terms-p (terms)
  (declare (xargs :measure (acl2-count terms)))
  (and (consp terms)
       (or (proof-is-call (car terms) *proof-plus*)
           (proof-is-call (car terms) *proof-minus*)
           (h4-book-tactics-arithmetic-terms-p (cdr terms)))))

(defun h4-book-tactics-solve-integers (terms value evidence search scope integers)
  (declare (xargs :measure (acl2-count terms)))
  (cond
   ((endp terms) (cons (reverse integers) search))
   ((equal (car terms) value)
    (h4-book-tactics-solve-integers (cdr terms) value evidence search scope integers))
   (t
    (h4-book-tactics-with-search-result
        (known search (h4-book-tactics-lookup-loop 1000000 search (library-integer (car terms)) evidence 1 scope))
      (h4-book-tactics-solve-integers (cdr terms) value evidence search scope
                                      (if known (cons known integers) integers))))))

(defun h4-book-tactics-linear-proof (library value integers equality)
  (proof-with-checked-results
      ((left (proof-term-at value 1))
       (right (proof-term-at value 2))
       (equation (library-library-linear-equal library left right integers)))
    (proof-proof-transport (library-library-proof library) equation equality)))

(defun h4-book-tactics-solve-linear (search value evidence scope equality)
  (if (not (and (h4-book-tactics-book-search-extended-rules search)
                (proof-is-call value *proof-equal*)))
      (cons nil search)
    (let ((terms (h4-book-tactics-terms value)))
      (if (not (h4-book-tactics-arithmetic-terms-p terms))
          (cons nil search)
        (h4-book-tactics-with-search-result
            (integers search (h4-book-tactics-solve-integers (proof-unique terms) value evidence search scope nil))
          (let ((attempt (h4-book-tactics-linear-proof
                          (h4-book-tactics-book-search-p search) value integers equality)))
            (cons (if (and (failure-p attempt)
                           (member-equal (cadr attempt)
                                         '("InapplicableTerm" "InapplicableStep" "value" "assertion")))
                      nil
                    attempt)
                  search)))))))

(defun h4-book-tactics-conditional-tests (terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (let ((conditional (proof-is-call (car terms) *proof-if*)))
      (proof-with-checked-results ((test (and conditional (proof-term-at (car terms) 1)))
                                   (rest (h4-book-tactics-conditional-tests (cdr terms))))
        (if conditional (cons test rest) rest)))))

(defun h4-book-tactics-unknown-tests (tests evidence)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      nil
    (let ((test (car tests)))
      (if (or (proof-is-call test *proof-quote*) (assoc-equal test evidence)
              (assoc-equal (proof-neg test) evidence))
          (h4-book-tactics-unknown-tests (cdr tests) evidence)
        (cons test (h4-book-tactics-unknown-tests (cdr tests) evidence))))))

(defun h4-book-tactics-solve-known-test (search tests evidence scope)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      (cons nil search)
    (h4-book-tactics-with-search-result
        (known search (h4-book-tactics-lookup-loop 1000000 search (car tests) evidence 1 scope))
      (if known
          (cons known search)
        (h4-book-tactics-with-search-result
            (denied search (h4-book-tactics-lookup-loop 1000000 search (proof-neg (car tests)) evidence 1 scope))
          (if denied
              (cons denied search)
            (h4-book-tactics-solve-known-test search (cdr tests) evidence scope)))))))

(defun h4-book-tactics-test-priority (test)
  (cond ((proof-is-call test *h4-book-arithmetic-zp*)
         (proof-with-checked-results ((argument (proof-term-at test 1)))
           (if (proof-compound argument) 1 0)))
        ((proof-is-call test *proof-if*) 3)
        (t 2)))

(defun h4-book-tactics-solve-branch (tests chosen priority)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      chosen
    (proof-with-checked-results ((next (h4-book-tactics-test-priority (car tests))))
      (if (< next priority)
          (h4-book-tactics-solve-branch (cdr tests) (car tests) next)
        (h4-book-tactics-solve-branch (cdr tests) chosen priority)))))

(mutual-recursion
 (defun h4-book-tactics-solve-loop (n search formula premises splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-solve-loop") search)
     (let* ((remaining (1- (h4-book-tactics-book-search-remaining search)))
            (search (h4-book-tactics-book-search-with-remaining search remaining))
            (proof (library-library-proof (h4-book-tactics-book-search-p search))))
       (if (< remaining 0)
           (cons '(:failure "Unproved" "") search)
         (h4-book-tactics-with-search-value (evidence (h4-book-tactics-solve-hypotheses search premises) search)
           (let* ((scoped (h4-book-tactics-book-search-begin-lookup-scope search))
                  (scope (car scoped))
                  (search (cdr scoped)))
             (h4-book-tactics-with-search-value
                 (immediate (h4-book-tactics-solve-evidence-answer evidence formula proof) search)
               (if immediate
                   (cons immediate search)
                 (h4-book-tactics-with-search-result
                     (known search (h4-book-tactics-lookup-loop 1000000 search formula evidence 2 scope))
                   (if known
                       (cons known search)
                     (h4-book-tactics-solve-form-loop (1- n) search formula premises splits
                                                      evidence scope)))))))))))

 (defun h4-book-tactics-solve-form-loop (n search formula premises splits evidence scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-solve-form-loop") search)
     (let* ((library (h4-book-tactics-book-search-p search))
            (proof (library-library-proof library))
            (implies (proof-is-call formula *library-implies*)))
       (h4-book-tactics-with-search-value
           (antecedent (and implies (proof-term-at formula 1)) search)
         (if (and implies (not (equal antecedent *proof-false*)))
             (h4-book-tactics-with-search-value (result (proof-term-at formula 2) search)
               (h4-book-tactics-with-search-value (assumed (proof-proof-assume proof antecedent t) search)
                 (h4-book-tactics-with-search-result
                     (conclusion search (h4-book-tactics-solve-loop (1- n) search result
                                                                   (append premises (list assumed)) splits))
                   (cons (h4-tactics-tactics-imply library formula conclusion) search))))
           (h4-book-tactics-with-search-value
               (tail (and (proof-is-call formula *proof-if*) (proof-term-at formula 3)) search)
             (if (not (equal tail *proof-false*))
                 (h4-book-tactics-solve-reduced-loop (1- n) search formula premises splits evidence scope)
               (h4-book-tactics-with-search-result
                   (first search (h4-book-tactics-solve-loop (1- n) search (cadr formula) premises splits))
                 (h4-book-tactics-with-search-result
                     (second search (h4-book-tactics-solve-loop (1- n) search (caddr formula)
                                                               (append premises (list first)) splits))
                   (cons (h4-tactics-tactics-conjunction library formula first second) search))))))))))

 (defun h4-book-tactics-solve-reduced-loop (n search formula premises splits evidence scope)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-solve-reduced-loop") search)
     (let* ((library (h4-book-tactics-book-search-p search))
            (proof (library-library-proof library)))
       (h4-book-tactics-with-search-result
           (equality search (h4-book-tactics-reduction-in-scope search formula evidence scope))
         (h4-book-tactics-with-search-value (value (h4-book-tactics-step-right equality) search)
           (h4-book-tactics-with-search-value (fits (h4-book-tactics-fits value 2500) search)
             (cond
              ((not fits) (cons '(:failure "Unproved" "") search))
              ((proof-is-call value *proof-quote*)
               (if (equal value *proof-false*)
                   (cons '(:failure "Unproved" "") search)
                 (cons (h4-tactics-tactics-non-nil library equality) search)))
              (t
               (h4-book-tactics-with-search-result
                   (known search (h4-book-tactics-lookup-loop 1000000 search value evidence 2 scope))
                 (if known
                     (cons (proof-proof-transport proof known equality) search)
                   (h4-book-tactics-with-search-value (shared (h4-book-tactics-equal-shared-test value splits) search)
                     (if (not shared)
                         (h4-book-tactics-solve-open-loop (1- n) search formula premises splits
                                                          evidence scope equality value)
                       (h4-book-tactics-with-search-result
                           (cases search (h4-book-tactics-solve-cases-loop (1- n) search value (car shared)
                                                                           premises (1- splits)))
                         (cons (proof-proof-transport proof cases equality) search))))))))))))))

 (defun h4-book-tactics-solve-open-loop (n search formula premises splits evidence scope equality value)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-solve-open-loop") search)
     (h4-book-tactics-with-search-result
         (linear search (h4-book-tactics-solve-linear search value evidence scope equality))
       (if linear
           (cons linear search)
         (h4-book-tactics-with-search-value
             (conditional (h4-book-tactics-conditional-tests (h4-book-tactics-terms value)) search)
           (let ((tests (h4-book-tactics-unknown-tests (proof-unique conditional) evidence)))
             (h4-book-tactics-with-search-result
                 (known search (h4-book-tactics-solve-known-test search tests evidence scope))
               (cond
                (known (h4-book-tactics-solve-loop (1- n) search formula
                                                   (append premises (list known)) splits))
                ((or (endp tests) (equal splits 0))
                 (cons '(:failure "Unproved" "") search))
                (t
                 (h4-book-tactics-with-search-value
                     (branch (h4-book-tactics-solve-branch tests nil 4) search)
                   (h4-book-tactics-solve-cases-loop (1- n) search formula branch premises
                                                     (1- splits))))))))))))

 (defun h4-book-tactics-solve-cases-loop (n search formula test premises splits)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-tactics-solve-cases-loop") search)
     (let* ((library (h4-book-tactics-book-search-p search))
            (proof (library-library-proof library)))
       (h4-book-tactics-with-search-value (positive (proof-proof-assume proof test t) search)
         (h4-book-tactics-with-search-result
             (yes search (h4-book-tactics-solve-loop (1- n) search formula
                                                    (append premises (list positive)) splits))
           (h4-book-tactics-with-search-value (negative (proof-proof-assume proof test nil) search)
             (h4-book-tactics-with-search-result
                 (no search (h4-book-tactics-solve-loop (1- n) search formula
                                                       (append premises (list negative)) splits))
               (cons (h4-tactics-tactics-case-of library formula test yes no) search)))))))))

(defun h4-book-tactics-book-search-solve (search formula premises splits)
  (h4-book-tactics-solve-loop 1000000 search formula premises splits))

(defun h4-book-tactics-induction-tests (cases formula argument library)
  (declare (xargs :measure (acl2-count cases)))
  (if (endp cases)
      nil
    (proof-with-checked-results
        ((descent (library-library-builtin library (caar cases) argument))
         (literal (proof-step-first descent))
         (instance (proof-subst formula (h4-book-tactics-bindings-map (cadar cases) nil)))
         (rest (h4-book-tactics-induction-tests (cdr cases) formula argument library)))
      (cons (list descent (proof-ite literal instance *proof-true*)) rest))))

(defun h4-book-tactics-induction-hypotheses (tests active proof)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((guard (proof-proof-assume proof (cadar tests) t))
         (evidence (proof-proof-discharge proof (caar tests) active))
         (step (proof-proof-prove-if proof guard evidence))
         (rest (h4-book-tactics-induction-hypotheses (cdr tests) active proof)))
      (cons step rest))))

(defun h4-book-tactics-book-search-induction-step (active search formula tests splits)
  (let ((proof (library-library-proof (h4-book-tactics-book-search-p search))))
    (h4-book-tactics-with-search-value
        (hypotheses (h4-book-tactics-induction-hypotheses tests active proof) search)
      (h4-book-tactics-book-search-solve
       search formula (append (h4-book-tactics-book-search-given search) (cons active hypotheses)) splits))))

(defun h4-book-tactics-book-search-induction-base (inactive search formula splits)
  (h4-book-tactics-book-search-solve
   search formula (append (h4-book-tactics-book-search-given search) (list inactive)) splits))

(defun h4-book-tactics-induction-substitutions (cases)
  (declare (xargs :measure (acl2-count cases)))
  (if (endp cases)
      nil
    (cons (cadar cases) (h4-book-tactics-induction-substitutions (cdr cases)))))

(defun h4-book-tactics-book-search-induction (search formula argument branch holds cases splits)
  (let* ((library (h4-book-tactics-book-search-p search))
         (proof (library-library-proof library)))
    (h4-book-tactics-with-search-value
        (tests (h4-book-tactics-induction-tests cases formula argument library) search)
      (h4-book-tactics-with-search-value (positive (proof-proof-assume proof branch t) search)
        (h4-book-tactics-with-search-result
            (yes search (if holds
                            (h4-book-tactics-book-search-induction-step positive search formula tests splits)
                          (h4-book-tactics-book-search-induction-base positive search formula splits)))
          (h4-book-tactics-with-search-value (negative (proof-proof-assume proof branch nil) search)
            (h4-book-tactics-with-search-result
                (no search (if holds
                               (h4-book-tactics-book-search-induction-base negative search formula splits)
                             (h4-book-tactics-book-search-induction-step negative search formula tests splits)))
              (h4-book-tactics-with-search-value
                  (case (h4-tactics-tactics-case-of library formula branch yes no) search)
                (h4-book-tactics-with-search-value (ordinal (library-library-builtin library 1 argument) search)
                  (cons (proof-proof-induct proof ordinal case formula (list *library-count* argument)
                                            (h4-book-tactics-induction-substitutions cases))
                        search))))))))))

(defun h4-book-tactics-retry-proof-p (value)
  (and (failure-p value)
       (member-equal (cadr value) '("Unproved" "InapplicableStep" "assertion" "recursion"))))

(defun h4-book-tactics-prove-direct (search formula given)
  (h4-book-tactics-with-search-result (step search (h4-book-tactics-book-search-solve search formula given 3))
    (let ((proof (library-library-proof (h4-book-tactics-book-search-p search))))
      (cons (proof-proof-subsume proof step (list formula)) search))))

(defun h4-book-tactics-prove-plan (search formula plan)
  (h4-book-tactics-book-search-induction
   search formula (car plan) (cadr plan) (caddr plan) (cadddr plan) 3))

(defun h4-book-tactics-prove-plans (search formula plans)
  (declare (xargs :measure (acl2-count plans)))
  (if (endp plans)
      (cons nil search)
    (let ((attempt (hide (h4-book-tactics-prove-plan
                          (h4-book-tactics-book-search-with-budgets search 24 2400)
                          formula (car plans)))))
      (if (hide (h4-book-tactics-retry-proof-p (car attempt)))
          (h4-book-tactics-prove-plans (cdr attempt) formula (cdr plans))
        attempt))))

(defun h4-book-tactics-prove-inductions (search formula plans extended)
  (if (not (eq plans :none))
      (let ((attempt (h4-book-tactics-prove-plans search formula plans)))
        (list (car attempt) (cdr attempt) plans))
    (let ((options (h4-book-tactics-book-search-induction-options search formula)))
      (if (failure-p options)
          (list options search plans)
        (let ((plans (seq-slice options 0 5))
              (simultaneous (h4-book-tactics-book-search-synchronized-countdown options)))
          (if (not simultaneous)
              (let ((attempt (h4-book-tactics-prove-plans search formula plans)))
                (list (car attempt) (cdr attempt) plans))
            (let* ((search (h4-book-tactics-book-search-with-extended search t))
                   (attempt (h4-book-tactics-prove-plan
                             (h4-book-tactics-book-search-with-budgets search 28 3000)
                             formula simultaneous)))
              (if (h4-book-tactics-retry-proof-p (car attempt))
                  (let* ((search (h4-book-tactics-book-search-with-extended (cdr attempt) extended))
                         (regular (h4-book-tactics-prove-plans search formula plans)))
                    (list (car regular) (cdr regular) plans))
                (list (car attempt) (cdr attempt) plans)))))))))

(defun h4-book-tactics-prove-levels (search formula given plans levels)
  (declare (xargs :measure (acl2-count levels)))
  (if (endp levels)
      (cons '(:failure "Unproved" "") search)
    (let* ((extended (car levels))
           (search (h4-book-tactics-book-search-with-extended search extended))
           (direct (hide (h4-book-tactics-prove-direct
                           (h4-book-tactics-book-search-with-budgets search 20 2400) formula given))))
      (if (not (hide (h4-book-tactics-retry-proof-p (car direct))))
          direct
        (let ((induced (hide (h4-book-tactics-prove-inductions (cdr direct) formula plans extended))))
          (if (hide (car induced))
              (cons (car induced) (cadr induced))
            (h4-book-tactics-prove-levels (cadr induced) formula given (caddr induced) (cdr levels))))))))

(defun h4-book-tactics-prove-large (search formula)
  (let ((failure '(:failure "Unproved" "")))
    (if (not (proof-is-call formula *proof-equal*))
        failure
      (proof-with-checked-results ((right (proof-term-at formula 2)))
        (if (equal (cadr formula) right)
            (proof-proof-reflexive (library-library-proof (h4-book-tactics-book-search-p search)) right)
          failure)))))

(defun h4-book-tactics-book-search-prove (search formula induction given)
  (h4-book-tactics-with-search-value (fits (h4-book-tactics-fits formula 2600) search)
    (if (not fits)
        (cons (h4-book-tactics-prove-large search formula) search)
      (h4-book-tactics-prove-levels (h4-book-tactics-book-search-with-given search given)
                                    formula given (if induction :none nil) '(nil t)))))
