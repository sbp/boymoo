(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun h2-search-data-text (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond ((or (consp value) (null value))
          (concatenate 'string "(" (text-join " " (h2-search-data-items value)) ")"))
         ((stringp value)
          (concatenate 'string "\"" (text-replace (text-replace value "\\" "\\\\") "\"" "\\\"") "\""))
         ((integerp value) (decimal-text value))
         ((rationalp value)
          (concatenate 'string (decimal-text (numerator value)) "/" (decimal-text (denominator value))))
         (t "t")))
 (defun h2-search-data-items (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (cons (h2-search-data-text (car items)) (h2-search-data-items (cdr items))))))

(defun h2-search-set-insert-at (item text items)
  (cond ((endp items) (list item))
        ((equal item (car items)) items)
        ((string< text (h2-search-data-text (car items))) (cons item items))
        (t (cons (car items) (h2-search-set-insert-at item text (cdr items))))))

(defun h2-search-set-insert (item items)
  (h2-search-set-insert-at item (h2-search-data-text item) items))

(defun h2-search-set (items result)
  (if (endp items)
      result
    (h2-search-set (cdr items) (h2-search-set-insert (car items) result))))

; A tree node contains an entry, its height, and its left and right subtrees.
(defun h2-search-index-precedes-p (key other)
  (if (and (stringp key) (stringp other))
      (string< key other)
    (lexorder key other)))

(defun h2-search-index-height (tree)
  (nfix (cadr tree)))

(defun h2-search-index-node (entry left right)
  (cons entry
        (cons (1+ (max (h2-search-index-height left)
                       (h2-search-index-height right)))
              (cons left right))))

(defun h2-search-index-rotate-left (entry left right)
  (h2-search-index-node (car right)
                       (h2-search-index-node entry left (caddr right))
                       (cdddr right)))

(defun h2-search-index-rotate-right (entry left right)
  (h2-search-index-node (car left)
                       (caddr left)
                       (h2-search-index-node entry (cdddr left) right)))

(defun h2-search-index-balance (entry left right)
  (let ((left-height (h2-search-index-height left))
        (right-height (h2-search-index-height right)))
    (cond ((< (1+ right-height) left-height)
           (h2-search-index-rotate-right
            entry
            (if (< (h2-search-index-height (caddr left))
                   (h2-search-index-height (cdddr left)))
                (h2-search-index-rotate-left (car left) (caddr left) (cdddr left))
              left)
            right))
          ((< (1+ left-height) right-height)
           (h2-search-index-rotate-left
            entry
            left
            (if (< (h2-search-index-height (cdddr right))
                   (h2-search-index-height (caddr right)))
                (h2-search-index-rotate-right (car right) (caddr right) (cdddr right))
              right)))
          (t (h2-search-index-node entry left right)))))

(defun h2-search-index-put (key value tree)
  (cond ((atom tree) (h2-search-index-node (cons key value) nil nil))
        ((equal key (caar tree))
         (if (or value (cdar tree))
             (cons (cons key value) (cdr tree))
           tree))
        ((h2-search-index-precedes-p key (caar tree))
         (h2-search-index-balance (car tree)
                                  (h2-search-index-put key value (caddr tree))
                                  (cdddr tree)))
        (t (h2-search-index-balance (car tree)
                                   (caddr tree)
                                   (h2-search-index-put key value (cdddr tree))))))

(defun h2-search-index-find (key tree)
  (cond ((atom tree) nil)
        ((equal key (caar tree)) (car tree))
        ((h2-search-index-precedes-p key (caar tree)) (h2-search-index-find key (caddr tree)))
        (t (h2-search-index-find key (cdddr tree)))))

(defun h2-search-index-values (tree tail)
  (if (atom tree)
      tail
    (h2-search-index-values
     (caddr tree)
     (cons (cdar tree) (h2-search-index-values (cdddr tree) tail)))))

(defun h2-search-index-from-reversed-alist (entries tree)
  (if (endp entries)
      tree
    (let ((entry (car entries)))
      (h2-search-index-from-reversed-alist
       (cdr entries)
       (if (consp entry) (h2-search-index-put (car entry) (cdr entry) tree) tree)))))

(defun h2-search-seen-p (term seen)
  (if (eq (car seen) :h2-indexed-seen)
      (h2-search-index-find term (cdr seen))
    (member-equal term seen)))

(defun h2-search-seen-add (term seen)
  (if (eq (car seen) :h2-indexed-seen)
      (cons :h2-indexed-seen (h2-search-index-put term nil (cdr seen)))
    (h2-search-set-insert term seen)))

(defconst *h2-search-return-last* (proof-sym "RETURN-LAST" "ACL2"))
(defconst *h2-search-characterp* (proof-cl "CHARACTERP"))
(defconst *h2-search-symbolp* (proof-cl "SYMBOLP"))
(defconst *h2-search-symbol-name* (proof-cl "SYMBOL-NAME"))
(defconst *h2-search-package-name* (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
(defconst *h2-search-char-code* (proof-cl "CHAR-CODE"))
(defconst *h2-search-code-char* (proof-cl "CODE-CHAR"))
(defconst *h2-search-string-less* (proof-cl "STRING<"))

(defconst *h2-search-transparent*
  (h2-search-set
   (list (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ") (proof-cl "EQL")
         (proof-cl "NULL") (proof-cl "=") *h2-search-return-last*
         (proof-sym "IFF" "ACL2") *library-implies*)
   nil))

(defconst *h2-search-type-facts*
  '("INTEGER-IMPLIES-RATIONAL" "rationalp-acl2-numberp" "consp-cons" "consp-not-acl2-numberp"
    "consp-not-characterp" "consp-not-stringp" "consp-not-symbolp"
    "acl2-numberp-not-characterp" "acl2-numberp-not-symbolp"
    "characterp-not-symbolp" "stringp-not-symbolp" "characterp-not-stringp"
    "acl2-numberp-not-stringp" "stringp-symbol-name" "STRINGP-SYMBOL-PACKAGE-NAME"
    "integerp-char-code" "char-code-non-negative" "CHAR-CODE-LINEAR"
    "CODE-CHAR-TYPE" "CHARACTER-LISTP-COERCE" "stringp-coerce"))

(mutual-recursion
 (defun h2-search-collect-variables (term found)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (h2-search-set-insert term found))
         ((or (endp term) (proof-is-call term *proof-quote*)) found)
         (t (h2-search-collect-variable-arguments (cdr term) found))))
 (defun h2-search-collect-variable-arguments (terms found)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       found
     (h2-search-collect-variable-arguments
      (cdr terms) (h2-search-collect-variables (car terms) found)))))

(defun h2-search-variables (term)
  (h2-search-collect-variables term nil))

(mutual-recursion
 (defun h2-search-match (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond ((not (proof-compound pattern))
          (let ((binding (assoc-equal pattern bindings)))
            (if binding
                (cons (equal (cdr binding) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((proof-is-call pattern *proof-quote*)
          (cons (equal pattern term) bindings))
         ((and (consp pattern) (consp term) (proof-compound term)
               (equal (len pattern) (len term)) (equal (car pattern) (car term)))
          (h2-search-match-arguments (cdr pattern) (cdr term) bindings))
         (t (cons nil bindings))))
 (defun h2-search-match-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (let ((matched (h2-search-match (car patterns) (car terms) bindings)))
       (if (car matched)
           (h2-search-match-arguments (cdr patterns) (cdr terms) (cdr matched))
         matched)))))

(defun h2-search-head (term)
  (if (proof-compound term) (proof-term-at term 0) nil))

(mutual-recursion
 (defun h2-search-size (term)
   (declare (xargs :measure (acl2-count term)))
   (if (and (consp term) (proof-compound term) (not (proof-is-call term *proof-quote*)))
       (1+ (h2-search-size-arguments (cdr term)))
     1))
 (defun h2-search-size-arguments (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       0
     (+ (h2-search-size (car terms)) (h2-search-size-arguments (cdr terms))))))

(defun h2-search-opposite (term)
  (if (proof-is-call term *proof-not*) (proof-term-at term 1) (proof-neg term)))

(defun h2-search-antecedents (term)
  (declare (xargs :measure (acl2-count term)))
  (cond ((proof-is-call term *proof-if*)
         (if (endp (cdddr term))
             '(:failure "TacticInapplicable" "")
           (if (equal (cadddr term) *proof-false*)
               (proof-with-checked-results
                ((yes (h2-search-antecedents (cadr term)))
                 (no (h2-search-antecedents (caddr term))))
                (append yes no))
             (list term))))
        ((equal term *proof-true*) nil)
        (t (list term))))

(defun h2-search-rule-name (rule) (cadr rule))
(defun h2-search-rule-pattern (rule) (caddr rule))
(defun h2-search-rule-action (rule) (cadddr rule))
(defun h2-search-rule-conditions (rule) (car (cddddr rule)))
(defun h2-search-rule-required (rule) (cadr (cddddr rule)))
(defun h2-search-rule-id (rule) (caddr (cddddr rule)))

(defun h2-search-rule-with-id (rule id)
  (list :h2-rule (h2-search-rule-name rule) (h2-search-rule-pattern rule)
        (h2-search-rule-action rule) (h2-search-rule-conditions rule)
        (h2-search-rule-required rule) id))

(defun h2-search-rule-init (name pattern action conditions)
  (list :h2-rule name pattern action conditions
        (h2-search-collect-variable-arguments conditions (h2-search-variables pattern)) nil))

(defun h2-search-object-p (search)
  (and (consp search) (eq (car search) :h2-search)))

(defun h2-search-search-library (search)
  (if (h2-search-object-p search) (cadr search) search))

(defun h2-search-proof (search)
  (descent-proof (h2-search-search-library search)))

(defun h2-search-rule-from-fact-descend (formula action conditions name)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((proof-is-call formula *library-implies*)
    (if (endp (cddr formula))
        '(:failure "TacticInapplicable" "")
      (let ((test (cadr formula)))
        (proof-with-checked-results ((antecedents (h2-search-antecedents test)))
          (h2-search-rule-from-fact-descend
           (caddr formula) (append action (list (list "implies" test)))
           (append conditions antecedents) name)))))
   ((proof-is-call formula *proof-if*)
    (cond ((endp (cdddr formula)) '(:failure "TacticInapplicable" ""))
          ((equal (cadddr formula) *proof-false*)
           (proof-with-checked-results
            ((first (h2-search-rule-from-fact-descend
                     (cadr formula) (append action '(("conjunct" 1))) conditions name))
             (second (h2-search-rule-from-fact-descend
                      (caddr formula) (append action '(("conjunct" 2))) conditions name)))
            (append first second)))
          (t (list (h2-search-rule-init name formula action conditions)))))
   (t (list (h2-search-rule-init name formula action conditions)))))

(defun h2-search-cut-conditions (sides)
  (if (endp sides)
      nil
    (proof-with-checked-results ((condition (h2-search-opposite (car sides)))
                                 (rest (h2-search-cut-conditions (cdr sides))))
      (cons condition rest))))

(defun h2-search-cut-actions (conditions)
  (if (endp conditions)
      nil
    (cons (list "cut" (car conditions)) (h2-search-cut-actions (cdr conditions)))))

(defun h2-search-identify-rules (rules origin index)
  (if (endp rules)
      nil
    (cons (h2-search-rule-with-id (car rules) (list origin index))
          (h2-search-identify-rules (cdr rules) origin (1+ index)))))

(defun h2-search-rule-from-fact (proof name)
  (let* ((key (if (stringp name) (list "str" name) name))
         (entry (assoc-equal key (proof-proof-facts (h2-search-proof proof)))))
    (cond ((not entry) '(:failure "TacticInapplicable" ""))
          ((endp (cdr entry))
           '(:failure "TacticInapplicable" ""))
          (t (proof-with-checked-results
              ((conditions (h2-search-cut-conditions (cddr entry)))
               (rules (h2-search-rule-from-fact-descend
                       (cadr entry) (h2-search-cut-actions conditions) conditions name)))
              (h2-search-identify-rules rules (list :fact name) 0))))))

(defun h2-search-rule-active-p (rule active)
  (and (consp active)
       (or (and (car active)
                (if (h2-search-rule-id rule)
                    (equal (h2-search-rule-id rule) (h2-search-rule-id (car active)))
                  (equal rule (car active))))
           (h2-search-rule-active-p rule (cdr active)))))

(defun h2-search-context-literals (context) (cadr context))
(defun h2-search-context-equalities (context) (caddr context))
(defun h2-search-context-representatives (context) (cadddr context))
(defun h2-search-context-tests (context) (car (cddddr context)))
(defun h2-search-context-contradiction (context) (cadr (cddddr context)))
(defun h2-search-context-reductions (context) (caddr (cddddr context)))
(defun h2-search-context-deductions (context) (cadddr (cddddr context)))

(defun h2-search-context-init ()
  (list :h2-context nil nil nil nil nil nil nil))

(defun h2-search-indexed-context-init ()
  (list :h2-indexed-context nil nil nil nil nil nil nil))

(defun h2-search-indexed-context-p (context)
  (eq (car context) :h2-indexed-context))

(defun h2-search-context-cache-find (context key table)
  (if (h2-search-indexed-context-p context)
      (h2-search-index-find key table)
    (assoc-equal key table)))

(defun h2-search-context-cache-put (context key value table)
  (if (h2-search-indexed-context-p context)
      (h2-search-index-put key value table)
    (table-put table key value)))

(defun h2-search-context-representative-p (context term)
  (let ((set (h2-search-context-representatives context)))
    (if (h2-search-indexed-context-p context)
        (h2-search-index-find term set)
      (member-equal term set))))

(defun h2-search-context-add-representative (context term)
  (let ((set (h2-search-context-representatives context)))
    (if (h2-search-indexed-context-p context)
        (h2-search-index-put term nil set)
      (h2-search-set-insert term set))))

(defun h2-search-context-with-contradiction (context contradiction)
  (update-nth 5 contradiction context))

(defun h2-search-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h2-search-context-not-contradiction (proof literal step context)
  (let ((other (cdr (assoc-equal (proof-neg literal) (h2-search-context-literals context)))))
    (cond ((or (h2-search-context-contradiction context) other)
           (if (h2-search-context-contradiction context)
               (h2-search-context-contradiction context)
             (proof-proof-cut proof step other)))
          ((proof-is-call literal *proof-not*)
           (proof-with-checked-results ((positive (proof-term-at literal 1)))
             (let ((other (cdr (assoc-equal positive (h2-search-context-literals context)))))
               (if other (proof-proof-cut proof other step) nil))))
          (t nil))))

(defun h2-search-equality-reversed-p (left right)
  (cond ((proof-is-call left *proof-quote*) t)
        ((proof-is-call right *proof-quote*) nil)
        (t (let ((left-size (h2-search-size left)))
             (proof-with-checked-results ((left-text (proof-write left)))
               (let ((right-size (h2-search-size right)))
                 (proof-with-checked-results ((right-text (proof-write right)))
                   (or (< left-size right-size)
                       (and (equal left-size right-size) (if (string< left-text right-text) t nil))))))))))

(defun h2-search-context-add-equality (proof literal step context)
  (if (not (proof-is-call literal *proof-equal*))
      context
    (proof-with-checked-results ((parts (proof-list-of-length (cdr literal) 2)))
      (let ((left (car parts)) (right (cadr parts)))
        (if (or (equal left right)
                (and (proof-is-call left *proof-quote*) (proof-is-call right *proof-quote*)))
            context
          (proof-with-checked-results
           ((reversed (h2-search-equality-reversed-p left right))
            (equality (if reversed (proof-proof-symmetric proof step) step)))
           (update-nth 3 (h2-search-context-add-representative context (if reversed left right))
                       (update-nth 2 (table-put (h2-search-context-equalities context)
                                                  (if reversed right left) equality)
                                   context))))))))

(defun h2-search-context-add (context proof step)
  (let ((proof (h2-search-proof proof)))
    (proof-with-checked-results ((literal (proof-step-first step)))
      (let ((literals (h2-search-context-literals context)))
        (if (or (assoc-equal literal literals) (equal literal *proof-true*))
            (cons nil context)
          (let ((context (update-nth 7 nil
                                     (update-nth 6 nil
                                                 (update-nth 1 (table-put literals literal step) context)))))
            (proof-with-checked-results
             ((contradiction (if (equal literal *proof-false*)
                                 (proof-proof-tidy proof step)
                               (h2-search-context-not-contradiction proof literal step context)))
              (context (h2-search-context-add-equality
                        proof literal step (h2-search-context-with-contradiction context contradiction))))
             (cons t context))))))))

(defun h2-search-context-test (context term)
  (declare (xargs :measure (acl2-count term)))
  (let ((value (if (proof-is-call term *proof-not*) (proof-term-at term 1) term)))
    (cond ((and (proof-is-call term *proof-not*) (endp (cdr term))) value)
          ((proof-is-call value *proof-if*)
           (if (endp (cdr value))
               '(:failure "TacticInapplicable" "")
             (h2-search-context-test context (cadr value))))
          ((or (assoc-equal value (h2-search-context-literals context))
               (assoc-equal (proof-neg value) (h2-search-context-literals context))
               (proof-is-call value *proof-quote*))
           context)
          (t (update-nth 4 (table-put (h2-search-context-tests context) value nil) context)))))

(defun h2-search-completion-next (n rule literals pending)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h2-search-completion-next")
    (if (endp pending)
        nil
      (let* ((task (car pending)) (bindings (cadr task)) (rest (cdr pending)))
        (case (car task)
          (:bindings
           (let ((missing (set-difference-equal (h2-search-rule-required rule) (table-keys bindings))))
             (if (endp missing)
                 (cons bindings rest)
               (h2-search-completion-next
                (1- n) rule literals
                (cons (list :conditions bindings missing (h2-search-rule-conditions rule)) rest)))))
          (:conditions
           (let ((missing (caddr task)) (conditions (cadddr task)))
             (if (endp conditions)
                 (h2-search-completion-next (1- n) rule literals rest)
               (let* ((test (car conditions))
                      (rest (cons (list :conditions bindings missing (cdr conditions)) rest)))
                 (h2-search-completion-next
                  (1- n) rule literals
                  (if (and (proof-compound test) (intersectp-equal (h2-search-variables test) missing))
                      (cons (list :literals bindings test literals) rest)
                    rest))))))
          (otherwise
           (let ((test (caddr task)) (known (cadddr task)))
             (if (endp known)
                 (h2-search-completion-next (1- n) rule literals rest)
               (let* ((candidate (h2-search-match test (caar known) bindings))
                      (rest (cons (list :literals bindings test (cdr known)) rest)))
                 (h2-search-completion-next
                  (1- n) rule literals
                  (if (car candidate) (cons (list :bindings (cdr candidate)) rest) rest)))))))))))

(defun h2-search-rule-completions (n rule literals pending found)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h2-search-rule-completions")
    (proof-with-checked-results ((next (h2-search-completion-next n rule literals pending)))
      (if next
          (h2-search-rule-completions (1- n) rule literals (cdr next) (cons (car next) found))
        (reverse found)))))

(defun h2-search-rule-complete (rule bindings context)
  (h2-search-rule-completions 1000000 rule (h2-search-context-literals context)
                              (list (list :bindings bindings)) nil))

(defun h2-search-search-init (library)
  (list :h2-search library nil nil :none nil nil nil nil))

(defun h2-search-search-indexes (search)
  (let ((field (and (h2-search-object-p search) (nth 11 search))))
    (and (eq (car field) :h2-search-indexes) (cdr field))))

(defun h2-search-search-with-indexes (search)
  (let ((indexes (h2-search-search-indexes search)))
    (if (and (consp indexes) (not (eq (cdr indexes) :unprepared)))
        search
      (update-nth 11
                  (cons :h2-search-indexes
                        (cons (if (consp indexes) (car indexes) (len search))
                              (h2-search-index-from-reversed-alist
                               (reverse (proof-proof-facts (h2-search-proof search))) nil)))
                  search))))

(defun h2-search-search-without-indexes (search)
  (let ((indexes (h2-search-search-indexes search)))
    (if (consp indexes) (take (car indexes) search) search)))

(defun h2-search-search-with-library (search library)
  (if (h2-search-object-p search)
      (let ((indexes (h2-search-search-indexes search))
            (updated (update-nth 1 library search)))
        (if (consp indexes)
            (update-nth 11 (cons :h2-search-indexes (cons (car indexes) :unprepared)) updated)
          updated))
    library))

(defun h2-search-indexed-fact (search name bindings)
  (let ((indexes (h2-search-search-indexes search))
        (proof (h2-search-proof search)))
    (if (and (consp indexes) (not (eq (cdr indexes) :unprepared)))
        (let* ((key (if (stringp name) (list "str" name) name))
               (entry (h2-search-index-find key (cdr indexes))))
          (if entry
              (proof-proof-instantiate proof (proof-make-step "fact" (list key) (cdr entry)) bindings)
            '(:failure "TacticInapplicable" "")))
      (proof-proof-fact proof name bindings))))

(defun h2-search-search-opened (search)
  (and (h2-search-object-p search) (caddr search)))

(defun h2-search-search-repeat (search)
  (and (h2-search-object-p search) (cadddr search)))

(defun h2-search-search-split-limit (search)
  (if (h2-search-object-p search) (car (cddddr search)) :none))

(defun h2-search-search-rule-heads (search)
  (and (h2-search-object-p search) (cadr (cddddr search))))

(defun h2-search-search-rewrite-heads (search)
  (and (h2-search-object-p search) (caddr (cddddr search))))

(defun h2-search-search-hooks (search)
  (and (h2-search-object-p search) (cadddr (cddddr search))))

(defun h2-search-search-replies (search)
  (and (h2-search-object-p search) (car (cddddr (cddddr search)))))

(defun h2-search-search-with-configuration (search opened repeat split-limit)
  (let ((search (if (h2-search-object-p search) search (h2-search-search-init search))))
    (update-nth 4 split-limit
                (update-nth 3 (h2-search-set repeat nil)
                            (update-nth 2 (h2-search-set opened nil) search)))))

(defun h2-search-search-with-hooks (search hooks)
  (update-nth 7 hooks (if (h2-search-object-p search) search (h2-search-search-init search))))

(defun h2-search-search-with-replies (search replies)
  (update-nth 8 replies (if (h2-search-object-p search) search (h2-search-search-init search))))

(defun h2-search-not-nil-dependencies (proof)
  (let ((facts (proof-proof-facts proof))
        (primitives (proof-proof-primitives proof)))
    (list (assoc-equal *proof-not* (proof-proof-definitions proof))
          (assoc-equal *proof-not* facts)
          (assoc-equal '("str" "non-nil-true") facts)
          (if (member-equal *proof-if* primitives) t nil)
          (if (member-equal *proof-equal* primitives) t nil))))

(defun h2-search-search-prepare-not-nil (search)
  (let ((proof (h2-search-proof search)))
    (update-nth 10 (cons (h2-search-not-nil-dependencies proof) (proof-proof-not-nil proof)) search)))

(defun h2-search-not-nil-in-proof (search proof)
  (let ((prepared (and (h2-search-object-p search) (nth 10 search))))
    (if (and (consp prepared) (equal (car prepared) (h2-search-not-nil-dependencies proof)))
        (cdr prepared)
      (proof-proof-not-nil proof))))

(defun h2-search-search-not-nil (search)
  (h2-search-not-nil-in-proof search (h2-search-proof search)))

(defun h2-search-excluded-middle (search term)
  (let ((proof (h2-search-proof search)))
    (proof-with-checked-results
        ((not-nil (h2-search-not-nil-in-proof search proof))
         (nil-or-true (proof-proof-nil-or-true proof term))
         (reversed (proof-proof-symmetric proof nil-or-true))
         (rewritten (proof-proof-rewrite proof not-nil reversed '(1 1))))
      (proof-proof-tidy proof rewritten))))

(defun h2-search-request-p (value)
  (and (consp value) (eq (car value) :h2-search-request)))

(defun h2-search-request-phase (request) (cadr request))
(defun h2-search-request-method (request) (caddr request))
(defun h2-search-request-args (request) (cadddr request))
(defun h2-search-request-result (request) (car (cddddr request)))

(defun h2-search-add-index-rule (index key rule)
  (table-put index key (append (cdr (assoc-equal key index)) (list rule))))

(defun h2-search-index-rules (rules claims rewrites)
  (if (endp rules)
      (cons claims rewrites)
    (let* ((rule (car rules)) (pattern (h2-search-rule-pattern rule)))
      (proof-with-checked-results ((key (h2-search-head pattern)))
        (let ((claims (h2-search-add-index-rule claims key rule)))
          (if (not (proof-is-call pattern *proof-equal*))
              (h2-search-index-rules (cdr rules) claims rewrites)
            (proof-with-checked-results ((left (proof-term-at pattern 1)))
              (if (not (proof-compound left))
                  (h2-search-index-rules (cdr rules) claims rewrites)
                (proof-with-checked-results ((key (h2-search-head left)))
                  (h2-search-index-rules (cdr rules) claims (h2-search-add-index-rule rewrites key rule)))))))))))

(defun h2-search-index-facts (search names claims rewrites)
  (if (endp names)
      (cons claims rewrites)
    (let* ((original (car names))
           (name (if (and (stringp original) (equal original (text-upper original))
                          (not (equal original (text-lower original))))
                     (proof-sym original "ACL2")
                   original)))
      (proof-with-checked-results
       ((rules (h2-search-rule-from-fact search name))
        (indexes (h2-search-index-rules (h2-search-identify-rules rules (list :configured original) 0)
                                         claims rewrites)))
       (h2-search-index-facts search (cdr names) (car indexes) (cdr indexes))))))

(defun h2-search-search-configure (search definitions facts repeat split-limit)
  (let* ((search (if (h2-search-search-indexes search)
                     (h2-search-search-with-indexes search)
                   search))
         (search (h2-search-search-with-configuration
                  search (append *h2-search-transparent* definitions) repeat split-limit)))
    (proof-with-checked-results
     ((indexes (h2-search-index-facts search (proof-unique (append *h2-search-type-facts* facts)) nil nil)))
     (update-nth 6 (cdr indexes) (update-nth 5 (car indexes) search)))))

(defun h2-search-search-nil-value (search evidence)
  (let ((proof (h2-search-proof search)))
    (proof-with-checked-results
     ((value (h2-search-step-at evidence 1))
      (clause (proof-proof-nil-or-true proof value))
      (front (proof-proof-front proof clause value))
      (result (proof-proof-cut proof front evidence)))
     (proof-proof-tidy proof result))))

(defun h2-search-search-deny (search evidence)
  (let ((proof (h2-search-proof search)))
    (proof-with-checked-results
     ((literal (proof-step-first evidence))
      (opened (proof-proof-unfold proof (proof-neg literal)))
      (value (h2-search-step-at opened 2))
      (selected (proof-proof-select proof value evidence))
      (equality (proof-proof-chain proof opened (list selected)))
      (not-nil (h2-search-not-nil-in-proof search proof)))
     (library-library-transport-argument (h2-search-search-library search) not-nil equality 1))))

(defun h2-search-lookup-denial (search term literals)
  (if (not (proof-is-call term *proof-not*))
      nil
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (cond ((proof-is-call argument *proof-not*)
             (proof-with-checked-results ((positive (proof-term-at argument 1)))
               (let ((evidence (cdr (assoc-equal positive literals))))
                 (if evidence (h2-search-search-deny search evidence) nil))))
            ((proof-is-call argument *proof-equal*)
             (proof-with-checked-results ((parts (proof-list-of-length argument 3)))
               (let* ((proof (h2-search-proof search))
                      (left (cadr parts)) (right (caddr parts))
                      (evidence (cdr (assoc-equal (proof-neg (proof-eq right left)) literals))))
                 (if (not evidence)
                     nil
                   (proof-with-checked-results
                    ((assumed (proof-proof-assume proof (proof-eq left right) t))
                     (reverse (proof-proof-symmetric proof assumed))
                     (step (proof-proof-cut proof reverse evidence)))
                    (proof-proof-front proof step term))))))
            (t nil)))))

(defun h2-search-lookup-base (search term context)
  (let* ((literals (h2-search-context-literals context))
         (evidence (cdr (assoc-equal term literals))))
    (cond (evidence evidence)
          ((proof-is-call term *proof-equal*)
           (proof-with-checked-results ((right (proof-term-at term 2)) (left (proof-term-at term 1)))
             (let ((reverse (cdr (assoc-equal (proof-eq right left) literals))))
               (if reverse (proof-proof-symmetric (h2-search-proof search) reverse) nil))))
          (t (h2-search-lookup-denial search term literals)))))

(defun h2-search-lookup-cons (search term context step)
  (if step
      step
    (let ((evidence (cdr (assoc-equal (list *proof-consp* term)
                                     (h2-search-context-literals context)))))
      (and evidence
           (library-library-cite (h2-search-search-library search) "H2-CONSP-NONNIL"
                                 (list term) (list evidence))))))

(defun h2-search-quoted-truth (proof term)
  (if (equal term *proof-false*)
      (proof-proof-not-nil proof)
    (proof-with-checked-results
     ((equality (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
      (step (proof-proof-nil-or-true proof term))
      (step (proof-proof-rewrite proof step equality '(1))))
     (proof-proof-tidy proof step))))

(defun h2-search-has-quoted-argument (args)
  (and (consp args)
       (or (proof-is-call (car args) *proof-quote*)
           (h2-search-has-quoted-argument (cdr args)))))

(defun h2-search-count-openings (fn opened)
  (if (endp opened)
      0
    (+ (if (equal fn (car opened)) 1 0) (h2-search-count-openings fn (cdr opened)))))

(defun h2-search-can-open-base (search term opened)
  (proof-with-checked-results ((fn (proof-term-at term 0)))
    (cond ((or (member-equal fn *h2-search-transparent*) (not (member-equal fn opened))) t)
          ((eq (h2-search-search-split-limit search) :none) '(:failure "failure" ""))
          (t (and (member-equal fn (h2-search-search-repeat search))
                  (h2-search-has-quoted-argument (cdr term))
                  (< (h2-search-count-openings fn opened) 128))))))

(defun h2-search-call-parts (term)
  (cond ((consp term) term)
        ((and (stringp term) (not (equal term ""))) (list term))
        (t '(:failure "TacticInapplicable" ""))))

(defun h2-search-list-at (items index)
  (if (< index (len items))
      (nth index items)
    '(:failure "TacticInapplicable" "")))

(defun h2-search-all-quoted-p (args)
  (or (endp args)
      (and (proof-is-call (car args) *proof-quote*) (h2-search-all-quoted-p (cdr args)))))

(defun h2-search-unquote-arguments (args)
  (if (endp args)
      nil
    (proof-with-checked-results
     ((value (proof-term-at (car args) 1))
      (values (h2-search-unquote-arguments (cdr args))))
     (cons value values))))

(defun h2-search-list-datum-p (value)
  (or (consp value) (null value)))

(defun h2-search-primitive-selector-value (fn object)
  (cond ((or (not (proof-compound object)) (endp object)) *proof-nil*)
        ((equal fn *library-car*) (car object))
        ((and (equal (len object) 2) (h2-search-list-datum-p (cadr object)))
         (proof-with-checked-results ((tag (proof-term-at (cadr object) 0)))
           (if (equal tag "dot") (proof-term-at (cadr object) 1) (cdr object))))
        (t (or (cdr object) *proof-nil*))))

(defun h2-search-primitive-tag (value)
  (and (h2-search-list-datum-p value) (proof-term-at value 0)))

(defun h2-search-primitive-quoted (proof term values)
  (let ((fn (car term)))
    (cond
     ((member-equal fn (list *library-car* *library-cdr*))
      (proof-with-checked-results
       ((object (h2-search-list-at values 0)) (value (h2-search-primitive-selector-value fn object)))
       (proof-proof-compute proof term value)))
     ((or (equal fn *h2-search-characterp*) (equal fn *h2-search-symbolp*))
      (proof-with-checked-results
       ((object (h2-search-list-at values 0)) (tag (h2-search-primitive-tag object)))
       (proof-proof-compute
        proof term (if (equal tag (if (equal fn *h2-search-characterp*) "char" "sym"))
                       *proof-t* *proof-nil*))))
     ((or (equal fn *h2-search-symbol-name*) (equal fn *h2-search-package-name*)
          (equal fn *h2-search-char-code*))
      (proof-with-checked-results
       ((object (h2-search-list-at values 0)) (tag (h2-search-primitive-tag object)))
       (let ((char-code (equal fn *h2-search-char-code*)))
         (if (not (equal tag (if char-code "char" "sym")))
             (proof-proof-constant proof term)
           (proof-with-checked-results
            ((value (proof-term-at object (if (equal fn *h2-search-symbol-name*) 2 1))))
            (proof-proof-compute proof term (if char-code value (list "str" value))))))))
     ((equal fn *library-numberp*)
      (proof-with-checked-results ((object (h2-search-list-at values 0)))
        (proof-proof-compute
         proof term (if (or (integerp object)
                            (and (consp object) (member-equal (car object) '("ratio" "complex"))))
                        *proof-t* *proof-nil*))))
     ((equal fn *proof-cons*)
      (proof-with-checked-results ((parts (proof-list-of-length values 2)))
        (proof-proof-compute proof term (proof-constant-cons-value (car parts) (cadr parts)))))
     ((equal fn *h2-search-code-char*)
      (proof-with-checked-results ((value (h2-search-list-at values 0)))
        (proof-proof-compute proof term
                             (list "char" (if (and (integerp value) (<= 0 value) (< value 256)) value 0)))))
     (t (proof-proof-constant proof term)))))

(defun h2-search-primitive-otherwise (proof term)
  (if (and (member-equal (car term) (proof-proof-primitives proof))
           (h2-search-all-quoted-p (cdr term)))
      (proof-with-checked-results ((values (h2-search-unquote-arguments (cdr term))))
        (h2-search-primitive-quoted proof term values))
    (if (and (equal (car term) *proof-equal*) (equal (cadr term) (caddr term)))
        (proof-proof-constant proof term)
      nil)))

(defun h2-search-primitive-cons-axiom (search selector term)
  (library-library-axiom (h2-search-search-library search)
                         (concatenate 'string (caddr selector) "-CONS") (cdr term)))

(defun h2-search-primitive-noncons (search selector object evidence)
  (let ((proof (h2-search-proof search)))
    (proof-with-checked-results
     ((step (library-library-axiom (h2-search-search-library search)
                                   (concatenate 'string "COMPLETION-OF-" (caddr selector)) (list object)))
      (value (h2-search-step-at step 2))
      (selected (proof-proof-select proof value evidence)))
     (proof-proof-chain proof step (list selected)))))

(defun h2-search-primitive-unequal (proof term evidence)
  (proof-with-checked-results
   ((step (proof-proof-fact proof "equal-different" (seq-zip (list *library-x* *library-y*) (cdr term))))
    (front (proof-proof-front proof step (proof-eq term *proof-false*))))
   (proof-proof-discharge proof front evidence)))

(defun h2-search-join-step (proof first step)
  (if first (proof-proof-chain proof first (list step)) step))

(defun h2-search-rewrite-from (proof term prior equality place)
  (proof-with-checked-results ((first (or prior (proof-proof-reflexive proof term))))
    (proof-proof-rewrite proof first equality place)))

(defun h2-search-rewrite-tidy (proof step equality place)
  (proof-with-checked-results ((result (proof-proof-rewrite proof step equality place)))
    (proof-proof-tidy proof result)))

(mutual-recursion
 (defun h2-search-search-rewrite-result-in-argument-rewrite (term place inside step search context)
   (declare (xargs :measure (acl2-count term)))
   (let ((equality (and inside (cdr (assoc-equal term (h2-search-context-equalities context))))))
     (cond (equality (proof-proof-rewrite (h2-search-proof search) step equality place))
           ((and (consp term) (proof-compound term) (not (proof-is-call term *proof-quote*)))
            (h2-search-rewrite-argument-children (cdr term) place 1 step search context))
           (t step))))
 (defun h2-search-rewrite-argument-children (terms place index step search context)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       step
     (proof-with-checked-results
      ((step (h2-search-search-rewrite-result-in-argument-rewrite
              (car terms) (append place (list index)) t step search context)))
      (h2-search-rewrite-argument-children (cdr terms) place (1+ index) step search context)))))

(defun h2-search-index-at (items index)
  (if (integerp index)
      (let ((index (if (< index 0) (+ (len items) index) index)))
        (if (< index 0) '(:failure "TacticInapplicable" "") (proof-term-at items index)))
    '(:failure "TacticInapplicable" "")))

(defun h2-search-search-rewrite-result-in-argument (search step index context)
  (proof-with-checked-results
   ((literal (proof-step-first step))
    (argument (h2-search-index-at literal index))
    (step (h2-search-search-rewrite-result-in-argument-rewrite argument (list 1 index) nil step search context)))
   (proof-proof-tidy (h2-search-proof search) step)))

(defun h2-search-search-introduce (search formula conclusion)
  (let ((proof (h2-search-proof search)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof formula))
      (opened-value (h2-search-step-at opened 2))
      (test (proof-term-at formula 1))
      (assumption (proof-proof-assume proof test t))
      (yes (proof-proof-select proof opened-value assumption))
      (yes-value (h2-search-step-at yes 2))
      (truth (proof-proof-select proof yes-value conclusion))
      (yes-equality (proof-proof-chain proof opened (list yes truth)))
      (yes (proof-proof-true-from-eq proof yes-equality))
      (no-equality (proof-proof-if-false proof opened-value))
      (no-equality (proof-proof-chain proof opened (list no-equality)))
      (no (proof-proof-true-from-eq proof no-equality)))
     (proof-proof-cases proof test yes no))))

(defun h2-search-make-bindings (pairs bindings)
  (if (endp pairs)
      bindings
    (proof-with-checked-results ((pair (proof-list-of-length (car pairs) 2)))
      (h2-search-make-bindings (cdr pairs) (table-put bindings (car pair) (cadr pair))))))

(defun h2-search-induction-seeds (proof formula measure substitutions)
  (if (endp substitutions)
      nil
    (proof-with-checked-results
     ((bindings (h2-search-make-bindings (car substitutions) nil))
      (smaller (proof-subst measure bindings))
      (instance (proof-subst formula bindings))
      (test (list *proof-ordinal-less* smaller measure))
      (step (proof-proof-assume proof (proof-ite test instance *proof-true*) t))
      (rest (h2-search-induction-seeds proof formula measure (cdr substitutions))))
     (cons step rest))))

(defun h2-search-list-child (n depth child)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h2-search-list-child"))
        ((zp depth) child)
        (t (h2-search-list-child (1- n) (1- depth) (list *library-cdr* child)))))

(defun h2-search-rule-discharge-p (sides first evidence)
  (and (consp sides)
       (or (and (not (equal (car sides) first))
                (or (equal (car sides) (proof-neg evidence))
                    (equal (proof-neg (car sides)) evidence)))
           (h2-search-rule-discharge-p (cdr sides) first evidence))))

(defun h2-search-discharge-rule (proof step evidence)
  (if (endp (cdr (proof-step-clause step)))
      step
    (proof-with-checked-results ((first (proof-step-first step)) (literal (proof-step-first evidence)))
      (if (h2-search-rule-discharge-p (cdr (proof-step-clause step)) first literal)
          (proof-proof-discharge proof step evidence)
        step))))

(defun h2-search-context-record-reduction (context key equality)
  (update-nth 6 (h2-search-context-cache-put context key equality
                                            (h2-search-context-reductions context))
              context))

(defun h2-search-context-record-deduction (context key step)
  (update-nth 7 (h2-search-context-cache-put context key step
                                            (h2-search-context-deductions context))
              context))

(defun h2-search-context-seed (proof seeds context)
  (if (endp seeds)
      context
    (proof-with-checked-results ((added (h2-search-context-add context proof (car seeds))))
      (h2-search-context-seed proof (cdr seeds) (cdr added)))))

(defun h2-search-context-seed-tests (cases context)
  (if (endp cases)
      context
    (proof-with-checked-results ((context (h2-search-context-test context (car cases))))
      (h2-search-context-seed-tests (cdr cases) context))))

(defund h2-search-visit-context (search seeds cases)
  (let ((empty (if (h2-search-search-indexes search)
                   (h2-search-indexed-context-init)
                 (h2-search-context-init))))
    (proof-with-checked-results ((context (h2-search-context-seed search seeds empty)))
      (h2-search-context-seed-tests cases context))))

(defun h2-search-stopped-p (result)
  (or (failure-p result) (h2-search-request-p result)))

(defun h2-search-finish (value replies)
  (if (h2-search-request-p value) value (cons value replies)))

(defmacro h2-search-return (value)
  `(h2-search-finish ,value replies))

(defmacro h2-search-bind (name form result)
  `(let ((h2-search-evaluation ,form))
     (if (or (h2-search-request-p h2-search-evaluation)
             (failure-p (car h2-search-evaluation)))
         h2-search-evaluation
       (let ((,name (car h2-search-evaluation))
             (replies (cdr h2-search-evaluation)))
         (declare (ignorable replies))
         ,result))))

(defmacro h2-search-check (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             (h2-search-return ,name)
           (h2-search-check ,(cdr bindings) ,result))))))

(defmacro h2-search-call (method &rest args)
  `(h2-search-run (1- n) search ,method (list ,@args) replies nil))

(defun h2-search-search-hook-data (search)
  (and (h2-search-object-p search) (cadr (cddddr (cddddr search)))))

(defun h2-search-search-with-hook-data (search data)
  (update-nth 9 data (if (h2-search-object-p search) search (h2-search-search-init search))))

(defun h2-search-request-search (request)
  (cadr (cddddr request)))

(defun h2-search-request (phase search method args result)
  (list :h2-search-request phase method args result (h2-search-search-with-replies search nil)))

; The pending events replay a deterministic prefix. The reversed events
; record the prefix consumed in this evaluation.
(defun h2-search-reply-transcript (pending reversed)
  (cons :h2-search-transcript (cons pending reversed)))

(defun h2-search-transcript-p (replies)
  (eq (car replies) :h2-search-transcript))

(defun h2-search-reply-pending (replies)
  (if (h2-search-transcript-p replies) (cadr replies) replies))

(defun h2-search-transcript-record (event replies)
  (h2-search-reply-transcript (cdadr replies) (cons event (cddr replies))))

(defun h2-search-reply-rest (replies)
  (if (h2-search-transcript-p replies)
      (h2-search-transcript-record (caadr replies) replies)
    (cdr replies)))

(defun h2-search-hook-request (phase search method args value replies)
  (let ((request (h2-search-request phase search method args value)))
    (if (h2-search-transcript-p replies)
        (append request (list (cddr replies)))
      request)))

(defun h2-search-replay-replies (replies request answer)
  (if (h2-search-transcript-p replies)
      (h2-search-reply-transcript (reverse (cons answer (nth 6 request))) nil)
    (append replies (list answer))))

(defun h2-search-transcript-finish (result before)
  (if (h2-search-request-p result)
      result
    (let ((value (car result)))
      (h2-search-finish
       value (h2-search-reply-transcript
              (cadr (cdr result))
              (cons (cons :h2-search-completed value) (cddr before)))))))

(defun h2-search-after-reply (search method args value replies)
  (let ((pending (h2-search-reply-pending replies)))
    (cond ((endp pending) (h2-search-hook-request :after search method args value replies))
          ((eq (car pending) :base) (h2-search-finish value (h2-search-reply-rest replies)))
          (t (h2-search-finish (cadar pending) (h2-search-reply-rest replies))))))

(defun h2-search-selector-equality-p (step)
  (let ((literal (car (proof-step-clause step))))
    (and (proof-is-call literal *proof-equal*)
         (or (proof-is-call (cadr literal) *library-car*)
             (proof-is-call (cadr literal) *library-cdr*)
             (proof-is-call (caddr literal) *library-car*)
             (proof-is-call (caddr literal) *library-cdr*)))))

(defund h2-search-inherited-method-p (search method args)
  (let ((hooks (h2-search-search-hooks search)))
    (or (member-eq method hooks)
        (case method
          (:apply-rules
           (and (member-eq :book-ordinal-rules hooks)
                (not (cadddr args))
                (proof-is-call (car args) *proof-ordinal-less*)))
          (:learn
           (and (member-eq :learn-selectors hooks)
                (h2-search-selector-equality-p (car args))))
          (otherwise nil)))))

; Calls use the same dispatcher for every recursive invocation. An inherited
; method can select the base body, supply a value, or inspect the base result.
(mutual-recursion
 (defun h2-search-run (n search method args replies base)
   (declare (xargs :measure (1+ (* 2 (nfix n)))))
   (if (not (h2-search-transcript-p replies))
       (h2-search-run-body n search method args replies base)
     (let ((event (caadr replies)))
       (if (and (consp event) (eq (car event) :h2-search-completed))
           (h2-search-finish (cdr event) (h2-search-transcript-record event replies))
         (h2-search-transcript-finish
          (h2-search-run-body n search method args
                              (h2-search-transcript-record :h2-search-enter replies) base)
          replies)))))

 (defun h2-search-run-body (n search method args replies base)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-body")))
    ((and (not base) (h2-search-inherited-method-p search method args))
     (let ((pending (h2-search-reply-pending replies)))
       (cond ((endp pending) (h2-search-hook-request :before search method args nil replies))
             ((eq (car pending) :base)
              (h2-search-run (1- n) search method args (h2-search-reply-rest replies) t))
             ((eq (car pending) :after)
              (h2-search-bind value (h2-search-run (1- n) search method args (h2-search-reply-rest replies) t)
                (h2-search-after-reply search method args value replies)))
             (t (h2-search-finish (cadar pending) (h2-search-reply-rest replies))))))
    (t
     (case method
       (:lookup
        (let ((step (h2-search-lookup-base search (car args) (cadr args))))
          (h2-search-return
           (if (member-eq :cons-lookup (h2-search-search-hooks search))
               (h2-search-lookup-cons search (car args) (cadr args) step)
             step))))
       (:can-open (h2-search-return (h2-search-can-open-base search (car args) (cadr args))))
       (:rule-apply
        (h2-search-run-rule-apply (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)
                                  (car (cddddr args))))
       (:rule-prove-instance
        (h2-search-run-rule-instance (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (:apply-rules
        (h2-search-run-apply-rules (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (:truth (h2-search-run-truth (1- n) search replies (car args) (cadr args) (caddr args)))
       (:primitive (h2-search-run-primitive (1- n) search replies (car args) (cadr args)))
       (:normalize
        (h2-search-run-normalize (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (:reduce (h2-search-run-reduce (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (:remove-wrappers (h2-search-run-remove-wrappers (1- n) search replies (car args)))
       (:learn (h2-search-run-learn (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (:learn-oriented-equality
        (h2-search-run-learn-oriented-equality (1- n) search replies (car args) (cadr args)))
       (:deduce (h2-search-run-deduce (1- n) search replies (car args) (cadr args) (caddr args)))
       (:find-proof (h2-search-run-find-proof (1- n) search replies (car args) (cadr args) (caddr args)))
       (:solve (h2-search-run-solve (1- n) search replies (car args) (cadr args) (caddr args)))
       (:visit (h2-search-run-visit (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (:visit-context (h2-search-return (h2-search-visit-context search (car args) (cadr args))))
       (:conjuncts (h2-search-return (proof-proof-conjunct (h2-search-proof search) (car args))))
       (:induction
        (h2-search-run-induction (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)
                                 (car (cddddr args))))
       (:list-induction
        (h2-search-run-list-induction (1- n) search replies (car args) (cadr args) (caddr args) (cadddr args)))
       (otherwise (h2-search-return '(:failure "failure" "")))))))

 (defun h2-search-run-rule-apply (n search replies rule term context active rewrite)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-rule-apply"))
     (h2-search-check
      ((pattern (if rewrite
                    (proof-term-at (h2-search-rule-pattern rule) 1)
                  (h2-search-rule-pattern rule))))
      (let ((matched (h2-search-match pattern term nil)))
        (if (or (not (car matched)) (h2-search-rule-active-p rule active))
            (h2-search-return (cons nil context))
          (h2-search-run-rule-candidates
           (1- n) search replies rule context active (list (list :bindings (cdr matched)))))))))

 (defun h2-search-run-rule-candidates (n search replies rule context active pending)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-rule-candidates"))
     (h2-search-check
      ((next (h2-search-completion-next n rule (h2-search-context-literals context) pending)))
      (if (not next)
          (h2-search-return (cons nil context))
        (h2-search-bind result (h2-search-call :rule-prove-instance rule context active (car next))
          (if (car result)
              (h2-search-return result)
            (h2-search-run-rule-candidates (1- n) search replies rule (cdr result) active (cdr next))))))))

 (defun h2-search-run-rule-instance (n search replies rule context active bindings)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-rule-instance"))
     (h2-search-check
      ((step (h2-search-indexed-fact search (h2-search-rule-name rule) (table-items bindings))))
      (h2-search-run-rule-actions (1- n) search replies (h2-search-rule-action rule)
                                  step context (append active (list rule)) bindings))))

 (defun h2-search-run-rule-actions (n search replies actions step context active bindings)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-rule-actions")))
    ((endp actions) (h2-search-return (cons step context)))
    (t
     (let ((proof (h2-search-proof search)))
       (h2-search-check ((parts (proof-list-of-length (car actions) 2)))
         (let ((action (car parts)) (datum (cadr parts)))
           (if (equal action "conjunct")
               (h2-search-check
                ((conjuncts (proof-proof-conjunct proof step))
                 (step (h2-search-index-at conjuncts (1- datum))))
                (h2-search-run-rule-actions (1- n) search replies (cdr actions) step context active bindings))
             (h2-search-check ((term (proof-subst datum bindings)))
               (h2-search-bind result (h2-search-call :deduce term context active)
                 (if (not (car result))
                     (h2-search-return result)
                   (h2-search-check
                    ((step (if (equal action "implies")
                               (proof-proof-modus-ponens proof step (car result))
                             (h2-search-discharge-rule proof step (car result)))))
                    (h2-search-run-rule-actions (1- n) search replies (cdr actions)
                                                step (cdr result) active bindings))))))))))))

 (defun h2-search-run-apply-rules (n search replies term context active rewrite)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-apply-rules")))
    ((eq (h2-search-search-split-limit search) :none)
     (h2-search-return '(:failure "failure" "")))
    ((or (equal term *proof-false*) (<= 5 (len active))) (h2-search-return (cons nil context)))
    (t
     (h2-search-check ((head (h2-search-head term)))
       (let ((index (if rewrite (h2-search-search-rewrite-heads search) (h2-search-search-rule-heads search))))
         (h2-search-run-apply-bucket (1- n) search replies
                                    (append (cdr (assoc-equal head index))
                                            (and head (cdr (assoc-equal nil index))))
                                    term context active rewrite))))))

 (defun h2-search-run-apply-bucket (n search replies rules term context active rewrite)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-apply-bucket")))
    ((endp rules) (h2-search-return (cons nil context)))
    (t
     (h2-search-bind result (h2-search-call :rule-apply (car rules) term context active rewrite)
       (let ((step (car result)) (context (cdr result)))
         (h2-search-check ((right (and step rewrite (h2-search-step-at step 2))))
           (if (and step (or (not rewrite) (not (equal right term))))
               (h2-search-return result)
             (h2-search-run-apply-bucket (1- n) search replies (cdr rules) term context active rewrite))))))))

 (defun h2-search-run-truth (n search replies term context active)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-truth")))
    ((proof-is-call term *proof-quote*)
     (h2-search-check ((step (if (equal term *proof-false*)
                                  (h2-search-search-not-nil search)
                                (h2-search-quoted-truth (h2-search-proof search) term))))
       (h2-search-return (cons step context))))
    (t
     (h2-search-bind step (h2-search-call :lookup term context)
       (if step
           (h2-search-return (cons step context))
         (h2-search-bind denial (h2-search-call :lookup (proof-neg term) context)
           (if denial
               (h2-search-return (cons denial context))
             (h2-search-bind result (h2-search-call :apply-rules term context active nil)
               (if (car result)
                   (h2-search-return result)
                 (h2-search-call :apply-rules (proof-neg term) (cdr result) active nil))))))))))

 (defun h2-search-run-primitive (n search replies term context)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-primitive"))
     (h2-search-check ((parts (h2-search-call-parts term)))
       (let ((proof (h2-search-proof search)) (fn (car parts)) (args (cdr parts)))
         (cond
          ((member-equal fn (list *library-car* *library-cdr*))
           (h2-search-check ((object (h2-search-list-at args 0)))
             (cond ((proof-is-call object *proof-cons*)
                    (h2-search-return (h2-search-primitive-cons-axiom search fn object)))
                   ((not (proof-is-call object *proof-quote*))
                    (h2-search-bind noncons (h2-search-call :lookup (proof-neg (list *proof-consp* object)) context)
                      (h2-search-return (if noncons
                                            (h2-search-primitive-noncons search fn object noncons)
                                          (h2-search-primitive-otherwise proof parts)))))
                   (t (h2-search-return (h2-search-primitive-otherwise proof parts))))))
          ((equal fn *proof-equal*)
           (h2-search-check ((left (h2-search-list-at args 0)) (right (h2-search-list-at args 1)))
             (if (equal left right)
                 (h2-search-return (h2-search-primitive-otherwise proof parts))
               (h2-search-bind unequal (h2-search-call :lookup (proof-neg term) context)
                 (h2-search-return (if unequal
                                       (h2-search-primitive-unequal proof term unequal)
                                     (h2-search-primitive-otherwise proof parts)))))))
          (t (h2-search-return (h2-search-primitive-otherwise proof parts))))))))

 (defun h2-search-run-normalize (n search replies term context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-normalize"))
     (let* ((key (list term opened active))
            (entry (h2-search-context-cache-find context key (h2-search-context-reductions context))))
       (if entry
           (h2-search-return (cons (cdr entry) context))
         (h2-search-bind result (h2-search-call :reduce term (h2-search-context-record-reduction context key nil)
                                               opened active)
           (h2-search-return (cons (car result)
                                   (h2-search-context-record-reduction (cdr result) key (car result)))))))))

 (defun h2-search-run-reduce (n search replies term context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce"))
     (let ((direct (cdr (assoc-equal term (h2-search-context-equalities context)))))
       (cond
        (direct (h2-search-run-normalize-chain (1- n) search replies direct context opened active nil))
        ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
         (h2-search-return (cons nil context)))
        (t
         (h2-search-check ((fn (proof-term-at term 0)))
           (if (< 2048 (h2-search-size term))
               (h2-search-return (cons nil context))
             (h2-search-bind known (h2-search-call :lookup term context)
               (cond
                ((or known (h2-search-context-representative-p context term))
                 (h2-search-return (cons nil context)))
                ((or (proof-compound fn) (equal fn *h2-search-return-last*))
                 (let ((proof (h2-search-proof search)))
                   (h2-search-check
                    ((first (if (proof-compound fn) (proof-proof-beta proof term) (proof-proof-unfold proof term))))
                    (h2-search-run-normalize-chain (1- n) search replies first context opened active nil))))
                ((equal fn *proof-if*)
                 (h2-search-run-reduce-if (1- n) search replies term context opened active))
                (t
                 (h2-search-bind rewrite (h2-search-call :apply-rules term context active t)
                   (cond ((car rewrite)
                          (h2-search-run-normalize-chain (1- n) search replies (car rewrite)
                                                         (cdr rewrite) opened active nil))
                         ((equal fn *proof-equal*)
                          (h2-search-run-reduce-equal-if (1- n) search replies term (cdr term) 1
                                                         (cdr rewrite) opened active))
                         (t (h2-search-run-reduce-primitive (1- n) search replies term (cdr rewrite)
                                                            opened active))))))))))))))

 (defun h2-search-run-normalize-chain (n search replies equality context opened active first)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-normalize-chain"))
     (h2-search-check ((value (h2-search-step-at equality 2)))
       (h2-search-bind next (h2-search-call :normalize value context opened active)
         (h2-search-check
          ((step (if first
                     (proof-proof-chain (h2-search-proof search) first (list equality (car next)))
                   (proof-proof-chain (h2-search-proof search) equality (list (car next))))))
          (h2-search-return (cons step (cdr next))))))))

 (defun h2-search-run-reduce-if (n search replies term context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-if"))
     (let ((proof (h2-search-proof search)))
       (h2-search-check ((test (proof-term-at term 1)))
         (h2-search-bind evidence (h2-search-call :truth test context active)
           (if (car evidence)
               (h2-search-check ((step (proof-proof-select proof term (car evidence))))
                 (h2-search-run-normalize-chain (1- n) search replies step (cdr evidence) opened active nil))
             (h2-search-bind equality (h2-search-call :normalize test (cdr evidence) opened active)
               (h2-search-check
                ((first (and (car equality) (h2-search-rewrite-from proof term nil (car equality) '(1 2 1))))
                 (current (if first (h2-search-step-at first 2) term))
                 (test (proof-term-at current 1)))
                (h2-search-bind evidence (h2-search-call :truth test (cdr equality) active)
                  (if (not (car evidence))
                      (h2-search-check ((context (if active (cdr evidence)
                                                             (h2-search-context-test (cdr evidence) test))))
                        (h2-search-return (cons first context)))
                    (h2-search-check
                     ((branch (proof-proof-select proof current (car evidence)))
                      (step (h2-search-join-step proof first branch)))
                     (h2-search-run-normalize-chain (1- n) search replies step (cdr evidence)
                                                    opened active nil))))))))))))

 (defun h2-search-run-reduce-equal-if (n search replies term args index context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-equal-if")))
    ((endp args) (h2-search-run-reduce-primitive (1- n) search replies term context opened active))
    ((not (proof-is-call (car args) *proof-if*))
     (h2-search-run-reduce-equal-if (1- n) search replies term (cdr args) (1+ index) context opened active))
    (t
     (h2-search-check ((test (proof-term-at (car args) 1)))
       (h2-search-bind evidence (h2-search-call :truth test context active)
         (if (not (car evidence))
             (h2-search-run-reduce-equal-if (1- n) search replies term (cdr args) (1+ index)
                                            (cdr evidence) opened active)
           (let ((proof (h2-search-proof search)))
             (h2-search-check
              ((reflexive (proof-proof-reflexive proof term))
               (selected (proof-proof-select proof (car args) (car evidence)))
               (first (proof-proof-rewrite proof reflexive selected (list 1 2 index))))
              (h2-search-run-normalize-chain (1- n) search replies first (cdr evidence) opened active nil)))))))))

 (defun h2-search-run-reduce-primitive (n search replies term context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-primitive"))
     (h2-search-bind primitive (h2-search-call :primitive term context)
       (if primitive
           (h2-search-return (cons primitive context))
         (h2-search-run-reduce-arguments (1- n) search replies term (cdr term) 1 nil context opened active)))))

 (defun h2-search-run-reduce-arguments (n search replies term args index first context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-arguments")))
    ((endp args) (h2-search-run-reduce-current (1- n) search replies term first context opened active))
    (t
     (h2-search-bind equality (h2-search-call :normalize (car args) context opened active)
       (if (not (car equality))
           (h2-search-run-reduce-arguments (1- n) search replies term (cdr args) (1+ index) first
                                          (cdr equality) opened active)
         (let ((proof (h2-search-proof search)))
           (h2-search-check
            ((first (h2-search-rewrite-from proof term first (car equality) (list 1 2 index)))
             (current (and (equal (car term) *proof-equal*) (h2-search-step-at first 2)))
             (left (and current (proof-term-at current 1)))
             (right (and current (proof-term-at current 2))))
            (if (and current (equal left right))
                (h2-search-check
                 ((constant (proof-proof-constant proof current))
                  (step (proof-proof-chain proof first (list constant))))
                 (h2-search-return (cons step (cdr equality))))
              (h2-search-run-reduce-arguments (1- n) search replies term (cdr args) (1+ index) first
                                             (cdr equality) opened active)))))))))

 (defun h2-search-run-reduce-current (n search replies term first context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-current"))
     (if (not first)
         (h2-search-run-reduce-open (1- n) search replies (car term) term nil context opened active)
       (h2-search-check ((current (h2-search-step-at first 2)))
         (let ((direct (cdr (assoc-equal current (h2-search-context-equalities context)))))
           (h2-search-bind primitive (if direct
                                         (h2-search-return direct)
                                       (h2-search-call :primitive current context))
             (if primitive
                 (h2-search-run-normalize-chain (1- n) search replies primitive context opened active first)
               (h2-search-bind rewrite (h2-search-call :apply-rules current context active t)
                 (if (car rewrite)
                     (h2-search-run-normalize-chain (1- n) search replies (car rewrite) (cdr rewrite) opened active first)
                   (h2-search-run-reduce-open (1- n) search replies (car term) current first
                                              (cdr rewrite) opened active))))))))))

 (defun h2-search-run-reduce-open (n search replies fn current first context opened active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-open"))
     (h2-search-bind known (h2-search-call :lookup current context)
       (cond
        ((or known (h2-search-context-representative-p context current))
         (h2-search-return (cons first context)))
        ((eq (h2-search-search-split-limit search) :none) (h2-search-return '(:failure "failure" "")))
        (t
         (h2-search-bind can-open (if (member-equal fn (h2-search-search-opened search))
                                      (h2-search-call :can-open current opened)
                                    (h2-search-return nil))
           (if can-open
               (let ((proof (h2-search-proof search)))
                 (h2-search-check ((opening (proof-proof-unfold proof current)))
                   (h2-search-bind next (h2-search-run-normalize-chain
                                         (1- n) search replies opening context (append opened (list fn)) active nil)
                     (h2-search-check ((step (h2-search-join-step proof first (car next))))
                       (h2-search-return (cons step (cdr next)))))))
             (h2-search-run-reduce-not (1- n) search replies fn current first context active))))))))

 (defun h2-search-run-reduce-not (n search replies fn current first context active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-not"))
     (if (not (equal fn *proof-not*))
         (h2-search-run-reduce-denial (1- n) search replies current first context)
       (h2-search-check ((test (proof-term-at current 1)))
         (h2-search-bind evidence (h2-search-call :truth test context active)
           (if (not (car evidence))
               (h2-search-run-reduce-denial (1- n) search replies current first (cdr evidence))
             (let ((proof (h2-search-proof search)))
               (h2-search-check
                ((opened (proof-proof-unfold proof current))
                 (value (h2-search-step-at opened 2))
                 (selected (proof-proof-select proof value (car evidence)))
                 (step (proof-proof-chain proof opened (list selected)))
                 (step (h2-search-join-step proof first step)))
                (h2-search-return (cons step (cdr evidence)))))))))))

 (defun h2-search-run-reduce-denial (n search replies current first context)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-reduce-denial"))
     (h2-search-bind evidence (h2-search-call :lookup (proof-neg current) context)
       (if (not evidence)
           (h2-search-return (cons first context))
         (h2-search-check
          ((step (h2-search-search-nil-value search evidence))
           (step (h2-search-join-step (h2-search-proof search) first step)))
          (h2-search-return (cons step context)))))))

 (defun h2-search-run-remove-wrappers (n search replies term)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-remove-wrappers")))
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) (h2-search-return nil))
    (t
     (let ((proof (h2-search-proof search)))
       (h2-search-check ((fn (proof-term-at term 0)))
         (if (or (proof-compound fn) (equal fn *h2-search-return-last*))
             (h2-search-check
              ((first (if (proof-compound fn) (proof-proof-beta proof term) (proof-proof-unfold proof term)))
               (value (h2-search-step-at first 2)))
              (h2-search-bind next (h2-search-call :remove-wrappers value)
                (h2-search-return (proof-proof-chain proof first (list next)))))
           (h2-search-run-remove-wrapper-arguments (1- n) search replies term (cdr term) 1 nil)))))))

 (defun h2-search-run-remove-wrapper-arguments (n search replies term args index first)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-remove-wrapper-arguments")))
    ((endp args) (h2-search-return first))
    (t
     (h2-search-bind equality (h2-search-call :remove-wrappers (car args))
       (h2-search-check
        ((first (if equality
                    (h2-search-rewrite-from (h2-search-proof search) term first equality (list 1 2 index))
                  first)))
        (h2-search-run-remove-wrapper-arguments (1- n) search replies term (cdr args) (1+ index) first))))))

 (defun h2-search-run-learn (n search replies step context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn"))
     (h2-search-check ((term (proof-step-first step)))
       (if (or (h2-search-seen-p term seen) (h2-search-context-contradiction context))
           (h2-search-return (cons context seen))
         (let ((seen (h2-search-seen-add term seen)))
           (h2-search-check ((added (h2-search-context-add context search step)))
             (let ((context (cdr added)))
               (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
                   (h2-search-return (cons context seen))
                 (h2-search-check ((fn (proof-term-at term 0)))
                   (if (equal fn *proof-equal*)
                       (h2-search-run-learn-equality (1- n) search replies term step context opened seen)
                     (h2-search-run-learn-form (1- n) search replies fn term step context opened seen)))))))))))

 (defun h2-search-run-learn-equality (n search replies term step context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn-equality"))
     (h2-search-bind direct (h2-search-call :remove-wrappers term)
       (h2-search-bind learned
         (if direct
             (h2-search-check
              ((rewritten (h2-search-rewrite-tidy (h2-search-proof search) step direct '(1))))
              (h2-search-call :learn rewritten context opened seen))
           (h2-search-return (cons context seen)))
         (h2-search-bind context (h2-search-call :learn-oriented-equality step (car learned))
           (h2-search-run-learn-form (1- n) search replies *proof-equal* term step context opened (cdr learned)))))))

 (defun h2-search-run-learn-form (n search replies fn term step context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn-form"))
     (let ((proof (h2-search-proof search)))
       (cond
        ((equal fn *library-implies*)
         (h2-search-check ((test (proof-term-at term 1)))
           (h2-search-bind evidence (h2-search-call :deduce test context '(nil))
             (if (not (car evidence))
                 (h2-search-return (cons (cdr evidence) seen))
               (h2-search-check ((consequence (proof-proof-modus-ponens proof step (car evidence))))
                 (h2-search-call :learn consequence (cdr evidence) opened seen))))))
        ((equal fn *proof-if*) (h2-search-run-learn-if (1- n) search replies term step context opened seen))
        ((or (proof-compound fn) (member-equal fn *h2-search-transparent*))
         (h2-search-check
          ((equality (if (proof-compound fn) (proof-proof-beta proof term) (proof-proof-unfold proof term)))
           (step (h2-search-rewrite-tidy proof step equality '(1))))
          (h2-search-call :learn step context (append opened (list fn)) seen)))
        ((equal fn *proof-not*)
         (h2-search-check ((value (proof-term-at term 1)))
           (h2-search-run-learn-not (1- n) search replies value step context opened seen)))
        (t (h2-search-run-learn-arguments (1- n) search replies fn (cdr term) 1 step step
                                          context opened seen))))))

 (defun h2-search-run-learn-if (n search replies term step context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn-if"))
     (let ((proof (h2-search-proof search)))
       (h2-search-check ((no (proof-term-at term 3)))
         (cond
          ((equal no *proof-false*)
           (h2-search-bind consequences (h2-search-call :conjuncts step)
             (h2-search-run-learn-steps (1- n) search replies consequences context opened seen)))
          ((equal (caddr term) *proof-false*)
           (h2-search-check
            ((equal-yes (proof-proof-if-true proof term))
             (evidence (h2-search-rewrite-tidy proof step equal-yes '(1)))
             (denied (proof-proof-front proof evidence (proof-neg (cadr term)))))
            (h2-search-bind learned (h2-search-call :learn denied context opened seen)
              (h2-search-check ((selected (proof-proof-prove-if proof step denied)))
                (h2-search-call :learn selected (car learned) opened (cdr learned))))))
          (t
           (h2-search-bind equality (h2-search-call :normalize (cadr term) context opened nil)
             (h2-search-check
              ((step (if (car equality) (h2-search-rewrite-tidy proof step (car equality) '(1 1)) step))
               (test (h2-search-step-at step 1)))
              (h2-search-bind evidence (h2-search-call :truth test (cdr equality) nil)
                (if (car evidence)
                    (h2-search-check ((selected (proof-proof-prove-if proof step (car evidence))))
                      (h2-search-call :learn selected (cdr evidence) opened seen))
                  (h2-search-check
                   ((otherwise (h2-search-step-at step 3))
                    (context (if (or (equal otherwise *proof-true*) (proof-is-call test *proof-ordinal-less*))
                                 (cdr evidence)
                               (h2-search-context-test (cdr evidence) test))))
                   (h2-search-return (cons context seen)))))))))))))

 (defun h2-search-run-learn-steps (n search replies steps context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-learn-steps")))
    ((endp steps) (h2-search-return (cons context seen)))
    (t
     (h2-search-bind learned (h2-search-call :learn (car steps) context opened seen)
       (h2-search-run-learn-steps (1- n) search replies (cdr steps) (car learned) opened (cdr learned))))))

 (defun h2-search-run-learn-not (n search replies value step context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-learn-not")))
    ((proof-is-call value *proof-if*)
     (h2-search-check ((parts (proof-list-of-length (cdr value) 3)))
       (let* ((test (car parts)) (yes (cadr parts))
              (select-yes (or (equal yes test) (equal yes *proof-true*))))
         (if (or select-yes (equal (caddr parts) *proof-true*))
             (h2-search-run-learn-not-if (1- n) search replies value step context opened seen select-yes test yes)
           (h2-search-run-learn-not-normalize (1- n) search replies value step context opened seen)))))
    ((proof-is-call value *proof-not*)
     (let ((proof (h2-search-proof search)))
       (h2-search-check
        ((test (proof-term-at value 1))
         (clause (h2-search-excluded-middle search test))
         (front (proof-proof-front proof clause value))
         (positive (proof-proof-cut proof front step)))
        (h2-search-bind learned (h2-search-call :learn positive context opened seen)
          (h2-search-run-learn-not-normalize (1- n) search replies value step (car learned) opened (cdr learned))))))
    (t (h2-search-run-learn-not-normalize (1- n) search replies value step context opened seen))))

 (defun h2-search-run-learn-not-if (n search replies value step context opened seen select-yes test yes)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn-not-if"))
     (let ((proof (h2-search-proof search)))
       (h2-search-check
        ((branch (proof-proof-assume proof test select-yes))
         (branch-equality (proof-proof-select proof value branch))
         (excluded (proof-proof-rewrite proof step branch-equality '(1 1)))
         (known (if (and select-yes (equal yes test)) branch (proof-proof-prove proof *proof-true* nil nil)))
         (joined (proof-proof-cut proof known excluded))
         (selected (proof-proof-front proof joined (if select-yes (proof-neg test) test))))
        (h2-search-bind learned (h2-search-call :learn selected context opened seen)
          (h2-search-check
           ((equality (proof-proof-select proof value selected))
            (reduced (h2-search-rewrite-tidy proof step equality '(1 1))))
           (h2-search-call :learn reduced (car learned) opened (cdr learned))))))))

 (defun h2-search-run-learn-not-normalize (n search replies value step context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn-not-normalize"))
     (let ((proof (h2-search-proof search)))
       (h2-search-bind equality (h2-search-call :normalize value context opened nil)
         (h2-search-bind learned
           (if (car equality)
               (h2-search-check ((reduced (h2-search-rewrite-tidy proof step (car equality) '(1 1))))
                 (h2-search-call :learn reduced (cdr equality) opened seen))
             (h2-search-return (cons (cdr equality) seen)))
           (if (or (not (proof-is-call value *proof-quote*)) (equal value *proof-false*))
               (h2-search-return learned)
             (h2-search-bind truth (h2-search-call :truth value (car learned) nil)
               (h2-search-check ((contradiction (proof-proof-cut proof (car truth) step)))
                 (h2-search-return
                  (cons (h2-search-context-with-contradiction (cdr truth) contradiction) (cdr learned)))))))))))

 (defun h2-search-run-learn-arguments (n search replies fn args index step first context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-learn-arguments")))
    ((endp args)
     (let ((proof (h2-search-proof search)))
       (h2-search-check
        ((current (proof-step-first first))
         (context
          (if (equal first step)
              context
            (proof-with-checked-results
             ((tidied (proof-proof-tidy proof first))
              (added (h2-search-context-add context search tidied)))
             (cdr added)))))
        (h2-search-run-learn-open (1- n) search replies fn current first context opened seen))))
    (t
     (h2-search-bind equality (h2-search-call :normalize (car args) context opened nil)
       (h2-search-check
        ((first (if (car equality)
                    (proof-proof-rewrite (h2-search-proof search) first (car equality) (list 1 index)) first)))
        (h2-search-run-learn-arguments (1- n) search replies fn (cdr args) (1+ index) step first
                                       (cdr equality) opened seen))))))

 (defun h2-search-run-learn-open (n search replies fn current first context opened seen)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-learn-open")))
    ((eq (h2-search-search-split-limit search) :none) (h2-search-return '(:failure "failure" "")))
    (t
     (let ((proof (h2-search-proof search)))
       (h2-search-bind can-open (if (member-equal fn (h2-search-search-opened search))
                                    (h2-search-call :can-open current opened)
                                  (h2-search-return nil))
         (if can-open
             (h2-search-check
              ((equality (proof-proof-unfold proof current))
               (step (h2-search-rewrite-tidy proof first equality '(1))))
              (h2-search-call :learn step context (append opened (list fn)) seen))
           (h2-search-bind primitive (h2-search-call :primitive current context)
             (h2-search-check ((value (and primitive (h2-search-step-at primitive 2))))
               (if (or (not primitive) (equal current value))
                   (h2-search-return (cons context seen))
                 (h2-search-check
                  ((first (h2-search-rewrite-tidy proof first primitive '(1)))
                   (added (h2-search-context-add context search first)))
                  (h2-search-return (cons (cdr added) seen))))))))))))

 (defun h2-search-run-learn-oriented-equality (n search replies step context)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-learn-oriented-equality"))
     (h2-search-check ((value (h2-search-step-at step 2)))
       (if (not (proof-is-call value *proof-if*))
           (h2-search-return context)
         (let ((proof (h2-search-proof search)))
           (h2-search-check ((test (proof-term-at value 1)))
             (h2-search-bind condition (h2-search-call :normalize test context nil nil)
               (h2-search-check
                ((step (if (car condition) (proof-proof-rewrite proof step (car condition) '(1 2 1)) step))
                 (value (if (car condition) (h2-search-step-at step 2) value))
                 (test (proof-term-at value 1)))
                (h2-search-bind evidence (h2-search-call :truth test (cdr condition) nil)
                  (if (not (car evidence))
                      (h2-search-return (cdr evidence))
                    (let ((context (cdr evidence)))
                      (h2-search-check
                       ((selected (proof-proof-select proof value (car evidence)))
                        (step (proof-proof-chain proof step (list selected)))
                        (step (h2-search-search-rewrite-result-in-argument search step 1 context))
                        (step (h2-search-search-rewrite-result-in-argument search step 2 context))
                        (added (h2-search-context-add context search step)))
                       (h2-search-return (cdr added))))))))))))))

 (defun h2-search-run-deduce (n search replies term context active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-deduce"))
     (let ((contradiction (h2-search-context-contradiction context)))
       (if contradiction
           (h2-search-check
            ((step (proof-proof-subsume (h2-search-proof search) contradiction
                                        (cons term (proof-step-clause contradiction)))))
            (h2-search-return (cons step context)))
         (let* ((key (list term active))
                (entry (h2-search-context-cache-find context key (h2-search-context-deductions context))))
           (if entry
               (h2-search-return (cons (cdr entry) context))
             (h2-search-bind result (h2-search-call :find-proof term
                                                    (h2-search-context-record-deduction context key nil) active)
               (h2-search-return (cons (car result)
                                       (h2-search-context-record-deduction (cdr result) key (car result)))))))))))

 (defun h2-search-run-find-proof (n search replies term context active)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-find-proof")))
    ((equal term *proof-false*) (h2-search-return (cons nil context)))
    ((proof-is-call term *proof-quote*) (h2-search-call :truth term context active))
    (t
     (h2-search-bind evidence (h2-search-run-lookup-or-rules (1- n) search replies term context active)
       (if (car evidence)
           (h2-search-return evidence)
         (h2-search-bind equality (h2-search-call :normalize term (cdr evidence) nil active)
           (if (not (car equality))
               (h2-search-return equality)
             (h2-search-check ((value (h2-search-step-at (car equality) 2)))
               (h2-search-bind step (if (and (proof-is-call value *proof-quote*) (not (equal value *proof-false*)))
                                        (h2-search-call :truth value (cdr equality) active)
                                      (h2-search-run-lookup-or-rules (1- n) search replies value (cdr equality) active))
                 (if (not (car step))
                     (h2-search-return step)
                   (h2-search-check
                    ((proof (proof-proof-transport (h2-search-proof search) (car step) (car equality))))
                    (h2-search-return (cons proof (cdr step))))))))))))))

 (defun h2-search-run-lookup-or-rules (n search replies term context active)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-lookup-or-rules"))
     (h2-search-bind evidence (h2-search-call :lookup term context)
       (if evidence
           (h2-search-return (cons evidence context))
         (h2-search-call :apply-rules term context active nil)))))

 (defun h2-search-run-solve (n search replies formula seeds cases)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-solve")))
    ((eq (h2-search-search-split-limit search) :none) (h2-search-return '(:failure "failure" "")))
    ((not (proof-is-call formula *library-implies*))
     (h2-search-bind visit (h2-search-call :visit formula seeds cases (h2-search-search-split-limit search))
       (h2-search-return (car visit))))
    (t
     (h2-search-check
      ((parts (proof-list-of-length (cdr formula) 2))
       (condition (proof-proof-assume (h2-search-proof search) (car parts) t)))
      (h2-search-bind step (h2-search-call :solve (cadr parts) (append seeds (list condition)) cases)
        (h2-search-return (h2-search-search-introduce search formula step)))))))

 (defun h2-search-run-visit (n search replies formula seeds cases remaining)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-visit"))
     (h2-search-bind context (h2-search-call :visit-context seeds cases)
      (h2-search-bind context (h2-search-run-visit-learn (1- n) search replies seeds context 12)
        (h2-search-bind result (h2-search-call :deduce formula context nil)
          (if (car result)
              (h2-search-return (cons (car result) remaining))
            (let ((context (cdr result)))
              (h2-search-bind context (h2-search-run-visit-contradiction
                                       (1- n) search replies (h2-search-context-literals context) context)
                (if (h2-search-context-contradiction context)
                    (h2-search-bind result (h2-search-call :deduce formula context nil)
                      (h2-search-return (cons (car result) remaining)))
                  (h2-search-run-visit-split (1- n) search replies formula seeds cases remaining context))))))))))

 (defun h2-search-run-visit-learn (n search replies seeds context rounds)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-visit-learn")))
    ((zp rounds) (h2-search-return context))
    (t
     (let ((previous (len (h2-search-context-literals context))))
       (h2-search-bind learned (h2-search-run-visit-learn-seeds (1- n) search replies seeds context)
         (if (or (h2-search-context-contradiction learned)
                 (equal previous (len (h2-search-context-literals learned))))
             (h2-search-return learned)
           (h2-search-run-visit-learn (1- n) search replies seeds learned (1- rounds))))))))

 (defun h2-search-run-visit-learn-seeds (n search replies seeds context)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-visit-learn-seeds")))
    ((endp seeds) (h2-search-return context))
    (t
     (let ((seen (and (h2-search-indexed-context-p context) (list :h2-indexed-seen))))
       (h2-search-bind learned (h2-search-call :learn (car seeds) context nil seen)
         (h2-search-run-visit-learn-seeds (1- n) search replies (cdr seeds) (car learned)))))))

 (defun h2-search-run-visit-contradiction (n search replies literals context)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-visit-contradiction")))
    ((endp literals) (h2-search-return context))
    (t
     (let ((literal (caar literals)) (step (cdar literals)) (proof (h2-search-proof search)))
       (cond
        ((proof-is-call literal *proof-not*)
         (h2-search-check ((positive (proof-term-at literal 1)))
           (h2-search-bind opposite (h2-search-call :apply-rules positive context nil nil)
             (if (not (car opposite))
                 (h2-search-run-visit-contradiction (1- n) search replies (cdr literals) (cdr opposite))
               (h2-search-check ((contradiction (proof-proof-cut proof (car opposite) step)))
                 (h2-search-return (h2-search-context-with-contradiction (cdr opposite) contradiction)))))))
        (t
         (h2-search-check ((head (h2-search-head literal)))
           (cond
            ((member-equal head (list *proof-less* *h2-search-string-less*))
             (h2-search-bind denial (h2-search-call :apply-rules (proof-neg literal) context nil nil)
               (if (not (car denial))
                   (h2-search-run-visit-contradiction (1- n) search replies (cdr literals) (cdr denial))
                 (h2-search-check ((contradiction (proof-proof-cut proof step (car denial))))
                   (h2-search-return (h2-search-context-with-contradiction (cdr denial) contradiction))))))
            ((and (proof-is-call literal *proof-equal*) (member-equal *proof-false* (cdr literal)))
             (h2-search-run-visit-false-equality (1- n) search replies literal step (cdr literals) context))
            (t (h2-search-run-visit-contradiction (1- n) search replies (cdr literals) context))))))))))

 (defun h2-search-run-visit-false-equality (n search replies literal step literals context)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-visit-false-equality"))
     (let ((symmetric (equal (cadr literal) *proof-false*)))
       (h2-search-check ((other (if symmetric (proof-term-at literal 2) (cadr literal))))
         (h2-search-bind present (h2-search-run-lookup-or-rules (1- n) search replies other context nil)
           (if (not (car present))
               (h2-search-run-visit-contradiction (1- n) search replies literals (cdr present))
             (let ((proof (h2-search-proof search)))
               (h2-search-check
                ((equality (if symmetric (proof-proof-symmetric proof step) step))
                 (contradiction (h2-search-rewrite-tidy proof (car present) equality '(1))))
                (h2-search-return (h2-search-context-with-contradiction (cdr present) contradiction))))))))))

 (defun h2-search-run-visit-split (n search replies formula seeds cases remaining context)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-visit-split"))
     (h2-search-bind best (h2-search-run-visit-choose (1- n) search replies (h2-search-context-tests context) context nil)
       (if (or (not best) (<= remaining 0))
           (h2-search-return '(:failure "Unproved" ""))
         (let ((test (cdr best)) (proof (h2-search-proof search)))
           (h2-search-check ((assumed (proof-proof-assume proof test t)))
             (h2-search-bind yes (h2-search-call :visit formula (append seeds (list assumed)) cases (1- remaining))
               (h2-search-check ((assumed (proof-proof-assume proof test nil)))
                 (h2-search-bind no (h2-search-call :visit formula (append seeds (list assumed)) cases (cdr yes))
                   (h2-search-check ((step (proof-proof-cases proof test (car yes) (car no))))
                     (h2-search-return (cons step (cdr no)))))))))))))

 (defun h2-search-run-visit-choose (n search replies tests context best)
   (declare (xargs :measure (* 2 (nfix n))))
   (cond
    ((zp n) (h2-search-return '(:failure "Fuel" "h2-search-run-visit-choose")))
    ((endp tests) (h2-search-return best))
    (t
     (let ((term (caar tests)))
       (h2-search-bind known (h2-search-call :lookup term context)
         (if known
             (h2-search-run-visit-choose (1- n) search replies (cdr tests) context best)
           (h2-search-bind denial (h2-search-call :lookup (proof-neg term) context)
             (let* ((size (and (not denial) (h2-search-size term)))
                    (best (if (and size (or (not best) (< size (car best)))) (cons size term) best)))
               (h2-search-run-visit-choose (1- n) search replies (cdr tests) context best)))))))))

 (defun h2-search-run-induction (n search replies formula measure substitutions ordinal cases)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-induction"))
     (let ((proof (h2-search-proof search)))
       (h2-search-check ((hypotheses (h2-search-induction-seeds proof formula measure substitutions)))
         (h2-search-bind step (h2-search-call :solve formula hypotheses cases)
           (h2-search-return (proof-proof-induct proof ordinal step formula measure substitutions)))))))

 (defun h2-search-run-list-induction (n search replies formula variable updated depth)
   (declare (xargs :measure (* 2 (nfix n))))
   (if (zp n)
       (h2-search-return '(:failure "Fuel" "h2-search-run-list-induction"))
     (h2-search-check
      ((child (h2-search-list-child n depth variable))
       (ordinal (library-library-builtin (h2-search-search-library search) 1 variable)))
      (h2-search-call :induction formula (list *library-count* variable)
                      (list (cons (list variable child) updated)) ordinal nil)))))

(defun h2-search-evaluate (search method args)
  (let ((result (h2-search-run 1000000 search method args (h2-search-search-replies search) nil)))
    (if (h2-search-request-p result) result (car result))))

(defun h2-search-search-call-with-outcome (search method args)
  (let ((result (h2-search-run 1000000 search method args (h2-search-search-replies search) nil)))
    (if (h2-search-request-p result)
        result
      (cons (car result) (h2-search-search-with-replies search (cdr result))))))

(defun h2-search-search-call-with-remainder (search method args)
  (let ((result (h2-search-search-call-with-outcome search method args)))
    (if (failure-p (car result)) (car result) result)))

(defun h2-search-rule-apply (rule search term context active rewrite)
  (h2-search-evaluate search :rule-apply (list rule term context active rewrite)))

(defun h2-search-rule-prove-instance (rule search context active bindings)
  (h2-search-evaluate search :rule-prove-instance (list rule context active bindings)))

(defun h2-search-search-lookup (search term context)
  (h2-search-evaluate search :lookup (list term context)))

(defun h2-search-search-truth (search term context active)
  (h2-search-evaluate search :truth (list term context active)))

(defun h2-search-search-apply-rules (search term context active rewrite)
  (h2-search-evaluate search :apply-rules (list term context active rewrite)))

(defun h2-search-search-primitive (search term context)
  (h2-search-evaluate search :primitive (list term context)))

(defun h2-search-search-normalize (search term context opened active)
  (h2-search-evaluate search :normalize (list term context opened active)))

(defun h2-search-search-reduce (search term context opened active)
  (h2-search-evaluate search :reduce (list term context opened active)))

(defun h2-search-search-can-open (search term opened)
  (h2-search-evaluate search :can-open (list term opened)))

(defun h2-search-search-remove-wrappers (search term)
  (h2-search-evaluate search :remove-wrappers (list term)))

(defun h2-search-search-learn (search step context opened seen)
  (h2-search-evaluate search :learn (list step context opened seen)))

(defun h2-search-search-learn-oriented-equality (search step context)
  (h2-search-evaluate search :learn-oriented-equality (list step context)))

(defun h2-search-search-deduce (search term context active)
  (h2-search-evaluate search :deduce (list term context active)))

(defun h2-search-search-find-proof (search term context active)
  (h2-search-evaluate search :find-proof (list term context active)))

(defun h2-search-search-solve (search formula seeds cases)
  (h2-search-evaluate search :solve (list formula seeds cases)))

(defun h2-search-search-solve-visit (seeds search formula cases remaining)
  (h2-search-evaluate search :visit (list formula seeds cases remaining)))

(defun h2-search-search-induction (search formula measure substitutions ordinal cases)
  (h2-search-evaluate search :induction (list formula measure substitutions ordinal cases)))

(defun h2-search-search-list-induction (search formula variable updated depth)
  (h2-search-evaluate search :list-induction (list formula variable updated depth)))

; Callers establish termination using their own measures.
(in-theory (disable (:definition h2-search-run)))
