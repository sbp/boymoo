(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-arrays-header* (proof-sym "HEADER" "ACL2"))
(defconst *b1-arrays-dimensions* (proof-sym "DIMENSIONS" "ACL2"))
(defconst *b1-arrays-maximum* (proof-sym "MAXIMUM-LENGTH" "ACL2"))
(defconst *b1-arrays-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *b1-arrays-assoc-keyword* (proof-sym "ASSOC-KEYWORD" "ACL2"))
(defconst *b1-arrays-array* (proof-sym "ARRAY1P" "ACL2"))
(defconst *b1-arrays-compress* (proof-sym "COMPRESS1" "ACL2"))
(defconst *b1-arrays-update* (proof-sym "ASET1" "ACL2"))
(defconst *b1-arrays-default* (proof-sym "DEFAULT" "ACL2"))
(defconst *b1-arrays-read* (proof-sym "AREF1" "ACL2"))
(defconst *b1-arrays-reset* (proof-sym "RESET-ARRAY1" "ACL2"))
(defconst *b1-arrays-alistp* (proof-sym "ALISTP" "ACL2"))
(defconst *b1-arrays-bounded* (proof-sym "BOUNDED-INTEGER-ALISTP" "ACL2"))
(defconst *b1-arrays-scan* (proof-sym "COMPRESS11" "ACL2"))
(defconst *b1-arrays-name* (proof-sym "NAME" "ACL2"))
(defconst *b1-arrays-l* (proof-sym "L" "ACL2"))
(defconst *b1-arrays-n* (proof-sym "N" "ACL2"))
(defconst *b1-arrays-val* (proof-sym "VAL" "ACL2"))
(defconst *b1-arrays-i* (proof-sym "I" "ACL2"))
(defconst *b1-arrays-j* (proof-sym "J" "ACL2"))
(defconst *b1-arrays-d* (proof-sym "D" "ACL2"))
(defconst *b1-arrays-header-key* (proof-quote (proof-sym "HEADER" "KEYWORD")))
(defconst *b1-arrays-projections*
  (list *b1-arrays-dimensions* *b1-arrays-maximum* *b1-arrays-default*))

(defmacro b1-arrays-normalize (lib term &optional evidence unfold rules inspect-branches)
  `(b1-logic-bookproof-normalize ,lib ,term ,evidence ,unfold ,rules nil nil ,inspect-branches))

(defmacro b1-arrays-normalize-proof (lib term &optional evidence unfold rules)
  `(b1-logic-bookproof-normalize-proof ,lib ,term ,evidence ,unfold ,rules nil))

(defun b1-arrays-list-at (items index)
  (if (< index (len items))
      (nth index items)
    '(:failure "failure" "")))

(defun b1-arrays-check-field (lib field)
  (proof-with-checked-results
      ((term (b1-logic-step-first field))
       (reduction (b1-arrays-normalize lib term)))
    (proof-proof-rewrite (library-library-proof lib) field reduction '(1))))

(defun b1-arrays-array-checks-field (lib fields)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((term (b1-logic-step-first fields)))
      (if (proof-is-call term *proof-if*)
          (proof-with-checked-results ((false-branch (proof-term-at term 3)))
            (if (equal false-branch *proof-false*)
                (proof-with-checked-results
                    ((parts (proof-proof-conjunct proof fields))
                     (field (b1-arrays-check-field lib (car parts))))
                  (list :continue field (cadr parts)))
              (proof-with-checked-results ((field (b1-arrays-check-field lib fields)))
                (list field))))
        (proof-with-checked-results ((field (b1-arrays-check-field lib fields)))
          (list field))))))

(defun b1-arrays-array-checks-fields (n lib pending)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "b1-arrays-array-checks-fields"))
        ((eq (car pending) :continue)
         (proof-with-checked-results
             ((rest (b1-arrays-array-checks-fields
                     (1- n) lib (b1-arrays-array-checks-field lib (caddr pending)))))
           (cons (cadr pending) rest)))
        (t pending)))

(defun b1-arrays-array-checks (lib premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (b1-logic-step-first premise))
         (parts (proof-list-of-length literal 3))
         (law (proof-proof-fact proof (proof-sym "ARRAY1P-FORWARD" "ACL2")
                                (list (list *b1-arrays-name* (cadr parts))
                                      (list *b1-arrays-l* (caddr parts)))))
         (fields (proof-proof-modus-ponens proof law premise)))
      (b1-arrays-array-checks-fields
       1000000 lib (b1-arrays-array-checks-field lib fields)))))

(defun b1-arrays-header-exists-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((goal (proof-term-at formula 2))
         (header (proof-term-at goal 1))
         (selector (b1-arrays-normalize lib header nil (list *b1-arrays-header*)))
         (not-header (proof-proof-assume proof goal nil))
         (bad (proof-proof-rewrite proof not-header selector '(1 1 1)))
         (empty (b1-structures-noncons-selector lib *library-cdr* bad))
         (checks (b1-arrays-array-checks lib premise))
         (dimension (proof-term-at checks 5))
         (term (b1-logic-step-first dimension))
         (reduced (b1-arrays-normalize
                   lib term nil
                   (list *b1-arrays-assoc-keyword* *b1-logic-endp* *b1-logic-atom* *proof-not*)
                   (list (b1-logic-equal-to empty))))
         (impossible (proof-proof-rewrite proof dimension reduced '(1)))
         (impossible (proof-proof-tidy proof impossible)))
      (proof-proof-front proof impossible goal))))

(defun b1-arrays-header-exists (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-header-exists-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-arrays-assoc-returned-key-leaf (value tests lib induction)
  (let* ((proof (library-library-proof lib))
         (claim (list *library-implies* (list *proof-consp* value)
                      (proof-eq (list *library-car* value) *library-x*))))
    (cond ((equal value *proof-false*)
           (proof-with-checked-results
               ((step (b1-arrays-normalize-proof lib claim nil (list *library-implies*))))
             (cons step induction)))
          ((proof-is-call value *b1-arrays-assoc*)
           (b1-induction-tree-induction-hypothesis
            induction (list (cons *library-y* (list *library-cdr* *library-y*))) tests))
          (t
           (proof-with-checked-results
               ((matching (proof-proof-assume
                           proof (proof-eq *library-x* (list *library-car* value)) t))
                (premise (b1-logic-bookproof-prove-implication-premise lib claim))
                (consequence (proof-proof-symmetric proof matching))
                (step (b1-logic-bookproof-prove-implication-with-premise
                       lib claim premise consequence)))
             (cons step induction))))))

(defun b1-arrays-assoc-returned-key-leaves (requests lib previous)
  (declare (xargs :measure (acl2-count requests)))
  (cond ((failure-p previous) previous)
        ((endp requests) (cons nil (cdr previous)))
        (t (let* ((request (car requests))
                  (leaf (b1-arrays-assoc-returned-key-leaf
                         (car request) (cadr request) lib (cdr previous))))
             (proof-with-checked-results
                 ((rest (b1-arrays-assoc-returned-key-leaves (cdr requests) lib leaf)))
               (cons (cons (cons request (car leaf)) (car rest)) (cdr rest)))))))

(defun b1-arrays-assoc-returned-key (lib)
  (let ((name (proof-sym "SELF-ASSOC-RETURNED-KEY" "ACL2"))
        (proof (library-library-proof lib)))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name lib)
      (let* ((call (list *b1-arrays-assoc* *library-x* *library-y*))
             (template (list *library-implies* (list *proof-consp* *proof-result*)
                             (proof-eq (list *library-car* *proof-result*) *library-x*)))
             (formula (list *library-implies* (list *proof-consp* call)
                            (proof-eq (list *library-car* call) *library-x*)))
             (induction (b1-induction-tree-induction-init lib formula *library-y*)))
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof call))
             (body (b1-logic-step-at opened 2))
             (requests (proof-proof-by-value-leaves proof body nil))
             (leaves (b1-arrays-assoc-returned-key-leaves requests lib (cons nil induction)))
             (step (proof-proof-by-value proof body template (car leaves) nil))
             (reversed (proof-proof-symmetric proof opened))
             (step (proof-proof-rewrite-result proof step reversed template *proof-result*))
             (finished (b1-induction-tree-induction-finish (cdr leaves) step))
             (updated (library-library-lemma lib "ASSOC-RETURNED-KEY" formula finished nil)))
          (cons name updated))))))

(defun b1-arrays-header-key-from-cons (lib header cons-step)
  (proof-with-checked-results
      ((opened (b1-arrays-normalize lib header nil (list *b1-arrays-header*)))
       (body (b1-logic-step-at opened 2))
       (parts (proof-list-of-length body 3))
       (lemma (b1-arrays-assoc-returned-key lib)))
    (let* ((updated (cdr lemma))
           (proof (library-library-proof updated)))
      (proof-with-checked-results
          ((law (proof-proof-fact proof (car lemma)
                                  (list (list *library-x* (cadr parts))
                                        (list *library-y* (caddr parts)))))
           (association (proof-proof-rewrite proof cons-step opened '(1 1)))
           (result (proof-proof-modus-ponens proof law association))
           (reversed (proof-proof-symmetric proof opened))
           (step (proof-proof-rewrite proof result reversed '(1 1 1))))
        (cons step updated)))))

(defun b1-arrays-header-key-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((goal (proof-term-at formula 2))
         (left (proof-term-at goal 1))
         (header (proof-term-at left 1))
         (assertion (b1-logic-step-first premise))
         (known (b1-logic-bookproof-from-fact
                 lib (proof-sym "ARRAY1P-CONSP-HEADER" "ACL2")
                 (list *library-implies* assertion (list *proof-consp* header))))
         (cons-step (proof-proof-modus-ponens proof known premise)))
      (b1-arrays-header-key-from-cons lib header cons-step))))

(defun b1-arrays-header-key (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-header-key-consequence premise lib formula))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-arrays-initialized-header-key (lib premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((assertion (b1-logic-step-first premise)))
      (let ((header (cons *b1-arrays-header* (cdr assertion))))
        (proof-with-checked-results
            ((law (b1-arrays-header-exists
                   lib (list *library-implies* assertion (list *proof-consp* header))))
             (cons-step (proof-proof-modus-ponens proof law premise)))
          (b1-arrays-header-key-from-cons lib header cons-step))))))

(defun b1-arrays-integer-key-not-header (lib integral)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((index (b1-logic-step-at integral 1)))
      (let ((claim (proof-eq index *b1-arrays-header-key*)))
        (proof-with-checked-results
            ((numeric (b1-arithmetic-known-type lib *library-numberp* index (list integral)))
             (law (proof-proof-fact proof "acl2-numberp-not-symbolp"
                                    (list (list *library-x* index))))
             (not-symbol (proof-proof-modus-ponens proof law numeric))
             (keyword (b1-arrays-normalize-proof
                       lib (list *b1-logic-symbolp* *b1-arrays-header-key*)))
             (same (proof-proof-assume proof claim t))
             (reversed (proof-proof-symmetric proof same))
             (impossible (proof-proof-rewrite proof keyword reversed '(1 1)))
             (contradiction (proof-proof-cut proof impossible not-symbol)))
          (proof-proof-front proof contradiction (proof-neg claim)))))))

(defun b1-arrays-integer-read-guard (lib integral)
  (proof-with-checked-results
      ((not-header (b1-arrays-integer-key-not-header lib integral))
       (index (b1-logic-step-at integral 1)))
    (b1-arrays-normalize lib (proof-neg (list *b1-logic-eq* index *b1-arrays-header-key*))
                         (list not-header) (list *proof-not* *b1-logic-eq*))))

(defun b1-arrays-association-at-front (lib term comparison)
  (b1-arrays-normalize lib term (list comparison)
                       (list *b1-arrays-assoc* *b1-logic-endp* *b1-logic-atom* *proof-not*)))

(defun b1-arrays-header-at-front (lib name items comparison)
  (proof-with-checked-results
      ((opened (b1-arrays-normalize lib (list *b1-arrays-header* name items)
                                   nil (list *b1-arrays-header*)))
       (body (b1-logic-step-at opened 2))
       (association (b1-arrays-association-at-front lib body comparison)))
    (proof-proof-chain (library-library-proof lib) opened (list association))))

(defun b1-arrays-array-fields-equal (lib claim headers)
  (b1-arrays-normalize-proof lib claim nil *b1-arrays-projections*
                             (list (b1-logic-equal-to headers))))

(defun b1-arrays-field-equation (lib field name new old headers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (b1-arrays-normalize
                lib (list field name new) nil (list field) (list (b1-logic-equal-to headers))))
         (right (b1-arrays-normalize lib (list field name old) nil (list field)))
         (reversed (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list reversed)))))

(defun b1-arrays-compress-array-properties-consequence-leaf
    (value tests lib name header comparison template)
  (declare (ignore tests))
  (if (proof-is-call value *proof-cons*)
      (b1-arrays-header-at-front lib name value comparison)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((reduction (b1-arrays-normalize lib value))
           (reflexive (proof-proof-reflexive proof header))
           (reversed (proof-proof-symmetric proof reduction)))
        (proof-proof-rewrite-result proof reflexive reversed template *proof-result*)))))

(defun b1-arrays-compress-array-properties-leaves
    (requests lib name header comparison template previous)
  (declare (xargs :measure (acl2-count requests)))
  (cond ((failure-p previous) previous)
        ((endp requests) nil)
        (t (let* ((request (car requests))
                  (step (b1-arrays-compress-array-properties-consequence-leaf
                         (car request) (cadr request) lib name header comparison template)))
             (proof-with-checked-results
                 ((rest (b1-arrays-compress-array-properties-leaves
                         (cdr requests) lib name header comparison template step)))
               (cons (cons request step) rest))))))

(defun b1-arrays-compress-array-properties-consequence (premise lib claim)
  (proof-with-checked-results
      ((assertion (b1-logic-step-first premise))
       (args (proof-list-of-length (cdr assertion) 2)))
    (let* ((name (car args))
           (data (cadr args))
           (header (list *b1-arrays-header* name data)))
      (proof-with-checked-results ((key (b1-arrays-initialized-header-key lib premise)))
        (let* ((updated (cdr key))
               (proof (library-library-proof updated)))
          (proof-with-checked-results
              ((comparison (proof-proof-symmetric proof (car key)))
               (opened (b1-arrays-normalize updated (list *b1-arrays-compress* name data)
                                            nil (list *b1-arrays-compress*))))
            (let ((template (proof-eq (list *b1-arrays-header* name *proof-result*) header)))
              (proof-with-checked-results
                  ((body (b1-logic-step-at opened 2))
                   (requests (proof-proof-by-value-leaves proof body nil))
                   (leaves (b1-arrays-compress-array-properties-leaves
                            requests updated name header comparison template nil))
                   (headers (proof-proof-by-value proof body template leaves nil))
                   (reversed (proof-proof-symmetric proof opened))
                   (headers (proof-proof-rewrite-result
                             proof headers reversed template *proof-result*))
                   (step (b1-arrays-array-fields-equal updated claim headers)))
                (cons step updated)))))))))

(defun b1-arrays-compress-array-properties (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-compress-array-properties-consequence premise lib claim))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-arrays-inserted-header (lib name data index value integral)
  (let ((proof (library-library-proof lib))
        (items (list *proof-cons* (list *proof-cons* index value) data)))
    (proof-with-checked-results
        ((not-header (b1-arrays-integer-key-not-header lib integral))
         (comparison (b1-reciprocal-reverse-inequality lib not-header))
         (opened (b1-arrays-header-at-front lib name items comparison))
         (before (b1-arrays-normalize lib (list *b1-arrays-header* name data)
                                     nil (list *b1-arrays-header*)))
         (reversed (proof-proof-symmetric proof before)))
      (proof-proof-chain proof opened (list reversed)))))

(defun b1-arrays-inserted-properties (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (first (proof-term-at goal 1))
       (sides (proof-list-of-length first 3))
       (new (proof-list-of-length (cadr sides) 3))
       (old (proof-list-of-length (caddr sides) 3))
       (items (proof-list-of-length (caddr new) 3))
       (entry (proof-list-of-length (cadr items) 3))
       (integral (b1-logic-bookproof-prove-implication-premise lib formula))
       (headers (b1-arrays-inserted-header
                 lib (cadr new) (caddr old) (cadr entry) (caddr entry) integral))
       (consequence (b1-arrays-array-fields-equal lib goal headers)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula integral consequence)))

(defun b1-arrays-inserted-array-supported (lib evidence previous)
  (declare (xargs :measure (acl2-count evidence)))
  (cond ((failure-p previous) previous)
        ((endp evidence) nil)
        (t
         (let ((step (proof-with-checked-results
                         ((term (b1-logic-step-first (car evidence)))
                          (reduction (b1-arrays-normalize
                                      lib term nil (list *b1-arrays-dimensions* *b1-arrays-header*))))
                       (proof-proof-rewrite
                        (library-library-proof lib) (car evidence) reduction '(1)))))
           (proof-with-checked-results
               ((rest (b1-arrays-inserted-array-supported lib (cdr evidence) step)))
             (cons step rest))))))

(defun b1-arrays-inserted-array (lib data-type index value evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (b1-logic-step-first data-type))
         (parts (proof-list-of-length literal 3))
         (rule (proof-proof-fact proof (proof-sym "ARRAY1P-CONS" "ACL2")
                                 (list (list *b1-arrays-name* (cadr parts))
                                       (list *b1-arrays-l* (caddr parts))
                                       (list *b1-arrays-n* index)
                                       (list *b1-arrays-val* value))))
         (supported (b1-arrays-inserted-array-supported lib evidence nil))
         (guard-term (b1-logic-step-at rule 1))
         (guard (b1-arrays-normalize lib guard-term))
         (bound-term (b1-logic-step-at guard 2))
         (bound (b1-arrays-normalize-proof lib bound-term (cons data-type supported)))
         (condition (proof-proof-transport proof bound guard)))
      (proof-proof-modus-ponens proof rule condition))))

(defun b1-arrays-update-paths-leaves (requests on-inserted on-compressed)
  (declare (xargs :measure (acl2-count requests)))
  (if (endp requests)
      nil
    (let ((request (car requests)))
      (cons (cons request (if (proof-is-call (car request) *b1-arrays-compress*)
                              on-compressed
                            on-inserted))
            (b1-arrays-update-paths-leaves (cdr requests) on-inserted on-compressed)))))

(defun b1-arrays-update-paths (lib call template on-inserted on-compressed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-arrays-normalize lib call nil (list *b1-arrays-update*)))
         (body (b1-logic-step-at opened 2))
         (requests (proof-proof-by-value-leaves proof body nil))
         (branches (proof-proof-by-value
                    proof body template
                    (b1-arrays-update-paths-leaves requests on-inserted on-compressed) nil))
         (reversed (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite-result proof branches reversed template *proof-result*))))

(defun b1-arrays-update-is-array-consequence (premise lib name update index value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-logic-bookproof-split-conjuncts lib premise))
         (inserted (b1-arrays-inserted-array lib (car fields) index value (cdr fields)))
         (items (b1-logic-step-at inserted 2))
         (compression-law (proof-proof-fact
                           proof (proof-sym "ARRAY1P-COMPRESS1" "ACL2")
                           (list (list *b1-arrays-name* name) (list *b1-arrays-l* items))))
         (compressed (proof-proof-modus-ponens proof compression-law inserted)))
      (b1-arrays-update-paths lib update (list *b1-arrays-array* name *proof-result*)
                              inserted compressed))))

(defun b1-arrays-update-is-array (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (goal-parts (proof-list-of-length goal 3))
       (update (proof-list-of-length (caddr goal-parts) 5))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-update-is-array-consequence
                     premise lib (cadr goal-parts) update (cadddr update) (nth 4 update))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-arrays-update-array-properties-consequence
    (premise lib formula name update old-header data index value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (if (consp (cdr fields))
                    fields
                  '(:failure "failure" "")))
         (inserted (b1-arrays-inserted-array lib (car parts) index value (cdr parts)))
         (add-header (b1-arrays-inserted-header lib name data index value (cadr parts)))
         (items (b1-logic-step-at inserted 2))
         (rule (proof-proof-fact
                proof (proof-sym "ARRAY1P-COMPRESS1-PROPERTIES" "ACL2")
                (list (list *b1-arrays-name* name) (list *b1-arrays-l* items))))
         (properties (proof-proof-modus-ponens proof rule inserted))
         (compressed (b1-logic-bookproof-split-conjuncts-first lib properties))
         (compressed-header (proof-proof-chain proof compressed (list add-header)))
         (headers (b1-arrays-update-paths
                   lib update (proof-eq (list *b1-arrays-header* name *proof-result*) old-header)
                   add-header compressed-header))
         (claim (proof-term-at formula 2)))
      (b1-arrays-array-fields-equal lib claim headers))))

(defun b1-arrays-update-array-properties (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (header-eq (proof-term-at claim 1))
       (sides (proof-list-of-length header-eq 3))
       (header (proof-list-of-length (cadr sides) 3))
       (update (proof-list-of-length (caddr header) 5))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-update-array-properties-consequence
                     premise lib formula (cadr header) update (caddr sides)
                     (caddr update) (cadddr update) (nth 4 update))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-arrays-inserted-value (lib name data store value fetch read-integer comparison headers)
  (let* ((proof (library-library-proof lib))
         (pair (list *proof-cons* store value))
         (new (list *proof-cons* pair data)))
    (proof-with-checked-results
        ((read-guard (b1-arrays-integer-read-guard lib read-integer))
         (lookup (b1-arrays-association-at-front lib (list *b1-arrays-assoc* fetch new) comparison)))
      (let ((unfold (list *b1-arrays-read* (proof-cl "NULL") *proof-not* *b1-logic-eq*))
            (rules (list (b1-logic-equal-to read-guard) (b1-logic-equal-to lookup))))
        (if (equal store fetch)
            (proof-with-checked-results
                ((some-cons (proof-proof-fact
                             proof "consp-cons"
                             (list (list *library-x* store) (list *library-y* value))))
                 (empty (proof-eq pair *proof-false*))
                 (empty-step (proof-proof-assume proof empty t))
                 (impossible (proof-proof-rewrite proof some-cons empty-step '(1 1)))
                 (simplified (proof-proof-simplify-first proof impossible nil nil))
                 (nonempty (proof-proof-front proof simplified (proof-neg empty))))
              (b1-arrays-normalize lib (list *b1-arrays-read* name new fetch)
                                   (list nonempty) unfold rules))
          (proof-with-checked-results
              ((default (b1-arrays-field-equation lib *b1-arrays-default* name new data headers))
               (left (b1-arrays-normalize lib (list *b1-arrays-read* name new fetch) nil
                                          unfold (append rules (list (b1-logic-equal-to default))) t))
               (right (b1-arrays-normalize lib (list *b1-arrays-read* name data fetch) nil
                                           unfold (list (car rules)) t))
               (reversed (proof-proof-symmetric proof right)))
            (proof-proof-chain proof left (list reversed))))))))

(defun b1-arrays-read-updated-array-consequence
    (premise lib name data store value fetch same update expected)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-logic-bookproof-split-conjuncts lib premise)))
      (let* ((array (car fields))
             (tests (cdr fields))
             (store-tests (seq-slice tests 0 3))
             (read-tests (if same store-tests (seq-slice tests 3 6))))
        (proof-with-checked-results
            ((comparison (if same
                             (proof-proof-reflexive proof fetch)
                           (if (consp tests)
                               (b1-reciprocal-reverse-inequality lib (car (last tests)))
                             '(:failure "failure" ""))))
             (inserted (b1-arrays-inserted-array lib array store value store-tests))
             (new (b1-logic-step-at inserted 2))
             (store-integer (b1-arrays-list-at store-tests 0))
             (headers (b1-arrays-inserted-header lib name data store value store-integer))
             (read-integer (b1-arrays-list-at read-tests 0))
             (raw-value (b1-arrays-inserted-value
                         lib name data store value fetch read-integer comparison headers))
             (dimension (b1-arrays-field-equation lib *b1-arrays-dimensions* name new data headers))
             (read-upper (b1-arrays-list-at read-tests 2))
             (reversed (proof-proof-symmetric proof dimension))
             (upper-bound (proof-proof-rewrite proof read-upper reversed '(1 2 1)))
             (law (proof-proof-fact proof (proof-sym "AREF1-COMPRESS1" "ACL2")
                                    (list (list *b1-arrays-name* name) (list *b1-arrays-l* new)
                                          (list *b1-arrays-n* fetch))))
             (guard-term (b1-logic-step-at law 1))
             (guard (b1-arrays-normalize-proof
                     lib guard-term (cons inserted (append (seq-slice read-tests 0 2)
                                                           (list upper-bound)))))
             (compressed (proof-proof-modus-ponens proof law guard))
             (compressed (proof-proof-chain proof compressed (list raw-value))))
          (b1-arrays-update-paths lib update
                                  (proof-eq (list *b1-arrays-read* name *proof-result* fetch)
                                            expected)
                                  raw-value compressed))))))

(defun b1-arrays-read-updated-array (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (sides (proof-list-of-length goal 3))
       (read (proof-list-of-length (cadr sides) 4))
       (update (proof-list-of-length (caddr read) 5)))
    (let* ((store (cadddr update))
           (fetch (cadddr read))
           (same (equal store fetch)))
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-arrays-read-updated-array-consequence
                         premise lib (cadr read) (caddr update) store (nth 4 update)
                         fetch same update (caddr sides))))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))))

(defun b1-arrays-read-updated-array-cases-consequence
    (premise lib name data store value fetch test choices n1 n2)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((bounds (b1-logic-bookproof-split-conjuncts lib premise))
         (hit (proof-proof-fact proof (proof-sym "AREF1-ASET1-EQUAL" "ACL2")
                                (list (list *b1-arrays-name* name) (list *b1-arrays-l* data)
                                      (list *b1-arrays-n* store) (list *b1-arrays-val* value))))
         (hit-term (b1-logic-step-at hit 1))
         (hit-guard (b1-arrays-normalize-proof lib hit-term (seq-slice bounds 0 4)))
         (yes (proof-proof-modus-ponens proof hit hit-guard))
         (equal-index (proof-proof-assume proof test t))
         (yes (proof-proof-rewrite proof yes equal-index '(1 1 3)))
         (yes-choice (proof-proof-if-true proof choices))
         (reversed (proof-proof-symmetric proof yes-choice))
         (yes (proof-proof-chain proof yes (list reversed)))
         (miss (proof-proof-fact proof (proof-sym "AREF1-ASET1-NOT-EQUAL" "ACL2")
                                 (list (list *b1-arrays-name* name) (list *b1-arrays-l* data)
                                       (list n1 store) (list n2 fetch) (list *b1-arrays-val* value))))
         (miss-term (b1-logic-step-at miss 1))
         (unequal-index (proof-proof-assume proof test nil))
         (miss-guard (b1-arrays-normalize-proof
                      lib miss-term (append bounds (list unequal-index))))
         (no (proof-proof-modus-ponens proof miss miss-guard))
         (no-choice (proof-proof-if-false proof choices))
         (reversed (proof-proof-symmetric proof no-choice))
         (no (proof-proof-chain proof no (list reversed))))
      (proof-proof-cases proof test yes no))))

(defun b1-arrays-read-updated-array-cases (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (sides (proof-list-of-length goal 3))
       (test (proof-term-at (caddr sides) 1))
       (read (proof-list-of-length (cadr sides) 4))
       (update (proof-list-of-length (caddr read) 5)))
    (let ((n1 (proof-sym "N1" "ACL2"))
          (n2 (proof-sym "N2" "ACL2")))
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-arrays-read-updated-array-cases-consequence
                         premise lib (cadr read) (caddr update) (cadddr update) (nth 4 update)
                         (cadddr read) test (caddr sides) n1 n2)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))))

(defun b1-arrays-lookup-header-only (lib header key integral)
  (let ((proof (library-library-proof lib))
        (items (list *proof-cons* header *proof-false*)))
    (proof-with-checked-results
        ((comparison (b1-arrays-integer-key-not-header lib integral))
         (reversed (proof-proof-symmetric proof key))
         (comparison (proof-proof-rewrite proof comparison reversed '(1 1 2)))
         (index (b1-logic-step-at integral 1))
         (lookup (b1-arrays-association-at-front lib (list *b1-arrays-assoc* index items) comparison))
         (body (b1-logic-step-at lookup 2))
         (normalized (b1-arrays-normalize
                      lib body nil
                      (list *b1-arrays-assoc* *b1-logic-endp* *b1-logic-atom* *proof-not*))))
      (proof-proof-chain proof lookup (list normalized)))))

(defun b1-arrays-scan-header-only-consequence
    (premise lib call end delta successor bindings formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length fields 3)))
      (let ((header (car parts))
            (int-i (cadr parts))
            (int-j (caddr parts))
            (types (cdr parts)))
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof call))
             (body (b1-logic-step-at opened 2))
             (empty (proof-proof-if-true proof body))
             (base (proof-proof-chain proof opened (list empty)))
             (no-end (proof-proof-assume proof end nil))
             (delta-integer (library-library-type-of lib delta types))
             (gap-positive (b1-integer-no-zp lib delta no-end delta-integer))
             (comparison (library-library-comparison lib *b1-arrays-i* *b1-arrays-j* types))
             (in-range (proof-proof-transport proof gap-positive comparison))
             (one-positive (proof-proof-prove proof (library-positive *proof-one*) nil nil))
             (advances (library-library-less-from-difference
                        lib *b1-arrays-i* successor one-positive types))
             (int-next (library-library-type-of lib successor types))
             (descent (library-library-cite
                       lib "GAP-DECREASE" (list *b1-arrays-j* *b1-arrays-i* successor)
                       (list int-j int-i int-next in-range advances)))
             (child (proof-subst formula bindings))
             (smaller (b1-logic-step-first descent))
             (assumption (proof-proof-assume proof (proof-ite smaller child *proof-true*) t))
             (hypothesis (proof-proof-prove-if proof assumption descent))
             (child-guard (proof-term-at child 1))
             (guard (b1-arrays-normalize-proof lib child-guard (list header int-next int-j)))
             (recursive (proof-proof-modus-ponens proof hypothesis guard))
             (lookup (b1-arrays-lookup-header-only lib *library-x* header int-i))
             (step (b1-arrays-normalize
                    lib call (list no-end)
                    (list *b1-arrays-scan* (proof-cl "NULL") *proof-not* *b1-logic-eq*)
                    (list (b1-logic-equal-to lookup))))
             (step (proof-proof-chain proof step (list recursive))))
          (proof-proof-cases proof end base step))))))

(defun b1-arrays-scan-header-only (lib)
  (let ((label (proof-sym "SELF-COMPRESS11-HEADER-ONLY" "ACL2"))
        (proof (library-library-proof lib)))
    (if (assoc-equal label (proof-proof-facts proof))
        (cons label lib)
      (let* ((items (list *proof-cons* *library-x* *proof-false*))
             (call (list *b1-arrays-scan* *b1-arrays-name* items
                         *b1-arrays-i* *b1-arrays-j* *b1-arrays-d*))
             (key (proof-eq (list *library-car* *library-x*) *b1-arrays-header-key*))
             (guard (proof-ite key (proof-ite (library-integer *b1-arrays-i*)
                                             (library-integer *b1-arrays-j*) *proof-false*)
                               *proof-false*))
             (formula (list *library-implies* guard (proof-eq call *proof-false*)))
             (measure (list *library-gap* *b1-arrays-j* *b1-arrays-i*))
             (delta (library-diff *b1-arrays-j* *b1-arrays-i*))
             (end (list *b1-logic-zp* delta))
             (successor (library-plus *b1-arrays-i* *proof-one*))
             (bindings (list (cons *b1-arrays-i* successor))))
        (proof-with-checked-results
            ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (b1-arrays-scan-header-only-consequence
                           premise lib call end delta successor bindings formula))
             (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))
             (ordinal (library-library-cite lib "GAP-ORDINAL" (list *b1-arrays-j* *b1-arrays-i*) nil))
             (step (proof-proof-induct proof ordinal step formula measure
                                       (list (list (list *b1-arrays-i* successor)))))
             (updated (library-library-lemma lib "COMPRESS11-HEADER-ONLY" formula step nil)))
          (cons label updated))))))

(defun b1-arrays-header-only-fields (lib premise only)
  (proof-with-checked-results
      ((assertion (b1-logic-step-first premise))
       (parts (proof-list-of-length (cdr assertion) 2))
       (key (b1-arrays-initialized-header-key lib premise)))
    (let* ((updated (cdr key))
           (proof (library-library-proof updated)))
      (proof-with-checked-results
          ((comparison (proof-proof-symmetric proof (car key)))
           (headers (b1-arrays-header-at-front updated (car parts) only comparison)))
        (cons (list (car key) headers) updated)))))

(defun b1-arrays-reset-contents-consequence (premise lib formula items name data header)
  (proof-with-checked-results ((fields (b1-arrays-header-only-fields lib premise items)))
    (let* ((key (caar fields))
           (headers (cadar fields))
           (updated (cdr fields))
           (proof (library-library-proof updated)))
      (proof-with-checked-results
          ((dimension (b1-arrays-field-equation updated *b1-arrays-dimensions* name items data headers))
           (old-size (b1-arrays-normalize
                      updated (list *b1-arrays-dimensions* name data) nil
                      (list *b1-arrays-dimensions* *b1-arrays-header*))))
        (let ((new-size (list *library-car* (list *b1-arrays-dimensions* name items))))
          (proof-with-checked-results
              ((checks (b1-arrays-array-checks updated premise))
               (integral (proof-term-at checks 5))
               (reversed (proof-proof-symmetric proof old-size))
               (integral (proof-proof-rewrite proof integral reversed '(1 1 1)))
               (reversed (proof-proof-symmetric proof dimension))
               (integral (proof-proof-rewrite proof integral reversed '(1 1 1))))
            (let* ((default (list *b1-arrays-default* name items))
                   (bindings (list (list *b1-arrays-name* name) (list *library-x* header)
                                   (list *b1-arrays-i* *proof-zero*) (list *b1-arrays-j* new-size)
                                   (list *b1-arrays-d* default))))
              (proof-with-checked-results ((lemma (b1-arrays-scan-header-only updated)))
                (let* ((updated (cdr lemma))
                       (proof (library-library-proof updated)))
                  (proof-with-checked-results
                      ((law (proof-proof-fact proof (car lemma) bindings))
                       (guard-term (b1-logic-step-at law 1))
                       (zero-integer (library-library-type-of updated *proof-zero* nil))
                       (guard (b1-arrays-normalize-proof updated guard-term
                                                        (list key integral zero-integer)))
                       (empty (proof-proof-modus-ponens proof law guard))
                       (goal (proof-term-at formula 2))
                       (step (b1-logic-bookproof-case-proof
                              updated goal nil
                              (list *b1-arrays-reset* *b1-arrays-compress*
                                    (proof-cl "REVERSE") (proof-cl "REVAPPEND")
                                    *b1-logic-eql* *b1-logic-eq* *b1-logic-atom*
                                    *b1-logic-endp* *proof-not*)
                              (list (b1-logic-equal-to empty) (b1-logic-equal-to headers)) 16)))
                    (cons step updated)))))))))))

(defun b1-arrays-reset-contents (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (sides (proof-list-of-length claim 3))
       (reset (proof-list-of-length (cadr sides) 3))
       (header (proof-term-at (caddr sides) 1))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-reset-contents-consequence
                     premise lib formula (caddr sides) (cadr reset) (caddr reset) header))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-arrays-reset-fields (lib premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assertion (b1-logic-step-first premise))
         (parts (proof-list-of-length (cdr assertion) 2))
         (law (proof-proof-fact proof (proof-sym "RESET-ARRAY1*" "ACL2")
                                (list (list *b1-arrays-name* (car parts))
                                      (list *b1-arrays-l* (cadr parts)))))
         (reset (proof-proof-modus-ponens proof law premise))
         (items (b1-logic-step-at reset 2))
         (fields (b1-arrays-header-only-fields lib premise items)))
      (cons (cons reset (car fields)) (cdr fields)))))

(defun b1-arrays-reset-properties-consequence (premise lib formula)
  (proof-with-checked-results
      ((fields (b1-arrays-reset-fields lib premise))
       (goal (proof-term-at formula 2))
       (step (b1-arrays-normalize-proof
              (cdr fields) goal nil *b1-arrays-projections*
              (list (b1-logic-equal-to (caar fields)) (b1-logic-equal-to (caddar fields))))))
    (cons step (cdr fields))))

(defun b1-arrays-reset-properties (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-reset-properties-consequence premise lib formula))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-arrays-reset-is-array-consequence (premise lib)
  (proof-with-checked-results
      ((fields (b1-arrays-reset-fields lib premise))
       (assertion (b1-logic-step-first premise))
       (parts (proof-list-of-length (cdr assertion) 2))
       (new (b1-logic-step-at (caar fields) 2))
       (header (proof-term-at new 1)))
    (let* ((reset (caar fields))
           (key (cadar fields))
           (headers (caddar fields))
           (updated (cdr fields))
           (proof (library-library-proof updated))
           (name (car parts))
           (old (cadr parts)))
      (proof-with-checked-results
          ((law (b1-logic-bookproof-from-fact
                 updated (proof-sym "ARRAY1P-CONSP-HEADER" "ACL2")
                 (list *library-implies* assertion (list *proof-consp* header))))
           (some-cons (proof-proof-modus-ponens proof law premise))
           (before (b1-arrays-normalize updated (list *b1-arrays-header* name old)
                                        nil (list *b1-arrays-header*)))
           (after (b1-arrays-normalize updated (list *b1-arrays-header* name new)
                                       nil (list *b1-arrays-header*)))
           (reversed (proof-proof-symmetric proof after))
           (association (proof-proof-chain proof reversed (list headers before)))
           (checks (b1-arrays-array-checks updated premise))
           (dimension (proof-term-at checks 5))
           (bound (b1-logic-step-at dimension 1)))
        (let* ((other-defs (list *b1-logic-atom* *b1-logic-endp* *proof-not*
                                 *b1-logic-eq* (proof-cl "NULL")))
               (alist-defs (cons *b1-arrays-alistp* other-defs))
               (bounded-defs (cons *b1-arrays-bounded* other-defs)))
          (proof-with-checked-results
              ((empty-alist (b1-arrays-normalize
                             updated (list *b1-arrays-alistp* *proof-false*) nil alist-defs))
               (empty-bounded (b1-arrays-normalize
                               updated (list *b1-arrays-bounded* *proof-false* bound)
                               nil bounded-defs))
               (alist (b1-arrays-normalize-proof
                       updated (list *b1-arrays-alistp* new) (list some-cons)
                       alist-defs (list (b1-logic-equal-to empty-alist))))
               (bounded (b1-arrays-normalize-proof
                         updated (list *b1-arrays-bounded* new bound) (list some-cons key)
                         bounded-defs (list (b1-logic-equal-to empty-bounded))))
               (definition (b1-arrays-normalize
                            updated (list *b1-arrays-array* name new) nil (list *b1-arrays-array*)
                            (list (b1-logic-equal-to association)) t))
               (definition-term (b1-logic-step-at definition 2))
               (opened (b1-arrays-normalize-proof updated definition-term
                                                  (append checks (list alist bounded))))
               (result (proof-proof-transport proof opened definition))
               (reversed (proof-proof-symmetric proof reset))
               (step (proof-proof-rewrite proof result reversed '(1 2))))
            (cons step updated)))))))

(defun b1-arrays-reset-is-array (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-reset-is-array-consequence premise lib))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-arrays-read-reset-array-consequence (premise lib left expected name)
  (proof-with-checked-results
      ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
       (parts (proof-list-of-length conjuncts 2))
       (fields (b1-arrays-reset-fields lib (car parts)))
       (data (b1-logic-step-at (car parts) 2))
       (only (b1-logic-step-at (caar fields) 2))
       (header (proof-term-at only 1)))
    (let* ((reset (caar fields))
           (key (cadar fields))
           (headers (caddar fields))
           (updated (cdr fields))
           (integral (cadr parts)))
      (proof-with-checked-results
          ((lookup (b1-arrays-lookup-header-only updated header key integral))
           (default (b1-arrays-field-equation updated *b1-arrays-default* name only data headers))
           (law (b1-arrays-integer-read-guard updated integral))
           (result (b1-arrays-normalize
                    updated left nil
                    (list *b1-arrays-read* (proof-cl "NULL") *b1-logic-eq* *proof-not*)
                    (list (b1-logic-equal-to reset) (b1-logic-equal-to law)
                          (b1-logic-equal-to lookup) (b1-logic-equal-to default))))
           (right (b1-logic-step-at result 2)))
        (if (equal right expected)
            (cons result updated)
          '(:failure "failure" ""))))))

(defun b1-arrays-read-reset-array (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (sides (proof-list-of-length goal 3))
       (left (proof-list-of-length (cadr sides) 4))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-read-reset-array-consequence
                     premise lib left (caddr sides) (cadr left)))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-arrays-array-forward-modular-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-arrays-array-checks lib premise))
         (bounds (proof-list-of-length (seq-slice fields 5 7) 2))
         (strict (proof-term-at fields 8))
         (strict-term (b1-logic-step-first strict))
         (weak (library-library-cite lib "LESS-TO-WEAK" (cdr strict-term)
                                     (list (car bounds) (cadr bounds) strict)))
         (claim (proof-term-at formula 2))
         (definition (b1-arrays-normalize
                      lib claim nil (list *b1-arrays-header* *b1-arrays-dimensions*
                                          *b1-arrays-maximum*) nil t))
         (body (b1-logic-step-at definition 2))
         (step (b1-arrays-normalize-proof lib body (append fields (list weak)))))
      (proof-proof-transport proof step definition))))

(defun b1-arrays-array-forward-modular (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-arrays-array-forward-modular-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
