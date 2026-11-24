(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *proper-lists-true-list* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *proper-lists-list-types*
  (list (proof-sym "CHARACTER-LISTP" "ACL2")
        (proof-sym "STRING-LISTP" "ACL2")
        (proof-sym "SYMBOL-LISTP" "ACL2")
        (proof-sym "NAT-LISTP" "ACL2")))

(defun proper-lists-definitions (lib)
  (proof-proof-definitions (library-library-proof lib)))

(defun proper-lists-recognizer-definition (lib predicate limit)
  (let ((definition (assoc-equal predicate (proper-lists-definitions lib))))
    (and definition
         (equal (len (cadr definition)) 1)
         (proof-with-checked-results ((fits (book-logic-within-size (caddr definition) limit)))
           (and fits definition)))))

(defun proper-lists-known-lemma-p (lib name)
  (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
               (proof-proof-facts (library-library-proof lib))))

(defun proper-lists-hash-name (prefix datum)
  (proof-with-checked-results ((source (proof-write datum)))
    (concatenate 'string prefix
                 (text-upper (seq-slice (siphash-hexdigest source) 0 16)))))

(defun proper-lists-check-arity (items count)
  (proof-with-checked-results ((parts (proof-list-of-length items count)))
    nil))

(defun proper-lists-first-right (step)
  (proof-with-checked-results ((formula (proof-step-first step)))
    (proof-term-at formula 2)))

(defun proper-lists-reduce (lib term evidence definitions expose budget size)
  (proof-with-checked-results
      ((reducer (book-logic-reducer-init lib evidence definitions expose budget size nil nil)))
    (car (book-logic-reducer-reduce reducer term nil))))

(defun proper-lists-add-rule (lib label formula step)
  (let ((updated (library-library-lemma lib label formula step nil)))
    (if (failure-p updated)
        (cons updated lib)
      (cons label updated))))

(defun proper-lists-proper-list-rule-branch (shape lib definitions typed premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proper-lists-reduce lib typed (list shape) definitions t 45 120)))
      (if step
          (proof-with-checked-results ((rewritten (proof-proof-rewrite proof premise step '(1))))
            (proof-proof-tidy proof rewritten))
        premise))))

(defun proper-lists-proper-list-rule-proof (lib predicate)
  (let* ((proof (library-library-proof lib))
         (typed (list predicate *library-x*))
         (result (list *proper-lists-true-list* *library-x*))
         (cons-test (list *proof-consp* *library-x*))
         (formula (list *library-implies* typed result)))
    (proof-with-checked-results
        ((premise (proof-proof-assume proof typed t))
         (when-cons (proof-proof-assume proof cons-test t))
         (when-atom (proof-proof-assume proof cons-test nil))
         (definitions (list predicate *rulers-atom* *rulers-endp*
                            (proof-cl "EQ") *proof-not*))
         (nil-test (proper-lists-proper-list-rule-branch
                    when-atom lib definitions typed premise))
         (nil-formula (proof-step-first nil-test)))
      (if (not (equal nil-formula (proof-eq *library-x* *proof-false*)))
          nil
        (proof-with-checked-results
            ((remains (proper-lists-proper-list-rule-branch
                       when-cons lib definitions typed premise))
             (tail-argument (list *library-cdr* *library-x*))
             (tail (list predicate tail-argument))
             (rulers (rulers-rulers-init lib nil nil))
             (remains-formula (proof-step-first remains))
             (tail-type (rulers-rulers-expand-first 1000000 rulers remains-formula
                                                    t remains tail)))
          (and tail-type
               (proof-with-checked-results
                   ((nil-list
                     (proof-proof-prove proof (list *proper-lists-true-list* *proof-false*)
                                        nil (list *proper-lists-true-list* (proof-cl "EQ"))))
                    (reverse-nil (proof-proof-symmetric proof nil-test))
                    (base (proof-proof-rewrite proof nil-list reverse-nil '(1 1)))
                    (induction (book-logic-tree-induction-init lib formula *library-x*))
                    (bound (library-library-builtin lib 3 *library-x*))
                    (smaller (proof-proof-discharge proof bound when-cons))
                    (descent (book-logic-tree-induction-at induction tail-argument smaller nil))
                    (instance (car descent))
                    (proper-tail (proof-proof-modus-ponens proof instance tail-type))
                    (opened (proof-proof-unfold proof result))
                    (opened-value (proper-lists-first-right opened))
                    (choice (proof-proof-select proof opened-value when-cons))
                    (selected (proof-proof-chain proof opened (list choice)))
                    (step (proof-proof-transport proof proper-tail selected))
                    (branches (proof-proof-cases proof cons-test step base))
                    (implication (witnesses-prove-implication lib formula premise branches)))
                 (book-logic-tree-induction-finish (cdr descent) implication))))))))

(defun proper-lists-proper-list-rule (lib predicate)
  (let ((definition (proper-lists-recognizer-definition lib predicate 90)))
    (if (or (not definition) (failure-p definition))
        (cons definition lib)
      (let ((name (proper-lists-hash-name "PROPER-LIST-" (cons predicate (cdr definition)))))
        (cond ((failure-p name) (cons name lib))
              ((proper-lists-known-lemma-p lib name) (cons name lib))
              (t
               (let ((step (proper-lists-proper-list-rule-proof lib predicate)))
                 (if (or (not step) (failure-p step))
                     (cons step lib)
                   (let ((formula (list *library-implies* (list predicate *library-x*)
                                        (list *proper-lists-true-list* *library-x*))))
                     (proper-lists-add-rule lib name formula step))))))))))

(defun proper-lists-proper-list-search-available (evidence value available)
  (declare (xargs :measure (acl2-count evidence)))
  (if (endp evidence)
      available
    (proof-with-checked-results ((formula (proof-step-first (car evidence))))
      (proper-lists-proper-list-search-available
       (cdr evidence) value
       (if (and (proof-compound formula) (equal (cdr formula) (list value)))
           (table-put available (car formula) (car evidence))
         available)))))

(defun proper-lists-proper-list-search-candidate (lib value predicate evidence)
  (let* ((result (proper-lists-proper-list-rule lib predicate))
         (rule (car result))
         (lib (cdr result)))
    (cond ((failure-p rule) result)
          ((not rule) (cons :continue lib))
          (t
           (cons (proof-with-checked-results ((implication (library-library-cite
                                                    lib rule (list value) nil)))
                   (proof-proof-modus-ponens (library-library-proof lib)
                                             implication evidence))
                 lib)))))

(defun proper-lists-proper-list-search-candidates (lib value available predicates)
  (declare (xargs :measure (acl2-count predicates)))
  (if (endp predicates)
      (cons nil lib)
    (let ((predicate (car predicates)))
      (cond ((equal predicate *proper-lists-true-list*)
             (proper-lists-proper-list-search-candidates lib value available (cdr predicates)))
            ((assoc-equal predicate available)
             (let ((result (proper-lists-proper-list-search-candidate
                            lib value predicate (cdr (assoc-equal predicate available)))))
               (if (eq (car result) :continue)
                   (proper-lists-proper-list-search-candidates
                    (cdr result) value available (cdr predicates))
                 result)))
            (t (cons (list :call (list predicate value) nil
                            (list value predicate available (cdr predicates)))
                     lib))))))

(defun proper-lists-proper-list-search (lib value evidence)
  (let ((available (proper-lists-proper-list-search-available evidence value nil)))
    (if (failure-p available)
        (cons available lib)
      (proper-lists-proper-list-search-candidates
       lib value available
       (proof-unique (append (table-keys available) *proper-lists-list-types*))))))

(defun proper-lists-proper-list-search-resume (lib continuation answer)
  (let ((value (car continuation))
        (predicate (cadr continuation))
        (available (caddr continuation))
        (predicates (cadddr continuation)))
    (cond ((terms-unproved-p answer)
           (proper-lists-proper-list-search-candidates lib value available predicates))
          ((failure-p answer) (cons answer lib))
          (t
           (let ((result (proper-lists-proper-list-search-candidate lib value predicate answer)))
             (if (eq (car result) :continue)
                 (proper-lists-proper-list-search-candidates
                  (cdr result) value available predicates)
               result))))))

(defun proper-lists-cons-type-rule-selectors (lib step selectors)
  (declare (xargs :measure (acl2-count selectors)))
  (if (endp selectors)
      step
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((law (library-library-axiom lib (car selectors) (list *library-x* *library-y*)))
           (rewritten (proof-proof-rewrite-first proof step law)))
        (proper-lists-cons-type-rule-selectors lib rewritten (cdr selectors))))))

(defun proper-lists-cons-type-rule-proof (lib predicate)
  (let ((call (list predicate (list *proof-cons* *library-x* *library-y*)))
        (definitions (list predicate *rulers-atom* *rulers-endp* *proof-not*)))
    (proof-with-checked-results ((opened (proper-lists-reduce lib call nil definitions t 45 145)))
      (and opened
           (proof-with-checked-results
               ((proof (proper-lists-cons-type-rule-selectors lib opened '("CAR-CONS" "CDR-CONS")))
                (value (proper-lists-first-right proof))
                (tail (list predicate *library-y*)))
             (and (or (equal value tail)
                      (and (proof-is-call value *proof-if*)
                           (equal (cddr value) (list tail *proof-false*))))
                  proof))))))

(defun proper-lists-cons-type-rule (lib predicate)
  (let ((definition (proper-lists-recognizer-definition lib predicate 105)))
    (if (or (not definition) (failure-p definition))
        (cons definition lib)
      (let ((label (proper-lists-hash-name "CONS-TYPE-" (cons predicate (cdr definition)))))
        (cond ((failure-p label) (cons label lib))
              ((proper-lists-known-lemma-p lib label) (cons label lib))
              (t
               (let ((step (proper-lists-cons-type-rule-proof lib predicate)))
                 (if (or (not step) (failure-p step))
                     (cons step lib)
                   (let ((formula (proof-step-first step)))
                     (if (failure-p formula)
                         (cons formula lib)
                       (proper-lists-add-rule lib label formula step)))))))))))

(defun proper-lists-expose-cons-type-step (lib formula evidence source rule)
  (if (proof-is-call source *proof-cons*)
      (library-library-cite lib rule (cdr source) nil)
    (let ((proof (library-library-proof lib))
          (definitions (list (car source) (proof-sym "THE-CHECK" "ACL2")
                             *rulers-atom* *rulers-endp* *proof-not*)))
      (proof-with-checked-results
          ((opened (proper-lists-reduce lib source evidence definitions t 63 220)))
        (and opened
             (proof-with-checked-results
                 ((value (proper-lists-first-right opened))
                  (identity (proof-proof-reflexive proof formula))
                  (projected (proof-proof-rewrite proof identity opened '(1 2 1))))
               (cond ((proof-is-call value *proof-cons*)
                      (proof-with-checked-results
                          ((cons-law (library-library-cite lib rule (cdr value) nil)))
                        (proof-proof-chain proof projected (list cons-law))))
                     ((or (proof-is-call value *proof-if*)
                          (proof-is-call value (proof-sym "BINARY-APPEND" "ACL2"))
                          (proof-is-call value (proof-cl "REVAPPEND")))
                      projected)
                     (t nil))))))))

(defun proper-lists-expose-cons-type (lib formula evidence)
  (let ((source (cadr formula)))
    (cond ((not (and (proof-compound formula) (equal (len formula) 2)
                     (proof-compound source)))
           (cons nil lib))
          ((endp source) (cons '(:failure "failure" "") lib))
          ((not (or (assoc-equal (car source) (proper-lists-definitions lib))
                    (proof-is-call source *proof-cons*)))
           (cons nil lib))
          (t
           (let* ((result (proper-lists-cons-type-rule lib (car formula)))
                  (rule (car result))
                  (lib (cdr result)))
             (if (or (not rule) (failure-p rule))
                 result
               (cons (proper-lists-expose-cons-type-step lib formula evidence source rule)
                     lib)))))))
