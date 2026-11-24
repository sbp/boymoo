(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-character-lists-character-list* *b2-list-properties-character-list*)
(defconst *b2-character-lists-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *b2-character-lists-digit* (proof-sym "DIGIT-TO-CHAR" "ACL2"))
(defconst *b2-character-lists-num-chars*
  (proof-sym "EXPLODE-NONNEGATIVE-INTEGER" "ACL2"))
(defconst *b2-character-lists-atom-chars* (proof-sym "EXPLODE-ATOM" "ACL2"))
(defconst *b2-character-lists-pack-list* (proof-sym "PACK-LIST" "ACL2"))
(defconst *b2-character-lists-pack-tree* (proof-sym "PACK-TREE" "ACL2"))
(defconst *b2-character-lists-print-base* (proof-sym "PRINT-BASE-P" "ACL2"))
(defconst *b2-character-lists-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *b2-character-lists-append-type* (proof-sym "CHARACTER-LISTP-APPEND" "ACL2"))
(defconst *b2-character-lists-coerce* (proof-cl "COERCE"))
(defconst *b2-character-lists-ten* (proof-quote 10))
(defconst *b2-character-lists-ans* (proof-sym "ANS" "ACL2"))
(defconst *b2-character-lists-list* (proof-quote (proof-cl "LIST")))
(defconst *b2-character-lists-pack-theorems*
  (list (proof-sym "CHARACTER-LISTP-OF-PACK-LIST" "ACL2")
        (proof-sym "CHARACTER-LISTP-OF-PACK-TREE" "ACL2")))

(defun b2-character-lists-normalization-step (equation)
  (or equation '(:failure "failure" "")))

(defun b2-character-lists-proper-characters-empty
    (atom lib condition target)
  (proof-with-checked-results
   ((request (b2-tactics-tactics-implication lib condition target nil))
    (premise (cadddr (car request)))
    (nil-x (b2-tactics-tactics-from-impossible
            (cdr request) (proof-eq *library-x* *proof-false*) premise
            (list atom) (list condition) nil 1500 nil))
    (step (b2-tactics-tactics-solve
           (cdr request) target (list atom nil-x) (list target) nil 0 nil)))
   (b2-tactics-tactics-implication lib condition target (cons step (cdr request)))))

(defun b2-character-lists-proper-characters-advance-prove
    (premise lib condition target cons-step induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (b2-tactics-tactics-normalize
               lib condition (list cons-step) (list condition) nil 1500 nil))
      (opened (b2-character-lists-normalization-step opened))
      (rewritten (proof-proof-rewrite proof premise opened '(1)))
      (tidied (proof-proof-tidy proof rewritten))
      (parts (proof-proof-conjunct proof tidied))
      (smaller (proof-proof-modus-ponens proof induction (cadr parts)))
      (step (b2-tactics-tactics-solve
             lib target (list cons-step smaller) (list target) nil 0 nil)))
     (cons step lib))))

(defun b2-character-lists-proper-characters-advance
    (cons-step induction lib condition target)
  (proof-with-checked-results
   ((request (b2-tactics-tactics-implication lib condition target nil))
    (reply (b2-character-lists-proper-characters-advance-prove
            (cadddr (car request)) (cdr request) condition target cons-step induction)))
   (b2-tactics-tactics-implication lib condition target reply)))

(defun b2-character-lists-proper-characters-lemma (lib label name)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
      lib
    (let* ((condition (list *b2-character-lists-character-list* *library-x*))
           (target (list *b2-list-properties-true-list* *library-x*))
           (formula (list *library-implies* condition target)))
      (proof-with-checked-results
       ((advance-request (b2-tactics-tactics-on-list lib formula *library-x* nil nil nil))
        (advance (b2-character-lists-proper-characters-advance
                  (cadddr (car advance-request)) (nth 4 (car advance-request))
                  (cdr advance-request) condition target))
        (base-request (b2-tactics-tactics-on-list lib formula *library-x* nil advance nil))
        (base (b2-character-lists-proper-characters-empty
               (cadddr (car base-request)) (cdr base-request) condition target))
        (induction (b2-tactics-tactics-on-list lib formula *library-x* base advance nil))
        (added (b2-tactics-tactics-add-lemma (cdr induction) label (car induction) :none)))
       (cdr added)))))

(defun b2-character-lists-proper-characters (lib typed)
  (let ((label "CHARACTER-LIST-IS-PROPER")
        (name (proof-sym "B2-CHARACTER-LIST-IS-PROPER" "ACL2")))
    (proof-with-checked-results
     ((lib (b2-character-lists-proper-characters-lemma lib label name))
      (literal (proof-step-first typed))
      (value (proof-term-at literal 1))
      (step (b2-tactics-tactics-use-fact
             lib name (list *b2-list-properties-true-list* value)
             (list typed) nil nil 0 nil)))
     (cons step lib))))

(defun b2-character-lists-typed-cell (lib character-term typed-tail facts)
  (proof-with-checked-results
   ((tail-literal (proof-step-first typed-tail))
    (tail (proof-term-at tail-literal 1))
    (cell (list *proof-cons* character-term tail))
    (goal (list *b2-character-lists-character-list* cell))
    (head (b2-tactics-tactics-solve
           lib (list *b2-tactics-characterp* character-term) facts nil nil 0 nil)))
   (b2-tactics-tactics-solve lib goal (list head typed-tail) (list goal) nil 0 nil)))

(defun b2-character-lists-digit-type-leaf (value signed lib)
  (declare (ignore signed))
  (b2-tactics-tactics-solve lib (list *b2-tactics-characterp* value) nil nil nil 0 nil))

(defun b2-character-lists-digit-type-by-value (n lib value template signed)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-character-lists-digit-type-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
       ((branches (proof-list-of-length (cdr value) 3))
        (test (car branches))
        (yes (b2-character-lists-digit-type-by-value
              (1- n) lib (cadr branches) template (append signed (list (list test t)))))
        (no (b2-character-lists-digit-type-by-value
             (1- n) lib (caddr branches) template (append signed (list (list test nil))))))
       (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
       ((equality (proof-proof-beta proof value))
        (opened (proof-rewritten-term equality))
        (step (b2-character-lists-digit-type-by-value (1- n) lib opened template signed))
        (symmetric (proof-proof-symmetric proof equality)))
       (proof-proof-rewrite-result proof step symmetric template *proof-result*)))
     (t (proof-with-checked-results
         ((step (b2-character-lists-digit-type-leaf value signed lib))
          (literal (proof-step-first step))
          (target (proof-subst template (list (cons *proof-result* value)))))
         (if (equal literal target)
             step
           '(:failure "tactic-rejected" "")))))))

(defun b2-character-lists-digit-type-lemma (lib label name)
  (let ((proof (library-library-proof lib))
        (template (list *b2-tactics-characterp* *proof-result*)))
    (if (assoc-equal name (proof-proof-facts proof))
        lib
      (proof-with-checked-results
       ((equation (proof-proof-unfold proof (list *b2-character-lists-digit* *library-x*)))
        (value (caddr (proof-step-first equation)))
        (step (b2-character-lists-digit-type-by-value 1000000 lib value template nil))
        (symmetric (proof-proof-symmetric proof equation))
        (step (proof-proof-rewrite-result proof step symmetric template *proof-result*))
        (added (b2-tactics-tactics-add-lemma lib label step :none)))
       (cdr added)))))

(defun b2-character-lists-digit-type (lib digit)
  (let ((label "DIGIT-TO-CHAR-TYPE")
        (name (proof-sym "B2-DIGIT-TO-CHAR-TYPE" "ACL2")))
    (proof-with-checked-results
     ((lib (b2-character-lists-digit-type-lemma lib label name))
      (step (proof-proof-fact (library-library-proof lib) name
                              (list (list *library-x* digit)))))
     (cons step lib))))

(defun b2-character-lists-decimal-type-prove-stopped
    (empty facts lib typed call)
  (proof-with-checked-results
   ((equation (b2-tactics-tactics-normalize lib call facts (list call) nil 1500 nil))
    (equation (b2-character-lists-normalization-step equation))
    (emitted (if empty
                 (b2-tactics-tactics-solve
                  lib (list *b2-character-lists-character-list*
                            (caddr (proof-step-first equation)))
                  nil (list *b2-character-lists-character-list*) nil 0 nil)
               typed))
    (step (library-library-transport-argument lib emitted equation 1)))
   (cons step lib)))

(defun b2-character-lists-decimal-type-prove-reply (result typed call)
  (let ((request (car result)))
    (b2-character-lists-decimal-type-prove-stopped
     (cadddr request) (nth 4 request) (cdr result) typed call)))

(defun b2-character-lists-decimal-type-prove-choose (lib call typed equality evidence)
  (proof-with-checked-results
   ((result (b2-tactics-choose lib equality evidence nil)))
   (if (eq (caar result) :call)
       (proof-with-checked-results
        ((yes (b2-character-lists-decimal-type-prove-reply result typed call))
         (result (b2-tactics-choose lib equality evidence (list yes))))
        (if (eq (caar result) :call)
            (proof-with-checked-results
             ((no (b2-character-lists-decimal-type-prove-reply result typed call)))
             (b2-tactics-choose lib equality evidence (list yes no)))
          result))
     result)))

(defun b2-character-lists-decimal-type-prove
    (typed lib call test stop collected hypothesis shown)
  (proof-with-checked-results
   ((before (b2-character-lists-decimal-type-prove-choose
             lib call typed
             (proof-eq *b2-character-lists-ans* *proof-false*) (list stop)))
    (lib (cdr before))
    (character-term (proof-term-at collected 1))
    (digit (proof-term-at character-term 1))
    (digit-type (b2-character-lists-digit-type lib digit))
    (lib (cdr digit-type))
    (cell (b2-character-lists-typed-cell lib character-term typed (list (car digit-type))))
    (next (proof-proof-modus-ponens (library-library-proof lib) hypothesis cell))
    (after (library-library-transport-argument lib next shown 1))
    (step (proof-proof-cases (library-library-proof lib) test (car before) after)))
   (cons step lib)))

(defun b2-character-lists-decimal-type-lemma (lib label name)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
      lib
    (let* ((call (list *b2-character-lists-num-chars* *library-x*
                       *b2-character-lists-ten* *b2-character-lists-ans*))
           (condition (list *b2-character-lists-character-list* *b2-character-lists-ans*))
           (goal (list *b2-character-lists-character-list* call))
           (formula (list *library-implies* condition goal))
           (test (list *b2-quotients-zp* *library-x*))
           (measure (list *library-count* *library-x*))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
       ((stop (proof-proof-assume proof test t))
        (run (proof-proof-assume proof test nil))
        (base (b2-tactics-tactics-solve
               lib (list *b2-character-lists-print-base* *b2-character-lists-ten*)
               nil (list *b2-character-lists-print-base* *b2-character-lists-member*)
               nil 0 nil))
        (shown (b2-tactics-tactics-normalize lib call (list run base) (list call) nil 1500 nil))
        (shown (b2-character-lists-normalization-step shown))
        (shown-literal (proof-step-first shown))
        (value (proof-term-at shown-literal 2))
        (parts (proof-list-of-length value 4))
        (child (cadr parts))
        (collected (cadddr parts))
        (bindings (list (list *library-x* child) (list *b2-character-lists-ans* collected)))
        (decrease (list *proof-ordinal-less* (list *library-count* child) measure))
        (nonzero-base (b2-tactics-tactics-solve
                       lib (proof-neg (list *b2-quotients-zp* *b2-character-lists-ten*))
                       nil (list *b2-quotients-zp*) nil 0 nil))
        (large-base (b2-tactics-tactics-solve
                     lib (proof-neg (library-lt *b2-character-lists-ten* (proof-quote 2)))
                     nil nil nil 0 nil))
        (smaller (b2-quotients-ilog-decrease lib decrease (list run nonzero-base large-base)))
        (lib (cdr smaller))
        (hypothesis (b2-tactics-tactics-induction-hypothesis
                     lib formula measure bindings (car smaller)))
        (ordinal (library-library-builtin lib 1 *library-x*))
        (request (b2-tactics-tactics-implication lib condition goal nil))
        (reply (b2-character-lists-decimal-type-prove
                (cadddr (car request)) (cdr request) call test stop collected hypothesis shown))
        (case (b2-tactics-tactics-implication lib condition goal reply))
        (lib (cdr case))
        (induction (proof-proof-induct (library-library-proof lib)
                                       ordinal (car case) formula measure (list bindings)))
        (added (b2-tactics-tactics-add-lemma lib label induction :none)))
       (cdr added)))))

(defun b2-character-lists-decimal-type (lib number accumulator)
  (let ((label "DECIMAL-CHARACTERS")
        (name (proof-sym "B2-DECIMAL-CHARACTERS" "ACL2"))
        (goal (list *b2-character-lists-character-list*
                    (list *b2-character-lists-num-chars* number
                          *b2-character-lists-ten* accumulator))))
    (proof-with-checked-results
     ((lib (b2-character-lists-decimal-type-lemma lib label name))
      (empty (b2-tactics-tactics-solve
              lib (list *b2-character-lists-character-list* accumulator)
              nil (list *b2-character-lists-character-list*) nil 0 nil))
      (step (b2-tactics-tactics-use-fact lib name goal (list empty) nil nil 0 nil)))
     (cons step lib))))

(defun b2-character-lists-signed-assumptions (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
     ((assumption (proof-proof-assume proof (caar signed) (cadar signed)))
      (rest (b2-character-lists-signed-assumptions proof (cdr signed))))
     (cons assumption rest))))

(mutual-recursion
 (defun b2-character-lists-character-result-visit (n lib value evidence other)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-character-result-visit")
     (let ((goal (list *b2-character-lists-character-list* value)))
       (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib evidence)))
        (cond
         ((assoc-equal goal known)
          (cons (cdr (assoc-equal goal known)) lib))
         ((proof-is-call value *proof-cons*)
          (proof-with-checked-results
           ((tail (proof-term-at value 2))
            (typed-tail (b2-character-lists-character-result-visit
                         (1- n) lib tail evidence other))
            (lib (cdr typed-tail))
            (character-term (proof-term-at value 1))
            (step (b2-character-lists-typed-cell lib character-term (car typed-tail) evidence)))
           (cons step lib)))
         ((proof-is-call value *b2-character-lists-append*)
          (proof-with-checked-results
           ((args (proof-list-of-length (cdr value) 2))
            (left (b2-character-lists-character-result-visit
                   (1- n) lib (car args) evidence other))
            (right (b2-character-lists-character-result-visit
                    (1- n) (cdr left) (cadr args) evidence other))
            (lib (cdr right))
            (left-step (car left))
            (right-step (car right))
            (left-literal (proof-step-first left-step))
            (right-literal (proof-step-first right-step))
            (conjunction (proof-ite left-literal right-literal *proof-false*))
            (target (proof-eq goal conjunction))
            (proper (b2-character-lists-proper-characters lib left-step))
            (lib (cdr proper))
            (opened (b2-tactics-tactics-use-fact
                     lib *b2-character-lists-append-type* target
                     (list (car proper)) nil nil 0 nil))
            (derived (b2-tactics-tactics-solve lib conjunction
                                              (list left-step right-step) nil nil 0 nil))
            (step (proof-proof-transport (library-library-proof lib) derived opened)))
           (cons step lib)))
         ((proof-is-call value *proof-quote*)
          (proof-with-checked-results
           ((step (b2-tactics-tactics-solve
                   lib goal nil (list *b2-character-lists-character-list*) nil 0 nil)))
           (cons step lib)))
         ((proof-is-call value *b2-character-lists-coerce*)
          (proof-with-checked-results
           ((coerce-type (proof-term-at value 2)))
           (if (equal coerce-type *b2-character-lists-list*)
               (proof-with-checked-results
                ((step (b2-tactics-tactics-use-fact
                        lib (proof-sym "CHARACTER-LISTP-COERCE" "ACL2") goal nil nil nil 0 nil)))
                (cons step lib))
             (b2-character-lists-character-result-other (1- n) value evidence lib other))))
         (t (b2-character-lists-character-result-other (1- n) value evidence lib other)))))))

 (defun b2-character-lists-character-result-other (n value evidence lib other)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-character-result-other")
     (case (car other)
       (:atom (b2-character-lists-atom-type-complete-read (1- n) value evidence lib (cadr other)))
       (:pack (proof-with-checked-results
               ((subject (proof-term-at value 1)))
               (b2-character-lists-atom-type-visit (1- n) lib subject nil)))
       (:replies (let ((found (assoc-equal (list value evidence) (cdr other))))
                   (if found
                       (cdr found)
                     '(:failure "inapplicable" ""))))
       (otherwise '(:failure "tactic-rejected" "")))))

 (defun b2-character-lists-analyze-result-leaf (n value signed lib evidence other)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-analyze-result-leaf")
     (proof-with-checked-results
      ((tests (b2-character-lists-signed-assumptions (library-library-proof lib) signed)))
      (b2-character-lists-character-result-visit (1- n) lib value
                                                  (append evidence tests) other))))

 (defun b2-character-lists-analyze-result-by-value
     (n lib value template signed evidence other)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-character-lists-analyze-result-by-value"))
    ((proof-is-call value *proof-if*)
     (proof-with-checked-results
      ((branches (proof-list-of-length (cdr value) 3))
       (test (car branches))
       (yes (b2-character-lists-analyze-result-by-value
             (1- n) lib (cadr branches) template
             (append signed (list (list test t))) evidence other))
       (no (b2-character-lists-analyze-result-by-value
            (1- n) (cdr yes) (caddr branches) template
            (append signed (list (list test nil))) evidence other))
       (lib (cdr no))
       (step (proof-by-value-join (library-library-proof lib) value template (car yes) (car no))))
      (cons step lib)))
    ((and (proof-compound value) (endp value))
     '(:failure "tactic-rejected" ""))
    ((and (proof-compound value) (proof-compound (car value)))
     (proof-with-checked-results
      ((equality (proof-proof-beta (library-library-proof lib) value))
       (opened (proof-rewritten-term equality))
       (inner (b2-character-lists-analyze-result-by-value
               (1- n) lib opened template signed evidence other))
       (lib (cdr inner))
       (proof (library-library-proof lib))
       (symmetric (proof-proof-symmetric proof equality))
       (step (proof-proof-rewrite-result proof (car inner) symmetric template *proof-result*)))
      (cons step lib)))
    (t (proof-with-checked-results
        ((result (b2-character-lists-analyze-result-leaf
                  (1- n) value signed lib evidence other))
         (literal (proof-step-first (car result)))
         (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target)
            result
          '(:failure "tactic-rejected" ""))))))

 (defun b2-character-lists-analyze-result-visit (n lib call evidence other)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-analyze-result-visit")
     (let ((template (list *b2-character-lists-character-list* *proof-result*)))
       (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize lib call evidence (list call) nil 1500 nil))
         (equation (b2-character-lists-normalization-step equation))
         (literal (proof-step-first equation))
         (value (proof-term-at literal 2))
         (cases (b2-character-lists-analyze-result-by-value
                 (1- n) lib value template nil evidence other))
         (lib (cdr cases))
         (proof (library-library-proof lib))
         (symmetric (proof-proof-symmetric proof equation))
         (step (proof-proof-rewrite-result proof (car cases) symmetric template *proof-result*)))
        (cons step lib)))))

 (defun b2-character-lists-atom-type-complete-read (n term evidence lib kind)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-atom-type-complete-read")
     (cond
      ((proof-is-call term *b2-character-lists-num-chars*)
       (proof-with-checked-results
        ((number (proof-term-at term 1))
         (accumulator (proof-term-at term 3)))
        (b2-character-lists-decimal-type lib number accumulator)))
      (t
       (proof-with-checked-results
        ((subkind (if kind *proof-integerp* *library-rationalp*))
         (value (proof-term-at term 1))
         (theorem (b2-character-lists-atom-type-visit (1- n) lib value subkind))
         (lib (cdr theorem))
         (literal (proof-step-first (car theorem)))
         (requirement (proof-term-at literal 1))
         (premise (b2-tactics-tactics-solve lib requirement evidence nil nil 0 nil))
         (step (proof-proof-modus-ponens (library-library-proof lib) (car theorem) premise)))
        (cons step lib))))))

 (defun b2-character-lists-atom-type-complete (n typed-atom lib kind call)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-atom-type-complete")
     (let ((facts (if typed-atom (list typed-atom) nil)))
       (proof-with-checked-results
        ((types (cond
                 ((equal kind *proof-integerp*)
                  (proof-with-checked-results
                   ((rational (library-library-rational lib *library-x* facts)))
                   (list rational)))
                 ((equal kind *library-rationalp*)
                  (proof-with-checked-results
                   ((factors (b2-products-rational-factors lib *library-x* typed-atom)))
                   (list (car factors) (cadr factors))))
                 (t (proof-with-checked-results
                     ((complex (library-library-axiom lib "COMPLEX-IMPLIES1" (list *library-x*))))
                     (proof-proof-conjunct (library-library-proof lib) complex))))))
        (b2-character-lists-analyze-result-visit (1- n) lib call (append facts types)
                                                (list :atom kind))))))

 (defun b2-character-lists-atom-type-lemma (n lib kind label name)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-character-lists-atom-type-lemma"))
    ((assoc-equal name (proof-proof-facts (library-library-proof lib))) lib)
    (t
     (let* ((call (list *b2-character-lists-atom-chars* *library-x* *b2-character-lists-ten*))
            (target (list *b2-character-lists-character-list* call))
            (rational (list *library-rationalp* *library-x*)))
       (proof-with-checked-results
        ((result
          (if kind
              (let ((condition (list kind *library-x*)))
                (proof-with-checked-results
                 ((request (b2-tactics-tactics-implication lib condition target nil))
                  (reply (b2-character-lists-atom-type-complete
                          (1- n) (cadddr (car request)) (cdr request) kind call)))
                 (b2-tactics-tactics-implication lib condition target reply)))
            (proof-with-checked-results
             ((theorem (b2-character-lists-atom-type-visit (1- n) lib *library-x* *library-rationalp*))
              (lib (cdr theorem))
              (proof (library-library-proof lib))
              (typed (proof-proof-assume proof rational t))
              (yes (proof-proof-modus-ponens proof (car theorem) typed))
              (not-typed (proof-proof-assume proof rational nil))
              (no (b2-character-lists-atom-type-complete (1- n) not-typed lib kind call))
              (lib (cdr no))
              (step (proof-proof-cases (library-library-proof lib) rational yes (car no))))
             (cons step lib))))
         (added (b2-tactics-tactics-add-lemma (cdr result) label (car result) :none)))
        (cdr added))))))

 (defun b2-character-lists-atom-type-visit (n lib value kind)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-character-lists-atom-type-visit")
     (proof-with-checked-results
      ((label (if kind
                  (proof-with-checked-results
                   ((kind-name (proof-term-at kind 2)))
                   (if (stringp kind-name)
                       (concatenate 'string kind-name "-ATOM-CHARACTERS")
                     '(:failure "failure" "")))
                "ATOM-CHARACTERS"))
       (name (proof-sym (concatenate 'string "B2-" label) "ACL2"))
       (lib (b2-character-lists-atom-type-lemma (1- n) lib kind label name))
       (step (proof-proof-fact (library-library-proof lib) name
                               (list (list *library-x* value)))))
      (cons step lib)))))

(defun b2-character-lists-character-result (lib value evidence other)
  (b2-character-lists-character-result-visit 1000000 lib value evidence other))

(defun b2-character-lists-analyze-result (lib call evidence other)
  (b2-character-lists-analyze-result-visit 1000000 lib call evidence other))

(defun b2-character-lists-atom-type (lib value kind)
  (b2-character-lists-atom-type-visit 1000000 lib value kind))

(defun b2-character-lists-pack-characters-prove (evidence lib packed goal)
  (proof-with-checked-results
   ((list-proof (b2-character-lists-analyze-result lib (car packed) evidence '(:pack)))
    (tree-proof (b2-character-lists-analyze-result
                 (cdr list-proof) (cadr packed) evidence '(:pack)))
    (lib (cdr tree-proof))
    (step (b2-tactics-tactics-solve
           lib goal (list (car list-proof) (car tree-proof)) nil nil 0 nil)))
   (cons step lib)))

(defun b2-character-lists-pack-hypothesis (lib goal measure binding builtin cons-step)
  (proof-with-checked-results
   ((size (library-library-builtin lib builtin *library-x*))
    (decrease (proof-proof-discharge (library-library-proof lib) size cons-step)))
   (b2-tactics-tactics-induction-hypothesis lib goal measure binding decrease)))

(defun b2-character-lists-pack-characters-lemma (lib label helper)
  (if (assoc-equal helper (proof-proof-facts (library-library-proof lib)))
      lib
    (let* ((packed (list (list *b2-character-lists-pack-list* *library-x*)
                         (list *b2-character-lists-pack-tree* *library-x*)))
           (goal (proof-ite (list *b2-character-lists-character-list* (car packed))
                            (list *b2-character-lists-character-list* (cadr packed))
                            *proof-false*))
           (measure (list *library-count* *library-x*))
           (test (list *proof-consp* *library-x*))
           (proof (library-library-proof lib))
           (car-binding (list (list *library-x* (list *library-car* *library-x*))))
           (cdr-binding (list (list *library-x* (list *library-cdr* *library-x*)))))
      (proof-with-checked-results
       ((cons-step (proof-proof-assume proof test t))
        (atom (proof-proof-assume proof test nil))
        (car-hypothesis (b2-character-lists-pack-hypothesis lib goal measure car-binding 2 cons-step))
        (cdr-hypothesis (b2-character-lists-pack-hypothesis lib goal measure cdr-binding 3 cons-step))
        (yes (b2-character-lists-pack-characters-prove
              (list cons-step car-hypothesis cdr-hypothesis) lib packed goal))
        (no (b2-character-lists-pack-characters-prove (list atom) (cdr yes) packed goal))
        (lib (cdr no))
        (proof (library-library-proof lib))
        (joint (proof-proof-cases proof test (car yes) (car no)))
        (ordinal (library-library-builtin lib 1 *library-x*))
        (step (proof-proof-induct proof ordinal joint goal measure (list car-binding cdr-binding)))
        (added (b2-tactics-tactics-add-lemma lib label step :none)))
       (cdr added)))))

(defun b2-character-lists-pack-characters (lib name formula)
  (declare (ignore name))
  (let ((label "PACK-CHARACTERS")
        (helper (proof-sym "B2-PACK-CHARACTERS" "ACL2")))
    (proof-with-checked-results
     ((lib (b2-character-lists-pack-characters-lemma lib label helper))
      (proof (library-library-proof lib))
      (packed (proof-term-at formula 1))
      (value (proof-term-at packed 1))
      (fact (proof-proof-fact proof helper (list (list *library-x* value))))
      (types (proof-proof-conjunct proof fact))
      (head (proof-term-at packed 0)))
     (cons (if (equal head *b2-character-lists-pack-tree*) (cadr types) (car types)) lib))))
