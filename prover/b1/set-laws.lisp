(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-set-laws-subset* (proof-sym "SUBSETP-EQUAL" "ACL2"))
(defconst *b1-set-laws-set-equal* (proof-sym "SET-EQUAL" "ACL2"))
(defconst *b1-set-laws-memberp* (proof-sym "MEMBERP-EQUAL" "ACL2"))
(defconst *b1-set-laws-adjoin* (proof-sym "ADJOIN-EQUAL" "ACL2"))
(defconst *b1-set-laws-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *b1-set-laws-union* (proof-sym "UNION-EQUAL" "ACL2"))
(defconst *b1-set-laws-difference* (proof-sym "SET-DIFFERENCE-EQUAL" "ACL2"))
(defconst *b1-set-laws-setp* (proof-sym "SETP-EQUAL" "ACL2"))
(defconst *b1-set-laws-no-duplicates* (proof-sym "NO-DUPLICATESP-EQUAL" "ACL2"))

(defun b1-set-laws-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-set-laws-fact-present-p (lib name)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
      t
    nil))

(defun b1-set-laws-list-induction-atom (lib preparation)
  (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))

(defun b1-set-laws-nonempty-value (lib pair)
  (proof-with-checked-results ((cell (b1-revappend-cons-value lib pair)))
    (b1-revappend-cons-is-nonempty lib cell)))

(defun b1-set-laws-subset-fields (lib assertion cell)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first assertion))
         (view (b1-revappend-open-list lib literal (list cell)))
         (opened (proof-proof-rewrite proof assertion view '(1))))
      (proof-proof-conjunct proof opened))))

(defun b1-set-laws-subset-from-fields (lib claim cell head tail)
  (proof-with-checked-results
      ((opened (b1-revappend-open-list lib claim (list cell head))))
    (proof-proof-transport (library-library-proof lib) tail opened)))

(defun b1-set-laws-subset-base (lib claim evidence)
  (proof-with-checked-results
      ((opened (b1-revappend-open-list lib claim evidence)))
    (proof-proof-true-from-eq (library-library-proof lib) opened)))

(defun b1-set-laws-member-into-cons (lib known new-head)
  (proof-with-checked-results
      ((literal (proof-step-first known))
       (parts (proof-list-of-length literal 3)))
    (let* ((proof (library-library-proof lib))
           (item (cadr parts))
           (pair (list *proof-cons* new-head (caddr parts)))
           (goal (list *b1-revappend-member* item pair))
           (hit (proof-eq item new-head)))
      (proof-with-checked-results
          ((nonempty (b1-set-laws-nonempty-value lib pair))
           (same (proof-proof-assume proof hit t))
           (open-yes (b1-revappend-open-list lib goal (list same)))
           (yes (proof-proof-transport proof nonempty open-yes))
           (different (proof-proof-assume proof hit nil))
           (open-no (b1-revappend-open-list lib goal (list different)))
           (no (proof-proof-transport proof known open-no)))
        (proof-proof-cases proof hit yes no)))))

(defun b1-set-laws-memberp-as-boolean-base (atom lib claim witness predicate-view)
  (proof-with-checked-results
      ((reduction (b1-revappend-open-list lib witness (list atom))))
    (b1-membership-membership-case lib claim (list predicate-view reduction)
                                   (list atom) nil)))

(defun b1-set-laws-memberp-as-boolean-step
    (cell induction lib claim witness hit predicate-view)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((same (proof-proof-assume proof hit t))
         (head (b1-revappend-open-list lib witness (list cell same)))
         (consp-value (b1-revappend-consp-value lib cell))
         (yes (b1-membership-membership-case
               lib claim (list predicate-view head consp-value) (list cell) nil))
         (different (proof-proof-assume proof hit nil))
         (tail (b1-revappend-open-list lib witness (list cell different)))
         (child-predicate (b1-set-laws-first-at induction 1))
         (child-view (proof-proof-unfold proof child-predicate))
         (child-claim (proof-proof-rewrite-first proof induction child-view))
         (identity (proof-proof-reflexive proof claim))
         (shape (proof-proof-rewrite proof identity predicate-view '(1 2 1)))
         (shape (proof-proof-rewrite proof shape tail '(1 2 1 1)))
         (shape (proof-proof-rewrite proof shape tail '(1 2 2 1)))
         (no (proof-proof-transport proof child-claim shape)))
      (proof-proof-cases proof hit yes no))))

(defun b1-set-laws-memberp-as-boolean-lemma (lib)
  (let* ((predicate (list *b1-set-laws-memberp* *library-z* *library-x*))
         (witness (list *b1-revappend-member* *library-z* *library-x*))
         (claim (proof-eq predicate (proof-ite witness *proof-true* *proof-false*)))
         (hit (proof-eq *library-z* (list *library-car* *library-x*))))
    (proof-with-checked-results
        ((predicate-view (proof-proof-unfold (library-library-proof lib) predicate))
         (preparation (b1-revappend-list-induction-prepare lib claim *library-x* nil))
         (step (b1-set-laws-memberp-as-boolean-step
                (caddr preparation) (cadddr preparation) lib claim witness hit
                predicate-view))
         (atom-proof (b1-set-laws-list-induction-atom lib preparation))
         (base (b1-set-laws-memberp-as-boolean-base
                atom-proof lib claim witness predicate-view))
         (inducted (b1-revappend-list-induction lib preparation base step)))
      (library-library-lemma lib "MEMBERP-BOOLEAN" claim inducted nil))))

(defun b1-set-laws-memberp-as-boolean (lib)
  (let ((name (proof-sym "SELF-MEMBERP-BOOLEAN" "ACL2")))
    (proof-with-checked-results
        ((lib (if (b1-set-laws-fact-present-p lib name)
                  lib
                (b1-set-laws-memberp-as-boolean-lemma lib)))
         (rule (b1-logic-bookproof-rewrite-rule lib name)))
      (cons rule lib))))

(defun b1-set-laws-append-membership-reduce (cell evidence lib combined first)
  (proof-with-checked-results
      ((view (b1-revappend-open-list lib (caddr combined) (list cell)))
       (appended (b1-revappend-lift-argument lib combined view 2))
       (original (b1-revappend-open-list lib first (cons cell evidence)))
       (literal (proof-step-first cell)))
    (if (equal literal (proof-neg (list *proof-consp* *library-x*)))
        (list appended original)
      (proof-with-checked-results
          ((value (b1-set-laws-first-at appended 2))
           (opened (b1-revappend-open-list lib value evidence))
           (chained (proof-proof-chain (library-library-proof lib)
                                       appended (list opened))))
        (list chained original)))))

(defun b1-set-laws-append-membership-base (atom-proof lib claim combined first)
  (proof-with-checked-results
      ((equations (b1-set-laws-append-membership-reduce
                   atom-proof nil lib combined first)))
    (b1-membership-membership-case lib claim equations (list atom-proof) nil)))

(defun b1-set-laws-append-membership-step
    (cell induction lib claim combined first test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((have (proof-proof-assume proof test t))
         (miss (proof-proof-assume proof test nil))
         (yes-equations (b1-set-laws-append-membership-reduce
                         cell (list have) lib combined first))
         (yes (b1-membership-membership-case lib claim yes-equations
                                            (list cell have) nil))
         (no-equations (b1-set-laws-append-membership-reduce
                        cell (list miss) lib combined first))
         (no (b1-membership-membership-case lib claim no-equations
                                           (list cell miss) induction)))
      (proof-proof-cases proof test yes no))))

(defun b1-set-laws-append-membership-lemma (lib)
  (let* ((first (list *b1-revappend-member* *library-z* *library-x*))
         (second (list *b1-revappend-member* *library-z* *library-y*))
         (combined (list *b1-revappend-member* *library-z*
                         (list *b1-revappend-append* *library-x* *library-y*)))
         (claim (list *b1-revappend-iff* combined (proof-ite first first second)))
         (test (proof-eq *library-z* (list *library-car* *library-x*))))
    (proof-with-checked-results
        ((preparation (b1-revappend-list-induction-prepare lib claim *library-x* nil))
         (step (b1-set-laws-append-membership-step
                (caddr preparation) (cadddr preparation) lib claim combined first test))
         (atom-proof (b1-set-laws-list-induction-atom lib preparation))
         (base (b1-set-laws-append-membership-base atom-proof lib claim combined first))
         (inducted (b1-revappend-list-induction lib preparation base step)))
      (library-library-lemma lib "MEMBER-APPENDED" claim inducted nil))))

(defun b1-set-laws-append-membership (lib item left right)
  (let ((name (proof-sym "SELF-MEMBER-APPENDED" "ACL2")))
    (proof-with-checked-results
        ((lib (if (b1-set-laws-fact-present-p lib name)
                  lib
                (b1-set-laws-append-membership-lemma lib)))
         (fact (proof-proof-fact (library-library-proof lib) name
                                 (list (list *library-z* item)
                                       (list *library-x* left)
                                       (list *library-y* right)))))
      (cons fact lib))))

(defun b1-set-laws-member-into-append (lib known other)
  (proof-with-checked-results
      ((literal (proof-step-first known))
       (parts (proof-list-of-length literal 3))
       (result (b1-set-laws-append-membership lib (cadr parts) (caddr parts) other))
       (goal (b1-set-laws-first-at (car result) 1))
       (step (b1-logic-bookproof-forces (cdr result) goal (car result)
                                       (list known) (list *b1-revappend-iff*) nil)))
    (cons step (cdr result))))

(defun b1-set-laws-member-from-subset-base-consequence (premise lib empty right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (proof-proof-conjunct proof premise))
         (impossible (proof-proof-rewrite proof (car fields) empty '(1)))
         (not-nil (b1-logic-proof-not-nil proof)))
      (b1-logic-bookproof-contradiction lib impossible not-nil right))))

(defun b1-set-laws-member-from-subset-base (atom-proof lib claim left right)
  (proof-with-checked-results
      ((empty (b1-revappend-open-list lib left (list atom-proof)))
       (premise (b1-logic-bookproof-prove-implication-premise lib claim))
       (consequence (b1-set-laws-member-from-subset-base-consequence
                     premise lib empty right)))
    (b1-logic-bookproof-prove-implication-with-premise lib claim premise consequence)))

(defun b1-set-laws-member-from-subset-step-consequence
    (premise lib cell induction left hit)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premises (proof-proof-conjunct proof premise))
         (fields (b1-set-laws-subset-fields lib (cadr premises) cell))
         (same (proof-proof-assume proof hit t))
         (reversed (proof-proof-symmetric proof same))
         (yes (proof-proof-rewrite proof (car fields) reversed '(1 1)))
         (different (proof-proof-assume proof hit nil))
         (opened (b1-revappend-open-list lib left (list cell different)))
         (suffix (proof-proof-rewrite proof (car premises) opened '(1)))
         (guard (b1-set-laws-first-at induction 1))
         (transfer (b1-logic-bookproof-normalize-proof
                    lib guard (list suffix (cadr fields)) nil nil nil))
         (no (proof-proof-modus-ponens proof induction transfer)))
      (proof-proof-cases proof hit yes no))))

(defun b1-set-laws-member-from-subset-step (cell induction lib claim left hit)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib claim))
       (consequence (b1-set-laws-member-from-subset-step-consequence
                     premise lib cell induction left hit)))
    (b1-logic-bookproof-prove-implication-with-premise lib claim premise consequence)))

(defun b1-set-laws-member-from-subset-lemma (lib)
  (let* ((left (list *b1-revappend-member* *library-z* *library-x*))
         (right (list *b1-revappend-member* *library-z* *library-y*))
         (relation (list *b1-set-laws-subset* *library-x* *library-y*))
         (claim (list *library-implies* (proof-ite left relation *proof-false*) right))
         (hit (proof-eq *library-z* (list *library-car* *library-x*))))
    (proof-with-checked-results
        ((preparation (b1-revappend-list-induction-prepare lib claim *library-x* nil))
         (step (b1-set-laws-member-from-subset-step
                (caddr preparation) (cadddr preparation) lib claim left hit))
         (atom-proof (b1-set-laws-list-induction-atom lib preparation))
         (base (b1-set-laws-member-from-subset-base atom-proof lib claim left right))
         (inducted (b1-revappend-list-induction lib preparation base step)))
      (library-library-lemma lib "MEMBER-FROM-SUBSET" claim inducted nil))))

(defun b1-set-laws-member-from-subset (lib subset member)
  (let ((name (proof-sym "SELF-MEMBER-FROM-SUBSET" "ACL2")))
    (proof-with-checked-results
        ((lib (if (b1-set-laws-fact-present-p lib name)
                  lib
                (b1-set-laws-member-from-subset-lemma lib)))
         (inclusion (proof-step-first subset))
         (parts (proof-list-of-length inclusion 3))
         (item (b1-set-laws-first-at member 1)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((rule (proof-proof-fact proof name (list (list *library-x* (cadr parts))
                                                     (list *library-y* (caddr parts))
                                                     (list *library-z* item))))
             (guard (b1-set-laws-first-at rule 1))
             (antecedent (b1-logic-bookproof-normalize-proof
                          lib guard (list subset member) nil nil nil))
             (step (proof-proof-modus-ponens proof rule antecedent)))
          (cons step lib))))))

(defun b1-set-laws-operation-tag (operation)
  (proof-with-checked-results ((name (proof-term-at operation 2)))
    (if (stringp name)
        (concatenate 'string "MEMBER-OF-" name)
      '(:failure "failure" ""))))

(defun b1-set-laws-operation-membership-lemma (lib operation tag)
  (let* ((left (list *b1-revappend-member* *library-z* *library-x*))
         (right (list *b1-revappend-member* *library-z* *library-y*))
         (body (cond ((equal operation *b1-revappend-intersection*)
                      (proof-ite left right *proof-false*))
                     ((equal operation *b1-set-laws-difference*)
                      (proof-ite left (proof-neg right) *proof-false*))
                     (t (proof-ite left left right))))
         (claim (list *b1-revappend-iff*
                      (list *b1-revappend-member* *library-z*
                            (list operation *library-x* *library-y*))
                      body)))
    (proof-with-checked-results
        ((proof (b1-membership-member-of-set-operation lib claim)))
      (library-library-lemma lib tag claim proof nil))))

(defun b1-set-laws-operation-membership (lib operation item left right)
  (proof-with-checked-results ((tag (b1-set-laws-operation-tag operation)))
    (let ((name (proof-sym (concatenate 'string "SELF-" tag) "ACL2")))
      (proof-with-checked-results
          ((lib (if (b1-set-laws-fact-present-p lib name)
                    lib
                  (b1-set-laws-operation-membership-lemma lib operation tag)))
           (step (proof-proof-fact (library-library-proof lib) name
                                   (list (list *library-x* left)
                                         (list *library-y* right)
                                         (list *library-z* item)))))
        (cons step lib)))))

(defun b1-set-laws-disjoint-head-and-tail (lib empty cell)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((overlap (b1-set-laws-first-at empty 1))
         (left (proof-term-at overlap 1))
         (right (proof-term-at overlap 2)))
      (let ((overlaps (list *b1-revappend-member* (list *library-car* left) right)))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof overlaps t))
             (expanded (b1-revappend-open-list lib overlap (list cell assumed)))
             (value (b1-set-laws-first-at expanded 2))
             (pair-cell (b1-revappend-cons-value lib value))
             (pair (library-library-transport-argument lib pair-cell expanded 1))
             (impossible (proof-proof-rewrite proof pair empty '(1 1)))
             (literal (proof-step-first impossible))
             (constant (b1-logic-bookproof-constant lib literal))
             (rewritten (if constant
                            (proof-proof-rewrite proof impossible constant '(1))
                          '(:failure "failure" "")))
             (impossible (proof-proof-tidy proof rewritten))
             (disjoint (proof-proof-front proof impossible (proof-neg overlaps)))
             (opened (b1-revappend-open-list lib overlap (list cell disjoint)))
             (tail (proof-proof-rewrite proof empty opened '(1 1))))
          (list disjoint tail))))))

(defun b1-set-laws-subset-of-extension-transform (premise cell lib other)
  (proof-with-checked-results
      ((fields (b1-set-laws-subset-fields lib premise cell))
       (op (proof-term-at other 0)))
    (if (equal op *proof-cons*)
        (proof-with-checked-results
            ((new (proof-term-at other 1))
             (head (b1-set-laws-member-into-cons lib (car fields) new)))
          (cons (list head (cadr fields)) lib))
      (proof-with-checked-results
          ((new (proof-term-at other 2))
           (result (b1-set-laws-member-into-append lib (car fields) new)))
        (cons (list (car result) (cadr fields)) (cdr result))))))

(defun b1-set-laws-subset-transitive-transform (premise cell lib)
  (proof-with-checked-results
      ((premises (proof-proof-conjunct (library-library-proof lib) premise))
       (fields (b1-set-laws-subset-fields lib (car premises) cell))
       (present (b1-set-laws-member-from-subset lib (cadr premises) (car fields)))
       (tail (proof-step-first (cadr fields)))
       (second (proof-step-first (cadr premises)))
       (guard (b1-logic-bookproof-normalize-proof
               (cdr present) (proof-ite tail second *proof-false*)
               (list (cadr fields) (cadr premises)) nil nil nil)))
    (cons (list (car present) guard) (cdr present))))

(defun b1-set-laws-subset-of-set-operation-preserved (evidence lib witness)
  (proof-with-checked-results ((goal (b1-set-laws-first-at witness 1)))
    (b1-logic-bookproof-forces lib goal witness evidence
                               (list *b1-revappend-iff* *proof-not*) nil)))

(defun b1-set-laws-subset-of-set-operation-union (premise cell lib guard witness)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-term-at guard 1))
         (first (proof-proof-assume proof test t))
         (different (proof-proof-assume proof test nil))
         (second (proof-proof-prove-if proof premise different))
         (a (b1-set-laws-subset-fields lib first cell))
         (b (b1-set-laws-subset-fields lib second cell))
         (choice (b1-set-laws-first-at witness 2))
         (in-either (b1-revappend-right-disjunct lib choice (car b)))
         (member-a (b1-set-laws-subset-of-set-operation-preserved (list (car a))
                                                                  lib witness))
         (member-b (b1-set-laws-subset-of-set-operation-preserved (list in-either)
                                                                  lib witness))
         (members (proof-proof-cases proof test member-a member-b))
         (tail-a (proof-step-first (cadr a)))
         (tail-b (proof-step-first (cadr b))))
      (let ((child (proof-ite tail-a tail-a tail-b)))
        (proof-with-checked-results
            ((in-a (b1-logic-bookproof-normalize-proof lib child (list (cadr a))
                                                       nil nil nil))
             (in-b (b1-revappend-right-disjunct lib child (cadr b)))
             (next-guard (proof-proof-cases proof test in-a in-b)))
          (list members next-guard))))))

(defun b1-set-laws-subset-of-set-operation-transform
    (premise cell lib op guard witness)
  (if (equal op *b1-set-laws-union*)
      (b1-set-laws-subset-of-set-operation-union premise cell lib guard witness)
    (proof-with-checked-results
        ((premises (proof-proof-conjunct (library-library-proof lib) premise))
         (a (b1-set-laws-subset-fields lib (car premises) cell))
         (b (if (equal op *b1-revappend-intersection*)
                (b1-set-laws-subset-fields lib (cadr premises) cell)
              (b1-set-laws-disjoint-head-and-tail lib (cadr premises) cell)))
         (tail-a (proof-step-first (cadr a)))
         (tail-b (proof-step-first (cadr b)))
         (head (b1-set-laws-subset-of-set-operation-preserved
                (list (car a) (car b)) lib witness))
         (next-guard (b1-logic-bookproof-normalize-proof
                      lib (proof-ite tail-a tail-b *proof-false*)
                      (list (cadr a) (cadr b)) nil nil nil)))
      (list head next-guard))))

(defun b1-set-laws-subset-map-transform (lib transform premise cell)
  (case (car transform)
    (:extension (b1-set-laws-subset-of-extension-transform premise cell lib
                                                           (cadr transform)))
    (:transitive (b1-set-laws-subset-transitive-transform premise cell lib))
    (otherwise
     (proof-with-checked-results
         ((fields (b1-set-laws-subset-of-set-operation-transform
                   premise cell lib (cadr transform) (caddr transform) (cadddr transform))))
       (cons fields lib)))))

(defun b1-set-laws-subset-map-base (atom-proof lib formula claim)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (base (b1-set-laws-subset-base lib claim (list atom-proof))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise base)))

(defun b1-set-laws-subset-map-step-consequence
    (premise lib claim cell induction transform)
  (proof-with-checked-results
      ((result (b1-set-laws-subset-map-transform lib transform premise cell))
       (lib (cdr result))
       (tail (proof-proof-modus-ponens (library-library-proof lib)
                                       induction (cadar result)))
       (step (b1-set-laws-subset-from-fields lib claim cell (caar result) tail)))
    (cons step lib)))

(defun b1-set-laws-subset-map-step (cell induction lib formula claim transform)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (result (b1-set-laws-subset-map-step-consequence
                premise lib claim cell induction transform))
       (lib (cdr result))
       (step (b1-logic-bookproof-prove-implication-with-premise
               lib formula premise (car result))))
    (cons step lib)))

(defun b1-set-laws-subset-map (lib formula transform)
  (proof-with-checked-results
      ((formula-parts (proof-list-of-length formula 3))
       (claim (caddr formula-parts))
       (claim-parts (proof-list-of-length claim 3))
       (preparation (b1-revappend-list-induction-prepare lib formula
                                                       (cadr claim-parts) nil))
       (result (b1-set-laws-subset-map-step (caddr preparation) (cadddr preparation)
                                           lib formula claim transform))
       (lib (cdr result))
       (atom-proof (b1-set-laws-list-induction-atom lib preparation))
       (base (b1-set-laws-subset-map-base atom-proof lib formula claim))
       (step (b1-revappend-list-induction lib preparation base (car result))))
    (cons step lib)))

(defun b1-set-laws-subset-of-extension (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (other (proof-term-at claim 2)))
    (b1-set-laws-subset-map lib formula (list :extension other))))

(defun b1-set-laws-subset-transitive (lib formula)
  (b1-set-laws-subset-map lib formula '(:transitive)))

(defun b1-set-laws-subset-of-set-operation (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3))
       (call (proof-list-of-length (caddr claim) 3))
       (witness (b1-set-laws-operation-membership lib (car call)
                                                  (list *library-car* (cadr claim))
                                                  (cadr call) (caddr call))))
    (b1-set-laws-subset-map (cdr witness) formula
                           (list :operation (car call) (cadr parts) (car witness)))))

(defun b1-set-laws-subset-append-singleton-base-consequence
    (premise lib atom-proof claim appended grown singleton)
  (declare (ignore premise))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((view (b1-revappend-open-list lib appended (list atom-proof)))
         (opened (b1-revappend-lift-argument lib claim view 1))
         (goal (b1-set-laws-first-at opened 2))
         (item (proof-term-at singleton 1))
         (member (b1-revappend-open-list lib (list *b1-revappend-member* item grown)
                                         nil))
         (nonempty (b1-set-laws-nonempty-value lib grown))
         (have (proof-proof-transport proof nonempty member))
         (empty (b1-set-laws-subset-base lib (list *b1-set-laws-subset* *proof-false*
                                                 grown)
                                         nil))
         (cell (b1-revappend-cons-value lib singleton))
         (supported (b1-set-laws-subset-from-fields lib goal cell have empty)))
      (proof-proof-transport proof supported opened))))

(defun b1-set-laws-subset-append-singleton-base
    (atom-proof lib formula claim appended grown singleton)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-subset-append-singleton-base-consequence
                     premise lib atom-proof claim appended grown singleton)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-subset-append-singleton-step-consequence
    (premise lib cell induction claim appended grown)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-set-laws-subset-fields lib premise cell))
         (added (proof-term-at grown 1))
         (preserved (b1-set-laws-member-into-cons lib (car fields) added))
         (next-proof (proof-proof-modus-ponens proof induction (cadr fields)))
         (view (b1-revappend-open-list lib appended (list cell)))
         (opened (b1-revappend-lift-argument lib claim view 1))
         (reduced (b1-set-laws-first-at opened 2))
         (pair (proof-term-at reduced 1))
         (pair-cell (b1-revappend-cons-value lib pair))
         (supported (b1-set-laws-subset-from-fields lib reduced pair-cell preserved
                                                    next-proof)))
      (proof-proof-transport proof supported opened))))

(defun b1-set-laws-subset-append-singleton-step
    (cell induction lib formula claim appended grown)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-subset-append-singleton-step-consequence
                     premise lib cell induction claim appended grown)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-subset-append-singleton (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (caddr parts))
       (field (proof-list-of-length claim 3))
       (appended (cadr field))
       (append-parts (proof-list-of-length appended 3)))
    (let ((grown (caddr field))
          (xs (cadr append-parts))
          (singleton (caddr append-parts)))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (step (b1-set-laws-subset-append-singleton-step
                  (caddr preparation) (cadddr preparation) lib formula claim appended grown))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-subset-append-singleton-base
                  atom-proof lib formula claim appended grown singleton)))
        (b1-revappend-list-induction lib preparation base step)))))

(defun b1-set-laws-subset-reflexive-step (cell induction lib formula xs)
  (let ((proof (library-library-proof lib))
        (head (list *library-car* xs))
        (tail (list *library-cdr* xs)))
    (proof-with-checked-results
        ((member (b1-revappend-open-list lib (list *b1-revappend-member* head xs)
                                        (list cell)))
         (nonempty (b1-revappend-cons-is-nonempty lib cell))
         (present (proof-proof-transport proof nonempty member)))
      (let ((pair (list *proof-cons* head tail)))
        (proof-with-checked-results
            ((hypothesis (proof-step-first induction))
             (extension (b1-logic-bookproof-from-fact
                         lib (proof-sym "SUBSETP-EQUAL-CONS" "ACL2")
                         (list *library-implies* hypothesis
                               (list *b1-set-laws-subset* tail pair))))
             (grown (proof-proof-modus-ponens proof extension induction))
             (test (proof-step-first cell))
             (reconstruction (b1-logic-bookproof-from-fact
                              lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                              (list *library-implies* test (proof-eq pair xs))))
             (reconstructed (proof-proof-modus-ponens proof reconstruction cell))
             (child (proof-proof-rewrite proof grown reconstructed '(1 2))))
          (b1-set-laws-subset-from-fields lib formula cell present child))))))

(defun b1-set-laws-subset-reflexive (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (preparation (b1-revappend-list-induction-prepare lib formula (cadr parts) nil))
       (step (b1-set-laws-subset-reflexive-step
              (caddr preparation) (cadddr preparation) lib formula (cadr parts)))
       (atom-proof (b1-set-laws-list-induction-atom lib preparation))
       (base (b1-set-laws-subset-base lib formula (list atom-proof))))
    (b1-revappend-list-induction lib preparation base step)))

(defun b1-set-laws-set-equal-law-parts (known lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first known))
         (definition (proof-proof-unfold proof literal))
         (unfolded (proof-proof-rewrite proof known definition '(1))))
      (proof-proof-conjunct proof unfolded))))

(defun b1-set-laws-set-equal-law-consequence-connect (left right lib)
  (proof-with-checked-results
      ((left-literal (proof-step-first left))
       (right-literal (proof-step-first right)))
    (let ((guard (proof-ite left-literal right-literal *proof-false*)))
      (proof-with-checked-results
          ((source (proof-term-at left-literal 1))
           (destination (proof-term-at right-literal 2))
           (law (b1-logic-bookproof-from-fact
                 lib (proof-sym "SUBSETP-EQUAL-TRANSITIVE" "ACL2")
                 (list *library-implies* guard
                       (list *b1-set-laws-subset* source destination))))
           (known (b1-logic-bookproof-normalize-proof lib guard (list left right)
                                                      nil nil nil)))
        (proof-proof-modus-ponens (library-library-proof lib) law known)))))

(defun b1-set-laws-set-equal-law-directions (lib premise)
  (proof-with-checked-results ((head (b1-set-laws-first-at premise 0)))
    (if (equal head *b1-set-laws-set-equal*)
        (proof-with-checked-results
            ((parts (b1-set-laws-set-equal-law-parts premise lib)))
          (list (cadr parts) (car parts)))
      (proof-with-checked-results
          ((premises (proof-proof-conjunct (library-library-proof lib) premise))
           (ab (b1-set-laws-set-equal-law-parts (car premises) lib))
           (bc (b1-set-laws-set-equal-law-parts (cadr premises) lib))
           (forward (b1-set-laws-set-equal-law-consequence-connect (car ab) (car bc) lib))
           (backward (b1-set-laws-set-equal-law-consequence-connect (cadr bc) (cadr ab) lib)))
        (list forward backward)))))

(defun b1-set-laws-set-equal-law-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((directions (b1-set-laws-set-equal-law-directions lib premise))
         (claim (proof-term-at formula 2))
         (view (proof-proof-unfold proof claim))
         (goal (b1-set-laws-first-at view 2))
         (proof-step (b1-logic-bookproof-normalize-proof lib goal directions nil nil nil)))
      (proof-proof-transport proof proof-step view))))

(defun b1-set-laws-set-equal-law (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-set-equal-law-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-list-type-at-atom (lib source-type atom-proof)
  (proof-with-checked-results
      ((literal (proof-step-first source-type))
       (normalized (b1-logic-bookproof-normalize
                    lib literal (list atom-proof)
                    (list *b1-set-laws-true-listp* *b1-logic-eq*) nil nil nil nil)))
    (proof-proof-rewrite (library-library-proof lib) source-type normalized '(1))))

(defun b1-set-laws-subset-filter-identity-base-consequence
    (premise lib atom-proof call op)
  (proof-with-checked-results
      ((reduced (b1-revappend-open-list lib call (list atom-proof))))
    (if (equal op *b1-revappend-intersection*)
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((parts (proof-proof-conjunct proof premise))
               (empty (b1-set-laws-list-type-at-atom lib (car parts) atom-proof))
               (reversed (proof-proof-symmetric proof empty)))
            (proof-proof-chain proof reduced (list reversed))))
      reduced)))

(defun b1-set-laws-subset-filter-identity-base (atom-proof lib formula call op)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-subset-filter-identity-base-consequence
                     premise lib atom-proof call op)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-subset-filter-identity-step-consequence
    (premise lib cell induction call op fixed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premises (proof-proof-conjunct proof premise))
         (fields (b1-set-laws-subset-fields lib (cadr premises) cell))
         (child-type (if (equal op *b1-revappend-intersection*)
                         (b1-structures-true-list-tail lib (car premises) cell)
                       (car premises)))
         (antecedent (b1-set-laws-first-at induction 1))
         (guard (b1-logic-bookproof-normalize-proof
                 lib antecedent (list child-type (cadr fields)) nil nil nil))
         (inherited (proof-proof-modus-ponens proof induction guard))
         (value (b1-revappend-open-list lib call (list cell (car fields)))))
      (if (not (equal op *b1-revappend-intersection*))
          (proof-proof-chain proof value (list inherited))
        (proof-with-checked-results
            ((reduced (proof-proof-rewrite proof value inherited '(1 2 2)))
             (test (proof-step-first cell))
             (value (b1-set-laws-first-at reduced 2))
             (reconstruction (b1-logic-bookproof-from-fact
                              lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                              (list *library-implies* test (proof-eq value fixed))))
             (reconstructed (proof-proof-modus-ponens proof reconstruction cell)))
          (proof-proof-chain proof reduced (list reconstructed)))))))

(defun b1-set-laws-subset-filter-identity-step
    (cell induction lib formula call op fixed)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-subset-filter-identity-step-consequence
                     premise lib cell induction call op fixed)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-subset-filter-identity (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3))
       (call (proof-list-of-length (cadr claim) 3)))
    (let ((op (car call))
          (xs (cadr call))
          (fixed (caddr claim)))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (step (b1-set-laws-subset-filter-identity-step
                  (caddr preparation) (cadddr preparation) lib formula call op fixed))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-subset-filter-identity-base atom-proof lib formula call op)))
        (b1-revappend-list-induction lib preparation base step)))))

(defun b1-set-laws-difference-of-disjoint-base-consequence (premise lib atom-proof call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premises (proof-proof-conjunct proof premise))
         (empty (b1-set-laws-list-type-at-atom lib (car premises) atom-proof))
         (opened (b1-revappend-open-list lib call (list atom-proof)))
         (reversed (proof-proof-symmetric proof empty)))
      (proof-proof-chain proof opened (list reversed)))))

(defun b1-set-laws-difference-of-disjoint-base (atom-proof lib formula call)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-difference-of-disjoint-base-consequence
                     premise lib atom-proof call)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-difference-of-disjoint-step-consequence
    (premise lib cell induction call xs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premises (proof-proof-conjunct proof premise))
         (fields (b1-set-laws-disjoint-head-and-tail lib (cadr premises) cell))
         (proper-tail (b1-structures-true-list-tail lib (car premises) cell))
         (antecedent (b1-set-laws-first-at induction 1))
         (guard (b1-logic-bookproof-normalize-proof
                 lib antecedent (list proper-tail (cadr fields)) nil nil nil))
         (child (proof-proof-modus-ponens proof induction guard))
         (opened (b1-revappend-open-list lib call (list cell (car fields))))
         (reduced (proof-proof-rewrite proof opened child '(1 2 2)))
         (test (proof-step-first cell))
         (value (b1-set-laws-first-at reduced 2))
         (law (b1-logic-bookproof-from-fact lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                                           (list *library-implies* test (proof-eq value xs))))
         (reconstructed (proof-proof-modus-ponens proof law cell)))
      (proof-proof-chain proof reduced (list reconstructed)))))

(defun b1-set-laws-difference-of-disjoint-step (cell induction lib formula call xs)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-difference-of-disjoint-step-consequence
                     premise lib cell induction call xs)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-difference-of-disjoint (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3)))
    (let ((call (cadr claim))
          (xs (caddr claim)))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (step (b1-set-laws-difference-of-disjoint-step
                  (caddr preparation) (cadddr preparation) lib formula call xs))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-difference-of-disjoint-base atom-proof lib formula call)))
        (b1-revappend-list-induction lib preparation base step)))))

(defun b1-set-laws-difference-of-redundant-cons-base
    (atom-proof lib formula with-head original)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (left (b1-revappend-open-list lib with-head (list atom-proof)))
         (right (b1-revappend-open-list lib original (list atom-proof)))
         (reversed (proof-proof-symmetric proof right))
         (consequence (proof-proof-chain proof left (list reversed))))
      (b1-logic-bookproof-prove-implication-with-premise
       lib formula premise consequence))))

(defun b1-set-laws-difference-of-redundant-cons-step-consequence-send
    (step equal-head lib grown old)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib grown (list equal-head)))
         (literal (proof-step-first step)))
      (if (equal literal (proof-neg old))
          (library-library-transport-argument lib step opened 1)
        (proof-proof-transport proof step opened)))))

(defun b1-set-laws-difference-of-redundant-cons-step-consequence-equal-sides
    (first second retained lib cell child with-head original)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (b1-revappend-open-list lib with-head (list cell first)))
         (right (b1-revappend-open-list lib original (list cell second)))
         (reduced (if retained
                      (proof-proof-rewrite proof left child '(1 2 2))
                    (proof-proof-chain proof left (list child))))
         (reversed (proof-proof-symmetric proof right)))
      (proof-proof-chain proof reduced (list reversed)))))

(defun b1-set-laws-difference-of-redundant-cons-step-consequence
    (premise lib cell induction with-head original head old test)
  (let ((proof (library-library-proof lib))
        (grown (list *b1-revappend-member* head (caddr with-head))))
    (proof-with-checked-results
        ((child (proof-proof-modus-ponens proof induction premise))
         (yes (proof-proof-assume proof old t))
         (no (proof-proof-assume proof old nil))
         (hit (proof-proof-assume proof test t))
         (miss (proof-proof-assume proof test nil))
         (reversed (proof-proof-symmetric proof hit))
         (original-hit (proof-proof-rewrite proof premise reversed '(1 1)))
         (known (b1-set-laws-nonempty-value lib (caddr grown)))
         (have-hit (b1-set-laws-difference-of-redundant-cons-step-consequence-send
                    known hit lib grown old))
         (both (b1-set-laws-difference-of-redundant-cons-step-consequence-equal-sides
                have-hit original-hit nil lib cell child with-head original))
         (have-neither (b1-set-laws-difference-of-redundant-cons-step-consequence-send
                        no miss lib grown old))
         (keep (b1-set-laws-difference-of-redundant-cons-step-consequence-equal-sides
                have-neither no t lib cell child with-head original))
         (have-old (b1-set-laws-difference-of-redundant-cons-step-consequence-send
                    yes miss lib grown old))
         (skip (b1-set-laws-difference-of-redundant-cons-step-consequence-equal-sides
                have-old yes nil lib cell child with-head original))
         (different (proof-proof-cases proof old skip keep)))
      (proof-proof-cases proof test both different))))

(defun b1-set-laws-difference-of-redundant-cons-step
    (cell induction lib formula with-head original head old test)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-difference-of-redundant-cons-step-consequence
                     premise lib cell induction with-head original head old test)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-difference-of-redundant-cons (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3))
       (with-head (proof-list-of-length (cadr claim) 3))
       (added (proof-list-of-length (caddr with-head) 3)))
    (let* ((original (caddr claim))
           (xs (cadr with-head))
           (head (list *library-car* xs))
           (old (list *b1-revappend-member* head (caddr added)))
           (test (proof-eq head (cadr added))))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (step (b1-set-laws-difference-of-redundant-cons-step
                  (caddr preparation) (cadddr preparation)
                  lib formula with-head original head old test))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-difference-of-redundant-cons-base
                  atom-proof lib formula with-head original)))
        (b1-revappend-list-induction lib preparation base step)))))

(defun b1-set-laws-memberp-subset-consequence (premise lib formula rule)
  (proof-with-checked-results
      ((parts (proof-proof-conjunct (library-library-proof lib) premise))
       (recognized (proof-step-first (car parts)))
       (call (if (integerp recognized)
                 '(:failure "failure" "")
               (cons *b1-revappend-member* (cdr recognized))))
       (known (b1-logic-bookproof-forces lib call (car parts) nil nil (list rule)))
       (member (b1-set-laws-member-from-subset lib (cadr parts) known))
       (claim (proof-term-at formula 2))
       (consequence (b1-logic-bookproof-normalize-proof
                     (cdr member) claim (list (car member)) nil (list rule) nil)))
    (cons consequence (cdr member))))

(defun b1-set-laws-memberp-subset (lib formula)
  (proof-with-checked-results
      ((result (b1-set-laws-memberp-as-boolean lib))
       (lib (cdr result))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-memberp-subset-consequence
                     premise lib formula (car result)))
       (lib (cdr consequence))
       (step (b1-logic-bookproof-prove-implication-with-premise
               lib formula premise (car consequence))))
    (cons step lib)))

(defun b1-set-laws-memberp-set-equal-consequence-result (proven goal inclusion lib name)
  (proof-with-checked-results
      ((literal (proof-step-first proven))
       (subset (proof-step-first inclusion)))
    (let ((guard (proof-ite literal subset *proof-false*)))
      (proof-with-checked-results
          ((law (b1-logic-bookproof-from-fact lib name (list *library-implies* guard goal)))
           (have (b1-logic-bookproof-normalize-proof lib guard (list proven inclusion)
                                                     nil nil nil)))
        (proof-proof-modus-ponens (library-library-proof lib) law have)))))

(defun b1-set-laws-memberp-set-equal-consequence (premise lib claim left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((directions (b1-set-laws-set-equal-law-parts premise lib)))
      (let ((name (proof-sym "MEMBERP-EQUAL-SUBSETP-EQUAL" "ACL2")))
        (proof-with-checked-results
            ((have (proof-proof-assume proof left t))
             (have-right (b1-set-laws-memberp-set-equal-consequence-result
                          have right (car directions) lib name))
             (yes (b1-membership-membership-case lib claim nil (list have have-right) nil))
             (have-right (proof-proof-assume proof right t))
             (miss-left (proof-proof-assume proof left nil))
             (miss-right (proof-proof-assume proof right nil))
             (have-left (b1-set-laws-memberp-set-equal-consequence-result
                         have-right left (cadr directions) lib name))
             (impossible (b1-logic-bookproof-contradiction lib have-left miss-left claim))
             (neither (b1-membership-membership-case lib claim nil (list miss-left miss-right)
                                                    nil))
             (no (proof-proof-cases proof right impossible neither)))
          (proof-proof-cases proof left yes no))))))

(defun b1-set-laws-memberp-set-equal (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-memberp-set-equal-consequence
                     premise lib claim (cadr claim) (caddr claim))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-member-of-adjoin-added (test lib claim new-list)
  (proof-with-checked-results
      ((value (b1-set-laws-first-at new-list 2))
       (opened (b1-revappend-open-list lib value (list test)))
       (result (proof-proof-chain (library-library-proof lib) new-list (list opened))))
    (b1-membership-membership-case lib claim (list result) (list test) nil)))

(defun b1-set-laws-member-of-adjoin (lib claim)
  (proof-with-checked-results
      ((parts (proof-list-of-length claim 3))
       (call (proof-list-of-length (cadr parts) 3))
       (inserted (proof-list-of-length (caddr call) 3))
       (hit (proof-term-at (caddr parts) 1)))
    (let ((proof (library-library-proof lib))
          (done (list *b1-revappend-member* (cadr inserted) (caddr inserted))))
      (proof-with-checked-results
          ((already (proof-proof-assume proof done t))
           (missing (proof-proof-assume proof done nil))
           (same (proof-proof-assume proof hit t))
           (different (proof-proof-assume proof hit nil))
           (view (b1-revappend-open-list lib inserted (list already)))
           (old (b1-revappend-lift-argument lib call view 2))
           (reversed (proof-proof-symmetric proof same))
           (known (proof-proof-rewrite proof already reversed '(1 1)))
           (yes (b1-membership-membership-case lib claim (list old) (list same known) nil))
           (no (b1-membership-membership-case lib claim (list old) (list different) nil))
           (new-view (b1-revappend-open-list lib inserted (list missing)))
           (new-list (b1-revappend-lift-argument lib call new-view 2))
           (retained (proof-proof-cases proof hit yes no))
           (added-same (b1-set-laws-member-of-adjoin-added same lib claim new-list))
           (added-different (b1-set-laws-member-of-adjoin-added different lib claim new-list))
           (added (proof-proof-cases proof hit added-same added-different)))
        (proof-proof-cases proof done retained added)))))

(mutual-recursion
 (defun b1-set-laws-memberp-of-set-operation-witnesses (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((proof-is-call term *b1-set-laws-memberp*)
          (cons *b1-revappend-member* (cdr term)))
         ((proof-is-call term *proof-not*)
          (if (consp (cdr term))
              (proof-with-checked-results
                  ((witness (b1-set-laws-memberp-of-set-operation-witnesses (cadr term))))
                (proof-neg witness))
            '(:failure "failure" "")))
         ((or (proof-is-call term *b1-revappend-iff*)
              (proof-is-call term *proof-if*))
          (proof-with-checked-results
              ((children (b1-set-laws-memberp-of-set-operation-witnesses-children (cdr term))))
            (cons (car term) children)))
         (t term)))
 (defun b1-set-laws-memberp-of-set-operation-witnesses-children (children)
   (declare (xargs :measure (* 2 (acl2-count children))))
   (if (endp children)
       nil
     (proof-with-checked-results
         ((first (b1-set-laws-memberp-of-set-operation-witnesses (car children)))
          (rest (b1-set-laws-memberp-of-set-operation-witnesses-children (cdr children))))
       (cons first rest)))))

(defun b1-set-laws-memberp-of-set-operation-law (lib operation item args)
  (if (= (len args) 2)
      (b1-set-laws-operation-membership lib operation item (car args) (cadr args))
    '(:failure "failure" "")))

(defun b1-set-laws-memberp-of-set-operation-equation (lib claim call operation-call)
  (cond ((integerp operation-call)
         '(:failure "failure" ""))
        ((endp operation-call)
         '(:failure "failure" ""))
        ((equal (car operation-call) *b1-set-laws-adjoin*)
         (proof-with-checked-results ((proof (b1-set-laws-member-of-adjoin lib claim)))
           (cons proof lib)))
        (t
         (proof-with-checked-results ((item (proof-term-at call 1)))
           (b1-set-laws-memberp-of-set-operation-law lib (car operation-call) item
                                                    (cdr operation-call))))))

(defun b1-set-laws-memberp-of-set-operation (lib formula)
  (proof-with-checked-results
      ((wrapper (b1-set-laws-memberp-as-boolean lib))
       (claim (b1-set-laws-memberp-of-set-operation-witnesses formula))
       (call (proof-term-at claim 1))
       (operation-call (proof-term-at call 2))
       (equation (b1-set-laws-memberp-of-set-operation-equation
                  (cdr wrapper) claim call operation-call))
       (lib (cdr equation))
       (relation (b1-logic-bookproof-case-proof
                  lib (list *library-implies* claim formula) nil
                  (list *library-implies* *b1-revappend-iff* *proof-not*)
                  (list (car wrapper)) 16))
       (step (proof-proof-modus-ponens (library-library-proof lib) relation
                                       (car equation))))
    (cons step lib)))

(defun b1-set-laws-subset-adjoin (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (cadr parts) 3))
       (inserted (proof-list-of-length (cadr claim) 3)))
    (let* ((proof (library-library-proof lib))
           (item (cadr inserted))
           (xs (caddr inserted))
           (before (list *b1-set-laws-subset* xs (caddr claim)))
           (existing (list *b1-revappend-member* item xs)))
      (proof-with-checked-results
          ((already (proof-proof-assume proof existing t))
           (absent (proof-proof-assume proof existing nil))
           (opened (b1-revappend-open-list lib inserted (list already)))
           (same (b1-revappend-lift-argument lib claim opened 1))
           (result (b1-set-laws-memberp-as-boolean lib))
           (rule (car result))
           (lib (cdr result))
           (subset (proof-proof-assume (library-library-proof lib) before t))
           (known (b1-set-laws-member-from-subset lib subset already))
           (lib (cdr known))
           (proof (library-library-proof lib))
           (same-rule (b1-logic-equal-to same))
           (yes (b1-logic-bookproof-case-proof lib formula (list (car known)) nil
                                               (list same-rule rule) 16))
           (missing (proof-proof-assume proof before nil))
           (false-value (b1-logic-bookproof-false-value lib missing))
           (no (b1-logic-bookproof-case-proof lib formula nil nil
                                              (list same-rule (b1-logic-equal-to false-value)
                                                    rule)
                                              16))
           (retained (proof-proof-cases proof before yes no))
           (opened (b1-revappend-open-list lib inserted (list absent)))
           (grown (b1-revappend-lift-argument lib claim opened 1))
           (value (b1-set-laws-first-at grown 2))
           (reduced (b1-revappend-open-list lib value nil))
           (grown (proof-proof-chain proof grown (list reduced)))
           (added (b1-logic-bookproof-case-proof
                   lib formula nil nil (list (b1-logic-equal-to grown) rule) 16))
           (step (proof-proof-cases proof existing retained added)))
        (cons step lib)))))

(defun b1-set-laws-setp-cons (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (left (cadr parts))
         (right (caddr parts))
         (pair (proof-term-at left 1))
         (open-left (proof-proof-unfold proof left))
         (right-test (proof-term-at right 1))
         (open-right (proof-proof-unfold proof right-test))
         (open-true-list (b1-revappend-open-list
                          lib (list *b1-set-laws-true-listp* pair) nil))
         (open-no-duplicates (b1-revappend-open-list
                              lib (list *b1-set-laws-no-duplicates* pair) nil))
         (tail (proof-term-at pair 2))
         (duplicates (list *b1-set-laws-no-duplicates* tail))
         (boolean (b1-predicates-boolean-definition lib duplicates 1))
         (lib (cdr boolean))
         (proof (library-library-proof lib))
         (have (proof-proof-assume proof duplicates t))
         (miss (proof-proof-assume proof duplicates nil))
         (wrapper (b1-set-laws-memberp-as-boolean lib))
         (lib (cdr wrapper))
         (rules (list (car wrapper)
                      (b1-logic-equal-to open-left) (b1-logic-equal-to open-right)
                      (b1-logic-equal-to open-true-list)
                      (b1-logic-equal-to open-no-duplicates)))
         (yes-value (b1-logic-bookproof-boolean-value lib have (car boolean)))
         (yes (b1-logic-bookproof-case-proof
               lib formula nil (list *proof-not*)
               (append rules (list (b1-logic-equal-to yes-value))) 16))
         (no-value (b1-logic-bookproof-false-value lib miss))
         (no (b1-logic-bookproof-case-proof
              lib formula nil (list *proof-not*)
              (append rules (list (b1-logic-equal-to no-value))) 16))
         (step (proof-proof-cases (library-library-proof lib) duplicates yes no)))
      (cons step lib))))

(defun b1-set-laws-setp-adjoin-consequence
    (premise lib unchanged grown item source rule member missing)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((present (library-library-transport-argument lib premise unchanged 1))
         (literal (proof-step-first premise))
         (guard (proof-ite literal (proof-neg (list *b1-set-laws-memberp* item source))
                           *proof-false*))
         (result (b1-set-laws-first-at grown 2))
         (law (b1-logic-bookproof-from-fact lib (proof-sym "SETP-EQUAL-CONS" "ACL2")
                                           (proof-eq (list *b1-set-laws-setp* result)
                                                     guard)))
         (added (b1-logic-bookproof-normalize-proof lib guard (list premise missing)
                                                    (list *proof-not*) (list rule) nil))
         (proved (proof-proof-transport proof added law))
         (absent (library-library-transport-argument lib proved grown 1)))
      (proof-proof-cases proof member present absent))))

(defun b1-set-laws-setp-adjoin (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 2))
       (inserted (proof-list-of-length (cadr claim) 3)))
    (let* ((proof (library-library-proof lib))
           (item (cadr inserted))
           (source (caddr inserted))
           (member (list *b1-revappend-member* item source)))
      (proof-with-checked-results
          ((yes (proof-proof-assume proof member t))
           (no (proof-proof-assume proof member nil))
           (unchanged (b1-revappend-open-list lib inserted (list yes)))
           (grown (b1-revappend-open-list lib inserted (list no)))
           (wrapper (b1-set-laws-memberp-as-boolean lib))
           (lib (cdr wrapper))
           (premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-set-laws-setp-adjoin-consequence premise lib unchanged grown
                                                           item source (car wrapper)
                                                           member no))
           (step (b1-logic-bookproof-prove-implication-with-premise
                   lib formula premise consequence)))
        (cons step lib)))))

(defun b1-set-laws-setp-under-operation-base-consequence
    (premise lib call op atom-proof)
  (proof-with-checked-results
      ((value (b1-revappend-open-list lib call (list atom-proof)))
       (result (if (equal op *b1-set-laws-union*)
                   (proof-with-checked-results
                       ((fields (proof-proof-conjunct (library-library-proof lib) premise)))
                     (cadr fields))
                 (b1-logic-bookproof-normalize-proof
                  lib (list *b1-set-laws-setp* *proof-false*) nil
                  (list *b1-set-laws-setp* *b1-set-laws-true-listp*
                        *b1-set-laws-no-duplicates* *b1-logic-atom* *b1-logic-endp*
                        *b1-logic-eq* *proof-not*)
                  nil nil))))
    (library-library-transport-argument lib result value 1)))

(defun b1-set-laws-setp-under-operation-base (atom-proof lib formula call op)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-setp-under-operation-base-consequence
                     premise lib call op atom-proof)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-set-laws-setp-under-operation-step-consequence-outcome
    (condition lib call cell child member law not-raw head wrapper constructor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (b1-revappend-open-list lib call (list cell condition)))
         (result (b1-set-laws-first-at value 2))
         (suffix (b1-set-laws-first-at child 1)))
      (if (equal result suffix)
          (library-library-transport-argument lib child value 1)
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof member t))
             (literal (proof-step-first law))
             (reduction (b1-logic-bookproof-normalize
                         lib literal (list assumed not-raw condition)
                         (list *b1-revappend-iff* *proof-not*) nil nil nil nil))
             (rewritten (proof-proof-rewrite proof law reduction '(1)))
             (empty (proof-proof-tidy proof rewritten))
             (negative (proof-proof-front proof empty (proof-neg member)))
             (repeated (list *b1-set-laws-memberp* head suffix))
             (no-repeat (b1-logic-bookproof-normalize-proof
                         lib (proof-neg repeated) (list negative) (list *proof-not*)
                         (list wrapper) nil))
             (child-literal (proof-step-first child))
             (no-repeat-literal (proof-step-first no-repeat))
             (guard (proof-ite child-literal no-repeat-literal *proof-false*))
             (law-cons (b1-logic-bookproof-from-fact
                        lib constructor (proof-eq (list *b1-set-laws-setp* result) guard)))
             (proved (b1-logic-bookproof-normalize-proof
                      lib guard (list child no-repeat) nil nil nil))
             (supported (proof-proof-transport proof proved law-cons)))
          (library-library-transport-argument lib supported value 1))))))

(defun b1-set-laws-setp-under-operation-step-consequence
    (premise lib cell induction call op xs other head tail test wrapper constructor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premises (if (equal op *b1-set-laws-union*)
                       (proof-proof-conjunct proof premise)
                     (list premise nil)))
         (cell-literal (proof-step-first cell))
         (original (b1-logic-bookproof-from-fact
                    lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                    (list *library-implies* cell-literal
                          (proof-eq (list *proof-cons* head tail) xs))))
         (reconstruction (proof-proof-modus-ponens proof original cell))
         (proper (library-library-transport-argument lib (car premises) reconstruction 1))
         (head-mem (list *b1-set-laws-memberp* head tail))
         (tail-type (list *b1-set-laws-setp* tail))
         (proper-literal (proof-step-first proper))
         (law (b1-logic-bookproof-from-fact
               lib constructor (proof-eq proper-literal
                                          (proof-ite tail-type (proof-neg head-mem)
                                                     *proof-false*))))
         (opened (proof-proof-rewrite proof proper law '(1)))
         (fields (proof-proof-conjunct proof opened))
         (child-guard
          (if (cadr premises)
              (proof-with-checked-results ((antecedent (b1-set-laws-first-at induction 1)))
                (b1-logic-bookproof-normalize-proof lib antecedent
                                                    (list (car fields) (cadr premises))
                                                    nil nil nil))
            (car fields)))
         (child (proof-proof-modus-ponens proof induction child-guard))
         (result (b1-set-laws-operation-membership lib op head tail other))
         (law (car result))
         (lib (cdr result))
         (proof (library-library-proof lib))
         (member (b1-set-laws-first-at law 1))
         (raw (list *b1-revappend-member* head tail))
         (possible (proof-proof-assume proof raw t))
         (impossible (b1-logic-bookproof-normalize-proof
                      lib head-mem (list possible) nil (list wrapper) nil))
         (cut (proof-proof-cut proof impossible (cadr fields)))
         (not-raw (proof-proof-front proof cut (proof-neg raw)))
         (hit (proof-proof-assume proof test t))
         (yes (b1-set-laws-setp-under-operation-step-consequence-outcome
               hit lib call cell child member law not-raw head wrapper constructor))
         (miss (proof-proof-assume proof test nil))
         (no (b1-set-laws-setp-under-operation-step-consequence-outcome
              miss lib call cell child member law not-raw head wrapper constructor))
         (step (proof-proof-cases proof test yes no)))
      (cons step lib))))

(defun b1-set-laws-setp-under-operation-step
    (cell induction lib formula call op xs other head tail test wrapper constructor)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-set-laws-setp-under-operation-step-consequence
                     premise lib cell induction call op xs other head tail test wrapper
                     constructor))
       (lib (cdr consequence))
       (step (b1-logic-bookproof-prove-implication-with-premise
               lib formula premise (car consequence))))
    (cons step lib)))

(defun b1-set-laws-setp-under-operation (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 2))
       (call (proof-list-of-length (cadr claim) 3)))
    (let* ((op (car call))
           (xs (cadr call))
           (other (caddr call))
           (head (list *library-car* xs))
           (tail (list *library-cdr* xs))
           (test (list *b1-revappend-member* head other)))
      (proof-with-checked-results
          ((wrapper (b1-set-laws-memberp-as-boolean lib))
           (lib (cdr wrapper))
           (constructor (proof-sym "SETP-EQUAL-CONS" "ACL2"))
           (preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (result (b1-set-laws-setp-under-operation-step
                    (caddr preparation) (cadddr preparation) lib formula call op xs other
                    head tail test (car wrapper) constructor))
           (lib (cdr result))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-setp-under-operation-base atom-proof lib formula call op))
           (step (b1-revappend-list-induction lib preparation base (car result))))
        (cons step lib)))))

(defun b1-set-laws-no-duplicates-append-base
    (atom-proof lib left appended original overlap formula)
  (proof-with-checked-results
      ((opened (b1-revappend-open-list lib appended (list atom-proof)))
       (combined (b1-revappend-lift-argument lib left opened 1))
       (current (b1-revappend-open-list lib original (list atom-proof)))
       (common (b1-revappend-open-list lib overlap (list atom-proof))))
    (b1-membership-membership-case lib formula (list combined current common)
                                   (list atom-proof) nil)))

(defun b1-set-laws-no-duplicates-append-step-finish
    (in-first in-second child lib cell combined original overlap formula)
  (let ((evidence (list cell in-first in-second)))
    (proof-with-checked-results
        ((value (b1-set-laws-first-at combined 2))
         (normalized (b1-logic-bookproof-normalize lib value evidence nil nil nil nil nil))
         (new (proof-proof-chain (library-library-proof lib) combined (list normalized)))
         (current (b1-revappend-open-list lib original (list cell in-first)))
         (common (b1-revappend-open-list lib overlap (list cell in-second))))
      (b1-membership-membership-case lib formula (list new current common) evidence
                                     child))))

(defun b1-set-laws-no-duplicates-append-step
    (cell induction lib left appended first second original overlap formula law)
  (proof-with-checked-results
      ((opened (b1-revappend-open-list lib appended (list cell)))
       (combined (b1-revappend-lift-argument lib left opened 1))
       (value (b1-set-laws-first-at combined 2))
       (open-value (b1-revappend-open-list lib value nil))
       (combined (proof-proof-chain (library-library-proof lib) combined (list open-value)))
       (value (b1-set-laws-first-at combined 2))
       (selection (b1-logic-bookproof-select-equivalent-test lib value law))
       (lib (cdr selection))
       (proof (library-library-proof lib))
       (combined (proof-proof-chain proof combined (list (car selection))))
       (present (proof-proof-assume proof first t))
       (missing (proof-proof-assume proof first nil))
       (inside (proof-proof-assume proof second t))
       (outside (proof-proof-assume proof second nil))
       (both (b1-set-laws-no-duplicates-append-step-finish
              present inside nil lib cell combined original overlap formula))
       (only-first (b1-set-laws-no-duplicates-append-step-finish
                    present outside nil lib cell combined original overlap formula))
       (yes (proof-proof-cases proof second both only-first))
       (only-second (b1-set-laws-no-duplicates-append-step-finish
                     missing inside nil lib cell combined original overlap formula))
       (neither (b1-set-laws-no-duplicates-append-step-finish
                 missing outside induction lib cell combined original overlap formula))
       (no (proof-proof-cases proof second only-second neither))
       (step (proof-proof-cases proof first yes no)))
    (cons step lib)))

(defun b1-set-laws-no-duplicates-append (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left (cadr parts))
       (right (caddr parts))
       (appended (proof-term-at left 1))
       (append-parts (proof-list-of-length appended 3))
       (original (proof-term-at right 1))
       (rest (proof-term-at right 2))
       (negated-overlap (proof-term-at rest 2))
       (overlap (proof-term-at negated-overlap 1)))
    (let* ((xs (cadr append-parts))
           (ys (caddr append-parts))
           (head (list *library-car* xs))
           (tail (list *library-cdr* xs))
           (first (list *b1-revappend-member* head tail))
           (second (list *b1-revappend-member* head ys)))
      (proof-with-checked-results
          ((law (b1-set-laws-append-membership lib head tail ys))
           (lib (cdr law))
           (preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (result (b1-set-laws-no-duplicates-append-step
                    (caddr preparation) (cadddr preparation) lib left appended first
                    second original overlap formula (car law)))
           (lib (cdr result))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-no-duplicates-append-base
                  atom-proof lib left appended original overlap formula))
           (step (b1-revappend-list-induction lib preparation base (car result))))
        (cons step lib)))))

(defun b1-set-laws-proper-tail-of-append-expose (cell lib left appended)
  (proof-with-checked-results
      ((opened (b1-revappend-open-list lib appended (list cell))))
    (b1-revappend-lift-argument lib left opened 1)))

(defun b1-set-laws-proper-tail-of-append-step (cell induction lib left appended)
  (proof-with-checked-results
      ((moved (b1-set-laws-proper-tail-of-append-expose cell lib left appended))
       (value (b1-set-laws-first-at moved 2))
       (opened (b1-revappend-open-list lib value nil)))
    (proof-proof-chain (library-library-proof lib) moved (list opened induction))))

(defun b1-set-laws-proper-tail-of-append (lib appended)
  (proof-with-checked-results
      ((ys (proof-term-at appended 2))
       (xs (proof-term-at appended 1)))
    (let* ((left (list *b1-set-laws-true-listp* appended))
           (right (list *b1-set-laws-true-listp* ys))
           (claim (proof-eq left right)))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib claim xs nil))
           (step (b1-set-laws-proper-tail-of-append-step
                  (caddr preparation) (cadddr preparation) lib left appended))
           (atom-proof (b1-set-laws-list-induction-atom lib preparation))
           (base (b1-set-laws-proper-tail-of-append-expose atom-proof lib left appended)))
        (b1-revappend-list-induction lib preparation base step)))))

(defun b1-set-laws-setp-append (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr parts) 3))
         (left (cadr claim))
         (right (caddr claim))
         (appended (proof-term-at left 1))
         (append-parts (proof-list-of-length appended 3))
         (rest (proof-term-at right 2))
         (overlap (proof-term-at rest 2)))
      (let* ((xs (cadr append-parts))
             (ys (caddr append-parts))
             (no-dup-x (list *b1-set-laws-no-duplicates* xs))
             (no-dup-y (list *b1-set-laws-no-duplicates* ys)))
        (proof-with-checked-results
            ((known (b1-logic-bookproof-from-fact
                     lib (proof-sym "NO-DUPLICATESP-EQUAL-APPEND" "ACL2")
                     (list *b1-revappend-iff* (list *b1-set-laws-no-duplicates* appended)
                           (proof-ite no-dup-x (proof-ite no-dup-y overlap *proof-false*)
                                      *proof-false*))))
             (tail-type (b1-set-laws-proper-tail-of-append lib appended))
             (opened (proof-proof-unfold proof left))
             (open-xs (proof-proof-unfold proof (list *b1-set-laws-setp* xs)))
             (open-ys (proof-proof-unfold proof (list *b1-set-laws-setp* ys)))
             (premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (b1-membership-membership-case
                           lib claim (list tail-type opened open-xs open-ys)
                           (list premise) known)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula premise
                                                           consequence))))))
