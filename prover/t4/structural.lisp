(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-structural-atom* (proof-cl "ATOM"))
(defconst *t4-structural-endp* (proof-cl "ENDP"))
(defconst *t4-structural-null* (proof-cl "NULL"))
(defconst *t4-structural-eq* (proof-cl "EQ"))
(defconst *t4-structural-eql* (proof-cl "EQL"))
(defconst *t4-structural-accessor* (proof-sym "LAMBDA-OBJECT-BODY" "ACL2"))
(defconst *t4-structural-last* (proof-cl "LAST"))
(defconst *t4-structural-evens* (proof-sym "EVENS" "ACL2"))
(defconst *t4-structural-odds* (proof-sym "ODDS" "ACL2"))
(defconst *t4-structural-tuple-tail* (proof-sym "CDR-LOOP$-AS-TUPLE" "ACL2"))
(defconst *t4-structural-tuple-empty* (proof-sym "EMPTY-LOOP$-AS-TUPLEP" "ACL2"))
(defconst *t4-structural-test-definitions*
  (list *t4-structural-atom* *t4-structural-endp* *t4-structural-null*
        *t4-structural-eq* *t4-structural-eql* *termination-return-last*))

(defun t4-structural-count (term)
  (list *library-count* term))

(defun t4-structural-evidence-p (value)
  (and (consp value) (eq (car value) :t4-structural-evidence)))

(defun t4-structural-evidence-make (hypotheses expanded recorded)
  (list :t4-structural-evidence hypotheses expanded recorded))

(defun t4-structural-evidence-hypotheses (evidence)
  (if (t4-structural-evidence-p evidence) (cadr evidence) evidence))

(defun t4-structural-evidence-proof (evidence)
  (descent-hypotheses-proof (t4-structural-evidence-hypotheses evidence)))

(defun t4-structural-evidence-tests (evidence)
  (descent-hypotheses-tests (t4-structural-evidence-hypotheses evidence)))

(defun t4-structural-evidence-extra (evidence)
  (descent-hypotheses-extra (t4-structural-evidence-hypotheses evidence)))

(defun t4-structural-evidence-found (evidence)
  (descent-hypotheses-found (t4-structural-evidence-hypotheses evidence)))

(defun t4-structural-evidence-expanded (evidence)
  (caddr evidence))

(defun t4-structural-evidence-recorded (evidence)
  (cadddr evidence))

(defun t4-structural-evidence-with-hypotheses (evidence hypotheses)
  (if (t4-structural-evidence-p evidence)
      (t4-structural-evidence-make hypotheses (t4-structural-evidence-expanded evidence)
                                  (t4-structural-evidence-recorded evidence))
    hypotheses))

(defun t4-structural-evidence-with-proof (evidence lib)
  (t4-structural-evidence-with-hypotheses
   evidence (descent-hypotheses-with-proof (t4-structural-evidence-hypotheses evidence) lib)))

(defun t4-structural-evidence-after-library (evidence before after)
  (if (and (not (equal before after)) (equal (t4-structural-evidence-proof evidence) before))
      (t4-structural-evidence-with-proof evidence after)
    evidence))

(defun t4-structural-evidence-init (lib tests extra)
  (proof-with-checked-results ((hypotheses (descent-hypotheses-init lib tests extra)))
    (t4-structural-evidence-make hypotheses nil nil)))

(defun t4-structural-evidence-selector-p (term)
  (or (proof-is-call term *library-car*) (proof-is-call term *library-cdr*)))

(defun t4-structural-evidence-non-nil-selector (literal)
  (proof-with-checked-results
      ((term (cond ((proof-is-call literal *proof-consp*) (proof-term-at literal 1))
                   ((proof-is-call literal *proof-not*)
                    (proof-with-checked-results ((inner (proof-term-at literal 1)))
                      (and (proof-is-call inner *proof-equal*)
                           (proof-with-checked-results ((right (proof-term-at inner 2)))
                             (and (equal right *proof-false*) (proof-term-at inner 1))))))
                   (t nil))))
    (and (t4-structural-evidence-selector-p term) term)))

(defun t4-structural-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t4-structural-evidence-open-test (proof term)
  (if (not (proof-compound term)) nil
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (cond ((proof-compound head) (proof-proof-beta proof term))
            ((member-equal head *t4-structural-test-definitions*)
             (proof-proof-unfold proof term))
            (t nil)))))

(defun t4-structural-evidence-conditional (proof step term negative)
  (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 3)))
    (let ((test (car parts)) (yes (cadr parts)) (no (caddr parts)))
      (cond
       ((and (not negative) (equal no *proof-false*))
        (proof-proof-conjunct proof step))
       ((and negative (or (equal yes test) (equal yes *proof-true*)))
        (proof-with-checked-results
            ((branch (if (equal yes test)
                         (proof-proof-assume proof test t)
                       (proof-proof-prove proof *proof-true* nil nil)))
             (equation (proof-proof-if-true proof term))
             (taken (proof-proof-transport proof branch equation))
             (consequence (proof-proof-cut proof taken step))
             (front (proof-proof-front proof consequence (proof-neg test))))
          (list front)))
       (t nil)))))

(defun t4-structural-evidence-consequences (proof step literal)
  (let ((negative (proof-is-call literal *proof-not*)))
    (proof-with-checked-results
        ((term (if negative (proof-term-at literal 1) literal))
         (opened (t4-structural-evidence-open-test proof term)))
      (cond
       (opened
        (proof-with-checked-results
            ((rewritten (proof-proof-rewrite proof step opened (if negative '(1 1) '(1))))
             (tidied (proof-proof-tidy proof rewritten)))
          (list tidied)))
       ((and negative (proof-is-call term *proof-not*))
        (proof-with-checked-results
            ((inner (proof-term-at term 1))
             (assumption (proof-proof-assume proof inner nil))
             (consequence (proof-proof-cut proof assumption step))
             (front (proof-proof-front proof consequence inner)))
          (list front)))
       ((proof-is-call term *proof-if*)
        (t4-structural-evidence-conditional proof step term negative))
       (t nil)))))

(defun t4-structural-evidence-selector-consequence (lib proof step literal)
  (proof-with-checked-results ((selector (t4-structural-evidence-non-nil-selector literal)))
    (cond
     ((not selector) nil)
     ((equal lib proof) '(:failure "failure" ""))
     (t
      (proof-with-checked-results
          ((parts (proof-list-of-length selector 2))
           (base (cadr parts))
           (name (concatenate 'string "COMPLETION-OF-" (caddr (car parts))))
           (opened (library-library-axiom lib name (list base)))
           (body (t4-structural-step-term opened 2))
           (if-false (proof-proof-if-false proof body))
           (empty (proof-proof-chain proof opened (list if-false)))
           (rewritten (proof-proof-rewrite-first proof step empty))
           (contradiction (proof-proof-simplify-first proof rewritten nil (list *proof-not*))))
        (proof-proof-front proof contradiction (list *proof-consp* base)))))))

(defun t4-structural-evidence-remember (evidence literal step)
  (let* ((hypotheses (t4-structural-evidence-hypotheses evidence))
         (found (t4-structural-evidence-found evidence))
         (recorded (t4-structural-evidence-recorded evidence)))
    (t4-structural-evidence-make
     (if (assoc-equal literal found)
         hypotheses
       (descent-hypotheses-with-found hypotheses (table-put found literal step)))
     (t4-structural-evidence-expanded evidence)
     (append recorded (list literal)))))

(defund t4-structural-evidence-record-run (n evidence step)
  (declare (xargs :measure (nfix n)))
  (if (zp n) '(:failure "Fuel" "t4-structural-evidence-record-run")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (if (member-equal literal (t4-structural-evidence-recorded evidence))
          evidence
        (let* ((evidence (t4-structural-evidence-remember evidence literal step))
               (lib (t4-structural-evidence-proof evidence))
               (proof (descent-proof lib)))
          (proof-with-checked-results
              ((consequences (t4-structural-evidence-consequences proof step literal))
               (evidence (if (consp consequences)
                             (t4-structural-evidence-record-run (1- n) evidence (car consequences))
                           evidence))
               (evidence (if (consp (cdr consequences))
                             (t4-structural-evidence-record-run (1- n) evidence (cadr consequences))
                           evidence))
               (selected (t4-structural-evidence-selector-consequence lib proof step literal)))
            (if selected
                (t4-structural-evidence-record-run (1- n) evidence selected)
              evidence)))))))

(defun t4-structural-evidence-record (evidence step)
  (t4-structural-evidence-record-run 1000000 evidence step))

(defun t4-structural-evidence-record-tests (tests evidence)
  (if (endp tests) evidence
    (proof-with-checked-results
        ((test (proof-list-of-length (car tests) 2))
         (step (proof-proof-assume (descent-proof (t4-structural-evidence-proof evidence))
                                   (car test) (cadr test)))
         (evidence (t4-structural-evidence-record evidence step)))
      (t4-structural-evidence-record-tests (cdr tests) evidence))))

(defun t4-structural-evidence-record-extra (entries evidence)
  (if (endp entries) evidence
    (proof-with-checked-results ((evidence (t4-structural-evidence-record evidence (cdar entries))))
      (t4-structural-evidence-record-extra (cdr entries) evidence))))

(defun t4-structural-evidence-find (evidence term)
  (proof-with-checked-results
      ((base (descent-hypotheses-find (t4-structural-evidence-hypotheses evidence) term))
       (evidence (t4-structural-evidence-with-hypotheses evidence (cdr base))))
    (cond
     ((or (car base) (not (t4-structural-evidence-p evidence))) (cons (car base) evidence))
     ((t4-structural-evidence-expanded evidence)
      (cons (table-get (t4-structural-evidence-found evidence) term nil) evidence))
     (t
      (proof-with-checked-results
          ((started (t4-structural-evidence-make (cdr base) t (t4-structural-evidence-recorded evidence)))
           (tested (t4-structural-evidence-record-tests (t4-structural-evidence-tests started) started))
           (expanded (t4-structural-evidence-record-extra (t4-structural-evidence-extra tested) tested)))
        (cons (table-get (t4-structural-evidence-found expanded) term nil) expanded))))))

(defun t4-structural-evidence-require (evidence term)
  (proof-with-checked-results ((result (t4-structural-evidence-find evidence term)))
    (if (car result) result (descent-missing-hypothesis term))))

(defun t4-structural-discharge-builtin-tests (tests proof clause step evidence)
  (cond
   ((endp tests) (cons step evidence))
   ((member-equal (car tests) clause)
    (t4-structural-discharge-builtin-tests (cdr tests) proof clause step evidence))
   (t
    (let ((test (car tests)))
      (proof-with-checked-results
          ((positive (if (proof-is-call test *proof-not*)
                         (proof-with-checked-results ((term (proof-term-at test 1)))
                           (t4-structural-evidence-find evidence term))
                       (cons nil evidence)))
           (found (if (car positive) positive
                    (t4-structural-evidence-find (cdr positive) (proof-neg test)))))
        (if (not (car found)) found
          (proof-with-checked-results ((result (proof-proof-discharge proof step (car found))))
            (t4-structural-discharge-builtin-tests (cdr tests) proof clause result (cdr found)))))))))

(defun t4-structural-discharge-builtin-matches (steps proof clause evidence)
  (if (endp steps) (cons nil evidence)
    (proof-with-checked-results
        ((result (t4-structural-discharge-builtin-tests
                  (cdr (proof-step-clause (car steps))) proof clause (car steps) evidence)))
      (if (car result) result
        (t4-structural-discharge-builtin-matches (cdr steps) proof clause (cdr result))))))

(defun t4-structural-direct-builtin (lib clause evidence)
  (if (endp clause) '(:failure "MalformedCandidate" "")
    (let ((proof (descent-proof lib)))
      (proof-with-checked-results
          ((matches (descent-builtin-matches (seq-range 1 24 1) proof clause (car (last clause)) nil)))
        (if (or (car matches) (not evidence)) (cons (car matches) evidence)
          (t4-structural-discharge-builtin-matches (cdr matches) proof clause evidence))))))

(defun t4-structural-step-with-library (step lib)
  (if (failure-p step) step (cons step lib)))

(defun t4-structural-step-with-evidence (step lib evidence)
  (if (failure-p step) step (list step lib evidence)))

(defun t4-structural-has-lemma (lib name)
  (assoc-equal (library-lemma-name name) (proof-proof-facts (library-library-proof lib))))

(defun t4-structural-weak-transitive-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (xy (library-le *library-x* *library-y*))
         (yz (library-le *library-y* *library-z*))
         (x (library-diff *library-y* *library-x*))
         (y (library-diff *library-z* *library-y*))
         (variables (list *library-x* *library-y* *library-z*)))
    (proof-with-checked-results
        ((ints (library-library-ints lib variables))
         (assume-x (proof-proof-assume proof (cadr xy) nil))
         (open-x (library-library-axiom lib "<-ON-OTHERS" (list *library-y* *library-x*)))
         (dx (proof-proof-rewrite proof assume-x open-x '(1 1)))
         (assume-y (proof-proof-assume proof (cadr yz) nil))
         (open-y (library-library-axiom lib "<-ON-OTHERS" (list *library-z* *library-y*)))
         (dy (proof-proof-rewrite proof assume-y open-y '(1 1)))
         (type-x (library-library-type-of lib x ints))
         (type-y (library-library-type-of lib y ints))
         (delta (library-library-cite lib "NONNEGATIVE-SUM" (list y x) (list type-x type-y dx dy)))
         (result (library-library-weak-from-difference lib *library-x* *library-z* delta ints)))
      (library-library-lemma lib "WEAK-TRANSITIVE" (library-le *library-x* *library-z*) result
                             (append (library-guards (list (library-integer *library-x*)
                                                           (library-integer *library-y*)
                                                           (library-integer *library-z*)))
                                     (list (cadr xy) (cadr yz)))))))

(defun t4-structural-weak-comparison-parts (literal)
  (proof-with-checked-results ((parts (proof-list-of-length literal 2)))
    (proof-list-of-length (cadr parts) 3)))

(defun t4-structural-structural-comparison-chain (lib left right)
  (proof-with-checked-results
      ((p (proof-step-first left))
       (p-head (proof-term-at p 0))
       (q (proof-step-first right))
       (q-head (proof-term-at q 0)))
    (if (or (equal p-head *proof-less*) (equal q-head *proof-less*))
        (t4-structural-step-with-library (library-library-compare-chain lib left right) lib)
      (proof-with-checked-results
          ((p (t4-structural-weak-comparison-parts p))
           (q (t4-structural-weak-comparison-parts q)))
        (let ((a (caddr p)) (b (cadr p)) (c (cadr q)))
          (if (not (equal b (caddr q))) '(:failure "InferenceMismatch" "")
            (proof-with-checked-results
                ((lib (if (t4-structural-has-lemma lib "WEAK-TRANSITIVE") lib
                        (t4-structural-weak-transitive-lemma lib)))
                 (a-type (library-library-type-of lib a nil))
                 (b-type (library-library-type-of lib b nil))
                 (c-type (library-library-type-of lib c nil)))
              (t4-structural-step-with-library
               (library-library-cite lib "WEAK-TRANSITIVE" (list a b c)
                                     (list a-type b-type c-type left right))
               lib))))))))

(defconst *t4-structural-branch-variables*
  (list (proof-sym "T4-TEST" "ACL2") (proof-sym "T4-THEN" "ACL2") (proof-sym "T4-ELSE" "ACL2")))

(defun t4-structural-branch-claim (template value)
  (proof-subst template (list (cons *proof-result* value))))

(defun t4-structural-branch-result-case (proof claim conditional template holds)
  (proof-with-checked-results
      ((assumption (proof-proof-assume proof claim t))
       (side (if holds (proof-proof-if-true proof conditional)
               (proof-proof-if-false proof conditional)))
       (reversed (proof-proof-symmetric proof side)))
    (proof-proof-rewrite-result proof assumption reversed template *proof-result*)))

(defun t4-structural-branch-results-prepare (lib name template)
  (let* ((test (car *t4-structural-branch-variables*))
         (yes (cadr *t4-structural-branch-variables*))
         (no (caddr *t4-structural-branch-variables*))
         (conditional (proof-ite test yes no))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((claim (t4-structural-branch-claim template conditional))
         (yes-claim (t4-structural-branch-claim template yes))
         (no-claim (t4-structural-branch-claim template no)))
      (if (t4-structural-has-lemma lib name) lib
        (proof-with-checked-results
            ((yes-case (t4-structural-branch-result-case proof yes-claim conditional template t))
             (no-case (t4-structural-branch-result-case proof no-claim conditional template nil))
             (cases (proof-proof-cases proof test yes-case no-case)))
          (library-library-lemma lib name claim cases (list (proof-neg yes-claim) (proof-neg no-claim))))))))

(defun t4-structural-branch-request-p (value)
  (and (consp value) (eq (car value) :t4-structural-branch-request)))

(defun t4-structural-branch-request-node (request)
  (cadr request))

(defun t4-structural-branch-leaf-check (step node template)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (claim (t4-structural-branch-claim template node)))
    (if (equal literal claim) step '(:failure "InferenceMismatch" ""))))

(defund t4-structural-branch-lambda-result (lib step opened template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((reversed (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*))))

(defund t4-structural-branch-open (lib node)
  (proof-with-checked-results
      ((opened (proof-proof-beta (library-library-proof lib) node))
       (value (t4-structural-step-term opened 2)))
    (cons value opened)))

(defund t4-structural-branch-if-result (lib lemma node left right)
  (proof-proof-use (library-library-proof lib) lemma
                   (seq-zip *t4-structural-branch-variables* (cdr node)) (list left right)))

(mutual-recursion
 (defund t4-structural-structural-branch-results-visit (n node lib template lemma frames)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-structural-structural-branch-results-visit"))
    ((proof-is-call node *proof-if*)
     (if (endp (cddr node)) '(:failure "SearchMiss" "")
       (t4-structural-structural-branch-results-visit
        (1- n) (caddr node) lib template lemma (cons (list :if-left node) frames))))
    ((not (proof-compound node))
     (cons (list :t4-structural-branch-request node template lemma frames n) lib))
    ((endp node) '(:failure "MalformedCandidate" ""))
    ((proof-compound (car node))
     (proof-with-checked-results ((opened (t4-structural-branch-open lib node)))
       (t4-structural-structural-branch-results-visit
        (1- n) (car opened) lib template lemma (cons (list :lambda (cdr opened)) frames))))
    (t (cons (list :t4-structural-branch-request node template lemma frames n) lib))))
 (defund t4-structural-branch-results-return (n step lib template lemma frames)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-structural-branch-results-return"))
    ((endp frames) (cons step lib))
    (t
     (let* ((frame (car frames))
            (node (cadr frame))
            (rest (cdr frames)))
       (case (car frame)
         (:if-left
          (if (endp (cdddr node)) '(:failure "SearchMiss" "")
            (t4-structural-structural-branch-results-visit
             (1- n) (cadddr node) lib template lemma (cons (list :if-right node step) rest))))
         (:if-right
          (if (consp (cddddr node))
              (t4-structural-structural-branch-results-visit
               (1- n) (car (cddddr node)) lib template lemma (cons (list :if-extra) rest))
            (proof-with-checked-results
                ((joined (t4-structural-branch-if-result lib lemma node (caddr frame) step)))
              (t4-structural-branch-results-return (1- n) joined lib template lemma rest))))
         (:if-extra '(:failure "SearchMiss" ""))
         (otherwise
          (proof-with-checked-results ((joined (t4-structural-branch-lambda-result lib step node template)))
            (t4-structural-branch-results-return (1- n) joined lib template lemma rest)))))))))

(defun t4-structural-branch-results-start (lib name value template)
  (proof-with-checked-results ((lib (t4-structural-branch-results-prepare lib name template)))
    (t4-structural-structural-branch-results-visit 1000000 value lib template (library-lemma-name name) nil)))

(defun t4-structural-branch-results-resume (request reply)
  (proof-with-checked-results
      ((reply reply)
       (step (car reply))
       (template (caddr request))
       (step (t4-structural-branch-leaf-check step (t4-structural-branch-request-node request) template)))
    (t4-structural-branch-results-return (cadr (cddddr request)) step (cdr reply) template
                                         (cadddr request) (car (cddddr request)))))

(defun t4-structural-branch-results-replies (replies result)
  (cond
   ((failure-p result) result)
   ((not (t4-structural-branch-request-p (car result))) result)
   ((endp replies)
    (cons (list :t4-structural-branch-results (t4-structural-branch-request-node (car result)))
          (cdr result)))
   (t (t4-structural-branch-results-replies
       (cdr replies) (t4-structural-branch-results-resume (car result) (car replies))))))

(defun t4-structural-structural-branch-results (lib name value template replies)
  (t4-structural-branch-results-replies replies (t4-structural-branch-results-start lib name value template)))

(defun t4-structural-structural-cons-count (lib obj cons)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((size (proof-proof-unfold proof (t4-structural-count obj)))
         (body (t4-structural-step-term size 2))
         (selected (proof-proof-select proof body cons)))
      (t4-structural-step-with-library (proof-proof-chain proof size (list selected)) lib))))

(defun t4-structural-structural-constructor-count (lib a b)
  (let ((proof (library-library-proof lib))
        (obj (list *proof-cons* a b)))
    (proof-with-checked-results
        ((cons (proof-proof-fact proof "consp-cons" (list (list *library-x* a) (list *library-y* b))))
         (counted (t4-structural-structural-cons-count lib obj cons))
         (first (library-library-axiom lib "CAR-CONS" (list a b)))
         (rewritten (proof-proof-rewrite proof (car counted) first '(1 2 2 1 1)))
         (rest (library-library-axiom lib "CDR-CONS" (list a b)))
         (rewritten (proof-proof-rewrite proof rewritten rest '(1 2 2 2 1))))
      (t4-structural-step-with-library (proof-proof-tidy proof rewritten) lib))))

(defun t4-structural-structural-replace-endpoints (lib step left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((head (t4-structural-step-term step 0))
         (strict (equal head *proof-less*))
         (left (proof-proof-symmetric proof left))
         (step (proof-proof-rewrite proof step left (if strict '(1 1) '(1 1 2))))
         (right (proof-proof-symmetric proof right))
         (step (proof-proof-rewrite proof step right (if strict '(1 2) '(1 1 1)))))
      (t4-structural-step-with-library (proof-proof-tidy proof step) lib))))

(defun t4-structural-structural-add-prefix (lib step a)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (head (proof-term-at literal 0))
         (strict (equal head *proof-less*))
         (parts (library-compare-chain-arguments literal strict)))
      (let* ((left (car parts))
             (right (cadr parts))
             (smaller (library-plus *proof-one* (library-plus a left)))
             (larger (library-plus *proof-one* (library-plus a right))))
        (t4-structural-step-with-library
         (if strict
             (proof-with-checked-results
                 ((comparison (library-library-comparison lib left right nil))
                  (rewritten (proof-proof-rewrite proof step comparison '(1))))
               (library-library-less-from-difference lib smaller larger rewritten nil))
           (proof-with-checked-results
               ((comparison (library-library-axiom lib "<-ON-OTHERS" (list right left)))
                (rewritten (proof-proof-rewrite proof step comparison '(1 1))))
             (library-library-weak-from-difference lib smaller larger rewritten nil)))
         lib)))))

(defun t4-structural-structural-count-of-nil (lib)
  (t4-structural-step-with-library
   (proof-proof-simplify (library-library-proof lib) (t4-structural-count *proof-false*)
                         nil (list *library-count*))
   lib))

(defun t4-structural-slice-from-one (term)
  (if (integerp term) '(:failure "MalformedCandidate" "") (cdr term)))

(defun t4-structural-structural-zero-bound (lib parent cons)
  (let ((size (t4-structural-count parent)))
    (t4-structural-step-with-library
     (if (not cons)
         (proof-with-checked-results ((natural (library-library-natural lib size)))
           (library-library-cite lib "NATURAL-NONNEGATIVE" (list size) (list natural)))
       (proof-with-checked-results
           ((opened (t4-structural-structural-cons-count lib parent cons))
            (sum (t4-structural-step-term (car opened) 2))
            (terms (t4-structural-slice-from-one sum))
            (parts (proof-list-of-length terms 2))
            (tail-sum (cadr parts))
            (natural (library-library-natural lib tail-sum))
            (nonneg (library-library-cite lib "NATURAL-NONNEGATIVE" (list tail-sum) (list natural)))
            (integer (library-library-type-of lib tail-sum nil))
            (positive (library-library-cite lib "POSITIVE-ONE-PLUS" (list tail-sum) (list integer nonneg))))
         (library-library-transport-argument lib positive (car opened) 2)))
     lib)))

(defun t4-structural-last-lemma-finish (lib formula measure test body opened recursive tail)
  (let ((proof (library-library-proof lib))
        (template (library-le (t4-structural-count *proof-result*) measure)))
    (proof-with-checked-results
        ((type (library-library-type-of lib measure nil))
         (base (library-library-cite lib "WEAK-REFLEXIVE" (list measure) (list type)))
         (true (proof-proof-if-true proof body))
         (true (proof-proof-chain proof opened (list true)))
         (base (t4-structural-branch-lambda-result lib base true template))
         (false (proof-proof-if-false proof body))
         (false (proof-proof-chain proof opened (list false)))
         (recursive (t4-structural-branch-lambda-result lib recursive false template))
         (case-step (proof-proof-cases proof test base recursive))
         (ordinal (library-library-builtin lib 1 *library-x*))
         (step (proof-proof-induct proof ordinal case-step formula measure
                                  (list (list (list *library-x* tail))))))
      (library-library-lemma lib "LAST-WEAK" formula step nil))))

(defun t4-structural-last-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (tail (list *library-cdr* x))
         (term (list *t4-structural-last* x))
         (measure (t4-structural-count x))
         (formula (library-le (t4-structural-count term) measure))
         (smaller-formula (library-le (t4-structural-count (list *t4-structural-last* tail))
                                      (t4-structural-count tail))))
    (proof-with-checked-results
        ((descent (library-library-builtin lib 3 x))
         (opened (proof-proof-unfold proof term))
         (body (t4-structural-step-term opened 2))
         (test (proof-term-at body 1))
         (evidence (t4-structural-evidence-init lib (list (list test nil)) nil))
         (cons (t4-structural-evidence-require evidence (list *proof-consp* x)))
         (descent (proof-proof-discharge proof descent (car cons)))
         (less (proof-step-first descent))
         (ih (proof-proof-assume proof (proof-ite less smaller-formula *proof-true*) t))
         (smaller (proof-proof-prove-if proof ih descent))
         (bound (library-library-cite lib "COUNT-CDR-WEAK" (list x) nil))
         (recursive (t4-structural-structural-comparison-chain lib smaller bound)))
      (t4-structural-last-lemma-finish (cdr recursive) formula measure test body opened
                                      (car recursive) tail))))

(defun t4-structural-structural-last-bound (lib obj)
  (proof-with-checked-results
      ((lib (if (t4-structural-has-lemma lib "LAST-WEAK") lib (t4-structural-last-lemma lib))))
    (t4-structural-step-with-library (library-library-cite lib "LAST-WEAK" (list obj) nil) lib)))

(defun t4-structural-structural-evens-nonempty (lib smaller cons nonempty)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((x (t4-structural-step-term cons 1))
         (term (list *t4-structural-evens* x))
         (opened (proof-proof-unfold proof term))
         (body (t4-structural-step-term opened 2))
         (branch (proof-proof-select proof body nonempty))
         (value (proof-proof-chain proof opened (list branch)))
         (pair (t4-structural-step-term value 2))
         (arguments (t4-structural-slice-from-one pair))
         (parts (proof-list-of-length arguments 2))
         (a (car parts))
         (b (cadr parts))
         (same (proof-proof-reflexive proof (t4-structural-count term)))
         (expanded (proof-proof-rewrite proof same value '(1 2 1)))
         (constructed (t4-structural-structural-constructor-count lib a b))
         (left (proof-proof-chain proof expanded (list (car constructed))))
         (shifted (t4-structural-structural-add-prefix lib smaller (t4-structural-count a)))
         (right (t4-structural-structural-cons-count lib x cons)))
      (t4-structural-structural-replace-endpoints lib (car shifted) left (car right)))))

(defun t4-structural-evens-weak-lemma-finish (lib term test formula recursive twice)
  (let ((proof (library-library-proof lib)) (x *library-x*))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (body (t4-structural-step-term opened 2))
         (if-true (proof-proof-if-true proof body))
         (empty (proof-proof-chain proof opened (list if-true)))
         (same (proof-proof-reflexive proof (t4-structural-count term)))
         (empty (proof-proof-rewrite proof same empty '(1 2 1)))
         (count-nil (t4-structural-structural-count-of-nil lib))
         (empty (proof-proof-chain proof empty (list (car count-nil))))
         (bound (t4-structural-structural-zero-bound lib x nil))
         (reversed (proof-proof-symmetric proof empty))
         (base (proof-proof-rewrite-first proof (car bound) reversed))
         (ordinal (library-library-builtin lib 1 x))
         (case-step (proof-proof-cases proof test base recursive))
         (step (proof-proof-induct proof ordinal case-step formula (t4-structural-count x)
                                  (list (list (list x twice))))))
      (library-library-lemma lib "EVENS-WEAK" formula step nil))))

(defun t4-structural-path-head-p (head)
  (member-equal head (list *library-car* *library-cdr* *t4-structural-accessor* *t4-structural-last*)))

(defun t4-structural-count-path (child parent heads)
  (if (or (equal child parent) (not (proof-compound child)))
      (cons child heads)
    (proof-with-checked-results ((head (proof-term-at child 0)))
      (if (not (t4-structural-path-head-p head)) (cons child heads)
        (if (and (consp (cdr child)) (equal (len child) 2))
            (t4-structural-count-path (cadr child) parent (cons head heads))
          '(:failure "SearchMiss" ""))))))

(defun t4-structural-path-names (heads)
  (if (endp heads) nil
    (proof-with-checked-results
        ((name (proof-term-at (car heads) 2))
         (name (if (stringp name) name '(:failure "failure" "")))
         (rest (t4-structural-path-names (cdr heads))))
      (cons name rest))))

(defun t4-structural-path-child (heads child)
  (if (endp heads) child
    (t4-structural-path-child (cdr heads) (list (car heads) child))))

(defun t4-structural-count-quoted-symbol-p (term)
  (and (proof-is-call term *proof-quote*)
       (proof-with-checked-results ((datum (proof-term-at term 1)))
         (and (true-listp datum)
              (proof-with-checked-results ((tag (proof-term-at datum 0)))
                (equal tag "sym"))))))

(defun t4-structural-count-quoted-bound (lib child parent evidence strict)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons (if strict (t4-structural-evidence-require evidence (list *proof-consp* parent))
                 (cons nil evidence)))
         (bound (t4-structural-structural-zero-bound lib parent (car cons)))
         (size (proof-proof-simplify proof (t4-structural-count child) nil (list *library-count*)))
         (reversed (proof-proof-symmetric proof size)))
      (t4-structural-step-with-evidence (proof-proof-rewrite-first proof (car bound) reversed)
                                        lib (cdr cons)))))

(defun t4-structural-count-selector-edge (lib child head base cons)
  (if (not cons)
      (library-library-cite lib (if (equal head *library-car*) "COUNT-CAR-WEAK" "COUNT-CDR-WEAK")
                            (list base) nil)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((builtin (library-library-builtin lib (if (equal head *library-car*) 2 3) base))
           (ordinal (proof-proof-discharge proof builtin cons))
           (comparison (library-library-ordinal-comparison lib (t4-structural-count child)
                                                           (t4-structural-count base))))
        (proof-proof-rewrite proof ordinal comparison '(1))))))

(defun t4-structural-weak-reflexive-count (lib parent)
  (let ((size (t4-structural-count parent)))
    (proof-with-checked-results ((type (library-library-type-of lib size nil)))
      (library-library-cite lib "WEAK-REFLEXIVE" (list size) (list type)))))

(defun t4-structural-accessor-finish (lib obj name opened template claim assumption cons branch)
  (proof-with-checked-results
      ((rewritten (t4-structural-branch-lambda-result lib branch opened template))
       (literal (if assumption (proof-step-first (car assumption)) nil))
       (lib (library-library-lemma lib name claim rewritten (if assumption (list (proof-neg literal)) nil))))
    (t4-structural-step-with-library
     (library-library-cite lib name (list obj) (if cons (list cons) nil)) lib)))

(mutual-recursion
 (defund t4-structural-count-bound-run (n lib child parent evidence strict)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-count-bound-run")
     (proof-with-checked-results
         ((cons (if strict (t4-structural-evidence-find evidence (list *proof-consp* parent))
                  (cons nil evidence)))
          (evidence (cdr cons))
          (path (if (car cons) (t4-structural-count-path child parent nil) nil)))
       (let ((heads (cdr path)))
         (if (and (car cons) (equal (car path) parent) (consp (cdr heads))
                  (member-equal (car heads) (list *library-car* *library-cdr* *t4-structural-accessor*)))
             (proof-with-checked-results
                 ((bound (t4-structural-path-bound-run (1- n) lib (reverse heads) parent (car cons))))
               (list (car bound) (cdr bound) (t4-structural-evidence-after-library evidence lib (cdr bound))))
           (t4-structural-count-bound-edges (1- n) lib child parent evidence strict))))))
 (defund t4-structural-path-bound-run (n lib path parent cons)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-path-bound-run")
     (let ((heads (reverse path)))
       (proof-with-checked-results
           ((names (t4-structural-path-names heads))
            (name (concatenate 'string "COUNT-" (text-join "-" names) "-LESS"))
            (lib (if (t4-structural-has-lemma lib name) lib
                   (let ((child (t4-structural-path-child heads *library-x*))
                         (test (list *proof-consp* *library-x*)))
                     (proof-with-checked-results
                         ((evidence (t4-structural-evidence-init lib (list (list test t)) nil))
                          (bound (t4-structural-count-bound-edges (1- n) lib child *library-x* evidence t)))
                       (library-library-lemma (cadr bound) name
                                              (library-lt (t4-structural-count child)
                                                          (t4-structural-count *library-x*))
                                              (car bound) (list (proof-neg test))))))))
         (t4-structural-step-with-library (library-library-cite lib name (list parent) (list cons)) lib)))))
 (defund t4-structural-count-bound-edges (n lib child parent evidence strict)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-structural-count-bound-edges"))
    ((and (not strict) (equal child parent))
     (t4-structural-step-with-evidence (t4-structural-weak-reflexive-count lib parent) lib evidence))
    (t
     (proof-with-checked-results ((quoted-symbol (t4-structural-count-quoted-symbol-p child)))
       (cond
        (quoted-symbol (t4-structural-count-quoted-bound lib child parent evidence strict))
        ((not (proof-compound child)) '(:failure "SearchMiss" ""))
        (t
         (proof-with-checked-results
             ((parts (proof-list-of-length child 2))
              (head (car parts))
              (base (cadr parts))
              (cons (if strict (t4-structural-evidence-find evidence (list *proof-consp* base))
                       (cons nil evidence)))
              (edge (cond
                     ((member-equal head (list *library-car* *library-cdr*))
                      (t4-structural-step-with-library
                       (t4-structural-count-selector-edge lib child head base (car cons)) lib))
                     ((member-equal head (list *t4-structural-accessor* *t4-structural-last*
                                               *t4-structural-evens* *t4-structural-odds*))
                      (t4-structural-transform-bound-run (1- n) lib head base))
                     (t '(:failure "SearchMiss" "")))))
           (t4-structural-count-bound-finish
            (1- n) (cdr edge) (car edge) head base parent
            (t4-structural-evidence-after-library (cdr cons) lib (cdr edge)) strict))))))))
 (defund t4-structural-count-bound-finish (n lib edge head base parent evidence strict)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-count-bound-finish")
     (proof-with-checked-results ((edge-head (if strict (t4-structural-step-term edge 0) nil)))
       (let ((need-strict (and strict (not (equal edge-head *proof-less*)))))
         (cond
          ((not (equal base parent))
           (proof-with-checked-results
               ((rest (t4-structural-count-bound-edges (1- n) lib base parent evidence need-strict))
                (chained (t4-structural-structural-comparison-chain (cadr rest) edge (car rest))))
             (list (car chained) (cdr chained)
                   (t4-structural-evidence-after-library (caddr rest) (cadr rest) (cdr chained)))))
          ((not need-strict) (list edge lib evidence))
          ((not (equal head *t4-structural-accessor*)) '(:failure "SearchMiss" ""))
          (t
           (proof-with-checked-results
               ((cons (t4-structural-evidence-require evidence (list *proof-consp* base)))
                (bound (t4-structural-accessor-bound-run (1- n) lib base (car cons))))
             (list (car bound) (cdr bound)
                   (t4-structural-evidence-after-library (cdr cons) lib (cdr bound))))))))))
 (defund t4-structural-transform-bound-run (n lib head base)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-structural-transform-bound-run"))
    ((equal head *t4-structural-accessor*) (t4-structural-accessor-bound-run (1- n) lib base nil))
    ((equal head *t4-structural-last*) (t4-structural-structural-last-bound lib base))
    (t (t4-structural-split-bound-run (1- n) lib head base nil))))
 (defund t4-structural-accessor-bound-run (n lib obj cons)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-accessor-bound-run")
     (let ((name (if cons "LAMBDA-BODY-LESS" "LAMBDA-BODY-WEAK"))
           (proof (library-library-proof lib)))
       (if (t4-structural-has-lemma lib name)
           (t4-structural-step-with-library (library-library-cite lib name (list obj) (if cons (list cons) nil)) lib)
         (let* ((x *library-x*)
                (term (list *t4-structural-accessor* x))
                (count-x (t4-structural-count x))
                (count-result (t4-structural-count *proof-result*))
                (template (if cons (library-lt count-result count-x) (library-le count-result count-x))))
           (proof-with-checked-results
               ((test (if cons (proof-proof-assume proof (list *proof-consp* x) t) nil))
                (assumption (if cons (list test) nil))
                (opened (proof-proof-unfold proof term))
                (body (t4-structural-step-term opened 2))
                (request (t4-structural-branch-results-start lib (concatenate 'string name "-IF") body template))
                (proved (t4-structural-accessor-visit (1- n) request assumption cons))
                (count-term (t4-structural-count term))
                (claim (if cons (library-lt count-term count-x) (library-le count-term count-x))))
             (t4-structural-accessor-finish (cdr proved) obj name opened template claim assumption cons
                                           (car proved))))))))
 (defund t4-structural-accessor-visit (n result assumption cons)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-structural-accessor-visit"))
    ((not (t4-structural-branch-request-p (car result))) result)
    (t
     (proof-with-checked-results
         ((reply (t4-structural-structural-accessor-bound-leaf
                  (1- n) (t4-structural-branch-request-node (car result)) (cdr result) assumption cons))
          (result (t4-structural-branch-results-resume (car result) reply)))
       (t4-structural-accessor-visit (1- n) result assumption cons)))))
 (defund t4-structural-structural-accessor-bound-leaf (n value lib assumption cons)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-structural-accessor-bound-leaf")
     (proof-with-checked-results
         ((evidence (t4-structural-evidence-init lib nil assumption))
          (bound (t4-structural-count-bound-run (1- n) lib value *library-x* evidence (if cons t nil))))
       (cons (car bound) (cadr bound)))))
 (defund t4-structural-split-bound-run (n lib head obj tail-cons)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-split-bound-run")
     (proof-with-checked-results
         ((lib (if (t4-structural-has-lemma lib "EVENS-WEAK") lib
                 (t4-structural-evens-weak-lemma-run (1- n) lib))))
       (cond
        ((equal head *t4-structural-odds*)
         (let ((tail (list *library-cdr* obj)))
           (proof-with-checked-results
               ((weak (library-library-cite lib "EVENS-WEAK" (list tail) nil))
                (evidence (t4-structural-evidence-init lib nil (if tail-cons (list tail-cons) nil)))
                (bound (t4-structural-count-bound-run (1- n) lib tail obj evidence (if tail-cons t nil)))
                (result (t4-structural-structural-comparison-chain (cadr bound) weak (car bound)))
                (lib (cdr result))
                (proof (library-library-proof lib))
                (equality (proof-proof-unfold proof (list *t4-structural-odds* obj)))
                (reversed (proof-proof-symmetric proof equality)))
             (t4-structural-step-with-library (proof-proof-rewrite-first proof (car result) reversed) lib))))
        ((not tail-cons)
         (t4-structural-step-with-library (library-library-cite lib "EVENS-WEAK" (list obj) nil) lib))
        (t
         (proof-with-checked-results
             ((lib (if (t4-structural-has-lemma lib "EVENS-LESS") lib
                     (t4-structural-evens-less-lemma-run (1- n) lib))))
           (t4-structural-step-with-library
            (library-library-cite lib "EVENS-LESS" (list obj) (list tail-cons)) lib)))))))
 (defund t4-structural-evens-less-lemma-run (n lib)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-evens-less-lemma-run")
     (let* ((x *library-x*)
            (tail (list *library-cdr* x))
            (twice (list *library-cdr* tail)))
       (proof-with-checked-results
           ((hypothesis (library-inherited proof-proof-assume lib (list *proof-consp* tail) t))
            (evidence (t4-structural-evidence-init lib nil (list hypothesis)))
            (decrease (t4-structural-count-bound-run (1- n) lib twice tail evidence t))
            (lib (cadr decrease))
            (weak (library-library-cite lib "EVENS-WEAK" (list twice) nil))
            (smaller (t4-structural-structural-comparison-chain lib weak (car decrease)))
            (evidence (t4-structural-evidence-after-library (caddr decrease) lib (cdr smaller)))
            (lib (cdr smaller))
            (cons (t4-structural-evidence-require evidence (list *proof-consp* x)))
            (nonempty (library-inherited proof-proof-prove lib (proof-neg (list *t4-structural-endp* x))
                                         (list (car cons))
                                         (list *t4-structural-endp* *t4-structural-atom* *proof-not*)))
            (step (t4-structural-structural-evens-nonempty lib (car smaller) (car cons) nonempty))
            (literal (proof-step-first hypothesis)))
         (library-library-lemma (cdr step) "EVENS-LESS"
                                (library-lt (t4-structural-count (list *t4-structural-evens* x))
                                            (t4-structural-count x))
                                (car step) (list (proof-neg literal)))))))
 (defund t4-structural-evens-weak-lemma-run (n lib)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-evens-weak-lemma-run")
     (let* ((x *library-x*)
            (test (list *t4-structural-endp* x))
            (term (list *t4-structural-evens* x))
            (tail (list *library-cdr* x))
            (twice (list *library-cdr* tail))
            (formula (library-le (t4-structural-count term) (t4-structural-count x)))
            (smaller-formula (library-le (t4-structural-count (list *t4-structural-evens* twice))
                                         (t4-structural-count twice))))
       (proof-with-checked-results
           ((evidence (t4-structural-evidence-init lib (list (list test nil)) nil))
            (cons (t4-structural-evidence-require evidence (list *proof-consp* x)))
            (bound (t4-structural-count-bound-run (1- n) lib twice x (cdr cons) t))
            (lib (cadr bound))
            (proof (library-library-proof lib))
            (comparison (library-library-ordinal-comparison lib (t4-structural-count twice)
                                                            (t4-structural-count x)))
            (smaller (proof-proof-transport proof (car bound) comparison))
            (less (proof-step-first smaller))
            (assumption (proof-proof-assume proof (proof-ite less smaller-formula *proof-true*) t))
            (ih (proof-proof-prove-if proof assumption smaller))
            (upper (library-library-cite lib "COUNT-CDR-WEAK" (list tail) nil))
            (chained (t4-structural-structural-comparison-chain lib ih upper))
            (evidence (t4-structural-evidence-after-library (caddr bound) lib (cdr chained)))
            (lib (cdr chained))
            (nonempty (t4-structural-evidence-require evidence (proof-neg test)))
            (recursive (t4-structural-structural-evens-nonempty lib (car chained) (car cons) (car nonempty))))
         (t4-structural-evens-weak-lemma-finish (cdr recursive) term test formula (car recursive) twice))))))

(defun t4-structural-structural-count-bound (lib child parent evidence strict)
  (t4-structural-count-bound-run 1000000 lib child parent evidence strict))

(defun t4-structural-structural-path-bound (lib path parent cons)
  (t4-structural-path-bound-run 1000000 lib path parent cons))

(defun t4-structural-structural--count-bound (lib child parent evidence strict)
  (t4-structural-count-bound-edges 1000000 lib child parent evidence strict))

(defun t4-structural-structural-transform-bound (lib head base)
  (t4-structural-transform-bound-run 1000000 lib head base))

(defun t4-structural-structural-accessor-bound (lib obj cons)
  (t4-structural-accessor-bound-run 1000000 lib obj cons))

(defun t4-structural-structural-split-bound (lib head obj tail-cons)
  (t4-structural-split-bound-run 1000000 lib head obj tail-cons))

(defun t4-structural-structural-evens-weak-lemma (lib)
  (t4-structural-evens-weak-lemma-run 1000000 lib))

(defun t4-structural-tuple-descent-tail (lib after obj evidence nonempty has-head)
  (let ((proof (library-library-proof lib))
        (head (list *library-car* obj)))
    (proof-with-checked-results
        ((tail (proof-proof-unfold proof (list *t4-structural-tuple-tail* obj)))
         (body (t4-structural-step-term tail 2))
         (selected (proof-proof-select proof body nonempty))
         (tail (proof-proof-chain proof tail (list selected)))
         (actual (proof-term-at after 1))
         (same (proof-proof-reflexive proof actual))
         (first (proof-proof-rewrite proof same tail '(1 2 1)))
         (body (t4-structural-step-term tail 2))
         (arguments (t4-structural-slice-from-one body))
         (car-cons (library-library-axiom lib "CAR-CONS" arguments))
         (first (proof-proof-chain proof first (list car-cons)))
         (builtin (library-library-builtin lib 3 head))
         (discharged (proof-proof-discharge proof builtin has-head))
         (reversed (proof-proof-symmetric proof first))
         (rewritten (proof-proof-rewrite proof discharged reversed '(1 1 1))))
      (t4-structural-step-with-evidence (proof-proof-tidy proof rewritten) lib evidence))))

(defun t4-structural-structural-tuple-descent (lib goal evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length goal 3))
         (measure (proof-term-at (caddr parts) 1))
         (obj (proof-term-at measure 1))
         (cons (t4-structural-evidence-require evidence (list *proof-consp* obj)))
         (nonempty (proof-proof-prove proof (proof-neg (list *t4-structural-endp* obj))
                                      (list (car cons))
                                      (list *t4-structural-endp* *t4-structural-atom* *proof-not*)))
         (head (list *library-car* obj))
         (cons-head (list *proof-consp* head))
         (empty (list *t4-structural-tuple-empty* obj))
         (opened (proof-proof-unfold proof empty))
         (body (t4-structural-step-term opened 2))
         (selected (proof-proof-select proof body nonempty))
         (selected (proof-proof-chain proof opened (list selected)))
         (absent (proof-proof-assume proof cons-head nil))
         (endp-head (proof-proof-unfold proof (list *t4-structural-endp* head)))
         (atom-head (proof-proof-unfold proof (list *t4-structural-atom* head)))
         (opened-test (proof-proof-chain proof endp-head (list atom-head)))
         (no-head (proof-proof-transport proof absent opened-test))
         (body (t4-structural-step-term selected 2))
         (branch (proof-proof-select proof body no-head))
         (selected (proof-proof-chain proof selected (list branch)))
         (true (proof-proof-true-from-eq proof selected))
         (not-empty (t4-structural-evidence-require (cdr cons) (proof-neg empty)))
         (contradiction (proof-proof-cut proof true (car not-empty)))
         (has-head (proof-proof-front proof contradiction cons-head)))
      (t4-structural-tuple-descent-tail lib (cadr parts) obj (cdr not-empty) nonempty has-head))))

(defun t4-structural-count-descent-bound (lib child parent evidence)
  (if (or (proof-is-call child *t4-structural-evens*) (proof-is-call child *t4-structural-odds*))
      (proof-with-checked-results ((obj (proof-term-at child 1)))
        (if (not (equal obj parent)) '(:failure "InferenceMismatch" "")
          (proof-with-checked-results
              ((cons (t4-structural-evidence-require evidence (list *proof-consp* (list *library-cdr* parent))))
               (step (t4-structural-structural-split-bound lib (car child) parent (car cons))))
            (list (car step) (cdr step) (t4-structural-evidence-after-library (cdr cons) lib (cdr step))))))
    (t4-structural-structural-count-bound lib child parent evidence t)))

(defun t4-structural-count-descent-rewrite (lib step opened)
  (if (not opened) step
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((reversed (proof-proof-symmetric proof opened))
           (rewritten (proof-proof-rewrite proof step reversed '(1 1 1))))
        (proof-proof-tidy proof rewritten)))))

(defund t4-structural-count-descent-direct (lib child parent larger evidence opened)
  (let* ((count-child (t4-structural-count child))
         (direct-goal (list *proof-ordinal-less* count-child larger)))
    (proof-with-checked-results ((direct (t4-structural-direct-builtin lib (list direct-goal) evidence)))
      (if (car direct)
          (t4-structural-step-with-evidence (t4-structural-count-descent-rewrite lib (car direct) opened)
                                            lib (cdr direct))
        (proof-with-checked-results
            ((bound (t4-structural-count-descent-bound lib child parent (cdr direct)))
             (lib (cadr bound))
             (comparison (library-library-ordinal-comparison lib count-child larger))
             (step (library-inherited proof-proof-transport lib (car bound) comparison)))
          (t4-structural-step-with-evidence (t4-structural-count-descent-rewrite lib step opened)
                                            lib (caddr bound)))))))

(defund t4-structural-count-descent-select (lib evidence child opened)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-term-at child 1))
         (yes (t4-structural-evidence-find evidence test))
         (decision (if (car yes) yes (t4-structural-evidence-find (cdr yes) (proof-neg test)))))
      (if (not (car decision)) (list child opened (cdr decision))
        (proof-with-checked-results
            ((equality (proof-proof-select proof child (car decision)))
             (opened (proof-proof-chain proof opened (list equality)))
             (child (t4-structural-step-term opened 2)))
          (list child opened (cdr decision)))))))

(defund t4-structural-count-descent-open (lib child)
  (proof-with-checked-results
      ((opened (library-inherited proof-proof-simplify lib child nil
                                 (list *termination-return-last* (proof-sym "HARD-ERROR" "ACL2")
                                       (proof-sym "ILLEGAL" "ACL2"))))
       (child (if opened (t4-structural-step-term opened 2) child)))
    (cons child opened)))

(defund t4-structural-count-descent-arguments (goal)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (child (proof-term-at (cadr parts) 1))
       (larger (caddr parts))
       (parent (proof-term-at larger 1)))
    (list child parent larger)))

(defund t4-structural-count-descent-leaf-evidence (lib evidence tests)
  (t4-structural-evidence-init lib (append (t4-structural-evidence-tests evidence) tests)
                              (table-values (t4-structural-evidence-extra evidence))))

(defund t4-structural-count-descent-branches (node)
  (proof-list-of-length (cdr node) 3))

(mutual-recursion
 (defund t4-structural-count-descent-run (n lib goal evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-count-descent-run")
     (proof-with-checked-results ((parts (t4-structural-count-descent-arguments goal)))
       (let ((child (car parts)) (parent (cadr parts)) (larger (caddr parts)))
         (if (proof-is-call child *proof-if*)
             (proof-with-checked-results
                 ((template (list *proof-ordinal-less* (t4-structural-count *proof-result*) larger))
                  (branch (t4-structural-count-descent-visit (1- n) child template lib evidence larger nil)))
               (list (car branch) (cdr branch) (t4-structural-evidence-after-library evidence lib (cdr branch))))
           (proof-with-checked-results ((opened (t4-structural-count-descent-open lib child)))
             (let ((child (car opened)) (opened (cdr opened)))
               (if (and opened (proof-is-call child *proof-if*))
                   (proof-with-checked-results
                       ((selected (t4-structural-count-descent-select lib evidence child opened))
                        (goal (list *proof-ordinal-less* (t4-structural-count (car selected)) larger))
                        (reduced (t4-structural-count-descent-run (1- n) lib goal (caddr selected))))
                     (t4-structural-step-with-evidence
                      (t4-structural-count-descent-rewrite (cadr reduced) (car reduced) (cadr selected))
                      (cadr reduced) (caddr reduced)))
                 (t4-structural-count-descent-direct lib child parent larger evidence opened)))))))))
 (defund t4-structural-count-descent-visit (n node template lib evidence larger tests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-structural-count-descent-visit"))
    ((proof-is-call node *proof-if*)
     (proof-with-checked-results
         ((branches (t4-structural-count-descent-branches node))
          (test (car branches))
          (yes (t4-structural-count-descent-visit (1- n) (cadr branches) template lib evidence larger
                                                  (append tests (list (list test t)))))
          (no (t4-structural-count-descent-visit (1- n) (caddr branches) template (cdr yes) evidence larger
                                                 (append tests (list (list test nil))))))
       (t4-structural-step-with-library
        (library-inherited proof-by-value-join (cdr no) node template (car yes) (car no)) (cdr no))))
    ((and (proof-compound node) (endp node)) '(:failure "MalformedCandidate" ""))
    ((and (proof-compound node) (proof-compound (car node)))
     (proof-with-checked-results
         ((opened (t4-structural-branch-open lib node))
          (step (t4-structural-count-descent-visit (1- n) (car opened) template lib evidence larger tests)))
       (t4-structural-step-with-library
        (t4-structural-branch-lambda-result (cdr step) (car step) (cdr opened) template) (cdr step))))
    (t
     (proof-with-checked-results
         ((leaf (t4-structural-structural-count-descent-leaf (1- n) node tests lib evidence larger)))
       (t4-structural-step-with-library (t4-structural-branch-leaf-check (car leaf) node template) (cdr leaf))))))
 (defund t4-structural-structural-count-descent-leaf (n value tests lib evidence larger)
   (declare (xargs :measure (nfix n)))
   (if (zp n) '(:failure "Fuel" "t4-structural-structural-count-descent-leaf")
     (proof-with-checked-results
         ((branch (t4-structural-count-descent-leaf-evidence lib evidence tests))
          (step (t4-structural-count-descent-run
                 (1- n) lib (list *proof-ordinal-less* (t4-structural-count value) larger) branch)))
       (cons (car step) (cadr step))))))

(defun t4-structural-structural-count-descent (lib goal evidence)
  (t4-structural-count-descent-run 1000000 lib goal evidence))

(defun t4-structural-numeric-descent-bottom (lib child parent evidence)
  (proof-with-checked-results
      ((child-head (proof-term-at child 0))
       (parent-head (proof-term-at parent 0)))
    (cond
     ((and (equal child-head *library-count*) (equal parent-head *library-count*))
      (proof-with-checked-results ((child (proof-term-at child 1)) (parent (proof-term-at parent 1)))
        (t4-structural-structural-count-bound lib child parent evidence t)))
     ((and (equal child-head *library-len*) (equal parent-head *library-len*))
      (proof-with-checked-results ((tail (proof-term-at child 1)) (obj (proof-term-at parent 1)))
        (if (equal tail (list *library-cdr* obj))
            (proof-with-checked-results ((cons (t4-structural-evidence-require evidence (list *proof-consp* obj))))
              (t4-structural-step-with-evidence
               (library-library-cite lib "LEN-CDR-LESS" (list obj) (list (car cons))) lib (cdr cons)))
          '(:failure "SearchMiss" ""))))
     (t '(:failure "SearchMiss" "")))))

(defun t4-structural-numeric-descent-shift (bound offset left-offset)
  (proof-with-checked-results
      ((bound bound)
       (shifted (descent-shift-with-library (cadr bound) (car bound) offset left-offset)))
    (list (car shifted) (cdr shifted) (t4-structural-evidence-after-library (caddr bound) (cadr bound) (cdr shifted)))))

(defund t4-structural-structural-numeric-descent (lib child parent evidence)
  (declare (xargs :measure (acl2-count child)))
  (if (and (consp child) (proof-is-call child *proof-plus*) (proof-is-call parent *proof-plus*))
      (if (endp (cdr child)) '(:failure "MalformedCandidate" "")
        (proof-with-checked-results ((left-parent (proof-term-at parent 1)))
          (if (endp (cddr child)) '(:failure "MalformedCandidate" "")
            (proof-with-checked-results ((right-parent (proof-term-at parent 2)))
              (cond
               ((equal (cadr child) left-parent)
                (t4-structural-numeric-descent-shift
                 (t4-structural-structural-numeric-descent lib (caddr child) right-parent evidence) left-parent t))
               ((equal (caddr child) right-parent)
                (t4-structural-numeric-descent-shift
                 (t4-structural-structural-numeric-descent lib (cadr child) left-parent evidence) right-parent nil))
               (t '(:failure "SearchMiss" "")))))))
    (t4-structural-numeric-descent-bottom lib child parent evidence)))

(defun t4-structural-structural-sum-descent (lib goal evidence)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (child (cadr parts))
       (parent (caddr parts))
       (step (t4-structural-structural-numeric-descent lib child parent evidence))
       (lib (cadr step))
       (comparison (library-library-ordinal-comparison lib child parent)))
    (t4-structural-step-with-evidence (library-inherited proof-proof-transport lib (car step) comparison)
                                      lib (caddr step))))
