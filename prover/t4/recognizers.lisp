(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-recognizers-atom* (proof-cl "ATOM"))
(defconst *t4-recognizers-endp* (proof-cl "ENDP"))
(defconst *t4-recognizers-eq* (proof-cl "EQ"))

(defmacro t4-recognizers-with-results (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings))
          (value (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,value) (eq (car ,value) :t4-request))
             ,value
           (t4-recognizers-with-results ,(cdr bindings) ,body))))))

(defun t4-recognizers-prove (lib term evidence definitions replies)
  (cond
   ((eq replies :ordinals)
    (proof-with-checked-results
     ((result (t4-ordinals-ordinals-prove lib term evidence definitions)))
     (list (car result) (cdr result) replies)))
   ((endp replies)
    (list :t4-request :prove (list term evidence definitions) lib))
   ((failure-p (car replies)) (car replies))
   (t (list (caar replies) (cdar replies) (cdr replies)))))

(defun t4-recognizers-branch-view (equation positive lib shape replies)
  (let ((proof (library-library-proof lib)))
    (t4-recognizers-with-results
     ((literal (proof-step-first equation))
      (body (proof-term-at literal 2))
      (test (proof-term-at body 1))
      (assumed (proof-proof-assume proof shape positive))
      (evidence (if (equal test shape)
                    (list assumed lib replies)
                  (t4-recognizers-prove
                   lib (if positive (proof-neg test) test) (list assumed)
                   (list *t4-recognizers-atom* *t4-recognizers-endp* *proof-not*) replies)))
      (lib (cadr evidence))
      (proof (library-library-proof lib))
      (selected (proof-proof-select proof body (car evidence)))
      (step (proof-proof-chain proof equation (list selected))))
     (list step lib (caddr evidence)))))

(defun t4-recognizers-recognizer-implication-branch-view
    (equation positive lib shape)
  (proof-with-checked-results
   ((result (t4-recognizers-branch-view equation positive lib shape :ordinals)))
   (car result)))

(defun t4-recognizers-recursive-call-p (term recursive)
  (and (proof-compound term)
       (equal (len term) 2)
       (if (member-equal (car term) recursive) t nil)))

(defun t4-recognizers-supported-body-p (equation shape obj)
  (proof-with-checked-results
   ((literal (proof-step-first equation))
    (body (proof-term-at literal 2)))
   (and (proof-is-call body *proof-if*)
        (proof-with-checked-results ((test (proof-term-at body 1)))
          (if (member-equal test (list shape
                                      (list *t4-recognizers-atom* obj)
                                      (list *t4-recognizers-endp* obj)))
              t
            nil)))))

(defun t4-recognizers-steps-by-first (steps facts)
  (if (endp steps)
      facts
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (t4-recognizers-steps-by-first (cdr steps)
                                    (table-put facts literal (car steps))))))

(defun t4-recognizers-extend-facts-from-body (proof first view body facts)
  (if (not (proof-is-call body *proof-if*))
      facts
    (proof-with-checked-results ((test (proof-term-at body 1)))
      (let ((test-step (assoc-equal test facts)))
        (if (not test-step)
            facts
          (proof-with-checked-results ((yes (proof-term-at body 2)))
            (let ((yes-step (assoc-equal yes facts)))
              (if (not yes-step)
                  facts
                (proof-with-checked-results
                 ((selected (proof-proof-select proof body (cdr test-step)))
                  (branch (proof-proof-chain proof view (list selected)))
                  (known (proof-proof-transport proof (cdr yes-step) branch)))
                 (table-put facts first known))))))))))

(defun t4-recognizers-extend-facts (proof expected facts)
  (if (not (proof-is-call expected *proof-if*))
      facts
    (proof-with-checked-results ((otherwise-term (proof-term-at expected 3)))
      (if (not (equal otherwise-term *proof-false*))
          facts
        (let ((first (cadr expected)))
          (if (not (proof-compound first))
              facts
            (proof-with-checked-results ((head (proof-term-at first 0)))
              (if (or (not (assoc-equal head (proof-proof-definitions proof)))
                      (assoc-equal first facts))
                  facts
                (proof-with-checked-results
                 ((view (proof-proof-unfold proof first))
                  (literal (proof-step-first view))
                  (body (proof-term-at literal 2)))
                 (t4-recognizers-extend-facts-from-body
                  proof first view body facts))))))))))

(defun t4-recognizers-cons-case
    (lib formula rhs obj bindings source-tail facts replies)
  (let ((proof (library-library-proof lib)))
    (t4-recognizers-with-results
     ((decrease (library-library-builtin lib 3 obj))
      (decrease-test (proof-step-first decrease))
      (instance (proof-subst formula (list (cons obj (cadar bindings)))))
      (condition (proof-ite decrease-test instance *proof-true*))
      (assumption (proof-proof-assume proof condition t))
      (smaller (proof-proof-prove-if proof assumption decrease))
      (target-tail (proof-proof-modus-ponens proof smaller source-tail))
      (literal (proof-step-first rhs))
      (expected (proof-term-at literal 2))
      (facts (t4-recognizers-extend-facts proof expected facts))
      (proved (t4-recognizers-prove
               lib expected (append (table-values facts) (list target-tail)) nil replies))
      (lib (cadr proved))
      (step (proof-proof-transport (library-library-proof lib) (car proved) rhs)))
     (list step lib (caddr proved)))))

(defun t4-recognizers-from-atom (proof left lhs obj)
  (proof-with-checked-results
   ((assumed (proof-proof-assume proof left t))
    (from-atom (proof-proof-rewrite proof assumed lhs '(1)))
    (literal (proof-step-first from-atom))
    (from-atom (if (proof-is-call literal *t4-recognizers-eq*)
                   (proof-with-checked-results ((opened (proof-proof-unfold proof literal)))
                     (proof-proof-rewrite proof from-atom opened '(1)))
                 from-atom))
    (literal (proof-step-first from-atom)))
   (if (equal literal (proof-neg obj))
       (proof-with-checked-results
        ((nil-or-true (proof-proof-nil-or-true proof obj))
         (front (proof-proof-front proof nil-or-true obj)))
        (proof-proof-cut proof front from-atom))
     from-atom)))

(defun t4-recognizers-atom-case (lib left lhs rhs obj replies)
  (let ((proof (library-library-proof lib)))
    (t4-recognizers-with-results
     ((from-atom (t4-recognizers-from-atom proof left lhs obj))
      (literal (proof-step-first from-atom)))
     (if (not (equal literal (proof-eq obj *proof-false*)))
         (list nil lib replies)
       (t4-recognizers-with-results
        ((right-literal (proof-step-first rhs))
         (right (proof-term-at right-literal 2))
         (reflexive (proof-proof-reflexive proof right))
         (on-nil (proof-proof-rewrite-result proof reflexive from-atom
                                            (proof-eq *proof-true* right) obj))
         (on-nil-literal (proof-step-first on-nil))
         (goal (proof-term-at on-nil-literal 2))
         (empty (t4-recognizers-prove
                 lib goal nil (list *t4-recognizers-eq* *proof-not*
                                    *t4-recognizers-atom* *t4-recognizers-endp*) replies))
         (lib (cadr empty))
         (proof (library-library-proof lib))
         (transported (proof-proof-transport proof (car empty) on-nil))
         (step (proof-proof-transport proof transported rhs)))
        (list step lib (caddr empty)))))))

(defun t4-recognizers-implication-cases (lib formula left obj shape opened-left opened-right replies)
  (t4-recognizers-with-results
   ((lhs (t4-recognizers-branch-view opened-left t lib shape replies))
    (rhs (t4-recognizers-branch-view opened-right t (cadr lhs) shape (caddr lhs)))
    (lib (cadr rhs))
    (proof (library-library-proof lib))
    (assumed (proof-proof-assume proof left t))
    (reduced (proof-proof-rewrite proof assumed (car lhs) '(1)))
    (pieces (t4-division-pieces lib reduced))
    (facts (t4-recognizers-steps-by-first pieces nil)))
   (let* ((tail (list *library-cdr* obj))
          (source-tail (table-get facts (list (car left) tail) nil))
          (bindings (list (list obj tail))))
     (if (not source-tail)
         (list nil lib (caddr rhs))
       (t4-recognizers-with-results
        ((yes (t4-recognizers-cons-case lib formula (car rhs) obj bindings source-tail facts
                                       (caddr rhs)))
         (lhs (t4-recognizers-branch-view opened-left nil (cadr yes) shape (caddr yes)))
         (rhs (t4-recognizers-branch-view opened-right nil (cadr lhs) shape (caddr lhs)))
         (no (t4-recognizers-atom-case (cadr rhs) left (car lhs) (car rhs) obj (caddr rhs))))
        (if (not (car no))
            no
          (let* ((lib (cadr no))
                 (proof (library-library-proof lib)))
            (proof-with-checked-results
             ((joined (proof-proof-cases proof shape (car yes) (car no)))
              (cases (t4-ordinals-ordinals-imply lib left joined))
              (ordinal (library-library-builtin lib 1 obj))
              (step (proof-proof-induct proof ordinal cases formula
                                        (t4-structural-count obj) (list bindings))))
             (list step lib (caddr no))))))))))

(defun t4-recognizers-opened-implication (lib formula left obj shape opened-left opened-right replies)
  (proof-with-checked-results
   ((left-supported (t4-recognizers-supported-body-p opened-left shape obj))
    (right-supported (and left-supported
                          (t4-recognizers-supported-body-p opened-right shape obj))))
   (if right-supported
       (t4-recognizers-implication-cases lib formula left obj shape opened-left opened-right replies)
     (list nil lib replies))))

(defun t4-recognizers-recognizer-implication-run (lib formula recursive replies)
  (if (not (proof-is-call formula *library-implies*))
      (list nil lib replies)
    (proof-with-checked-results ((terms (proof-list-of-length (cdr formula) 2)))
      (let* ((left (car terms))
             (right (cadr terms))
             (obj (cadr left)))
        (if (and (t4-recognizers-recursive-call-p left recursive)
                 (t4-recognizers-recursive-call-p right recursive)
                 (equal obj (cadr right))
                 (not (proof-compound obj)))
            (let ((proof (library-library-proof lib))
                  (shape (list *proof-consp* obj)))
              (proof-with-checked-results
               ((opened-left (proof-proof-unfold proof left))
                (opened-right (proof-proof-unfold proof right)))
               (t4-recognizers-opened-implication
                lib formula left obj shape opened-left opened-right replies)))
          (list nil lib replies))))))

(defun t4-recognizers-recognizer-implication-with-replies (lib formula recursive replies)
  (t4-recognizers-with-results
   ((result (t4-recognizers-recognizer-implication-run lib formula recursive replies)))
   (cons (car result) (cadr result))))

(defun t4-recognizers-recognizer-implication-with-library (lib formula recursive)
  (t4-recognizers-recognizer-implication-with-replies lib formula recursive :ordinals))

(defun t4-recognizers-recognizer-implication (lib formula recursive)
  (proof-with-checked-results
   ((result (t4-recognizers-recognizer-implication-with-library lib formula recursive)))
   (car result)))
