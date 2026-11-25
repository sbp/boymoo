(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h4-book-measures-o-finp* (proof-sym "O-FINP" "ACL2"))
(defconst *h4-book-measures-o-rst* (proof-sym "O-RST" "ACL2"))
(defconst *h4-book-measures-o-first-expt* (proof-sym "O-FIRST-EXPT" "ACL2"))
(defconst *h4-book-measures-o-first-coeff* (proof-sym "O-FIRST-COEFF" "ACL2"))
(defconst *h4-book-measures-atom* (proof-cl "ATOM"))
(defconst *h4-book-measures-endp* (proof-cl "ENDP"))
(defconst *h4-book-measures-eq* (proof-cl "EQ"))
(defconst *h4-book-measures-eql* (proof-cl "EQL"))
(defconst *h4-book-measures-num-eq* (proof-cl "="))
(defconst *h4-book-measures-wrappers*
  (list *h4-book-measures-atom* *h4-book-measures-endp* *h4-book-measures-eq*
        *h4-book-measures-eql* *h4-book-measures-num-eq* *h4-book-measures-o-finp*
        (proof-sym "FORCE" "ACL2") (proof-sym "MBT" "ACL2") (proof-sym "POSP" "ACL2")))
(defconst *h4-book-measures-selectors*
  (append *h4-book-measures-wrappers*
          (list *h4-book-measures-o-rst* *h4-book-measures-o-first-expt*
                *h4-book-measures-o-first-coeff* (proof-sym "HARD-ERROR" "ACL2"))))

(defun h4-book-measures-contradiction (proof premise selection negative literal)
  (proof-with-checked-results
   ((positive (proof-proof-transport proof premise selection))
    (contradiction (proof-proof-cut proof positive negative)))
   (proof-proof-front proof contradiction literal)))

(defun h4-book-measures-negative-conditional (proof step conditional)
  (proof-with-checked-results ((parts (proof-list-of-length conditional 4)))
    (let ((test (cadr parts))
          (yes (caddr parts))
          (no (cadddr parts)))
      (cond
       ((or (equal test *proof-true*) (equal test *proof-false*)) nil)
       ((or (equal yes test) (equal yes *proof-true*))
        (proof-with-checked-results
         ((known (if (equal yes *proof-true*)
                     (proof-proof-prove proof *proof-true* nil nil)
                   (proof-proof-assume proof test t)))
          (selection (proof-proof-if-true proof conditional)))
         (h4-book-measures-contradiction proof known selection step (proof-neg test))))
       ((equal no *proof-true*)
        (proof-with-checked-results
         ((known (proof-proof-prove proof *proof-true* nil nil))
          (selection (proof-proof-if-false proof conditional)))
         (h4-book-measures-contradiction proof known selection step test)))
       (t nil)))))

(defun h4-book-measures-negative-consequence (proof step literal)
  (if (proof-is-call literal *proof-not*)
      (proof-with-checked-results ((inner (proof-term-at literal 1)))
        (cond
         ((proof-is-call inner *proof-not*)
          (proof-with-checked-results
           ((term (proof-term-at inner 1))
            (assumption (proof-proof-assume proof term nil))
            (contradiction (proof-proof-cut proof assumption step)))
           (proof-proof-front proof contradiction term)))
         ((proof-is-call inner *proof-if*)
          (h4-book-measures-negative-conditional proof step inner))
         (t nil)))
    nil))

(defun h4-book-measures-conjuncts (p step literal)
  (if (proof-is-call literal *proof-if*)
      (proof-with-checked-results ((tail (proof-term-at literal 3)))
        (and (equal tail *proof-false*) (h4-book-flatten-conjunct p step)))
    nil))

(defun h4-book-measures-enqueue-consequences (p step literal pending)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((conjuncts (h4-book-measures-conjuncts p step literal))
      (negative (h4-book-measures-negative-consequence proof step literal))
      (equality (h4-book-flatten-normalize p literal nil *h4-book-measures-wrappers* nil))
      (reduced (h4-book-flatten-step-right equality))
      (rewritten (if (equal reduced literal) nil (proof-proof-rewrite proof step equality '(1)))))
     (append (and rewritten (list rewritten))
             (and negative (list negative))
             (reverse conjuncts)
             pending))))

(defun h4-book-measures-select-evidence (proof literal step evidence selected)
  (let ((negative (proof-is-call literal *proof-not*)))
    (proof-with-checked-results
     ((conditional (if negative (proof-term-at literal 1) literal)))
     (if (and (not (member-equal literal selected)) (proof-is-call conditional *proof-if*))
         (proof-with-checked-results ((test (proof-term-at conditional 1)))
           (let ((known (or (table-get evidence test nil)
                            (table-get evidence (proof-neg test) nil))))
             (and known
                  (proof-with-checked-results
                   ((selection (proof-proof-select proof conditional known)))
                   (proof-proof-rewrite proof step selection
                                        (if negative '(1 1) '(1)))))))
       nil))))

(defun h4-book-measures-enqueue-selected (proof entries evidence pending selected)
  (if (endp entries)
      (cons pending selected)
    (let ((literal (caar entries))
          (step (cdar entries)))
      (proof-with-checked-results
       ((rewritten (h4-book-measures-select-evidence proof literal step evidence selected)))
       (h4-book-measures-enqueue-selected proof (cdr entries) evidence
                                          (if rewritten (cons rewritten pending) pending)
                                          (if rewritten (cons literal selected) selected))))))

(defun h4-book-measures-expand-next (p pending evidence selected)
  (if (consp pending)
    (let ((step (car pending)))
      (proof-with-checked-results ((literal (proof-step-first step)))
        (if (assoc-equal literal evidence)
            (list :more (cdr pending) evidence selected)
          (proof-with-checked-results
           ((next (h4-book-measures-enqueue-consequences p step literal (cdr pending))))
           (list :more next (table-put evidence literal step) selected)))))
    (proof-with-checked-results
     ((next (h4-book-measures-enqueue-selected (library-library-proof p) evidence
                                              evidence nil selected)))
     (if (car next)
         (list :more (car next) evidence (cdr next))
       (list :done (table-values evidence))))))

(defun h4-book-measures-expand-pending (n p progress)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-measures-expand-pending"))
   ((eq (car progress) :more)
    (h4-book-measures-expand-pending
     (1- n) p (h4-book-measures-expand-next p (cadr progress) (caddr progress) (cadddr progress))))
   ((eq (car progress) :done) (cadr progress))
   (t progress)))

(defun h4-book-measures-expand-evidence (p premises)
  (h4-book-measures-expand-pending 1000000 p (list :more (reverse premises) nil nil)))

(defun h4-book-measures-assume-tests (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
     ((test (proof-list-of-length (car tests) 2))
      (step (proof-proof-assume proof (car test) (cadr test)))
      (rest (h4-book-measures-assume-tests proof (cdr tests))))
     (cons step rest))))

(defun h4-book-measures-rule-tests (p tests)
  (proof-with-checked-results
   ((premises (h4-book-measures-assume-tests (library-library-proof p) tests)))
   (h4-book-measures-expand-evidence p premises)))

(defun h4-book-measures-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((head (proof-term-at (car definitions) 0))
      (rest (h4-book-measures-definition-names (cdr definitions))))
     (cons head rest))))

(defun h4-book-measures-ordinal-aids (aids)
  (if (endp aids)
      nil
    (proof-with-checked-results
     ((aid (proof-list-of-length (car aids) 2))
      (rest (h4-book-measures-ordinal-aids (cdr aids))))
     (if (equal (cadr aid) *proof-ordinal-less*) (cons (car aid) rest) rest))))

(defun h4-book-measures-saved-axes (names aids)
  (if (endp names)
      nil
    (proof-with-checked-results
     ((axis (h4-book-measures-ordinal-aids (table-get aids (car names) nil)))
      (rest (h4-book-measures-saved-axes (cdr names) aids)))
     (cons axis rest))))

(defun h4-book-measures-prepend-measure (measure plans)
  (if (endp plans)
      nil
    (cons (cons measure (car plans))
          (h4-book-measures-prepend-measure measure (cdr plans)))))

(defun h4-book-measures-product-axis (axis tails)
  (if (or (endp axis) (endp tails))
      nil
    (append (h4-book-measures-prepend-measure (car axis) tails)
            (h4-book-measures-product-axis (cdr axis) tails))))

(defun h4-book-measures-product (axes)
  (cond ((endp axes) (list nil))
        ((endp (car axes)) nil)
        (t (h4-book-measures-product-axis (car axes)
                                         (h4-book-measures-product (cdr axes))))))

(defun h4-book-measures-structural-plan (names structural)
  (if (endp names)
      nil
    (let ((variable (assoc-equal (car names) structural)))
      (if variable
          (proof-with-checked-results
           ((rest (h4-book-measures-structural-plan (cdr names) structural)))
           (cons (list *library-count* (cdr variable)) rest))
        '(:failure "failure" "")))))

(defun h4-book-measures-formal-plans (formals)
  (if (endp formals)
      nil
    (cons (list (list *library-count* (car formals)))
          (h4-book-measures-formal-plans (cdr formals)))))

(defun h4-book-measures-measure-plans (definitions calls aids)
  (proof-with-checked-results
   ((names (h4-book-measures-definition-names definitions))
    (saved (h4-book-measures-saved-axes names aids))
    (plans (h4-book-measures-product saved))
    (structural (termination-selector-plan definitions calls))
    (structural-plan (and structural (h4-book-measures-structural-plan names structural)))
    (formals (if (= (len names) 1) (proof-term-at (car definitions) 1) nil)))
   (append plans (and structural (list structural-plan))
           (h4-book-measures-formal-plans formals))))

(mutual-recursion
 (defun h4-book-measures-well-formed-measure (term formals functions)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) (and (member-equal term formals) t))
    ((proof-is-call term *proof-quote*) t)
    ((endp term) '(:failure "failure" ""))
    (t
     (let ((head (car term)))
       (proof-with-checked-results
        ((good-head (cond ((not (proof-compound head)) (member-equal head functions))
                         ((consp (cddr head))
                          (h4-book-measures-well-formed-measure (caddr head)
                                                                (cadr head) functions))
                         (t '(:failure "failure" "")))))
        (and good-head (h4-book-measures-well-formed-arguments (cdr term) formals functions)))))))

 (defun h4-book-measures-well-formed-arguments (terms formals functions)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       t
     (proof-with-checked-results
      ((good (h4-book-measures-well-formed-measure (car terms) formals functions)))
      (and good (h4-book-measures-well-formed-arguments (cdr terms) formals functions))))))

(defun h4-book-measures-hypotheses-put-new (context term step)
  (let ((found (descent-hypotheses-found context)))
    (if (assoc-equal term found)
        context
      (descent-hypotheses-with-found context (table-put found term step)))))

(defun h4-book-measures-find-conjunct (prefix tail term step p context)
  (if (endp prefix)
      (let ((context (h4-book-measures-hypotheses-put-new context tail step)))
        (cons (table-get (descent-hypotheses-found context) term nil) context))
    (proof-with-checked-results ((parts (h4-book-flatten-conjunct p step)))
      (let* ((conjunct (car prefix))
             (context (h4-book-measures-hypotheses-put-new context conjunct (car parts))))
        (if (equal term conjunct)
            (cons (table-get (descent-hypotheses-found context) term nil) context)
          (h4-book-measures-find-conjunct (cdr prefix) tail term (cadr parts) p context))))))

(defun h4-book-measures-find-in-test (term p context test)
  (let* ((proof (library-library-proof p))
         (literal (car test))
         (holds (cadr test)))
    (cond
     ((equal term (if holds literal (proof-neg literal)))
      (proof-with-checked-results ((step (proof-proof-assume proof literal holds)))
        (cons step (h4-book-measures-hypotheses-put-new context term step))))
     ((not holds) nil)
     (t
      (proof-with-checked-results ((parts (descent-conjuncts literal nil)))
        (let ((prefix (car parts))
              (tail (cdr parts)))
          (and (or (member-equal term prefix) (equal term tail))
               (proof-with-checked-results
                ((step (proof-proof-assume proof literal t)))
                (h4-book-measures-find-conjunct prefix tail term step p context)))))))))

(defun h4-book-measures-find-tests (tests term p context)
  (if (endp tests)
      (cons nil context)
    (proof-with-checked-results
     ((test (proof-list-of-length (car tests) 2))
      (match (h4-book-measures-find-in-test term p context test)))
     (or match (h4-book-measures-find-tests (cdr tests) term p context)))))

(defun h4-book-measures-hypotheses-find (context term)
  (let ((known (or (assoc-equal term (descent-hypotheses-extra context))
                   (assoc-equal term (descent-hypotheses-found context)))))
    (if known
        (cons (cdr known) context)
      (h4-book-measures-find-tests (descent-hypotheses-tests context)
                                   term (descent-hypotheses-proof context) context))))

(defun h4-book-measures-hypotheses-require (context term)
  (proof-with-checked-results
   ((result (h4-book-measures-hypotheses-find context term)))
   (if (car result) (car result) (descent-missing-hypothesis term))))

(defun h4-book-measures-simplify-term (proof definitions frames term)
  (let ((head (proof-datum-head term)))
    (cond
     ((or (not (proof-compound term)) (equal head *proof-quote*))
      (list :result frames nil))
     ((endp term) '(:failure "missing-term-part" ""))
     ((or (proof-compound head) (member-equal head definitions))
      (proof-with-checked-results ((expanded (proof-simplify-expansion proof term)))
        (list :term (cons (list :chain (car expanded)) frames) (cadr expanded))))
     ((equal head *proof-if*)
      (proof-with-checked-results ((test (proof-term-at term 1)))
        (list :term (cons (list :if term) frames) test)))
     (t (list :arguments frames term (cdr term) 1 nil)))))

(defun h4-book-measures-simplify-arguments (proof frames term args index simplified)
  (if (endp args)
      (proof-with-checked-results
       ((current (if simplified (h4-book-flatten-step-right simplified) term))
        (constant (h4-association-constant proof current))
        (result (cond ((not constant) simplified)
                      (simplified (proof-proof-chain proof simplified (list constant)))
                      (t constant))))
       (list :result frames result))
    (list :term (cons (list :argument term (cdr args) index simplified) frames)
          (car args))))

(defun h4-book-measures-simplify-result (proof evidence frames step)
  (if (endp frames)
      (cons :done step)
    (let ((frame (car frames))
          (frames (cdr frames)))
      (case (car frame)
        (:chain
         (proof-with-checked-results
          ((step (proof-proof-chain proof (cadr frame) (list step))))
          (list :result frames step)))
        (:if
         (proof-with-checked-results ((path (proof-simplify-if-path proof (cadr frame) step evidence)))
           (if (eq (car path) :simplify)
               (list :term (cons (list :chain (cadr path)) frames) (caddr path))
             (list :result frames path))))
        (:argument
         (let ((term (cadr frame))
               (args (caddr frame))
               (index (cadddr frame))
               (simplified (nth 4 frame)))
           (proof-with-checked-results
            ((next (proof-simplify-argument-result proof term index simplified step)))
            (list :arguments frames term args (1+ index) next))))
        (otherwise '(:failure "inapplicable-term" ""))))))

(defun h4-book-measures-simplify-next (proof evidence definitions work)
  (let ((frames (cadr work))
        (args (cddr work)))
    (case (car work)
      (:term (h4-book-measures-simplify-term proof definitions frames (car args)))
      (:arguments (h4-book-measures-simplify-arguments
                   proof frames (car args) (cadr args) (caddr args) (cadddr args)))
      (:result (h4-book-measures-simplify-result proof evidence frames (car args)))
      (otherwise '(:failure "inapplicable-term" "")))))

(defun h4-book-measures-simplify-visit (n proof evidence definitions work)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-measures-simplify-visit"))
   ((eq (car work) :done) (cdr work))
   ((failure-p work) work)
   (t (h4-book-measures-simplify-visit
       (1- n) proof evidence definitions (h4-book-measures-simplify-next
                                          proof evidence definitions work)))))

(defun h4-book-measures-simplify (proof term evidence definitions)
  (h4-book-measures-simplify-visit 1000000 proof evidence definitions (list :term nil term)))

(defun h4-book-measures-simplify-first (proof step evidence definitions)
  (proof-with-checked-results
   ((literal (proof-step-first step))
    (equality (h4-book-measures-simplify proof literal evidence definitions)))
   (if equality
       (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
         (proof-proof-tidy proof rewritten))
     step)))

(defun h4-book-measures-prove-step (proof term evidence definitions)
  (if (equal term *proof-true*)
      (proof-proof-prove proof term evidence definitions)
    (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
      (if premise
          premise
        (proof-with-checked-results
         ((equality (h4-book-measures-simplify proof term evidence definitions))
          (right (and equality (h4-book-flatten-step-right equality))))
         (cond ((or (not equality) (equal right term))
                (proof-prove-unproved-term term))
               ((equal right *proof-true*)
                (proof-proof-true-from-eq proof equality))
               (t (list :transport right equality))))))))

(defun h4-book-measures-prove-visit (n proof evidence definitions result)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-measures-prove-visit"))
   ((eq (car result) :transport)
    (proof-with-checked-results
     ((step (h4-book-measures-prove-visit
             (1- n) proof evidence definitions
             (h4-book-measures-prove-step proof (cadr result) evidence definitions))))
     (proof-proof-transport proof step (caddr result))))
   (t result)))

(defun h4-book-measures-prove (proof term evidence definitions)
  (h4-book-measures-prove-visit 1000000 proof evidence definitions
                                (h4-book-measures-prove-step proof term evidence definitions)))

(mutual-recursion
 (defun h4-book-measures-natural (p term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *library-count*)
     (library-library-cite p "COUNT-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-len*)
     (library-library-cite p "LEN-NATURAL" (cdr term) nil))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results ((steps (h4-book-measures-natural-arguments p (cdr term))))
       (library-library-cite p "NATURAL-SUM" (cdr term) steps)))
    (t (h4-book-measures-prove (library-library-proof p) (list *library-natp* term)
                               nil (list *library-natp* *proof-not*)))))

 (defun h4-book-measures-natural-arguments (p args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((first (h4-book-measures-natural p (car args)))
       (rest (h4-book-measures-natural-arguments p (cdr args))))
      (cons first rest)))))

(defun h4-book-measures-measure-ordinal (p measure)
  (proof-with-checked-results
   ((builtin (descent-direct-builtin p (list (list *proof-ordinalp* measure)) nil)))
   (or (car builtin)
       (proof-with-checked-results ((head (proof-term-at measure 0)))
         (if (equal head *library-gap*)
             (library-library-cite p "GAP-ORDINAL" (cdr measure) nil)
           (proof-with-checked-results ((natural (h4-book-measures-natural p measure)))
             (library-library-cite p "NATURAL-ORDINAL" (list measure) (list natural))))))))

(defun h4-book-measures-selector-query (p goal context replies)
  (let ((proof (library-library-proof p)))
    (descent-let*
     ((parts (proof-list-of-length goal 3))
      (child-head (proof-term-at (cadr parts) 0))
      (parent-head (proof-term-at (caddr parts) 0)))
     (if (and (equal child-head *library-count*) (equal parent-head *library-count*))
         (descent-let*
          ((raw (proof-term-at (cadr parts) 1))
           (opened (h4-book-measures-simplify proof raw nil (list *termination-return-last*)))
           (actual (if opened (h4-book-flatten-step-right opened) raw))
           (result (descent-selector-step p actual (caddr parts) context replies)))
          (if opened
              (descent-let*
               ((reversed (proof-proof-symmetric proof opened))
                (rewritten (proof-proof-rewrite proof (car result) reversed '(1 1 1)))
                (step (proof-proof-tidy proof rewritten)))
               (cons step (cdr result)))
            result))
       '(:failure "inapplicable-step" "")))))

(defun h4-book-measures-descent-next (recipe p args initial context replies)
  (proof-with-checked-results
   ((result (if (eq recipe :selector-decrease)
                (h4-book-measures-selector-query p (car args) initial replies)
              (descent-query-recipe recipe p args initial replies))))
    (if (descent-request-p result)
        (let ((term (descent-request-term result)))
          (proof-with-checked-results
           ((reply (h4-book-measures-hypotheses-find context term)))
           (list :more (cdr reply) (table-put replies term (cons (car reply) nil)))))
      (cons :done (cons (car result) context)))))

(defun h4-book-measures-descent-replies (n recipe p args initial progress)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-measures-descent-replies"))
   ((eq (car progress) :more)
    (h4-book-measures-descent-replies
     (1- n) recipe p args initial
     (h4-book-measures-descent-next recipe p args initial (cadr progress) (caddr progress))))
   ((eq (car progress) :done) (cdr progress))
   (t progress)))

(defun h4-book-measures-descent (recipe p args context)
  (proof-with-checked-results ((initial (descent-hypotheses-init p nil nil)))
    (h4-book-measures-descent-replies 1000000 recipe p args initial (list :more context nil))))

(defun h4-book-measures-selector-decrease (p goal context)
  (h4-book-measures-descent :selector-decrease p (list goal) context))

(defun h4-book-measures-count-nil (p smaller original context)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((x (proof-term-at original 1))
      (builtin-step (library-library-builtin p 3 x))
      (shape (h4-book-measures-hypotheses-require context (list *proof-consp* x)))
      (descent (proof-proof-discharge proof builtin-step shape))
      (child (list *library-count* (list *library-cdr* x)))
      (order (library-library-ordinal-comparison p child original))
      (strict (proof-proof-rewrite proof descent order '(1)))
      (natural (h4-book-measures-natural p child))
      (weak (library-library-cite p "NATURAL-NONNEGATIVE" (list child) (list natural)))
      (lower (library-library-compare-chain p weak strict))
      (reduced (h4-book-flatten-normalize p smaller nil (list *library-count*) nil))
      (lower (library-library-transport-argument p lower reduced 1))
      (order (library-library-ordinal-comparison p smaller original)))
     (proof-proof-transport proof lower order))))

(defun h4-book-measures-count-decrease (p goal smaller original context)
  (proof-with-checked-results
   ((child (proof-term-at smaller 1))
    (head (if (proof-compound child) (proof-term-at child 0) nil)))
   (cond ((member-equal head (list *library-car* *library-cdr*))
          (proof-with-checked-results
           ((result (h4-book-measures-selector-decrease p goal context)))
           (car result)))
         ((equal child *proof-false*) (h4-book-measures-count-nil p smaller original context))
         (t '(:failure "unproved" "")))))

(defun h4-book-measures-len-decrease (p smaller original context)
  (proof-with-checked-results
   ((child (proof-term-at smaller 1))
    (parent (proof-term-at original 1)))
   (if (equal child (list *library-cdr* parent))
       (proof-with-checked-results
        ((shape (h4-book-measures-hypotheses-require context (list *proof-consp* parent)))
         (less (library-library-cite p "LEN-CDR-LESS" (cdr original) (list shape)))
         (order (library-library-ordinal-comparison p smaller original)))
        (proof-proof-transport (library-library-proof p) less order))
     '(:failure "unproved" ""))))

(defun h4-book-measures-structural-decrease (p goal context)
  (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
    (let ((smaller (cadr parts))
          (original (caddr parts)))
      (cond
       ((and (proof-is-call smaller *library-count*) (proof-is-call original *library-count*))
        (h4-book-measures-count-decrease p goal smaller original context))
       ((and (proof-is-call smaller *library-len*) (proof-is-call original *library-len*))
        (h4-book-measures-len-decrease p smaller original context))
       (t '(:failure "unproved" ""))))))

(defun h4-book-measures-split-term (goal splits)
  (if (or (not splits) (equal splits 0))
      nil
    (proof-with-checked-results ((child (proof-term-at goal 1)))
      (and (proof-is-call child *library-count*)
           (proof-with-checked-results ((value (proof-term-at child 1)))
             (and (proof-is-call value *proof-if*) value))))))

(defun h4-book-measures-prove-reduced (p new-clause new-goal context)
  (proof-with-checked-results ((known (h4-book-measures-hypotheses-find context new-goal)))
    (if (car known)
        (car known)
      (proof-with-checked-results
       ((direct (h4-book-measures-descent :direct-builtin p (list new-clause) (cdr known))))
       (or (car direct) (h4-book-measures-structural-decrease p new-goal (cdr direct)))))))

(defun h4-book-measures-decrease-with-evidence (p clause evidence context splits)
  (let* ((proof (library-library-proof p))
         (goal (car (last clause)))
         (expand (append *h4-book-measures-selectors* (list (proof-sym "THE-CHECK" "ACL2")))))
    (proof-with-checked-results
     ((reduced (h4-book-flatten-normalize p goal evidence expand nil))
      (new-goal (h4-book-flatten-step-right reduced))
      (split (h4-book-measures-split-term new-goal splits)))
     (if split
         (proof-with-checked-results ((test (proof-term-at split 1)))
           (cons :split test))
       (proof-with-checked-results
        ((step (h4-book-measures-prove-reduced
                p (append (butlast clause 1) (list new-goal)) new-goal context))
         (step (if (equal new-goal goal) step (proof-proof-transport proof step reduced))))
        (cons :done step))))))

(defun h4-book-measures-decrease-prepare (p clause tests splits)
  (proof-with-checked-results
   ((context (descent-hypotheses-init p tests nil))
    (direct (h4-book-measures-descent :direct-builtin p (list clause) context)))
   (if (car direct)
       (cons :done (car direct))
     (proof-with-checked-results
      ((evidence (h4-book-measures-rule-tests p tests))
       (context (descent-hypotheses-init p tests evidence))
       (direct (h4-book-measures-descent :direct-builtin p (list clause) context)))
      (if (car direct)
          (cons :done (car direct))
        (h4-book-measures-decrease-with-evidence p clause evidence (cdr direct) splits))))))

(defun h4-book-measures-decrease-prepare-branch (p clause tests splits test holds)
  (proof-with-checked-results
   ((assumed (proof-proof-assume (library-library-proof p) test holds)))
   (h4-book-measures-decrease-prepare p clause tests splits)))

(defun h4-book-measures-decrease-search (n p clause tests splits progress)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-measures-decrease-search"))
   ((eq (car progress) :done) (cdr progress))
   ((eq (car progress) :split)
    (let* ((test (cdr progress))
           (less-splits (1- (if (eq splits t) 1 splits)))
           (yes-tests (append tests (list (list test t))))
           (no-tests (append tests (list (list test nil)))))
      (proof-with-checked-results
       ((yes (h4-book-measures-decrease-search
              (1- n) p clause yes-tests less-splits
              (h4-book-measures-decrease-prepare-branch p clause yes-tests less-splits test t)))
        (no (h4-book-measures-decrease-search
             (1- n) p clause no-tests less-splits
             (h4-book-measures-decrease-prepare-branch p clause no-tests less-splits test nil))))
       (h4-book-flatten-case-of p (car (last clause)) test yes no))))
   (t progress)))

(defun h4-book-measures-decrease (p clause tests splits)
  (h4-book-measures-decrease-search 1000000 p clause tests splits
                                    (h4-book-measures-decrease-prepare p clause tests splits)))

(defun h4-book-measures-plan-well-formed (definitions plan functions)
  (if (or (endp definitions) (endp plan))
      t
    (proof-with-checked-results
     ((formals (proof-term-at (car definitions) 1))
      (good (h4-book-measures-well-formed-measure (car plan) formals functions)))
     (and good (h4-book-measures-plan-well-formed (cdr definitions) (cdr plan) functions)))))

(defun h4-book-measures-plan-error (failure last-call)
  (if (member-equal (cadr failure)
                    '("unproved" "inapplicable-term" "inapplicable-step"
                      "missing-proof-input" "missing-term-part"
                      "value" "assertion" "key" "index"))
      (if (eq last-call :unbound)
          '(:failure "failure" "")
        (list :retry last-call))
    failure))

(defun h4-book-measures-ordinality (p clause)
  (proof-with-checked-results
   ((term (proof-term-at (car clause) 1))
    (step (h4-book-flatten-fact-instance p (list *proof-ordinalp* term) nil :none nil)))
   (or step (h4-book-measures-measure-ordinal p term))))

(defun h4-book-measures-store-proof (p clause call proofs)
  (if (assoc-equal clause proofs)
      proofs
    (proof-with-checked-results
     ((step (if call
                (h4-book-measures-decrease p clause (termination-call-tests call) 2)
              (h4-book-measures-ordinality p clause)))
      (subsumed (proof-proof-subsume (library-library-proof p) step clause)))
     (table-put proofs clause subsumed))))

(defun h4-book-measures-prove-entry (p entry progress)
  (if (failure-p entry)
      (h4-book-measures-plan-error entry (caddr progress))
    (let* ((clause (caar entry))
           (call (cadar entry))
           (proofs (h4-book-measures-store-proof p clause call (cadr progress))))
      (if (failure-p proofs)
          (h4-book-measures-plan-error proofs call)
        (list :more proofs call)))))

(defun h4-book-measures-prove-calls (p calls measures formals progress)
  (declare (xargs :measure (acl2-count calls)))
  (cond
   ((not (eq (car progress) :more)) progress)
   ((endp calls) (list :success (table-values (cadr progress))))
   (t (h4-book-measures-prove-calls
       p (cdr calls) measures formals
       (h4-book-measures-prove-entry p (termination-call-cases (list (car calls)) measures formals)
                                     progress)))))

(defun h4-book-measures-prove-ordinalities (p definitions calls measures formals progress)
  (declare (xargs :measure (acl2-count definitions)))
  (cond
   ((not (eq (car progress) :more)) progress)
   ((endp definitions) (h4-book-measures-prove-calls p calls measures formals progress))
   (t (h4-book-measures-prove-ordinalities
       p (cdr definitions) calls measures formals
       (h4-book-measures-prove-entry p (termination-ordinality-cases (list (car definitions))
                                                                    measures)
                                     progress)))))

(defun h4-book-measures-prove-plan (p definitions calls measures last-call)
  (let ((formals (termination-formals definitions nil nil)))
    (if (failure-p formals)
        (h4-book-measures-plan-error formals last-call)
      (h4-book-measures-prove-ordinalities p definitions calls measures formals
                                           (list :more nil last-call)))))

(defun h4-book-measures-try-one-plan (p definitions calls functions names plan progress)
  (proof-with-checked-results
   ((good (h4-book-measures-plan-well-formed definitions plan functions)))
   (if (not good)
       progress
     (proof-with-checked-results
      ((result (h4-book-measures-prove-plan
                p definitions calls (h4-book-flatten-binding-map (seq-zip names plan) nil)
                (cadr progress))))
      (if (eq (car result) :success)
          (list :done plan (cadr result))
        (cons :more (cdr result)))))))

(defun h4-book-measures-try-plans (p definitions calls functions names plans progress)
  (declare (xargs :measure (acl2-count plans)))
  (cond
   ((eq (car progress) :done) (cdr progress))
   ((not (eq (car progress) :more)) progress)
   ((endp plans) '(:failure "unproved" ""))
   (t (h4-book-measures-try-plans
       p definitions calls functions names (cdr plans)
       (h4-book-measures-try-one-plan p definitions calls functions names (car plans) progress)))))

(defun h4-book-measures-termination-proof (p definitions calls aids book-functions)
  (let* ((proof (library-library-proof p))
         (functions (append (table-keys (proof-proof-definitions proof))
                            (proof-proof-primitives proof)
                            book-functions)))
    (proof-with-checked-results
     ((plans (h4-book-measures-measure-plans definitions calls aids))
      (names (h4-book-measures-definition-names definitions)))
     (h4-book-measures-try-plans p definitions calls functions names (proof-unique plans)
                                 (list :more :unbound)))))
