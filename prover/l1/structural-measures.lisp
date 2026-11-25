(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-structural-measures-atom* (proof-cl "ATOM"))
(defconst *l1-structural-measures-endp* (proof-cl "ENDP"))

(defund l1-structural-measures-find-opposite (hypotheses test)
  (descent-hypotheses-find hypotheses (proof-neg test)))

(defun l1-structural-measures-cons-evidence-tests (proof term goal hypotheses predicates)
  (declare (xargs :measure (acl2-count predicates)))
  (if (endp predicates)
      (cons nil hypotheses)
    (let ((test (list (car predicates) term)))
      (proof-with-checked-results ((opposite (l1-structural-measures-find-opposite hypotheses test)))
        (if (not (car opposite))
            (l1-structural-measures-cons-evidence-tests proof term goal (cdr opposite)
                                                         (cdr predicates))
          (proof-with-checked-results
              ((assumption (proof-proof-assume proof goal nil))
               (atom-case (l1-application-proof-prove proof test (list assumption)
                                                      (list *l1-structural-measures-atom*
                                                            *l1-structural-measures-endp*
                                                            *proof-not*)))
               (cut (proof-proof-cut proof atom-case (car opposite)))
               (step (proof-proof-front proof cut goal)))
            (cons step (cdr opposite))))))))

(defund l1-structural-measures-cons-evidence (proof term hypotheses)
  (let ((goal (list *proof-consp* term)))
    (proof-with-checked-results ((found (descent-hypotheses-find hypotheses goal)))
      (if (car found)
          found
        (l1-structural-measures-cons-evidence-tests proof term goal (cdr found)
          (list *l1-structural-measures-atom* *l1-structural-measures-endp*))))))

(defun l1-structural-measures-selector-path-walk (term bases)
  (declare (xargs :measure (acl2-count term)))
  (cond ((not (proof-compound term)) (list term (reverse bases)))
        ((endp term) '(:failure "failure" ""))
        ((member-equal (car term) (list *library-car* *library-cdr*))
         (if (consp (cdr term))
             (l1-structural-measures-selector-path-walk (cadr term) (cons (cadr term) bases))
           '(:failure "failure" "")))
        (t (list term (reverse bases)))))

(defun l1-structural-measures-selector-path (term)
  (l1-structural-measures-selector-path-walk term nil))

(defun l1-structural-measures-selector-proofs (proof bases hypotheses)
  (declare (xargs :measure (acl2-count bases)))
  (if (endp bases)
      (cons nil hypotheses)
    (proof-with-checked-results
        ((first (l1-structural-measures-cons-evidence proof (car bases) hypotheses))
         (rest (l1-structural-measures-selector-proofs proof (cdr bases) (cdr first))))
      (if (car first)
          (cons (cons (car first) (car rest)) (cdr rest))
        rest))))

(defun l1-structural-measures-selector-hypotheses (proof child parent hypotheses)
  (proof-with-checked-results ((path (l1-structural-measures-selector-path child)))
    (if (not (equal (car path) parent))
        (cons nil hypotheses)
      (proof-with-checked-results
          ((known (l1-structural-measures-selector-proofs proof (cadr path) hypotheses))
           (scoped (and (car known)
                        (descent-hypotheses-init proof (descent-hypotheses-tests hypotheses)
                                                 (car known)))))
        (cons scoped (cdr known))))))

(defund l1-structural-measures-require-table-entry (entries key)
  (let ((entry (assoc-equal key entries)))
    (if entry (cdr entry) '(:failure "failure" ""))))

(defun l1-structural-measures-phase-zero-offsets (functions offsets)
  (declare (xargs :measure (acl2-count functions)))
  (if (endp functions)
      offsets
    (l1-structural-measures-phase-zero-offsets
     (cdr functions) (table-put offsets (car functions) 0))))

(defund l1-structural-measures-phase-offset-pass (edges offsets changed)
  (declare (xargs :measure (acl2-count edges)))
  (if (endp edges)
      (cons offsets changed)
    (proof-with-checked-results
        ((edge (proof-list-of-length (car edges) 3))
         (caller (car edge))
         (callee-offset (l1-structural-measures-require-table-entry offsets (cadr edge)))
         (required (+ callee-offset (if (eq (caddr edge) t) 1 (ifix (caddr edge)))))
         (caller-offset (l1-structural-measures-require-table-entry offsets caller)))
      (if (< caller-offset required)
          (l1-structural-measures-phase-offset-pass
           (cdr edges) (table-put offsets caller required) t)
        (l1-structural-measures-phase-offset-pass (cdr edges) offsets changed)))))

(defun l1-structural-measures-phase-offset-passes (functions edges offsets)
  (declare (xargs :measure (acl2-count functions)))
  (if (endp functions)
      :none
    (proof-with-checked-results
        ((result (l1-structural-measures-phase-offset-pass edges offsets nil)))
      (if (cdr result)
          (l1-structural-measures-phase-offset-passes (cdr functions) edges (car result))
        (car result)))))

(defun l1-structural-measures-phase-offsets (functions edges)
  (l1-structural-measures-phase-offset-passes
   functions edges (l1-structural-measures-phase-zero-offsets functions nil)))

(defun l1-structural-measures-with-phase (count phase)
  (if (and phase (not (equal phase 0)))
      (library-plus (proof-quote phase) count)
    count))

(defun l1-structural-measures-phase-formals (definitions formals)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      formals
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (l1-structural-measures-phase-formals
       (cdr definitions)
       (table-put formals (car definition)
                    (if (equal (cadr definition) *proof-nil*) nil (cadr definition)))))))

(defun l1-structural-measures-phase-candidates (formals)
  (if (endp formals)
      nil
    (cons (cons (caar formals) (seq-range 0 (len (cdar formals)) 1))
          (l1-structural-measures-phase-candidates (cdr formals)))))

(defund l1-structural-measures-phase-actual (actual)
  (proof-with-checked-results ((logical (termination-logical-body actual)))
    (l1-structural-measures-selector-path logical)))

(defund l1-structural-measures-phase-actuals (actuals)
  (if (endp actuals)
      nil
    (proof-with-checked-results
        ((path (l1-structural-measures-phase-actual (car actuals)))
         (rest (l1-structural-measures-phase-actuals (cdr actuals))))
      (cons path rest))))

(defun l1-structural-measures-phase-paths (calls)
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((actuals (l1-structural-measures-phase-actuals (termination-call-actuals (car calls))))
         (rest (l1-structural-measures-phase-paths (cdr calls))))
      (cons (cons (car calls) actuals) rest))))

(defun l1-structural-measures-phase-eligible (actuals formals candidates position)
  (declare (xargs :measure (acl2-count actuals)))
  (if (endp actuals)
      nil
    (let* ((eligible (and (member-equal (caar actuals) formals)
                          (member-equal position candidates)))
           (rest (l1-structural-measures-phase-eligible (cdr actuals) formals candidates
                                                        (1+ position))))
      (if eligible
          (cons position rest)
        rest))))

(defund l1-structural-measures-phase-filter-call (path candidates formals)
  (let* ((call (car path))
         (callee (termination-call-callee call))
         (actuals (cdr path)))
    (proof-with-checked-results
        ((existing (l1-structural-measures-require-table-entry candidates callee))
         (caller-formals (and actuals
                              (l1-structural-measures-require-table-entry formals
                                                              (termination-call-caller call)))))
      (table-put candidates callee
                   (l1-structural-measures-phase-eligible actuals caller-formals existing 0)))))

(defun l1-structural-measures-phase-filter (paths candidates formals)
  (declare (xargs :measure (acl2-count paths)))
  (if (endp paths)
      candidates
    (proof-with-checked-results
        ((candidates (l1-structural-measures-phase-filter-call (car paths) candidates formals)))
      (l1-structural-measures-phase-filter (cdr paths) candidates formals))))

(defun l1-structural-measures-phase-arguments (formals positions)
  (if (endp formals)
      nil
    (proof-with-checked-results
        ((position (l1-structural-measures-require-table-entry positions (caar formals)))
         (argument (proof-term-at (cdar formals) position))
         (rest (l1-structural-measures-phase-arguments (cdr formals) positions)))
      (cons (cons (caar formals) argument) rest))))

(defun l1-structural-measures-phase-edges (paths positions arguments edges)
  (declare (xargs :measure (acl2-count paths)))
  (if (endp paths)
      (reverse edges)
    (let* ((call (caar paths))
           (callee (termination-call-callee call))
           (caller (termination-call-caller call)))
      (proof-with-checked-results
          ((position (l1-structural-measures-require-table-entry positions callee))
           (path (proof-term-at (cdar paths) position))
           (argument (l1-structural-measures-require-table-entry arguments caller)))
        (if (not (equal (car path) argument))
            :none
          (l1-structural-measures-phase-edges
           (cdr paths) positions arguments
           (cons (list caller callee (not (cadr path))) edges)))))))

(defun l1-structural-measures-phase-has-unchanged (edges)
  (and (consp edges)
       (or (caddar edges)
           (l1-structural-measures-phase-has-unchanged (cdr edges)))))

(defun l1-structural-measures-phase-map (arguments offsets)
  (if (endp arguments)
      nil
    (let* ((name (caar arguments))
           (count (list *library-count* (cdar arguments)))
           (phase (table-get offsets name 0)))
      (cons (cons name (l1-structural-measures-with-phase count phase))
            (l1-structural-measures-phase-map (cdr arguments) offsets)))))

(defund l1-structural-measures-phase-assignment (formals paths positions)
  (proof-with-checked-results
      ((arguments (l1-structural-measures-phase-arguments formals positions))
       (edges (l1-structural-measures-phase-edges paths positions arguments nil)))
    (if (not (l1-structural-measures-phase-has-unchanged edges))
        nil
      (proof-with-checked-results
          ((offsets (l1-structural-measures-phase-offsets (table-keys formals) edges)))
        (if (eq offsets :none) nil (l1-structural-measures-phase-map arguments offsets))))))

; The argument positions form a Cartesian product, with the last function varying fastest.
(mutual-recursion
 (defun l1-structural-measures-phase-search (n candidates formals paths positions)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "l1-structural-measures-phase-search"))
         ((endp candidates)
          (l1-structural-measures-phase-assignment formals paths positions))
         (t (l1-structural-measures-phase-search-positions
             (1- n) (caar candidates) (cdar candidates) (cdr candidates)
             formals paths positions))))
 (defun l1-structural-measures-phase-search-positions (n name indices remaining formals paths positions)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "l1-structural-measures-phase-search-positions"))
         ((endp indices) nil)
         (t (let ((found (l1-structural-measures-phase-search
                          (1- n) remaining formals paths (acons name (car indices) positions))))
              (or found
                  (l1-structural-measures-phase-search-positions
                   (1- n) name (cdr indices) remaining formals paths positions)))))))

(defun l1-structural-measures-phase-measures (definitions calls)
  (proof-with-checked-results
      ((formals (l1-structural-measures-phase-formals definitions nil))
       (candidates (l1-structural-measures-phase-candidates formals))
       (paths (l1-structural-measures-phase-paths calls))
       (candidates (l1-structural-measures-phase-filter paths candidates formals)))
    (l1-structural-measures-phase-search 1000000 candidates formals paths nil)))

(defun l1-structural-measures-phased-count (term)
  (cond
   ((proof-is-call term *library-count*)
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (list 0 argument)))
   ((proof-is-call term *proof-plus*)
    (proof-with-checked-results ((phase (proof-term-at term 1)))
      (and (proof-is-call phase *proof-quote*)
           (proof-with-checked-results ((count (proof-term-at term 2)))
             (and (proof-is-call count *library-count*)
                  (proof-with-checked-results ((offset (proof-term-at phase 1)))
                    (and (or (eq offset t) (and (integerp offset) (< 0 offset)))
                         (proof-with-checked-results ((argument (proof-term-at count 1)))
                           (list offset argument)))))))))
   (t nil)))

(defun l1-structural-measures-phase-number (phase)
  (if (eq phase t) 1 phase))

(defun l1-structural-measures-phase-selector-step (proof library new old new-phase hypotheses)
  (if (equal new old)
      (list nil t hypotheses)
    (proof-with-checked-results
        ((scope (l1-structural-measures-selector-hypotheses proof new old hypotheses)))
      (if (not (car scope))
          (list nil nil (cdr scope))
        (proof-with-checked-results
            ((selected (descent-selector-chain library new old (car scope)))
             (step (if (equal new-phase 0)
                       (car selected)
                     (descent-shift library (car selected) (proof-quote new-phase) t))))
          (list step t (cdr scope)))))))

(defun l1-structural-measures-phase-lower (library step old old-phase new-phase parent)
  (let ((before (l1-structural-measures-phase-number old-phase))
        (after (l1-structural-measures-phase-number new-phase)))
    (if (not (< after before))
        step
      (proof-with-checked-results
          ((difference (proof-proof-prove
                        (library-library-proof library)
                        (library-positive (proof-quote (- before after))) nil nil))
           (lower (library-library-less-from-difference
                   library (l1-structural-measures-with-phase (list *library-count* old) new-phase)
                   parent difference nil)))
        (if step (library-library-compare-chain library step lower) lower)))))

(defun l1-structural-measures-phase-decrease-proof (proof library child parent before after hypotheses)
  (let ((old-phase (car before))
        (old (cadr before))
        (new-phase (car after))
        (raw (cadr after))
        (library-proof (library-library-proof library)))
    (if (< (l1-structural-measures-phase-number old-phase)
           (l1-structural-measures-phase-number new-phase))
        (cons nil hypotheses)
      (proof-with-checked-results
          ((opened (l1-application-proof-simplify proof raw nil (list *termination-return-last*)))
           (new (if opened (proof-rewritten-term opened) raw))
           (selected (l1-structural-measures-phase-selector-step
                      proof library new old new-phase hypotheses))
           (hypotheses (caddr selected)))
        (if (not (cadr selected))
            (cons nil hypotheses)
          (proof-with-checked-results
              ((step (l1-structural-measures-phase-lower library (car selected) old
                                                        old-phase new-phase parent)))
            (if (not step)
                (cons nil hypotheses)
              (proof-with-checked-results
                  ((step (if opened
                             (proof-with-checked-results
                                 ((reversed (proof-proof-symmetric library-proof opened)))
                               (proof-proof-rewrite library-proof step reversed
                                                    (if (equal new-phase 0) '(1 1 1) '(1 1 2 1))))
                           step))
                   (comparison (library-library-ordinal-comparison library child parent))
                   (result (proof-proof-transport library-proof step comparison)))
                (cons result hypotheses)))))))))

(defun l1-structural-measures-phase-decrease (proof library goal hypotheses)
  (if (not (and hypotheses (proof-is-call goal *proof-ordinal-less*)))
      (cons nil hypotheses)
    (proof-with-checked-results
        ((parts (proof-list-of-length goal 3))
         (child (cadr parts))
         (parent (caddr parts))
         (before (l1-structural-measures-phased-count parent))
         (after (l1-structural-measures-phased-count child)))
      (if (and before after)
          (l1-structural-measures-phase-decrease-proof proof library child parent before after hypotheses)
        (cons nil hypotheses)))))
