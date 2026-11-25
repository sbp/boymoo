(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-slice-missing-term-field* '(:failure "malformed-candidate" ""))

(defun t4-slice-local-name-delimiter (char)
  (member-equal (char-code char) '(9 10 11 12 13 32 40 41)))

(defun t4-slice-local-name-start (chars)
  (and (eql (car chars) #\A)
       (or (and (equal (take 11 chars) (coerce "ACL2::SELF-" 'list))
                (consp (nthcdr 11 chars))
                (not (t4-slice-local-name-delimiter (nth 11 chars))))
           (and (equal (take 9 chars) (coerce "ACL2::T4-" 'list))
                (consp (nthcdr 9 chars))
                (not (t4-slice-local-name-delimiter (nth 9 chars)))))))

(defun t4-slice-remember-local-name (reversed names)
  (if (endp reversed)
      names
    (let ((name (coerce (reverse reversed) 'string)))
      (if (member-equal name names) names (cons name names)))))

(defun t4-slice-local-names (chars reversed names)
  (cond
   ((endp chars) (t4-slice-remember-local-name reversed names))
   ((t4-slice-local-name-delimiter (car chars))
    (t4-slice-local-names (cdr chars) nil (t4-slice-remember-local-name reversed names)))
   ((or reversed (t4-slice-local-name-start chars))
    (t4-slice-local-names (cdr chars) (cons (car chars) reversed) names))
   (t
    (t4-slice-local-names (cdr chars) nil names))))

(defun t4-slice-select-prelude (entries needed used)
  (if (endp entries)
      used
    (let ((entry (car entries)))
      (proof-with-checked-results
       ((name (proof-term-at entry 1))
        (written (proof-write name)))
       (if (member-equal written needed)
           (proof-with-checked-results
            ((source (proof-term-at entry 3)))
            (t4-slice-select-prelude
             (cdr entries) (t4-slice-local-names (coerce source 'list) nil needed)
             (cons entry used)))
         (t4-slice-select-prelude (cdr entries) needed used))))))

(defun t4-slice-sum-counts (counts)
  (if (endp counts)
      0
    (+ (car counts) (t4-slice-sum-counts (cdr counts)))))

(defun t4-slice-prelude-text (entries steps sources)
  (if (endp entries)
      (list steps (text-join "" (reverse sources)))
    (proof-with-checked-results
     ((counts (proof-term-at (car entries) 2))
      (source (proof-term-at (car entries) 3)))
     (t4-slice-prelude-text
      (cdr entries) (+ steps (t4-slice-sum-counts counts)) (cons source sources)))))

(defun t4-slice-used-prelude (entries target)
  (proof-with-checked-results
   ((source (proof-term-at target 3))
    (used (t4-slice-select-prelude
           (reverse entries) (t4-slice-local-names (coerce source 'list) nil nil)
           (list target))))
   (t4-slice-prelude-text used 0 nil)))

(defun t4-slice-proof-library (prefix library-type)
  (declare (ignore library-type))
  (let* ((ground (proof-proof-init))
         (proof (proof-make-proof
                 (table-update (proof-proof-facts ground) (proof-proof-facts prefix))
                 (table-update (proof-proof-definitions ground) (proof-proof-definitions prefix))
                 (proof-proof-primitives ground))))
    (library-library-build (library-library-init proof))))

(defun t4-slice-selector-path-end (term formal)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((not (proof-compound term)) (equal term formal))
   ((endp term) *t4-slice-missing-term-field*)
   ((not (member-equal (car term) *termination-selectors*)) (equal term formal))
   ((endp (cdr term)) *t4-slice-missing-term-field*)
   (t (t4-slice-selector-path-end (cadr term) formal))))

(defun t4-slice-selector-path (term formal)
  (if (proof-compound term)
      (proof-with-checked-results
       ((head (proof-term-at term 0)))
       (if (member-equal head *termination-selectors*)
           (t4-slice-selector-path-end term formal)
         nil))
    nil))

(defun t4-slice-logical-terms (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
     ((term (termination-logical-body (car terms)))
      (rest (t4-slice-logical-terms (cdr terms))))
     (cons term rest))))

(defun t4-slice-logical-actuals (calls)
  (if (endp calls)
      nil
    (proof-with-checked-results
     ((actuals (t4-slice-logical-terms (termination-call-actuals (car calls))))
      (rest (t4-slice-logical-actuals (cdr calls))))
     (cons actuals rest))))

(defun t4-slice-all-tuple-tails (actuals index formal)
  (if (endp actuals)
      t
    (proof-with-checked-results
     ((actual (proof-term-at (car actuals) index)))
     (and (equal actual (list *t4-structural-tuple-tail* formal))
          (t4-slice-all-tuple-tails (cdr actuals) index formal)))))

(defun t4-slice-tuple-candidates (formals index actuals name)
  (if (endp formals)
      nil
    (proof-with-checked-results
     ((matches (t4-slice-all-tuple-tails actuals index (car formals)))
      (later (t4-slice-tuple-candidates (cdr formals) (1+ index) actuals name)))
     (if matches
         (cons (list (list (cons name (list *library-count* (list *library-car* (car formals)))))
                     "tuple")
               later)
       later))))

(defun t4-slice-all-advancing (actuals advances)
  (or (endp actuals)
      (and (member-equal (seq-slice (car actuals) 0 3) advances)
           (t4-slice-all-advancing (cdr actuals) advances))))

(defun t4-slice-range-candidates (formals actuals name)
  (if (< (len formals) 3)
      nil
    (let* ((lower (car formals))
           (upper (cadr formals))
           (stride (caddr formals))
           (negative (list *proof-minus* stride))
           (advances (list (list (library-plus lower stride) upper stride)
                           (list (library-plus stride lower) upper stride)
                           (list lower (library-plus upper negative) stride)
                           (list lower (library-plus negative upper) stride))))
      (if (t4-slice-all-advancing actuals advances)
          (list (list (list (cons name (list *library-gap* (library-plus *proof-one* upper) lower)))
                      "range"))
        nil))))

(defun t4-slice-any-changed (actuals index formal)
  (if (endp actuals)
      nil
    (proof-with-checked-results
     ((actual (proof-term-at (car actuals) index)))
     (or (not (equal actual formal))
         (t4-slice-any-changed (cdr actuals) index formal)))))

(defun t4-slice-all-selector-actuals (actuals index formal)
  (if (endp actuals)
      t
    (proof-with-checked-results
     ((actual (proof-term-at (car actuals) index))
      (follows (or (equal actual formal) (t4-slice-selector-path actual formal))))
     (and follows (t4-slice-all-selector-actuals (cdr actuals) index formal)))))

(defun t4-slice-moving-formals (formals index actuals)
  (if (endp formals)
      nil
    (let ((formal (car formals)))
      (proof-with-checked-results
       ((changed (t4-slice-any-changed actuals index formal))
        (moving (and changed (t4-slice-all-selector-actuals actuals index formal)))
        (later (t4-slice-moving-formals (cdr formals) (1+ index) actuals)))
       (if moving (cons (list index formal) later) later)))))

(defun t4-slice-change-count (moving actuals)
  (if (endp moving)
      0
    (proof-with-checked-results
     ((actual (proof-term-at actuals (caar moving)))
      (later (t4-slice-change-count (cdr moving) actuals)))
     (+ (if (equal actual (cadar moving)) 0 1) later))))

(defun t4-slice-all-single-move (actuals moving)
  (if (endp actuals)
      t
    (proof-with-checked-results
     ((changed (t4-slice-change-count moving (car actuals))))
     (and (equal changed 1) (t4-slice-all-single-move (cdr actuals) moving)))))

(defun t4-slice-selector-sum (moving)
  (let ((head (list *library-count* (cadar moving))))
    (if (endp (cdr moving))
        head
      (library-plus head (t4-slice-selector-sum (cdr moving))))))

(defun t4-slice-sum-candidates (formals actuals name)
  (proof-with-checked-results
   ((moving (t4-slice-moving-formals formals 0 actuals))
    (one-at-a-time (and (consp (cdr moving)) (t4-slice-all-single-move actuals moving))))
   (if one-at-a-time
       (list (list (list (cons name (t4-slice-selector-sum moving))) "ordinary"))
     nil)))

(defun t4-slice-inferred-measures (definitions calls)
  (if (not (equal (len definitions) 1))
      nil
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3)))
     (let ((name (car definition))
           (formals (cadr definition)))
       (if (equal formals *proof-nil*)
           nil
         (proof-with-checked-results
          ((actuals (t4-slice-logical-actuals calls))
           (tuples (t4-slice-tuple-candidates formals 0 actuals name))
           (ranges (t4-slice-range-candidates formals actuals name))
           (sums (t4-slice-sum-candidates formals actuals name)))
          (append tuples ranges sums)))))))

(defun t4-slice-phase-candidates (definitions name)
  (cond
   ((equal name *t4-application-apply*)
    (proof-with-checked-results
     ((measures (t4-application-measures definitions)))
     (list (list measures "application"))))
   ((equal name *t4-unification-unify*)
    (proof-with-checked-results
     ((measures (t4-unification-measures definitions)))
     (list (list measures "unification"))))
   (t nil)))

(defun t4-slice-lexicographic-candidates (name formals stored)
  (if (and (equal name *t4-lexicographic-do*) (proof-compound formals)
           (equal (len formals) 6))
      (let ((supplied (table-get stored name nil))
            (default (list *t4-lexicographic-lex-fix*
                           (list *t4-application-apply* (car formals)
                                 (list *proof-cons* (cadr formals) *proof-false*)))))
        (proof-with-checked-results
         ((relation (and supplied (proof-term-at supplied 1))))
         (list (list (list (cons name (list *t4-lexicographic-encode*
                                           (if (equal relation *t4-lexicographic-l-less*)
                                               (car supplied)
                                             default))))
                     "lexicographic"))))
    nil))

(defun t4-slice-candidates-of-kind (candidates ordinary)
  (if (endp candidates)
      nil
    (if (eq (equal (cadar candidates) "ordinary") ordinary)
        (cons (car candidates) (t4-slice-candidates-of-kind (cdr candidates) ordinary))
      (t4-slice-candidates-of-kind (cdr candidates) ordinary))))

(defun t4-slice-count-plan (plan)
  (if (endp plan)
      nil
    (cons (cons (caar plan) (list *library-count* (cdar plan)))
          (t4-slice-count-plan (cdr plan)))))

(defun t4-slice-all-stored (definitions stored)
  (if (endp definitions)
      t
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3)))
     (let ((entry (assoc-equal (car definition) stored)))
       (if entry
           (proof-with-checked-results
            ((relation (proof-term-at (cdr entry) 1)))
            (and (equal relation *proof-ordinal-less*)
                 (t4-slice-all-stored (cdr definitions) stored)))
         nil)))))

(defun t4-slice-stored-plan (definitions stored measures)
  (if (endp definitions)
      measures
    (let ((name (caar definitions)))
      (t4-slice-stored-plan
       (cdr definitions) stored
       (table-put measures name (car (table-get stored name nil)))))))

(defun t4-slice-formal-pools (definitions reversed)
  (if (endp definitions)
      reversed
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3)))
     (let ((formals (cadr definition)))
       (t4-slice-formal-pools
        (cdr definitions) (cons (if (proof-compound formals) formals nil) reversed))))))

(defun t4-slice-product-formals (reversed-pools index selected)
  (cond
   ((endp reversed-pools) (and (equal index 0) (cons t selected)))
   ((endp (car reversed-pools)) nil)
   (t
    (let ((size (len (car reversed-pools))))
      (t4-slice-product-formals
       (cdr reversed-pools) (floor index size)
       (cons (nth (mod index size) (car reversed-pools)) selected))))))

(defun t4-slice-product-plan (definitions selected measures)
  (if (or (endp definitions) (endp selected))
      measures
    (t4-slice-product-plan
     (cdr definitions) (cdr selected)
     (table-put measures (caar definitions) (list *library-count* (car selected))))))

(defund t4-slice-candidate-stage (definitions calls stored cursor)
  (let ((ordinary (caddr cursor)))
    (case (car cursor)
    (:phase
     (proof-with-checked-results
      ((first (proof-term-at definitions 0))
       (name (proof-term-at first 0))
       (formals (proof-term-at first 1))
       (found (t4-slice-phase-candidates definitions name)))
      (list :lexicographic found nil)))
    (:lexicographic
     (proof-with-checked-results
      ((found (t4-slice-lexicographic-candidates (caar definitions) (cadar definitions) stored)))
      (list :inferred found nil)))
    (:inferred
     (proof-with-checked-results
      ((inferred (t4-slice-inferred-measures definitions calls)))
      (list :selector (t4-slice-candidates-of-kind inferred nil)
            (t4-slice-candidates-of-kind inferred t))))
    (:selector
     (proof-with-checked-results
      ((plan (termination-selector-plan definitions calls)))
      (list :stored (and plan (list (list (t4-slice-count-plan plan) "ordinary"))) ordinary)))
    (:stored
     (proof-with-checked-results
      ((all-stored (t4-slice-all-stored definitions stored)))
      (list :ordinary
            (and all-stored (list (list (t4-slice-stored-plan definitions stored nil) "ordinary")))
            ordinary)))
    (:ordinary (list :product ordinary nil))
    (:product
     (proof-with-checked-results
      ((pools (t4-slice-formal-pools definitions nil)))
      (list :product-item nil nil 0 pools)))
    (:product-item
     (let* ((index (nth 3 cursor))
            (pools (nth 4 cursor))
            (selected (and (< index 12) (t4-slice-product-formals pools index nil))))
       (if selected
           (list :product-item
                 (list (list (t4-slice-product-plan definitions (cdr selected) nil) "ordinary"))
                 nil (1+ index) pools)
         (list :done nil nil))))
    (otherwise (list :done nil nil)))))

(defund t4-slice-next-candidate (n definitions calls stored cursor)
  (declare (xargs :measure (nfix n)))
  (let ((stage (car cursor))
        (pending (cadr cursor)))
    (cond
     ((failure-p cursor) cursor)
     ((zp n) '(:failure "fuel" "t4-slice-next-candidate"))
     ((consp pending)
      (cons (car pending) (list* stage (cdr pending) (cddr cursor))))
     ((eq stage :done) nil)
     (t
      (t4-slice-next-candidate (1- n) definitions calls stored
                              (t4-slice-candidate-stage definitions calls stored cursor))))))

(defconst *t4-slice-unproved* '(:failure "unproved" ""))

(defun t4-slice-unproved-p (value)
  (and (failure-p value) (equal (cadr value) "unproved")))

(defun t4-slice-phase-mode-p (mode)
  (member-equal mode '("application" "unification")))

(defun t4-slice-range-replies (queries evidence)
  (if (endp queries)
      nil
    (proof-with-checked-results
     ((required (t4-structural-evidence-require evidence (car queries)))
      (later (t4-slice-range-replies (cdr queries) (cdr required))))
     (cons (car required) later))))

(defun t4-slice-range-descent (library goal evidence formals)
  (proof-with-checked-results
   ((queries (t4-ranges-range-descent-queries goal formals))
    (replies (t4-slice-range-replies queries evidence))
    (step (t4-ranges-range-descent library goal replies formals)))
   (cons step library)))

(defun t4-slice-structural-descent (library goal call mode formals)
  (proof-with-checked-results
   ((evidence (t4-structural-evidence-init library (termination-call-tests call) nil)))
   (if (equal mode "tuple")
       (proof-with-checked-results
        ((result (t4-structural-structural-tuple-descent library goal evidence)))
        (cons (car result) (cadr result)))
     (proof-with-checked-results
      ((parent (proof-term-at goal 2))
       (head (proof-term-at parent 0)))
      (cond
       ((equal head *library-count*)
        (proof-with-checked-results
         ((result (t4-structural-structural-count-descent library goal evidence)))
         (cons (car result) (cadr result))))
       ((equal head *proof-plus*)
        (proof-with-checked-results
         ((result (t4-structural-structural-sum-descent library goal evidence)))
         (cons (car result) (cadr result))))
       ((equal mode "range")
        (t4-slice-range-descent library goal evidence formals))
       (t *t4-slice-unproved*))))))

(defun t4-slice-lexicographic-ordinal (library goal)
  (proof-with-checked-results
   ((embedded (t4-lexicographic-lexicographic-build-embedding library))
    (measure (proof-term-at goal 1))
    (step (library-library-cite embedded "LEX-ORDINAL" (cdr measure) nil)))
   (cons step embedded)))

(defun t4-slice-measure-case (library clause call mode formals)
  (let ((goal (car (last clause))))
    (cond
     ((t4-slice-phase-mode-p mode)
      (cond
       ((not call)
        (proof-with-checked-results
         ((measure (proof-term-at goal 1)))
         (t4-ordinals-ordinals-phase-measure-ordinal library measure)))
       ((equal mode "application") (t4-application-descent library goal call))
       (t (t4-unification-descent library goal call))))
     ((equal mode "lexicographic")
      (if call
          (proof-with-checked-results
           ((step (t4-lexicographic-lexicographic-do-descent library goal call)))
           (cons step library))
        (t4-slice-lexicographic-ordinal library goal)))
     ((not call)
      (proof-with-checked-results
       ((measure (proof-term-at goal 1)))
       (descent-measure-ordinal-with-library library measure)))
     (t (t4-slice-structural-descent library goal call mode formals)))))

(defun t4-slice-measure-work-library (prefix library mode)
  (or library
      (t4-slice-proof-library
       prefix
       (cond ((t4-slice-phase-mode-p mode) :ordinals)
             ((equal mode "lexicographic") :lexicographic)
             (t :structural)))))

(defun t4-slice-measure-case-step (prefix library clause call mode formals)
  (let ((proof-source (or library prefix)))
    (proof-with-checked-results
     ((hypotheses (and call (descent-hypotheses-init proof-source (termination-call-tests call) nil)))
      (direct (descent-direct-builtin proof-source clause hypotheses)))
     (if (car direct)
         (cons (car direct) library)
       (proof-with-checked-results
        ((work-library (t4-slice-measure-work-library prefix library mode)))
        (let ((result (t4-slice-measure-case work-library clause call mode formals)))
          (if (and (failure-p result)
                   (member-equal (cadr result) '("search-miss" "value" "unproved")))
              *t4-slice-unproved*
            result)))))))

(defun t4-slice-required-value (dictionary key)
  (let ((entry (assoc-equal key dictionary)))
    (if entry (cdr entry) '(:failure "missing-proof-input" ""))))

(defun t4-slice-definition-formals (definitions formals)
  (if (endp definitions)
      formals
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3)))
     (t4-slice-definition-formals
      (cdr definitions) (table-put formals (car definition) (cadr definition))))))

(defun t4-slice-case-tests (tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
     ((signed (proof-list-of-length (car tests) 2))
      (rest (t4-slice-case-tests (cdr tests))))
     (cons (if (cadr signed) (proof-neg (car signed)) (car signed)) rest))))

(defun t4-slice-bind-actuals (formals actuals bindings)
  (if (or (endp formals) (endp actuals))
      bindings
    (t4-slice-bind-actuals
     (cdr formals) (cdr actuals) (table-put bindings (car formals) (car actuals)))))

(defun t4-slice-call-clause (call measures formals)
  (let ((callee (termination-call-callee call)))
    (proof-with-checked-results
     ((tests (t4-slice-case-tests (termination-call-tests call)))
      (measure (t4-slice-required-value measures callee))
      (parameters (t4-slice-required-value formals callee))
      (smaller (proof-subst measure (t4-slice-bind-actuals
                                     parameters (termination-call-actuals call) nil)))
      (original (t4-slice-required-value measures (termination-call-caller call))))
     (append tests (list (list *proof-ordinal-less* smaller original))))))

(defund t4-slice-prove-case (prefix clause call mode formals progress)
  (let ((library (car progress))
        (seen (cadr progress))
        (proofs (caddr progress)))
    (if (member-equal clause seen)
        progress
      (proof-with-checked-results
       ((step (t4-slice-measure-case-step prefix library clause call mode formals))
        (subsumed (proof-proof-subsume
                   (if (cdr step) (library-library-proof (cdr step)) prefix) (car step) clause)))
       (list (cdr step) (cons clause seen) (cons subsumed proofs))))))

(defun t4-slice-prove-ordinal-cases (definitions measures prefix mode formals progress)
  (if (endp definitions)
      progress
    (proof-with-checked-results
     ((measure (t4-slice-required-value measures (caar definitions)))
      (proved (t4-slice-prove-case prefix (list (list *proof-ordinalp* measure)) nil
                                   mode formals progress)))
     (t4-slice-prove-ordinal-cases (cdr definitions) measures prefix mode formals proved))))

(defun t4-slice-prove-call-cases (calls measures all-formals prefix mode formals progress)
  (if (endp calls)
      progress
    (proof-with-checked-results
     ((clause (t4-slice-call-clause (car calls) measures all-formals))
      (proved (t4-slice-prove-case prefix clause (car calls) mode formals progress)))
     (t4-slice-prove-call-cases (cdr calls) measures all-formals prefix mode formals proved))))

(defun t4-slice-ordered-measures (definitions measures)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car definitions) 0))
      (measure (t4-slice-required-value measures name))
      (rest (t4-slice-ordered-measures (cdr definitions) measures)))
     (cons measure rest))))

(defund t4-slice-measure-proofs (prefix definitions calls measures mode)
  (proof-with-checked-results
   ((definition (if (endp definitions) *t4-slice-missing-term-field*
                  (proof-list-of-length (car definitions) 3)))
    (formals (t4-slice-definition-formals definitions nil))
    (ordinals (t4-slice-prove-ordinal-cases definitions measures prefix mode (cadr definition) nil))
    (proved (t4-slice-prove-call-cases calls measures formals prefix mode (cadr definition) ordinals))
    (ordered (t4-slice-ordered-measures definitions measures))
    (entry (proof-proof-entry "measure" (car definition) (cons (car definition) ordered)
                              (reverse (caddr proved)))))
   (t4-slice-used-prelude (and (car proved) (library-library-entries (car proved))) entry)))

(defun t4-slice-try-measures (n prefix definitions calls stored cursor attempts)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t4-slice-try-measures")
    (proof-with-checked-results
     ((next (t4-slice-next-candidate 1000000 definitions calls stored cursor)))
     (if (not next)
         *t4-slice-unproved*
       (let ((measures (caar next))
             (mode (cadar next))
             (cursor (cdr next)))
         (proof-with-checked-results
          ((ordered (t4-slice-ordered-measures definitions measures)))
          (let ((attempt (list ordered mode)))
            (if (member-equal attempt attempts)
                (t4-slice-try-measures
                 (1- n) prefix definitions calls stored cursor attempts)
              (let ((result (t4-slice-measure-proofs prefix definitions calls measures mode)))
                (if (and (failure-p result)
                         (member-equal (cadr result)
                                       '("unproved" "search-miss" "inference-mismatch" "missing-proof-input"
                                         "value" "assertion" "key" "recursion")))
                    (t4-slice-try-measures
                     (1- n) prefix definitions calls stored cursor (cons attempt attempts))
                  result))))))))))

(defun t4-slice-measure-entry (prefix data stored)
  (cond
   ((null data) '(:failure "search-miss" ""))
   ((endp data) (proof-list-of-length data 1))
   (t
    (proof-with-checked-results
     ((calls (termination-recursive-calls (car data) (cdr data))))
     (t4-slice-try-measures 1000000 prefix (cdr data) calls stored '(:phase nil nil) nil)))))

(defun t4-slice-common-lisp-definition-p (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3))
      (package (proof-term-at (car definition) 1)))
     (or (equal package "COMMON-LISP")
         (t4-slice-common-lisp-definition-p (cdr definitions))))))

(defun t4-slice-witness-failure (data)
  (proof-with-checked-results
   ((functions (proof-term-at data 0))
    (function (proof-term-at functions 0))
    (name (proof-term-at function 0)))
   *t4-slice-unproved*))

(defun t4-slice-generate (prefix kind data stored choices)
  (if (equal kind "define")
      (proof-with-checked-results
       ((refused (t4-slice-common-lisp-definition-p (cdr data))))
       (if refused
           *t4-slice-unproved*
         (proof-with-checked-results
          ((generated (t4-slice-measure-entry prefix data stored)))
          (cons generated prefix))))
    (proof-with-checked-results
     ((witness (t4-witness-prove-witness prefix data choices)))
     (if (car witness) witness (t4-slice-witness-failure data)))))

(defun t4-slice-evaluator-witness (prefix name data suffix)
  (let ((first (t4-evaluator-evaluator-witness nil prefix name data suffix)))
    (if (not (t4-evaluator-request-p first))
        first
      (let* ((generation (t4-slice-generate (nth 2 first) (nth 3 first) (nth 4 first)
                                            (nth 5 first) (nth 6 first)))
             (reply (if (failure-p generation) generation (car generation)))
             (second (t4-evaluator-evaluator-witness reply prefix name data suffix)))
        (if (t4-evaluator-request-p second)
            (t4-evaluator-evaluator-witness
             (list :replies reply (t4-slice-used-prelude (nth 2 second) (nth 3 second)))
             prefix name data suffix)
          second)))))

(defund t4-slice-simple-witness-step (library tactic name data suffix replies)
  (proof-with-checked-results
   ((result (t4-bookwitness-simple-witness replies library name data suffix)))
   (let ((value (car result)))
     (cond
      ((not (t4-bookwitness-request-p value))
       (cons value (t4-booklogic-booklogic-with-library tactic (cdr result))))
      ((eq (cadr value) :solve)
       (let* ((working (t4-booklogic-booklogic-with-remaining
                        (t4-booklogic-booklogic-with-library tactic (nth 2 value)) 850))
              (solved (t4-booklogic-booklogic-solve-with-book working (nth 3 value) nil nil 0))
              (updated (cdr solved))
              (reply (cons (car solved) (t4-booklogic-booklogic-library updated))))
         (list :continue updated (append replies (list reply)))))
      (t
       (let ((reply (t4-slice-used-prelude (nth 2 value) (nth 3 value))))
         (list :continue tactic (append replies (list reply)))))))))

(defun t4-slice-simple-witness-requests (n library tactic name data suffix replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t4-slice-simple-witness-requests")
    (let ((next (t4-slice-simple-witness-step library tactic name data suffix replies)))
      (if (eq (car next) :continue)
          (t4-slice-simple-witness-requests (1- n) library (cadr next) name data suffix (caddr next))
        next))))

(defun t4-slice-simple-witness (tactic name data suffix)
  (let ((tactic (t4-booklogic-booklogic-with-total-remaining
                 (t4-booklogic-booklogic-with-enabled tactic nil) :none)))
    (t4-slice-simple-witness-requests 1000000 (t4-booklogic-booklogic-library tactic)
                                     tactic name data suffix nil)))

(defun t4-slice-theorem-entry (tactic name formula enabled)
  (let* ((proved (t4-booklogic-booklogic-theorem-with-book tactic formula enabled))
         (step (car proved))
         (tactic (cdr proved)))
    (cons (proof-with-checked-results
           ((step step)
            (entry (proof-proof-entry "theorem" name (list name) (list step))))
           (t4-slice-used-prelude (t4-booklogic-booklogic-entries tactic) entry))
          tactic)))

(defun t4-slice-book-entry-result (name kind raw generated evaluator simple proof tactic)
  (proof-with-checked-results
   ((entry (t4-bookrun-book-entry name kind raw generated evaluator simple)))
   (list entry proof tactic)))

(defun t4-slice-constraint-entry (proof tactic name data raw generated)
  (let* ((suffix (t4-bookrun-witness-suffix raw))
         (evaluator (t4-slice-evaluator-witness proof name data suffix)))
    (if evaluator
        (t4-slice-book-entry-result name "constrain" raw generated evaluator nil proof tactic)
      (proof-with-checked-results
       ((simple (t4-slice-simple-witness tactic name data suffix)))
       (t4-slice-book-entry-result name "constrain" raw generated nil (car simple)
                                   proof (cdr simple))))))

(defun t4-slice-book-entry-with-tactic (proof tactic choices raw kind data name stored hints)
  (if (equal kind "theorem")
      (let* ((formula (proof-term-at data 1))
             (theorem (if (failure-p formula) (cons formula tactic)
                        (t4-slice-theorem-entry tactic name formula (table-get hints name nil)))))
        (t4-slice-book-entry-result name kind raw (car theorem) nil nil proof (cdr theorem)))
    (let ((generated (t4-slice-generate proof kind data stored choices)))
      (cond
       ((and (equal kind "constrain") (t4-slice-unproved-p generated))
        (t4-slice-constraint-entry proof tactic name data raw generated))
       ((failure-p generated)
        (t4-slice-book-entry-result name kind raw generated nil nil proof tactic))
       (t (t4-slice-book-entry-result name kind raw (car generated) nil nil (cdr generated) tactic))))))

(defun t4-slice-book-entry (proof tactic choices raw kind data name stored hints)
  (proof-with-checked-results
   ((result (t4-slice-book-entry-with-tactic proof tactic choices raw kind data name stored hints)))
   (cons (car result) (cadr result))))

