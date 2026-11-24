(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-measures-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *b1-measures-hard-error* (proof-sym "HARD-ERROR" "ACL2"))

(defun b1-measures-all-calls (terms head)
  (if (endp terms)
      t
    (and (proof-is-call (car terms) head)
         (b1-measures-all-calls (cdr terms) head))))

(defun b1-measures-right (step)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first 2)))

(defund b1-measures-normalization (lib term evidence unfold rules replies)
  (b1-logic-bookproof-normalize-with-library
   lib term evidence unfold rules nil nil nil replies))

(defund b1-measures-open-constant-member (lib term)
  (if (and (proof-is-call term *b1-measures-member*)
           (b1-measures-all-calls (cdr term) *proof-quote*))
      (proof-with-checked-results
          ((opened (proof-proof-unfold (library-library-proof lib) term))
           (value (b1-measures-right opened)))
        (cons opened value))
    nil))

(mutual-recursion
 (defun b1-measures-normalize-member (n lib term evidence unfold rules replies)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "b1-measures-normalize-member")
     (let ((result (b1-measures-normalization lib term evidence unfold rules replies)))
       (cond
        ((failure-p result) result)
        ((b1-logic-call-p result)
         (let* ((current (b1-logic-call-library result))
                (step (b1-measures-constant-member-fueled
                       (1- n) current (b1-logic-call-term result)))
                (reply (if (failure-p step) step (cons step current))))
           (b1-measures-normalize-member
            (1- n) lib term evidence unfold rules (append replies (list reply)))))
        (t (car result))))))
 (defun b1-measures-constant-member-fueled (n lib term)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "b1-measures-constant-member-fueled")
     (proof-with-checked-results ((opened (b1-measures-open-constant-member lib term)))
       (if (not opened)
           nil
         (proof-with-checked-results
             ((body (b1-measures-normalize-member
                     (1- n) lib (cdr opened) nil
                     (list *b1-logic-atom* *b1-logic-endp* *proof-not*)
                     '((:callback :constant-member)) nil)))
           (proof-proof-chain (library-library-proof lib) (car opened) (list body))))))))

(defun b1-measures-constant-member (lib term)
  (b1-measures-constant-member-fueled 1000000 lib term))

(defun b1-measures-rulers-from-hypotheses (hypotheses)
  (list :b1-measures-rulers hypotheses))

(defun b1-measures-rulers-hypotheses (rulers)
  (cadr rulers))

(defun b1-measures-rulers-init (lib tests extra)
  (proof-with-checked-results ((hypotheses (descent-hypotheses-init lib tests extra)))
    (b1-measures-rulers-from-hypotheses hypotheses)))

(defun b1-measures-rulers-proof (rulers)
  (descent-hypotheses-proof (b1-measures-rulers-hypotheses rulers)))

(defun b1-measures-rulers-tests (rulers)
  (descent-hypotheses-tests (b1-measures-rulers-hypotheses rulers)))

(defun b1-measures-rulers-with-proof (rulers lib)
  (b1-measures-rulers-from-hypotheses
   (descent-hypotheses-with-proof (b1-measures-rulers-hypotheses rulers) lib)))

(defun b1-measures-rulers-remember (hypotheses term step)
  (cons step (descent-hypotheses-remember hypotheses term step)))

(defun b1-measures-rulers-contrary (lib test holds normalized outcome)
  (let ((proof (library-library-proof lib)))
    (cond
     ((and holds (equal outcome *proof-false*))
      (proof-with-checked-results
          ((not-nil (b1-logic-proof-not-nil proof))
           (reversed (proof-proof-symmetric proof normalized))
           (contrary (proof-proof-rewrite proof not-nil reversed '(1 1)))
           (assumed (proof-proof-assume proof test t)))
        (proof-proof-cut proof assumed contrary)))
     ((and (not holds) (proof-is-call outcome *proof-quote*)
           (not (equal outcome *proof-false*)))
      (proof-with-checked-results
          ((truth (b1-logic-bookproof-true-constant lib outcome))
           (contrary (proof-proof-transport proof truth normalized))
           (assumed (proof-proof-assume proof test nil)))
        (proof-proof-cut proof contrary assumed)))
     (t nil))))

(defund b1-measures-rulers-test-step (lib signed-test noncons rules)
  (proof-with-checked-results
      ((signed (proof-list-of-length signed-test 2))
       (test (car signed))
       (normalized
        (b1-measures-normalize-member
         1000000 lib test (list noncons)
         (list *b1-logic-atom* *b1-logic-endp* *b1-logic-eq*
               *b1-logic-eql* *proof-not* (proof-cl "NULL"))
         rules nil))
       (outcome (b1-measures-right normalized)))
    (b1-measures-rulers-contrary lib test (cadr signed) normalized outcome)))

(defun b1-measures-rulers-test-noncons (tests hypotheses term noncons rules)
  (if (endp tests)
      (cons nil hypotheses)
    (let ((lib (descent-hypotheses-proof hypotheses)))
      (proof-with-checked-results
          ((step (b1-measures-rulers-test-step lib (car tests) noncons rules)))
        (if (and step (member-equal term (proof-step-clause step)))
            (proof-with-checked-results
                ((front (proof-proof-front (library-library-proof lib) step term)))
              (b1-measures-rulers-remember hypotheses term front))
          (b1-measures-rulers-test-noncons (cdr tests) hypotheses term noncons rules))))))

(defun b1-measures-selector-on-noncons (lib selector base noncons)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((completion (library-library-axiom lib selector (list base)))
         (body (b1-measures-right completion))
         (selected (proof-proof-select proof body noncons)))
      (proof-proof-chain proof completion (list selected)))))

(defun b1-measures-rulers-selector-tests (hypotheses term base noncons)
  (let* ((lib (descent-hypotheses-proof hypotheses))
         (proof (library-library-proof lib))
         (true-listp (proof-sym "TRUE-LISTP" "ACL2")))
    (proof-with-checked-results
        ((car-on-atom (b1-measures-selector-on-noncons lib "COMPLETION-OF-CAR" base noncons))
         (cdr-on-atom (b1-measures-selector-on-noncons lib "COMPLETION-OF-CDR" base noncons))
         (true-list (descent-hypotheses-find hypotheses (list true-listp base)))
         (nil-base (if (car true-list)
                       (proof-proof-simplify-first proof (car true-list) (list noncons)
                                                   (list true-listp *b1-logic-eq*))
                     nil)))
      (let ((rules (append (list (b1-logic-equal-to car-on-atom)
                                 (b1-logic-equal-to cdr-on-atom))
                           (if (car true-list) (list (b1-logic-equal-to nil-base)) nil)
                           '((:callback :constant-member)))))
        (b1-measures-rulers-test-noncons (descent-hypotheses-tests hypotheses)
                                        (cdr true-list) term noncons rules)))))

(defun b1-measures-rulers-atom-tests (heads hypotheses term base noncons)
  (if (endp heads)
      (b1-measures-rulers-selector-tests hypotheses term base noncons)
    (let* ((lib (descent-hypotheses-proof hypotheses))
           (proof (library-library-proof lib))
           (test (list (car heads) base)))
      (proof-with-checked-results
          ((negative (descent-hypotheses-find hypotheses (proof-neg test))))
        (if (car negative)
            (proof-with-checked-results
                ((positive (b1-logic-bookproof-normalize-proof
                            lib test (list noncons)
                            (list *b1-logic-atom* *b1-logic-endp* *proof-not*) nil nil))
                 (cut (proof-proof-cut proof positive (car negative)))
                 (step (proof-proof-front proof cut term)))
              (b1-measures-rulers-remember (cdr negative) term step))
          (b1-measures-rulers-atom-tests (cdr heads) (cdr negative) term base noncons))))))

(defund b1-measures-rulers-find (rulers term)
  (let* ((hypotheses (b1-measures-rulers-hypotheses rulers))
         (proof (library-library-proof (b1-measures-rulers-proof rulers))))
    (proof-with-checked-results ((direct (descent-hypotheses-find hypotheses term)))
      (if (or (car direct) (not (proof-is-call term *proof-consp*)))
          (cons (car direct) (b1-measures-rulers-from-hypotheses (cdr direct)))
        (proof-with-checked-results
            ((base (proof-term-at term 1))
             (noncons (proof-proof-assume proof term nil))
             (result (b1-measures-rulers-atom-tests
                      (list *b1-logic-atom* *b1-logic-endp*)
                      (cdr direct) term base noncons)))
          (cons (car result) (b1-measures-rulers-from-hypotheses (cdr result))))))))

(defun b1-measures-rulers-require (rulers term)
  (proof-with-checked-results ((result (b1-measures-rulers-find rulers term)))
    (if (car result) result (descent-missing-hypothesis term))))

(defund b1-measures-discharge-tests (tests proof clause step rulers)
  (cond
   ((endp tests) (cons step rulers))
   ((member-equal (car tests) clause)
    (b1-measures-discharge-tests (cdr tests) proof clause step rulers))
   (t
    (let ((test (car tests)))
      (proof-with-checked-results
          ((negative (if (proof-is-call test *proof-not*)
                         (proof-with-checked-results ((inner (proof-term-at test 1)))
                           (b1-measures-rulers-find rulers inner))
                       (cons nil rulers)))
           (evidence (if (car negative)
                         negative
                       (b1-measures-rulers-find (cdr negative) (proof-neg test)))))
        (if (not (car evidence))
            (cons nil (cdr evidence))
          (proof-with-checked-results
              ((step (proof-proof-discharge proof step (car evidence))))
            (b1-measures-discharge-tests (cdr tests) proof clause step (cdr evidence)))))))))

(defun b1-measures-discharge-matches (matches proof clause rulers)
  (if (endp matches)
      (cons nil rulers)
    (proof-with-checked-results
        ((step (car matches))
         (result (b1-measures-discharge-tests
                  (cdr (proof-step-clause step)) proof clause step rulers)))
      (if (car result)
          result
        (b1-measures-discharge-matches (cdr matches) proof clause (cdr result))))))

(defun b1-measures-direct-builtin (lib clause rulers)
  (if (endp clause)
      '(:failure "failure" "")
    (let ((proof (library-library-proof lib))
          (goal (car (last clause))))
      (proof-with-checked-results
          ((matches (descent-builtin-matches (seq-range 1 24 1) proof clause goal nil)))
        (if (car matches)
            (cons (car matches) rulers)
          (b1-measures-discharge-matches (cdr matches) proof clause rulers))))))

(defun b1-measures-selector-steps (edges lib rulers step)
  (if (endp edges)
      (proof-with-checked-results
          ((first (proof-step-first step))
           (head (proof-term-at first 0)))
        (if (equal head *proof-less*)
            step
          '(:failure "RuleInapplicable" "")))
    (let* ((edge (car edges))
           (head (car edge))
           (base (cadr edge)))
      (proof-with-checked-results
          ((evidence (b1-measures-rulers-find rulers (list *proof-consp* base)))
           (bound (descent-selector-edge lib head base (car evidence)))
           (combined (if step (library-library-compare-chain lib bound step) bound)))
        (b1-measures-selector-steps (cdr edges) lib (cdr evidence) combined)))))

(defun b1-measures-selector-chain (lib child parent rulers)
  (proof-with-checked-results ((edges (descent-selector-chain-edges child parent nil)))
    (if edges
        (b1-measures-selector-steps edges lib rulers nil)
      (proof-with-checked-results ((text (proof-write parent)))
        '(:failure "RuleInapplicable" "")))))

(defun b1-measures-selector-root (term)
  (if (or (proof-is-call term *library-car*) (proof-is-call term *library-cdr*))
      (if (consp (cdr term))
          (b1-measures-selector-root (cadr term))
        '(:failure "failure" ""))
    term))

(defun b1-measures-count-descent-strict (lib value base context)
  (proof-with-checked-results ((subtree (b1-measures-selector-root value)))
    (if (or (not (equal subtree base)) (equal value base))
        '(:failure "Unproved" "")
      (proof-with-checked-results
          ((cons-proof (b1-measures-rulers-find context (list *proof-consp* base))))
        (if (not (car cons-proof))
            '(:failure "Unproved" "")
          (b1-measures-selector-chain lib value base (cdr cons-proof)))))))

(defun b1-measures-count-descent-zero (lib context child-size parent base)
  (let ((proof (library-library-proof lib))
        (tail (list *library-count* (list *library-cdr* base))))
    (proof-with-checked-results
        ((builtin (library-library-builtin lib 3 base))
         (evidence (b1-measures-rulers-require context (list *proof-consp* base)))
         (descent (proof-proof-discharge proof builtin (car evidence)))
         (equation (library-library-ordinal-comparison lib tail parent))
         (strict (proof-proof-rewrite proof descent equation '(1)))
         (natural (library-library-natural lib tail))
         (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list tail) (list natural)))
         (weak (proof-proof-front proof nonnegative (library-le *proof-zero* tail)))
         (bound (library-library-compare-chain lib weak strict))
         (size-zero (proof-proof-simplify proof child-size nil (list *library-count*))))
      (library-library-transport-argument lib bound size-zero 1))))

(defun b1-measures-count-descent-leaf (value tests lib hypotheses parent)
  (let* ((proof (library-library-proof lib))
         (child-size (list *library-count* value))
         (claim (list *proof-ordinal-less* child-size parent)))
    (proof-with-checked-results
        ((context (b1-measures-rulers-init
                   lib (append (b1-measures-rulers-tests hypotheses) tests) nil))
         (builtin (b1-measures-direct-builtin lib (list claim) context)))
      (if (car builtin)
          (car builtin)
        (proof-with-checked-results
            ((base (proof-term-at parent 1))
             (bound (if (equal value *proof-false*)
                        (b1-measures-count-descent-zero lib (cdr builtin) child-size parent base)
                      (b1-measures-count-descent-strict lib value base (cdr builtin))))
             (equation (library-library-ordinal-comparison lib child-size parent)))
          (proof-proof-transport proof bound equation))))))

(defun b1-measures-count-descent-branch (value tests lib hypotheses parent template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reduction (b1-logic-bookproof-normalize
                     lib value nil (list *b1-measures-hard-error*) nil nil nil nil))
         (reduced (b1-measures-right reduction))
         (step (b1-measures-count-descent-leaf reduced tests lib hypotheses parent))
         (reverse (proof-proof-symmetric proof reduction)))
      (proof-proof-rewrite-result proof step reverse template *proof-result*))))

(defund b1-measures-open-value (proof value)
  (proof-with-checked-results
      ((equality (proof-proof-beta proof value))
       (opened (b1-measures-right equality)))
    (cons equality opened)))

(defun b1-measures-count-value (n lib value hypotheses parent template tests)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "Fuel" "b1-measures-count-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b1-measures-count-value
                 (1- n) lib (cadr branches) hypotheses parent template
                 (append tests (list (list (car branches) t)))))
           (no (b1-measures-count-value
                (1- n) lib (caddr branches) hypotheses parent template
                (append tests (list (list (car branches) nil))))))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((opened (b1-measures-open-value proof value))
           (step (b1-measures-count-value (1- n) lib (cdr opened) hypotheses parent template tests))
           (reverse (proof-proof-symmetric proof (car opened))))
        (proof-proof-rewrite-result proof step reverse template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (b1-measures-count-descent-branch value tests lib hypotheses parent template))
           (first (proof-step-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first target) step '(:failure "RuleInapplicable" "")))))))

(defun b1-measures-count-descent (lib goal hypotheses)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
      (let ((child (cadr parts)) (parent (caddr parts)))
        (if (not (and (proof-is-call child *library-count*) (proof-is-call parent *library-count*)))
            '(:failure "Unproved" "")
          (proof-with-checked-results
              ((actual (proof-term-at child 1))
               (base (proof-term-at parent 1))
               (opened (b1-logic-bookproof-normalize
                        lib actual nil (list *b1-measures-hard-error*) nil nil nil nil))
               (value (b1-measures-right opened)))
            (let ((template (list *proof-ordinal-less* (list *library-count* *proof-result*) parent)))
              (proof-with-checked-results
                  ((step (b1-measures-count-value 1000000 lib value hypotheses parent template nil))
                   (reverse (proof-proof-symmetric proof opened)))
                (proof-proof-rewrite-result proof step reverse template *proof-result*)))))))))

(defun b1-measures-proof-for-measures-bit-lengths (term)
  (and (proof-is-call term *proof-plus*)
       (b1-measures-all-calls (cdr term) *b1-bit-length-length*)))

(defun b1-measures-ordinal (lib measure)
  (cond
   ((proof-is-call measure *b1-integer-nfix*)
    (proof-with-checked-results ((step (b1-integer-clipped-ordinal lib measure)))
      (cons step lib)))
   ((b1-measures-proof-for-measures-bit-lengths measure)
    (b1-bit-length-bit-length-sum-ordinal lib measure))
   (t (descent-measure-ordinal-with-library lib measure))))

(defun b1-measures-clipped-gap-p (term)
  (if (not (proof-is-call term *b1-integer-nfix*))
      nil
    (proof-with-checked-results ((gap (proof-term-at term 1)))
      (if (not (proof-is-call gap *proof-plus*))
          nil
        (proof-with-checked-results ((negative (proof-term-at gap 2)))
          (if (not (proof-is-call negative *proof-minus*))
              nil
            (proof-with-checked-results ((bound (proof-term-at gap 1)))
              (if (not (proof-is-call bound *b1-integer-nfix*))
                  nil
                (proof-with-checked-results ((index (proof-term-at negative 1)))
                  (proof-is-call index *b1-integer-nfix*))))))))))

(defun b1-measures-halving-p (child parent head)
  (if (not (proof-is-call parent head))
      nil
    (proof-with-checked-results ((base (proof-term-at parent 1)))
      (equal child
             (list head (if (equal head *library-count*)
                            (list *b1-quotient-floor* base *b1-bitwise-two*)
                          (list *library-cdr* base)))))))

(defun b1-measures-halved-lengths (sizes)
  (if (endp sizes)
      nil
    (proof-with-checked-results
        ((base (proof-term-at (car sizes) 1))
         (rest (b1-measures-halved-lengths (cdr sizes))))
      (cons (list *b1-bit-length-length* (list *b1-bit-length-logcdr* base)) rest))))

(defun b1-measures-bit-length-stop (child parent clause)
  (if (not (b1-measures-proof-for-measures-bit-lengths parent))
      nil
    (proof-with-checked-results ((sizes (b1-measures-halved-lengths (cdr parent))))
      (if (not (equal child (cons *proof-plus* sizes)))
          nil
        (proof-with-checked-results
            ((left (proof-term-at parent 1))
             (right (proof-term-at parent 2)))
          (let ((stop (proof-ite (list *b1-logic-zp* left)
                                 (list *b1-logic-zp* right) *proof-false*)))
            (and (member-equal stop clause) stop)))))))

(defun b1-measures-floor-descent-proof (lib lemma value clause)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proof-proof-fact proof lemma (list (list *library-x* value)))))
      (let ((numeric-test (list *b1-quotient-numeric-eq* value *proof-neg-one*))
            (equality (proof-eq value *proof-neg-one*)))
        (if (and (not (member-equal equality clause))
                 (member-equal numeric-test clause))
            (proof-with-checked-results
                ((opened (proof-proof-unfold proof numeric-test))
                 (reverse (proof-proof-symmetric proof opened)))
              (proof-proof-rewrite proof step reverse '(3)))
          step)))))

(defun b1-measures-floor-descent (lib value clause)
  (proof-with-checked-results ((lemma (b1-bitwise-floor-half-descent lib)))
    (cons (b1-measures-floor-descent-proof (cdr lemma) (car lemma) value clause)
          (cdr lemma))))

(defun b1-measures-length-descent (lib child parent hypotheses)
  (let ((proof (library-library-proof lib)) (base (cadr parent)))
    (proof-with-checked-results
        ((cons-proof (b1-measures-rulers-find hypotheses (list *proof-consp* base))))
      (if (not (car cons-proof))
          '(:failure "Unproved" "")
        (proof-with-checked-results
            ((decrease (library-library-cite lib "LEN-CDR-LESS" (list base) (list (car cons-proof))))
             (equation (library-library-ordinal-comparison lib child parent)))
          (proof-proof-transport proof decrease equation))))))

(defun b1-measures-decrease (lib goal clause hypotheses)
  (proof-with-checked-results
      ((parent (proof-term-at goal 2))
       (clipped (b1-measures-clipped-gap-p parent)))
    (if clipped
        (proof-with-checked-results
            ((step (b1-integer-clipped-advance
                    lib goal (b1-measures-rulers-hypotheses hypotheses))))
          (cons step lib))
      (proof-with-checked-results
          ((child (proof-term-at goal 1))
           (actual (if (proof-is-call child *library-count*) (proof-term-at child 1) nil)))
        (if (and (proof-is-call child *library-count*) (proof-is-call actual *b1-quotient-ash*))
            (b1-quotient-shift-descent lib goal)
          (proof-with-checked-results ((halving (b1-measures-halving-p child parent *library-count*)))
            (if halving
                (b1-measures-floor-descent lib (cadr parent) clause)
              (proof-with-checked-results ((tail (b1-measures-halving-p child parent *library-len*)))
                (if tail
                    (proof-with-checked-results
                        ((step (b1-measures-length-descent lib child parent hypotheses)))
                      (cons step lib))
                  (proof-with-checked-results ((stop (b1-measures-bit-length-stop child parent clause)))
                    (if stop
                        (b1-bit-length-paired-bit-length-descent lib goal stop)
                      (proof-with-checked-results
                          ((step (b1-measures-count-descent lib goal hypotheses)))
                        (cons step lib)))))))))))))

(defun b1-measures-obligation (lib clause call)
  (if (not call)
      (proof-with-checked-results ((measure (proof-term-at (car clause) 1)))
        (b1-measures-ordinal lib measure))
    (proof-with-checked-results
        ((hypotheses (b1-measures-rulers-init lib (termination-call-tests call) nil))
         (builtin (b1-measures-direct-builtin lib clause hypotheses)))
      (if (car builtin)
          (cons (car builtin) lib)
        (b1-measures-decrease lib (car (last clause)) clause (cdr builtin))))))

(defund b1-measures-prove-case (lib clause call)
  (let ((result (b1-measures-obligation lib clause call)))
    (cond
     ((failure-p result) (cons result lib))
     ((failure-p (car result)) result)
     (t
      (let* ((lib (cdr result))
             (step (proof-proof-subsume (library-library-proof lib) (car result) clause)))
        (cons step lib))))))

(defund b1-measures-next-case (definitions calls measures formals)
  (if (consp definitions)
      (termination-ordinality-cases (list (car definitions)) measures)
    (termination-call-cases (list (car calls)) measures formals)))

(defun b1-measures-prove-cases (lib definitions calls measures formals seen proofs)
  (declare (xargs :measure (+ (acl2-count definitions) (acl2-count calls))))
  (if (and (endp definitions) (endp calls))
      (cons (reverse proofs) lib)
    (let* ((cases (b1-measures-next-case definitions calls measures formals))
           (clause (caar cases)))
      (if (failure-p cases)
          (cons cases lib)
        (let ((rest-definitions (cdr definitions))
              (rest-calls (if (consp definitions) calls (cdr calls))))
          (if (member-equal clause seen)
              (b1-measures-prove-cases lib rest-definitions rest-calls measures formals seen proofs)
            (let ((result (b1-measures-prove-case lib clause (cadar cases))))
              (if (failure-p (car result))
                  result
                (b1-measures-prove-cases
                 (cdr result) rest-definitions rest-calls measures formals
                 (cons clause seen) (cons (car result) proofs))))))))))

(defun b1-measures-measure-values (definitions measures)
  (if (endp definitions)
      nil
    (let* ((name (caar definitions))
           (entry (assoc-equal name measures)))
      (if entry
          (proof-with-checked-results ((rest (b1-measures-measure-values (cdr definitions) measures)))
            (cons (cdr entry) rest))
        '(:failure "RuleInapplicable" "")))))

(defun b1-measures-proof-for-measures-attempt (lib definitions calls measures)
  (let ((formals (termination-formals definitions nil nil)))
    (if (failure-p formals)
        (cons formals lib)
      (let ((result (b1-measures-prove-cases lib definitions calls measures formals nil nil)))
        (if (failure-p (car result))
            result
          (let ((ordered (b1-measures-measure-values definitions measures)))
            (cons (if (failure-p ordered) ordered (list ordered (car result)))
                  (cdr result))))))))

(defun b1-measures-proof-for-measures (lib definitions calls measures)
  (let ((result (b1-measures-proof-for-measures-attempt lib definitions calls measures)))
    (if (failure-p (car result)) (car result) result)))

(defun b1-measures-have-aids (definitions aids)
  (if (endp definitions)
      t
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (and (assoc-equal (car definition) aids)
           (b1-measures-have-aids (cdr definitions) aids)))))

(defun b1-measures-aided-plan (definitions aids plan)
  (if (endp definitions)
      plan
    (let* ((name (caar definitions))
           (measure (cdr (assoc-equal name aids))))
      (b1-measures-aided-plan (cdr definitions) aids (table-put plan name measure)))))

(defun b1-measures-selector-measures (selectors)
  (if (endp selectors)
      nil
    (cons (cons (caar selectors) (list *library-count* (cdar selectors)))
          (b1-measures-selector-measures (cdr selectors)))))

(defun b1-measures-formal-plans (name formals)
  (if (endp formals)
      nil
    (cons (list (cons name (list *library-count* (car formals))))
          (b1-measures-formal-plans name (cdr formals)))))

(defun b1-measures-singleton-plans (definitions)
  (if (not (equal (len definitions) 1))
      nil
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (if (proof-compound (cadr definition))
          (b1-measures-formal-plans (car definition) (cadr definition))
        nil))))

(defun b1-measures-measure-plans (definitions calls aids)
  (proof-with-checked-results
      ((aided-p (b1-measures-have-aids definitions aids))
       (aided (if aided-p (list (b1-measures-aided-plan definitions aids nil)) nil))
       (selectors (termination-selector-plan definitions calls))
       (selected (if (equal (len selectors) (len definitions))
                     (list (b1-measures-selector-measures selectors))
                   nil))
       (singletons (b1-measures-singleton-plans definitions)))
    (append aided selected singletons)))

(defund b1-measures-try-plan (lib definitions calls plan seen)
  (let ((key (table-values plan)))
    (if (member-equal key seen)
        (list nil lib seen)
      (let* ((attempt (b1-measures-proof-for-measures-attempt lib definitions calls plan))
             (result (car attempt))
             (lib (cdr attempt))
             (kind (cadr result)))
        (if (and (failure-p result)
                 (member-equal kind '("Unproved" "RuleInapplicable" "value" "assertion" "key")))
            (list nil lib (cons key seen))
          (list (cons result lib) lib seen))))))

(defun b1-measures-try-formals (lib definitions calls name formals seen)
  (declare (xargs :measure (acl2-count formals)))
  (if (endp formals)
      (cons '(:failure "Unproved" "") lib)
    (let* ((plan (list (cons name (list *library-count* (car formals)))))
           (attempt (b1-measures-try-plan lib definitions calls plan seen)))
      (or (car attempt)
          (b1-measures-try-formals (cadr attempt) definitions calls name (cdr formals)
                                  (caddr attempt))))))

(defun b1-measures-try-selectors (lib definitions calls seen)
  (let ((selectors (termination-selector-plan definitions calls)))
    (if (failure-p selectors)
        (cons selectors lib)
      (let* ((attempt (if (equal (len selectors) (len definitions))
                          (b1-measures-try-plan lib definitions calls
                                               (b1-measures-selector-measures selectors) seen)
                        (list nil lib seen)))
             (lib (cadr attempt)))
        (or (car attempt)
            (if (not (equal (len definitions) 1))
                (cons '(:failure "Unproved" "") lib)
              (let ((definition (proof-list-of-length (car definitions) 3)))
                (if (failure-p definition)
                    (cons definition lib)
                  (b1-measures-try-formals lib definitions calls (car definition)
                                          (if (proof-compound (cadr definition)) (cadr definition) nil)
                                          (caddr attempt))))))))))

(defun b1-measures-termination-with-library (lib definitions calls aids)
  (let ((aided-p (b1-measures-have-aids definitions aids)))
    (if (failure-p aided-p)
        (cons aided-p lib)
      (let ((attempt (if aided-p
                         (b1-measures-try-plan lib definitions calls
                                               (b1-measures-aided-plan definitions aids nil) nil)
                       (list nil lib nil))))
        (or (car attempt)
            (b1-measures-try-selectors (cadr attempt) definitions calls (caddr attempt)))))))

(defun b1-measures-termination (lib definitions calls aids)
  (let ((result (b1-measures-termination-with-library lib definitions calls aids)))
    (if (failure-p (car result)) (car result) result)))
