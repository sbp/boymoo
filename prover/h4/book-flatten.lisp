(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h4-book-flatten-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *h4-book-flatten-list-fix* (proof-sym "TRUE-LIST-FIX" "ACL2"))
(defconst *h4-book-flatten-list-equiv* (proof-sym "LIST-EQUIV" "ACL2"))
(defconst *h4-book-flatten-revappend* (proof-cl "REVAPPEND"))
(defconst *h4-book-flatten-logic*
  (list *proof-not* (proof-cl "ATOM") (proof-cl "ENDP")
        (proof-cl "EQ") (proof-cl "EQL")))

(defun h4-book-flatten-normalize (p term evidence expand rewrites)
  (h4-association-normalize p term evidence expand rewrites))

(defun h4-book-flatten-establish (p formula evidence expand rewrites)
  (h4-association-establish p formula evidence expand rewrites))

(defun h4-book-flatten-imply (p formula conclusion)
  (h4-association-imply p formula conclusion))

(defun h4-book-flatten-conjunction (p formula first second)
  (h4-association-conjunction p formula first second))

(defun h4-book-flatten-conjunct (p step)
  (h4-association-conjunct p step))

(defun h4-book-flatten-modus-ponens (p step evidence)
  (h4-association-modus-ponens p step evidence))

(defun h4-book-flatten-nil-value (p negative)
  (h4-association-nil-value p negative))

(defun h4-book-flatten-non-nil (p equality)
  (h4-association-non-nil (library-library-proof p) equality))

(defun h4-book-flatten-case-of (p formula test yes no)
  (h4-association-case-of p formula test yes no))

(defun h4-book-flatten-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun h4-book-flatten-binding-map (bindings result)
  (if (endp bindings)
      result
    (h4-book-flatten-binding-map
     (cdr bindings) (table-put result (caar bindings) (cadar bindings)))))

(defun h4-book-flatten-evidence-map (evidence result)
  (if (endp evidence)
      result
    (proof-with-checked-results ((literal (proof-step-first (car evidence))))
      (h4-book-flatten-evidence-map
       (cdr evidence) (table-put result literal (car evidence))))))

(mutual-recursion
 (defun h4-book-flatten-match-term (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond
    ((not (proof-compound pattern))
     (let ((prior (assoc-equal pattern bindings)))
       (if prior
           (cons (equal (cdr prior) term) bindings)
         (cons t (table-put bindings pattern term)))))
    ((proof-is-call pattern *proof-quote*)
     (cons (equal pattern term) bindings))
    ((or (not (proof-compound term)) (/= (len pattern) (len term)))
     (cons nil bindings))
    ((endp pattern) '(:failure "MissingTermPart" ""))
    ((equal (car pattern) (car term))
     (h4-book-flatten-match-arguments (cdr pattern) (cdr term) bindings))
    (t (cons nil bindings))))

 (defun h4-book-flatten-match-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
      ((matched (h4-book-flatten-match-term (car patterns) (car terms) bindings)))
      (if (car matched)
          (h4-book-flatten-match-arguments (cdr patterns) (cdr terms) (cdr matched))
        matched)))))

(defun h4-book-flatten-fact-conclusion (conclusion)
  (declare (xargs :measure (acl2-count conclusion)))
  (if (proof-is-call conclusion *library-implies*)
      (if (consp (cddr conclusion))
          (h4-book-flatten-fact-conclusion (caddr conclusion))
        '(:failure "MissingTermPart" ""))
    conclusion))

(defun h4-book-flatten-fact-discharge (n p step known)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h4-book-flatten-fact-discharge")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (if (proof-is-call literal *library-implies*)
          (proof-with-checked-results ((premise (proof-term-at literal 1)))
            (let ((evidence (table-get known premise nil)))
              (and evidence
                   (proof-with-checked-results
                    ((next (h4-book-flatten-modus-ponens p step evidence)))
                    (h4-book-flatten-fact-discharge (1- n) p next known)))))
        step))))

(defun h4-book-flatten-match-fact (p name clause term known rewrite)
  (if (= (len clause) 1)
      (proof-with-checked-results
       ((conclusion (h4-book-flatten-fact-conclusion (car clause))))
       (if (and rewrite (not (proof-is-call conclusion *proof-equal*)))
           nil
         (proof-with-checked-results
          ((target (if rewrite (proof-term-at conclusion 1) conclusion))
           (matched (if (proof-compound target)
                        (h4-book-flatten-match-term target term nil)
                      nil)))
          (and (car matched)
               (proof-with-checked-results
                ((step (proof-proof-fact (library-library-proof p) name
                                         (table-items (cdr matched)))))
                (h4-book-flatten-fact-discharge 1000000 p step known))))))
    nil))

(defun h4-book-flatten-fact-instances (p names facts term known rewrite)
  (if (endp names)
      nil
    (let ((result (h4-book-flatten-match-fact
                   p (car names) (table-get facts (car names) nil)
                   term known rewrite)))
      (or result (h4-book-flatten-fact-instances
                  p (cdr names) facts term known rewrite)))))

(defun h4-book-flatten-fact-instance (p term evidence names rewrite)
  (proof-with-checked-results
   ((known (h4-book-flatten-evidence-map evidence nil)))
   (let ((facts (proof-proof-facts (library-library-proof p))))
     (h4-book-flatten-fact-instances p
                                    (if (eq names :none) (table-keys facts) names)
                                    facts term known rewrite))))

(defun h4-book-flatten-unfold-selected (p call shape selectors)
  (if (not shape)
      '(:failure "InapplicableStep" "")
    (let ((proof (library-library-proof p)))
      (proof-with-checked-results
       ((opened (proof-proof-unfold proof call))
        (body (h4-book-flatten-step-right opened))
        (result (h4-book-flatten-normalize
                 p body (list shape) *h4-book-flatten-logic* selectors)))
       (proof-proof-chain proof opened (list result))))))

(defun h4-book-flatten-unfold-on-list (p call sequence shape)
  (let ((proof (library-library-proof p)))
    (cond
     ((proof-is-call sequence *proof-cons*)
      (let ((args (cdr sequence)))
        (proof-with-checked-results
         ((shape (proof-proof-fact
                  proof "consp-cons" (seq-zip (list *library-x* *library-y*) args)))
          (first (library-library-axiom p "CAR-CONS" args))
          (rest (library-library-axiom p "CDR-CONS" args)))
         (h4-book-flatten-unfold-selected p call shape (list first rest)))))
     ((equal sequence *proof-false*)
      (proof-with-checked-results
       ((shape (h4-book-flatten-establish p (proof-neg (list *proof-consp* *proof-false*))
                                         nil *h4-book-flatten-logic* nil)))
       (h4-book-flatten-unfold-selected p call shape nil)))
     (t (h4-book-flatten-unfold-selected p call shape nil)))))

(defun h4-book-flatten-rewrite-argument (p call index equality)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((reflexive (proof-proof-reflexive proof call)))
      (proof-proof-rewrite proof reflexive equality (list 1 2 index)))))

(defun h4-book-flatten-cdr-induction-substitution (sequence changes)
  (cons (list sequence (list *library-cdr* sequence)) changes))

(defun h4-book-flatten-cdr-induction-recurse (shape p formula sequence changes)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((builtin-step (library-library-builtin p 3 sequence))
      (decreases (proof-proof-discharge proof builtin-step shape))
      (goal (proof-step-first decreases))
      (smaller (proof-subst formula
                            (h4-book-flatten-binding-map
                             (h4-book-flatten-cdr-induction-substitution sequence changes)
                             nil)))
      (assumption (proof-proof-assume proof (proof-ite goal smaller *proof-true*) t)))
     (proof-proof-prove-if proof assumption decreases))))

(defun h4-book-flatten-cdr-induction (p formula sequence base step changes)
  (let* ((proof (library-library-proof p))
         (test (list *proof-consp* sequence))
         (substitution (h4-book-flatten-cdr-induction-substitution sequence changes)))
    (proof-with-checked-results
     ((cases (h4-book-flatten-case-of p formula test step base))
      (ordinal (library-library-builtin p 1 sequence)))
     (proof-proof-induct proof ordinal cases formula
                         (list *library-count* sequence) (list substitution)))))

(defun h4-book-flatten-list-shape (p sequence holds)
  (proof-proof-assume (library-library-proof p) (list *proof-consp* sequence) holds))

(defun h4-book-flatten-append-associativity-expand (shape p inner first last)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((combined (h4-book-flatten-unfold-on-list p inner *library-x* shape))
      (left (h4-book-flatten-rewrite-argument p first 1 combined))
      (sequence (h4-book-flatten-step-right combined))
      (left (if (proof-is-call sequence *proof-cons*)
                (proof-with-checked-results
                 ((call (h4-book-flatten-step-right left))
                  (opened (h4-book-flatten-unfold-on-list p call sequence nil)))
                 (proof-proof-chain proof left (list opened)))
              left))
      (right (h4-book-flatten-unfold-on-list p last *library-x* shape)))
     (list left right))))

(defun h4-book-flatten-append-associativity-finish (shape hypothesis p inner first last)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((sides (h4-book-flatten-append-associativity-expand shape p inner first last))
      (left (if hypothesis
                (proof-proof-rewrite proof (car sides) hypothesis '(1 2 2))
              (car sides)))
      (right (proof-proof-symmetric proof (cadr sides))))
     (proof-proof-chain proof left (list right)))))

(defun h4-book-flatten-append-associativity (p)
  (let* ((inner (list *h4-book-flatten-append* *library-x* *library-y*))
         (outer (list *h4-book-flatten-append* *library-y* *library-z*))
         (first (list *h4-book-flatten-append* inner *library-z*))
         (last (list *h4-book-flatten-append* *library-x* outer))
         (formula (proof-eq first last)))
    (proof-with-checked-results
     ((shape (h4-book-flatten-list-shape p *library-x* t))
      (hypothesis (h4-book-flatten-cdr-induction-recurse shape p formula *library-x* nil))
      (step (h4-book-flatten-append-associativity-finish shape hypothesis p inner first last))
      (shape (h4-book-flatten-list-shape p *library-x* nil))
      (base (h4-book-flatten-append-associativity-finish shape nil p inner first last)))
     (h4-book-flatten-cdr-induction p formula *library-x* base step nil))))

(defun h4-book-flatten-revappend-after-append-finish
    (shape hypothesis p joined reversed-head first last)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((combined (h4-book-flatten-unfold-on-list p joined *library-x* shape))
      (left (h4-book-flatten-rewrite-argument p first 1 combined))
      (left (if hypothesis
                (proof-with-checked-results
                 ((call (h4-book-flatten-step-right left))
                  (sequence (h4-book-flatten-step-right combined))
                  (opened (h4-book-flatten-unfold-on-list p call sequence nil)))
                 (proof-proof-chain proof left (list opened hypothesis)))
              left))
      (opened (h4-book-flatten-unfold-on-list p reversed-head *library-x* shape))
      (right (h4-book-flatten-rewrite-argument p last 2 opened))
      (right (proof-proof-symmetric proof right)))
     (proof-proof-chain proof left (list right)))))

(defun h4-book-flatten-revappend-after-append (p)
  (let* ((joined (list *h4-book-flatten-append* *library-x* *library-y*))
         (reversed-head (list *h4-book-flatten-revappend* *library-x* *library-z*))
         (first (list *h4-book-flatten-revappend* joined *library-z*))
         (last (list *h4-book-flatten-revappend* *library-y* reversed-head))
         (formula (proof-eq first last))
         (changes (list (list *library-z*
                              (list *proof-cons* (list *library-car* *library-x*)
                                    *library-z*)))))
    (proof-with-checked-results
     ((shape (h4-book-flatten-list-shape p *library-x* t))
      (hypothesis (h4-book-flatten-cdr-induction-recurse shape p formula *library-x* changes))
      (step (h4-book-flatten-revappend-after-append-finish
             shape hypothesis p joined reversed-head first last))
      (shape (h4-book-flatten-list-shape p *library-x* nil))
      (base (h4-book-flatten-revappend-after-append-finish
             shape nil p joined reversed-head first last)))
     (h4-book-flatten-cdr-induction p formula *library-x* base step changes))))

(defun h4-book-flatten-chain-empty (p step output)
  (if (equal output *proof-false*)
      (proof-with-checked-results
       ((call (h4-book-flatten-step-right step))
        (opened (h4-book-flatten-unfold-on-list p call *proof-false* nil)))
       (proof-proof-chain (library-library-proof p) step (list opened)))
    '(:failure "InapplicableStep" "")))

(defun h4-book-flatten-concat-map-extend
    (p lhs rhs combined first-output hypothesis associative second-output)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((call (h4-book-flatten-step-right lhs))
      (sequence (h4-book-flatten-step-right combined))
      (opened (h4-book-flatten-unfold-on-list p call sequence nil))
      (lhs (proof-proof-chain proof lhs (list opened)))
      (lhs (proof-proof-rewrite proof lhs hypothesis '(1 2 2)))
      (output (h4-book-flatten-step-right first-output))
      (parts (proof-list-of-length output 3))
      (instance (proof-proof-instantiate
                 proof associative
                 (seq-zip (list *library-x* *library-y* *library-z*)
                         (list (cadr parts) (caddr parts) second-output))))
      (rhs (proof-proof-chain proof rhs (list instance))))
     (list lhs rhs))))

(defun h4-book-flatten-concat-map-finish
    (shape hypothesis p mapper first second joined left right associative)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((combined (h4-book-flatten-unfold-on-list p joined first shape))
      (lhs (h4-book-flatten-rewrite-argument p left 1 combined))
      (first-output (h4-book-flatten-unfold-on-list p (list mapper first) first shape))
      (rhs (h4-book-flatten-rewrite-argument p right 1 first-output))
      (sides (if hypothesis
                 (h4-book-flatten-concat-map-extend
                  p lhs rhs combined first-output hypothesis associative (list mapper second))
               (proof-with-checked-results
                ((output (h4-book-flatten-step-right first-output))
                 (rhs (h4-book-flatten-chain-empty p rhs output)))
                (list lhs rhs))))
      (reversed (proof-proof-symmetric proof (cadr sides))))
     (proof-proof-chain proof (car sides) (list reversed)))))

(defun h4-book-flatten-concat-map (p mapper first second)
  (let* ((joined (list *h4-book-flatten-append* first second))
         (left (list mapper joined))
         (right (list *h4-book-flatten-append* (list mapper first) (list mapper second)))
         (formula (proof-eq left right)))
    (proof-with-checked-results
     ((associative (h4-book-flatten-append-associativity p))
      (shape (h4-book-flatten-list-shape p first t))
      (hypothesis (h4-book-flatten-cdr-induction-recurse shape p formula first nil))
      (step (h4-book-flatten-concat-map-finish
             shape hypothesis p mapper first second joined left right associative))
      (shape (h4-book-flatten-list-shape p first nil))
      (base (h4-book-flatten-concat-map-finish
             shape nil p mapper first second joined left right associative)))
     (h4-book-flatten-cdr-induction p formula first base step nil))))

(defun h4-book-flatten-map-accumulator-extend
    (p lhs rhs output-equation hypothesis distributive accumulator)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((lhs (proof-proof-chain proof lhs (list hypothesis)))
      (output (h4-book-flatten-step-right output-equation))
      (revision (proof-proof-instantiate
                 proof distributive
                 (seq-zip (list *library-x* *library-y* *library-z*)
                         (append (cdr output) (list accumulator)))))
      (rhs (proof-proof-chain proof rhs (list revision))))
     (list lhs rhs))))

(defun h4-book-flatten-map-accumulator-finish
    (shape hypothesis p left output right sequence accumulator distributive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((lhs (h4-book-flatten-unfold-on-list p left sequence shape))
      (output-equation (h4-book-flatten-unfold-on-list p output sequence shape))
      (rhs (h4-book-flatten-rewrite-argument p right 1 output-equation))
      (sides (if hypothesis
                 (h4-book-flatten-map-accumulator-extend
                  p lhs rhs output-equation hypothesis distributive accumulator)
               (proof-with-checked-results
                ((output (h4-book-flatten-step-right output-equation))
                 (rhs (h4-book-flatten-chain-empty p rhs output)))
                (list lhs rhs))))
      (reversed (proof-proof-symmetric proof (cadr sides))))
     (proof-proof-chain proof (car sides) (list reversed)))))

(defun h4-book-flatten-map-accumulator (p mapper executable sequence accumulator)
  (let* ((left (list executable sequence accumulator))
         (output (list mapper sequence))
         (right (list *h4-book-flatten-revappend* output accumulator))
         (formula (proof-eq left right)))
    (proof-with-checked-results
     ((distributive (h4-book-flatten-revappend-after-append p))
      (shape (h4-book-flatten-list-shape p sequence t))
      (project (h4-book-flatten-unfold-on-list p output sequence shape))
      (piece-call (h4-book-flatten-step-right project)))
     (if (proof-is-call piece-call *h4-book-flatten-append*)
         (proof-with-checked-results ((piece (proof-term-at piece-call 1)))
           (let* ((saved (list *h4-book-flatten-revappend* piece accumulator))
                  (changes (list (list accumulator saved))))
             (proof-with-checked-results
              ((shape (h4-book-flatten-list-shape p sequence t))
               (hypothesis (h4-book-flatten-cdr-induction-recurse
                            shape p formula sequence changes))
               (step (h4-book-flatten-map-accumulator-finish
                      shape hypothesis p left output right sequence accumulator distributive))
               (shape (h4-book-flatten-list-shape p sequence nil))
               (base (h4-book-flatten-map-accumulator-finish
                      shape nil p left output right sequence accumulator distributive)))
              (h4-book-flatten-cdr-induction p formula sequence base step changes))))
       '(:failure "InapplicableStep" "")))))

(defun h4-book-flatten-map-after-list-fix-finish (shape hypothesis p fixed left right)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((fixation (h4-book-flatten-unfold-on-list p fixed *library-x* shape))
      (lhs (h4-book-flatten-rewrite-argument p left 1 fixation))
      (call (h4-book-flatten-step-right lhs))
      (sequence (h4-book-flatten-step-right fixation))
      (opened (h4-book-flatten-unfold-on-list p call sequence nil))
      (lhs (proof-proof-chain proof lhs (list opened)))
      (lhs (if hypothesis (proof-proof-rewrite proof lhs hypothesis '(1 2 2)) lhs))
      (rhs (h4-book-flatten-unfold-on-list p right *library-x* shape))
      (rhs (proof-proof-symmetric proof rhs)))
     (proof-proof-chain proof lhs (list rhs)))))

(defun h4-book-flatten-map-after-list-fix (p mapper)
  (let* ((fixed (list *h4-book-flatten-list-fix* *library-x*))
         (left (list mapper fixed))
         (right (list mapper *library-x*))
         (formula (proof-eq left right)))
    (proof-with-checked-results
     ((shape (h4-book-flatten-list-shape p *library-x* t))
      (hypothesis (h4-book-flatten-cdr-induction-recurse shape p formula *library-x* nil))
      (step (h4-book-flatten-map-after-list-fix-finish shape hypothesis p fixed left right))
      (shape (h4-book-flatten-list-shape p *library-x* nil))
      (base (h4-book-flatten-map-after-list-fix-finish shape nil p fixed left right)))
     (h4-book-flatten-cdr-induction p formula *library-x* base step nil))))

(defun h4-book-flatten-equivalence-shape (premise goal)
  (if (and (proof-is-call premise *h4-book-flatten-list-equiv*)
           (proof-is-call goal *proof-equal*))
      (proof-with-checked-results
       ((variables (proof-list-of-length (cdr premise) 2))
        (sides (proof-list-of-length (cdr goal) 2)))
       (let ((x (car variables))
             (y (cadr variables))
             (first (car sides))
             (last (cadr sides)))
         (and (proof-compound first)
              (proof-with-checked-results ((mapper (proof-term-at first 0)))
                (and (not (proof-compound mapper))
                     (= (len first) 2)
                     (equal (cadr first) x)
                     (equal last (list mapper y))
                     (list "equivalence" mapper x y))))))
    nil))

(defun h4-book-flatten-concatenation-shape (first last)
  (if (and (= (len first) 2) (proof-is-call (cadr first) *h4-book-flatten-append*))
      (proof-with-checked-results ((variables (proof-list-of-length (cdadr first) 2)))
        (let ((mapper (car first))
              (x (car variables))
              (y (cadr variables)))
          (and (not (proof-compound x))
               (equal last (list *h4-book-flatten-append* (list mapper x) (list mapper y)))
               (list "concatenation" mapper x y))))
    nil))

(defun h4-book-flatten-accumulator-shape (first last)
  (and (equal (len first) 3) (proof-is-call last *h4-book-flatten-revappend*)
       (proof-with-checked-results ((mapped (proof-term-at last 1)))
         (and (proof-compound mapped) (equal (len mapped) 2)
              (proof-with-checked-results ((accumulator (proof-term-at last 2)))
                (let ((sequence (cadr mapped)))
                  (and (equal (cdr first) (list sequence accumulator))
                       (not (proof-compound sequence))
                       (not (proof-compound accumulator))
                       (list "accumulator" (car mapped) (car first) sequence accumulator))))))))

(defun h4-book-flatten-append-map-shape (formula)
  (cond
   ((proof-is-call formula *library-implies*)
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
      (h4-book-flatten-equivalence-shape (car parts) (cadr parts))))
   ((proof-is-call formula *proof-equal*)
    (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((first (car sides))
            (last (cadr sides)))
        (and (proof-compound first)
             (proof-with-checked-results ((mapper (proof-term-at first 0)))
               (and (not (proof-compound mapper))
                    (or (h4-book-flatten-concatenation-shape first last)
                        (h4-book-flatten-accumulator-shape first last))))))))
   (t nil)))

(defun h4-book-flatten-append-map-equivalence (p formula mapper x y)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((fixed (h4-book-flatten-map-after-list-fix p mapper))
      (guard (proof-proof-assume proof (cadr formula) t))
      (premise (proof-step-first guard))
      (opened (proof-proof-unfold proof premise))
      (body (h4-book-flatten-step-right opened))
      (normalized (h4-book-flatten-normalize p body nil nil nil))
      (opened (proof-proof-chain proof opened (list normalized)))
      (equality (proof-proof-rewrite proof guard opened '(1)))
      (equality-literal (proof-step-first equality))
      (argument (proof-term-at equality-literal 1))
      (lifted (h4-book-flatten-rewrite-argument p (list mapper argument) 1 equality))
      (before (proof-proof-instantiate proof fixed (list (list *library-x* x))))
      (before (proof-proof-symmetric proof before))
      (after (proof-proof-instantiate proof fixed (list (list *library-x* y))))
      (related (proof-proof-chain proof before (list lifted after))))
     (h4-book-flatten-imply p formula related))))

(defun h4-book-flatten-append-map-try (p formula shape definitions)
  (let ((mode (car shape))
        (mapper (cadr shape))
        (parts (cddr shape)))
    (proof-with-checked-results
     ((shape (h4-book-flatten-list-shape p *library-x* t))
      (opened (h4-book-flatten-unfold-on-list p (list mapper *library-x*) *library-x* shape))
      (active (h4-book-flatten-step-right opened)))
     (and (proof-is-call active *h4-book-flatten-append*)
          (proof-with-checked-results ((tail (proof-term-at active 2)))
            (and (equal tail (list mapper (list *library-cdr* *library-x*)))
                 (cond
                  ((equal mode "concatenation")
                   (h4-book-flatten-concat-map p mapper (car parts) (cadr parts)))
                  ((equal mode "accumulator")
                   (and (assoc-equal (car parts) definitions)
                        (h4-book-flatten-map-accumulator p mapper
                                                        (car parts) (cadr parts) (caddr parts))))
                  (t (and (assoc-equal *h4-book-flatten-list-equiv* definitions)
                          (h4-book-flatten-append-map-equivalence
                           p formula mapper (car parts) (cadr parts)))))))))))

(defun h4-book-flatten-append-map-proof (p formula)
  (proof-with-checked-results ((shape (h4-book-flatten-append-map-shape formula)))
    (let* ((definitions (proof-proof-definitions (library-library-proof p)))
           (definition (and shape (assoc-equal (cadr shape) definitions))))
      (and definition (equal (len (cadr definition)) 1)
           (let ((result (h4-book-flatten-append-map-try p formula shape definitions)))
             (if (and (failure-p result)
                      (member-equal (cadr result) '("InapplicableStep" "assertion")))
                 nil
               result))))))
