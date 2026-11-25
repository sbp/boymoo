(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro b2-sorting-declare-events ()
  '(progn

(defconst *b2-sorting-sort* (proof-sym "SORT-SYMBOL-LISTP" "ACL2"))
(defconst *b2-sorting-merge* (proof-sym "STRICT-MERGE-SYMBOL<" "ACL2"))
(defconst *b2-sorting-merge-sort* (proof-sym "STRICT-MERGE-SORT-SYMBOL<" "ACL2"))
(defconst *b2-sorting-evens* (proof-sym "EVENS" "ACL2"))
(defconst *b2-sorting-odds* (proof-sym "ODDS" "ACL2"))
(defconst *b2-sorting-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *b2-sorting-revappend* (proof-cl "REVAPPEND"))
(defconst *b2-sorting-bit* (proof-sym "B2-MEMBER-BOOLEAN" "ACL2"))
(defconst *b2-sorting-item* (proof-sym "A" "ACL2"))

(defun b2-sorting-bit (item lst)
  (list *b2-sorting-bit* item lst))

(defun b2-sorting-either-fold (earlier term)
  (if (endp earlier)
      term
    (b2-sorting-either-fold (cdr earlier)
                            (proof-ite (car earlier) *proof-true* term))))

(defun b2-sorting-either (terms)
  (let ((reversed (reverse terms)))
    (if (endp reversed)
        '(:failure "tactic-rejected" "")
      (b2-sorting-either-fold (cdr reversed) (car reversed)))))

(defun b2-sorting-length (lst)
  (list *library-len* lst))

(defun b2-sorting-require-step (step)
  (or step '(:failure "failure" "")))

(defun b2-sorting-step-argument (step index)
  (proof-with-checked-results
      ((step (b2-sorting-require-step step))
       (literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b2-sorting-known (known term)
  (let ((entry (assoc-equal term known)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(mutual-recursion
 (defun b2-sorting-apply-equations-positions (node pattern path)
   (declare (xargs :measure (1+ (* 2 (acl2-count node)))))
   (cond ((equal node pattern) (list path))
         ((not (proof-compound node)) nil)
         ((endp node) '(:failure "tactic-rejected" ""))
         ((equal (car node) *proof-quote*) nil)
         (t (b2-sorting-apply-equations-position-arguments
             (cdr node) pattern path 1))))
 (defun b2-sorting-apply-equations-position-arguments (arguments pattern path index)
   (declare (xargs :measure (* 2 (acl2-count arguments))))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((here (b2-sorting-apply-equations-positions
                 (car arguments) pattern (append path (list index))))
          (later (b2-sorting-apply-equations-position-arguments
                  (cdr arguments) pattern path (1+ index))))
       (append here later)))))

(defun b2-sorting-apply-equations-rewrite (proof step rule places)
  (declare (xargs :measure (acl2-count places)))
  (if (endp places)
      step
    (proof-with-checked-results
        ((step (proof-proof-rewrite proof step rule (list* 1 2 (car places)))))
      (b2-sorting-apply-equations-rewrite proof step rule (cdr places)))))

(defun b2-sorting-apply-equations-rules (proof step rules)
  (declare (xargs :measure (acl2-count rules)))
  (if (endp rules)
      (proof-proof-tidy proof step)
    (proof-with-checked-results
        ((node (b2-sorting-step-argument step 2))
         (pattern (b2-sorting-step-argument (car rules) 1))
         (places (b2-sorting-apply-equations-positions node pattern nil))
         (step (b2-sorting-apply-equations-rewrite proof step (car rules) places)))
      (b2-sorting-apply-equations-rules proof step (cdr rules)))))

(defun b2-sorting-apply-equations (library formula rules)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results ((step (proof-proof-reflexive proof formula)))
      (b2-sorting-apply-equations-rules proof step rules))))

(mutual-recursion
 (defun b2-sorting-boolean-equality-atoms (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((proof-is-call term *proof-if*)
          (b2-sorting-boolean-equality-argument-atoms (cdr term)))
         ((or (equal term *proof-true*) (equal term *proof-false*)) nil)
         (t (list term))))
 (defun b2-sorting-boolean-equality-argument-atoms (arguments)
   (declare (xargs :measure (* 2 (acl2-count arguments))))
   (if (endp arguments)
       nil
     (append (b2-sorting-boolean-equality-atoms (car arguments))
             (b2-sorting-boolean-equality-argument-atoms (cdr arguments))))))

(defun b2-sorting-boolean-member-true (proof term held)
  (proof-with-checked-results
      ((equation (proof-proof-unfold proof term))
       (opened-fact (proof-proof-rewrite proof held equation '(1)))
       (opened-fact (proof-proof-tidy proof opened-fact))
       (parts (proof-proof-conjunct proof opened-fact))
       (body (b2-sorting-step-argument equation 2))
       (selected (proof-proof-select proof body (car parts))))
    (proof-proof-chain proof equation (list selected))))

(defun b2-sorting-boolean-equality-evaluate (index assignments library goal leaves)
  (declare (xargs :measure (nfix (- (len leaves) (ifix index)))))
  (let ((count (len leaves)))
    (cond
     ((equal index count)
      (b2-tactics-tactics-solve library goal nil nil assignments 0 nil))
     ((< (ifix index) (- count))
      '(:failure "tactic-rejected" ""))
     ((not (o< (nfix (- count (ifix (1+ index)))) (nfix (- count (ifix index)))))
      '(:failure "tactic-rejected" ""))
     (t
      (proof-with-checked-results
          ((term (proof-term-at leaves (if (< index 0) (+ count index) index)))
           (proof (library-library-proof library))
           (held (proof-proof-assume proof term t))
           (yes (if (proof-is-call term *b2-sorting-bit*)
                    (b2-sorting-boolean-member-true proof term held)
                  (b2-tactics-tactics-truth-value library term t held)))
           (no (b2-tactics-tactics-truth-value library term nil nil))
           (yes-case (b2-sorting-boolean-equality-evaluate
                      (1+ index) (append assignments (list yes)) library goal leaves))
           (no-case (b2-sorting-boolean-equality-evaluate
                     (1+ index) (append assignments (list no)) library goal leaves)))
        (proof-proof-cases proof term yes-case no-case))))))

(defun b2-sorting-boolean-equality (library formula rules)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((opened (b2-sorting-apply-equations library formula rules))
         (goal (b2-sorting-step-argument opened 2))
         (left (proof-term-at goal 1))
         (right (proof-term-at goal 2))
         (step (if (equal left right)
                   (proof-proof-reflexive proof left)
                 (b2-sorting-boolean-equality-evaluate
                  0 nil library goal
                  (proof-unique (b2-sorting-boolean-equality-argument-atoms (cdr goal)))))))
      (proof-proof-transport proof step opened))))

(defun b2-sorting-member-view (library item lst premise)
  (let ((proof (library-library-proof library))
        (raw (list *b2-sorting-member* item lst))
        (result (b2-sorting-bit item lst)))
    (proof-with-checked-results ((literal (proof-step-first premise)))
      (if (not (equal literal (list *proof-consp* lst)))
          (b2-tactics-tactics-normalize library result (list premise)
                                       (list raw result) nil 1500 nil)
        (proof-with-checked-results
            ((opened (b2-tactics-tactics-normalize library raw (list premise)
                                                   (list raw) nil 1500 nil))
             (body (b2-sorting-step-argument opened 2))
             (branches (if (integerp body)
                           '(:failure "tactic-rejected" "")
                         (proof-list-of-length (cdr body) 3)))
             (test (car branches))
             (rest (caddr branches))
             (raw-tail (proof-term-at rest 2))
             (reduced-tail (b2-tactics-tactics-normalize library raw-tail nil
                                                          nil nil 1500 nil))
             (tail-argument (if reduced-tail (b2-sorting-step-argument reduced-tail 2)
                              raw-tail))
             (tail (b2-sorting-bit item tail-argument))
             (goal (proof-eq result (proof-ite test *proof-true* tail)))
             (nonnil (b2-tactics-tactics-from-impossible library lst premise
                                                         nil nil nil 1500 nil))
             (yes (proof-proof-assume proof test t))
             (no (proof-proof-assume proof test nil))
             (good (b2-tactics-tactics-solve library goal (list premise nonnil yes)
                                             (list raw result tail) nil 0 nil))
             (bad (b2-tactics-tactics-solve library goal (list premise no)
                                            (list raw result tail) nil 0 nil)))
          (proof-proof-cases proof test good bad))))))

(defun b2-sorting-member-cons (library item pair)
  (if (integerp pair)
      '(:failure "tactic-rejected" "")
    (proof-with-checked-results
        ((fact (proof-proof-fact (library-library-proof library) "consp-cons"
                                 (seq-zip (list *library-x* *library-y*) (cdr pair)))))
      (b2-sorting-member-view library item pair fact))))

(defun b2-sorting-merge-descent (library arguments measure known)
  (if (integerp arguments)
      '(:failure "tactic-rejected" "")
    (let ((new-lengths (if (endp arguments)
                           nil
                         (cons (b2-sorting-length (car arguments))
                               (if (consp (cdr arguments))
                                   (list (b2-sorting-length (cadr arguments)))
                                 nil)))))
      (proof-with-checked-results
          ((left (proof-term-at arguments 0))
           (left-step
            (if (equal left *library-x*)
                nil
              (proof-with-checked-results
                  ((evidence (b2-sorting-known known (list *proof-consp* *library-x*)))
                   (reduced (library-library-cite library "LEN-CDR-LESS"
                                                   (list *library-x*) (list evidence)))
                   (offset (proof-term-at new-lengths 1)))
                (descent-shift library reduced offset nil))))
           (right (proof-term-at arguments 1))
           (right-step
            (if (equal right *library-y*)
                nil
              (proof-with-checked-results
                  ((evidence (b2-sorting-known known (list *proof-consp* *library-y*)))
                   (reduced (library-library-cite library "LEN-CDR-LESS"
                                                   (list *library-y*) (list evidence))))
                (descent-shift library reduced (b2-sorting-length *library-x*) t))))
           (comparison
            (cond ((and left-step right-step)
                   (library-library-compare-chain library left-step right-step))
                  ((or left-step right-step) (or left-step right-step))
                  (t '(:failure "tactic-rejected" ""))))
           (ordinal (library-library-ordinal-comparison
                     library (library-plus (car new-lengths) (cadr new-lengths)) measure)))
        (proof-proof-transport (library-library-proof library) comparison ordinal)))))

(defmacro b2-sorting-on-list (lib formula variable extra advance base)
  `(proof-with-checked-results
       ((advance-request (b2-tactics-tactics-on-list ,lib ,formula ,variable
                                                   nil nil ,extra))
        (advance-step (,(car advance)
                       (cadddr (car advance-request))
                       (car (cddddr (car advance-request)))
                       ,@(cdr advance)))
        (advance-reply (cons advance-step (cdr advance-request)))
        (base-request (b2-tactics-tactics-on-list ,lib ,formula ,variable
                                                nil advance-reply ,extra))
        (base-step (,(car base) (cadddr (car base-request)) ,@(cdr base))))
     (b2-tactics-tactics-on-list ,lib ,formula ,variable
                                (cons base-step (cdr base-request)) advance-reply ,extra)))

(defun b2-sorting-partition-length-length-base (atom library length-goal)
  (b2-tactics-tactics-solve library length-goal (list atom)
                           (list *b2-sorting-evens* *b2-sorting-odds* *library-len*)
                           nil 0 nil))

(defun b2-sorting-partition-length-length-advance
    (cons-step hypothesis library first second second-tail length-goal)
  (let ((proof (library-library-proof library))
        (total (b2-sorting-length *library-x*)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof second-tail))
         (use (proof-proof-rewrite-first proof hypothesis opened))
         (left (b2-tactics-tactics-normalize library total (list cons-step)
                                            (list total) (list use) 1500 nil))
         (goal-right (proof-term-at length-goal 2))
         (right (b2-tactics-tactics-normalize
                 library goal-right (list cons-step)
                 (list first second (b2-sorting-length first)) nil 1500 nil))
         (left-normal (b2-sorting-step-argument left 2))
         (right-normal (b2-sorting-step-argument right 2))
         (reorder (b2-tactics-tactics-linear-equal library left-normal right-normal nil))
         (symmetric (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list reorder symmetric)))))

(defun b2-sorting-partition-length (library)
  (let ((name (proof-sym "B2-EVENS-ODDS-LENGTH" "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof library)))
        (cons name library)
      (let* ((first (list *b2-sorting-evens* *library-x*))
             (second (list *b2-sorting-odds* *library-x*))
             (second-tail (list *b2-sorting-odds* (list *library-cdr* *library-x*)))
             (length-goal (proof-eq (b2-sorting-length *library-x*)
                                    (library-plus (b2-sorting-length first)
                                                  (b2-sorting-length second)))))
        (proof-with-checked-results
            ((result (b2-sorting-on-list
                      library length-goal *library-x* nil
                      (b2-sorting-partition-length-length-advance
                       library first second second-tail length-goal)
                      (b2-sorting-partition-length-length-base library length-goal))))
          (b2-tactics-tactics-add-lemma (cdr result) "EVENS-ODDS-LENGTH"
                                       (car result) :none))))))

(defun b2-sorting-partition-base (atom library membership-goal)
  (proof-with-checked-results
      ((reduced (b2-tactics-tactics-normalize
                 library (b2-sorting-bit *b2-sorting-item* *proof-false*) nil
                 (list *b2-sorting-bit* *b2-sorting-member*) nil 1500 nil)))
    (b2-tactics-tactics-solve
     library membership-goal (list atom)
     (list *b2-sorting-evens* *b2-sorting-odds* *b2-sorting-bit*
           (list *b2-sorting-member* *b2-sorting-item* *library-x*))
     (list reduced) 0 nil)))

(defun b2-sorting-partition-advance
    (cons-step hypothesis library first second second-tail membership-goal)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((unfolded (b2-tactics-tactics-normalize library first (list cons-step)
                                                (list first) nil 1500 nil))
         (pair (b2-sorting-step-argument unfolded 2))
         (member (b2-sorting-member-cons library *b2-sorting-item* pair))
         (symmetric (proof-proof-symmetric proof unfolded))
         (use-first (proof-proof-rewrite-first proof member symmetric))
         (opened-tail (proof-proof-unfold proof second-tail))
         (use-right (proof-proof-rewrite-first proof hypothesis opened-tail))
         (direct (b2-sorting-member-view library *b2-sorting-item* *library-x* cons-step))
         (opened-second (proof-proof-unfold proof second)))
      (b2-sorting-boolean-equality library membership-goal
                                   (list direct use-right use-first opened-second)))))

(defun b2-sorting-partition (library)
  (proof-with-checked-results ((size (b2-sorting-partition-length library)))
    (let* ((library (cdr size))
           (first (list *b2-sorting-evens* *library-x*))
           (second (list *b2-sorting-odds* *library-x*))
           (second-tail (list *b2-sorting-odds* (list *library-cdr* *library-x*)))
           (membership-goal
            (proof-eq (b2-sorting-bit *b2-sorting-item* *library-x*)
                      (b2-sorting-either (list (b2-sorting-bit *b2-sorting-item* first)
                                              (b2-sorting-bit *b2-sorting-item* second))))))
      (proof-with-checked-results
          ((result (b2-sorting-on-list
                    library membership-goal *library-x* nil
                    (b2-sorting-partition-advance library first second second-tail
                                                 membership-goal)
                    (b2-sorting-partition-base library membership-goal)))
           (elements (b2-tactics-tactics-add-lemma (cdr result) "EVENS-ODDS-MEMBERSHIP"
                                                   (car result) :none)))
        (cons (list (car size) (car elements)) (cdr elements))))))

(defun b2-sorting-reverse-append-base (atom library call goal)
  (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize library call (list atom)
                                               (list call) nil 1500 nil))
       (member (b2-sorting-member-view library *b2-sorting-item* *library-x* atom)))
    (b2-sorting-boolean-equality library goal (list equation member))))

(defun b2-sorting-reverse-append-advance (cons-step hypothesis library call goal pair)
  (proof-with-checked-results
      ((opened (b2-tactics-tactics-normalize library call (list cons-step)
                                             (list call) nil 1500 nil))
       (member (b2-sorting-member-view library *b2-sorting-item* *library-x* cons-step))
       (member-pair (b2-sorting-member-cons library *b2-sorting-item* pair)))
    (b2-sorting-boolean-equality library goal (list opened hypothesis member member-pair))))

(defun b2-sorting-reverse-append (library)
  (let* ((call (list *b2-sorting-revappend* *library-x* *library-y*))
         (goal (proof-eq (b2-sorting-bit *b2-sorting-item* call)
                         (b2-sorting-either
                          (list (b2-sorting-bit *b2-sorting-item* *library-x*)
                                (b2-sorting-bit *b2-sorting-item* *library-y*)))))
         (pair (list *proof-cons* (list *library-car* *library-x*) *library-y*)))
    (proof-with-checked-results
        ((result (b2-sorting-on-list
                  library goal *library-x* (list (list *library-y* pair))
                  (b2-sorting-reverse-append-advance library call goal pair)
                  (b2-sorting-reverse-append-base library call goal))))
      (b2-tactics-tactics-add-lemma (cdr result) "REVAPPEND-MEMBERSHIP"
                                   (car result) :none))))

(defun b2-sorting-assumptions (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
        ((parts (proof-list-of-length (car signed) 2))
         (step (proof-proof-assume proof (car parts) (cadr parts)))
         (rest (b2-sorting-assumptions proof (cdr signed))))
      (cons step rest))))

(defun b2-sorting-changed-bindings (parents actuals)
  (if (or (endp parents) (endp actuals))
      nil
    (if (equal (car parents) (car actuals))
        (b2-sorting-changed-bindings (cdr parents) (cdr actuals))
      (cons (list (car parents) (car actuals))
            (b2-sorting-changed-bindings (cdr parents) (cdr actuals))))))

(defun b2-sorting-merge-membership-atom-rules (parents known library)
  (if (endp parents)
      nil
    (let ((evidence (assoc-equal (proof-neg (list *proof-consp* (car parents))) known)))
      (if evidence
          (proof-with-checked-results
              ((rule (b2-sorting-member-view library *b2-sorting-item*
                                             (car parents) (cdr evidence)))
               (rest (b2-sorting-merge-membership-atom-rules (cdr parents) known library)))
            (cons rule rest))
        (b2-sorting-merge-membership-atom-rules (cdr parents) known library)))))

(defun b2-sorting-merge-membership-child-rules (parents actuals known library)
  (declare (xargs :measure (len parents)))
  (cond ((not (o< (len (cdr parents)) (len parents))) nil)
        ((endp actuals) nil)
        ((equal (car parents) (car actuals))
         (b2-sorting-merge-membership-child-rules (cdr parents) (cdr actuals) known library))
        (t (proof-with-checked-results
               ((evidence (b2-sorting-known known (list *proof-consp* (car parents))))
                (rule (b2-sorting-member-view library *b2-sorting-item*
                                               (car parents) evidence))
                (rest (b2-sorting-merge-membership-child-rules
                       (cdr parents) (cdr actuals) known library)))
             (cons rule rest)))))

(defun b2-sorting-merge-membership-leaf
    (value signed library reverse-lemma call goal measure substitutions)
  (let ((proof (library-library-proof library))
        (parents (list *library-x* *library-y*)))
    (proof-with-checked-results
        ((evidence (b2-sorting-assumptions proof signed))
         (known (b2-tactics-tactics-evidence library evidence)))
      (if (proof-is-call value *b2-sorting-revappend*)
          (proof-with-checked-results
              ((tail (proof-term-at value 2))
               (rule (proof-proof-fact proof reverse-lemma
                                       (list (list *library-x* *library-z*)
                                             (list *library-y* tail))))
               (atom-rules (b2-sorting-merge-membership-atom-rules parents known library))
               (goal-side (proof-term-at goal 2))
               (result (b2-sorting-boolean-equality
                        library (proof-eq (b2-sorting-bit *b2-sorting-item* value) goal-side)
                        (cons rule atom-rules))))
            (cons result substitutions))
        (if (integerp value)
            '(:failure "tactic-rejected" "")
          (let* ((arguments (cdr value))
                 (bindings (b2-sorting-changed-bindings (cdr call) arguments))
                 (substitutions (append substitutions (list bindings))))
            (proof-with-checked-results
                ((decrease (b2-sorting-merge-descent library arguments measure known))
                 (hypothesis (b2-tactics-tactics-induction-hypothesis
                              library goal measure bindings decrease))
                 (child-rules (b2-sorting-merge-membership-child-rules
                               parents arguments known library))
                 (pair (proof-term-at arguments 2))
                 (member (b2-sorting-member-cons library *b2-sorting-item* pair))
                 (equality (assoc-equal (proof-eq (list *library-car* *library-x*)
                                                 (list *library-car* *library-y*))
                                        known))
                 (symmetric (if equality (proof-proof-symmetric proof (cdr equality)) nil))
                 (rules (cons hypothesis
                              (append child-rules
                                      (if equality (list member symmetric) (list member)))))
                 (goal-side (proof-term-at goal 2))
                 (result (b2-sorting-boolean-equality
                          library (proof-eq (b2-sorting-bit *b2-sorting-item* value) goal-side)
                          rules)))
              (cons result substitutions))))))))

(defun b2-sorting-merge-membership-by-value
    (n value template signed library reverse-lemma call goal measure substitutions)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof library)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-sorting-merge-membership-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (test (car branches))
           (yes (b2-sorting-merge-membership-by-value
                 (1- n) (cadr branches) template (append signed (list (list test t)))
                 library reverse-lemma call goal measure substitutions))
           (no (b2-sorting-merge-membership-by-value
                (1- n) (caddr branches) template (append signed (list (list test nil)))
                library reverse-lemma call goal measure (cdr yes)))
           (if-true (proof-proof-if-true proof value))
           (symmetric (proof-proof-symmetric proof if-true))
           (yes-step (proof-proof-rewrite-result proof (car yes) symmetric template *proof-result*))
           (if-false (proof-proof-if-false proof value))
           (symmetric (proof-proof-symmetric proof if-false))
           (no-step (proof-proof-rewrite-result proof (car no) symmetric template *proof-result*))
           (step (proof-proof-cases proof test yes-step no-step)))
        (cons step (cdr no))))
     ((null value) '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (body (b2-sorting-step-argument equality 2))
           (opened (b2-sorting-merge-membership-by-value
                    (1- n) body template signed library reverse-lemma call goal measure
                    substitutions))
           (symmetric (proof-proof-symmetric proof equality))
           (step (proof-proof-rewrite-result proof (car opened) symmetric template *proof-result*)))
        (cons step (cdr opened))))
     (t
      (proof-with-checked-results
          ((leaf (b2-sorting-merge-membership-leaf
                  value signed library reverse-lemma call goal measure substitutions))
           (literal (proof-step-first (car leaf)))
           (claim (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal claim)
            leaf
          '(:failure "tactic-rejected" "")))))))

(defun b2-sorting-merge-membership (library)
  (proof-with-checked-results ((reverse-lemma (b2-sorting-reverse-append library)))
    (let* ((library (cdr reverse-lemma))
           (proof (library-library-proof library))
           (call (list *b2-sorting-merge* *library-x* *library-y* *library-z*))
           (goal (proof-eq (b2-sorting-bit *b2-sorting-item* call)
                           (b2-sorting-either
                            (list (b2-sorting-bit *b2-sorting-item* *library-x*)
                                  (b2-sorting-bit *b2-sorting-item* *library-y*)
                                  (b2-sorting-bit *b2-sorting-item* *library-z*)))))
           (measure (library-plus (b2-sorting-length *library-x*)
                                  (b2-sorting-length *library-y*))))
      (proof-with-checked-results
          ((unfolded (proof-proof-unfold proof call))
           (template (proof-eq (b2-sorting-bit *b2-sorting-item* *proof-result*)
                               (caddr goal)))
           (body (b2-sorting-step-argument unfolded 2))
           (leaves (b2-sorting-merge-membership-by-value
                    1000000 body template nil library (car reverse-lemma) call goal measure nil))
           (symmetric (proof-proof-symmetric proof unfolded))
           (result (proof-proof-rewrite-result proof (car leaves) symmetric template *proof-result*))
           (natural (library-library-natural library measure))
           (ordinal (library-library-cite library "NATURAL-ORDINAL" (list measure) (list natural)))
           (step (proof-proof-induct proof ordinal result goal measure (cdr leaves))))
        (b2-tactics-tactics-add-lemma library "MERGE-MEMBERSHIP" step :none)))))

(defun b2-sorting-nontrivial-partition-positive (library branch source evidence)
  (let ((expression (list *b2-sorting-evens* source)))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize
                    library (b2-sorting-length branch) (list evidence)
                    (list branch expression *library-len*) nil 1500 nil))
         (opened (b2-sorting-step-argument equation 2))
         (child-size (proof-term-at opened 2))
         (natural (library-library-natural library child-size))
         (nonnegative (library-library-cite library "NATURAL-NONNEGATIVE"
                                             (list child-size) (list natural)))
         (integer-step (library-library-type-of library child-size nil))
         (positive (library-library-cite library "POSITIVE-ONE-PLUS"
                                          (list child-size) (list integer-step nonnegative))))
      (library-library-transport-argument library positive equation 2))))

(defun b2-sorting-nontrivial-partition-decrease (library part split positive-other total)
  (let ((length (b2-sorting-length part)))
    (proof-with-checked-results
        ((sum (b2-sorting-step-argument split 2))
         (difference (b2-tactics-tactics-less-from-difference library length sum positive-other nil))
         (strict (library-library-transport-argument library difference split 2))
         (ordinal (library-library-ordinal-comparison library length total)))
      (proof-proof-transport (library-library-proof library) strict ordinal))))

(defun b2-sorting-nontrivial-partition (library size nonempty-tail)
  (let ((proof (library-library-proof library))
        (tail (list *library-cdr* *library-x*))
        (consp-x (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((false-x (proof-proof-assume proof consp-x nil))
         (completion (library-library-axiom library "COMPLETION-OF-CDR" (list *library-x*)))
         (opened (b2-sorting-step-argument completion 2))
         (selection (proof-proof-select proof opened false-x))
         (completion (proof-proof-chain proof completion (list selection)))
         (impossible (proof-proof-rewrite proof nonempty-tail completion '(1 1)))
         (computed (proof-proof-compute proof (list *proof-consp* *proof-false*) *proof-nil*))
         (impossible (proof-proof-rewrite proof impossible computed '(1)))
         (impossible (proof-proof-tidy proof impossible))
         (nonempty (proof-proof-front proof impossible consp-x))
         (a (list *b2-sorting-evens* *library-x*))
         (b (list *b2-sorting-odds* *library-x*))
         (total (b2-sorting-length *library-x*))
         (split (proof-proof-fact proof size nil))
         (positive-a (b2-sorting-nontrivial-partition-positive library a *library-x* nonempty))
         (positive-b (b2-sorting-nontrivial-partition-positive library b tail nonempty-tail))
         (first (b2-sorting-nontrivial-partition-decrease library a split positive-b total))
         (second (b2-sorting-nontrivial-partition-decrease library b split positive-a total)))
      (list first second))))

(defun b2-sorting-merge-sort-membership-conclude (a-sign b-sign library a b formula fact)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((assume-a (proof-proof-assume proof a a-sign))
         (assume-b (proof-proof-assume proof b b-sign)))
      (let ((evidence (list assume-a assume-b)))
        (if (equal a-sign b-sign)
            (b2-tactics-tactics-solve library formula evidence nil nil 0 nil)
          (proof-with-checked-results
              ((literal (proof-step-first fact))
               (unfolded (b2-tactics-tactics-normalize library literal evidence
                                                      (list *b2-sorting-bit*) nil 1500 nil))
               (unfolded (b2-sorting-require-step unfolded))
               (conflict (proof-proof-rewrite proof fact unfolded '(1)))
               (conflict (proof-proof-tidy proof conflict)))
            (proof-proof-subsume proof conflict (cons formula (proof-step-clause conflict)))))))))

(defun b2-sorting-merge-sort-membership (library formula)
  (proof-with-checked-results
      ((library (library-library-definition
                 library *b2-sorting-bit* (list *b2-sorting-item* *library-x*)
                 (proof-ite (list *b2-sorting-member* *b2-sorting-item* *library-x*)
                            *proof-true* *proof-false*)))
       (partition (b2-sorting-partition library))
       (size (caar partition))
       (parts (cadar partition))
       (merged (b2-sorting-merge-membership (cdr partition))))
    (let* ((library (cdr merged))
           (proof (library-library-proof library))
           (call (list *b2-sorting-merge-sort* *library-x*))
           (goal (proof-eq (b2-sorting-bit *b2-sorting-item* call)
                           (b2-sorting-bit *b2-sorting-item* *library-x*)))
           (tail (list *library-cdr* *library-x*))
           (test (list *proof-consp* tail)))
      (proof-with-checked-results
          ((yes (proof-proof-assume proof test t))
           (no (proof-proof-assume proof test nil))
           (base (b2-tactics-tactics-solve library goal (list no) (list call) nil 0 nil))
           (measure (b2-sorting-length *library-x*))
           (left (list *b2-sorting-evens* *library-x*))
           (right (list *b2-sorting-odds* *library-x*))
           (substitutions (list (list (list *library-x* left)) (list (list *library-x* right))))
           (decreases (b2-sorting-nontrivial-partition library size yes))
           (left-hypothesis
            (b2-tactics-tactics-induction-hypothesis
             library goal measure (car substitutions) (car decreases)))
           (right-hypothesis
            (b2-tactics-tactics-induction-hypothesis
             library goal measure (cadr substitutions) (cadr decreases)))
           (opened (b2-tactics-tactics-normalize library call (list yes) (list call) nil 1500 nil))
           (combination (proof-proof-fact proof (car merged)
                                          (list (list *library-x* (list *b2-sorting-merge-sort* left))
                                                (list *library-y* (list *b2-sorting-merge-sort* right))
                                                (list *library-z* *proof-false*))))
           (empty (b2-tactics-tactics-normalize
                   library (b2-sorting-bit *b2-sorting-item* *proof-false*) nil
                   (list *b2-sorting-bit* *b2-sorting-member*) nil 1500 nil))
           (partition-fact (proof-proof-fact proof parts nil))
           (step (b2-sorting-boolean-equality
                  library goal (list opened combination left-hypothesis right-hypothesis
                                     empty partition-fact)))
           (natural (library-library-natural library measure))
           (ordinality (library-library-cite library "NATURAL-ORDINAL"
                                              (list measure) (list natural)))
           (branches (proof-proof-cases proof test step base))
           (fact (proof-proof-induct proof ordinality branches goal measure substitutions))
           (a (list *b2-sorting-member* *b2-sorting-item* call))
           (b (list *b2-sorting-member* *b2-sorting-item* *library-x*))
           (both (b2-sorting-merge-sort-membership-conclude t t library a b formula fact))
           (a-only (b2-sorting-merge-sort-membership-conclude t nil library a b formula fact))
           (yes (proof-proof-cases proof b both a-only))
           (b-only (b2-sorting-merge-sort-membership-conclude nil t library a b formula fact))
           (neither (b2-sorting-merge-sort-membership-conclude nil nil library a b formula fact))
           (no (proof-proof-cases proof b b-only neither))
           (result (proof-proof-cases proof a yes no)))
        (cons result library)))))

(defun b2-sorting-sort-wrapper (library name formula)
  (let ((proof (library-library-proof library))
        (membership (equal name (proof-sym "MEMBER-EQ-SORT-SYMBOL-LISTP" "ACL2"))))
    (proof-with-checked-results
        ((expression (proof-term-at formula (if membership 1 2)))
         (sorted-term (proof-term-at expression (if membership 2 1)))
         (opened (proof-proof-unfold proof sorted-term))
         (body (b2-sorting-step-argument opened 2))
         (test (proof-term-at body 1))
         (yes (proof-proof-assume proof test t))
         (no (proof-proof-assume proof test nil))
         (in-order (b2-tactics-tactics-solve library formula (list yes)
                                             (list sorted-term) nil 1 nil))
         (equation (b2-tactics-tactics-normalize library sorted-term (list no)
                                                 (list sorted-term) nil 1500 nil))
         (prior (proof-sym (if membership "MEMBER-EQ-STRICT-MERGE-SORT-SYMBOL<"
                             "STRICT-SYMBOL<-SORTEDP-STRICT-MERGE-SORT-SYMBOL<")
                           "ACL2"))
         (prior-fact (proof-proof-fact proof prior nil))
         (equation (b2-sorting-require-step equation))
         (symmetric (proof-proof-symmetric proof equation))
         (out-of-order (proof-proof-rewrite-first proof prior-fact symmetric)))
      (proof-proof-cases proof test in-order out-of-order))))
))
