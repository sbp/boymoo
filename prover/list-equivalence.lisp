(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *list-equivalence-iff* (proof-sym "IFF" "ACL2"))

(defun list-equivalence-list-equivalence-library (equivalence)
  (cadr equivalence))

(defun list-equivalence-list-equivalence-relation (equivalence)
  (caddr equivalence))

(defun list-equivalence-list-equivalence-equation (equivalence)
  (cadddr equivalence))

(defun list-equivalence-list-equivalence-name (equivalence)
  (nth 4 equivalence))

(defun list-equivalence-list-equivalence-cons-equation (equivalence)
  (nth 5 equivalence))

(defun list-equivalence-list-equivalence-atom-equation (equivalence)
  (nth 6 equivalence))

(defun list-equivalence-list-equivalence-relation-equation (equivalence call)
  (let* ((lib (list-equivalence-list-equivalence-library equivalence))
         (proof (library-library-proof lib)))
    (proof-with-checked-results ((name (proof-term-at call 0)))
      (let ((definition (assoc-equal name (proper-lists-definitions lib))))
        (proof-with-checked-results
            ((fits (and definition (book-logic-within-size (caddr definition) 80))))
          (if (not fits)
              *terms-unproved*
            (proof-with-checked-results
                ((opened (proof-proof-unfold proof call))
                 (value (proper-lists-first-right opened))
                 (reduced (proper-lists-reduce lib value nil nil nil 30 125)))
              (proof-proof-chain proof opened (list reduced)))))))))

(defun list-equivalence-list-equivalence-align-operands (equivalence equality operands shape position)
  (declare (xargs :measure (acl2-count operands)))
  (if (endp operands)
      equality
    (let ((proof (library-library-proof (list-equivalence-list-equivalence-library equivalence))))
      (proof-with-checked-results
          ((holds (proof-term-at shape 0))
           (spine (if holds
                      (list-equivalence-list-equivalence-cons-equation equivalence)
                    (list-equivalence-list-equivalence-atom-equation equivalence)))
           (equation (proof-proof-instantiate proof spine (list (list *library-x* (car operands)))))
           (rewritten (proof-proof-rewrite proof equality equation (list 1 position))))
        (list-equivalence-list-equivalence-align-operands
         equivalence rewritten (cdr operands) (cdr shape) (1+ position))))))

(defun list-equivalence-list-equivalence-align (equivalence premise left right shape)
  (let ((proof (library-library-proof (list-equivalence-list-equivalence-library equivalence))))
    (proof-with-checked-results
        ((named (proof-proof-instantiate proof
                                        (list-equivalence-list-equivalence-equation equivalence)
                                        (list (list *library-x* left) (list *library-y* right))))
         (equality (proof-proof-rewrite proof premise named '(1)))
         (aligned (list-equivalence-list-equivalence-align-operands
                   equivalence equality (list left right) shape 1)))
      (proof-proof-tidy proof aligned))))

(defun list-equivalence-list-equivalence-mismatch (equivalence equality)
  (let ((proof (library-library-proof (list-equivalence-list-equivalence-library equivalence))))
    (proof-with-checked-results
        ((formula (proof-step-first equality))
         (first (proof-term-at formula 1))
         (equality (if (equal first *proof-false*) (proof-proof-symmetric proof equality)
                     equality))
         (formula (proof-step-first equality))
         (parts (proof-list-of-length (cdr formula) 2))
         (left (car parts))
         (right (cadr parts))
         (cons-step (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdr left))))
         (impossible (proof-proof-rewrite proof cons-step equality '(1 1)))
         (value (proof-term-at right 1))
         (computed (proof-proof-compute proof (list *proof-consp* right) value))
         (rewritten (proof-proof-rewrite proof impossible computed '(1))))
      (proof-proof-tidy proof rewritten))))

(defun list-equivalence-list-equivalence-contents (equivalence equality left right)
  (let ((proof (library-library-proof (list-equivalence-list-equivalence-library equivalence))))
    (proof-with-checked-results
        ((formula (proof-step-first equality))
         (arguments (proof-list-of-length (cdr formula) 2))
         (first (car arguments))
         (second (cadr arguments))
         (rule (proof-proof-fact
                proof (proof-sym "CONS-EQUAL" "ACL2")
                (seq-zip (list (proof-sym "X1" "ACL2") (proof-sym "Y1" "ACL2")
                              (proof-sym "X2" "ACL2") (proof-sym "Y2" "ACL2"))
                        (append (cdr first) (cdr second)))))
         (rewritten (proof-proof-rewrite proof equality rule '(1)))
         (parts (proof-proof-conjunct proof rewritten))
         (tails (list (list-equivalence-list-equivalence-relation equivalence)
                      (list *library-cdr* left) (list *library-cdr* right)))
         (equation (list-equivalence-list-equivalence-relation-equation equivalence tails))
         (transported (proof-proof-transport proof (cadr parts) equation)))
      (list (car parts) transported))))

(defun list-equivalence-list-equivalence-record-lemma (equivalence label claim step conditions)
  (let ((lib (list-equivalence-list-equivalence-library equivalence)))
    (if (proper-lists-known-lemma-p lib label)
        ;; The entry is appended before checking for a duplicate fact.
        (let* ((name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
               (clause (cons claim conditions))
               (proof (library-library-proof lib))
               (entry (proof-with-checked-results
                          ((step (proof-proof-subsume proof step clause)))
                        (proof-proof-entry "lemma" name (cons name clause) (list step)))))
          (if (failure-p entry)
              (cons entry equivalence)
            (let ((updated (library-library-with-entries
                            lib (append (library-library-entries lib) (list entry)))))
              (cons '(:failure "failure" "") (update-nth 1 updated equivalence)))))
      (let ((updated (library-library-lemma lib label claim step conditions)))
        (if (failure-p updated)
            (cons updated equivalence)
          (cons nil (update-nth 1 updated equivalence)))))))

(defun list-equivalence-list-equivalence-add-branch (equivalence hypothesis left right holds suffix)
  (let* ((lib (list-equivalence-list-equivalence-library equivalence))
         (proof (library-library-proof lib))
         (name (list-equivalence-list-equivalence-name equivalence))
         (claim (if holds right (proof-neg right)))
         (guard (if holds (proof-neg left) left))
         (result (proof-with-checked-results
                     ((equality (list-equivalence-list-equivalence-align
                                 equivalence hypothesis *library-x* *library-y*
                                 (list holds (not holds))))
                      (mismatch (list-equivalence-list-equivalence-mismatch equivalence equality))
                      (step (proof-proof-front proof mismatch claim))
                      (hypothesis-term (proof-step-first hypothesis)))
                   (list-equivalence-list-equivalence-record-lemma
                    equivalence (concatenate 'string name suffix) claim step
                    (list (proof-neg hypothesis-term) guard)))))
    (if (failure-p result) (cons result equivalence) result)))

(defun list-equivalence-list-equivalence-add-contents (equivalence steps suffixes conditions)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      (cons nil equivalence)
    (let* ((name (list-equivalence-list-equivalence-name equivalence))
           (result (proof-with-checked-results ((claim (proof-step-first (car steps))))
                     (list-equivalence-list-equivalence-record-lemma
                      equivalence (concatenate 'string name (car suffixes))
                      claim (car steps) conditions))))
      (cond ((failure-p result) (cons result equivalence))
            ((car result) result)
            (t
             (list-equivalence-list-equivalence-add-contents
              (cdr result) (cdr steps) (cdr suffixes) conditions))))))

(defun list-equivalence-list-equivalence-lemmas (equivalence)
  (let* ((lib (list-equivalence-list-equivalence-library equivalence))
         (name (list-equivalence-list-equivalence-name equivalence))
         (proof (library-library-proof lib)))
    (if (proper-lists-known-lemma-p lib (concatenate 'string name "-TAILS"))
        (cons nil equivalence)
      (let* ((hypothesis
              (proof-proof-assume proof
                                  (list (list-equivalence-list-equivalence-relation equivalence)
                                        *library-x* *library-y*) t))
             (left (list *proof-consp* *library-x*))
             (right (list *proof-consp* *library-y*))
             (cons-result (if (failure-p hypothesis)
                              (cons hypothesis equivalence)
                            (list-equivalence-list-equivalence-add-branch
                             equivalence hypothesis left right t "-CONS"))))
        (if (car cons-result)
            cons-result
          (let* ((atom-result (list-equivalence-list-equivalence-add-branch
                               (cdr cons-result) hypothesis left right nil "-ATOM"))
                 (atom-branch (cdr atom-result)))
            (if (car atom-result)
                atom-result
              (let ((result
                     (proof-with-checked-results
                         ((equality (list-equivalence-list-equivalence-align
                                     atom-branch hypothesis *library-x* *library-y* '(t t)))
                          (parts (list-equivalence-list-equivalence-contents
                                  atom-branch equality *library-x* *library-y*))
                          (hypothesis-term (proof-step-first hypothesis)))
                       (list-equivalence-list-equivalence-add-contents
                        atom-branch parts '("-HEADS" "-TAILS")
                        (list (proof-neg hypothesis-term) (proof-neg left) (proof-neg right))))))
                (if (failure-p result)
                    (cons result atom-branch)
                  result)))))))))

(defun list-equivalence-list-equivalence-spine (lib left test holds fixer expected)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premise (proof-proof-assume proof test holds))
         (equation (proper-lists-reduce lib left (list premise) (list fixer) nil 38 150)))
      (if (not equation)
          *terms-unproved*
        (proof-with-checked-results ((value (proper-lists-first-right equation)))
          (if (equal value expected)
              equation
            *terms-unproved*))))))

(defun list-equivalence-list-equivalence-prepare (lib relation)
  (let ((equivalence (list :list-equivalence lib relation nil nil nil nil)))
    (proof-with-checked-results
        ((equation (list-equivalence-list-equivalence-relation-equation
                    equivalence (list relation *library-x* *library-y*)))
         (equality (proper-lists-first-right equation)))
      (if (not (proof-is-call equality *proof-equal*))
          *terms-unproved*
        (let ((bad-equality (proper-lists-check-arity (cdr equality) 2))
              (left (cadr equality))
              (right (caddr equality)))
          (cond (bad-equality bad-equality)
                ((and (proof-compound left) (proof-compound right) (endp left))
                 '(:failure "failure" ""))
                ((not (and (proof-compound left) (proof-compound right)
                           (assoc-equal (car left) (proper-lists-definitions lib))))
                 *terms-unproved*)
                ((endp right) '(:failure "failure" ""))
                ((not (and (equal (car left) (car right)) (equal (cdr left) (list *library-x*))
                           (equal (cdr right) (list *library-y*))))
                 *terms-unproved*)
                (t
                 (let* ((fixer (car left))
                        (test (list *proof-consp* *library-x*))
                        (expected (list *proof-cons* (list *library-car* *library-x*)
                                        (list fixer (list *library-cdr* *library-x*)))))
                   (proof-with-checked-results
                       ((formula (proof-step-first equation))
                        (name (proper-lists-hash-name "LIST-SPINE-" formula))
                        (cons-equation (list-equivalence-list-equivalence-spine
                                        lib left test t fixer expected))
                        (atom-equation (list-equivalence-list-equivalence-spine
                                        lib left test nil fixer *proof-false*)))
                     (list :list-equivalence lib relation equation name
                           cons-equation atom-equation))))))))))

(defun list-equivalence-list-equivalence-new-result (lib relation)
  (let ((equivalence (list-equivalence-list-equivalence-prepare lib relation)))
    (if (failure-p equivalence)
        (cons equivalence lib)
      (let* ((result (list-equivalence-list-equivalence-lemmas equivalence))
             (answer (car result))
             (equivalence (cdr result)))
        (cons (or answer equivalence)
              (list-equivalence-list-equivalence-library equivalence))))))

(defun list-equivalence-paired-substitutions-terms (lib terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((reduced (proper-lists-reduce lib (car terms) nil nil nil 30 110))
         (term (if reduced (proper-lists-first-right reduced) (car terms)))
         (rest (list-equivalence-paired-substitutions-terms lib (cdr terms))))
      (cons term rest))))

(defun list-equivalence-paired-substitutions-positions (first second position)
  (declare (xargs :measure (acl2-count first)))
  (if (or (endp first) (endp second))
      nil
    (let* ((different (not (equal (car first) (car second))))
           (rest (list-equivalence-paired-substitutions-positions (cdr first) (cdr second)
                                                                 (1+ position))))
      (if different
          (cons (list position (car first) (car second)) rest)
        rest))))

(defun list-equivalence-pair-bindings (keys values result)
  (declare (xargs :measure (acl2-count keys)))
  (if (or (endp keys) (endp values))
      result
    (list-equivalence-pair-bindings
     (cdr keys) (cdr values) (table-put result (car keys) (car values)))))

(defun list-equivalence-paired-substitutions-call (actuals here)
  (declare (xargs :measure (acl2-count actuals)))
  (if (endp actuals)
      nil
    (proof-with-checked-results
        ((term (proof-subst (car actuals) here))
         (rest (list-equivalence-paired-substitutions-call (cdr actuals) here)))
      (cons term rest))))

(defun list-equivalence-paired-substitutions-extras (old new left right extras)
  (declare (xargs :measure (acl2-count old)))
  (if (or (endp old) (endp new))
      extras
    (let ((original (car old))
          (replacement (car new)))
      (list-equivalence-paired-substitutions-extras
       (cdr old) (cdr new) left right
       (if (or (equal original replacement) (proof-compound original)
               (equal original left) (equal original right))
           extras
         (table-put extras original replacement))))))

(defun list-equivalence-paired-substitutions-binding (invocation position here arguments left right)
  (proof-with-checked-results
      ((call (list-equivalence-paired-substitutions-call
              (termination-call-actuals invocation) here))
       (recursive-argument (proof-term-at call position))
       (tail (list *library-cdr* right)))
    (and (equal recursive-argument tail)
         (table-items
          (list-equivalence-paired-substitutions-extras
           arguments call left right (list (cons right tail)))))))

(defun list-equivalence-paired-substitutions-plan (lib conclusion left right)
  (proof-with-checked-results
      ((terms (list-equivalence-paired-substitutions-terms lib (cdr conclusion)))
       (parts (proof-list-of-length terms 2))
       (first (car parts))
       (second (cadr parts)))
    (cond ((not (and (proof-compound first) (proof-compound second))) nil)
          ((or (endp first) (endp second)) '(:failure "failure" ""))
          ((not (equal (car first) (car second))) nil)
          (t
           (let ((definition (assoc-equal (car first) (proper-lists-definitions lib))))
             (and definition
                  (let ((positions (list-equivalence-paired-substitutions-positions
                                    (cdr first) (cdr second) 0)))
                    (and (equal (len positions) 1)
                         (equal (cdar positions) (list left right))
                         (let ((here (list-equivalence-pair-bindings
                                      (cadr definition) (cdr second) nil)))
                           (proof-with-checked-results
                               ((calls (termination-recursive-calls
                                        *termination-all* (list definition))))
                             (list calls (caar positions) here (cdr second))))))))))))

(defun list-equivalence-paired-reduction-reduce (term lib evidence definitions)
  (proof-with-checked-results
      ((opened (proper-lists-reduce lib term evidence definitions nil 68 185)))
    (or opened (proof-proof-reflexive (library-library-proof lib) term))))

(defun list-equivalence-paired-reduction (lib goal evidence)
  (let ((left (cadr goal))
        (right (caddr goal))
        (proof (library-library-proof lib)))
    (cond ((not (proof-is-call goal *proof-equal*)) nil)
          ((not (equal (len goal) 3)) (proper-lists-check-arity (cdr goal) 2))
          ((not (and (proof-compound left) (proof-compound right))) nil)
          ((or (endp left) (endp right)) '(:failure "failure" ""))
          ((not (and (equal (car left) (car right))
                     (assoc-equal (car left) (proper-lists-definitions lib))))
           nil)
          (t
           (let ((definitions (list (car left) (proof-cl "ATOM") (proof-cl "ENDP")
                                    *proof-not*)))
             (proof-with-checked-results
                 ((first (list-equivalence-paired-reduction-reduce left lib evidence definitions))
                  (second (list-equivalence-paired-reduction-reduce right lib evidence definitions))
                  (first-value (proper-lists-first-right first))
                  (second-value (proper-lists-first-right second)))
               (and (equal first-value second-value)
                    (proof-with-checked-results ((reversed (proof-proof-symmetric proof second)))
                      (proof-proof-chain proof first (list reversed))))))))))

(defun list-equivalence-prove-list-equivalence-instances (lib calls position here arguments
                                                             induction left right descent tails)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      (cons nil induction)
    (proof-with-checked-results
        ((extra (list-equivalence-paired-substitutions-binding
                 (car calls) position here arguments left right)))
      (if (not extra)
          (list-equivalence-prove-list-equivalence-instances
           lib (cdr calls) position here arguments induction left right descent tails)
        (proof-with-checked-results
            ((instance (book-logic-tree-induction-at induction (list *library-cdr* left)
                                                    descent extra))
             (hypothesis (car instance))
             (step (proof-proof-modus-ponens (library-library-proof lib) hypothesis tails))
             (rest (list-equivalence-prove-list-equivalence-instances
                    lib (cdr calls) position here arguments (cdr instance)
                    left right descent tails)))
          (cons (cons step (car rest)) (cdr rest)))))))

(defun list-equivalence-prove-list-equivalence-cons-evidence (lib goal left right name
                                                                hypothesis signed other induction)
  (let ((proof (library-library-proof lib))
        (values (list left right))
        (premises (list hypothesis signed other)))
    (proof-with-checked-results
        ((heads (library-library-cite lib (concatenate 'string name "-HEADS") values premises))
         (tails (library-library-cite lib (concatenate 'string name "-TAILS") values premises))
         (bound (library-library-builtin lib 3 left))
         (descent (proof-proof-discharge proof bound signed))
         (plan (list-equivalence-paired-substitutions-plan lib goal left right))
         (instances (list-equivalence-prove-list-equivalence-instances
                     lib (car plan) (cadr plan) (caddr plan) (cadddr plan)
                     induction left right descent tails)))
      (list (list* signed other hypothesis heads tails (car instances))
            (cdr instances)))))

(defun list-equivalence-prove-list-equivalence-branch (holds suffix lib formula goal left right
                                                            name hypothesis induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((signed (proof-proof-assume proof (list *proof-consp* left) holds))
         (other (library-library-cite lib (concatenate 'string name suffix)
                                      (list left right) (list hypothesis signed)))
         (branch
          (if holds
              (list-equivalence-prove-list-equivalence-cons-evidence
               lib goal left right name hypothesis signed other induction)
            (list (list signed other hypothesis) induction)))
         (reduced (list-equivalence-paired-reduction lib goal (car branch)))
         (implication (and reduced (witnesses-prove-implication lib formula hypothesis reduced))))
      (cons implication branch))))

(defun list-equivalence-finish-induction (lib induction step)
  (let ((variable (book-logic-tree-induction-variable induction)))
    (proof-with-checked-results ((ordinal (library-library-builtin lib 1 variable)))
      (proof-proof-induct (library-library-proof lib) ordinal step
                         (book-logic-tree-induction-formula induction)
                         (book-logic-tree-induction-measure induction)
                         (book-logic-tree-induction-substitutions induction)))))

(defun list-equivalence-prove-list-equivalence-finish (lib left induction opened yes no)
  (let ((proof (library-library-proof lib)))
    (cons (proof-with-checked-results
              ((no no)
               (step (proof-proof-cases proof (list *proof-consp* left) yes no))
               (step (if (book-logic-tree-induction-substitutions induction)
                         (list-equivalence-finish-induction lib induction step)
                       step)))
            (if opened (proof-proof-transport proof step opened) step))
          lib)))

(defun list-equivalence-prove-list-equivalence-after-cons (lib context yes)
  (let* ((formula (car context))
         (goal (cadr context))
         (hypothesis (caddr context))
         (left (cadddr context))
         (right (nth 4 context))
         (name (nth 5 context))
         (induction (nth 6 context))
         (opened (nth 7 context)))
    (if (failure-p yes)
        (cons yes lib)
      (let ((branch (list-equivalence-prove-list-equivalence-branch
                     nil "-ATOM" lib formula goal left right name hypothesis induction)))
        (cond ((failure-p branch) (cons branch lib))
              ((car branch)
               (list-equivalence-prove-list-equivalence-finish
                lib left induction opened yes (car branch)))
              (t
               (cons (list :call goal (cadr branch)
                           (list :atom formula hypothesis left induction opened yes))
                     lib)))))))

(defun list-equivalence-prove-list-equivalence-start (lib equivalence original premise goal left right)
  (let* ((proof (library-library-proof lib))
         (name (list-equivalence-list-equivalence-name equivalence))
         (result
          (proof-with-checked-results
              ((reduction (proper-lists-reduce lib goal nil nil nil 56 240))
               (goal (if reduction (proper-lists-first-right reduction) goal))
               (formula (if reduction (list *library-implies* premise goal) original))
               (opened (and reduction
                            (proof-with-checked-results ((identity (proof-proof-reflexive proof original)))
                              (proof-proof-rewrite proof identity reduction '(1 2 2)))))
               (hypothesis (proof-proof-assume proof premise t))
               (induction (book-logic-tree-induction-init lib formula left))
               (branch (list-equivalence-prove-list-equivalence-branch
                        t "-CONS" lib formula goal left right name hypothesis induction))
               (context (list formula goal hypothesis left right name (caddr branch) opened)))
            (if (car branch)
                (list-equivalence-prove-list-equivalence-after-cons lib context (car branch))
              (cons (list :call goal (cadr branch) (cons :cons context)) lib)))))
    (if (failure-p result) (cons result lib) result)))

(defun list-equivalence-prove-list-equivalence (lib formula)
  (let* ((premise (cadr formula))
         (goal (caddr formula))
         (relation (car premise))
         (left (cadr premise))
         (right (caddr premise)))
    (cond ((not (proof-is-call formula *library-implies*))
           (cons *terms-unproved* lib))
          ((not (equal (len formula) 3))
           (cons (proper-lists-check-arity (cdr formula) 2) lib))
          ((not (and (proof-compound premise) (equal (len premise) 3)))
           (cons *terms-unproved* lib))
          ((or (proof-compound left) (proof-compound right) (equal left right))
           (cons *terms-unproved* lib))
          ((not (or (proof-is-call goal *proof-equal*) (proof-is-call goal *list-equivalence-iff*)
                    (proof-is-call goal relation)))
           (cons *terms-unproved* lib))
          (t
           (let* ((result (list-equivalence-list-equivalence-new-result lib relation))
                  (equivalence (car result))
                  (lib (cdr result)))
             (if (failure-p equivalence)
                 result
               (list-equivalence-prove-list-equivalence-start
                lib equivalence formula premise goal left right)))))))

(defun list-equivalence-prove-list-equivalence-resume (lib continuation answer)
  (if (eq (car continuation) :cons)
      (let* ((context (cdr continuation))
             (implication (proof-with-checked-results ((answer answer))
                            (witnesses-prove-implication lib (car context)
                                                         (caddr context) answer))))
        (list-equivalence-prove-list-equivalence-after-cons lib context implication))
    (let ((implication (proof-with-checked-results ((answer answer))
                         (witnesses-prove-implication lib (cadr continuation)
                                                      (caddr continuation) answer))))
      (list-equivalence-prove-list-equivalence-finish
       lib (cadddr continuation) (nth 4 continuation) (nth 5 continuation)
       (nth 6 continuation) implication))))
