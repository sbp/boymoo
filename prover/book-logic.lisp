(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *book-logic-cons-excluded*
  (list (cons (proof-cl "CHARACTERP") "consp-not-characterp")
        (cons (proof-cl "STRINGP") "consp-not-stringp")
        (cons (proof-cl "SYMBOLP") "consp-not-symbolp")
        (cons (proof-sym "ACL2-NUMBERP" "ACL2") "consp-not-acl2-numberp")))

(mutual-recursion
 (defun book-logic-match (pattern value bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond
    ((not (proof-compound pattern))
     (let ((existing (assoc-equal pattern bindings)))
       (if existing
           (cons (equal (cdr existing) value) bindings)
         (cons t (table-put bindings pattern value)))))
    ((proof-is-call pattern *proof-quote*)
     (cons (equal pattern value) bindings))
    ((not (and (proof-compound value) (eql (len pattern) (len value))))
     (cons nil bindings))
    ((not (consp pattern)) (cons '(:failure "failure" "") bindings))
    ((not (equal (car pattern) (car value))) (cons nil bindings))
    (t (book-logic-match-arguments (cdr pattern) (cdr value) bindings))))

 (defun book-logic-match-arguments (patterns values bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (let ((result (book-logic-match (car patterns) (car values) bindings)))
       (if (eq (car result) t)
           (book-logic-match-arguments (cdr patterns) (cdr values) (cdr result))
         result)))))

(defun book-logic-instance (lib name formula)
  (let ((proof (library-library-proof lib)))
    (termination-proofs-check
        ((step (proof-proof-fact proof name nil))
         (pattern (proof-step-first step)))
      (let ((match (book-logic-match pattern formula nil)))
        (cond
         ((failure-p (car match)) (car match))
         ((not (car match)) *terms-unproved*)
         (t (proof-proof-instantiate proof step (table-items (cdr match)))))))))

(defun book-logic-term-size-pending (n pending size limit)
  (declare (xargs :measure (nfix n)))
  (cond
   ((endp pending) size)
   ((zp n) (list :failure "fuel" "book-logic-term-size-pending"))
   ((< limit (1+ size)) (1+ size))
   (t
    (let ((item (car pending))
          (rest (cdr pending)))
      (if (and (proof-compound item) (not (proof-is-call item *proof-quote*)))
          (let ((head (car item))
                (children (revappend (cdr item) rest)))
            (cond
             ((endp item) '(:failure "failure" ""))
             ((not (proof-compound head))
              (book-logic-term-size-pending (1- n) children (1+ size) limit))
             ((not (consp (cddr head))) '(:failure "failure" ""))
             (t
              (book-logic-term-size-pending
               (1- n) (cons (caddr head) children) (1+ size) limit))))
        (book-logic-term-size-pending (1- n) rest (1+ size) limit))))))

(defun book-logic-term-size (term limit)
  (book-logic-term-size-pending 1000000 (list term) 0 limit))

(defun book-logic-within-size (term limit)
  (termination-proofs-check
      ((size (book-logic-term-size term limit)))
    (<= size limit)))

(defun book-logic-evidence-map (evidence facts)
  (if (endp evidence)
      facts
    (termination-proofs-check
        ((term (proof-step-first (car evidence))))
      (book-logic-evidence-map (cdr evidence) (table-put facts term (car evidence))))))

(defun book-logic-reducer-init (lib evidence definitions expose budget size rewrite logical)
  (termination-proofs-check
      ((facts (book-logic-evidence-map evidence nil)))
    (list :reducer lib facts definitions expose budget size rewrite logical nil)))

(defun book-logic-reducer-lib (reducer)
  (cadr reducer))

(defun book-logic-reducer-evidence (reducer)
  (caddr reducer))

(defun book-logic-reducer-definitions (reducer)
  (cadddr reducer))

(defun book-logic-reducer-expose (reducer)
  (nth 4 reducer))

(defun book-logic-reducer-budget (reducer)
  (nth 5 reducer))

(defun book-logic-reducer-size (reducer)
  (nth 6 reducer))

(defun book-logic-reducer-rewrite (reducer)
  (nth 7 reducer))

(defun book-logic-reducer-logical (reducer)
  (nth 8 reducer))

(defun book-logic-reducer-memo (reducer)
  (nth 9 reducer))

(defun book-logic-reducer-with-rewrite (reducer rewrite)
  (update-nth 7 rewrite reducer))

(defun book-logic-reducer-proof (reducer)
  (library-library-proof (book-logic-reducer-lib reducer)))

(defun book-logic-reducer-memoize (reducer key value)
  (update-nth 9 (table-put (book-logic-reducer-memo reducer) key value) reducer))

(defun book-logic-reducer-known-from-evidence (reducer term)
  (let ((proof (book-logic-reducer-proof reducer))
        (evidence (assoc-equal term (book-logic-reducer-evidence reducer))))
    (cond
     (evidence (cdr evidence))
     ((and (proof-is-call term *proof-consp*) (not (consp (cdr term))))
      '(:failure "failure" ""))
     ((and (proof-is-call term *proof-consp*) (proof-is-call (cadr term) *proof-cons*))
      (proof-proof-fact proof "consp-cons"
                        (seq-zip (list *library-x* *library-y*) (cdadr term))))
     ((and (proof-is-call term *proof-quote*) (not (equal term *proof-false*)))
      (termination-proofs-check
          ((either (proof-proof-nil-or-true proof term))
           (literal (proof-step-first either))
           (computed (proof-proof-compute proof literal *proof-nil*))
           (changed (proof-proof-rewrite proof either computed '(1))))
        (proof-proof-tidy proof changed)))
     ((equal term (proof-neg *proof-false*)) (proof-proof-not-nil proof))
     (t nil))))

(defun book-logic-reducer-exclude-cons (reducer term exclusions)
  (if (endp exclusions)
      nil
    (let* ((value (cadr term))
           (predicate (caar exclusions))
           (atomic (cdr (assoc-equal (list predicate value)
                                    (book-logic-reducer-evidence reducer)))))
      (if (not atomic)
          (book-logic-reducer-exclude-cons reducer term (cdr exclusions))
        (let ((proof (book-logic-reducer-proof reducer)))
          (termination-proofs-check
              ((law (proof-proof-fact proof (cdar exclusions) (list (list *library-x* value))))
               (assumed (proof-proof-assume proof term t))
               (excluded (proof-proof-modus-ponens proof law assumed))
               (impossible (proof-proof-cut proof atomic excluded)))
            (proof-proof-front proof impossible (proof-neg term))))))))

(defun book-logic-step-right (step)
  (if (not step)
      '(:failure "failure" "")
    (termination-proofs-check
        ((literal (proof-step-first step)))
      (if (consp (cddr literal))
          (caddr literal)
        '(:failure "failure" "")))))

(defun book-logic-reducer-exclude-equal (reducer term candidates)
  (if (endp candidates)
      nil
    (let* ((candidate (car candidates))
           (value (car candidate))
           (constant (cadr candidate))
           (reverse-p (caddr candidate)))
      (if (not (proof-is-call constant *proof-quote*))
          (book-logic-reducer-exclude-equal reducer term (cdr candidates))
        (termination-proofs-check
            ((cons-proof (book-logic-reducer-known-from-evidence
                          reducer (list *proof-consp* value)))
             (computed (proof-proof-constant
                        (book-logic-reducer-proof reducer) (list *proof-consp* constant)))
             (right (if (and cons-proof computed) (book-logic-step-right computed) nil)))
          (if (not (equal right *proof-false*))
              (book-logic-reducer-exclude-equal reducer term (cdr candidates))
            (let ((proof (book-logic-reducer-proof reducer)))
              (termination-proofs-check
                  ((assumption (proof-proof-assume proof term t))
                   (equality (if reverse-p (proof-proof-symmetric proof assumption) assumption))
                   (rewritten (proof-proof-rewrite proof cons-proof equality '(1 1)))
                   (impossible (proof-proof-rewrite proof rewritten computed '(1)))
                   (tidy (proof-proof-tidy proof impossible)))
                (proof-proof-front proof tidy (proof-neg term))))))))))

(defun book-logic-reducer-disjoint (reducer term)
  (if (not (proof-compound term))
      nil
    (if (endp term)
        '(:failure "failure" "")
      (let ((law (cdr (assoc-equal (car term) *book-logic-cons-excluded*)))
            (proof (book-logic-reducer-proof reducer)))
        (termination-proofs-check
            ((cons-proof (cond
                          ((not law) nil)
                          ((endp (cdr term)) '(:failure "failure" ""))
                          (t (book-logic-reducer-known-from-evidence
                              reducer (list *proof-consp* (cadr term)))))))
          (cond
           (cons-proof
            (termination-proofs-check
                ((instance (proof-proof-fact proof law (list (list *library-x* (cadr term))))))
              (proof-proof-modus-ponens proof instance cons-proof)))
           ((proof-is-call term *proof-consp*)
            (if (consp (cdr term))
                (book-logic-reducer-exclude-cons reducer term *book-logic-cons-excluded*)
              '(:failure "failure" "")))
           ((proof-is-call term *proof-equal*)
            (if (consp (cddr term))
                (book-logic-reducer-exclude-equal
                 reducer term (list (list (cadr term) (caddr term) nil)
                                    (list (caddr term) (cadr term) t)))
              '(:failure "failure" "")))
           (t nil)))))))

(defun book-logic-reducer-known (reducer term)
  (termination-proofs-check
      ((known (book-logic-reducer-known-from-evidence reducer term)))
    (or known
        (and (book-logic-reducer-logical reducer)
             (proof-is-call term *proof-not*)
             (if (consp (cdr term))
                 (book-logic-reducer-disjoint reducer (cadr term))
               '(:failure "failure" ""))))))

(defun book-logic-reducer-book-library-p (reducer)
  (eq (proof-proof-kind (book-logic-reducer-proof reducer)) :book))

(defun book-logic-reducer-boolean (reducer term)
  (if (book-logic-reducer-book-library-p reducer)
      (book-library-book-library-boolean (book-logic-reducer-lib reducer) term)
    '(:failure "failure" "")))

(defun book-logic-reducer-true-equality (reducer term evidence)
  (let ((lib (book-logic-reducer-lib reducer)))
    (termination-proofs-check
        ((typed (book-logic-reducer-boolean reducer term)))
      (library-library-cite lib "BOOLEAN-TRUE-VALUE" (list term) (list typed evidence)))))

(defun book-logic-reducer-truth-value (reducer term)
  (if (or (equal term *proof-false*) (equal term *proof-true*))
      nil
    (let* ((lib (book-logic-reducer-lib reducer))
           (evidence (book-logic-reducer-evidence reducer))
           (premise (assoc-equal term evidence)))
      (termination-proofs-check
          ((rejected (book-logic-reducer-known reducer (proof-neg term))))
        (if rejected
            (if (book-logic-reducer-book-library-p reducer)
                (book-library-book-library-false-value lib term rejected)
              '(:failure "failure" ""))
          (termination-proofs-check
              ((typed (and premise
                           (or (cdr (assoc-equal (list *book-library-booleanp* term) evidence))
                               (book-logic-reducer-boolean reducer term)))))
            (cond
             (typed (library-library-cite lib "BOOLEAN-TRUE-VALUE" (list term)
                                          (list typed (cdr premise))))
             ((proof-is-call term *book-library-booleanp*)
              (if (endp (cdr term))
                  '(:failure "failure" "")
                (termination-proofs-check
                    ((typed (book-logic-reducer-boolean reducer (cadr term))))
                  (and typed (book-logic-reducer-true-equality reducer term typed)))))
             (t nil))))))))

(defun book-logic-reducer-chain (reducer first rest)
  (proof-proof-chain (book-logic-reducer-proof reducer) first (list rest)))

(defun book-logic-reducer-extend (reducer prefix step)
  (if prefix (book-logic-reducer-chain reducer prefix step) step))

(defun book-logic-reducer-smaller-literal-p (args parent)
  (if (or (endp args) (endp parent))
      nil
    (let ((child (car args))
          (old (car parent)))
      (cond
       ((not (and (proof-is-call child *proof-quote*) (proof-is-call old *proof-quote*)))
        (book-logic-reducer-smaller-literal-p (cdr args) (cdr parent)))
       ((endp (cdr child)) '(:failure "failure" ""))
       (t
        (let ((a (if (eq (cadr child) t) 1 (cadr child))))
          (cond
           ((not (integerp a))
            (book-logic-reducer-smaller-literal-p (cdr args) (cdr parent)))
           ((endp (cdr old)) '(:failure "failure" ""))
           (t
            (let ((b (if (eq (cadr old) t) 1 (cadr old))))
              (or (and (natp a) (integerp b) (< a b))
                  (book-logic-reducer-smaller-literal-p (cdr args) (cdr parent))))))))))))

(defun book-logic-reducer-may-open-from (term parents)
  (cond
   ((endp parents) t)
   ((or (endp (car parents)) (endp term)) '(:failure "failure" ""))
   ((equal (caar parents) (car term))
    (book-logic-reducer-smaller-literal-p (cdr term) (cdar parents)))
   (t (book-logic-reducer-may-open-from term (cdr parents)))))

(defun book-logic-reducer-may-open (term active)
  (book-logic-reducer-may-open-from term (reverse active)))

(defun book-logic-reducer-premise (term evidence)
  (if (endp evidence)
      nil
    (let ((premise (cdar evidence)))
      (termination-proofs-check
          ((first (proof-step-first premise)))
        (cond
         ((and (proof-is-call first *proof-equal*) (endp (cdr first)))
          '(:failure "failure" ""))
         ((and (proof-is-call first *proof-equal*) (equal (cadr first) term))
          (cond
           ((endp (cddr first)) '(:failure "failure" ""))
           ((not (equal (caddr first) term)) premise)
           (t (book-logic-reducer-premise term (cdr evidence)))))
         (t (book-logic-reducer-premise term (cdr evidence))))))))

(defun book-logic-reducer-known-branch (reducer test)
  (termination-proofs-check
      ((step (book-logic-reducer-known reducer test)))
    (or step (book-logic-reducer-known reducer (proof-neg test)))))

(defun book-logic-reducer-rewrite-answer (reducer term)
  (let ((replies (cdr (book-logic-reducer-rewrite reducer))))
    (if (endp replies)
        (cons (list :call :rewrite (book-logic-reducer-lib reducer) term) reducer)
      (let ((reply (car replies)))
        (cons (car reply)
              (book-logic-reducer-with-rewrite
               (update-nth 1 (cdr reply) reducer) (cons t (cdr replies))))))))

(defun book-logic-reducer-fuel (name reducer)
  (cons (list :failure "fuel" name) reducer))

(defconst *book-logic-coerce* (proof-cl "COERCE"))
(defconst *book-logic-char-code* (proof-cl "CHAR-CODE"))

(mutual-recursion
 (defun book-logic-reducer-reduce-in (n reducer term active)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (book-logic-reducer-fuel "book-logic-reducer-reduce-in" reducer))
    ((<= (book-logic-reducer-budget reducer) 0) (cons nil reducer))
    (t
     (termination-proofs-check-in reducer
         ((allowed (book-logic-within-size term (book-logic-reducer-size reducer))))
       (if (not allowed)
           (cons nil reducer)
         (let* ((key (list term active))
                (memoized (assoc-equal key (book-logic-reducer-memo reducer))))
           (if memoized
               (cons (cdr memoized) reducer)
             (let ((reducer
                    (book-logic-reducer-memoize
                     (update-nth 5 (1- (book-logic-reducer-budget reducer)) reducer)
                     key nil)))
               (termination-proofs-bind reducer
                   (step (book-logic-reducer-reduction-in (1- n) reducer term active))
                 (cons step (book-logic-reducer-memoize reducer key step)))))))))))

 (defun book-logic-reducer-reduction-in (n reducer term active)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (book-logic-reducer-fuel "book-logic-reducer-reduction-in" reducer)
     (termination-proofs-check-in reducer
         ((value (and (book-logic-reducer-logical reducer)
                      (book-logic-reducer-truth-value reducer term))))
       (if value
           (cons value reducer)
         (termination-proofs-check-in reducer
             ((premise (book-logic-reducer-premise term (book-logic-reducer-evidence reducer))))
           (cond
            (premise (book-logic-reducer-chain-reduce-in (1- n) reducer premise active))
            ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
             (cons nil reducer))
            ((endp term) (cons '(:failure "failure" "") reducer))
            ((or (proof-compound (car term)) (equal (car term) *termination-return-last*))
             (let ((proof (book-logic-reducer-proof reducer)))
               (termination-proofs-check-in reducer
                   ((opened (if (proof-compound (car term))
                                (proof-proof-beta proof term)
                              (proof-proof-unfold proof term)))
                    (right (book-logic-step-right opened))
                    (allowed (book-logic-within-size right (book-logic-reducer-size reducer))))
                 (if allowed
                     (book-logic-reducer-chain-reduce-in (1- n) reducer opened active)
                   (cons nil reducer)))))
            ((equal (car term) *proof-if*)
             (book-logic-reducer-conditional-in (1- n) reducer term active))
            (t (book-logic-reducer-arguments-in (1- n) reducer term active
                                                (cdr term) 1 nil))))))))

 (defun book-logic-reducer-chain-reduce-in (n reducer step active)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (book-logic-reducer-fuel "book-logic-reducer-chain-reduce-in" reducer)
     (termination-proofs-check-in reducer
         ((right (book-logic-step-right step)))
       (termination-proofs-bind reducer
           (change (book-logic-reducer-reduce-in (1- n) reducer right active))
         (cons (book-logic-reducer-chain reducer step change) reducer)))))

 (defun book-logic-reducer-arguments-in (n reducer term active args index prefix)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (book-logic-reducer-fuel "book-logic-reducer-arguments-in" reducer))
    ((endp args)
     (termination-proofs-check-in reducer
         ((current (if prefix (book-logic-step-right prefix) term)))
       (book-logic-reducer-current-in (1- n) reducer current active (car term) prefix)))
    (t
     (termination-proofs-bind reducer
         (change (book-logic-reducer-reduce-in (1- n) reducer (car args) active))
       (termination-proofs-check-in reducer
           ((prefix (if change
                        (termination-proofs-check
                            ((proof (or prefix
                                        (proof-proof-reflexive (book-logic-reducer-proof reducer)
                                                               term))))
                          (proof-proof-rewrite (book-logic-reducer-proof reducer)
                                               proof change (list 1 2 index)))
                      prefix)))
         (book-logic-reducer-arguments-in
          (1- n) reducer term active (cdr args) (1+ index) prefix))))))

 (defun book-logic-reducer-current-in (n reducer current active head prefix)
   (declare (xargs :measure (nfix n)))
   (let ((selector (or (equal head *library-car*) (equal head *library-cdr*))))
     (cond
      ((zp n) (book-logic-reducer-fuel "book-logic-reducer-current-in" reducer))
      ((and selector (not (consp (cdr current))))
       (cons '(:failure "failure" "") reducer))
      ((and selector (proof-is-call (cadr current) *proof-cons*))
       (termination-proofs-check-in reducer
           ((step (library-library-axiom
                   (book-logic-reducer-lib reducer)
                   (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
                   (cdadr current))))
         (cons (book-logic-reducer-extend reducer prefix step) reducer)))
      (t
       (termination-proofs-check-in reducer
           ((computed (proof-proof-constant (book-logic-reducer-proof reducer) current)))
         (if computed
             (cons (book-logic-reducer-extend reducer prefix computed) reducer)
           (termination-proofs-bind reducer
               (completed (if (book-logic-reducer-logical reducer)
                              (book-logic-reducer-completion-in (1- n) reducer current active)
                            (cons nil reducer)))
             (if completed
                 (cons (book-logic-reducer-extend reducer prefix completed) reducer)
               (book-logic-reducer-rewrite-in (1- n) reducer current active head prefix)))))))))

 (defun book-logic-reducer-rewrite-in (n reducer current active head prefix)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (book-logic-reducer-fuel "book-logic-reducer-rewrite-in" reducer)
     (termination-proofs-bind reducer
         (rewritten (if (and (book-logic-reducer-rewrite reducer)
                             (not (member-equal current active)))
                        (book-logic-reducer-rewrite-answer reducer current)
                      (cons nil reducer)))
       (termination-proofs-check-in reducer
           ((right (and rewritten (book-logic-step-right rewritten)))
            (allowed (and rewritten
                          (book-logic-within-size right (book-logic-reducer-size reducer)))))
         (if allowed
             (termination-proofs-bind reducer
                 (step (book-logic-reducer-chain-reduce-in
                        (1- n) reducer rewritten (append active (list current))))
               (cons (book-logic-reducer-extend reducer prefix step) reducer))
           (book-logic-reducer-open-in (1- n) reducer current active head prefix))))))

 (defun book-logic-reducer-open-in (n reducer current active head prefix)
   (declare (xargs :measure (nfix n)))
   (let* ((proof (book-logic-reducer-proof reducer))
          (definition (assoc-equal head (proof-proof-definitions proof)))
          (allowed (book-logic-reducer-definitions reducer)))
     (cond
      ((zp n) (book-logic-reducer-fuel "book-logic-reducer-open-in" reducer))
      ((or (not definition) (not (or (eq allowed :none) (member-equal head allowed))))
       (cons prefix reducer))
      (t
       (termination-proofs-check-in reducer
           ((may-open (book-logic-reducer-may-open current active))
            (body-fits (and may-open
                            (book-logic-within-size (caddr definition)
                                                    (book-logic-reducer-size reducer)))))
         (if (not body-fits)
             (cons prefix reducer)
           (termination-proofs-check-in reducer
               ((opened (proof-proof-unfold proof current))
                (right (book-logic-step-right opened))
                (result-fits (book-logic-within-size right (book-logic-reducer-size reducer))))
             (if (not result-fits)
                 (cons prefix reducer)
               (termination-proofs-bind reducer
                   (result (book-logic-reducer-chain-reduce-in
                            (1- n) reducer opened (append active (list current))))
                 (termination-proofs-check-in reducer
                     ((right (and (not (book-logic-reducer-expose reducer))
                                  (book-logic-step-right result))))
                   (if (proof-is-call right *proof-if*)
                       (cons prefix reducer)
                     (cons (book-logic-reducer-extend reducer prefix result) reducer))))))))))))

 (defun book-logic-reducer-completion-in (n reducer term active)
   (declare (xargs :measure (nfix n)))
   (let ((function (car term))
         (args (cdr term))
         (lib (book-logic-reducer-lib reducer)))
     (cond
      ((zp n) (book-logic-reducer-fuel "book-logic-reducer-completion-in" reducer))
      ((endp term) (cons *terms-invalid-proof-arity* reducer))
      ((equal function *book-library-booleanp*)
       (if (endp args)
           (cons '(:failure "failure" "") reducer)
         (termination-proofs-check-in reducer
             ((typed (book-logic-reducer-boolean reducer (car args))))
           (cons (and typed (book-logic-reducer-true-equality reducer term typed))
                 reducer))))
      ((and (equal function *book-logic-coerce*) (endp args))
       (cons '(:failure "failure" "") reducer))
      ((and (equal function *book-logic-coerce*)
            (not (equal (car (last args)) (proof-quote (proof-cl "LIST")))))
       (cons nil reducer))
      ((not (member-equal function
                          (list *library-car* *library-cdr* *book-logic-coerce*
                                *book-logic-char-code*)))
       (cons nil reducer))
      (t
       (termination-proofs-check-in reducer
           ((opened (library-library-axiom
                     lib (concatenate 'string "COMPLETION-OF-" (caddr function)) args))
            (right (book-logic-step-right opened)))
         (termination-proofs-bind reducer
             (reduced (book-logic-reducer-reduce-in (1- n) reducer right active))
           (termination-proofs-check-in reducer
               ((right (and reduced (book-logic-step-right reduced))))
             (cond
              ((and reduced (not (equal right term))
                    (or (not (proof-is-call right *proof-if*))
                        (and (book-logic-reducer-expose reducer)
                             (or (equal function *book-logic-coerce*)
                                 (equal function *book-logic-char-code*)))))
               (cons (book-logic-reducer-chain reducer opened reduced) reducer))
              ((and (book-logic-reducer-expose reducer)
                    (equal function *book-logic-char-code*) (not reduced))
               (cons opened reducer))
              (t (cons nil reducer))))))))))

 (defun book-logic-reducer-conditional-in (n reducer term active)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (book-logic-reducer-fuel "book-logic-reducer-conditional-in" reducer))
    ((endp (cdr term)) (cons '(:failure "failure" "") reducer))
    (t
     (let ((test (cadr term)))
       (termination-proofs-check-in reducer
           ((premise (book-logic-reducer-known-branch reducer test)))
         (if premise
             (book-logic-reducer-select-in (1- n) reducer term active premise nil)
           (termination-proofs-bind reducer
               (reduction (book-logic-reducer-reduce-in (1- n) reducer test active))
             (if (not reduction)
                 (cons nil reducer)
               (let ((proof (book-logic-reducer-proof reducer)))
                 (termination-proofs-check-in reducer
                     ((identity (proof-proof-reflexive proof term))
                      (prefix (proof-proof-rewrite proof identity reduction '(1 2 1)))
                      (term (book-logic-step-right prefix))
                      (premise (if (consp (cdr term))
                                   (book-logic-reducer-known-branch reducer (cadr term))
                                 '(:failure "failure" ""))))
                   (book-logic-reducer-select-in
                    (1- n) reducer term active premise prefix)))))))))))

 (defun book-logic-reducer-select-in (n reducer term active premise prefix)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (book-logic-reducer-fuel "book-logic-reducer-select-in" reducer))
    ((not premise) (cons prefix reducer))
    (t
     (termination-proofs-check-in reducer
         ((selected (proof-proof-select (book-logic-reducer-proof reducer) term premise)))
       (termination-proofs-bind reducer
           (step (book-logic-reducer-chain-reduce-in (1- n) reducer selected active))
         (cons (book-logic-reducer-extend reducer prefix step) reducer)))))))

(defun book-logic-reducer-reduce (reducer term active)
  (book-logic-reducer-reduce-in 1000000 reducer term active))

(defun book-logic-reducer-prove (reducer term)
  (termination-proofs-check-in reducer
      ((known (book-logic-reducer-known reducer term)))
    (if known
        (cons known reducer)
      (termination-proofs-bind reducer
          (reduction (book-logic-reducer-reduce reducer term nil))
        (if (not reduction)
            (cons *terms-unproved* reducer)
          (let ((proof (book-logic-reducer-proof reducer)))
            (termination-proofs-check-in reducer
                ((simplified (book-logic-step-right reduction)))
              (if (equal simplified *proof-true*)
                  (cons (proof-proof-true-from-eq proof reduction) reducer)
                (termination-proofs-check-in reducer
                    ((known (book-logic-reducer-known reducer simplified)))
                  (cons (if known
                            (proof-proof-transport proof known reduction)
                          *terms-unproved*)
                        reducer))))))))))

(defun book-logic-tree-induction-init (lib formula variable)
  (list :tree-induction lib formula variable (list *library-count* variable) nil))

(defun book-logic-tree-induction-lib (induction)
  (cadr induction))

(defun book-logic-tree-induction-formula (induction)
  (caddr induction))

(defun book-logic-tree-induction-variable (induction)
  (cadddr induction))

(defun book-logic-tree-induction-measure (induction)
  (nth 4 induction))

(defun book-logic-tree-induction-substitutions (induction)
  (nth 5 induction))

(defun book-logic-bindings-map (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings)))
      (if (eql (len binding) 2)
          (book-logic-bindings-map (cdr bindings)
                                   (table-put result (car binding) (cadr binding)))
        *terms-invalid-proof-arity*))))

(defun book-logic-tree-induction-at (induction value descent extra)
  (let* ((lib (book-logic-tree-induction-lib induction))
         (formula (book-logic-tree-induction-formula induction))
         (variable (book-logic-tree-induction-variable induction))
         (measure (book-logic-tree-induction-measure induction))
         (substitutions (book-logic-tree-induction-substitutions induction))
         (binding (cons (list variable value) extra))
         (updated (update-nth 5 (append substitutions (list binding)) induction))
         (proof (library-library-proof lib))
         (smaller (list *proof-ordinal-less* (list *library-count* value) measure)))
    (termination-proofs-check-in updated
        ((bindings (book-logic-bindings-map binding nil))
         (instance (proof-subst formula bindings))
         (premise (proof-proof-assume proof (proof-ite smaller instance *proof-true*) t)))
      (cons (proof-proof-prove-if proof premise descent) updated))))

(defun book-logic-tree-induction-finish (induction step)
  (let ((lib (book-logic-tree-induction-lib induction))
        (variable (book-logic-tree-induction-variable induction)))
    (termination-proofs-check
        ((ordinal (library-library-builtin lib 1 variable)))
      (proof-proof-induct
       (library-library-proof lib) ordinal step
       (book-logic-tree-induction-formula induction)
       (book-logic-tree-induction-measure induction)
       (book-logic-tree-induction-substitutions induction)))))
