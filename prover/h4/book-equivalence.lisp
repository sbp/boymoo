(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-equivalence-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(mutual-recursion
 (defun h4-book-equivalence-positions (term place)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cons (list term place)
         (and (consp term)
              (proof-compound term)
              (not (proof-is-call term *proof-quote*))
              (h4-book-equivalence-argument-positions (cdr term) place 1))))
 (defun h4-book-equivalence-argument-positions (arguments place index)
   (declare (xargs :measure (* 2 (acl2-count arguments))))
   (if (endp arguments)
       nil
     (append (h4-book-equivalence-positions (car arguments)
                                           (append place (list index)))
             (h4-book-equivalence-argument-positions
              (cdr arguments) place (1+ index))))))

(defun h4-book-equivalence-inverse-order (operator identity plain inverse)
  (and (not (proof-compound plain))
       (proof-compound inverse)
       (proof-with-checked-results
           ((head (proof-term-at inverse 0)))
         (and (not (proof-compound head))
              (equal (len inverse) 2)
              (equal (cadr inverse) plain)
              (list (list operator head identity))))))

(defun h4-book-equivalence-inverse-side (product identity)
  (and (proof-compound product)
       (proof-with-checked-results
           ((operator (proof-term-at product 0)))
         (and (not (proof-compound operator))
              (equal (len product) 3)
              (proof-compound identity)
              (or (equal (len identity) 1) (proof-is-call identity *proof-quote*))
              (proof-with-checked-results
                  ((forward (h4-book-equivalence-inverse-order
                             operator identity (cadr product) (caddr product)))
                   (backward (h4-book-equivalence-inverse-order
                              operator identity (caddr product) (cadr product))))
                (append forward backward))))))

(defun h4-book-equivalence-inverse-operations (rules)
  (if (endp rules)
      nil
    (proof-with-checked-results
        ((parts (proof-list-of-length (h4-book-tactics-rule-conclusion (car rules)) 3))
         (forward (h4-book-equivalence-inverse-side (cadr parts) (caddr parts)))
         (backward (h4-book-equivalence-inverse-side (caddr parts) (cadr parts)))
         (rest (h4-book-equivalence-inverse-operations (cdr rules))))
      (append forward backward rest))))

(defun h4-book-equivalence-equivalence-search (self)
  (cadr self))

(defun h4-book-equivalence-equivalence-relation (self)
  (caddr self))

(defun h4-book-equivalence-equivalence-premises (self)
  (cadddr self))

(defun h4-book-equivalence-equivalence-boolean (self)
  (nth 4 self))

(defun h4-book-equivalence-equivalence-reflexive (self)
  (nth 5 self))

(defun h4-book-equivalence-equivalence-symmetric (self)
  (nth 6 self))

(defun h4-book-equivalence-equivalence-transitive (self)
  (nth 7 self))

(defun h4-book-equivalence-equivalence-rules (self)
  (nth 8 self))

(defun h4-book-equivalence-equivalence-inverses (self)
  (nth 9 self))

(defun h4-book-equivalence-equivalence-lookup-scope (self)
  (nth 10 self))

(defun h4-book-equivalence-equivalence-with-search (self search)
  (list* :h4-equivalence search (cddr self)))

(defun h4-book-equivalence-library (self)
  (h4-book-tactics-book-search-p (h4-book-equivalence-equivalence-search self)))

(defun h4-book-equivalence-proof (self)
  (library-library-proof (h4-book-equivalence-library self)))

(defun h4-book-equivalence-evidence (steps evidence)
  (if (endp steps)
      evidence
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-equivalence-evidence
       (cdr steps) (table-put evidence literal (car steps))))))

(defun h4-book-equivalence-select-rules (rules name)
  (if (endp rules)
      nil
    (let ((rule (car rules)))
      (if (and (not (equal (h4-book-tactics-rule-source rule) name))
               (equal (len (h4-book-tactics-rule-conclusion rule)) 3))
          (cons rule (h4-book-equivalence-select-rules (cdr rules) name))
        (h4-book-equivalence-select-rules (cdr rules) name)))))

(defun h4-book-equivalence-relation-rules (index relation name)
  (if (endp index)
      nil
    (append (and (equal (caaar index) relation)
                 (h4-book-equivalence-select-rules (cdar index) name))
            (h4-book-equivalence-relation-rules (cdr index) relation name))))

(defun h4-book-equivalence-equivalence-init (search relation name premises)
  (let* ((p (h4-book-tactics-book-search-p search))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((expanded (h4-book-measures-expand-evidence p premises))
         (evidence (h4-book-equivalence-evidence expanded nil))
         (laws (proof-proof-fact proof name nil))
         (boolean-and-rest (h4-tactics-tactics-conjunct p laws))
         (reflexive-and-rest (h4-tactics-tactics-conjunct p (cadr boolean-and-rest)))
         (symmetric-and-transitive
          (h4-tactics-tactics-conjunct p (cadr reflexive-and-rest)))
         (reflexive (proof-step-first (car reflexive-and-rest))))
      (if (not (proof-is-call reflexive relation))
          '(:failure "Unproved" "")
        (proof-with-checked-results
            ((rules
              (proof-unique
               (h4-book-equivalence-relation-rules
                (h4-book-tactics-book-search-literal-rules search) relation name)))
             (inverses (h4-book-equivalence-inverse-operations rules)))
          (let ((lookup (h4-book-tactics-book-search-begin-lookup-scope search)))
            (list :h4-equivalence (cdr lookup) relation evidence
                  (car boolean-and-rest) (car reflexive-and-rest)
                  (car symmetric-and-transitive) (cadr symmetric-and-transitive)
                  rules (proof-unique inverses) (car lookup))))))))

(defun h4-book-equivalence-unproved-p (result)
  (and (failure-p result) (equal (cadr result) "Unproved")))

(defun h4-book-equivalence-finish (result)
  (if (failure-p (car result))
      (car result)
    result))

(defmacro h4-book-equivalence-with-result (self value form body)
  `(let ((h4-book-equivalence-outcome ,form))
     (if (failure-p (car h4-book-equivalence-outcome))
         h4-book-equivalence-outcome
       (let ((,value (car h4-book-equivalence-outcome))
             (,self (cdr h4-book-equivalence-outcome)))
         ,body))))

(defun h4-book-equivalence-match-proof (target proof)
  (proof-with-checked-results
      ((literal (proof-step-first proof))
       (match (h4-tactics-match-term target literal nil)))
    (if (car match)
        (cdr match)
      '(:failure "InapplicableStep" ""))))

(defun h4-book-equivalence-equivalence-reverse (self step)
  (let* ((p (h4-book-equivalence-library self))
         (proof (library-library-proof p))
         (symmetry (h4-book-equivalence-equivalence-symmetric self)))
    (proof-with-checked-results
        ((literal (proof-step-first symmetry))
         (target (proof-term-at literal 1))
         (bindings (h4-book-equivalence-match-proof target step))
         (implication (proof-proof-instantiate proof symmetry (table-items bindings))))
      (h4-tactics-tactics-modus-ponens p implication step))))

(defun h4-book-equivalence-match-pair (test first second)
  (proof-with-checked-results
      ((target (proof-term-at test 1))
       (bindings (h4-book-equivalence-match-proof target first))
       (next-target (proof-term-at test 2))
       (literal (proof-step-first second))
       (match (h4-tactics-match-term next-target literal bindings)))
    (if (car match)
        (cdr match)
      '(:failure "InapplicableStep" ""))))

(defun h4-book-equivalence-equivalence-compose (self first second)
  (let* ((p (h4-book-equivalence-library self))
         (proof (library-library-proof p))
         (transitivity (h4-book-equivalence-equivalence-transitive self)))
    (proof-with-checked-results
        ((literal (proof-step-first transitivity))
         (test (proof-term-at literal 1))
         (bindings (h4-book-equivalence-match-pair test first second))
         (implication
          (proof-proof-instantiate proof transitivity (table-items bindings)))
         (instantiated (proof-step-first implication))
         (guard (proof-term-at instantiated 1))
         (conjuncts (h4-tactics-tactics-conjunction p guard first second)))
      (h4-tactics-tactics-modus-ponens p implication conjuncts))))

(defun h4-book-equivalence-trace (n paths left right trace)
  (declare (xargs :measure (nfix n)))
  (cond ((equal left right) trace)
        ((zp n) '(:failure "Fuel" "h4-book-equivalence-trace"))
        (t (let ((link (assoc-equal right paths)))
             (if link
                 (proof-with-checked-results
                     ((pair (proof-list-of-length (cdr link) 2)))
                   (h4-book-equivalence-trace
                    (1- n) paths left (car pair) (cons (cadr pair) trace)))
               '(:failure "failure" ""))))))

(defun h4-book-equivalence-compose-trace (self first rest)
  (declare (xargs :measure (acl2-count rest)))
  (if (endp rest)
      first
    (proof-with-checked-results
        ((joined (h4-book-equivalence-equivalence-compose self first (car rest))))
      (h4-book-equivalence-compose-trace self joined (cdr rest)))))

(defun h4-book-equivalence-equivalence-follow (self paths left right)
  (proof-with-checked-results
      ((trace (h4-book-equivalence-trace 1000000 paths left right nil)))
    (if (endp trace)
        '(:failure "failure" "")
      (h4-book-equivalence-compose-trace self (car trace) (cdr trace)))))

(defun h4-book-equivalence-lookup (self formula evidence depth)
  (let ((result (h4-book-tactics-book-search-lookup-scoped
                 (h4-book-equivalence-equivalence-search self)
                 formula evidence depth
                 (h4-book-equivalence-equivalence-lookup-scope self))))
    (cons (car result)
          (h4-book-equivalence-equivalence-with-search self (cdr result)))))

(defun h4-book-equivalence-replay-rule (self rule bindings depth)
  (let ((result (h4-book-tactics-book-search-replay-scoped
                 (h4-book-equivalence-equivalence-search self) rule bindings
                 (h4-book-equivalence-equivalence-premises self) depth
                 (h4-book-equivalence-equivalence-lookup-scope self))))
    (cons (car result)
          (h4-book-equivalence-equivalence-with-search self (cdr result)))))

(defun h4-book-equivalence-lookup-new-evidence (self formula evidence depth)
  (let* ((lookup (h4-book-tactics-book-search-begin-lookup-scope
                  (h4-book-equivalence-equivalence-search self)))
         (result (h4-book-tactics-book-search-lookup-scoped
                  (cdr lookup) formula evidence depth (car lookup))))
    (cons (car result)
          (h4-book-equivalence-equivalence-with-search self (cdr result)))))

(defun h4-book-equivalence-lift-proof (self term index child)
  (proof-with-checked-results
      ((literal (proof-step-first child))
       (old (proof-term-at literal 1))
       (new (proof-term-at literal 2))
       (replacement (proof-change term (list index) old new)))
    (let ((evidence (table-put (h4-book-equivalence-equivalence-premises self)
                                literal child)))
      (list (list (h4-book-equivalence-equivalence-relation self) term replacement)
            evidence))))

(defun h4-book-equivalence-lift (self term place step)
  (declare (xargs :measure (acl2-count place)))
  (if (endp place)
      (cons step self)
    (let ((child-term (proof-term-at term (car place))))
      (if (failure-p child-term)
          (cons child-term self)
        (h4-book-equivalence-with-result
         self child (h4-book-equivalence-lift self child-term (cdr place) step)
         (if (null child)
             (cons nil self)
           (let ((query (h4-book-equivalence-lift-proof self term (car place) child)))
             (if (failure-p query)
                 (cons query self)
               (h4-book-equivalence-lookup-new-evidence self (car query) (cadr query) 3)))))))))

(defun h4-book-equivalence-equivalence-lift (self term place step)
  (h4-book-equivalence-finish (h4-book-equivalence-lift self term place step)))

(defun h4-book-equivalence-contains-call (head terms)
  (and (consp terms)
       (or (proof-is-call (car terms) head)
           (h4-book-equivalence-contains-call head (cdr terms)))))

(defun h4-book-equivalence-all-bound (terms bindings)
  (or (endp terms)
      (and (or (proof-compound (car terms)) (assoc-equal (car terms) bindings))
           (h4-book-equivalence-all-bound (cdr terms) bindings))))

(defun h4-book-equivalence-match-rewrite (conclusion term bound reverse-p)
  (proof-with-checked-results
      ((parts (proof-list-of-length conclusion 3))
       (source (if reverse-p (caddr parts) (cadr parts)))
       (result (if reverse-p (cadr parts) (caddr parts)))
       (match (h4-tactics-match-term source term nil)))
    (let ((bindings (cdr match)))
      (and (car match)
           (h4-book-equivalence-all-bound (h4-book-tactics-terms result) bindings)
           (proof-with-checked-results ((value (proof-subst result bindings)))
             (and (not (equal value term))
                  (<= (h4-book-tactics-size value 150) bound)
                  match))))))

(defun h4-book-equivalence-root-cursor (self)
  ;; Resume with the pending premises and rules in their current orientation.
  (list (table-values (h4-book-equivalence-equivalence-premises self))
        (h4-book-equivalence-equivalence-rules self)
        nil))

(defun h4-book-equivalence-next-root-cursor (premises rules reverse-p)
  (cond ((not reverse-p) (list premises rules t))
        (premises (list (cdr premises) rules nil))
        (t (list nil (cdr rules) nil))))

(defun h4-book-equivalence-root-premise (self step term reverse-p)
  (proof-with-checked-results
      ((literal (proof-step-first step)))
    (and (proof-is-call literal (h4-book-equivalence-equivalence-relation self))
         (proof-with-checked-results
             ((side (proof-term-at literal (if reverse-p 2 1))))
           (and (equal side term)
                (if reverse-p
                    (h4-book-equivalence-equivalence-reverse self step)
                  step))))))

(defun h4-book-equivalence-instance-guard (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 1)))

(defun h4-book-equivalence-guarded-rule-p (rule)
  (and (equal (h4-book-tactics-rule-path rule) '(0))
       (not (h4-book-tactics-rule-clause rule))))

(defun h4-book-equivalence-insert-pending (entry pending)
  ;; The insertion number breaks ties between terms of the same size.
  (if (or (endp pending)
          (< (car entry) (caar pending))
          (and (equal (car entry) (caar pending))
               (< (cadr entry) (cadar pending))))
      (cons entry pending)
    (cons (car pending) (h4-book-equivalence-insert-pending entry (cdr pending)))))

(defun h4-book-equivalence-reflexivity (self term)
  (let ((reflexive (h4-book-equivalence-equivalence-reflexive self))
        (proof (h4-book-equivalence-proof self)))
    (proof-with-checked-results
        ((literal (proof-step-first reflexive))
         (variable (proof-term-at literal 1)))
      (proof-proof-instantiate proof reflexive (list (list variable term))))))

(defun h4-book-equivalence-rewrite-value (term place node step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (replacement (proof-term-at literal 2)))
    (proof-change term place node replacement)))

(mutual-recursion
 (defun h4-book-equivalence-replay-rewrite (n self rule bindings)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n)
     (cons '(:failure "Fuel" "h4-book-equivalence-replay-rewrite") self))
    ((h4-book-equivalence-guarded-rule-p rule)
     (let* ((p (h4-book-equivalence-library self))
            (step (proof-proof-fact
                   (library-library-proof p)
                   (h4-book-tactics-rule-source rule) (table-items bindings)))
            (guard (if (failure-p step)
                       step
                     (h4-book-equivalence-instance-guard step))))
       (cond
        ((failure-p guard) (cons guard self))
        ((h4-book-equivalence-contains-call
          (h4-book-equivalence-equivalence-relation self)
          (h4-book-tactics-terms guard))
         (h4-book-equivalence-replay-rule self rule bindings 5))
        (t (let* ((guarded (h4-book-equivalence-establish-guard (1- n) self guard))
                  (evidence (car guarded))
                  (result (if (failure-p evidence)
                              evidence
                            (h4-tactics-tactics-modus-ponens p step evidence))))
             (cons (if (h4-book-equivalence-unproved-p result) nil result)
                   (cdr guarded)))))))
    (t (h4-book-equivalence-replay-rule self rule bindings 5))))
 (defun h4-book-equivalence-at-root-next (n self term bound cursor)
   (declare (xargs :measure (nfix n)))
   (let ((premises (car cursor))
         (rules (cadr cursor))
         (reverse-p (caddr cursor)))
     (cond
      ((zp n)
       (cons '(:failure "Fuel" "h4-book-equivalence-at-root-next") self))
      ((and (endp premises) (endp rules)) (cons nil self))
      (t (let* ((next (h4-book-equivalence-next-root-cursor premises rules reverse-p))
                (rule (car rules))
                (match (and (endp premises)
                            (h4-book-equivalence-match-rewrite
                             (h4-book-tactics-rule-conclusion rule)
                             term bound reverse-p)))
                (reply (cond
                        (premises
                         (cons (h4-book-equivalence-root-premise
                                self (car premises) term reverse-p)
                               self))
                        ((failure-p match) (cons match self))
                        (match
                         (h4-book-equivalence-with-result
                          self step
                          (h4-book-equivalence-replay-rewrite
                           (1- n) self rule (cdr match))
                          (cons (if (and step reverse-p)
                                    (h4-book-equivalence-equivalence-reverse self step)
                                  step)
                                self)))
                        (t (cons nil self)))))
           (h4-book-equivalence-with-result
            self step reply
            (if step
                (cons (cons step next) self)
              (h4-book-equivalence-at-root-next (1- n) self term bound next))))))))
 (defun h4-book-equivalence-rewrite (n self left right)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "Fuel" "h4-book-equivalence-rewrite") self))
    ((equal left right) (cons (h4-book-equivalence-reflexivity self left) self))
    (t (let ((relation (h4-book-equivalence-equivalence-relation self))
             (evidence (h4-book-equivalence-equivalence-premises self)))
         (h4-book-equivalence-with-result
          self direct (h4-book-equivalence-lookup self (list relation left right) evidence 3)
          (if direct
              (cons direct self)
            (h4-book-equivalence-with-result
             self backward (h4-book-equivalence-lookup self (list relation right left) evidence 3)
             (if backward
                 (cons (h4-book-equivalence-equivalence-reverse self backward) self)
               (let* ((left-size (h4-book-tactics-size left 150))
                      (bound (max left-size (h4-book-tactics-size right 150)))
                      (paths (list (cons left nil)))
                      (pending (list (list left-size 0 left))))
                 (h4-book-equivalence-rewrite-pending
                  (1- n) self left right bound paths pending 1 70))))))))))
 (defun h4-book-equivalence-rewrite-pending
   (n self left right bound paths pending order remaining)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n)
     (cons '(:failure "Fuel" "h4-book-equivalence-rewrite-pending") self))
    ((or (zp remaining) (endp pending))
     (cons '(:failure "Unproved" "") self))
    (t (let* ((term (caddar pending))
              (budget (- bound (h4-book-tactics-size term 150)))
              (positions (h4-book-equivalence-positions term nil)))
         (h4-book-equivalence-rewrite-positions
          (1- n) self left right bound term budget positions
          (h4-book-equivalence-root-cursor self)
          paths (cdr pending) order (1- remaining))))))
 (defun h4-book-equivalence-rewrite-positions
   (n self left right bound term budget positions cursor paths pending order remaining)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n)
     (cons '(:failure "Fuel" "h4-book-equivalence-rewrite-positions") self))
    ((endp positions)
     (h4-book-equivalence-rewrite-pending
      (1- n) self left right bound paths pending order remaining))
    (t (let* ((node (caar positions))
              (place (cadar positions))
              (node-bound (+ (h4-book-tactics-size node 150) budget)))
         (h4-book-equivalence-with-result
          self item
          (h4-book-equivalence-at-root-next (1- n) self node node-bound cursor)
          (cond
           ((null item)
            (h4-book-equivalence-rewrite-positions
             (1- n) self left right bound term budget (cdr positions)
             (h4-book-equivalence-root-cursor self) paths pending order remaining))
           (t (let ((value (h4-book-equivalence-rewrite-value term place node (car item))))
                (h4-book-equivalence-with-result
                 self equality
                 (cond ((failure-p value) (cons value self))
                       ((or (assoc-equal value paths)
                            (> (h4-book-tactics-size value 150) bound))
                        (cons nil self))
                       (t (h4-book-equivalence-lift self term place (car item))))
                 (let ((paths (if equality
                                  (table-put paths value (list term equality))
                                paths)))
                   (if (and equality (equal value right))
                       (cons (h4-book-equivalence-equivalence-follow
                              self paths left right)
                             self)
                     (h4-book-equivalence-rewrite-positions
                      (1- n) self left right bound term budget positions (cdr item) paths
                      (if equality
                          (h4-book-equivalence-insert-pending
                           (list (h4-book-tactics-size value 150) order value)
                           pending)
                        pending)
                      (if equality (1+ order) order) remaining))))))))))))
 (defun h4-book-equivalence-establish-guard (n self guard)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h4-book-equivalence-establish-guard") self)
     (let ((tail (and (proof-is-call guard *proof-if*) (proof-term-at guard 3))))
       (cond
        ((failure-p tail) (cons tail self))
        ((equal tail *proof-false*)
         (h4-book-equivalence-with-result
          self first (h4-book-equivalence-establish-guard (1- n) self (cadr guard))
          (h4-book-equivalence-with-result
           self second (h4-book-equivalence-establish-guard (1- n) self (caddr guard))
           (cons (h4-tactics-tactics-conjunction
                  (h4-book-equivalence-library self) guard first second)
                 self))))
        (t (h4-book-equivalence-with-result
            self step (h4-book-equivalence-lookup
                       self guard (h4-book-equivalence-equivalence-premises self) 4)
            (cond
             (step (cons step self))
             ((not (proof-is-call guard (h4-book-equivalence-equivalence-relation self)))
              (cons '(:failure "Unproved" "") self))
             ((equal (len guard) 3)
              (h4-book-equivalence-rewrite (1- n) self (cadr guard) (caddr guard)))
             (t (cons '(:failure "failure" "") self)))))))))
 (defun h4-book-equivalence-guarded-rules (n self left right rules reverse-p)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "Fuel" "h4-book-equivalence-guarded-rules") self))
    ((endp rules)
     (if reverse-p
         (cons '(:failure "Unproved" "") self)
       (h4-book-equivalence-guarded-rules
        (1- n) self right left (h4-book-equivalence-equivalence-rules self) t)))
    (t (let* ((rule (car rules))
              (target (list (h4-book-equivalence-equivalence-relation self) left right))
              (match (and (h4-book-equivalence-guarded-rule-p rule)
                          (h4-tactics-match-term
                           (h4-book-tactics-rule-conclusion rule) target nil))))
         (cond
          ((failure-p match) (cons match self))
          ((not (car match))
           (h4-book-equivalence-guarded-rules (1- n) self left right (cdr rules) reverse-p))
          (t (let* ((p (h4-book-equivalence-library self))
                    (step (proof-proof-fact
                           (library-library-proof p)
                           (h4-book-tactics-rule-source rule)
                           (table-items (cdr match))))
                    (guard (if (failure-p step)
                               step
                             (h4-book-equivalence-instance-guard step)))
                    (reply (if (failure-p guard)
                               (cons guard self)
                             (h4-book-equivalence-establish-guard (1- n) self guard)))
                    (self (cdr reply))
                    (evidence (car reply)))
               (cond
                ((h4-book-equivalence-unproved-p evidence)
                 (h4-book-equivalence-guarded-rules
                  (1- n) self left right (cdr rules) reverse-p))
                ((failure-p evidence) reply)
                (t (let ((result (h4-tactics-tactics-modus-ponens p step evidence)))
                     (cons (if (and reverse-p (not (failure-p result)))
                               (h4-book-equivalence-equivalence-reverse self result)
                             result)
                           self))))))))))))

(defun h4-book-equivalence-at-root-collect (n term bound reply proofs)
  (declare (xargs :measure (nfix n)))
  (let ((item (car reply))
        (self (cdr reply)))
    (cond ((failure-p item) reply)
          ((null item) (cons (reverse proofs) self))
          ((zp n) (cons '(:failure "Fuel" "h4-book-equivalence-at-root-collect") self))
          (t (h4-book-equivalence-at-root-collect
              (1- n) term bound
              (h4-book-equivalence-at-root-next (1- n) self term bound (cdr item))
              (cons (car item) proofs))))))

(defun h4-book-equivalence-equivalence-at-root (self term bound)
  (h4-book-equivalence-finish
   (h4-book-equivalence-at-root-collect
    1000000 term bound
    (h4-book-equivalence-at-root-next 1000000 self term bound
                                      (h4-book-equivalence-root-cursor self))
    nil)))

(defun h4-book-equivalence-equivalence-replay-rewrite (self rule bindings)
  (h4-book-equivalence-finish
   (h4-book-equivalence-replay-rewrite 1000000 self rule bindings)))

(defun h4-book-equivalence-equivalence-rewrite (self left right)
  (h4-book-equivalence-finish (h4-book-equivalence-rewrite 1000000 self left right)))

(defun h4-book-equivalence-equivalence-establish-guard (self guard)
  (h4-book-equivalence-finish (h4-book-equivalence-establish-guard 1000000 self guard)))

(defun h4-book-equivalence-guarded (self left right)
  (h4-book-equivalence-guarded-rules
   1000000 self left right (h4-book-equivalence-equivalence-rules self) nil))

(defun h4-book-equivalence-equivalence-guarded (self left right)
  (h4-book-equivalence-finish (h4-book-equivalence-guarded self left right)))

(defun h4-book-equivalence-reset-matches (self)
  (h4-book-equivalence-equivalence-with-search
   self (h4-book-tactics-book-search-with-matches
         (h4-book-equivalence-equivalence-search self) 4200)))

(defun h4-book-equivalence-join-three (self first middle last)
  (proof-with-checked-results
      ((prefix (h4-book-equivalence-equivalence-compose self first middle)))
    (h4-book-equivalence-equivalence-compose self prefix last)))

(defun h4-book-equivalence-cancel-ends (self orientation left right)
  (let* ((self (h4-book-equivalence-reset-matches self))
         (first (h4-book-equivalence-instance-guard orientation)))
    (h4-book-equivalence-with-result
     self reduction
     (if (failure-p first)
         (cons first self)
       (h4-book-equivalence-rewrite 1000000 self first left))
     (let ((first (h4-book-equivalence-equivalence-reverse self reduction)))
       (if (failure-p first)
           (cons first self)
         (let* ((self (h4-book-equivalence-reset-matches self))
                (last (proof-with-checked-results
                          ((literal (proof-step-first orientation)))
                        (proof-term-at literal 2))))
           (h4-book-equivalence-with-result
            self last
            (if (failure-p last)
                (cons last self)
              (h4-book-equivalence-rewrite 1000000 self last right))
            (cons (list first last) self))))))))

(defun h4-book-equivalence-cancel-orientations (self orientations left right)
  (declare (xargs :measure (acl2-count orientations)))
  (if (endp orientations)
      (cons nil self)
    (let* ((middle (car orientations))
           (reply (h4-book-equivalence-cancel-ends self middle left right))
           (ends (car reply))
           (self (cdr reply)))
      (cond
       ((h4-book-equivalence-unproved-p ends)
        (h4-book-equivalence-cancel-orientations self (cdr orientations) left right))
       ((failure-p ends) reply)
       (t (cons (h4-book-equivalence-join-three self (car ends) middle (cadr ends))
                self))))))

(defun h4-book-equivalence-cancel-by-inverse
  (self step before product index triple left right)
  (if (not (equal (car triple) (car product)))
      (cons nil self)
    (let* ((operator (car triple))
           (inverse (cadr triple))
           (factor (list inverse (nth (- 3 index) product)))
           (context (if (equal index 1)
                        (list operator before factor)
                      (list operator factor before))))
      (h4-book-equivalence-with-result
       self middle (h4-book-equivalence-lift self context (list index) step)
       (if (not middle)
           (cons nil self)
         (let ((backward (h4-book-equivalence-equivalence-reverse self middle)))
           (if (failure-p backward)
               (cons backward self)
             (h4-book-equivalence-cancel-orientations
              self (list middle backward) left right))))))))

(defun h4-book-equivalence-cancel-inverses
  (self step before product index triples left right)
  (declare (xargs :measure (acl2-count triples)))
  (if (endp triples)
      (cons nil self)
    (h4-book-equivalence-with-result
     self result
     (h4-book-equivalence-cancel-by-inverse self step before product index
                                            (car triples) left right)
     (if result
         (cons result self)
       (h4-book-equivalence-cancel-inverses
        self step before product index (cdr triples) left right)))))

(defun h4-book-equivalence-cancel-indices (self step before product indices left right)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      (cons nil self)
    (h4-book-equivalence-with-result
     self result
     (h4-book-equivalence-cancel-inverses
      self step before product (car indices)
      (h4-book-equivalence-equivalence-inverses self) left right)
     (if result
         (cons result self)
       (h4-book-equivalence-cancel-indices self step before product
                                           (cdr indices) left right)))))

(defun h4-book-equivalence-cancel-factor-other-p (index product left right)
  (let ((argument (nth index product)))
    (and (not (equal argument left))
         (not (equal argument right)))))

(defun h4-book-equivalence-cancel-products (self step before products left right)
  (declare (xargs :measure (acl2-count products)))
  (if (endp products)
      (cons nil self)
    (let* ((product (car products))
           (operator (and (proof-compound product) (proof-term-at product 0)))
           (reply
            (cond
             ((failure-p operator) (cons operator self))
             ((and (proof-compound product) (not (proof-compound operator))
                   (equal (len product) 3))
              (let* ((first (h4-book-equivalence-cancel-factor-other-p 1 product left right))
                     (second (h4-book-equivalence-cancel-factor-other-p 2 product left right))
                     (indices (if (and first (not second)) '(2 1) '(1 2))))
                (h4-book-equivalence-cancel-indices self step before product
                                                    indices left right)))
             (t (cons nil self)))))
      (h4-book-equivalence-with-result
       self result reply
       (if result
           (cons result self)
         (h4-book-equivalence-cancel-products self step before (cdr products) left right))))))

(defun h4-book-equivalence-cancel-evidence (self evidence left right)
  (declare (xargs :measure (acl2-count evidence)))
  (if (endp evidence)
      (cons '(:failure "Unproved" "") self)
    (let* ((step (car evidence))
           (literal (proof-step-first step))
           (parts (cond ((failure-p literal) literal)
                        ((proof-is-call literal (h4-book-equivalence-equivalence-relation self))
                         (proof-list-of-length literal 3))
                        (t nil)))
           (reply (cond ((failure-p parts) (cons parts self))
                        (parts (h4-book-equivalence-cancel-products
                                self step (cadr parts)
                                (proof-unique (cdr parts)) left right))
                        (t (cons nil self)))))
      (h4-book-equivalence-with-result
       self result reply
       (if result
           (cons result self)
         (h4-book-equivalence-cancel-evidence self (cdr evidence) left right))))))

(defun h4-book-equivalence-cancel-factor (self left right evidence)
  (h4-book-equivalence-cancel-evidence
   self
   (if (eq evidence :none)
       (table-values (h4-book-equivalence-equivalence-premises self))
     evidence)
   left right))

(defun h4-book-equivalence-equivalence-cancel-factor (self left right evidence)
  (h4-book-equivalence-finish
   (h4-book-equivalence-cancel-factor self left right evidence)))

(defun h4-book-equivalence-left-inverse-product (premise)
  (proof-with-checked-results
      ((literal (proof-step-first premise))
       (sides (proof-list-of-length (cdr literal) 2)))
    (proof-list-of-length (car sides) 3)))

(defun h4-book-equivalence-cancel-left-inverse (self premise inverse identity)
  (let ((product (h4-book-equivalence-left-inverse-product premise)))
    (if (failure-p product)
        (cons product self)
      (let* ((operator (car product))
             (factor (cadr product))
             (survivor (caddr product))
             (inverse-factor (list inverse factor))
             (context (list operator inverse-factor product))
             (regrouped (list operator (list operator inverse-factor factor) survivor)))
        (h4-book-equivalence-with-result
         self associativity (h4-book-equivalence-guarded self context regrouped)
         (h4-book-equivalence-with-result
          self inverse-law (h4-book-equivalence-rewrite 1000000 self (cadr regrouped) identity)
          (h4-book-equivalence-with-result
           self identity-product
           (h4-book-equivalence-lift self regrouped '(1) inverse-law)
           (h4-book-equivalence-with-result
            self changed (h4-book-equivalence-lift self context '(2) premise)
            (if (not (and identity-product changed))
                (cons '(:failure "Unproved" "") self)
              (let ((subject
                     (proof-with-checked-results
                         ((literal (proof-step-first identity-product)))
                       (proof-term-at literal 2))))
                (h4-book-equivalence-with-result
                 self identity-law
                 (if (failure-p subject)
                     (cons subject self)
                   (h4-book-equivalence-guarded self subject survivor))
                 (cons
                  (proof-with-checked-results
                      ((cancelled (h4-book-equivalence-join-three
                                   self associativity identity-product identity-law))
                       (reversed (h4-book-equivalence-equivalence-reverse self cancelled)))
                    (h4-book-equivalence-equivalence-compose self reversed changed))
                  self))))))))))))

(defun h4-book-equivalence-equivalence-cancel-left-inverse (self premise inverse identity)
  (h4-book-equivalence-finish
   (h4-book-equivalence-cancel-left-inverse self premise inverse identity)))

(defun h4-book-equivalence-inverse-goal-target (other candidate triple)
  (let ((operator (car triple))
        (inverse (cadr triple))
        (identity (caddr triple)))
    (cond
     ((equal other identity)
      (list (list operator candidate candidate) candidate))
     ((proof-is-call other inverse)
      (proof-with-checked-results ((operand (proof-term-at other 1)))
        (list (list operator operand candidate) identity)))
     (t nil))))

(defun h4-book-equivalence-inverse-goal-attempt (self candidate other triple target)
  (h4-book-equivalence-with-result
   self premise (h4-book-equivalence-rewrite 1000000 self (car target) (cadr target))
   (if (and (proof-compound candidate) (equal (len candidate) 3)
            (not (equal (car candidate) (car triple))))
       (h4-book-equivalence-with-result
        self removed
        (h4-book-equivalence-cancel-left-inverse self premise (cadr triple) (caddr triple))
        (let ((value (proof-with-checked-results ((literal (proof-step-first removed)))
                       (proof-term-at literal 2))))
          (h4-book-equivalence-with-result
           self last
           (if (failure-p value)
               (cons value self)
             (h4-book-equivalence-rewrite 1000000 self value other))
           (cons (h4-book-equivalence-equivalence-compose self removed last) self))))
     (h4-book-equivalence-cancel-factor self candidate other (list premise)))))

(defun h4-book-equivalence-inverse-goal-inverses (self candidate other reverse-p triples)
  (declare (xargs :measure (acl2-count triples)))
  (if (endp triples)
      (cons nil self)
    (let* ((triple (car triples))
           (target (h4-book-equivalence-inverse-goal-target other candidate triple))
           (reply (cond ((failure-p target) (cons target self))
                        (target (h4-book-equivalence-inverse-goal-attempt
                                 self candidate other triple target))
                        (t (cons nil self))))
           (value (car reply))
           (self (cdr reply)))
      (cond
       ((or (null value) (h4-book-equivalence-unproved-p value))
        (h4-book-equivalence-inverse-goal-inverses self candidate other reverse-p
                                                    (cdr triples)))
       ((or (failure-p value) (not reverse-p)) reply)
       (t (cons (h4-book-equivalence-equivalence-reverse self value) self))))))

(defun h4-book-equivalence-inverse-goal (self left right)
  (let ((triples (h4-book-equivalence-equivalence-inverses self)))
    (h4-book-equivalence-with-result
     self forward (h4-book-equivalence-inverse-goal-inverses self left right nil triples)
     (if forward
         (cons forward self)
       (h4-book-equivalence-with-result
        self backward (h4-book-equivalence-inverse-goal-inverses self right left t triples)
        (cons (or backward '(:failure "Unproved" "")) self))))))

(defun h4-book-equivalence-equivalence-inverse-goal (self left right)
  (h4-book-equivalence-finish (h4-book-equivalence-inverse-goal self left right)))

(defun h4-book-equivalence-inverse-bridge-orientation (self inverse first second reverse-p)
  (let* ((middle (list inverse (list inverse second)))
         (reply (h4-book-equivalence-rewrite 1000000 self middle second))
         (removed (car reply))
         (self (cdr reply)))
    (cond
     ((h4-book-equivalence-unproved-p removed) (cons nil self))
     ((failure-p removed) reply)
     (t (let* ((reply (h4-book-equivalence-guarded self first middle))
               (introduced (car reply))
               (self (cdr reply)))
          (cond
           ((h4-book-equivalence-unproved-p introduced) (cons nil self))
           ((failure-p introduced) reply)
           (t (let ((step (h4-book-equivalence-equivalence-compose self introduced removed)))
                (cons (if (and reverse-p (not (failure-p step)))
                          (h4-book-equivalence-equivalence-reverse self step)
                        step)
                      self)))))))))

(defun h4-book-equivalence-inverse-bridge-inverses (self left right triples)
  (declare (xargs :measure (acl2-count triples)))
  (if (endp triples)
      (cons '(:failure "Unproved" "") self)
    (let ((inverse (cadar triples)))
      (h4-book-equivalence-with-result
       self forward (h4-book-equivalence-inverse-bridge-orientation self inverse left right nil)
       (if forward
           (cons forward self)
         (h4-book-equivalence-with-result
          self backward (h4-book-equivalence-inverse-bridge-orientation self inverse right left t)
          (if backward
              (cons backward self)
            (h4-book-equivalence-inverse-bridge-inverses self left right (cdr triples)))))))))

(defun h4-book-equivalence-equivalence-inverse-bridge (self left right)
  (h4-book-equivalence-finish
   (h4-book-equivalence-inverse-bridge-inverses
    self left right (h4-book-equivalence-equivalence-inverses self))))

(defun h4-book-equivalence-prove-in-order (self left right tactics)
  (declare (xargs :measure (acl2-count tactics)))
  (if (endp tactics)
      (cons '(:failure "Unproved" "") self)
    (let* ((self (h4-book-equivalence-reset-matches self))
           (reply (case (car tactics)
                    (:rewrite (h4-book-equivalence-rewrite 1000000 self left right))
                    (:guarded (h4-book-equivalence-guarded self left right))
                    (:cancel-factor (h4-book-equivalence-cancel-factor self left right :none))
                    (:inverse-goal (h4-book-equivalence-inverse-goal self left right))
                    (otherwise (h4-book-equivalence-inverse-bridge-inverses
                                self left right
                                (h4-book-equivalence-equivalence-inverses self))))))
      (if (h4-book-equivalence-unproved-p (car reply))
          (h4-book-equivalence-prove-in-order (cdr reply) left right (cdr tactics))
        reply))))

(defun h4-book-equivalence-prove (self left right)
  (h4-book-equivalence-prove-in-order
   self left right '(:rewrite :guarded :cancel-factor :inverse-goal :inverse-bridge)))

(defun h4-book-equivalence-equivalence-prove (self left right)
  (h4-book-equivalence-finish (h4-book-equivalence-prove self left right)))

(defun h4-book-equivalence-equivalence-true-value (self step)
  (let* ((p (h4-book-equivalence-library self))
         (proof (library-library-proof p))
         (law (h4-book-equivalence-equivalence-boolean self)))
    (proof-with-checked-results
        ((pattern (h4-book-equivalence-instance-guard law))
         (bindings (h4-book-equivalence-match-proof pattern step))
         (boolean (proof-proof-instantiate proof law (table-items bindings)))
         (literal (proof-step-first step))
         (exact (proof-eq literal *proof-true*))
         (negative (proof-proof-assume proof exact nil))
         (boolean-literal (proof-step-first boolean))
         (reduced (h4-tactics-tactics-normalize
                   p boolean-literal (list negative)
                   (list *h4-book-equivalence-booleanp* (proof-cl "EQ"))
                   nil nil))
         (false-value (proof-proof-rewrite proof boolean reduced '(1)))
         (rewritten (proof-proof-rewrite proof step false-value '(1)))
         (tidied (proof-proof-tidy proof rewritten)))
      (proof-proof-front proof tidied exact))))

(defun h4-book-equivalence-equivalence-equality-equal-when-true
  (hypothesis p forward right-true)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((left (h4-book-equivalence-equivalence-true-value forward hypothesis))
         (right (h4-book-equivalence-equivalence-true-value forward right-true))
         (symmetric (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list symmetric)))))

(defun h4-book-equivalence-equivalence-equality-equal-when-false
  (hypothesis p left-true right)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((cut (proof-proof-cut proof left-true hypothesis))
         (right-false (proof-proof-front proof cut (proof-neg right)))
         (left-value (h4-tactics-tactics-nil-value p hypothesis))
         (right-value (h4-tactics-tactics-nil-value p right-false))
         (symmetric (proof-proof-symmetric proof right-value)))
      (proof-proof-chain proof left-value (list symmetric)))))

(defun h4-book-equivalence-equality-cases (p forward left right right-true left-true)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((positive (proof-proof-assume proof left t))
         (yes (h4-book-equivalence-equivalence-equality-equal-when-true
               positive p forward right-true))
         (negative (proof-proof-assume proof left nil))
         (no (h4-book-equivalence-equivalence-equality-equal-when-false
              negative p left-true right)))
      (h4-tactics-tactics-case-of p (proof-eq left right) left yes no))))

(defun h4-book-equivalence-prove-operands (self operands)
  (if (equal (len operands) 2)
      (h4-book-equivalence-prove self (car operands) (cadr operands))
    (cons '(:failure "failure" "") self)))

(defun h4-book-equivalence-equivalence-equality-run (search relation name premises left right)
  (let* ((p (h4-book-tactics-book-search-p search))
         (proof (library-library-proof p))
         (directions
          (proof-with-checked-results
              ((assumed-left (proof-proof-assume proof left t))
               (assumed-right (proof-proof-assume proof right t))
               (forward (h4-book-equivalence-equivalence-init
                         search relation name (append premises (list assumed-left))))
               (backward (h4-book-equivalence-equivalence-init
                          (h4-book-equivalence-equivalence-search forward)
                          relation name (append premises (list assumed-right)))))
            (list forward backward))))
    (if (failure-p directions)
        (cons directions search)
      (let* ((backward (cadr directions))
             (forward (h4-book-equivalence-equivalence-with-search
                       (car directions)
                       (h4-book-equivalence-equivalence-search backward)))
             (forward-result (h4-book-equivalence-prove-operands forward (cdr right)))
             (right-true (car forward-result))
             (forward (cdr forward-result))
             (search (h4-book-equivalence-equivalence-search forward)))
        (if (failure-p right-true)
            (cons right-true search)
          (let* ((backward (h4-book-equivalence-equivalence-with-search backward search))
                 (backward-result (h4-book-equivalence-prove-operands backward (cdr left)))
                 (left-true (car backward-result))
                 (search (h4-book-equivalence-equivalence-search (cdr backward-result))))
            (cons (if (failure-p left-true)
                      left-true
                    (h4-book-equivalence-equality-cases
                     p forward left right right-true left-true))
                  search)))))))

(defun h4-book-equivalence-equivalence-equality (search relation name premises left right)
  (h4-book-equivalence-finish
   (h4-book-equivalence-equivalence-equality-run search relation name premises left right)))

(defun h4-book-equivalence-setoid-split (n goal conclusions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "h4-book-equivalence-setoid-split"))
   ((proof-is-call goal *library-implies*)
    (proof-with-checked-results ((next (proof-term-at goal 2)))
      (h4-book-equivalence-setoid-split (1- n) next (cons goal conclusions))))
   (t (cons goal conclusions))))

(defun h4-book-equivalence-equality-relation (left right)
  (and (proof-compound left)
       (proof-with-checked-results ((head (proof-term-at left 0)))
         (and (proof-is-call right head)
              (equal (len left) 3)
              (equal (len right) 3)
              (not (proof-compound head))
              head))))

(defun h4-book-equivalence-require-name-part (datum)
  (if (stringp datum)
      datum
    '(:failure "failure" "")))

(defun h4-book-equivalence-law-name (relation)
  (proof-with-checked-results
      ((name (proof-term-at relation 2))
       (name (h4-book-equivalence-require-name-part name))
       (package (proof-term-at relation 1))
       (package (h4-book-equivalence-require-name-part package)))
    (proof-sym (concatenate 'string name "-IS-AN-EQUIVALENCE") package)))

(defun h4-book-equivalence-setoid-assumptions (proof implications)
  (if (endp implications)
      nil
    (proof-with-checked-results
        ((guard (proof-term-at (car implications) 1))
         (step (proof-proof-assume proof guard t))
         (rest (h4-book-equivalence-setoid-assumptions proof (cdr implications))))
      (cons step rest))))

(defun h4-book-equivalence-setoid-imply (p implications step)
  (if (endp implications)
      step
    (proof-with-checked-results
        ((next (h4-tactics-tactics-imply p (car implications) step)))
      (h4-book-equivalence-setoid-imply p (cdr implications) next))))

(defun h4-book-equivalence-setoid-relation (search relation name premises left right)
  (let ((self (h4-book-equivalence-equivalence-init search relation name premises)))
    (if (failure-p self)
        (cons self search)
      (let ((reply (h4-book-equivalence-prove self left right)))
        (cons (car reply)
              (h4-book-equivalence-equivalence-search (cdr reply)))))))

(defun h4-book-equivalence-setoid-try
  (search formula conclusions equality-p relation name premises left right)
  (let* ((p (h4-book-tactics-book-search-p search))
         (proof (library-library-proof p))
         (reply (if equality-p
                    (h4-book-equivalence-equivalence-equality-run
                     search relation name premises left right)
                  (h4-book-equivalence-setoid-relation
                   search relation name premises left right)))
         (step (car reply))
         (result (if (failure-p step)
                     step
                   (proof-with-checked-results
                       ((implication (h4-book-equivalence-setoid-imply p conclusions step)))
                     (proof-proof-subsume proof implication (list formula))))))
    (cond ((or (h4-book-equivalence-unproved-p result)
               (and (failure-p result)
                    (member-equal (cadr result) '("InapplicableStep" "assertion"))))
           (cons nil (cdr reply)))
          ((failure-p result) result)
          (t (cons result (cdr reply))))))

(defun h4-book-equivalence-setoid-proof (search formula)
  (proof-with-checked-results
      ((split (h4-book-equivalence-setoid-split 1000000 formula nil)))
    (let* ((goal (car split))
           (conclusions (cdr split))
           (head (car goal))
           (left (cadr goal))
           (right (caddr goal)))
      (if (or (not (proof-compound goal))
              (not (equal (len goal) 3))
              (proof-compound head))
          (cons nil search)
        (let ((equality-p (equal head *proof-equal*)))
          (proof-with-checked-results
              ((relation (if equality-p
                             (h4-book-equivalence-equality-relation left right)
                           head)))
            (if (not relation)
                (cons nil search)
              (let* ((p (h4-book-tactics-book-search-p search))
                     (proof (library-library-proof p)))
                (proof-with-checked-results
                    ((name (h4-book-equivalence-law-name relation)))
                  (if (not (assoc-equal name (proof-proof-facts proof)))
                      (cons nil search)
                    (proof-with-checked-results
                        ((premises (h4-book-equivalence-setoid-assumptions
                                    proof (reverse conclusions))))
                      (h4-book-equivalence-setoid-try
                       search formula conclusions equality-p relation name
                       premises left right))))))))))))
