(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-record-extensionality-difference* '("sym" "ACL2" "B2-RECORD-DIFFERENCE"))
(defconst *b2-record-extensionality-above* '("sym" "ACL2" "B2-RECORD-DIFFERENCE-ABOVE"))
(defconst *b2-record-extensionality-witness* '("sym" "ACL2" "B2-RECORD-DIFFERENCE-WITNESS"))
(defconst *b2-record-extensionality-u* '("sym" "ACL2" "U"))
(defconst *b2-record-extensionality-e* '("sym" "ACL2" "E"))
(defconst *b2-record-extensionality-get* '("sym" "ACL2" "G"))
(defconst *b2-record-extensionality-set* '("sym" "ACL2" "S"))
(defconst *b2-record-extensionality-get-update* '("sym" "ACL2" "G-OF-S-REDUX"))
(defconst *b2-record-extensionality-extensional*
  '(("sym" "ACL2" "EQUAL-BY-G") ("sym" "ACL2" "S-DIFF-S") ("sym" "ACL2" "S-SAME-S")))

(defun b2-record-extensionality-step-argument (step index)
  (proof-with-checked-results ((literal (b2-record-update-first step)))
    (proof-term-at literal index)))

(defun b2-record-extensionality-install-difference (lib)
  (let* ((proof (library-library-proof lib))
         (name *b2-record-extensionality-difference*)
         (r *b2-record-update-r*)
         (u *b2-record-extensionality-u*))
    (if (assoc-equal name (proof-proof-definitions proof))
        lib
      (let* ((a (b2-record-update-key r))
             (b (b2-record-update-key u))
             (tail (list name (list *library-cdr* r) (list *library-cdr* u)))
             (distinct (proof-ite (list *b2-strict-order-strict* a b) a b))
             (both (proof-ite
                    (proof-eq a b)
                    (proof-ite (proof-eq (b2-record-update-value r) (b2-record-update-value u))
                               tail a)
                    distinct))
             (body (proof-ite (list *proof-consp* r)
                              (proof-ite (list *proof-consp* u) both a)
                              b))
             (definitions (list (list name (list r u) body))))
        (proof-with-checked-results
            ((source (proof-line "define" (cons *termination-all* definitions)))
             (lib (library-library-with-entries
                   lib (append (library-library-entries lib) (list (list "define" name nil source)))))
             (calls (termination-recursive-calls *termination-all* definitions))
             (measure (b2-measures-prove-measure
                       lib definitions calls (list (cons name (list *library-count* r)))))
             (entry (car measure))
             (lib (cdr measure))
             (lib (library-library-with-entries lib (append (library-library-entries lib) (list entry))))
             (proof (proof-proof-add-definition (library-library-proof lib) name (list r u) body)))
          (library-library-with-proof lib proof))))))

(defun b2-record-extensionality-contradict (lib goal first second)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((impossible (proof-proof-cut proof first second)))
      (proof-proof-subsume proof impossible (cons goal (proof-step-clause impossible))))))

(defun b2-record-extensionality-different-tails-rebuilt (record lib known)
  (let ((proof (library-library-proof lib))
        (head (list *library-car* record)))
    (proof-with-checked-results
        ((cons-step (b2-record-update-evidence-at known (list *proof-consp* record)))
         (outer (b2-tactics-rebuild lib record cons-step))
         (cons-step (b2-record-update-evidence-at known (list *proof-consp* head)))
         (pair (b2-tactics-rebuild lib head cons-step))
         (reverse (proof-proof-symmetric proof pair))
         (rewritten (proof-proof-rewrite proof outer reverse '(1 1 1))))
      (proof-proof-tidy proof rewritten))))

(defun b2-record-extensionality-different-tails (lib facts)
  (let* ((proof (library-library-proof lib))
         (r *b2-record-update-r*)
         (u *b2-record-extensionality-u*)
         (tail-r (list *library-cdr* r))
         (tail-u (list *library-cdr* u))
         (test (proof-eq tail-r tail-u)))
    (proof-with-checked-results
        ((equals (proof-proof-assume proof test t))
         (known (b2-tactics-tactics-evidence lib facts))
         (rebuilt (b2-record-extensionality-different-tails-rebuilt r lib known))
         (from-r (proof-proof-symmetric proof rebuilt))
         (keys-equal (b2-record-update-evidence-at
                      known (proof-eq (b2-record-update-key r) (b2-record-update-key u))))
         (from-r (proof-proof-rewrite proof from-r keys-equal '(1 2 1 1)))
         (values-equal (b2-record-update-evidence-at
                        known (proof-eq (b2-record-update-value r) (b2-record-update-value u))))
         (from-r (proof-proof-rewrite proof from-r values-equal '(1 2 1 2)))
         (from-r (proof-proof-rewrite proof from-r equals '(1 2 2)))
         (rebuilt (b2-record-extensionality-different-tails-rebuilt u lib known))
         (same (proof-proof-chain proof from-r (list rebuilt)))
         (different (b2-record-update-evidence-at known (proof-neg (proof-eq r u))))
         (contradiction (proof-proof-cut proof same different)))
      (proof-proof-front proof contradiction (proof-neg test)))))

(defun b2-record-extensionality-after-head-branch
    (empty evidence lib start head record before bound goal)
  (proof-with-checked-results
      ((updated (if empty
                    evidence
                  (proof-with-checked-results
                      ((later (proof-proof-prove-if (library-library-proof lib) bound
                                                    (car (last evidence))))
                       (order (b2-record-update-ordered-after
                               lib start head (b2-record-update-key record) before later)))
                    (append evidence (list order))))))
    (b2-tactics-tactics-solve lib goal updated nil nil 0 nil)))

(defun b2-record-extensionality-after-head-case (empty args lib start head record before bound goal)
  (b2-record-extensionality-after-head-branch empty (car args) lib start head record before bound goal))

(defun b2-record-extensionality-after-head (lib start head record before bound)
  (let ((goal (b2-record-update-order-or-empty start record)))
    (b2-record-update-choose
     lib (proof-eq record *proof-false*) nil
     b2-record-extensionality-after-head-case start head record before bound goal)))

(defun b2-record-extensionality-self-comparison (lib key-value)
  (proof-proof-fact (library-library-proof lib) (proof-sym "<<-IRREFLEXIVE" "ACL2")
                    (list (list *library-x* key-value))))

(defun b2-record-extensionality-first-key-laws (lib lookup-key record-key order)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((backward (b2-tactics-tactics-use-fact
                    lib (proof-sym "<<-ASYMMETRIC" "ACL2")
                    (proof-neg (list *b2-strict-order-strict* lookup-key record-key))
                    (list order) nil nil 0 nil))
         (comparable (proof-eq lookup-key record-key))
         (assumption (proof-proof-assume proof comparable t))
         (without (proof-proof-rewrite proof order assumption '(1 2)))
         (irreflexive (b2-record-extensionality-self-comparison lib record-key))
         (cut (proof-proof-cut proof without irreflexive))
         (distinct (proof-proof-front proof cut (proof-neg comparable))))
      (list backward distinct))))

(defun b2-record-extensionality-difference-lemma-selected
    (record evidence lib is-bound target openers)
  (let ((head (b2-record-update-key record))
        (proof (library-library-proof lib))
        (r *b2-record-update-r*)
        (u *b2-record-extensionality-u*))
    (if is-bound
        (proof-with-checked-results
            ((order (b2-record-update-head-order lib *b2-record-extensionality-e* record evidence)))
          (b2-tactics-tactics-solve lib target (append evidence (list order)) openers nil 0 nil))
      (proof-with-checked-results
          ((known (b2-tactics-tactics-evidence lib evidence))
           (reflexive (b2-record-extensionality-self-comparison lib head))
           (equality (proof-proof-reflexive proof head))
           (facts (append evidence (list reflexive equality)))
           (other (if (equal record r) u r))
           (keys-equal (proof-eq (b2-record-update-key r) (b2-record-update-key u)))
           (facts
            (if (or (assoc-equal (proof-eq other *proof-false*) known)
                    (assoc-equal (proof-neg keys-equal) known))
                (let ((value (b2-record-update-value record)))
                  (proof-with-checked-results
                      ((present (b2-record-update-evidence-at known value))
                       (distinct (b2-tactics-tactics-from-impossible
                                  lib (proof-neg (proof-eq value *proof-false*))
                                  present nil nil nil 1500 nil))
                       (flipped (b2-strict-order-flipped-distinct lib value *proof-false* distinct)))
                    (append facts (list distinct flipped))))
              (proof-with-checked-results
                  ((same (b2-record-update-evidence-at known keys-equal))
                   (changed (proof-proof-rewrite proof reflexive same '(1 1 2)))
                   (changed (proof-proof-tidy proof changed)))
                (append facts (list changed))))))
        (b2-tactics-tactics-solve lib target facts openers nil 0 nil)))))

(defun b2-record-extensionality-difference-lemma-shared-head-bound
    (lib evidence induction target openers guards left-bound right-bound)
  (let* ((proof (library-library-proof lib))
         (r *b2-record-update-r*)
         (u *b2-record-extensionality-u*)
         (limit *b2-record-extensionality-e*))
    (proof-with-checked-results
        ((before (b2-record-update-head-order lib limit r evidence))
         (left (b2-record-extensionality-after-head
                lib limit (b2-record-update-key r) (list *library-cdr* r) before left-bound))
         (before (b2-record-update-head-order lib limit u evidence))
         (right (b2-record-extensionality-after-head
                 lib limit (b2-record-update-key u) (list *library-cdr* u) before right-bound))
         (condition (b2-record-extensionality-step-argument induction 1))
         (premise (b2-tactics-tactics-solve
                   lib condition (append guards (list left right)) nil nil 0 nil))
         (inherited (proof-proof-modus-ponens proof induction premise)))
      (b2-tactics-tactics-solve lib target (append evidence (list inherited)) openers nil 0 nil))))

(defun b2-record-extensionality-difference-lemma-shared-head-witness
    (lib evidence induction target openers known guards left-bound right-bound)
  (let* ((proof (library-library-proof lib))
         (r *b2-record-update-r*)
         (u *b2-record-extensionality-u*)
         (head-r (b2-record-update-key r))
         (head-u (b2-record-update-key u))
         (smaller-call (list *b2-record-extensionality-difference*
                             (list *library-cdr* r) (list *library-cdr* u))))
    (proof-with-checked-results
        ((same (b2-record-update-evidence-at known (proof-eq head-r head-u)))
         (reverse (proof-proof-symmetric proof same))
         (both-above (proof-proof-rewrite proof right-bound reverse '(1 3 1)))
         (both-above (proof-proof-tidy proof both-above))
         (bounds (b2-tactics-tactics-use-fact
                  lib *b2-record-extensionality-above* (list *b2-strict-order-strict* head-r smaller-call)
                  (append guards (list left-bound both-above)) nil nil 0 nil))
         (other-bound (proof-proof-rewrite proof bounds same '(1 1)))
         (other-bound (proof-proof-tidy proof other-bound))
         (passed (b2-record-extensionality-first-key-laws lib smaller-call head-r bounds))
         (other-passed (b2-record-extensionality-first-key-laws lib smaller-call head-u other-bound))
         (condition (b2-record-extensionality-step-argument induction 1))
         (premise (b2-tactics-tactics-solve lib condition guards nil nil 0 nil))
         (inherited (proof-proof-modus-ponens proof induction premise)))
      (b2-tactics-tactics-solve
       lib target (append evidence passed other-passed (list inherited)) openers nil 0 nil))))

(defun b2-record-extensionality-pair-cases-absent
    (right-facts lib evidence goal known left is-bound openers)
  (let ((proof (library-library-proof lib))
        (facts (append evidence right-facts))
        (r *b2-record-update-r*)
        (u *b2-record-extensionality-u*))
    (if left
        (b2-record-extensionality-difference-lemma-selected r facts lib is-bound goal openers)
      (proof-with-checked-results
          ((premises (b2-tactics-tactics-evidence lib facts))
           (left (b2-record-update-evidence-at premises (proof-eq r *proof-false*)))
           (right (b2-record-update-evidence-at premises (proof-eq u *proof-false*)))
           (reverse (proof-proof-symmetric proof right))
           (identical (proof-proof-chain proof left (list reverse)))
           (different (b2-record-update-evidence-at known (proof-neg (proof-eq r u)))))
        (b2-record-extensionality-contradict lib goal identical different)))))

(defun b2-record-extensionality-pair-cases-present-heads-order
    (earlier facts lib goal is-bound openers different)
  (let ((r *b2-record-update-r*)
        (u *b2-record-extensionality-u*))
    (if earlier
        (b2-record-extensionality-difference-lemma-selected r facts lib is-bound goal openers)
      (proof-with-checked-results
          ((reverse (b2-record-update-smaller
                     lib (b2-record-update-key r) (b2-record-update-key u) different
                     (car (last facts)))))
        (b2-record-extensionality-difference-lemma-selected
         u (append facts (list reverse)) lib is-bound goal openers)))))

; The shared-head case of the witness requests the bound lemma.
(mutual-recursion
 (defun b2-record-extensionality-difference-lemma-run (n lib is-bound)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-difference-lemma-run")
     (let ((name (if is-bound *b2-record-extensionality-above* *b2-record-extensionality-witness*)))
       (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
           lib
         (proof-with-checked-results ((lib (b2-record-extensionality-install-difference lib)))
           (let* ((r *b2-record-update-r*)
                  (u *b2-record-extensionality-u*)
                  (tail-u (list *library-cdr* u))
                  (call (list *b2-record-extensionality-difference* r u))
                  (left (list *b2-record-update-get-aux* call r))
                  (right (list *b2-record-update-get-aux* call u))
                  (basic (list (list *b2-record-update-rcdp* r)
                               (list *b2-record-update-rcdp* u)
                               (proof-neg (proof-eq r u))))
                  (limit *b2-record-extensionality-e*)
                  (target (if is-bound
                              (list *b2-strict-order-strict* limit call)
                            (proof-neg (proof-eq left right))))
                  (openers (if is-bound (list call) (list call left right)))
                  (label (if is-bound "RECORD-DIFFERENCE-ABOVE" "RECORD-DIFFERENCE-WITNESS")))
             (proof-with-checked-results
                 ((condition (b2-powers-and-terms
                              (if is-bound
                                  (append basic (list (b2-record-update-order-or-empty limit r)
                                                      (b2-record-update-order-or-empty limit u)))
                                basic)))
                  (request (b2-record-update-record-induction
                            lib label condition target openers t (list (list u tail-u)))))
               (b2-record-extensionality-difference-lemma-induction
                (1- n) request is-bound target openers))))))))

 (defun b2-record-extensionality-difference-lemma-induction (n request is-bound target openers)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-difference-lemma-induction")
     (proof-with-checked-results ((value (car request)))
       (if (b2-record-update-request-p value)
           (let ((args (caddr value)))
             (proof-with-checked-results
                 ((result (if (eq (cadr value) :advance)
                              (b2-record-extensionality-difference-lemma-advance
                               (1- n) (car args) (cadr args) (cdr request) target is-bound openers)
                            (b2-record-extensionality-difference-lemma-base
                             (1- n) (car args) (cdr request) target is-bound openers)))
                  (next (b2-record-update-record-induction-resume
                         (cdr result) (cadddr value) (car result))))
               (b2-record-extensionality-difference-lemma-induction
                (1- n) next is-bound target openers)))
         (cdr request)))))

 (defun b2-record-extensionality-difference-lemma-advance
     (n evidence induction lib target is-bound openers)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-difference-lemma-advance")
     (b2-record-extensionality-pair-cases (1- n) lib evidence target is-bound openers induction)))

 (defun b2-record-extensionality-difference-lemma-base (n evidence lib target is-bound openers)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-difference-lemma-base")
     (b2-record-extensionality-pair-cases (1- n) lib evidence target is-bound openers nil)))

 (defun b2-record-extensionality-pair-cases (n lib evidence goal is-bound openers induction)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-pair-cases")
     (proof-with-checked-results
         ((known (b2-tactics-tactics-evidence lib evidence))
          (typed (b2-record-update-evidence-at
                  known (list *b2-record-update-rcdp* *b2-record-extensionality-u*)))
          (left (assoc-equal (list *proof-consp* *b2-record-update-r*) known))
          (request (b2-record-update-with-record lib *b2-record-extensionality-u* typed)))
       (b2-record-extensionality-pair-cases-record
        (1- n) request evidence goal known left is-bound openers induction))))

 (defun b2-record-extensionality-pair-cases-record
     (n request evidence goal known left is-bound openers induction)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-pair-cases-record")
     (proof-with-checked-results ((value (car request)))
       (if (b2-record-update-request-p value)
           (let* ((lib (cdr request))
                  (right-facts (car (caddr value))))
             (proof-with-checked-results
                 ((result (if (eq (cadr value) :empty)
                              (proof-with-checked-results
                                  ((step (b2-record-extensionality-pair-cases-absent
                                          right-facts lib evidence goal known left is-bound openers)))
                                (cons step lib))
                            (b2-record-extensionality-pair-cases-present
                             (1- n) right-facts lib evidence goal left is-bound openers induction)))
                  (next (b2-record-update-with-record-resume (cdr result) (cadddr value) (car result))))
               (b2-record-extensionality-pair-cases-record
                (1- n) next evidence goal known left is-bound openers induction)))
         request))))

 (defun b2-record-extensionality-pair-cases-present
     (n right-facts lib evidence goal left is-bound openers induction)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-pair-cases-present")
     (let ((facts (append evidence right-facts))
           (r *b2-record-update-r*)
           (u *b2-record-extensionality-u*))
       (if (not left)
           (proof-with-checked-results
               ((step (b2-record-extensionality-difference-lemma-selected
                       u facts lib is-bound goal openers)))
             (cons step lib))
         (b2-record-extensionality-pair-cases-choose
          (1- n)
          (b2-record-update-case-request
           lib (proof-eq (b2-record-update-key r) (b2-record-update-key u)) facts nil)
          :heads goal is-bound openers induction nil)))))

 (defun b2-record-extensionality-pair-cases-present-heads
     (n equal-heads branch lib goal is-bound openers induction)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-pair-cases-present-heads")
     (let ((r *b2-record-update-r*)
           (u *b2-record-extensionality-u*))
       (if equal-heads
           (b2-record-extensionality-pair-cases-choose
            (1- n)
            (b2-record-update-case-request
             lib (proof-eq (b2-record-update-value r) (b2-record-update-value u)) branch nil)
            :values goal is-bound openers induction nil)
         (b2-record-extensionality-pair-cases-choose
          (1- n)
          (b2-record-update-case-request
           lib (list *b2-strict-order-strict* (b2-record-update-key r) (b2-record-update-key u))
           branch nil)
          :order goal is-bound openers induction (car (last branch)))))))

 (defun b2-record-extensionality-pair-cases-choose
     (n request branch goal is-bound openers induction different)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-pair-cases-choose")
     (proof-with-checked-results ((value (car request)))
       (if (b2-record-update-request-p value)
           (proof-with-checked-results
               ((result (b2-record-extensionality-pair-cases-branch
                         (1- n) (cdr request) (cadr value) (car (caddr value))
                         branch goal is-bound openers induction different))
                (next (b2-record-update-case-resume (cdr result) (cadddr value) (car result))))
             (b2-record-extensionality-pair-cases-choose
              (1- n) next branch goal is-bound openers induction different))
         request))))

 (defun b2-record-extensionality-pair-cases-branch
     (n lib sign facts branch goal is-bound openers induction different)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-pair-cases-branch")
     (let ((r *b2-record-update-r*))
       (cond
        ((eq branch :heads)
         (b2-record-extensionality-pair-cases-present-heads
          (1- n) sign facts lib goal is-bound openers induction))
        ((and (eq branch :values) sign)
         (if induction
             (b2-record-extensionality-difference-lemma-shared-head
              (1- n) facts induction lib is-bound goal openers)
           '(:failure "tactic-rejected" "")))
        ((eq branch :order)
         (proof-with-checked-results
             ((step (b2-record-extensionality-pair-cases-present-heads-order
                     sign facts lib goal is-bound openers different)))
           (cons step lib)))
        (t (proof-with-checked-results
               ((step (b2-record-extensionality-difference-lemma-selected
                       r facts lib is-bound goal openers)))
             (cons step lib)))))))

 (defun b2-record-extensionality-difference-lemma-shared-head
     (n evidence induction lib is-bound target openers)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-record-extensionality-difference-lemma-shared-head")
     (let* ((r *b2-record-update-r*)
            (u *b2-record-extensionality-u*)
            (tail-r (list *library-cdr* r))
            (tail-u (list *library-cdr* u)))
       (proof-with-checked-results
           ((known (b2-tactics-tactics-evidence lib evidence))
            (typed-r (b2-record-update-evidence-at known (list *b2-record-update-rcdp* tail-r)))
            (typed-u (b2-record-update-evidence-at known (list *b2-record-update-rcdp* tail-u)))
            (tails (b2-record-extensionality-different-tails lib evidence))
            (guards (list typed-r typed-u tails))
            (left-bound (b2-record-update-evidence-at
                         known (b2-record-update-order-or-empty (b2-record-update-key r) tail-r)))
            (right-bound (b2-record-update-evidence-at
                          known (b2-record-update-order-or-empty (b2-record-update-key u) tail-u)))
            (lib (if is-bound lib (b2-record-extensionality-difference-lemma-run (1- n) lib t)))
            (step (if is-bound
                      (b2-record-extensionality-difference-lemma-shared-head-bound
                       lib evidence induction target openers guards left-bound right-bound)
                    (b2-record-extensionality-difference-lemma-shared-head-witness
                     lib evidence induction target openers known guards left-bound right-bound))))
         (cons step lib))))))

(defun b2-record-extensionality-difference-lemma (lib is-bound)
  (b2-record-extensionality-difference-lemma-run 1000000 lib is-bound))

(defun b2-record-extensionality-updated-lookup-rules (n lib lookup-key record rules keys)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n)))
    '(:failure "Fuel" "b2-record-extensionality-updated-lookup-rules"))
   ((not (proof-is-call record *b2-record-extensionality-set*)) (list rules keys))
   (t
    (proof-with-checked-results
        ((parts (proof-list-of-length record 4))
         (key-value (cadr parts))
         (value (caddr parts))
         (inner (cadddr parts))
         (get *b2-record-extensionality-get*)
         (lookup (list get lookup-key record))
         (rhs (proof-ite (proof-eq lookup-key key-value) value (list get lookup-key inner)))
         (name *b2-record-extensionality-get-update*)
         (facts (proof-proof-facts (library-library-proof lib)))
         (clause (b2-record-update-evidence-at facts name))
         (claim (proof-term-at clause 0))
         (rule (b2-tactics-tactics-exact lib name claim (proof-eq lookup rhs))))
      (b2-record-extensionality-updated-lookup-rules
       (1- n) lib lookup-key inner (append rules (list rule))
       (if (member-equal key-value keys) keys (append keys (list key-value))))))))

(defun b2-record-extensionality-updated-lookup-prove-finish (lib target rules premise evidence matches)
  (if (not (equal (len matches) 2))
      (b2-tactics-tactics-solve lib target evidence nil rules 0 nil)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((reverse (proof-proof-symmetric proof (car matches)))
           (equal-keys (proof-proof-chain proof reverse (list (cadr matches))))
           (literal (proof-step-first equal-keys))
           (expected (b2-record-extensionality-step-argument premise 1))
           (equal-keys (if (equal literal expected)
                           equal-keys
                         (proof-proof-symmetric proof equal-keys))))
        (b2-record-extensionality-contradict lib target equal-keys premise)))))

(defun b2-record-extensionality-updated-lookup-matches (sign facts matches)
  (if sign (append matches (list (car (last facts)))) matches))

(defun b2-record-extensionality-updated-lookup-prove
    (keys evidence matches lib lookup-key target rules premise)
  (if (endp keys)
      (b2-record-extensionality-updated-lookup-prove-finish lib target rules premise evidence matches)
    (let ((test (proof-eq lookup-key (car keys))))
      (proof-with-checked-results
          ((first (b2-record-update-case-request lib test evidence nil))
           (call (car first))
           (facts (car (caddr call)))
           (answer (b2-record-extensionality-updated-lookup-prove
                    (cdr keys) facts
                    (b2-record-extensionality-updated-lookup-matches (cadr call) facts matches)
                    (cdr first) lookup-key target rules premise))
           (second (b2-record-update-case-resume (cdr first) (cadddr call) answer))
           (call (car second)))
        (if (b2-record-update-request-p call)
            (let ((facts (car (caddr call))))
              (proof-with-checked-results
                  ((answer (b2-record-extensionality-updated-lookup-prove
                            (cdr keys) facts
                            (b2-record-extensionality-updated-lookup-matches
                             (cadr call) facts matches)
                            (cdr second) lookup-key target rules premise))
                   (result (b2-record-update-case-resume (cdr second) (cadddr call) answer)))
                (car result)))
          call)))))

(defun b2-record-extensionality-updated-lookup (lib lookup-key left right premise)
  (let* ((get *b2-record-extensionality-get*)
         (target (proof-eq (list get lookup-key left) (list get lookup-key right))))
    (proof-with-checked-results
        ((entries (b2-record-extensionality-updated-lookup-rules
                   1000000 lib lookup-key left nil nil))
         (entries (b2-record-extensionality-updated-lookup-rules
                   1000000 lib lookup-key right (car entries) (cadr entries))))
      (b2-record-extensionality-updated-lookup-prove
       (cadr entries) nil nil lib lookup-key target (car entries) premise))))

(defun b2-record-extensionality-lookup-equality (lib key-value a b use-constraint premise)
  (if use-constraint
      (let ((get *b2-record-extensionality-get*))
        (b2-tactics-tactics-use-fact
         lib (proof-sym "EQUAL-BY-G-CONSTRAINT" "ACL2")
         (proof-eq (list get key-value a) (list get key-value b))
         (list premise) nil nil 0 nil))
    (b2-record-extensionality-updated-lookup lib key-value a b premise)))

(defun b2-record-extensionality-equal-from-lookups (lib goal use-constraint premise)
  (proof-with-checked-results
      ((encoded (b2-record-update-encoding-lemmas lib))
       (encoding-result (car encoded))
       (lib (cdr encoded))
       (lib (b2-record-extensionality-difference-lemma lib nil))
       (parts (proof-list-of-length goal 3)))
    (let* ((proof (library-library-proof lib))
           (a (cadr parts))
           (b (caddr parts))
           (left (list *b2-record-update-encode* a))
           (right (list *b2-record-update-encode* b))
           (type-name (proof-sym "B2-ENCODE-RECORD" "ACL2"))
           (decode-name (proof-sym "B2-DECODE-ENCODE" "ACL2"))
           (bind-a (list (list *library-x* a)))
           (bind-b (list (list *library-x* b))))
      (proof-with-checked-results
          ((typed-left (proof-proof-fact proof type-name bind-a))
           (typed-right (proof-proof-fact proof type-name bind-b))
           (decoded-left (proof-proof-fact proof decode-name bind-a))
           (decoded-right (proof-proof-fact proof decode-name bind-b))
           (equality (proof-eq left right))
           (same (proof-proof-reflexive proof (list *b2-record-update-decode* left)))
           (assume-same (proof-proof-assume proof equality t))
           (original (proof-proof-rewrite proof same assume-same '(1 2 1)))
           (original (proof-proof-rewrite proof original decoded-left '(1 1)))
           (original (proof-proof-chain proof original (list decoded-right)))
           (not-goal (proof-proof-assume proof goal nil))
           (different (proof-proof-cut proof original not-goal))
           (different (proof-proof-front proof different (proof-neg equality)))
           (distinguishing-key (list *b2-record-extensionality-difference* left right))
           (auxiliary (proof-eq (list *b2-record-update-get-aux* distinguishing-key left)
                                (list *b2-record-update-get-aux* distinguishing-key right)))
           (unequal (b2-tactics-tactics-use-fact
                     lib *b2-record-extensionality-witness* (proof-neg auxiliary)
                     (list typed-left typed-right different) nil nil 0 nil))
           (same (b2-record-extensionality-lookup-equality
                  lib distinguishing-key a b use-constraint premise))
           (left-get (b2-record-extensionality-step-argument same 1))
           (opened (proof-proof-unfold proof left-get))
           (rewritten (proof-proof-rewrite proof same opened '(1 1)))
           (right-get (b2-record-extensionality-step-argument same 2))
           (opened (proof-proof-unfold proof right-get))
           (same (proof-proof-rewrite proof rewritten opened '(1 2)))
           (cut (proof-proof-cut proof same unequal))
           (step (proof-proof-front proof cut goal)))
        (cons step lib)))))

(defun b2-record-extensionality-record-extensionality-consequent (premise lib name goal)
  (b2-record-extensionality-equal-from-lookups
   lib goal (equal name (proof-sym "EQUAL-BY-G" "ACL2")) premise))

(defun b2-record-extensionality-record-extensionality (lib name formula)
  (if (equal name (proof-sym "S-SAME-S" "ACL2"))
      (b2-record-extensionality-equal-from-lookups lib formula nil nil)
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (condition (cadr parts))
         (goal (proof-list-of-length (caddr parts) 3))
         (request (b2-tactics-tactics-implication lib condition goal nil))
         (call (car request))
         (result (b2-record-extensionality-record-extensionality-consequent
                  (cadddr call) (cdr request) name goal))
         (result (b2-tactics-tactics-implication lib condition goal result))
         (step (car result)))
      (cons step (cdr result)))))
