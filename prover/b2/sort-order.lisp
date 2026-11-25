(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-sort-order-symbol-list* (proof-sym "SYMBOL-LISTP" "ACL2"))
(defconst *b2-sort-order-symbol-less* (proof-sym "SYMBOL<" "ACL2"))
(defconst *b2-sort-order-sorted* (proof-sym "STRICT-SYMBOL<-SORTEDP" "ACL2"))
(defconst *b2-sort-order-descending* (proof-sym "B2-DESCENDING-SYMBOL-LIST" "ACL2"))

(defun b2-sort-order-lower (element lst)
  (proof-ite (list *proof-consp* lst)
             (list *b2-sort-order-symbol-less* element (list *library-car* lst))
             *proof-true*))

(defun b2-sort-order-follows (prefix suffix)
  (proof-ite (list *proof-consp* prefix)
             (b2-sort-order-lower (list *library-car* prefix) suffix)
             *proof-true*))

(defun b2-sort-order-evidence-at (known term)
  (let ((found (assoc-equal term known)))
    (if found
        (cdr found)
      '(:failure "tactic-rejected" ""))))

(defun b2-sort-order-signs (lib test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((yes (proof-proof-assume proof test t))
      (no (proof-proof-assume proof test nil)))
     (list yes no))))

(defun b2-sort-order-normalization-step (equation)
  (or equation '(:failure "failure" "")))

(defun b2-sort-order-nil-from-symbol-list (lib lst atom typed)
  (declare (ignore lst))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first typed))
      (opened (b2-tactics-tactics-normalize lib literal (list atom) (list literal) nil 1500 nil))
      (opened (b2-sort-order-normalization-step opened))
      (rewritten (proof-proof-rewrite proof typed opened '(1))))
     (proof-proof-tidy proof rewritten))))

(defun b2-sort-order-typed-parts (lib lst cons-step typed)
  (b2-lists-opened-conjuncts lib typed (list cons-step)
                            (list (list *b2-sort-order-symbol-list* lst))))

(defun b2-sort-order-ordered-parts (lib lst cons-step sorted-proof)
  (let* ((proof (library-library-proof lib))
         (head (list *library-car* lst))
         (tail (list *library-cdr* lst))
         (test (list *proof-consp* tail))
         (nil-tail (proof-neg (proof-eq tail *proof-false*)))
         (sorted-tail (list *b2-sort-order-sorted* tail))
         (bound (b2-sort-order-lower head tail)))
    (proof-with-checked-results
     ((signs (b2-sort-order-signs lib test))
      (pos (car signs))
      (atom (cadr signs))
      (nonempty (b2-tactics-tactics-from-impossible lib nil-tail pos nil nil nil 1500 nil))
      (literal (proof-step-first sorted-proof))
      (parts (b2-lists-opened-conjuncts lib sorted-proof (list cons-step nonempty) (list literal)))
      (empty-order (b2-tactics-tactics-solve lib sorted-tail (list atom)
                                            (list sorted-tail) nil 0 nil))
      (yes (b2-tactics-tactics-solve lib bound (list pos (car parts)) nil nil 0 nil))
      (no (b2-tactics-tactics-solve lib bound (list atom) nil nil 0 nil))
      (bound-step (proof-proof-cases proof test yes no))
      (tail-step (proof-proof-cases proof test (cadr parts) empty-order)))
     (list bound-step tail-step))))

(defun b2-sort-order-prepend-ordered (lib pair tail-type tail-order bound)
  (proof-with-checked-results
   ((parts (proof-list-of-length pair 3)))
   (let* ((proof (library-library-proof lib))
          (tail (caddr parts))
          (test (list *proof-consp* tail))
          (goal (list *b2-sort-order-sorted* pair)))
     (proof-with-checked-results
      ((signs (b2-sort-order-signs lib test))
       (order (proof-proof-prove-if proof bound (car signs)))
       (nonempty (b2-tactics-tactics-from-impossible
                  lib (proof-neg (proof-eq tail *proof-false*)) (car signs)
                  nil nil nil 1500 nil))
       (yes (b2-tactics-tactics-solve lib goal (list order nonempty tail-order)
                                     (list goal) nil 0 nil))
       (empty (b2-sort-order-nil-from-symbol-list lib tail (cadr signs) tail-type))
       (no (b2-tactics-tactics-solve lib goal (list (cadr signs) empty) (list goal) nil 0 nil)))
      (proof-proof-cases proof test yes no)))))

(defun b2-sort-order-prepend-descending (lib pair old-descending order)
  (proof-with-checked-results
   ((parts (proof-list-of-length pair 3)))
   (let ((test (list *proof-consp* (caddr parts)))
         (goal (list *b2-sort-order-descending* pair))
         (proof (library-library-proof lib)))
     (proof-with-checked-results
      ((signs (b2-sort-order-signs lib test))
       (head-bound (proof-proof-prove-if proof order (car signs)))
       (yes (b2-tactics-tactics-solve lib goal (list (car signs) old-descending head-bound)
                                     (list goal) nil 0 nil))
       (no (b2-tactics-tactics-solve lib goal (list (cadr signs)) (list goal) nil 0 nil)))
      (proof-proof-cases proof test yes no)))))

(defun b2-sort-order-reverse-order-base (atom lib premise goal reverse)
  (proof-with-checked-results
   ((request (b2-tactics-tactics-implication lib premise goal nil))
    (base-lib (cdr request))
    (given (cadddr (car request)))
    (known (b2-tactics-tactics-evidence base-lib (list given)))
    (ordered (b2-sort-order-evidence-at known (list *b2-sort-order-sorted* *library-y*)))
    (step (b2-tactics-tactics-solve base-lib goal (list atom ordered) (list reverse) nil 0 nil)))
   (b2-tactics-tactics-implication lib premise goal (cons step base-lib))))

(defun b2-sort-order-reverse-order-advance-consequent-branch
    (tail-test lib has-tail empty-tail desc cons-step tail tail-link typed-tail
               typed-pair sorted-pair hypothesis goal reverse)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first desc))
      (opened (b2-tactics-tactics-normalize
               lib literal (list cons-step tail-test) (list literal) nil 1500 nil))
      (opened (b2-sort-order-normalization-step opened))
      (rewritten (proof-proof-rewrite proof desc opened '(1)))
      (inherited (proof-proof-tidy proof rewritten))
      (decrease-and-link
       (if (equal tail-test has-tail)
           (proof-with-checked-results
            ((parts (proof-proof-conjunct proof inherited))
             (link (b2-tactics-tactics-solve lib tail-link (list has-tail (car parts))
                                             nil nil 0 nil)))
            (list (cadr parts) link))
         (proof-with-checked-results
          ((desc-tail (list *b2-sort-order-descending* tail))
           (decreasing (b2-tactics-tactics-solve lib desc-tail (list empty-tail)
                                                (list desc-tail) nil 0 nil))
           (link (b2-tactics-tactics-solve lib tail-link (list empty-tail) nil nil 0 nil)))
          (list decreasing link))))
      (hypothesis-literal (proof-step-first hypothesis))
      (condition (proof-term-at hypothesis-literal 1))
      (next-premise (b2-tactics-tactics-solve
                     lib condition (list typed-tail typed-pair (car decrease-and-link)
                                         sorted-pair (cadr decrease-and-link))
                     nil nil 0 nil))
      (done (proof-proof-modus-ponens proof hypothesis next-premise)))
     (b2-tactics-tactics-solve lib goal (list cons-step done) (list reverse) nil 0 nil))))

(defun b2-sort-order-reverse-order-advance-consequent
    (given lib cons-step hypothesis goal reverse tail pair)
  (let ((proof (library-library-proof lib))
        (pair-symbol-list (list *b2-sort-order-symbol-list* pair))
        (next-test (list *proof-consp* tail)))
    (proof-with-checked-results
     ((known (b2-tactics-tactics-evidence lib (list given)))
      (typed-x (b2-sort-order-evidence-at known (list *b2-sort-order-symbol-list* *library-x*)))
      (typed-parts (b2-sort-order-typed-parts lib *library-x* cons-step typed-x))
      (typed-y (b2-sort-order-evidence-at known (list *b2-sort-order-symbol-list* *library-y*)))
      (typed-pair (b2-tactics-tactics-solve
                   lib pair-symbol-list (list (car typed-parts) typed-y)
                   (list pair-symbol-list) nil 0 nil))
      (follows (b2-sort-order-evidence-at known (b2-sort-order-follows *library-x* *library-y*)))
      (order (proof-proof-prove-if proof follows cons-step))
      (sorted-y (b2-sort-order-evidence-at known (list *b2-sort-order-sorted* *library-y*)))
      (sorted-pair (b2-sort-order-prepend-ordered lib pair typed-y sorted-y order))
      (signs (b2-sort-order-signs lib next-test))
      (has-tail (car signs))
      (empty-tail (cadr signs))
      (desc (b2-sort-order-evidence-at known (list *b2-sort-order-descending* *library-x*)))
      (tail-link (b2-sort-order-follows tail pair))
      (yes (b2-sort-order-reverse-order-advance-consequent-branch
            has-tail lib has-tail empty-tail desc cons-step tail tail-link
            (cadr typed-parts) typed-pair sorted-pair hypothesis goal reverse))
      (no (b2-sort-order-reverse-order-advance-consequent-branch
           empty-tail lib has-tail empty-tail desc cons-step tail tail-link
           (cadr typed-parts) typed-pair sorted-pair hypothesis goal reverse)))
     (proof-proof-cases proof next-test yes no))))

(defun b2-sort-order-reverse-order-advance (cons-step hypothesis lib premise goal reverse tail pair)
  (proof-with-checked-results
   ((request (b2-tactics-tactics-implication lib premise goal nil))
    (step (b2-sort-order-reverse-order-advance-consequent
           (cadddr (car request)) (cdr request) cons-step hypothesis goal reverse tail pair)))
   (b2-tactics-tactics-implication lib premise goal (cons step (cdr request)))))

(defun b2-sort-order-reverse-order-definition (lib tail)
  (proof-with-checked-results
   ((order (list *b2-sort-order-symbol-less* (list *library-car* tail)
                 (list *library-car* *library-x*)))
    (ordered-tail (list *b2-sort-order-descending* tail))
    (both (b2-powers-and-terms (list order ordered-tail)))
    (descending (proof-ite (list *proof-consp* *library-x*)
                           (proof-ite (list *proof-consp* tail) both *proof-true*)
                           *proof-true*))
    (formals (list *library-x*))
    (definitions (list (list *b2-sort-order-descending* formals descending)))
    (source (proof-line "define" (cons *termination-all* definitions)))
    (entry (list "define" *b2-sort-order-descending* nil source))
    (lib (library-library-with-entries lib (append (library-library-entries lib) (list entry))))
    (calls (termination-recursive-calls *termination-all* definitions))
    (measure (b2-measures-prove-measure
              lib definitions calls
              (list (cons *b2-sort-order-descending* (list *library-count* *library-x*)))))
    (lib (cdr measure))
    (lib (library-library-with-entries
          lib (append (library-library-entries lib) (list (car measure)))))
    (proof (proof-proof-add-definition (library-library-proof lib)
                                      *b2-sort-order-descending* formals descending)))
   (library-library-with-proof lib proof)))

(defun b2-sort-order-reverse-order (lib)
  (let* ((tail (list *library-cdr* *library-x*))
         (reverse (list *b2-sorting-revappend* *library-x* *library-y*))
         (goal (list *b2-sort-order-sorted* reverse))
         (element (list *library-car* *library-x*))
         (pair (list *proof-cons* element *library-y*))
         (extra (list (list *library-y* pair))))
    (proof-with-checked-results
     ((lib (b2-sort-order-reverse-order-definition lib tail))
      (premise (b2-powers-and-terms
                (list (list *b2-sort-order-symbol-list* *library-x*)
                      (list *b2-sort-order-symbol-list* *library-y*)
                      (list *b2-sort-order-descending* *library-x*)
                      (list *b2-sort-order-sorted* *library-y*)
                      (b2-sort-order-follows *library-x* *library-y*))))
      (formula (list *library-implies* premise goal))
      (advance-request (b2-tactics-tactics-on-list lib formula *library-x* nil nil extra))
      (advance (b2-sort-order-reverse-order-advance
                (cadddr (car advance-request)) (nth 4 (car advance-request))
                (cdr advance-request) premise goal reverse tail pair))
      (base-request (b2-tactics-tactics-on-list lib formula *library-x* nil advance extra))
      (base (b2-sort-order-reverse-order-base
             (cadddr (car base-request)) (cdr base-request) premise goal reverse))
      (induction (b2-tactics-tactics-on-list lib formula *library-x* base advance extra)))
     (b2-tactics-tactics-add-lemma (cdr induction) "REVERSE-APPEND-ORDER" (car induction) :none))))

(defun b2-sort-order-partition-type-base (atom lib condition goal)
  (proof-with-checked-results
   ((request (b2-tactics-tactics-implication lib condition goal nil))
    (base-lib (cdr request))
    (step (b2-tactics-tactics-solve
           base-lib goal (list atom)
           (list *b2-sorting-evens* *b2-sorting-odds* *b2-sort-order-symbol-list*) nil 0 nil)))
   (b2-tactics-tactics-implication lib condition goal (cons step base-lib))))

(defun b2-sort-order-partition-type-advance-consequent
    (given lib cons-step hypothesis first second goal)
  (let ((proof (library-library-proof lib))
        (first-type (list *b2-sort-order-symbol-list* first)))
    (proof-with-checked-results
     ((parts (b2-sort-order-typed-parts lib *library-x* cons-step given))
      (induction (proof-proof-modus-ponens proof hypothesis (cadr parts)))
      (even-and-odd (proof-proof-conjunct proof induction))
      (odd-tail (proof-proof-unfold proof (list *b2-sorting-odds* (list *library-cdr* *library-x*))))
      (odd (proof-proof-rewrite-first proof (cadr even-and-odd) odd-tail))
      (first-step (b2-tactics-tactics-solve lib first-type (list cons-step (car parts) odd)
                                           (list first first-type) nil 0 nil))
      (opened (proof-proof-unfold proof second))
      (symmetric (proof-proof-symmetric proof opened))
      (second-step (proof-proof-rewrite-first proof (car even-and-odd) symmetric)))
     (b2-tactics-tactics-solve lib goal (list first-step second-step) nil nil 0 nil))))

(defun b2-sort-order-partition-type-advance
    (cons-step hypothesis lib condition goal first second)
  (proof-with-checked-results
   ((request (b2-tactics-tactics-implication lib condition goal nil))
    (step (b2-sort-order-partition-type-advance-consequent
           (cadddr (car request)) (cdr request) cons-step hypothesis first second goal)))
   (b2-tactics-tactics-implication lib condition goal (cons step (cdr request)))))

(defun b2-sort-order-partition-type (lib)
  (let ((first (list *b2-sorting-evens* *library-x*))
        (second (list *b2-sorting-odds* *library-x*))
        (condition (list *b2-sort-order-symbol-list* *library-x*)))
    (proof-with-checked-results
     ((goal (b2-powers-and-terms (list (list *b2-sort-order-symbol-list* first)
                                      (list *b2-sort-order-symbol-list* second))))
      (formula (list *library-implies* condition goal))
      (advance-request (b2-tactics-tactics-on-list lib formula *library-x* nil nil nil))
      (advance (b2-sort-order-partition-type-advance
                (cadddr (car advance-request)) (nth 4 (car advance-request))
                (cdr advance-request) condition goal first second))
      (base-request (b2-tactics-tactics-on-list lib formula *library-x* nil advance nil))
      (base (b2-sort-order-partition-type-base
             (cadddr (car base-request)) (cdr base-request) condition goal))
      (induction (b2-tactics-tactics-on-list lib formula *library-x* base advance nil)))
     (b2-tactics-tactics-add-lemma
      (cdr induction) "EVENS-ODDS-SYMBOL-LISTS" (car induction) :none))))

(defun b2-sort-order-signed-assumptions (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
     ((assumption (proof-proof-assume proof (caar signed) (cadar signed)))
      (rest (b2-sort-order-signed-assumptions proof (cdr signed))))
     (cons assumption rest))))

(defun b2-sort-order-merge-order-consequent-leaf-preceding
    (lib source selected element head order known given)
  (let ((direct (assoc-equal order known)))
    (if direct
        (cdr direct)
      (let* ((proof (library-library-proof lib))
             (source-head (list *library-car* source))
             (source-smaller (list *b2-sort-order-symbol-less* source-head element))
             (different (proof-neg (proof-eq source-head element))))
        (proof-with-checked-results
         ((cons-selected (b2-sort-order-evidence-at known (list *proof-consp* selected)))
          (typed-selected (b2-sort-order-evidence-at
                           given (list *b2-sort-order-symbol-list* selected)))
          (selected-parts (b2-sort-order-typed-parts lib selected cons-selected typed-selected))
          (inverse (proof-sym "SYMBOL<-TRICHOTOMY" "ACL2"))
          (antecedent (proof-proof-fact
                       proof inverse (list (list *library-x* source-head)
                                           (list *library-y* element))))
          (literal (proof-step-first antecedent))
          (condition (proof-term-at literal 1))
          (not-smaller (b2-sort-order-evidence-at known (proof-neg source-smaller)))
          (valid (b2-tactics-tactics-solve
                  lib condition (list head (car selected-parts) not-smaller) nil nil 0 nil))
          (disjunction (proof-proof-modus-ponens proof antecedent valid))
          (distinct (b2-sort-order-evidence-at known different)))
         (b2-tactics-tactics-from-impossible lib order disjunction (list distinct)
                                             nil nil 1500 nil))))))

(defun b2-sort-order-merge-order-consequent-leaf-source
    (lib source next-source selected element cons-step typed typed-parts given known)
  (if (equal source next-source)
      (let ((order (list *b2-sort-order-symbol-less* element (list *library-car* source))))
        (proof-with-checked-results
         ((preceding (b2-sort-order-merge-order-consequent-leaf-preceding
                      lib source selected element (car typed-parts) order known given))
          (lower-bound (b2-tactics-tactics-solve
                        lib (b2-sort-order-lower element source)
                        (list cons-step preceding) nil nil 0 nil))
          (sorted (b2-sort-order-evidence-at given (list *b2-sort-order-sorted* source))))
         (list typed sorted lower-bound)))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
       ((sorted (b2-sort-order-evidence-at given (list *b2-sort-order-sorted* source)))
        (ordered (b2-sort-order-ordered-parts lib source cons-step sorted))
        (bound (if (equal source selected)
                   (car ordered)
                 (proof-with-checked-results
                  ((same (b2-sort-order-evidence-at
                          known (proof-eq (list *library-car* *library-x*)
                                          (list *library-car* *library-y*))))
                   (symmetric (proof-proof-symmetric proof same)))
                  (proof-proof-rewrite-first proof (car ordered) symmetric)))))
       (list (cadr typed-parts) (cadr ordered) bound)))))

(defun b2-sort-order-merge-order-consequent-leaf-row
    (source next-source lib selected element pair given known typed-pair)
  (let ((pair-type (list *b2-sort-order-symbol-list* pair)))
    (proof-with-checked-results
     ((cons-step (b2-sort-order-evidence-at known (list *proof-consp* source)))
      (typed (b2-sort-order-evidence-at given (list *b2-sort-order-symbol-list* source)))
      (parts (b2-sort-order-typed-parts lib source cons-step typed))
      (typed-pair (if (equal source selected)
                      (proof-with-checked-results
                       ((typed-z (b2-sort-order-evidence-at
                                  given (list *b2-sort-order-symbol-list* *library-z*))))
                       (b2-tactics-tactics-solve lib pair-type (list (car parts) typed-z)
                                                (list pair-type) nil 0 nil))
                    typed-pair))
      (updated (b2-sort-order-merge-order-consequent-leaf-source
                lib source next-source selected element cons-step typed parts given known)))
     (cons typed-pair updated))))

(defun b2-sort-order-merge-order-consequent-leaf-sources
    (sources next-sources lib selected element pair given known result)
  (declare (xargs :measure (acl2-count sources)))
  (cond
   ((failure-p result) result)
   ((or (endp sources) (endp next-sources)) result)
   (t (b2-sort-order-merge-order-consequent-leaf-sources
       (cdr sources) (cdr next-sources) lib selected element pair given known
       (proof-with-checked-results
        ((row (b2-sort-order-merge-order-consequent-leaf-row
               (car sources) (car next-sources) lib selected element pair given known (car result))))
        (cons (car row) (append (cdr result) (cdr row))))))))

(defun b2-sort-order-merge-order-consequent-leaf-links
    (next-sources updated pair pair-cons car-pair proof links)
  (declare (xargs :measure (acl2-count next-sources)))
  (cond
   ((failure-p links) links)
   ((or (endp next-sources) (endp (cddr updated))) (reverse links))
   (t (b2-sort-order-merge-order-consequent-leaf-links
       (cdr next-sources) (cdddr updated) pair pair-cons car-pair proof
       (proof-with-checked-results
        ((equation (proof-proof-select proof (b2-sort-order-follows pair (car next-sources)) pair-cons))
         (equation (proof-proof-rewrite proof equation car-pair '(1 2 2 1)))
         (equation (proof-proof-tidy proof equation))
         (linked (proof-proof-transport proof (caddr updated) equation)))
        (cons linked links))))))

(defun b2-sort-order-merge-order-consequent-leaf-bindings (formals args)
  (if (or (endp formals) (endp args))
      nil
    (if (equal (car formals) (car args))
        (b2-sort-order-merge-order-consequent-leaf-bindings (cdr formals) (cdr args))
      (cons (list (car formals) (car args))
            (b2-sort-order-merge-order-consequent-leaf-bindings (cdr formals) (cdr args))))))

(defun b2-sort-order-merge-order-consequent-leaf-reverse (lib branch given desc rev)
  (proof-with-checked-results
   ((rest (proof-term-at branch 2))
    (type-z (b2-sort-order-evidence-at given (list *b2-sort-order-symbol-list* *library-z*)))
    (type-rest (b2-sort-order-evidence-at given (list *b2-sort-order-symbol-list* rest)))
    (descending (b2-sort-order-evidence-at given desc))
    (sorted-rest (b2-sort-order-evidence-at given (list *b2-sort-order-sorted* rest)))
    (link (b2-sort-order-evidence-at given (b2-sort-order-follows *library-z* rest)))
    (step (b2-tactics-tactics-use-fact
           lib rev (list *b2-sort-order-sorted* branch)
           (list type-z type-rest descending sorted-rest link) nil nil 0 nil)))
   (cons step nil)))

(defun b2-sort-order-merge-order-consequent-leaf-step
    (lib branch known given desc call formula measure)
  (let* ((proof (library-library-proof lib))
         (args (cdr branch))
         (sources (list *library-x* *library-y*))
         (next-sources (take 2 args))
         (acc-test (list *proof-consp* *library-z*)))
    (proof-with-checked-results
     ((pair (proof-term-at args 2))
      (element (proof-term-at pair 1))
      (selected (if (equal element (list *library-car* *library-x*)) *library-x* *library-y*))
      (typed-and-updated (b2-sort-order-merge-order-consequent-leaf-sources
                          sources next-sources lib selected element pair given known (list nil)))
      (updated (cdr typed-and-updated))
      (signs (b2-sort-order-signs lib acc-test))
      (acc-cons (car signs))
      (acc-atom (cadr signs))
      (link (b2-sort-order-evidence-at given (b2-sort-order-follows *library-z* selected)))
      (link (proof-proof-prove-if proof link acc-cons))
      (selected-cons (b2-sort-order-evidence-at known (list *proof-consp* selected)))
      (old-order (proof-proof-prove-if proof link selected-cons))
      (bound (proof-ite acc-test
                        (list *b2-sort-order-symbol-less* (list *library-car* *library-z*) element)
                        *proof-true*))
      (yes (b2-tactics-tactics-solve lib bound (list acc-cons old-order) nil nil 0 nil))
      (no (b2-tactics-tactics-solve lib bound (list acc-atom) nil nil 0 nil))
      (bound-step (proof-proof-cases proof acc-test yes no))
      (descending (b2-sort-order-evidence-at given desc))
      (desc-pair (b2-sort-order-prepend-descending lib pair descending bound-step))
      (all-steps (cons (car typed-and-updated) (cons desc-pair updated)))
      (pair-cons (proof-proof-fact proof "consp-cons" (seq-zip sources (cdr pair))))
      (car-pair (library-library-axiom lib "CAR-CONS" (cdr pair)))
      (links (b2-sort-order-merge-order-consequent-leaf-links
              next-sources updated pair pair-cons car-pair proof nil))
      (binding (b2-sort-order-merge-order-consequent-leaf-bindings (cdr call) args))
      (decrease (b2-sorting-merge-descent lib args measure known))
      (hypothesis (b2-tactics-tactics-induction-hypothesis lib formula measure binding decrease))
      (literal (proof-step-first hypothesis))
      (condition (proof-term-at literal 1))
      (ready (b2-tactics-tactics-solve lib condition (append all-steps links) nil nil 0 nil))
      (step (proof-proof-modus-ponens proof hypothesis ready)))
     (cons step (list binding)))))

(defun b2-sort-order-merge-order-consequent-leaf
    (branch signed lib given rev desc call formula measure)
  (proof-with-checked-results
   ((signs (b2-sort-order-signed-assumptions (library-library-proof lib) signed))
    (known (b2-tactics-tactics-evidence lib signs)))
   (if (proof-is-call branch *b2-sorting-revappend*)
       (b2-sort-order-merge-order-consequent-leaf-reverse lib branch given desc rev)
     (b2-sort-order-merge-order-consequent-leaf-step lib branch known given desc call
                                                   formula measure))))

(defun b2-sort-order-merge-order-consequent-by-value
    (n lib value template signed given rev desc call formula measure)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "b2-sort-order-merge-order-consequent-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
       ((branches (proof-list-of-length (cdr value) 3))
        (test (car branches))
        (yes (b2-sort-order-merge-order-consequent-by-value
              (1- n) lib (cadr branches) template (append signed (list (list test t)))
              given rev desc call formula measure))
        (no (b2-sort-order-merge-order-consequent-by-value
             (1- n) lib (caddr branches) template (append signed (list (list test nil)))
             given rev desc call formula measure))
        (step (proof-by-value-join proof value template (car yes) (car no))))
       (cons step (append (cdr yes) (cdr no)))))
     ((and (proof-compound value) (endp value))
      '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
       ((equality (proof-proof-beta proof value))
        (opened (proof-rewritten-term equality))
        (result (b2-sort-order-merge-order-consequent-by-value
                 (1- n) lib opened template signed given rev desc call formula measure))
        (symmetric (proof-proof-symmetric proof equality))
        (step (proof-proof-rewrite-result proof (car result) symmetric template *proof-result*)))
       (cons step (cdr result))))
     (t (proof-with-checked-results
         ((result (b2-sort-order-merge-order-consequent-leaf
                   value signed lib given rev desc call formula measure))
          (literal (proof-step-first (car result)))
          (target (proof-subst template (list (cons *proof-result* value)))))
         (if (equal literal target)
             result
           '(:failure "tactic-rejected" "")))))))

(defun b2-sort-order-merge-order-consequent
    (premise lib opened template rev desc call formula measure)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((given (b2-tactics-tactics-evidence lib (list premise)))
      (value (proof-rewritten-term opened))
      (result (b2-sort-order-merge-order-consequent-by-value
               1000000 lib value template nil given rev desc call formula measure))
      (symmetric (proof-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof (car result) symmetric template *proof-result*)))
     (cons step (cdr result)))))

(defun b2-sort-order-merge-order (lib)
  (proof-with-checked-results
   ((reverse-order (b2-sort-order-reverse-order lib))
    (lib (cdr reverse-order))
    (rev (car reverse-order))
    (x *library-x*) (y *library-y*) (z *library-z*)
    (call (list *b2-sorting-merge* x y z))
    (desc (list *b2-sort-order-descending* z))
    (conditions (b2-powers-and-terms
                 (list (list *b2-sort-order-symbol-list* x)
                       (list *b2-sort-order-symbol-list* y)
                       (list *b2-sort-order-symbol-list* z)
                       (list *b2-sort-order-sorted* x)
                       (list *b2-sort-order-sorted* y)
                       desc (b2-sort-order-follows z x) (b2-sort-order-follows z y))))
    (goal (list *b2-sort-order-sorted* call))
    (formula (list *library-implies* conditions goal))
    (measure (library-plus (b2-sorting-length x) (b2-sorting-length y)))
    (opened (proof-proof-unfold (library-library-proof lib) call))
    (template (list *b2-sort-order-sorted* *proof-result*))
    (request (b2-tactics-tactics-implication lib conditions goal nil))
    (case-lib (cdr request))
    (consequent (b2-sort-order-merge-order-consequent
                 (cadddr (car request)) case-lib opened template rev desc call formula measure))
    (case (b2-tactics-tactics-implication lib conditions goal (cons (car consequent) case-lib)))
    (lib (cdr case))
    (natural (library-library-natural lib measure))
    (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))
    (induction (proof-proof-induct (library-library-proof lib)
                                   ordinal (car case) formula measure (cdr consequent))))
   (b2-tactics-tactics-add-lemma lib "MERGE-ORDER" induction :none)))

(defun b2-sort-order-sort-order-hypotheses (lib formula measure substitutions decreases hypotheses)
  (declare (xargs :measure (acl2-count substitutions)))
  (cond
   ((failure-p hypotheses) hypotheses)
   ((or (endp substitutions) (endp decreases)) (reverse hypotheses))
   (t (b2-sort-order-sort-order-hypotheses
       lib formula measure (cdr substitutions) (cdr decreases)
       (proof-with-checked-results
        ((hypothesis (b2-tactics-tactics-induction-hypothesis
                      lib formula measure (car substitutions) (car decreases))))
        (cons hypothesis hypotheses))))))

(defun b2-sort-order-sort-order-ordered-pieces (proof hypotheses pieces ordered)
  (declare (xargs :measure (acl2-count hypotheses)))
  (cond
   ((failure-p ordered) ordered)
   ((or (endp hypotheses) (endp pieces)) (reverse ordered))
   (t (b2-sort-order-sort-order-ordered-pieces
       proof (cdr hypotheses) (cdr pieces)
       (proof-with-checked-results
        ((step (proof-proof-modus-ponens proof (car hypotheses) (car pieces))))
        (cons step ordered))))))

(defun b2-sort-order-sort-order-sorted-pieces (ordered pieces)
  (declare (xargs :measure (acl2-count ordered)))
  (cond
   ((failure-p pieces) pieces)
   ((endp ordered) (reverse pieces))
   (t (b2-sort-order-sort-order-sorted-pieces
       (cdr ordered)
       (proof-with-checked-results
        ((literal (proof-step-first (car ordered)))
         (piece (proof-term-at literal 1)))
        (cons piece pieces))))))

(defun b2-sort-order-sort-order-types (lib sorted-pieces pieces types)
  (declare (xargs :measure (acl2-count sorted-pieces)))
  (cond
   ((failure-p types) types)
   ((or (endp sorted-pieces) (endp pieces)) (reverse types))
   (t (b2-sort-order-sort-order-types
       lib (cdr sorted-pieces) (cdr pieces)
       (proof-with-checked-results
        ((step (b2-tactics-tactics-use-fact
                lib (proof-sym "SYMBOL-LISTP-STRICT-MERGE-SORT-SYMBOL<" "ACL2")
                (list *b2-sort-order-symbol-list* (car sorted-pieces))
                (list (car pieces)) nil nil 0 nil)))
        (cons step types))))))

(defun b2-sort-order-sort-order-consequent
    (premise lib call no yes test hypothesis partition helper)
  (let* ((proof (library-library-proof lib))
         (outer-test (list *proof-consp* *library-x*))
         (sorted (list *b2-sort-order-sorted* *library-x*))
         (tail (list *library-cdr* *library-x*)))
    (proof-with-checked-results
     ((empty (b2-tactics-tactics-normalize lib call (list no) (list call) nil 1500 nil))
      (outer-signs (b2-sort-order-signs lib outer-test))
      (outer-cons (car outer-signs))
      (outer-atom (cadr outer-signs))
      (parts (b2-sort-order-typed-parts lib *library-x* outer-cons premise))
      (tail-nil (b2-sort-order-nil-from-symbol-list lib tail no (cadr parts)))
      (typed (b2-tactics-tactics-solve lib sorted (list outer-cons tail-nil) (list sorted) nil 0 nil))
      (atom (b2-tactics-tactics-solve lib sorted (list outer-atom) (list sorted) nil 0 nil))
      (base (proof-proof-cases proof outer-test typed atom))
      (empty (b2-sort-order-normalization-step empty))
      (base (library-library-transport-argument lib base empty 1))
      (partition-fact (proof-proof-fact proof partition nil))
      (partitioned (proof-proof-modus-ponens proof partition-fact premise))
      (pieces (proof-proof-conjunct proof partitioned))
      (ordered (b2-sort-order-sort-order-ordered-pieces proof hypothesis pieces nil))
      (sorted-pieces (b2-sort-order-sort-order-sorted-pieces ordered nil))
      (types (b2-sort-order-sort-order-types lib sorted-pieces pieces nil))
      (unfolded (b2-tactics-tactics-normalize lib call (list yes) (list call) nil 1500 nil))
      (sorted-left (proof-term-at sorted-pieces 0))
      (sorted-right (proof-term-at sorted-pieces 1))
      (theorem (proof-proof-fact proof helper (list (list *library-x* sorted-left)
                                                    (list *library-y* sorted-right)
                                                    (list *library-z* *proof-false*))))
      (literal (proof-step-first theorem))
      (condition (proof-term-at literal 1))
      (ready (b2-tactics-tactics-solve lib condition (append types ordered)
                                      (list *b2-sort-order-symbol-list*
                                            *b2-sort-order-descending*) nil 0 nil))
      (follows (proof-proof-modus-ponens proof theorem ready))
      (unfolded (b2-sort-order-normalization-step unfolded))
      (step (library-library-transport-argument lib follows unfolded 1)))
     (proof-proof-cases proof test step base))))

(defun b2-sort-order-sort-order (lib formula)
  (proof-with-checked-results
   ((merge-order (b2-sort-order-merge-order lib))
    (helper (car merge-order))
    (partition-type (b2-sort-order-partition-type (cdr merge-order)))
    (lib (cdr partition-type))
    (partition (car partition-type))
    (formula-parts (proof-list-of-length formula 3))
    (condition (cadr formula-parts))
    (goal (caddr formula-parts))
    (call (proof-term-at goal 1))
    (x *library-x*)
    (test (list *proof-consp* (list *library-cdr* x)))
    (signs (b2-sort-order-signs lib test))
    (yes (car signs))
    (no (cadr signs))
    (left (list *b2-sorting-evens* x))
    (right (list *b2-sorting-odds* x))
    (substitutions (list (list (list x left)) (list (list x right))))
    (measure (b2-sorting-length x))
    (size (b2-sorting-partition-length lib))
    (lib (cdr size))
    (decreases (b2-sorting-nontrivial-partition lib (car size) yes))
    (hypotheses (b2-sort-order-sort-order-hypotheses lib formula measure substitutions decreases nil))
    (request (b2-tactics-tactics-implication lib condition goal nil))
    (case-lib (cdr request))
    (step (b2-sort-order-sort-order-consequent
           (cadddr (car request)) case-lib call no yes test hypotheses partition helper))
    (case (b2-tactics-tactics-implication lib condition goal (cons step case-lib)))
    (lib (cdr case))
    (natural (library-library-natural lib measure))
    (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))
    (induction (proof-proof-induct (library-library-proof lib)
                                   ordinal (car case) formula measure substitutions)))
   (cons induction lib)))
