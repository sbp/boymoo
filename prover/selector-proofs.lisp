(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun selector-proofs-count-cons-lemmas (lib)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal (proof-sym "SELF-COUNT-CONS" "ACL2") (proof-proof-facts proof))
        lib
      (let ((parts (library-plus *proof-one*
                                 (library-plus (list *library-count* (list *library-car* *library-x*))
                                               (list *library-count* (list *library-cdr* *library-x*)))))
            (count (list *library-count* *library-x*))
            (cons-test (list *proof-consp* *library-x*)))
        (proof-with-checked-results
         ((expansion (proof-proof-unfold proof count))
          (branch (proof-proof-if-true proof (caddr (proof-step-first expansion))))
          (selected (proof-proof-chain proof expansion (list branch)))
          (lib (library-library-lemma lib "COUNT-CONS-PARTS" (proof-eq count parts) selected
                                      (list (proof-neg cons-test)))))
         (let ((proof (library-library-proof lib))
               (pair (list *proof-cons* *library-x* *library-y*))
               (parts (library-plus *proof-one*
                                    (library-plus (list *library-count* *library-x*)
                                                  (list *library-count* *library-y*)))))
           (proof-with-checked-results
            ((nonempty (proof-proof-fact proof "consp-cons" nil))
             (selected (library-library-cite lib "COUNT-CONS-PARTS" (list pair) (list nonempty)))
             (car-cons (library-library-axiom lib "CAR-CONS" (list *library-x* *library-y*)))
             (selected (proof-proof-rewrite proof selected car-cons '(1 2 2 1 1)))
             (cdr-cons (library-library-axiom lib "CDR-CONS" (list *library-x* *library-y*)))
             (selected (proof-proof-rewrite proof selected cdr-cons '(1 2 2 2 1))))
            (library-library-lemma lib "COUNT-CONS" (proof-eq (list *library-count* pair) parts)
                                   selected nil))))))))

(defun selector-proofs-grouped-count-rest (lib siblings rest expanded)
  (if (endp siblings)
      (list rest expanded)
    (proof-with-checked-results
     ((pair (library-library-cite lib "COUNT-CONS" (list (car siblings) rest) nil))
      (expanded (if expanded
                    (proof-proof-rewrite (library-library-proof lib) pair expanded '(1 2 2 2))
                  pair)))
     (selector-proofs-grouped-count-rest lib (cdr siblings)
                                        (list *proof-cons* (car siblings) rest) expanded))))

(defun selector-proofs-grouped-count (lib actual siblings)
  (if (endp siblings)
      '(:failure "failure" "")
    (let ((reversed (reverse siblings)))
      (proof-with-checked-results
       ((grouped (selector-proofs-grouped-count-rest lib (cdr reversed) (car reversed) nil))
        (count (library-library-cite lib "COUNT-CONS" (list actual (car grouped)) nil))
        (count (if (cadr grouped)
                   (proof-proof-rewrite (library-library-proof lib) count (cadr grouped) '(1 2 2 2))
                 count)))
       (list (car grouped) count)))))

(defun selector-proofs-regrouped-expansions (lib edges evidence before place siblings)
  (declare (xargs :measure (acl2-count edges)))
  (cond
   ((endp edges) (list before (reverse siblings)))
   ((endp evidence) (list before (reverse siblings)))
   (t
    (proof-with-checked-results
     ((edge (proof-list-of-length (car edges) 2))
      (expansion (library-library-cite lib "COUNT-CONS-PARTS" (list (cadr edge)) (list (car evidence))))
      (before (if before
                  (proof-proof-rewrite (library-library-proof lib) before expansion place)
                expansion)))
     (let ((car-edge (equal (car edge) *library-car*)))
       (selector-proofs-regrouped-expansions
        lib (cdr edges) (cdr evidence) before (append place (list 2 (if car-edge 1 2)))
        (cons (list (if car-edge *library-cdr* *library-car*) (cadr edge)) siblings)))))))

(defun selector-proofs-regrouped-descent (lib actual edges evidence)
  (proof-with-checked-results
   ((lib (selector-proofs-count-cons-lemmas lib))
    (expansions (selector-proofs-regrouped-expansions lib edges evidence nil '(1 2) nil))
    (grouped (selector-proofs-grouped-count lib actual (cadr expansions))))
   (let ((proof (library-library-proof lib))
         (before (car expansions))
         (rest (car grouped))
         (after (cadr grouped)))
     (proof-with-checked-results
      ((order (library-library-linear-equal lib (caddr (proof-step-first before))
                                           (caddr (proof-step-first after)) nil))
       (reverse-after (proof-proof-symmetric proof after))
       (same-count (proof-proof-chain proof before (list order reverse-after)))
       (nonempty (proof-proof-fact proof "consp-cons"
                                   (list (list *library-x* actual) (list *library-y* rest))))
       (builtin (library-library-builtin lib 2 (list *proof-cons* actual rest)))
       (strict (proof-proof-discharge proof builtin nonempty))
       (car-cons (library-library-axiom lib "CAR-CONS" (list actual rest)))
       (strict (proof-proof-rewrite proof strict car-cons '(1 1 1)))
       (reverse-count (proof-proof-symmetric proof same-count))
       (strict (proof-proof-rewrite proof strict reverse-count '(1 2)))
       (step (proof-proof-tidy proof strict)))
      (cons step lib)))))

(defun selector-proofs-count-nil-bound (lib)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal (proof-sym "SELF-COUNT-NIL-LESS" "ACL2") (proof-proof-facts proof))
        lib
      (proof-with-checked-results
       ((cons-test (proof-proof-assume proof (list *proof-consp* *library-x*) t))
        (builtin (library-library-builtin lib 2 *library-x*))
        (strict (proof-proof-discharge proof builtin cons-test))
        (left-ord (library-library-builtin lib 1 (list *library-car* *library-x*)))
        (right-ord (library-library-builtin lib 1 *library-x*))
        (ordinal (ordinal-proofs-positive-ordinal lib strict left-ord right-ord)))
       (let* ((lib (cdr ordinal))
              (proof (library-library-proof lib))
              (nil-term (list *library-count* *proof-false*))
              (goal (list *proof-ordinal-less* nil-term (list *library-count* *library-x*))))
         (proof-with-checked-results
          ((nil-count (proof-proof-simplify proof nil-term nil (list *library-count*)))
           (step (library-library-transport-argument lib (car ordinal) nil-count 1)))
          (library-library-lemma lib "COUNT-NIL-LESS" goal step
                                 (list (proof-neg (proof-step-first cons-test))))))))))

(defun selector-proofs-nil-path-reduce (lib edges reduction)
  (if (endp edges)
      reduction
    (let ((proof (library-library-proof lib))
          (selector (caar edges))
          (parent (cadar edges)))
      (proof-with-checked-results
       ((parts (proof-list-of-length (car edges) 2))
        (identity (proof-proof-reflexive proof (list selector parent)))
        (opened (proof-proof-rewrite proof identity reduction '(1 2 1)))
        (computed (proof-proof-compute proof (list selector *proof-false*) (cadr *proof-false*)))
        (reduction (proof-proof-chain proof opened (list computed))))
       (selector-proofs-nil-path-reduce lib (cdr edges) reduction)))))

(defun selector-proofs-nil-path-descent (lib edges root-cons start)
  (let* ((index (if (< start 0) (+ (len edges) start) start))
         (edge (nth index edges))
         (proof (library-library-proof lib)))
    (if (or (< index 0) (<= (len edges) index))
        '(:failure "failure" "")
      (proof-with-checked-results
       ((parts (proof-list-of-length edge 2))
        (completion (library-library-axiom
                     lib (concatenate 'string "COMPLETION-OF-" (caddar edge)) (list (cadr edge))))
        (branch (proof-proof-if-false proof (caddr (proof-step-first completion))))
        (reduction (proof-proof-chain proof completion (list branch)))
        (reduction (selector-proofs-nil-path-reduce lib (seq-slice edges (+ start 1) :none) reduction))
        (lib (selector-proofs-count-nil-bound lib)))
       (let ((proof (library-library-proof lib)))
         (proof-with-checked-results
          ((nil-less (library-library-cite lib "COUNT-NIL-LESS" (list (cadar edges)) (list root-cons)))
           (inverse (proof-proof-symmetric proof reduction))
           (strict (proof-proof-rewrite proof nil-less inverse '(1 1 1)))
           (step (proof-proof-tidy proof strict)))
          (cons step lib)))))))

(defun selector-proofs-selector-path-descent-descend (n evidence lib actual edges initial)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "selector-proofs-selector-path-descent-descend")
    (if (not (member-equal nil evidence))
        (selector-proofs-regrouped-descent lib actual edges evidence)
      (let* ((index (position-equal nil evidence))
             (test (list *proof-consp* (cadr (nth index edges)))))
        (proof-with-checked-results
         ((cons-test (proof-proof-assume (library-library-proof lib) test t))
          (yes (selector-proofs-selector-path-descent-descend
                (1- n) (update-nth index cons-test evidence) lib actual edges initial))
          (no (selector-proofs-nil-path-descent (cdr yes) edges (car initial) index))
          (step (proof-proof-cases (library-library-proof (cdr no)) test (car yes) (car no))))
         (cons step (cdr no)))))))

(defun selector-proofs-initial-evidence (edges rulers)
  (if (endp edges)
      (cons nil rulers)
    (proof-with-checked-results
     ((parts (proof-list-of-length (car edges) 2))
      (found (rulers-rulers-find rulers (list *proof-consp* (cadar edges))))
      (rest (selector-proofs-initial-evidence (cdr edges) (cdr found))))
     (cons (cons (car found) (car rest)) (cdr rest)))))

(defun selector-proofs-selector-path-descent-with-rulers (lib actual edges rulers)
  (if (< (len edges) 2)
      (cons (list nil rulers) lib)
    (proof-with-checked-results
     ((found (selector-proofs-initial-evidence edges rulers)))
     (let ((initial (car found))
           (rulers (cdr found)))
       (if (not (car initial))
           (cons (list nil rulers) lib)
         (proof-with-checked-results
          ((proof (selector-proofs-selector-path-descent-descend 1000000 initial lib actual edges initial)))
          (let ((updated (cdr proof)))
            (cons (list (car proof)
                        (if (equal (rulers-rulers-proof rulers) lib)
                            (rulers-rulers-with-proof rulers updated)
                          rulers))
                  updated))))))))

