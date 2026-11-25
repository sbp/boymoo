(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t3-book-occurrences-natural-count-leaf (n value tests lib recursive premise)
  (declare (ignore tests) (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t3-book-occurrences-natural-count-leaf"))
   ((equal value recursive) premise)
   ((proof-is-call value *proof-plus*)
    (let ((args (cdr value)))
      (if (endp args)
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((first (t3-book-occurrences-natural-count-leaf (1- n) (car args) nil
                                                            lib recursive premise)))
          (if (endp (cdr args))
              '(:failure "unproved" "")
            (proof-with-checked-results
                ((second (t3-book-occurrences-natural-count-leaf (1- n) (cadr args) nil
                                                                 lib recursive premise)))
              (if (endp (cddr args))
                  (library-library-cite lib "NATURAL-SUM" args (list first second))
                (proof-with-checked-results
                    ((extra (t3-book-occurrences-natural-count-leaf (1- n) (caddr args) nil
                                                                    lib recursive premise)))
                  '(:failure "unproved" "")))))))))
   (t (t3-book-values-book-proofs-natural
       (t3-book-values-make-book-proofs lib nil nil) value))))

(defun t3-book-occurrences-natural-count-leaves (requests lib recursive premise)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (answer (t3-book-occurrences-natural-count-leaf
                    1000000 (car request) (cadr request) lib recursive premise))
           (entry (cons request answer)))
      (if (failure-p answer)
          (list entry)
        (cons entry (t3-book-occurrences-natural-count-leaves
                     (cdr requests) lib recursive premise))))))

(defun t3-book-occurrences-natural-count-case (holds lib call test recursive premise)
  (let ((proof (library-library-proof lib))
        (template (list *library-natp* *proof-result*)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test holds))
         (opened (t3-book-spines-shallow lib call (list assumed)))
         (body (proof-rewritten-term opened))
         (requests (t3-logic-libraryproofs-by-value-leaves lib body nil))
         (answers (t3-book-occurrences-natural-count-leaves requests lib recursive premise))
         (natural (t3-logic-libraryproofs-by-value lib body template answers nil)))
      (library-library-transport-argument lib natural opened 1))))

(defun t3-book-occurrences-natural-count (lib call variable)
  (let* ((proof (library-library-proof lib))
         (test (list *proof-consp* variable))
         (tail (list *library-cdr* variable))
         (measure (list *library-count* variable))
         (pairs (list (list variable tail)))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure))
         (goal (list *library-natp* call)))
    (proof-with-checked-results
        ((recursive (proof-subst call (list (cons variable tail))))
         (assumed (proof-proof-assume proof
                                     (proof-ite smaller (list *library-natp* recursive)
                                                *proof-true*) t))
         (decrease (library-library-builtin lib 3 variable))
         (premise (proof-proof-prove-if proof assumed decrease))
         (ordinal (library-library-builtin lib 1 variable))
         (yes (t3-book-occurrences-natural-count-case t lib call test recursive premise))
         (no (t3-book-occurrences-natural-count-case nil lib call test recursive premise))
         (case-proof (proof-proof-cases proof test yes no)))
      (proof-proof-induct proof ordinal case-proof goal measure (list pairs)))))

(defun t3-book-occurrences-count-same-key-reduced (tests lib removed lhs occurs rhs current)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((drop (t3-book-spines-shallow lib removed tests))
         (reflexive (proof-proof-reflexive proof lhs))
         (left (proof-proof-rewrite proof reflexive drop '(1 2 2)))
         (value (proof-rewritten-term drop))
         (left (if (or (equal value *proof-false*) (proof-is-call value *proof-cons*))
                   (proof-with-checked-results
                       ((call (proof-rewritten-term left))
                        (opened (t3-book-spines-shallow lib call tests)))
                     (proof-proof-chain proof left (list opened)))
                 left))
         (members (t3-book-spines-shallow lib occurs tests))
         (reflexive (proof-proof-reflexive proof rhs))
         (right (proof-proof-rewrite proof reflexive members '(1 2 1)))
         (changed (t3-book-spines-shallow lib current tests))
         (value (proof-rewritten-term right))
         (right (proof-proof-rewrite-result proof right changed
                                             (proof-eq *proof-false* value) current))
         (value (proof-rewritten-term right))
         (normalized (t3-book-spines-constructor-form lib value tests *t3-book-spines-guards*))
         (right (proof-proof-chain proof right (list normalized))))
      (list left right))))

(defun t3-book-occurrences-count-same-key-conclude
    (lib formula measure pairs variable current recursive induction test first
     lhs rhs removed occurs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons-proof (proof-proof-assume proof test t))
         (atom-proof (proof-proof-assume proof test nil))
         (equations (t3-book-occurrences-count-same-key-reduced
                     (list atom-proof) lib removed lhs occurs rhs current))
         (left-result (proof-rewritten-term (car equations)))
         (right-result (proof-rewritten-term (cadr equations))))
      (and (equal left-result right-result)
        (proof-with-checked-results
            ((reverse-right (proof-proof-symmetric proof (cadr equations)))
             (base (proof-proof-chain proof (car equations) (list reverse-right)))
             (different (proof-proof-assume proof first nil))
             (equations (t3-book-occurrences-count-same-key-reduced
                         (list cons-proof different) lib removed lhs occurs rhs current))
             (left-result (proof-rewritten-term (car equations)))
             (right-result (proof-rewritten-term (cadr equations)))
             (hypothesis (proof-step-first induction)))
          (and (equal (proof-eq left-result right-result) hypothesis)
            (proof-with-checked-results
                ((reverse-right (proof-proof-symmetric proof (cadr equations)))
                 (missed (proof-proof-chain proof (car equations) (list induction reverse-right)))
                 (same (proof-proof-assume proof first t))
                 (equations (t3-book-occurrences-count-same-key-reduced
                             (list cons-proof same) lib removed lhs occurs rhs current))
                 (left-result (proof-rewritten-term (car equations))))
              (and (equal left-result recursive)
                (proof-with-checked-results
                    ((natural (t3-book-occurrences-natural-count lib current variable))
                     (typed (proof-proof-instantiate proof natural pairs))
                     (integral (library-library-cite lib "NATURAL-INTEGER" (list recursive)
                                                     (list typed)))
                     (right-result (proof-rewritten-term (cadr equations)))
                     (cancellation (library-library-linear-equal lib right-result recursive
                                                                  (list integral)))
                     (right (proof-proof-chain proof (cadr equations) (list cancellation)))
                     (reversed (proof-proof-symmetric proof right))
                     (hit (proof-proof-chain proof (car equations) (list reversed)))
                     (matched (proof-proof-cases proof first hit missed))
                     (case-proof (proof-proof-cases proof test matched base))
                     (ordinal (library-library-builtin lib 1 variable)))
                  (proof-proof-induct proof ordinal case-proof formula measure (list pairs)))))))))))

(defun t3-book-occurrences-count-same-key (lib formula count remove member key variable)
  (let* ((proof (library-library-proof lib))
         (test (list *proof-consp* variable))
         (tail (list *library-cdr* variable))
         (measure (list *library-count* variable))
         (pairs (list (list variable tail)))
         (current (list count key variable))
         (removed (list remove key variable))
         (occurs (list member key variable))
         (first (proof-eq key (list *library-car* variable)))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
    (proof-with-checked-results
        ((sides (proof-list-of-length (cdr formula) 2))
         (substituted (proof-subst formula (list (cons variable tail))))
         (assumed (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
         (decrease (library-library-builtin lib 3 variable))
         (induction (proof-proof-prove-if proof assumed decrease)))
      (t3-book-occurrences-count-same-key-conclude
       lib formula measure pairs variable current (list count key tail) induction test first
       (car sides) (cadr sides) removed occurs))))

(defun t3-book-occurrences-solve-request-p (result)
  (and (consp result) (eq (car result) :t3-book-occurrences-solve)))

(defun t3-book-occurrences-solve-request-goal (result)
  (cadr result))

(defun t3-book-occurrences-calls-map (lib original removed membership variable)
  (proof-with-checked-results ((count-variable (t3-book-spines-map-parameter lib original)))
    (and (equal count-variable variable)
         (proof-with-checked-results ((remove-variable (t3-book-spines-map-parameter lib removed)))
           (and (equal remove-variable variable)
                (proof-with-checked-results
                    ((member-variable (t3-book-spines-map-parameter lib membership)))
                  (equal member-variable variable)))))))

(defun t3-book-occurrences-after-removal-finish
    (lib formula lhs rhs original count remove key other variable same membership solve)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((absent (proof-proof-assume proof same nil)))
      (let* ((difference (list *library-implies* (proof-neg same) (proof-eq lhs original)))
             (reply (assoc-equal difference solve)))
        (if (not reply)
            (list :t3-book-occurrences-solve difference)
          (proof-with-checked-results
              ((applies (or (cdr reply) (t3-book-spines-different-key lib difference))))
            (and applies
              (proof-with-checked-results
                  ((right (t3-book-spines-constructor-form lib rhs (list absent)
                                                            *t3-book-spines-guards*))
                   (applied (proof-proof-modus-ponens proof applies absent))
                   (reversed (proof-proof-symmetric proof right))
                   (distinct (proof-proof-chain proof applied (list reversed)))
                   (assumed (proof-proof-assume proof same t))
                   (same-key (proof-proof-symmetric proof assumed))
                   (reflexive (proof-proof-reflexive proof formula))
                   (opened (proof-proof-rewrite-result proof reflexive same-key
                                                       (proof-eq *proof-false* formula) other))
                   (value (proof-rewritten-term opened))
                   (normalized (t3-book-spines-constructor-form lib value nil
                                                                 *t3-book-spines-guards*))
                   (reduced (proof-proof-chain proof opened (list normalized)))
                   (value (proof-rewritten-term reduced))
                   (equality (t3-book-occurrences-count-same-key
                              lib value count remove (car membership) key variable)))
                (and equality
                  (proof-with-checked-results ((equal-case (proof-proof-transport proof equality reduced)))
                    (proof-proof-cases proof same equal-case distinct)))))))))))

(defun t3-book-occurrences-after-removal (lib formula solve)
  (and (proof-is-call formula *proof-equal*)
    (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((lhs (car sides))
            (rhs (cadr sides)))
        (and (and (proof-compound lhs) (equal (len lhs) 3) (proof-is-call rhs *proof-if*))
          (let ((count (car lhs))
                (key (cadr lhs))
                (removed (caddr lhs)))
            (and (and (proof-compound removed) (equal (len removed) 3))
              (proof-with-checked-results ((branches (proof-list-of-length (cdr rhs) 3)))
                (let* ((remove (car removed))
                       (other (cadr removed))
                       (variable (caddr removed))
                       (test (car branches))
                       (bumped (cadr branches))
                       (original (caddr branches))
                       (same (proof-eq key other)))
                  (and (and (not (proof-compound key))
                             (not (proof-compound other))
                             (not (proof-compound variable))
                             (not (equal key other))
                             (not (equal key variable))
                             (not (equal other variable))
                             (equal original (list count key variable))
                             (equal bumped (library-plus *proof-neg-one* original))
                             (proof-is-call test *proof-if*))
                    (proof-with-checked-results ((condition (proof-term-at test 1)))
                      (and (equal condition same)
                        (proof-with-checked-results ((otherwise (proof-term-at test 3)))
                          (and (equal otherwise *proof-false*)
                            (let ((membership (caddr test)))
                              (and (and (proof-compound membership)
                                         (equal (cdr membership) (list key variable)))
                                (proof-with-checked-results
                                    ((mapped (t3-book-occurrences-calls-map
                                              lib original removed membership variable)))
                                  (and mapped
                                    (t3-book-occurrences-after-removal-finish
                                     lib formula lhs rhs original count remove key other variable
                                     same membership solve)))))))))))))))))))
