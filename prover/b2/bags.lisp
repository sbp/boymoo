(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-bags-a* (proof-sym "A" "ACL2"))
(defconst *b2-bags-u* (proof-sym "U" "ACL2"))
(defconst *b2-bags-v* (proof-sym "V" "ACL2"))
(defconst *b2-bags-binop* (proof-sym "BINOP" "ACL2"))
(defconst *b2-bags-arg* (proof-sym "ARG" "ACL2"))
(defconst *b2-bags-term* (proof-sym "TERM" "ACL2"))
(defconst *b2-bags-del* (proof-sym "DEL" "ACL2"))
(defconst *b2-bags-memb* (proof-sym "MEMB" "ACL2"))
(defconst *b2-bags-subbag* (proof-sym "SUBBAGP" "ACL2"))
(defconst *b2-bags-intersect* (proof-sym "BAGINT" "ACL2"))
(defconst *b2-bags-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *b2-bags-fringe* (proof-sym "BINARY-OP_FRINGE" "ACL2"))
(defconst *b2-bags-occur* (proof-sym "FRINGE-OCCUR" "ACL2"))
(defconst *b2-bags-member-delete* (proof-sym "MEMBER-DELETE" "ACL2"))
(defconst *b2-bags-delete-commutes* (proof-sym "DELETE-COMMUTATIVITY" "ACL2"))
(defconst *b2-bags-subbag-delete* (proof-sym "SUBBAGP-DELETE" "ACL2"))
(defconst *b2-bags-subbag-cdr1* (proof-sym "SUBBAGP-CDR1" "ACL2"))
(defconst *b2-bags-subbag-cdr2* (proof-sym "SUBBAGP-CDR2" "ACL2"))
(defconst *b2-bags-intersect1* (proof-sym "SUBBAGP-BAGINT1" "ACL2"))
(defconst *b2-bags-intersect2* (proof-sym "SUBBAGP-BAGINT2" "ACL2"))
(defconst *b2-bags-member-append* (proof-sym "MEMB-APPEND" "ACL2"))
(defconst *b2-bags-fringe-member* (proof-sym "FRINGE-OCCUR-SAME-AS-OCCUR-IN-FRINGE" "ACL2"))
(defconst *b2-bags-nonempty-intersection* (proof-sym "B2-NONEMPTY-BAGINT" "ACL2"))

(defconst *b2-bags-formulas*
  (let* ((x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (member-x (list *b2-bags-memb* *b2-bags-a* x))
         (intersection (list *b2-bags-intersect* x y))
         (subbag-xy (list *b2-bags-subbag* x y))
         (cdr-x (list *library-cdr* x))
         (cdr-y (list *library-cdr* y)))
    (list
     (cons *b2-bags-member-delete*
           (list *library-implies* (list *b2-bags-memb* x (list *b2-bags-del* *b2-bags-u* *b2-bags-v*))
                 (list *b2-bags-memb* x *b2-bags-v*)))
     (cons *b2-bags-delete-commutes*
           (proof-eq (list *b2-bags-del* x (list *b2-bags-del* y z))
                     (list *b2-bags-del* y (list *b2-bags-del* x z))))
     (cons *b2-bags-subbag-delete*
           (list *library-implies* (list *b2-bags-subbag* x (list *b2-bags-del* *b2-bags-u* y))
                 subbag-xy))
     (cons *b2-bags-subbag-cdr1*
           (list *library-implies*
                 (b2-powers-and-terms (list subbag-xy (list *proof-consp* x)))
                 (list *b2-bags-subbag* cdr-x y)))
     (cons *b2-bags-subbag-cdr2*
           (list *library-implies*
                 (b2-powers-and-terms (list (list *b2-bags-subbag* x cdr-y) (list *proof-consp* y)))
                 subbag-xy))
     (cons *b2-bags-intersect1* (list *b2-bags-subbag* intersection x))
     (cons *b2-bags-intersect2* (list *b2-bags-subbag* intersection y))
     (cons *b2-bags-member-append*
           (proof-eq (list *b2-bags-memb* *b2-bags-a* (list *b2-bags-append* x y))
                     (proof-ite member-x member-x (list *b2-bags-memb* *b2-bags-a* y))))
     (cons *b2-bags-fringe-member*
           (proof-eq (list *b2-bags-occur* *b2-bags-binop* *b2-bags-arg* *b2-bags-term*)
                     (list *b2-bags-memb* *b2-bags-arg*
                           (list *b2-bags-fringe* *b2-bags-binop* *b2-bags-term*)))))))

(defmacro b2-bags-implication (lib condition goal consequent)
  (let ((premise (caar consequent))
        (new-lib (cadar consequent)))
    `(proof-with-checked-results
         ((b2-bags-implication-request
           (b2-tactics-tactics-implication ,lib ,condition ,goal nil))
          (b2-bags-implication-reply
           (let ((,premise (cadddr (car b2-bags-implication-request)))
                 (,new-lib (cdr b2-bags-implication-request)))
             (declare (ignorable ,premise))
             ,(cadr consequent))))
       (b2-tactics-tactics-implication ,lib ,condition ,goal b2-bags-implication-reply))))

(defmacro b2-bags-on-list (lib formula variable extra advance base)
  (let ((cons-step (caar advance))
        (hypothesis (cadar advance))
        (lib-advance (caddar advance))
        (atom-step (caar base))
        (lib-base (cadar base)))
    `(proof-with-checked-results
         ((b2-bags-advance-request
           (b2-tactics-tactics-on-list ,lib ,formula ,variable nil nil ,extra))
          (b2-bags-advance-reply
           (let ((,cons-step (cadddr (car b2-bags-advance-request)))
                 (,hypothesis (car (cddddr (car b2-bags-advance-request))))
                 (,lib-advance (cdr b2-bags-advance-request)))
             ,(cadr advance)))
          (b2-bags-base-request
           (b2-tactics-tactics-on-list ,lib ,formula ,variable nil b2-bags-advance-reply ,extra))
          (b2-bags-base-reply
           (let ((,atom-step (cadddr (car b2-bags-base-request)))
                 (,lib-base (cdr b2-bags-base-request)))
             ,(cadr base))))
       (b2-tactics-tactics-on-list
        ,lib ,formula ,variable b2-bags-base-reply b2-bags-advance-reply ,extra))))

(defun b2-bags-signed (lib test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof test t))
         (no (proof-proof-assume proof test nil)))
      (list yes no))))

(defun b2-bags-reduced-premise (lib premise evidence unfold rules)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first premise))
         (equation (b2-tactics-tactics-normalize lib first evidence unfold rules 1500 nil)))
      (if equation
          (proof-with-checked-results ((step (proof-proof-rewrite proof premise equation '(1))))
            (proof-proof-tidy proof step))
        premise))))

(defun b2-bags-condition-and-goal (formula)
  (if (integerp formula)
      (proof-term-at formula 0)
    (proof-list-of-length (cdr formula) 2)))

(defun b2-bags-equation-first (equation)
  (if equation
      (proof-step-first equation)
    '(:failure "failure" "")))

(defun b2-bags-member-delete-base (atom-step lib condition goal removed)
  (b2-bags-implication
   lib condition goal
   ((premise new-lib)
    (proof-with-checked-results
        ((step (b2-bags-reduced-premise new-lib premise (list atom-step) (list removed) nil)))
      (cons step new-lib)))))

(defun b2-bags-member-delete-advance-branch
    (keeps-head lib cons-step miss equal-removed premise removed induction goal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((tested (proof-proof-assume proof equal-removed (not keeps-head))))
      (let ((evidence (list cons-step miss tested)))
        (proof-with-checked-results
            ((child (b2-bags-reduced-premise lib premise evidence (list removed) nil))
             (member (if keeps-head
                         (proof-with-checked-results
                             ((first (proof-step-first child))
                              (child (b2-bags-reduced-premise lib child evidence (list first) nil)))
                           (proof-proof-modus-ponens proof induction child))
                       child)))
          (b2-tactics-tactics-solve lib goal (append evidence (list member)) (list goal) nil 0 nil))))))

(defun b2-bags-member-delete-advance-consequent
    (premise lib cons-step induction goal equal-key equal-removed removed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((signed (b2-bags-signed lib equal-key))
         (present (b2-tactics-tactics-solve lib goal (list cons-step (car signed)) (list goal) nil 0 nil))
         (drops (b2-bags-member-delete-advance-branch
                 nil lib cons-step (cadr signed) equal-removed premise removed induction goal))
         (keeps (b2-bags-member-delete-advance-branch
                 t lib cons-step (cadr signed) equal-removed premise removed induction goal))
         (branches (proof-proof-cases proof equal-removed drops keeps))
         (step (proof-proof-cases proof equal-key present branches)))
      (cons step lib))))

(defun b2-bags-member-delete-advance
    (cons-step induction lib condition goal equal-key equal-removed removed)
  (b2-bags-implication
   lib condition goal
   ((premise new-lib)
    (b2-bags-member-delete-advance-consequent
     premise new-lib cons-step induction goal equal-key equal-removed removed))))

(defun b2-bags-member-delete (lib formula)
  (proof-with-checked-results
      ((parts (b2-bags-condition-and-goal formula))
       (condition (proof-list-of-length (car parts) 3))
       (removed (proof-list-of-length (caddr condition) 3)))
    (let* ((goal (cadr parts))
           (xs (caddr removed))
           (head (list *library-car* xs))
           (equal-key (proof-eq (cadr condition) head))
           (equal-removed (proof-eq (cadr removed) head)))
      (proof-with-checked-results
          ((result (b2-bags-on-list
                    lib formula xs nil
                    ((cons-step induction advance-lib)
                     (b2-bags-member-delete-advance
                      cons-step induction advance-lib condition goal equal-key equal-removed removed))
                    ((atom-step base-lib)
                     (b2-bags-member-delete-base atom-step base-lib condition goal removed)))))
        (car result)))))

(defun b2-bags-delete-commutes-equalities (evidence tests)
  (if (endp evidence)
      nil
    (proof-with-checked-results
        ((first (proof-step-first (car evidence)))
         (keep (member-equal first tests))
         (rest (b2-bags-delete-commutes-equalities (cdr evidence) tests)))
      (if keep (cons (car evidence) rest) rest))))

(defun b2-bags-delete-commutes-opener (term equation)
  (proof-with-checked-results
      ((first (b2-bags-equation-first equation))
       (value (proof-term-at first 2)))
    (and (proof-is-call value *proof-cons*)
         (proof-with-checked-results ((item (proof-term-at term 1)))
           (list *b2-bags-del* item value)))))

(defun b2-bags-delete-commutes-advance-branch
    (index evidence lib tests formula left right induction)
  (declare (xargs :measure (nfix (- (len tests) (ifix index)))))
  (if (equal index (len tests))
      (proof-with-checked-results
          ((equalities (b2-bags-delete-commutes-equalities evidence tests)))
        (if (equal (len equalities) 2)
            (b2-tactics-tactics-solve lib formula evidence nil equalities 0 nil)
          (proof-with-checked-results
              ((inner-left (proof-term-at left 2))
               (eq-left (b2-tactics-tactics-normalize lib inner-left evidence
                                                      (list inner-left) nil 1500 nil))
               (inner-right (proof-term-at right 2))
               (eq-right (b2-tactics-tactics-normalize lib inner-right evidence
                                                       (list inner-right) nil 1500 nil))
               (open-left (b2-bags-delete-commutes-opener left eq-left))
               (open-right (b2-bags-delete-commutes-opener right eq-right)))
            (b2-tactics-tactics-solve lib formula evidence
                                     (append (and open-left (list open-left))
                                             (and open-right (list open-right)))
                                     (list eq-left eq-right induction) 0 nil))))
    (if (and (integerp index) (< index (len tests)) (<= (- (len tests)) index))
        (let ((test (nth (if (< index 0) (+ (len tests) index) index) tests)))
          (proof-with-checked-results
              ((signs (b2-bags-signed lib test))
               (yes (b2-bags-delete-commutes-advance-branch
                     (1+ index) (append evidence (list (car signs))) lib tests formula left right induction))
               (no (b2-bags-delete-commutes-advance-branch
                    (1+ index) (append evidence (list (cadr signs))) lib tests formula left right induction)))
            (proof-proof-cases (library-library-proof lib) test yes no)))
      '(:failure "tactic-rejected" ""))))

(defun b2-bags-delete-commutes-advance (cons-step induction lib tests formula left right)
  (proof-with-checked-results
      ((step (b2-bags-delete-commutes-advance-branch
              0 (list cons-step) lib tests formula left right induction)))
    (cons step lib)))

(defun b2-bags-delete-commutes (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left (proof-list-of-length (cadr parts) 3))
       (inner (proof-list-of-length (caddr left) 3)))
    (let* ((right (caddr parts))
           (xs (caddr inner))
           (head (list *library-car* xs))
           (tests (list (proof-eq (cadr left) head) (proof-eq (cadr inner) head))))
      (proof-with-checked-results
          ((result (b2-bags-on-list
                    lib formula xs nil
                    ((cons-step induction advance-lib)
                     (b2-bags-delete-commutes-advance
                      cons-step induction advance-lib tests formula left right))
                    ((atom-step base-lib)
                     (proof-with-checked-results
                         ((step (b2-tactics-tactics-solve base-lib formula (list atom-step)
                                                         (list *b2-bags-del*) nil 0 nil)))
                       (cons step base-lib))))))
        (car result)))))

(defun b2-bags-subbag-delete-base (atom-step lib condition goal)
  (b2-bags-implication
   lib condition goal
   ((premise new-lib)
    (proof-with-checked-results
        ((step (b2-tactics-tactics-solve new-lib goal (list atom-step) (list goal) nil 0 nil)))
      (cons step new-lib)))))

(defun b2-bags-subbag-tail-data (lib name goal included cons-step)
  (if (equal name *b2-bags-subbag-cdr1*)
      (proof-with-checked-results
          ((first (proof-step-first included))
           (parts (proof-list-of-length first 3))
           (opened (b2-bags-reduced-premise lib included (list cons-step) (list first) nil))
           (conjuncts (proof-proof-conjunct (library-library-proof lib) opened)))
        (list (cadr conjuncts) (list *library-car* (cadr parts)) (caddr parts)))
    (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
      (let* ((ys (caddr parts))
             (item (list *library-car* ys))
             (deletion (list *b2-bags-del* item ys)))
        (proof-with-checked-results
            ((equation (b2-tactics-tactics-normalize lib deletion (list cons-step)
                                                     (list deletion) nil 1500 nil))
             (tail (if equation
                       (library-library-transport-argument lib included equation 2)
                     '(:failure "failure" ""))))
          (list tail item ys))))))

(defun b2-bags-intersection-bound-finish
    (lib formula xs call test has-member cons-step atom-step absent
         measure changed unchanged positive inherited)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((negative (b2-tactics-tactics-solve lib formula (list cons-step absent inherited)
                                            (list call) nil 0 nil))
         (base (b2-tactics-tactics-solve lib formula (list atom-step)
                                        (list call *b2-bags-subbag*) nil 0 nil))
         (ordinal (library-library-builtin lib 1 xs))
         (cases (proof-proof-cases proof has-member positive negative))
         (cases (proof-proof-cases proof test cases base))
         (step (proof-proof-induct proof ordinal cases formula measure (list changed unchanged))))
      (cons step lib))))

(defun b2-bags-intersection-cons-advance-recurse (premise lib cons-step no common induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize lib common (list cons-step no)
                                                 (list common) nil 1500 nil))
         (equation (or equation '(:failure "failure" "")))
         (tail (proof-proof-rewrite proof premise equation '(1)))
         (tail (proof-proof-tidy proof tail))
         (goal (proof-proof-modus-ponens proof induction tail))
         (step (library-library-transport-argument lib goal equation 1)))
      (cons step lib))))

(defun b2-bags-intersection-cons-advance (cons-step induction lib common goal test)
  (proof-with-checked-results
      ((signed (b2-bags-signed lib test))
       (positive (b2-bags-implication
                  lib common goal
                  ((premise new-lib)
                   (proof-with-checked-results
                       ((step (b2-tactics-tactics-solve new-lib goal (list cons-step (car signed))
                                                       (list common) nil 0 nil)))
                     (cons step new-lib)))))
       (negative (b2-bags-implication
                  (cdr positive) common goal
                  ((premise new-lib)
                   (b2-bags-intersection-cons-advance-recurse
                    premise new-lib cons-step (cadr signed) common induction))))
       (step (proof-proof-cases (library-library-proof (cdr negative))
                                test (car positive) (car negative))))
    (cons step (cdr negative))))

(defun b2-bags-intersection-cons-base (atom-step lib formula common)
  (proof-with-checked-results
      ((step (b2-tactics-tactics-solve lib formula (list atom-step) (list common) nil 0 nil)))
    (cons step lib)))

(defun b2-bags-intersection-cons-lemma (lib)
  (let* ((common (list *b2-bags-intersect* *library-x* *library-y*))
         (goal (list *proof-consp* common))
         (formula (list *library-implies* common goal))
         (test (list *b2-bags-memb* (list *library-car* *library-x*) *library-y*)))
    (proof-with-checked-results
        ((result (b2-bags-on-list
                  lib formula *library-x* nil
                  ((cons-step induction advance-lib)
                   (b2-bags-intersection-cons-advance cons-step induction advance-lib common goal test))
                  ((atom-step base-lib)
                   (b2-bags-intersection-cons-base atom-step base-lib formula common)))))
      (b2-tactics-tactics-add-lemma (cdr result) "NONEMPTY-BAGINT" (car result) :none))))

(defun b2-bags-intersection-cons (lib present)
  (proof-with-checked-results
      ((call (proof-step-first present))
       (lib (if (assoc-equal *b2-bags-nonempty-intersection*
                             (proof-proof-facts (library-library-proof lib)))
                lib
              (proof-with-checked-results ((added (b2-bags-intersection-cons-lemma lib)))
                (cdr added))))
       (x (proof-term-at call 1))
       (y (proof-term-at call 2))
       (proof (library-library-proof lib))
       (fact (proof-proof-fact proof *b2-bags-nonempty-intersection*
                                (list (list *library-x* x) (list *library-y* y))))
       (step (proof-proof-modus-ponens proof fact present)))
    (cons step lib)))

(defun b2-bags-append-membership-advance (cons-step induction lib formula a append-call xs member)
  (let ((test (proof-eq a (list *library-car* xs))))
    (proof-with-checked-results
        ((joined (b2-tactics-tactics-normalize lib append-call (list cons-step)
                                               (list append-call) nil 1500 nil))
         (first (b2-bags-equation-first joined))
         (body (proof-term-at first 2))
         (signs (b2-bags-signed lib test)))
      (let ((opens (list (list *b2-bags-memb* a body) member))
            (rules (list joined induction)))
        (proof-with-checked-results
            ((yes (b2-tactics-tactics-solve lib formula (list cons-step (car signs)) opens rules 2 t))
             (no (b2-tactics-tactics-solve lib formula (list cons-step (cadr signs)) opens rules 2 t))
             (step (proof-proof-cases (library-library-proof lib) test yes no)))
          (cons step lib))))))

(defun b2-bags-append-membership (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left (proof-list-of-length (cadr parts) 3))
       (append-call (proof-list-of-length (caddr left) 3)))
    (let* ((a (cadr left))
           (xs (cadr append-call))
           (member (list *b2-bags-memb* a xs)))
      (proof-with-checked-results
          ((result (b2-bags-on-list
                    lib formula xs nil
                    ((cons-step induction advance-lib)
                     (b2-bags-append-membership-advance
                      cons-step induction advance-lib formula a append-call xs member))
                    ((atom-step base-lib)
                     (proof-with-checked-results
                         ((step (b2-tactics-tactics-solve base-lib formula (list atom-step)
                                                         (list append-call member) nil 0 nil)))
                       (cons step base-lib))))))
        (car result)))))

(defun b2-bags-fringe-membership-hypothesis (lib formula measure cons-step part sub)
  (let ((goal (list *proof-ordinal-less* (list *library-count* part) measure)))
    (proof-with-checked-results
        ((rulers (b2-measures-rulers-init lib (list cons-step)))
         (decrease (b2-measures-rulers-selector-decrease lib goal rulers)))
      (b2-tactics-tactics-induction-hypothesis lib formula measure sub (car decrease)))))

(defun b2-bags-fringe-membership-singleton (evidence lib key term occurrence fringe formula)
  (let ((test (proof-eq key term))
        (openers (list occurrence fringe *b2-bags-memb* (list *b2-bags-memb* key *proof-false*))))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib test))
         (yes (b2-tactics-tactics-solve lib formula (append evidence (list (car signs))) openers nil 0 nil))
         (no (b2-tactics-tactics-solve lib formula (append evidence (list (cadr signs))) openers nil 0 nil)))
      (proof-proof-cases (library-library-proof lib) test yes no))))

(defun b2-bags-fringe-membership-finish
    (lib formula term key occurrence fringe test same signed matches measure bindings
         left-ih right-ih append-step)
  (let ((proof (library-library-proof lib))
        (cons-step (car signed))
        (atom-step (cadr signed)))
    (proof-with-checked-results
        ((good (b2-tactics-tactics-solve lib formula (list cons-step (car matches))
                                        (list occurrence fringe) (list left-ih right-ih append-step)
                                        0 t))
         (bad (b2-bags-fringe-membership-singleton
               (list cons-step (cadr matches)) lib key term occurrence fringe formula))
         (base (b2-bags-fringe-membership-singleton (list atom-step) lib key term occurrence fringe formula))
         (cases (proof-proof-cases proof same good bad))
         (cases (proof-proof-cases proof test cases base))
         (ordinal (library-library-builtin lib 1 term))
         (step (proof-proof-induct proof ordinal cases formula measure bindings)))
      (cons step lib))))

(mutual-recursion
 (defun b2-bags-bag-fact-with-fuel (n lib name bindings)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-bag-fact-with-fuel")
     (let ((proof (library-library-proof lib)))
       (if (assoc-equal name (proof-proof-facts proof))
           (proof-with-checked-results ((step (proof-proof-fact proof name bindings)))
             (cons step lib))
         (proof-with-checked-results
             ((stem (proof-term-at name 2))
              (stem (if (stringp stem)
                        stem
                      '(:failure "failure" "")))
              (local (proof-sym (concatenate 'string "B2-" stem) "ACL2"))
              (lib (if (assoc-equal local (proof-proof-facts proof))
                       lib
                     (let ((entry (assoc-equal name *b2-bags-formulas*)))
                       (if (not entry)
                           '(:failure "tactic-rejected" "")
                         (proof-with-checked-results
                             ((result (b2-bags-prove-bag-with-fuel (1- n) lib name (cdr entry)))
                              (added (b2-tactics-tactics-add-lemma
                                      (cdr result) stem (car result) :none)))
                           (cdr added))))))
              (step (proof-proof-fact (library-library-proof lib) local bindings)))
           (cons step lib))))))

 (defun b2-bags-subbag-delete-advance-consequent
     (n premise lib cons-step induction condition goal head item ys)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-subbag-delete-advance-consequent")
     (proof-with-checked-results
         ((opened (b2-bags-reduced-premise lib premise (list cons-step) (list condition) nil))
          (parts (proof-proof-conjunct (library-library-proof lib) opened))
          (membership (b2-bags-bag-fact-with-fuel
                       (1- n) lib *b2-bags-member-delete*
                       (list (list *library-x* head) (list *b2-bags-u* item) (list *b2-bags-v* ys))))
          (present (proof-proof-modus-ponens (library-library-proof (cdr membership))
                                            (car membership) (car parts)))
          (commute (b2-bags-bag-fact-with-fuel
                    (1- n) (cdr membership) *b2-bags-delete-commutes*
                    (list (list *library-x* head) (list *library-y* item) (list *library-z* ys)))))
       (let* ((lib (cdr commute))
              (proof (library-library-proof lib)))
         (proof-with-checked-results
             ((smaller (proof-proof-rewrite proof (cadr parts) (car commute) '(1 2)))
              (smaller (proof-proof-tidy proof smaller))
              (inherited (proof-proof-modus-ponens proof induction smaller))
              (step (b2-tactics-tactics-solve lib goal (list cons-step present inherited)
                                              (list goal) nil 0 nil)))
           (cons step lib))))))

 (defun b2-bags-subbag-delete-advance
     (n cons-step induction lib condition goal head item ys)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-subbag-delete-advance")
     (b2-bags-implication
      lib condition goal
      ((premise new-lib)
       (b2-bags-subbag-delete-advance-consequent
        (1- n) premise new-lib cons-step induction condition goal head item ys)))))

 (defun b2-bags-subbag-delete-with-fuel (n lib formula)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-subbag-delete-with-fuel")
     (proof-with-checked-results
         ((parts (b2-bags-condition-and-goal formula))
          (condition (proof-list-of-length (car parts) 3))
          (deletion (proof-list-of-length (caddr condition) 3)))
       (let* ((goal (cadr parts))
              (xs (cadr condition))
              (item (cadr deletion))
              (ys (caddr deletion))
              (head (list *library-car* xs))
              (after (list *b2-bags-del* head ys)))
         (b2-bags-on-list
          lib formula xs (list (list ys after))
          ((cons-step induction advance-lib)
           (b2-bags-subbag-delete-advance
            (1- n) cons-step induction advance-lib condition goal head item ys))
          ((atom-step base-lib)
           (b2-bags-subbag-delete-base atom-step base-lib condition goal)))))))

 (defun b2-bags-subbag-tail-consequent (n premise lib name goal)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-subbag-tail-consequent")
     (proof-with-checked-results
         ((conjuncts (proof-proof-conjunct (library-library-proof lib) premise))
          (data (b2-bags-subbag-tail-data lib name goal (car conjuncts) (cadr conjuncts)))
          (x (proof-term-at goal 1))
          (fact (b2-bags-bag-fact-with-fuel
                 (1- n) lib *b2-bags-subbag-delete*
                 (list (list *library-x* x) (list *b2-bags-u* (cadr data))
                       (list *library-y* (caddr data)))))
          (step (proof-proof-modus-ponens (library-library-proof (cdr fact)) (car fact) (car data))))
       (cons step (cdr fact)))))

 (defun b2-bags-subbag-tail-with-fuel (n lib name formula)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-subbag-tail-with-fuel")
     (proof-with-checked-results ((parts (b2-bags-condition-and-goal formula)))
       (let ((condition (car parts))
             (goal (cadr parts)))
         (b2-bags-implication
          lib condition goal
          ((premise new-lib)
           (b2-bags-subbag-tail-consequent (1- n) premise new-lib name goal)))))))

 (defun b2-bags-intersection-bound-with-fuel (n lib name formula)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-intersection-bound-with-fuel")
     (proof-with-checked-results
         ((parts (proof-list-of-length formula 3))
          (call (proof-list-of-length (cadr parts) 3)))
       (let* ((xs (cadr call))
              (ys (caddr call))
              (a (list *library-car* xs))
              (tail (list *library-cdr* xs))
              (after (list *b2-bags-del* a ys))
              (has-member (list *b2-bags-memb* a ys))
              (test (list *proof-consp* xs))
              (proof (library-library-proof lib)))
         (proof-with-checked-results
             ((signs (b2-bags-signed lib test))
              (member-signs (b2-bags-signed lib has-member)))
           (let* ((cons-step (car signs))
                  (atom-step (cadr signs))
                  (member (car member-signs))
                  (absent (cadr member-signs))
                  (unchanged (list (list xs tail)))
                  (changed (append unchanged (list (list ys after))))
                  (measure (list *library-count* xs)))
             (proof-with-checked-results
                 ((builtin (library-library-builtin lib 3 xs))
                  (smaller (proof-proof-discharge proof builtin cons-step))
                  (ih-yes (b2-tactics-tactics-induction-hypothesis
                           lib formula measure changed smaller))
                  (ih-no (b2-tactics-tactics-induction-hypothesis
                          lib formula measure unchanged smaller)))
               (if (equal name *b2-bags-intersect1*)
                   (let* ((rest (list *b2-bags-intersect* tail ys))
                          (deletion (list *b2-bags-del* a xs))
                          (member-x (list *b2-bags-memb* a xs)))
                     (proof-with-checked-results
                         ((cut (b2-tactics-tactics-normalize lib deletion (list cons-step)
                                                             (list deletion) nil 1500 nil))
                          (present (b2-tactics-tactics-solve lib member-x (list cons-step)
                                                             (list member-x) nil 0 nil))
                          (weaker (b2-bags-bag-fact-with-fuel
                                   (1- n) lib *b2-bags-subbag-cdr2*
                                   (list (list *library-x* rest) (list *library-y* xs))))
                          (weaker-first (proof-step-first (car weaker)))
                          (condition (proof-term-at weaker-first 1))
                          (guard (b2-tactics-tactics-solve (cdr weaker) condition
                                                           (list cons-step ih-no) nil nil 0 nil))
                          (inherited (proof-proof-modus-ponens
                                      (library-library-proof (cdr weaker)) (car weaker) guard))
                          (positive (b2-tactics-tactics-solve
                                     (cdr weaker) formula (list cons-step member present ih-yes)
                                     (list call *b2-bags-subbag*) (list cut) 0 nil)))
                       (b2-bags-intersection-bound-finish
                        (cdr weaker) formula xs call test has-member cons-step atom-step absent
                        measure changed unchanged positive inherited)))
                 (proof-with-checked-results
                     ((positive (b2-tactics-tactics-solve lib formula (list cons-step member ih-yes)
                                                          (list call *b2-bags-subbag*) nil 0 nil)))
                   (b2-bags-intersection-bound-finish
                    lib formula xs call test has-member cons-step atom-step absent
                    measure changed unchanged positive ih-no))))))))))

 (defun b2-bags-fringe-membership-with-fuel (n lib formula)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-fringe-membership-with-fuel")
     (proof-with-checked-results
         ((parts (proof-list-of-length formula 3))
          (member (proof-list-of-length (caddr parts) 3))
          (fringe (proof-list-of-length (caddr member) 3)))
       (let* ((occurrence (cadr parts))
              (key (cadr member))
              (operation (cadr fringe))
              (term (caddr fringe))
              (test (list *proof-consp* term))
              (same (proof-eq (list *library-car* term) operation)))
         (proof-with-checked-results ((signed (b2-bags-signed lib test))
                                      (matches (b2-bags-signed lib same)))
           (let* ((measure (list *library-count* term))
                  (cdr-term (list *library-cdr* term))
                  (left (list *library-car* cdr-term))
                  (right (list *library-car* (list *library-cdr* cdr-term)))
                  (left-sub (list (list term left)))
                  (right-sub (list (list term right))))
             (proof-with-checked-results
                 ((left-ih (b2-bags-fringe-membership-hypothesis
                            lib formula measure (car signed) left left-sub))
                  (right-ih (b2-bags-fringe-membership-hypothesis
                             lib formula measure (car signed) right right-sub))
                  (append-step (b2-bags-bag-fact-with-fuel
                                (1- n) lib *b2-bags-member-append*
                                (list (list *b2-bags-a* key)
                                      (list *library-x* (list *b2-bags-fringe* operation left))
                                      (list *library-y* (list *b2-bags-fringe* operation right))))))
               (b2-bags-fringe-membership-finish
                (cdr append-step) formula term key occurrence fringe test same signed matches
                measure (list left-sub right-sub) left-ih right-ih (car append-step)))))))))

 (defun b2-bags-prove-bag-with-fuel (n lib name formula)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "b2-bags-prove-bag-with-fuel")
     (cond ((equal name *b2-bags-member-delete*)
            (proof-with-checked-results ((step (b2-bags-member-delete lib formula)))
              (cons step lib)))
           ((equal name *b2-bags-delete-commutes*)
            (proof-with-checked-results ((step (b2-bags-delete-commutes lib formula)))
              (cons step lib)))
           ((equal name *b2-bags-subbag-delete*)
            (b2-bags-subbag-delete-with-fuel (1- n) lib formula))
           ((or (equal name *b2-bags-subbag-cdr1*) (equal name *b2-bags-subbag-cdr2*))
            (b2-bags-subbag-tail-with-fuel (1- n) lib name formula))
           ((or (equal name *b2-bags-intersect1*) (equal name *b2-bags-intersect2*))
            (b2-bags-intersection-bound-with-fuel (1- n) lib name formula))
           ((equal name *b2-bags-member-append*)
            (proof-with-checked-results ((step (b2-bags-append-membership lib formula)))
              (cons step lib)))
           (t (b2-bags-fringe-membership-with-fuel (1- n) lib formula))))))

(defun b2-bags-bag-fact (lib name bindings)
  (b2-bags-bag-fact-with-fuel 1000000 lib name bindings))

(defun b2-bags-prove-bag (lib name formula)
  (b2-bags-prove-bag-with-fuel 1000000 lib name formula))
