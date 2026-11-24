(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-agreement-lookup* (proof-sym "HONS-ASSOC-EQUAL" "ACL2"))
(defconst *h4-book-agreement-get* (proof-sym "HONS-GET" "ACL2"))
(defconst *h4-book-agreement-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h4-book-agreement-agree* (proof-sym "ALISTS-AGREE" "ACL2"))
(defconst *h4-book-agreement-disagree* (proof-sym "ALISTS-DISAGREE-WITNESS" "ACL2"))
(defconst *h4-book-agreement-subset* (proof-sym "SUB-ALISTP" "ACL2"))
(defconst *h4-book-agreement-subset-witness* (proof-sym "NOT-SUB-ALISTP-WITNESS" "ACL2"))
(defconst *h4-book-agreement-equiv* (proof-sym "ALIST-EQUIV" "ACL2"))
(defconst *h4-book-agreement-bad-guy* (proof-sym "ALIST-EQUIV-BAD-GUY" "ACL2"))
(defconst *h4-book-agreement-iff* (proof-sym "IFF" "ACL2"))
(defconst *h4-book-agreement-hons-equal* (proof-sym "HONS-EQUAL" "ACL2"))
(defconst *h4-book-agreement-key-list* (proof-sym "H4-KEY-LIST" "ACL2"))
(defconst *h4-book-agreement-lookup-key* (proof-sym "H4-LOOKUP-KEY" "ACL2"))

(defmacro h4-book-agreement-cases (p formula test positive negative)
  `(let ((h4-book-agreement-test ,test))
     (proof-with-checked-results
         ((,(car positive) (proof-proof-assume
                            (library-library-proof ,p) h4-book-agreement-test t))
          (h4-book-agreement-yes ,(cadr positive))
          (,(car negative) (proof-proof-assume
                            (library-library-proof ,p) h4-book-agreement-test nil))
          (h4-book-agreement-no ,(cadr negative)))
       (h4-tactics-tactics-case-of
        ,p ,formula h4-book-agreement-test h4-book-agreement-yes h4-book-agreement-no))))

(defmacro h4-book-agreement-cdr-cases (p formula sequence pair atom)
  `(let ((h4-book-agreement-test (list *proof-consp* ,sequence)))
     (proof-with-checked-results
         ((,(car pair) (proof-proof-assume
                        (library-library-proof ,p) h4-book-agreement-test t))
          (,(cadr pair) (h4-book-flatten-cdr-induction-recurse ,(car pair) ,p ,formula ,sequence nil))
          (h4-book-agreement-pair ,(caddr pair))
          (,(car atom) (proof-proof-assume
                        (library-library-proof ,p) h4-book-agreement-test nil))
          (h4-book-agreement-atom ,(cadr atom)))
       (h4-book-flatten-cdr-induction
        ,p ,formula ,sequence h4-book-agreement-atom h4-book-agreement-pair nil))))

(defun h4-book-agreement-binding-pairs (bindings)
  (if (endp bindings)
      nil
    (cons (list (proof-sym (text-replace (text-upper (caar bindings)) "_" "-") "ACL2")
                (cdar bindings))
          (h4-book-agreement-binding-pairs (cdr bindings)))))

(defun h4-book-agreement-instantiate (p name bindings)
  (proof-proof-fact (library-library-proof p) (proof-sym name "ACL2")
                    (h4-book-agreement-binding-pairs bindings)))

(defun h4-book-agreement-iff-transport (p equivalence evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((formula (proof-step-first equivalence)))
      (if (not (proof-is-call formula *h4-book-agreement-iff*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((sides (proof-list-of-length (cdr formula) 2))
             (signed (proof-step-first evidence)))
          (let* ((left (car sides))
                 (right (cadr sides))
                 (positive (or (equal signed left) (equal signed right)))
                 (other (cond ((or (equal signed left) (equal signed (proof-neg left))) right)
                              ((or (equal signed right) (equal signed (proof-neg right))) left)
                              (t :invalid))))
            (if (eq other :invalid)
                '(:failure "failure" "")
              (proof-with-checked-results
                  ((opposite (proof-proof-assume proof other (not positive)))
                   (reduction (h4-tactics-tactics-normalize
                               p formula (list evidence opposite) (list *h4-book-agreement-iff*) nil nil))
                   (literal (proof-step-first reduction))
                   (value (proof-term-at literal 2)))
                (if (not (equal value *proof-false*))
                    '(:failure "failure" "")
                  (proof-with-checked-results
                      ((rewritten (proof-proof-rewrite proof equivalence reduction '(1)))
                       (conflict (proof-proof-tidy proof rewritten)))
                    (proof-proof-front proof conflict (if positive other (proof-neg other)))))))))))))

(defun h4-book-agreement-member-head (p term key shape equality)
  (proof-with-checked-results
      ((result (h4-book-projections-open-selected
                p (list *h4-book-agreement-member* key term) (list shape equality) nil nil))
       (nonempty (h4-book-sets-nonempty-value p shape)))
    (proof-proof-transport (library-library-proof p) nonempty result)))

(defun h4-book-agreement-member-from-tail-missing (sign p tail-found goal shape)
  (proof-with-checked-results
      ((opened (h4-book-projections-open-selected p goal (list shape sign) nil nil)))
    (proof-proof-transport (library-library-proof p) tail-found opened)))

(defun h4-book-agreement-member-from-tail (p term tail-found shape)
  (proof-with-checked-results
      ((literal (proof-step-first tail-found))
       (parts (proof-list-of-length literal 3)))
    (let* ((key (cadr parts))
           (goal (list *h4-book-agreement-member* key term))
           (test (proof-eq key (list *library-car* term))))
      (h4-book-agreement-cases
       p goal test
       (same (h4-book-agreement-member-head p term key shape same))
       (sign (h4-book-agreement-member-from-tail-missing sign p tail-found goal shape))))))

(defun h4-book-agreement-unfold-agreement (p relation)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof relation))
         (literal (proof-step-first opened))
         (body (proof-term-at literal 2))
         (normalized (h4-tactics-tactics-normalize p body nil nil nil nil)))
      (proof-proof-chain proof opened (list normalized)))))

(defun h4-book-agreement-agreement-lookup-empty (shape p formula goal member)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first member))
         (opened (h4-book-projections-open-selected p literal (list shape) nil nil))
         (impossible (proof-proof-rewrite proof member opened '(1)))
         (subsumed (proof-proof-subsume
                    proof impossible (cons goal (cdr (proof-step-clause impossible))))))
      (h4-tactics-tactics-imply p formula subsumed))))

(defun h4-book-agreement-agreement-lookup-pair-found (same p formula head)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first head))
         (normalized (h4-tactics-tactics-normalize
                      p literal nil (list *h4-book-agreement-get*) nil nil))
         (projected (proof-proof-rewrite proof head normalized '(1)))
         (reverse (proof-proof-symmetric proof projected))
         (same-reverse (proof-proof-symmetric proof same))
         (swapped (proof-proof-rewrite-first proof reverse same-reverse)))
      (h4-tactics-tactics-imply p formula swapped))))

(defun h4-book-agreement-agreement-lookup-pair-missed (sign p formula member shape child rest)
  (proof-with-checked-results
      ((literal (proof-step-first member))
       (opened (h4-book-projections-open-selected p literal (list shape sign) nil nil))
       (tail-member (proof-proof-rewrite (library-library-proof p) member opened '(1)))
       (premise (h4-book-division-conjunction p (list rest tail-member)))
       (result (h4-tactics-tactics-modus-ponens p child premise)))
    (h4-tactics-tactics-imply p formula result)))

(defun h4-book-agreement-agreement-lookup-pair (shape child p formula agreeing member key keys)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first agreeing))
         (opened (h4-book-projections-open-selected p literal (list shape) nil nil))
         (rewritten (proof-proof-rewrite proof agreeing opened '(1)))
         (conjuncts (h4-tactics-tactics-conjunct p rewritten)))
      (let ((head-test (proof-eq key (list *library-car* keys))))
        (h4-book-agreement-cases
         p formula head-test
         (same (h4-book-agreement-agreement-lookup-pair-found same p formula (car conjuncts)))
         (sign (h4-book-agreement-agreement-lookup-pair-missed
                sign p formula member shape child (cadr conjuncts))))))))

(defun h4-book-agreement-agreement-lookup (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((parts (proof-list-of-length (cdr formula) 2))
         (assumed (proof-proof-assume proof (car parts) t))
         (conjuncts (h4-tactics-tactics-conjunct p assumed))
         (member (cadr conjuncts))
         (literal (proof-step-first member))
         (member-parts (proof-list-of-length literal 3)))
      (let ((key (cadr member-parts)) (keys (caddr member-parts)))
        (h4-book-agreement-cdr-cases
         p formula keys
         (shape child (h4-book-agreement-agreement-lookup-pair
                       shape child p formula (car conjuncts) member key keys))
         (shape (h4-book-agreement-agreement-lookup-empty shape p formula (cadr parts) member)))))))

(defun h4-book-agreement-find-disagreement-empty (shape p formula relation goal denied)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((yes (h4-tactics-tactics-establish
               p relation (list shape)
               (append *h4-book-flatten-logic* (list *h4-book-agreement-agree*)) nil nil))
         (conflict (proof-proof-cut proof yes denied))
         (subsumed (proof-proof-subsume proof conflict (cons goal (proof-step-clause conflict)))))
      (h4-tactics-tactics-imply p formula subsumed))))

(defun h4-book-agreement-find-disagreement-pair-agrees
    (sign p relation shape denied child keys witness formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((projected (h4-book-projections-open-selected p relation (list shape sign) nil nil))
         (remaining (proof-proof-rewrite proof denied projected '(1 1)))
         (applied (h4-tactics-tactics-modus-ponens p child remaining))
         (conjuncts (h4-tactics-tactics-conjunct p applied))
         (found (h4-book-agreement-member-from-tail p keys (car conjuncts) shape))
         (result (h4-book-division-conjunction p (list found (cadr conjuncts))))
         (next-witness (h4-book-projections-open-selected p witness (list shape sign) nil nil))
         (reverse (proof-proof-symmetric proof next-witness))
         (rewritten (proof-proof-rewrite-first proof result reverse)))
      (h4-tactics-tactics-imply p formula rewritten))))

(defun h4-book-agreement-find-disagreement-pair-differs (sign p keys head shape witness formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof head))
         (found (h4-book-agreement-member-head p keys head shape reflexive))
         (literal (proof-step-first sign))
         (test (proof-term-at literal 1))
         (reduced (h4-tactics-tactics-normalize p test nil (list *h4-book-agreement-get*) nil nil))
         (mismatch (proof-proof-rewrite proof sign reduced '(1 1)))
         (first-witness (h4-book-projections-open-selected p witness (list shape sign) nil nil))
         (result (h4-book-division-conjunction p (list found mismatch)))
         (reverse (proof-proof-symmetric proof first-witness))
         (rewritten (proof-proof-rewrite-first proof result reverse)))
      (h4-tactics-tactics-imply p formula rewritten))))

(defun h4-book-agreement-find-disagreement-pair (shape child p keys a b relation denied witness formula)
  (let* ((head (list *library-car* keys))
         (test (proof-eq (list *h4-book-agreement-get* head a)
                        (list *h4-book-agreement-get* head b))))
    (h4-book-agreement-cases
     p formula test
     (sign (h4-book-agreement-find-disagreement-pair-agrees
            sign p relation shape denied child keys witness formula))
     (sign (h4-book-agreement-find-disagreement-pair-differs sign p keys head shape witness formula)))))

(defun h4-book-agreement-find-disagreement (p keys a b)
  (let* ((relation (list *h4-book-agreement-agree* keys a b))
         (witness (list *h4-book-agreement-disagree* keys a b))
         (member (list *h4-book-agreement-member* witness keys))
         (different (proof-neg (proof-eq (list *h4-book-agreement-lookup* witness a)
                                         (list *h4-book-agreement-lookup* witness b))))
         (goal (proof-ite member different *proof-false*))
         (formula (list *library-implies* (proof-neg relation) goal)))
    (proof-with-checked-results
        ((denied (proof-proof-assume (library-library-proof p) (proof-neg relation) t)))
      (h4-book-agreement-cdr-cases
       p formula keys
       (shape child (h4-book-agreement-find-disagreement-pair
                     shape child p keys a b relation denied witness formula))
       (shape (h4-book-agreement-find-disagreement-empty shape p formula relation goal denied))))))

(defun h4-book-agreement-agreement-on-key (p agreed membership)
  (proof-with-checked-results
      ((relation (proof-step-first agreed))
       (parts (proof-list-of-length relation 4))
       (literal (proof-step-first membership))
       (key (proof-term-at literal 1))
       (rule (h4-book-agreement-instantiate
              p "ALISTS-AGREE-HONS-ASSOC-EQUAL"
              (list (cons "keys" (cadr parts)) (cons "a" (caddr parts))
                    (cons "b" (cadddr parts)) (cons "x" key))))
       (premise (h4-book-division-conjunction p (list agreed membership)))
       (step (h4-tactics-tactics-modus-ponens p rule premise)))
    (proof-proof-symmetric (library-library-proof p) step)))

(defun h4-book-agreement-key-membership-equivalence (p key alist)
  (h4-book-agreement-instantiate p "ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL"
                                 (list (cons "x" key) (cons "a" alist))))

(defun h4-book-agreement-subset-on-key (p subset found)
  (proof-with-checked-results
      ((relation (proof-step-first subset))
       (parts (proof-list-of-length relation 3))
       (literal (proof-step-first found))
       (key (proof-term-at literal 1))
       (rule (h4-book-agreement-instantiate
              p "SUB-ALISTP-HONS-ASSOC-EQUAL"
              (list (cons "a" (cadr parts)) (cons "b" (caddr parts)) (cons "x" key))))
       (premise (h4-book-division-conjunction p (list subset found))))
    (h4-tactics-tactics-modus-ponens p rule premise)))

(defun h4-book-agreement-compare-lookups-missing (not-first p formula second converse)
  (let ((proof (library-library-proof p)))
    (h4-book-agreement-cases
     p formula second
     (found (proof-with-checked-results ((step (h4-book-agreement-subset-on-key p converse found)))
              (proof-proof-symmetric proof step)))
     (not-second
      (proof-with-checked-results
          ((first-nil (h4-tactics-tactics-nil-value p not-first))
           (second-nil (h4-tactics-tactics-nil-value p not-second))
           (reverse (proof-proof-symmetric proof second-nil)))
        (proof-proof-chain proof first-nil (list reverse)))))))

(defun h4-book-agreement-compare-lookups (p pair key)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((relation (proof-step-first pair))
         (parts (proof-list-of-length relation 3)))
      (let* ((first (list *h4-book-agreement-lookup* key (cadr parts)))
             (second (list *h4-book-agreement-lookup* key (caddr parts)))
             (formula (proof-eq first second)))
        (proof-with-checked-results
            ((opened (h4-book-agreement-unfold-agreement p relation))
             (rewritten (proof-proof-rewrite proof pair opened '(1)))
             (conjuncts (h4-tactics-tactics-conjunct p rewritten)))
          (h4-book-agreement-cases
           p formula first
           (found (h4-book-agreement-subset-on-key p (car conjuncts) found))
           (not-first (h4-book-agreement-compare-lookups-missing
                       not-first p formula second (cadr conjuncts)))))))))

(defun h4-book-agreement-first-difference-all-keys (key p left right match choices)
  (let* ((proof (library-library-proof p))
         (aim (proof-eq (list *h4-book-agreement-lookup* key left)
                        (list *h4-book-agreement-lookup* key right))))
    (proof-with-checked-results
        ((chosen (h4-book-choice-choice-fact
                  p *h4-book-agreement-bad-guy*
                  (list (list (proof-sym "BG" "ACL2") key)
                        (list (proof-sym "AL1" "ACL2") left)
                        (list (proof-sym "AL2" "ACL2") right))
                  choices))
         (assumed (proof-proof-assume proof aim nil))
         (denied (h4-tactics-tactics-modus-ponens p chosen assumed))
         (cut (proof-proof-cut proof match denied)))
      (proof-proof-front proof cut aim))))

(defun h4-book-agreement-agreement-boolean-pair (shape child p call)
  (proof-with-checked-results
      ((opened (h4-book-projections-open-selected p call (list shape) nil nil)))
    (h4-book-sets-boolean-result p opened child)))

(defun h4-book-agreement-agreement-boolean-atom (shape p call)
  (proof-with-checked-results
      ((nil-value (h4-tactics-tactics-nil-value p shape))
       (reduced (h4-book-projections-open-selected p call nil nil (list nil-value))))
    (h4-book-sets-boolean-result p reduced nil)))

(defun h4-book-agreement-agreement-boolean (p)
  (let* ((key-list *h4-book-agreement-key-list*)
         (call (list *h4-book-agreement-agree* key-list *library-x* *library-y*))
         (goal (list *h4-book-sets-boolean* call)))
    (h4-book-agreement-cdr-cases
     p goal key-list
     (shape child (h4-book-agreement-agreement-boolean-pair shape child p call))
     (shape (h4-book-agreement-agreement-boolean-atom shape p call)))))

(defun h4-book-agreement-relation-boolean-prepare (p relation agreement)
  (proof-with-checked-results ((head (proof-term-at relation 0)))
    (if (equal head *h4-book-agreement-agree*)
        (proof-with-checked-results
            ((parts (proof-list-of-length relation 4))
             (instance (proof-proof-instantiate
                        (library-library-proof p) agreement
                        (list (list *h4-book-agreement-key-list* (cadr parts))
                              (list *library-x* (caddr parts))
                              (list *library-y* (cadddr parts))))))
          (cons :agreement instance))
      (proof-with-checked-results ((opened (h4-book-agreement-unfold-agreement p relation)))
        (cond
         ((equal head *h4-book-agreement-subset*)
          (proof-with-checked-results
              ((literal (proof-step-first opened))
               (body (proof-term-at literal 2)))
            (list :subset opened body)))
         ((equal head *h4-book-agreement-equiv*)
          (proof-with-checked-results
              ((literal (proof-step-first opened))
               (body (proof-term-at literal 2))
               (right (proof-term-at body 2)))
            (list :equivalence opened right)))
         (t '(:failure "failure" "")))))))

(defun h4-book-agreement-relation-boolean-prepared (n p agreement prepared)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h4-book-agreement-relation-boolean-prepared"))
        ((failure-p prepared) prepared)
        ((eq (car prepared) :agreement) (cdr prepared))
        (t (proof-with-checked-results
               ((child (h4-book-agreement-relation-boolean-prepared
                        (1- n) p agreement
                        (h4-book-agreement-relation-boolean-prepare p (caddr prepared) agreement))))
             (if (eq (car prepared) :subset)
                 (library-library-transport-argument p child (cadr prepared) 1)
               (h4-book-sets-boolean-result p (cadr prepared) child))))))

(defun h4-book-agreement-relation-boolean (n p relation agreement)
  (if (zp n)
      '(:failure "Fuel" "h4-book-agreement-relation-boolean")
    (h4-book-agreement-relation-boolean-prepared
     n p agreement (h4-book-agreement-relation-boolean-prepare p relation agreement))))

(defun h4-book-agreement-subset-directions (p step)
  (proof-with-checked-results
      ((relation (proof-step-first step))
       (opened (h4-book-agreement-unfold-agreement p relation))
       (rewritten (proof-proof-rewrite (library-library-proof p) step opened '(1))))
    (h4-tactics-tactics-conjunct p rewritten)))

(defun h4-book-agreement-join-subsets (p first second)
  (proof-with-checked-results
      ((literal (proof-step-first first))
       (relation (cons *h4-book-agreement-equiv* (cdr literal)))
       (conjoined (h4-book-division-conjunction p (list first second)))
       (opened (h4-book-agreement-unfold-agreement p relation)))
    (proof-proof-transport (library-library-proof p) conjoined opened)))

(defun h4-book-agreement-map-lookup (p call signs provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (literal (proof-step-first opened))
         (body (proof-term-at literal 2))
         (reduced (h4-tactics-tactics-normalize
                   p body signs (append *h4-book-flatten-logic* (list *h4-book-agreement-hons-equal*))
                   nil provide)))
      (proof-proof-chain proof opened (list reduced)))))

(defun h4-book-agreement-lookup-append-open-append (shape p call)
  (proof-with-checked-results
      ((append-call (proof-term-at call 2))
       (opened (h4-book-flatten-unfold-on-list p append-call *library-x* shape)))
    (h4-book-flatten-rewrite-argument p call 2 opened)))

(defun h4-book-agreement-lookup-append-apply-test (lookup p selection a)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((reflexive (proof-proof-reflexive proof selection)))
      (proof-proof-rewrite-result proof reflexive lookup
                                  (proof-eq *proof-result* selection) a))))

(defun h4-book-agreement-lookup-append-atom (shape p call a provide selection)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((turned (h4-book-agreement-lookup-append-open-append shape p call))
         (mapped (h4-book-agreement-map-lookup p a (list shape) provide))
         (right (h4-book-agreement-lookup-append-apply-test mapped p selection a))
         (right-literal (proof-step-first right))
         (if-term (proof-term-at right-literal 2))
         (choose (h4-tactics-tactics-select-literal p if-term))
         (right (proof-proof-chain proof right (list choose)))
         (reverse (proof-proof-symmetric proof right)))
      (proof-proof-chain proof turned (list reverse)))))

(defun h4-book-agreement-lookup-append-pair-branch
    (additional hit p exposed a shape provide selection child)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((exposed-literal (proof-step-first exposed))
         (exposed-call (proof-term-at exposed-literal 2))
         (exposed-mapped (h4-book-agreement-map-lookup p exposed-call additional provide))
         (left (proof-proof-chain proof exposed (list exposed-mapped)))
         (mapped (h4-book-agreement-map-lookup p a (cons shape additional) provide))
         (right (h4-book-agreement-lookup-append-apply-test mapped p selection a)))
      (if hit
          (proof-with-checked-results
              ((nonnil (h4-book-sets-nonempty-value p hit))
               (right-literal (proof-step-first right))
               (if-term (proof-term-at right-literal 2))
               (selected (proof-proof-select proof if-term nonnil))
               (right (proof-proof-chain proof right (list selected)))
               (reverse (proof-proof-symmetric proof right)))
            (proof-proof-chain proof left (list reverse)))
        (proof-with-checked-results
            ((left (proof-proof-chain proof left (list child)))
             (reverse (proof-proof-symmetric proof right)))
          (proof-proof-chain proof left (list reverse)))))))

(defun h4-book-agreement-lookup-congruence-lookup-branch
    (signs hit p left right provide same-tail)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first (h4-book-agreement-map-lookup p left signs provide))
         (second (h4-book-agreement-map-lookup p right signs provide))
         (reverse (proof-proof-symmetric proof second)))
      (proof-proof-chain proof first (list (if hit nil same-tail) reverse)))))

(defun h4-book-agreement-member-after-lookup-atom (shape p lookup provide found goal formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((mapped (h4-book-agreement-map-lookup p lookup (list shape) provide))
         (impossible (proof-proof-rewrite proof found mapped '(1)))
         (step (proof-proof-subsume proof impossible
                                    (cons goal (cdr (proof-step-clause impossible))))))
      (h4-tactics-tactics-imply p formula step))))

(defun h4-book-agreement-member-after-lookup-lift (p child found located projected)
  (proof-with-checked-results
      ((tail-found (proof-proof-rewrite (library-library-proof p) found located '(1)))
       (member (h4-tactics-tactics-modus-ponens p child tail-found))
       (literal (proof-step-first projected))
       (mapped (proof-term-at literal 2))
       (member (if (proof-is-call mapped *proof-cons*)
                   (proof-with-checked-results ((arguments (proof-list-of-length (cdr mapped) 2)))
                     (h4-book-sets-member-extension p (car arguments) (cadr arguments) member))
                 member)))
    (library-library-transport-argument p member projected 2)))

(defun h4-book-agreement-member-after-lookup-pair-branch
    (signs hit p shape lookup goal provide found child formula)
  (let ((proof (library-library-proof p))
        (known (cons shape signs)))
    (proof-with-checked-results
        ((located (h4-book-agreement-map-lookup p lookup known provide))
         (projection (proof-term-at goal 2))
         (projected (h4-book-projections-open-selected p projection known provide nil))
         (member (if hit
                     (h4-book-projection-sets-projected-member p projected)
                   (h4-book-agreement-member-after-lookup-lift p child found located projected)))
         (reverse (proof-proof-symmetric proof located))
         (restored (proof-proof-rewrite proof member reverse '(1 1 1))))
      (h4-tactics-tactics-imply p formula restored))))

(defun h4-book-agreement-lookup-head-solve (p solve signs hit)
  (let ((arguments (cdr solve)))
    (case (car solve)
      (:lookup-append
       (h4-book-agreement-lookup-append-pair-branch
        signs hit p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)
        (nth 4 arguments) (nth 5 arguments)))
      (:lookup-congruence
       (h4-book-agreement-lookup-congruence-lookup-branch
        signs hit p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)))
      (:member-after-lookup
       (h4-book-agreement-member-after-lookup-pair-branch
        signs hit p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)
        (nth 4 arguments) (nth 5 arguments) (nth 6 arguments)))
      (otherwise
       (table-get solve (list signs hit) '(:failure "failure" ""))))))

(defun h4-book-agreement-on-lookup-head-pair-branch (sign p test shape solve)
  (proof-with-checked-results ((literal (proof-step-first sign)))
    (h4-book-agreement-lookup-head-solve
     p solve (list shape sign) (and (equal literal test) shape))))

(defun h4-book-agreement-on-lookup-head-pair (shape p formula key head solve)
  (let ((test (proof-eq key (list *library-car* head))))
    (h4-book-agreement-cases
     p formula test
     (sign (h4-book-agreement-on-lookup-head-pair-branch sign p test shape solve))
     (sign (h4-book-agreement-on-lookup-head-pair-branch sign p test shape solve)))))

(defun h4-book-agreement-on-lookup-head (p formula key head solve)
  (h4-book-agreement-cases
   p formula (list *proof-consp* head)
   (shape (h4-book-agreement-on-lookup-head-pair shape p formula key head solve))
   (shape (h4-book-agreement-lookup-head-solve p solve (list shape) nil))))

(defun h4-book-agreement-lookup-append-pair (shape child p call a provide selection formula key)
  (proof-with-checked-results
      ((exposed (h4-book-agreement-lookup-append-open-append shape p call)))
    (h4-book-agreement-on-lookup-head
     p formula key (list *library-car* *library-x*)
     (list :lookup-append exposed a shape provide selection child))))

(defun h4-book-agreement-lookup-append (p)
  (let* ((key *h4-book-agreement-lookup-key*)
         (call (list *h4-book-agreement-lookup* key
                     (list *h4-book-flatten-append* *library-x* *library-y*)))
         (a (list *h4-book-agreement-lookup* key *library-x*))
         (b (list *h4-book-agreement-lookup* key *library-y*))
         (selection (proof-ite a a b))
         (formula (proof-eq call selection)))
    (proof-with-checked-results ((provide (h4-book-finite-reduction-provider p)))
      (h4-book-agreement-cdr-cases
       p formula *library-x*
       (shape child (h4-book-agreement-lookup-append-pair
                     shape child p call a provide selection formula key))
       (shape (h4-book-agreement-lookup-append-atom shape p call a provide selection))))))

(defun h4-book-agreement-lookup-congruence-lookup-cons (key p a b given head provide)
  (let* ((left (list *h4-book-agreement-lookup* key a))
         (right (list *h4-book-agreement-lookup* key b))
         (goal (proof-eq left right)))
    (proof-with-checked-results ((same-tail (h4-book-agreement-compare-lookups p given key)))
      (h4-book-agreement-on-lookup-head
       p goal key head (list :lookup-congruence left right provide same-tail)))))

(defun h4-book-agreement-lookup-congruence-append-instance (p general term key)
  (proof-with-checked-results
      ((first (proof-term-at term 1))
       (second (proof-term-at term 2)))
    (proof-proof-instantiate
     (library-library-proof p) general
     (list (list *library-x* first) (list *library-y* second)
           (list *h4-book-agreement-lookup-key* key)))))

(defun h4-book-agreement-lookup-congruence-lookup-append (key p a b given general)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((same-tail (h4-book-agreement-compare-lookups p given key))
         (first (h4-book-agreement-lookup-congruence-append-instance p general a key))
         (second (h4-book-agreement-lookup-congruence-append-instance p general b key))
         (first-literal (proof-step-first first))
         (first-right (proof-term-at first-literal 2))
         (tail-literal (proof-step-first same-tail))
         (slot (proof-term-at tail-literal 1))
         (rewritten (proof-proof-rewrite-result proof first same-tail
                                                (proof-eq *proof-result* first-right) slot))
         (reverse (proof-proof-symmetric proof second)))
      (proof-proof-chain proof rewritten (list reverse)))))

(defun h4-book-agreement-member-after-lookup-pair (shape child p lookup goal provide found formula key alist)
  (h4-book-agreement-on-lookup-head
   p formula key (list *library-car* alist)
   (list :member-after-lookup shape lookup goal provide found child formula)))

(defun h4-book-agreement-member-after-lookup (p formula)
  (proof-with-checked-results
      ((lookup (proof-term-at formula 1))
       (parts (proof-list-of-length lookup 3))
       (found (proof-proof-assume (library-library-proof p) lookup t))
       (goal (proof-term-at formula 2))
       (provide (h4-book-finite-reduction-provider p)))
    (let ((key (cadr parts)) (alist (caddr parts)))
      (h4-book-agreement-cdr-cases
       p formula alist
       (shape child (h4-book-agreement-member-after-lookup-pair
                     shape child p lookup goal provide found formula key alist))
       (shape (h4-book-agreement-member-after-lookup-atom shape p lookup provide found goal formula))))))

(defun h4-book-agreement-list-spine-equivalence-compare (key p conditional variable given)
  (proof-with-checked-results
      ((lookup (proof-proof-instantiate
                (library-library-proof p) conditional (list (list variable key)))))
    (h4-tactics-tactics-modus-ponens p lookup given)))

(defun h4-book-agreement-agreement-congruence-transfer-pointwise (key member p source given converse)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((agreement (h4-book-agreement-agreement-on-key p source member))
         (equivalent (h4-book-agreement-compare-lookups p given key))
         (step (if converse (proof-proof-symmetric proof equivalent) equivalent)))
      (proof-proof-chain proof agreement (list step)))))

(defun h4-book-agreement-subset-congruence-transfer-pointwise (key found p given source converse)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((equation (h4-book-agreement-compare-lookups p given key))
         (equation (if converse equation (proof-proof-symmetric proof equation)))
         (original (proof-proof-rewrite proof found equation '(1)))
         (step (h4-book-agreement-subset-on-key p source original)))
      (proof-proof-chain proof equation (list step)))))

(defun h4-book-agreement-from-agreement-pointwise (key found p left right)
  (declare (ignore key))
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first (h4-book-agreement-subset-on-key p left found))
         (rewritten (proof-proof-rewrite proof found first '(1)))
         (second (h4-book-agreement-subset-on-key p right rewritten)))
      (proof-proof-chain proof first (list second)))))

(defun h4-book-agreement-pointwise-step (p pointwise key evidence)
  (let ((arguments (cdr pointwise)))
    (case (car pointwise)
      (:all-keys
       (h4-book-agreement-first-difference-all-keys
        key p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)))
      (:reflexive
       (proof-proof-reflexive (library-library-proof p)
                              (list *h4-book-agreement-lookup* key (car arguments))))
      (:list-spine
       (h4-book-agreement-list-spine-equivalence-compare
        key p (car arguments) (cadr arguments) (caddr arguments)))
      (:agreement-transfer
       (h4-book-agreement-agreement-congruence-transfer-pointwise
        key evidence p (car arguments) (cadr arguments) (caddr arguments)))
      (:subset-transfer
       (h4-book-agreement-subset-congruence-transfer-pointwise
        key evidence p (car arguments) (cadr arguments) (caddr arguments)))
      (:lookup-cons
       (h4-book-agreement-lookup-congruence-lookup-cons
        key p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments) (nth 4 arguments)))
      (:lookup-append
       (h4-book-agreement-lookup-congruence-lookup-append
        key p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)))
      (:subset-transitivity
       (h4-book-agreement-from-agreement-pointwise key evidence p (car arguments) (cadr arguments)))
      (:compare-lookups (h4-book-agreement-compare-lookups p (car arguments) key))
      (:keys (table-get arguments key '(:failure "failure" "")))
      (otherwise
       (table-get pointwise (list key evidence) '(:failure "failure" ""))))))

(defun h4-book-agreement-pointwise (p pointwise key evidence)
  (if (eq (car pointwise) :symmetric)
      (proof-with-checked-results
          ((step (h4-book-agreement-pointwise-step p (cadr pointwise) key evidence)))
        (proof-proof-symmetric (library-library-proof p) step))
    (h4-book-agreement-pointwise-step p pointwise key evidence)))

(defun h4-book-agreement-prove-subset (p a b pointwise)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((equivalence (h4-book-agreement-instantiate p "SUB-ALISTP-IFF-WITNESS"
                                                   (list (cons "a" a) (cons "b" b))))
         (literal (proof-step-first equivalence))
         (wrapped (proof-term-at literal 2))
         (lifted (proof-proof-beta proof wrapped))
         (lifted-literal (proof-step-first lifted))
         (guard (proof-term-at lifted-literal 2))
         (premise (proof-term-at guard 1))
         (parts (proof-list-of-length premise 3))
         (assumed (proof-proof-assume proof premise t))
         (same (h4-book-agreement-pointwise p pointwise (cadr parts) assumed))
         (implies (h4-tactics-tactics-imply p guard same))
         (transported (proof-proof-transport proof implies lifted)))
      (h4-book-agreement-iff-transport p equivalence transported))))

(defun h4-book-agreement-prove-agreement (p keys a b pointwise)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((equivalent (h4-book-agreement-instantiate
                      p "ALISTS-AGREE-IFF-WITNESS"
                      (list (cons "keys" keys) (cons "al1" a) (cons "al2" b))))
         (literal (proof-step-first equivalent))
         (wrapped (proof-term-at literal 2))
         (opened (proof-proof-beta proof wrapped))
         (opened-literal (proof-step-first opened))
         (implication (proof-term-at opened-literal 2))
         (premise (proof-term-at implication 1))
         (member (proof-proof-assume proof premise t))
         (member-literal (proof-step-first member))
         (key (proof-term-at member-literal 1))
         (value (h4-book-agreement-pointwise p pointwise key member))
         (implies (h4-tactics-tactics-imply p implication value))
         (transported (proof-proof-transport proof implies opened)))
      (h4-book-agreement-iff-transport p equivalent transported))))

(defun h4-book-agreement-first-difference (p step a b reversed-order choices)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (beta (proof-proof-beta proof literal))
         (given (proof-proof-rewrite proof step beta '(1))))
      (let ((relation (list *h4-book-agreement-equiv* a b))
            (left (if reversed-order b a))
            (right (if reversed-order a b)))
        (proof-with-checked-results
            ((match (if reversed-order (proof-proof-symmetric proof given) given))
             (pointwise (list :all-keys left right match choices))
             (first (h4-book-agreement-prove-subset p left right pointwise))
             (second (h4-book-agreement-prove-subset p right left (list :symmetric pointwise)))
             (subsets (if reversed-order (list second first) (list first second)))
             (conjoined (h4-book-division-conjunction p subsets))
             (opened (h4-book-agreement-unfold-agreement p relation)))
          (proof-proof-transport proof conjoined opened))))))

(defun h4-book-agreement-prove-alist-equiv (p a b pointwise)
  (proof-with-checked-results
      ((direct (h4-book-agreement-prove-subset p a b pointwise))
       (reverse (h4-book-agreement-prove-subset p b a (list :symmetric pointwise))))
    (h4-book-agreement-join-subsets p direct reverse)))

(defun h4-book-agreement-lookup-congruence (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((premise (proof-term-at formula 1))
         (given (proof-proof-assume proof premise t))
         (goal (proof-term-at formula 2))
         (parts (proof-list-of-length goal 3))
         (a (cadr parts))
         (b (caddr parts))
         (provide (h4-book-finite-reduction-provider p))
         (lookup (if (proof-is-call a *proof-cons*)
                     (proof-with-checked-results ((head (proof-term-at a 1)))
                       (list :lookup-cons a b given head provide))
                   (proof-with-checked-results ((general (h4-book-agreement-lookup-append p)))
                     (list :lookup-append a b given general))))
         (step (h4-book-agreement-prove-alist-equiv p a b lookup)))
      (h4-tactics-tactics-imply p formula step))))

(defun h4-book-agreement-equivalence-laws (p)
  (let* ((proof (library-library-proof p))
         (same (list *h4-book-agreement-equiv* *library-x* *library-y*))
         (reverse (list *h4-book-agreement-equiv* *library-y* *library-x*)))
    (proof-with-checked-results
        ((agreement (h4-book-agreement-agreement-boolean p))
         (typed (h4-book-agreement-relation-boolean 1000000 p same agreement))
         (reflexive (h4-book-agreement-prove-alist-equiv p *library-x* *library-x*
                                                       (list :reflexive *library-x*)))
         (assumed (proof-proof-assume proof same t))
         (directions (h4-book-agreement-subset-directions p assumed))
         (joined (h4-book-agreement-join-subsets p (cadr directions) (car directions)))
         (symmetric (h4-tactics-tactics-imply p (list *library-implies* same reverse) joined))
         (guard (proof-ite same (list *h4-book-agreement-equiv* *library-y* *library-z*) *proof-false*))
         (guard-step (proof-proof-assume proof guard t))
         (pair (h4-tactics-tactics-conjunct p guard-step))
         (first (h4-book-agreement-subset-directions p (car pair)))
         (second (h4-book-agreement-subset-directions p (cadr pair)))
         (rule (h4-book-agreement-instantiate p "SUB-ALISTP-TRANS"
                                            (list (cons "x" *library-x*) (cons "y" *library-y*)
                                                  (cons "z" *library-z*))))
         (premise (h4-book-division-conjunction p (list (car first) (car second))))
         (composed (h4-tactics-tactics-modus-ponens p rule premise))
         (rule (h4-book-agreement-instantiate p "SUB-ALISTP-TRANS"
                                            (list (cons "x" *library-z*) (cons "y" *library-y*)
                                                  (cons "z" *library-x*))))
         (premise (h4-book-division-conjunction p (list (cadr second) (cadr first))))
         (backward (h4-tactics-tactics-modus-ponens p rule premise))
         (result (h4-book-agreement-join-subsets p composed backward))
         (transitive (h4-tactics-tactics-imply
                      p (list *library-implies* guard (list *h4-book-agreement-equiv* *library-x* *library-z*))
                      result)))
      (h4-book-division-conjunction p (list typed reflexive symmetric transitive)))))

(defun h4-book-agreement-list-spine-equivalence (p formula)
  (proof-with-checked-results
      ((premise (proof-term-at formula 1))
       (given (proof-proof-assume (library-library-proof p) premise t))
       (literal (proof-step-first given))
       (sides (proof-list-of-length (cdr literal) 2)))
    (let* ((a (car sides))
           (b (cadr sides))
           (variable *h4-book-agreement-lookup-key*)
           (left (list *h4-book-agreement-lookup* variable a))
           (right (list *h4-book-agreement-lookup* variable b)))
      (proof-with-checked-results
          ((conditional (h4-book-projections-list-equiv-proof
                         p (list *library-implies* literal (proof-eq left right))
                         (list left right 2)))
           (equivalent (h4-book-agreement-prove-alist-equiv
                        p a b (list :list-spine conditional variable given))))
        (h4-tactics-tactics-imply p formula equivalent)))))

(defun h4-book-agreement-agreement-iff-forward (known p implication opened)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((premise (proof-term-at implication 1))
         (assumed (proof-proof-assume proof premise t))
         (equality (h4-book-agreement-agreement-on-key p known assumed))
         (implied (h4-tactics-tactics-imply p implication equality)))
      (proof-proof-transport proof implied opened))))

(defun h4-book-agreement-agreement-iff-backward (denied p keys a b wrapped opened)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((disagreement (h4-book-agreement-find-disagreement p keys a b))
         (applied (h4-tactics-tactics-modus-ponens p disagreement denied))
         (conjuncts (h4-tactics-tactics-conjunct p applied))
         (assumed (proof-proof-assume proof wrapped t))
         (rewritten (proof-proof-rewrite proof assumed opened '(1)))
         (result (h4-tactics-tactics-modus-ponens p rewritten (car conjuncts)))
         (cut (proof-proof-cut proof result (cadr conjuncts))))
      (proof-proof-front proof cut (proof-neg wrapped)))))

(defun h4-book-agreement-subset-iff-forward (known p related comparison implication names opened)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((agrees (proof-proof-rewrite proof known related '(1)))
         (result (h4-book-agreement-iff-transport p comparison agrees))
         (premise (proof-term-at implication 1))
         (found (proof-proof-assume proof premise t))
         (member (h4-book-agreement-iff-transport p names found))
         (same (h4-tactics-tactics-modus-ponens p result member))
         (implied (h4-tactics-tactics-imply p implication same)))
      (proof-proof-transport proof implied opened))))

(defun h4-book-agreement-subset-iff-backward (denied p related comparison names wrapped opened)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((no-agreement (proof-proof-rewrite proof denied related '(1 1)))
         (no-implication (h4-book-agreement-iff-transport p comparison no-agreement))
         (literal (proof-step-first no-implication))
         (member-guard (proof-term-at literal 1))
         (premise (proof-term-at member-guard 1))
         (assumed (proof-proof-assume proof premise t))
         (found (h4-book-agreement-iff-transport p names assumed))
         (assumed (proof-proof-assume proof wrapped t))
         (rewritten (proof-proof-rewrite proof assumed opened '(1)))
         (same (h4-tactics-tactics-modus-ponens p rewritten found))
         (implied (h4-tactics-tactics-imply p member-guard same))
         (impossible (proof-proof-cut proof implied no-implication)))
      (proof-proof-front proof impossible (proof-neg wrapped)))))

(defun h4-book-agreement-witness-equivalence-forward (proven p witness opened)
  (proof-with-checked-results ((compared (h4-book-agreement-compare-lookups p proven witness)))
    (proof-proof-transport (library-library-proof p) compared opened)))

(defun h4-book-agreement-witness-equivalence-backward (denied p wrapped a b choices)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((given (proof-proof-assume proof wrapped t))
         (proven (h4-book-agreement-first-difference p given a b nil choices))
         (cut (proof-proof-cut proof proven denied)))
      (proof-proof-front proof cut (proof-neg wrapped)))))

(defun h4-book-agreement-iff-forward (p callback sign)
  (let ((arguments (cdr callback)))
    (case (car callback)
      (:agreement (h4-book-agreement-agreement-iff-forward
                   sign p (car arguments) (cadr arguments)))
      (:subset (h4-book-agreement-subset-iff-forward
                sign p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)
                (nth 4 arguments)))
      (:equivalent (h4-book-agreement-witness-equivalence-forward
                    sign p (car arguments) (cadr arguments)))
      (otherwise (table-get callback sign '(:failure "failure" ""))))))

(defun h4-book-agreement-iff-backward (p callback sign)
  (let ((arguments (cdr callback)))
    (case (car callback)
      (:agreement (h4-book-agreement-agreement-iff-backward
                   sign p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)
                   (nth 4 arguments)))
      (:subset (h4-book-agreement-subset-iff-backward
                sign p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)
                (nth 4 arguments)))
      (:equivalent (h4-book-agreement-witness-equivalence-backward
                    sign p (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments)))
      (otherwise (table-get callback sign '(:failure "failure" ""))))))

(defun h4-book-agreement-prove-iff-branch (sign p formula forward backward)
  (proof-with-checked-results
      ((literal (proof-step-first sign))
       (left (proof-term-at formula 1))
       (second (if (equal literal left)
                   (h4-book-agreement-iff-forward p forward sign)
                 (h4-book-agreement-iff-backward p backward sign))))
    (h4-tactics-tactics-establish
     p formula (list sign second) (list *h4-book-agreement-iff*) nil nil)))

(defun h4-book-agreement-prove-iff (p formula forward backward)
  (proof-with-checked-results ((test (proof-term-at formula 1)))
    (h4-book-agreement-cases
     p formula test
     (sign (h4-book-agreement-prove-iff-branch sign p formula forward backward))
     (sign (h4-book-agreement-prove-iff-branch sign p formula forward backward)))))

(defun h4-book-agreement-agreement-iff (p formula)
  (proof-with-checked-results
      ((sides (proof-list-of-length (cdr formula) 2))
       (parts (proof-list-of-length (car sides) 4))
       (wrapped (cadr sides))
       (opened (proof-proof-beta (library-library-proof p) wrapped))
       (literal (proof-step-first opened))
       (implication (proof-term-at literal 2)))
    (h4-book-agreement-prove-iff
     p formula (list :agreement implication opened)
     (list :agreement (cadr parts) (caddr parts) (cadddr parts) wrapped opened))))

(defun h4-book-agreement-subset-iff (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((sides (proof-list-of-length (cdr formula) 2))
         (relation (car sides))
         (wrapped (cadr sides))
         (parts (proof-list-of-length relation 3))
         (a (cadr parts))
         (b (caddr parts))
         (keys (list *h4-book-projections-keys* a))
         (comparison (h4-book-agreement-instantiate
                      p "ALISTS-AGREE-IFF-WITNESS"
                      (list (cons "keys" keys) (cons "al1" a) (cons "al2" b))))
         (comparison-literal (proof-step-first comparison))
         (comparison-right (proof-term-at comparison-literal 2))
         (body (proof-proof-beta proof comparison-right))
         (comparison (proof-proof-rewrite proof comparison body '(1 2)))
         (opened (proof-proof-beta proof wrapped))
         (opened-literal (proof-step-first opened))
         (opened-right (proof-term-at opened-literal 2))
         (reduced (h4-tactics-tactics-normalize
                   p opened-right nil (list *h4-book-agreement-subset-witness*) nil nil))
         (opened (proof-proof-chain proof opened (list reduced)))
         (literal (proof-step-first opened))
         (implication (proof-term-at literal 2))
         (premise (proof-term-at implication 1))
         (key (proof-term-at premise 1))
         (names (h4-book-agreement-key-membership-equivalence p key a))
         (related (h4-book-agreement-unfold-agreement p relation)))
      (h4-book-agreement-prove-iff
       p formula (list :subset related comparison implication names opened)
       (list :subset related comparison names wrapped opened)))))

(defun h4-book-agreement-witness-call (wrapped)
  (and (proof-compound wrapped) (consp (cdr wrapped))
       (proof-compound (car wrapped)) (cadr wrapped)))

(defun h4-book-agreement-witness-equivalence (p formula choices)
  (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
    (let* ((relation (car sides))
           (wrapped (cadr sides))
           (witness (h4-book-agreement-witness-call wrapped)))
      (cond
       ((and (proof-is-call relation *h4-book-agreement-agree*)
             (equal witness (cons *h4-book-agreement-disagree* (cdr relation))))
        (h4-book-agreement-agreement-iff p formula))
       ((and (proof-is-call relation *h4-book-agreement-subset*)
             (equal witness (cons *h4-book-agreement-subset-witness* (cdr relation))))
        (h4-book-agreement-subset-iff p formula))
       ((and (proof-is-call relation *h4-book-agreement-equiv*)
             (equal witness (cons *h4-book-agreement-bad-guy* (cdr relation))))
        (proof-with-checked-results
            ((arguments (proof-list-of-length (cdr relation) 2))
             (opened (proof-proof-beta (library-library-proof p) wrapped)))
          (h4-book-agreement-prove-iff
           p formula (list :equivalent witness opened)
           (list :equivalent wrapped (car arguments) (cadr arguments) choices))))
       (t nil)))))

(defun h4-book-agreement-agreement-congruence-transfer (source target converse p keys a given)
  (h4-book-agreement-prove-agreement
   p keys a target (list :agreement-transfer source given converse)))

(defun h4-book-agreement-subset-congruence-transfer (source target converse p b given)
  (h4-book-agreement-prove-subset p target b (list :subset-transfer given source converse)))

(defun h4-book-agreement-boolean-transfer (p callback sign)
  (let ((arguments (cdr callback)))
    (case (car callback)
      (:agreement
       (h4-book-agreement-agreement-congruence-transfer
        sign (car arguments) (cadr arguments) p (caddr arguments) (cadddr arguments) (nth 4 arguments)))
      (:subset
       (h4-book-agreement-subset-congruence-transfer
        sign (car arguments) (cadr arguments) p (caddr arguments) (cadddr arguments)))
      (otherwise (table-get callback sign '(:failure "failure" ""))))))

(defun h4-book-agreement-equal-booleans-positive (sign p left-type right-type forward)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first (h4-book-order-true-boolean-value p sign left-type))
         (transferred (h4-book-agreement-boolean-transfer p forward sign))
         (last (h4-book-order-true-boolean-value p transferred right-type))
         (reverse (proof-proof-symmetric proof last)))
      (proof-proof-chain proof first (list reverse)))))

(defun h4-book-agreement-equal-booleans-negative (sign p right backward)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof right t))
         (transferred (h4-book-agreement-boolean-transfer p backward assumed))
         (impossible (proof-proof-cut proof transferred sign))
         (not-right (proof-proof-front proof impossible (proof-neg right)))
         (left-nil (h4-tactics-tactics-nil-value p sign))
         (right-nil (h4-tactics-tactics-nil-value p not-right))
         (reverse (proof-proof-symmetric proof right-nil)))
      (proof-proof-chain proof left-nil (list reverse)))))

(defun h4-book-agreement-equal-booleans (p formula forward backward)
  (proof-with-checked-results
      ((sides (proof-list-of-length (cdr formula) 2))
       (left (car sides))
       (right (cadr sides))
       (boolean (h4-book-agreement-agreement-boolean p))
       (left-type (h4-book-agreement-relation-boolean 1000000 p left boolean))
       (right-type (h4-book-agreement-relation-boolean 1000000 p right boolean)))
    (h4-book-agreement-cases
     p formula left
     (sign (h4-book-agreement-equal-booleans-positive sign p left-type right-type forward))
     (sign (h4-book-agreement-equal-booleans-negative sign p right backward)))))

(defun h4-book-agreement-agreement-congruence (p formula)
  (proof-with-checked-results
      ((premise (proof-term-at formula 1))
       (given (proof-proof-assume (library-library-proof p) premise t))
       (goal (proof-term-at formula 2))
       (sides (proof-list-of-length (cdr goal) 2))
       (arguments (proof-list-of-length (cdar sides) 3))
       (keys (car arguments))
       (a (cadr arguments))
       (b (caddr arguments))
       (other (proof-term-at (cadr sides) 3))
       (equality (h4-book-agreement-equal-booleans
                  p goal (list :agreement other nil keys a given)
                  (list :agreement b t keys a given))))
    (h4-tactics-tactics-imply p formula equality)))

(defun h4-book-agreement-subset-congruence (p formula)
  (proof-with-checked-results
      ((premise (proof-term-at formula 1))
       (given (proof-proof-assume (library-library-proof p) premise t))
       (goal (proof-term-at formula 2))
       (sides (proof-list-of-length (cdr goal) 2))
       (arguments (proof-list-of-length (cdar sides) 2))
       (a (car arguments))
       (b (cadr arguments))
       (other (proof-term-at (cadr sides) 1))
       (equality (h4-book-agreement-equal-booleans
                  p goal (list :subset other nil b given) (list :subset a t b given))))
    (h4-tactics-tactics-imply p formula equality)))

(defun h4-book-agreement-set-of-keys-direction-atom (shape p claim goal variable)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((truth (proof-proof-prove proof *proof-true* nil nil))
         (opened (h4-book-flatten-unfold-on-list p goal variable shape))
         (step (proof-proof-transport proof truth opened)))
      (h4-tactics-tactics-imply p claim step))))

(defun h4-book-agreement-set-of-keys-direction-pair
    (shape child p included equivalent reverse source target goal variable claim)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((parts (h4-book-sets-subset-parts p included shape))
         (present (car parts))
         (literal (proof-step-first present))
         (key (proof-term-at literal 1))
         (look (h4-book-agreement-compare-lookups p equivalent key))
         (look (if reverse (proof-proof-symmetric proof look) look))
         (source-membership (h4-book-agreement-key-membership-equivalence p key source))
         (original (h4-book-agreement-iff-transport p source-membership present))
         (transferred (proof-proof-rewrite proof original look '(1)))
         (target-membership (h4-book-agreement-key-membership-equivalence p key target))
         (head (h4-book-agreement-iff-transport p target-membership transferred))
         (premise (h4-book-division-conjunction p (list equivalent (cadr parts))))
         (child-subset (h4-tactics-tactics-modus-ponens p child premise))
         (conjoined (h4-book-division-conjunction p (list head child-subset)))
         (opened (h4-book-flatten-unfold-on-list p goal variable shape))
         (step (proof-proof-transport proof conjoined opened)))
      (h4-tactics-tactics-imply p claim step))))

(defun h4-book-agreement-set-of-keys-direction (source target reverse p relation subset-reflexivity variable)
  (let* ((proof (library-library-proof p))
         (premise (list *h4-book-sets-subset* variable (list *h4-book-projections-keys* source)))
         (goal (list *h4-book-sets-subset* variable (list *h4-book-projections-keys* target)))
         (hypothesis (proof-ite relation premise *proof-false*))
         (claim (list *library-implies* hypothesis goal)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof hypothesis t))
         (parts (h4-tactics-tactics-conjunct p assumed))
         (induction
          (h4-book-agreement-cdr-cases
           p claim variable
           (shape child (h4-book-agreement-set-of-keys-direction-pair
                         shape child p (cadr parts) (car parts) reverse source target goal variable claim))
           (shape (h4-book-agreement-set-of-keys-direction-atom shape p claim goal variable))))
         (keys (list *h4-book-projections-keys* source))
         (self-rule (proof-proof-instantiate
                     proof subset-reflexivity (list (list *library-x* keys) (list *library-y* keys))))
         (literal (proof-step-first self-rule))
         (test (proof-term-at literal 1))
         (term (proof-term-at test 1))
         (reflexive (proof-proof-reflexive proof term))
         (self-subset (h4-tactics-tactics-modus-ponens p self-rule reflexive))
         (instantiated (proof-proof-instantiate proof induction (list (list variable keys))))
         (given (proof-proof-assume proof relation t))
         (evidence (h4-book-division-conjunction p (list given self-subset))))
      (h4-tactics-tactics-modus-ponens p instantiated evidence))))

(defun h4-book-agreement-set-of-keys (p formula)
  (proof-with-checked-results
      ((relation (proof-term-at formula 1))
       (arguments (proof-list-of-length (cdr relation) 2))
       (a (car arguments))
       (b (cadr arguments))
       (subset-reflexivity (h4-book-sets-subset-of-equal-fixes p))
       (first (h4-book-agreement-set-of-keys-direction
               a b nil p relation subset-reflexivity *h4-book-agreement-key-list*))
       (second (h4-book-agreement-set-of-keys-direction
                b a t p relation subset-reflexivity *h4-book-agreement-key-list*))
       (pair (h4-book-sets-set-pair p first second)))
    (h4-tactics-tactics-imply p formula pair)))

(defun h4-book-agreement-from-agreement-lookup (p formula call key a)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof call t))
         (parts (h4-tactics-tactics-conjunct p assumed))
         (subset (car parts))
         (literal (proof-step-first subset))
         (opened (h4-book-agreement-unfold-agreement p literal))
         (agreed (proof-proof-rewrite proof subset opened '(1)))
         (equivalence (h4-book-agreement-key-membership-equivalence p key a))
         (member (h4-book-agreement-iff-transport p equivalence (cadr parts)))
         (step (h4-book-agreement-agreement-on-key p agreed member)))
      (h4-tactics-tactics-imply p formula step))))

(defun h4-book-agreement-from-agreement-compose (p formula call a b)
  (proof-with-checked-results
      ((assumed (proof-proof-assume (library-library-proof p) call t))
       (parts (h4-tactics-tactics-conjunct p assumed))
       (step (h4-book-agreement-prove-subset
              p a b (list :subset-transitivity (car parts) (cadr parts)))))
    (h4-tactics-tactics-imply p formula step)))

(defun h4-book-agreement-from-agreement-subset (p formula call goal relation evidence)
  (proof-with-checked-results ((arguments (proof-list-of-length (cdr relation) 2)))
    (let ((a (car arguments)) (b (cadr arguments)))
      (cond
       ((proof-is-call evidence *h4-book-agreement-lookup*)
        (proof-with-checked-results ((source (proof-term-at evidence 2)))
          (and (equal source a)
               (proof-with-checked-results ((key (proof-term-at evidence 1)))
                 (and (equal goal (proof-eq evidence (list *h4-book-agreement-lookup* key b)))
                      (h4-book-agreement-from-agreement-lookup p formula call key a))))))
       ((proof-is-call evidence *h4-book-agreement-subset*)
        (proof-with-checked-results ((source (proof-term-at evidence 1)))
          (and (equal source b)
               (proof-with-checked-results ((target (proof-term-at evidence 2)))
                 (and (equal goal (list *h4-book-agreement-subset* a target))
                      (h4-book-agreement-from-agreement-compose p formula call a target))))))
       (t nil)))))

(defun h4-book-agreement-from-agreement (p formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (cadr parts))
       (goal (caddr parts))
       (no (proof-term-at call 3)))
    (and (equal no *proof-false*)
         (let ((relation (cadr call)) (evidence (caddr call)))
           (cond
            ((and (proof-is-call relation *h4-book-agreement-agree*)
                  (proof-is-call evidence *h4-book-agreement-member*))
             (proof-with-checked-results
                 ((keys (proof-term-at relation 1))
                  (membership (proof-term-at evidence 2)))
               (and (equal keys membership)
                    (proof-with-checked-results
                        ((sides (proof-list-of-length (cddr relation) 2))
                         (key (proof-term-at evidence 1)))
                      (and (equal goal (proof-eq (list *h4-book-agreement-lookup* key (cadr sides))
                                                 (list *h4-book-agreement-lookup* key (car sides))))
                           (h4-book-agreement-agreement-lookup p formula))))))
            ((proof-is-call relation *h4-book-agreement-subset*)
             (h4-book-agreement-from-agreement-subset p formula call goal relation evidence))
            (t nil))))))

(defun h4-book-agreement-same-lookup-consequences (p formula equivalent)
  (proof-with-checked-results
      ((literal (proof-step-first equivalent))
       (relation (proof-list-of-length literal 3))
       (a (cadr relation))
       (b (caddr relation))
       (goal (proof-term-at formula 2)))
    (cond
     ((proof-is-call goal *proof-equal*)
      (proof-with-checked-results ((left (proof-term-at goal 1)))
        (and (proof-is-call left *h4-book-agreement-lookup*)
             (proof-with-checked-results
                 ((right (proof-term-at goal 2)) (key (proof-term-at left 1)))
               (and (equal right (list *h4-book-agreement-lookup* key b))
                    (proof-with-checked-results ((alist (proof-term-at left 2)))
                      (and (equal alist a)
                           (proof-with-checked-results
                               ((compared (h4-book-agreement-compare-lookups p equivalent key)))
                             (h4-tactics-tactics-imply p formula compared)))))))))
     ((and (proof-is-call goal *h4-book-agreement-agree*)
           (equal (cddr goal) (list a b)))
      (proof-with-checked-results
          ((agreed (h4-book-agreement-prove-agreement
                    p (cadr goal) a b (list :compare-lookups equivalent))))
        (h4-tactics-tactics-imply p formula agreed)))
     (t nil))))

(defun h4-book-agreement-alist-congruence-lookup-p (left right a b)
  (cond
   ((proof-is-call left *proof-cons*)
    (proof-with-checked-results ((tail (proof-term-at left 2)))
      (and (equal tail a) (equal right (list *proof-cons* (cadr left) b)))))
   ((proof-is-call left *h4-book-flatten-append*)
    (proof-with-checked-results ((last (proof-term-at left 2)))
      (let ((first (cadr left)))
        (or (and (equal last a) (equal right (list *h4-book-flatten-append* first b)))
            (and (equal first a) (equal right (list *h4-book-flatten-append* b last)))))))
   (t nil)))

(defun h4-book-agreement-alist-congruence (p formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (guard (proof-list-of-length (cadr parts) 3))
       (a (cadr guard))
       (b (caddr guard))
       (goal (caddr parts)))
    (cond
     ((proof-is-call goal *proof-equal*)
      (proof-with-checked-results ((sides (proof-list-of-length (cdr goal) 2)))
        (let ((left (car sides)) (right (cadr sides)))
          (cond
           ((proof-is-call left *h4-book-agreement-agree*)
            (proof-with-checked-results ((last (proof-term-at left 3)))
              (and (equal last a)
                   (equal right (list *h4-book-agreement-agree* (cadr left) (caddr left) b))
                   (h4-book-agreement-agreement-congruence p formula))))
           ((proof-is-call left *h4-book-agreement-subset*)
            (proof-with-checked-results ((first (proof-term-at left 1)))
              (and (equal first a)
                   (proof-with-checked-results ((last (proof-term-at left 2)))
                     (and (equal right (list *h4-book-agreement-subset* b last))
                          (h4-book-agreement-subset-congruence p formula))))))
           (t nil)))))
     ((proof-is-call goal *h4-book-agreement-equiv*)
      (proof-with-checked-results
          ((sides (proof-list-of-length (cdr goal) 2))
           (match (h4-book-agreement-alist-congruence-lookup-p (car sides) (cadr sides) a b)))
        (and match (h4-book-agreement-lookup-congruence p formula))))
     ((equal goal (list *h4-book-sets-set-equiv* (list *h4-book-projections-keys* a)
                       (list *h4-book-projections-keys* b)))
      (h4-book-agreement-set-of-keys p formula))
     (t nil))))

(defun h4-book-agreement-lookup-absence (p formula guard goal)
  (proof-with-checked-results ((member (proof-term-at guard 1)))
    (and (proof-is-call member *h4-book-agreement-member*)
         (proof-with-checked-results ((keys (proof-term-at member 2)))
           (and (proof-is-call keys *h4-book-projections-keys*)
                (proof-with-checked-results
                    ((arguments (proof-list-of-length (cdr member) 2))
                     (parts (proof-list-of-length keys 2)))
                  (let ((key (car arguments)) (a (cadr parts)))
                    (and (equal goal (proof-eq (list *h4-book-agreement-lookup* key a) *proof-false*))
                         (proof-with-checked-results
                             ((rule (h4-book-agreement-key-membership-equivalence p key a))
                              (assumed (proof-proof-assume (library-library-proof p) guard t))
                              (absence (h4-book-agreement-iff-transport p rule assumed))
                              (step (h4-tactics-tactics-nil-value p absence)))
                           (h4-tactics-tactics-imply p formula step))))))))))

(defun h4-book-agreement-witness-consequences (p formula guard goal choices)
  (let ((witness (h4-book-agreement-witness-call guard))
        (proof (library-library-proof p)))
    (and (proof-is-call witness *h4-book-agreement-bad-guy*)
         (proof-with-checked-results
             ((sides (proof-list-of-length (cdr witness) 2))
              (a (car sides))
              (b (cadr sides))
              (given (proof-proof-assume proof guard t)))
           (cond
            ((equal goal (list *h4-book-agreement-subset* b a))
             (proof-with-checked-results
                 ((equivalent (h4-book-agreement-first-difference p given b a t choices))
                  (literal (proof-step-first equivalent))
                  (opened (h4-book-agreement-unfold-agreement p literal))
                  (rewritten (proof-proof-rewrite proof equivalent opened '(1)))
                  (pair (h4-tactics-tactics-conjunct p rewritten)))
               (h4-tactics-tactics-imply p formula (car pair))))
            ((equal goal (proof-eq (list *h4-book-agreement-equiv* a b) *proof-true*))
             (proof-with-checked-results
                 ((equivalent (h4-book-agreement-first-difference p given a b nil choices))
                  (boolean (h4-book-agreement-instantiate
                            p "ALIST-EQUIV-IS-AN-EQUIVALENCE"
                            (list (cons "x" a) (cons "y" b))))
                  (pair (h4-tactics-tactics-conjunct p boolean))
                  (step (h4-book-order-true-boolean-value p equivalent (car pair))))
               (h4-tactics-tactics-imply p formula step)))
            ((and (proof-is-call goal *h4-book-agreement-agree*)
                  (equal (cddr goal) (list a b)))
             (proof-with-checked-results
                 ((equivalent (h4-book-agreement-first-difference p given a b nil choices)))
               (h4-book-agreement-same-lookup-consequences p formula equivalent)))
            (t nil))))))

(defun h4-book-agreement-agreement-implication (p formula choices)
  (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
    (let ((guard (cadr parts)) (goal (caddr parts)))
      (cond
       ((proof-is-call guard *h4-book-flatten-list-equiv*)
        (and (equal goal (cons *h4-book-agreement-equiv* (cdr guard)))
             (h4-book-agreement-list-spine-equivalence p formula)))
       ((proof-is-call guard *h4-book-agreement-equiv*)
        (proof-with-checked-results
            ((assumed (proof-proof-assume (library-library-proof p) guard t))
             (consequence (h4-book-agreement-same-lookup-consequences p formula assumed)))
          (or consequence (h4-book-agreement-alist-congruence p formula))))
       ((proof-is-call guard *proof-if*)
        (h4-book-agreement-from-agreement p formula))
       ((proof-is-call guard *proof-not*)
        (h4-book-agreement-lookup-absence p formula guard goal))
       ((proof-is-call guard *h4-book-agreement-lookup*)
        (proof-with-checked-results ((alist (proof-term-at guard 2)))
          (and (equal goal (list *h4-book-agreement-member* (list *library-cdr* guard)
                                 (list *h4-book-projections-values* alist)))
               (h4-book-agreement-member-after-lookup p formula))))
       (t (h4-book-agreement-witness-consequences p formula guard goal choices))))))

(defun h4-book-agreement-agreement-proof-with-choices (p formula choices)
  (cond
   ((proof-is-call formula *h4-book-agreement-iff*)
    (h4-book-agreement-witness-equivalence p formula choices))
   ((proof-is-call formula *proof-if*)
    (proof-with-checked-results ((test (proof-term-at formula 1)))
      (and (proof-is-call test *h4-book-sets-boolean*)
           (proof-with-checked-results ((relation (proof-term-at test 1)))
             (and (proof-is-call relation *h4-book-agreement-equiv*)
                  (h4-book-agreement-equivalence-laws p))))))
   ((proof-is-call formula *library-implies*)
    (h4-book-agreement-agreement-implication p formula choices))
   (t nil)))

(defun h4-book-agreement-agreement-proof (p formula)
  (h4-book-agreement-agreement-proof-with-choices p formula nil))
