(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-printing-characterp* (proof-cl "CHARACTERP"))
(defconst *b1-printing-coerce* (proof-cl "COERCE"))
(defconst *b1-printing-realpart* (proof-cl "REALPART"))
(defconst *b1-printing-imagpart* (proof-cl "IMAGPART"))
(defconst *b1-printing-null* (proof-cl "NULL"))
(defconst *b1-printing-characters* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *b1-printing-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *b1-printing-digit* (proof-sym "DIGIT-TO-CHAR" "ACL2"))
(defconst *b1-printing-print-base* (proof-sym "PRINT-BASE-P" "ACL2"))
(defconst *b1-printing-explode-integer*
  (proof-sym "EXPLODE-NONNEGATIVE-INTEGER" "ACL2"))
(defconst *b1-printing-explode-atom* (proof-sym "EXPLODE-ATOM" "ACL2"))
(defconst *b1-printing-pack-list* (proof-sym "PACK-LIST" "ACL2"))
(defconst *b1-printing-pack-tree* (proof-sym "PACK-TREE" "ACL2"))
(defconst *b1-printing-base* (proof-sym "PRINT-BASE" "ACL2"))
(defconst *b1-printing-ans* (proof-sym "ANS" "ACL2"))
(defconst *b1-printing-n* (proof-sym "N" "ACL2"))

(defun b1-printing-character-constant (lib term)
  (if (proof-is-call term *b1-printing-characterp*)
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (if (proof-is-call argument *proof-quote*)
            (proof-with-checked-results ((datum (proof-term-at argument 1)))
              (proof-proof-compute
               (library-library-proof lib) term
               (if (and (consp datum) (equal (car datum) "char"))
                   *proof-t*
                 *proof-nil*)))
          nil))
    nil))

(defun b1-printing-known-character-found (term lib)
  (b1-printing-character-constant lib term))

(defun b1-printing-character-list-quoted-chars (call lib)
  (if (proof-is-call call *b1-printing-characters*)
      (proof-with-checked-results ((items (proof-term-at call 1)))
        (if (proof-is-call items *proof-quote*)
            (proof-proof-unfold (library-library-proof lib) call)
          nil))
    nil))

(defun b1-printing-print-base-bound-open-membership (term lib)
  (if (proof-is-call term *b1-revappend-member*)
      (proof-with-checked-results ((items (proof-term-at term 2)))
        (if (proof-is-call items *proof-quote*)
            (proof-proof-unfold (library-library-proof lib) term)
          nil))
    nil))

(defun b1-printing-normalize-rule (lib id term)
  (case id
    (:quoted-chars (b1-printing-character-list-quoted-chars term lib))
    (:open-membership (b1-printing-print-base-bound-open-membership term lib))
    (otherwise (b1-printing-known-character-found term lib))))

(defun b1-printing-normalize-request (lib term evidence unfold rules provep replies)
  (if provep
      (b1-logic-bookproof-normalize-proof-with-library
       lib term evidence unfold rules nil replies)
    (b1-logic-bookproof-normalize-with-library
     lib term evidence unfold rules nil nil nil replies)))

(defun b1-printing-normalize-replies (n lib term evidence unfold rules provep replies result)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "b1-printing-normalize-replies"))
   ((failure-p result) result)
   ((b1-logic-call-p result)
    (let* ((current (b1-logic-call-library result))
           (step (b1-printing-normalize-rule current (b1-logic-call-id result)
                                             (b1-logic-call-term result)))
           (reply (if (failure-p step) step (cons step current)))
           (replies (append replies (list reply))))
      (b1-printing-normalize-replies
       (1- n) lib term evidence unfold rules provep replies
       (b1-printing-normalize-request lib term evidence unfold rules provep replies))))
   (t (car result))))

(defun b1-printing-normalize-with-rules (lib term evidence unfold rules provep)
  (b1-printing-normalize-replies
   1000000 lib term evidence unfold rules provep nil
   (b1-printing-normalize-request lib term evidence unfold rules provep nil)))

(defmacro b1-printing-normalize (lib term evidence unfold)
  `(b1-logic-bookproof-normalize ,lib ,term ,evidence ,unfold nil nil nil nil))

(defmacro b1-printing-normalize-proof (lib goal evidence)
  `(b1-logic-bookproof-normalize-proof ,lib ,goal ,evidence nil nil nil))

(defun b1-printing-by-value-rewrite (lib step equality template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((back (proof-proof-symmetric proof equality)))
      (proof-proof-rewrite-result proof step back template *proof-result*))))

; Each pending frame records how a result is used after its branch is proved.
(defun b1-printing-by-value-visit (lib value tests pending)
  (cond
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
      (let ((test (car branches)))
        (list :visit lib (cadr branches) (append tests (list (list test t)))
              (cons (list :yes value test (caddr branches) tests) pending)))))
   ((and (proof-compound value) (endp value))
    '(:failure "failure" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta (library-library-proof lib) value))
         (opened (proof-rewritten-term equality)))
      (list :visit lib opened tests (cons (list :beta equality) pending))))
   (t (list :leaf lib value tests pending))))

(defun b1-printing-by-value-return (lib step pending template)
  (if (endp pending)
      (list :done (cons step lib))
    (let ((frame (car pending))
          (pending (cdr pending))
          (proof (library-library-proof lib)))
      (case (car frame)
        (:beta
         (proof-with-checked-results
             ((step (b1-printing-by-value-rewrite lib step (cadr frame) template)))
           (list :return lib step nil pending)))
        (:yes
         (let ((value (cadr frame))
               (test (caddr frame))
               (no (cadddr frame))
               (tests (nth 4 frame)))
           (list :visit lib no (append tests (list (list test nil)))
                 (cons (list :no value test step) pending))))
        (otherwise
         (let ((value (cadr frame))
               (test (caddr frame)))
           (proof-with-checked-results
               ((true-eq (proof-proof-if-true proof value))
                (yes (b1-printing-by-value-rewrite lib (cadddr frame) true-eq template))
                (false-eq (proof-proof-if-false proof value))
                (no (b1-printing-by-value-rewrite lib step false-eq template))
                (step (proof-proof-cases proof test yes no)))
             (list :return lib step nil pending))))))))

(defun b1-printing-by-value-check-leaf (result value template pending)
  (proof-with-checked-results
      ((result result)
       (literal (proof-step-first (car result)))
       (claim (proof-subst template (list (cons *proof-result* value)))))
    (if (equal literal claim)
        (list :return (cdr result) (car result) nil pending)
      '(:failure "failure" ""))))

(defmacro b1-printing-by-value-next (cursor template leaf)
  `(case (car ,cursor)
     (:visit (b1-printing-by-value-visit (cadr ,cursor) (caddr ,cursor)
                                       (cadddr ,cursor) (nth 4 ,cursor)))
     (:leaf (b1-printing-by-value-check-leaf ,leaf (caddr ,cursor)
                                            ,template (nth 4 ,cursor)))
     (otherwise (b1-printing-by-value-return (cadr ,cursor) (caddr ,cursor)
                                             (nth 4 ,cursor) ,template))))

(defun b1-printing-known-character-paths (n cursor template)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p cursor) cursor)
   ((zp n) '(:failure "fuel" "b1-printing-known-character-paths"))
   ((eq (car cursor) :done) (cadr cursor))
   (t
    (let ((lib (cadr cursor))
          (value (caddr cursor)))
      (b1-printing-known-character-paths
       (1- n)
       (b1-printing-by-value-next
        cursor template
        (proof-with-checked-results
            ((step (b1-printing-normalize-with-rules
                    lib (list *b1-printing-characterp* value)
                    nil nil '((:callback :character-constant)) t)))
          (cons step lib)))
       template)))))

(defun b1-printing-known-character-lemma (lib)
  (let* ((call (list *b1-printing-digit* *b1-printing-n*))
         (template (list *b1-printing-characterp* *proof-result*))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((view (proof-proof-unfold proof call))
         (value (proof-rewritten-term view))
         (proved (b1-printing-known-character-paths
                  1000000 (list :visit lib value nil nil) template))
         (step (b1-printing-by-value-rewrite (cdr proved) (car proved) view template)))
      (library-library-lemma (cdr proved) "DIGIT-TO-CHAR-TYPE"
                             (list *b1-printing-characterp* call) step nil))))

(defun b1-printing-known-character (lib value evidence)
  (if (proof-is-call value *b1-printing-digit*)
      (let ((name (proof-sym "SELF-DIGIT-TO-CHAR-TYPE" "ACL2")))
        (proof-with-checked-results
            ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                      lib
                    (b1-printing-known-character-lemma lib)))
             (argument (proof-term-at value 1))
             (step (proof-proof-fact (library-library-proof lib) name
                                     (list (list *b1-printing-n* argument)))))
          (cons step lib)))
    (proof-with-checked-results
        ((step (b1-printing-normalize-with-rules
                lib (list *b1-printing-characterp* value) evidence nil
                '((:callback :character-constant)) t)))
      (cons step lib))))

(defun b1-printing-proper-character-list-base-consequence (premise lib source proper atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib source (list atom)))
         (empty (proof-proof-rewrite proof premise opened '(1)))
         (target (b1-printing-normalize
                  lib proper (list atom) (list *b1-printing-true-listp* *b1-logic-eq*))))
      (proof-proof-transport proof empty target))))

(defun b1-printing-proper-character-list-base (atom lib source proper formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-printing-proper-character-list-base-consequence
                     premise lib source proper atom)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-printing-proper-character-list-step-consequence (premise lib source proper cons-step induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib source (list cons-step)))
         (rewritten (proof-proof-rewrite proof premise opened '(1)))
         (split (proof-proof-conjunct proof rewritten))
         (child (proof-proof-modus-ponens proof induction (cadr split)))
         (target (b1-revappend-open-list lib proper (list cons-step))))
      (proof-proof-transport proof child target))))

(defun b1-printing-proper-character-list-step (cons-step induction lib source proper formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-printing-proper-character-list-step-consequence
                     premise lib source proper cons-step induction)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-printing-proper-character-list-lemma (lib)
  (let* ((source (list *b1-printing-characters* *library-x*))
         (proper (list *b1-printing-true-listp* *library-x*))
         (formula (list *library-implies* source proper)))
    (proof-with-checked-results
        ((preparation (b1-revappend-list-induction-prepare lib formula *library-x* nil))
         (step (b1-printing-proper-character-list-step
                (caddr preparation) (cadddr preparation) lib source proper formula))
         (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
         (base (b1-printing-proper-character-list-base atom lib source proper formula))
         (proof (b1-revappend-list-induction lib preparation base step)))
      (library-library-lemma lib "CHARACTER-LIST-IS-PROPER" formula proof nil))))

(defun b1-printing-proper-character-list (lib known)
  (let ((name (proof-sym "SELF-CHARACTER-LIST-IS-PROPER" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-printing-proper-character-list-lemma lib)))
         (proof (library-library-proof lib))
         (claim (proof-step-first known))
         (subject (proof-term-at claim 1))
         (law (proof-proof-fact proof name (list (list *library-x* subject))))
         (step (proof-proof-modus-ponens proof law known)))
      (cons step lib))))

(defun b1-printing-character-list-evidence (goal evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car evidence))))
      (if (equal literal goal)
          (car evidence)
        (b1-printing-character-list-evidence goal (cdr evidence))))))

(defun b1-printing-character-list-append (lib goal first second)
  (proof-with-checked-results
      ((proper (b1-printing-proper-character-list lib first))
       (lib (cdr proper))
       (first-claim (proof-step-first first))
       (second-claim (proof-step-first second))
       (proper-claim (proof-step-first (car proper))))
    (let ((result (proof-eq goal (proof-ite first-claim second-claim *proof-false*)))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((law (b1-logic-bookproof-from-fact
                 lib (proof-sym "CHARACTER-LISTP-APPEND" "ACL2")
                 (list *library-implies* proper-claim result)))
           (both (b1-printing-normalize-proof lib (caddr result) (list first second)))
           (equality (proof-proof-modus-ponens proof law (car proper)))
           (step (proof-proof-transport proof both equality)))
        (cons step lib)))))

(defun b1-printing-character-list-visit (lib term evidence pending)
  (let ((goal (list *b1-printing-characters* term)))
    (proof-with-checked-results ((known (b1-printing-character-list-evidence goal evidence)))
      (cond
       (known (list :return (cons known lib) pending))
       ((proof-is-call term *proof-cons*)
        (proof-with-checked-results
            ((argument (proof-term-at term 1))
             (head (b1-printing-known-character lib argument evidence)))
          (if (endp (cddr term))
              '(:failure "failure" "")
            (list :visit (cdr head) (caddr term) (cons (list :cons goal (car head)) pending)))))
       ((proof-is-call term *b1-revappend-append*)
        (if (endp (cdr term))
            '(:failure "failure" "")
          (list :visit lib (cadr term) (cons (list :append-first term) pending))))
       ((proof-is-call term *b1-printing-coerce*)
        (proof-with-checked-results
            ((step (b1-logic-bookproof-from-fact
                    lib (proof-sym "CHARACTER-LISTP-COERCE" "ACL2") goal)))
          (list :return (cons step lib) pending)))
       (t
        (proof-with-checked-results
            ((step (b1-printing-normalize-with-rules
                    lib goal evidence (list *b1-logic-atom* *proof-not*)
                    '((:callback :quoted-chars) (:callback :character-constant)) t)))
          (list :return (cons step lib) pending)))))))

; The pending frames preserve the order in which the list arguments are proved.
(defun b1-printing-character-list-return (result pending)
  (if (endp pending)
      (list :done result)
    (let ((frame (car pending))
          (pending (cdr pending))
          (lib (cdr result))
          (step (car result)))
      (case (car frame)
        (:cons
         (proof-with-checked-results
             ((opened (b1-revappend-open-list lib (cadr frame) (list (caddr frame))))
              (step (proof-proof-transport (library-library-proof lib) step opened)))
           (list :return (cons step lib) pending)))
        (:append-first
         (let ((term (cadr frame)))
           (if (endp (cddr term))
               '(:failure "failure" "")
             (list :visit lib (caddr term) (cons (list :append-second term step) pending)))))
        (:append-second
         (let ((term (cadr frame)))
           (if (endp (cdddr term))
               (proof-with-checked-results
                   ((result (b1-printing-character-list-append
                             lib (list *b1-printing-characters* term) (caddr frame) step)))
                 (list :return result pending))
             (list :visit lib (cadddr term) (cons '(:append-extra) pending)))))
        (otherwise '(:failure "failure" ""))))))

(defun b1-printing-character-list-run (n cursor evidence)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p cursor) cursor)
   ((zp n) '(:failure "fuel" "b1-printing-character-list-run"))
   ((eq (car cursor) :done) (cadr cursor))
   (t
    (b1-printing-character-list-run
     (1- n)
     (if (eq (car cursor) :visit)
         (b1-printing-character-list-visit (cadr cursor) (caddr cursor) evidence (cadddr cursor))
       (b1-printing-character-list-return (cadr cursor) (caddr cursor)))
     evidence))))

(defun b1-printing-character-list (lib term evidence)
  (b1-printing-character-list-run 1000000 (list :visit lib term nil) evidence))

(defun b1-printing-print-base-bound-candidate (lib candidates base conclusion)
  (if (endp candidates)
      nil
    (let* ((proof (library-library-proof lib))
           (value (proof-quote (car candidates)))
           (test (proof-eq base value)))
      (proof-with-checked-results
          ((assumed (proof-proof-assume proof test t))
           (back (proof-proof-symmetric proof assumed))
           (typed (library-library-type-of lib value nil))
           (typed (proof-proof-rewrite proof typed back '(1 1)))
           (bound (proof-proof-prove proof (library-lt *proof-one* value) nil nil))
           (bound (proof-proof-rewrite proof bound back '(1 2)))
           (yes (b1-printing-normalize-proof lib conclusion (list typed bound)))
           (negative (proof-proof-assume proof test nil)))
        (list test yes negative)))))

(defun b1-printing-print-base-bound-search-visit
    (candidates missed lib known view base conclusion candidate)
  (declare (xargs :measure (acl2-count candidates)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((failure-p candidate) candidate)
     ((endp candidates)
      (proof-with-checked-results
          ((opened (proof-rewritten-term view))
           (reduction (b1-printing-normalize-with-rules
                       lib opened missed
                       (list *b1-logic-endp* *b1-logic-atom* *proof-not*)
                       '((:callback :open-membership)) nil))
           (equation (proof-proof-chain proof view (list reduction)))
           (impossible (proof-proof-rewrite proof known equation '(1)))
           (not-nil (b1-logic-proof-not-nil proof)))
        (b1-logic-bookproof-contradiction lib impossible not-nil conclusion)))
     (t
      (let ((remaining (cdr candidates)))
        (proof-with-checked-results
            ((no (b1-printing-print-base-bound-search-visit
                  remaining (append missed (list (caddr candidate))) lib known view base conclusion
                  (b1-printing-print-base-bound-candidate lib remaining base conclusion))))
          (proof-proof-cases proof (car candidate) (cadr candidate) no)))))))

(defun b1-printing-print-base-bound-search (candidates missed lib known view base conclusion)
  (b1-printing-print-base-bound-search-visit
   candidates missed lib known view base conclusion
   (b1-printing-print-base-bound-candidate lib candidates base conclusion)))

(defun b1-printing-print-base-bound (lib known)
  (proof-with-checked-results
      ((claim (proof-step-first known))
       (base (proof-term-at claim 1))
       (view (b1-printing-normalize lib claim nil (list *b1-printing-print-base*)))
       (opened (proof-rewritten-term view))
       (test (proof-term-at opened 1))
       (members (proof-term-at test 2))
       (candidates (proof-term-at members 1))
       (conclusion (proof-ite (library-integer base)
                             (library-lt *proof-one* base) *proof-false*))
       (cases (b1-printing-print-base-bound-search
               candidates nil lib known view base conclusion)))
    (proof-proof-conjunct (library-library-proof lib) cases)))

(defun b1-printing-floor-by-larger-base-cases
    (lib n base denominator numerator natural-num bound less natural-q types)
  (let* ((proof (library-library-proof lib))
         (floor-term (list *b1-quotient-floor* n base))
         (unit-test (proof-eq denominator *proof-one*))
         (unfold (list *b1-quotient-floor* *b1-quotient-numeric-eq*
                       *b1-logic-eql* *proof-not*)))
    (proof-with-checked-results
        ((lower-num (library-library-cite lib "NATURAL-NONNEGATIVE"
                                         (list numerator) (list natural-num)))
         (unit (proof-proof-assume proof unit-test t))
         (numeral (proof-proof-rewrite proof bound unit '(1 2 1)))
         (identity (b1-arithmetic-multiply-one lib n types t))
         (numeral (proof-proof-rewrite proof numeral identity '(1 2)))
         (yes (b1-printing-normalize lib floor-term (list lower-num unit) unfold))
         (nonunit (proof-proof-assume proof unit-test nil))
         (no (b1-printing-normalize lib floor-term (list lower-num nonunit) unfold))
         (yes-strict (library-library-transport-argument lib numeral yes 1))
         (no-strict (library-library-transport-argument lib less no 1))
         (strict (proof-proof-cases proof unit-test yes-strict no-strict))
         (yes-natural (library-library-transport-argument lib natural-num yes 1))
         (no-natural (library-library-transport-argument lib natural-q no 1))
         (natural (proof-proof-cases proof unit-test yes-natural no-natural)))
      (cons (list strict natural) lib))))

(defun b1-printing-floor-by-larger-base (lib int-n pos-n int-base above-one)
  (proof-with-checked-results
      ((int-n-claim (proof-step-first int-n))
       (n (proof-term-at int-n-claim 1))
       (int-base-claim (proof-step-first int-base))
       (base (proof-term-at int-base-claim 1))
       (inv (b1-arithmetic-reciprocal base))
       (types (list int-n int-base))
       (int-zero (library-library-type-of lib *proof-zero* nil))
       (int-one (library-library-type-of lib *proof-one* nil))
       (pos-one (proof-proof-prove (library-library-proof lib)
                                   (library-positive *proof-one*) nil nil))
       (base-pos (library-library-cite lib "LESS-TRANSITIVE"
                                       (list *proof-zero* *proof-one* base)
                                       (list int-zero int-one int-base pos-one above-one)))
       (base-rational (b1-arithmetic-known-type lib *library-rationalp* base types))
       (inv-result (b1-arithmetic-positive-reciprocal lib base-pos base-rational))
       (lib (cdr inv-result))
       (inv-pos (car inv-result))
       (base-numeric (b1-arithmetic-known-type lib *library-numberp* base types))
       (nonzero (b1-arithmetic-positive-nonzero lib base-pos))
       (inverse (b1-arithmetic-inverse-product lib base base-numeric nonzero))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list inv base)))
       (inverse (proof-proof-chain (library-library-proof lib) commuted (list inverse)))
       (inv-bound (b1-arithmetic-multiply-strict lib inv-pos above-one types))
       (lib (cdr inv-bound))
       (proof (library-library-proof lib))
       (identity (b1-arithmetic-multiply-one lib inv types nil))
       (inv-lower (proof-proof-rewrite proof (car inv-bound) identity '(1 1)))
       (inv-lower (proof-proof-rewrite proof inv-lower inverse '(1 2)))
       (ratio-bound (b1-arithmetic-multiply-strict lib pos-n inv-lower types))
       (lib (cdr ratio-bound))
       (proof (library-library-proof lib))
       (identity (b1-arithmetic-multiply-one lib n types nil))
       (ratio-upper (proof-proof-rewrite proof (car ratio-bound) identity '(1 2)))
       (ratio (b1-arithmetic-product n inv))
       (ratio-pos (b1-arithmetic-positive-product lib pos-n inv-pos types))
       (rational (b1-arithmetic-known-type lib *library-rationalp* ratio types))
       (representation (b1-arithmetic-numerator-product lib rational))
       (int-d (car (cadr representation)))
       (int-num (cadr (cadr representation)))
       (pos-d (caddr (cadr representation)))
       (int-d-claim (proof-step-first int-d))
       (denominator (proof-term-at int-d-claim 1))
       (int-num-claim (proof-step-first int-num))
       (numerator (proof-term-at int-num-claim 1))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list denominator ratio)))
       (represented (proof-proof-chain proof commuted (list (car representation))))
       (extended-types (append types (list int-d rational)))
       (num-pos (b1-arithmetic-positive-product lib pos-d ratio-pos extended-types))
       (numerator-positive (proof-proof-rewrite proof num-pos represented '(1 2)))
       (product-bound (b1-arithmetic-multiply-strict lib pos-d ratio-upper extended-types))
       (lib (cdr product-bound))
       (bound (proof-proof-rewrite (library-library-proof lib)
                                   (car product-bound) represented '(1 1)))
       (quotient (b1-quotient-quotient-less
                  lib int-num int-d pos-d numerator-positive int-n bound))
       (lib (cdr quotient))
       (natural-num (b1-quotient-natural-from-positive lib numerator int-num numerator-positive)))
    (b1-printing-floor-by-larger-base-cases
     lib n base denominator numerator natural-num bound (caar quotient) (cadar quotient) types)))

(defun b1-printing-assume-first-test (lib tests)
  (if (endp tests)
      nil
    (proof-proof-assume (library-library-proof lib) (caar tests) (cadar tests))))

(defun b1-printing-assume-tests-visit (lib tests step)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((step step)
         (rest (b1-printing-assume-tests-visit
                lib (cdr tests) (b1-printing-assume-first-test lib (cdr tests)))))
      (cons step rest))))

(defun b1-printing-assume-tests (lib tests)
  (b1-printing-assume-tests-visit lib tests (b1-printing-assume-first-test lib tests)))

(defun b1-printing-explode-atom-chars-leaf (items tests lib)
  (proof-with-checked-results ((evidence (b1-printing-assume-tests lib tests)))
    (b1-printing-character-list lib items evidence)))

(defun b1-printing-character-list-paths (n cursor template evidence signed-tests-p)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p cursor) cursor)
   ((zp n) '(:failure "fuel" "b1-printing-character-list-paths"))
   ((eq (car cursor) :done) (cadr cursor))
   (t
    (let ((lib (cadr cursor))
          (value (caddr cursor)))
      (b1-printing-character-list-paths
       (1- n)
       (b1-printing-by-value-next
        cursor template
        (if signed-tests-p
            (b1-printing-explode-atom-chars-leaf value (cadddr cursor) lib)
          (b1-printing-character-list lib value evidence)))
       template evidence signed-tests-p)))))

(defun b1-printing-explode-integer-chars-consequence
    (premise lib opened opened-term stopper floor-term extended-chars bindings template formula)
  (proof-with-checked-results
      ((proof (library-library-proof lib))
       (if-true (proof-proof-if-true proof opened-term))
       (yes-branch (proof-proof-chain proof opened (list if-true)))
       (yes-value (proof-rewritten-term yes-branch))
       (yes-result (b1-printing-character-list-paths
                    1000000 (list :visit lib yes-value nil nil) template (list premise) nil))
       (lib (cdr yes-result))
       (proof (library-library-proof lib))
       (yes (library-library-transport-argument lib (car yes-result) yes-branch 1))
       (not-done (proof-proof-assume proof stopper nil))
       (zp-test (list *b1-logic-zp* *b1-printing-n*))
       (printed (list *b1-printing-print-base* *b1-printing-base*))
       (at-zero (proof-proof-assume proof zp-test t))
       (wrong-base (proof-proof-assume proof printed nil))
       (selection (proof-proof-select proof stopper at-zero))
       (stopped (proof-proof-transport proof at-zero selection))
       (cut (proof-proof-cut proof stopped not-done))
       (not-zp (proof-proof-front proof cut (proof-neg zp-test)))
       (selection (proof-proof-select proof stopper not-zp))
       (stopped (proof-proof-transport proof wrong-base selection))
       (cut (proof-proof-cut proof stopped not-done))
       (base-known (proof-proof-front proof cut printed))
       (int-n (b1-logic-bookproof-forces
               lib (library-integer *b1-printing-n*) not-zp nil
               (list *b1-logic-zp* *proof-not*) nil))
       (pos-n (b1-integer-no-zp lib *b1-printing-n* not-zp int-n))
       (bases (b1-printing-print-base-bound lib base-known))
       (bounds (b1-printing-floor-by-larger-base lib int-n pos-n (car bases) (cadr bases)))
       (lib (cdr bounds))
       (proof (library-library-proof lib))
       (less (caar bounds))
       (floor-nat (cadar bounds))
       (int-floor (library-library-cite lib "NATURAL-INTEGER" (list floor-term)
                                       (list floor-nat)))
       (decrease (library-library-cite lib "NFIX-DECREASE" (list floor-term *b1-printing-n*)
                                      (list int-floor int-n pos-n less)))
       (child (proof-subst formula bindings))
       (decrease-claim (proof-step-first decrease))
       (assumed (proof-proof-assume proof (proof-ite decrease-claim child *proof-true*) t))
       (hyp (proof-proof-prove-if proof assumed decrease))
       (expanded (b1-printing-character-list lib extended-chars (list premise)))
       (lib (cdr expanded))
       (proof (library-library-proof lib))
       (result (proof-proof-modus-ponens proof hyp (car expanded)))
       (if-false (proof-proof-if-false proof opened-term))
       (no-branch (proof-proof-chain proof opened (list if-false)))
       (no (library-library-transport-argument lib result no-branch 1))
       (step (proof-proof-cases proof stopper yes no)))
    (cons step lib)))

(defun b1-printing-explode-integer-chars-lemma (lib)
  (let* ((call (list *b1-printing-explode-integer* *b1-printing-n*
                     *b1-printing-base* *b1-printing-ans*))
         (goal (list *b1-printing-characters* call))
         (formula (list *library-implies* (list *b1-printing-characters* *b1-printing-ans*) goal))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (opened-term (proof-rewritten-term opened))
         (stopper (proof-term-at opened-term 1))
         (next-call (proof-term-at opened-term 3))
         (actuals (if (integerp next-call)
                      '(:failure "failure" "")
                    (proof-list-of-length (cdr next-call) 3)))
         (floor-term (car actuals))
         (extended-chars (caddr actuals))
         (bindings (list (cons *b1-printing-n* floor-term)
                         (cons *b1-printing-ans* extended-chars)))
         (template (list *b1-printing-characters* *proof-result*))
         (ordinal (library-library-cite lib "NFIX-ORDINAL" (list *b1-printing-n*) nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-printing-explode-integer-chars-consequence
                       premise lib opened opened-term stopper floor-term extended-chars
                       bindings template formula))
         (lib (cdr consequence))
         (case-step (b1-logic-bookproof-prove-implication-with-premise
                     lib formula premise (car consequence)))
         (induction (proof-proof-induct (library-library-proof lib) ordinal case-step formula
                                       (list *library-nfix* *b1-printing-n*)
                                       (list (table-items bindings)))))
      (library-library-lemma lib "EXPLODE-INTEGER-CHARACTERS" formula induction nil))))

(defun b1-printing-explode-integer-chars (lib term accumulator-type)
  (let ((name (proof-sym "SELF-EXPLODE-INTEGER-CHARACTERS" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-printing-explode-integer-chars-lemma lib)))
         (proof (library-library-proof lib))
         (actuals (if (integerp term)
                      '(:failure "failure" "")
                    (cdr term)))
         (law (proof-proof-fact proof name
                                (seq-zip (list *b1-printing-n* *b1-printing-base* *b1-printing-ans*)
                                        actuals)))
         (step (proof-proof-modus-ponens proof law accumulator-type)))
      (cons step lib))))

(defun b1-printing-printable-integer-leaf (term tests lib empty)
  (declare (ignore tests))
  (if (proof-is-call term *proof-cons*)
      (proof-with-checked-results
          ((argument (proof-term-at term 2))
           (tail (b1-printing-explode-integer-chars lib argument empty)))
        (b1-printing-character-list (cdr tail) term (list (car tail))))
    (b1-printing-explode-integer-chars lib term empty)))

(defun b1-printing-printable-integer-paths (n cursor template empty)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p cursor) cursor)
   ((zp n) '(:failure "fuel" "b1-printing-printable-integer-paths"))
   ((eq (car cursor) :done) (cadr cursor))
   (t
    (b1-printing-printable-integer-paths
     (1- n)
     (b1-printing-by-value-next
      cursor template
      (b1-printing-printable-integer-leaf (caddr cursor) (cadddr cursor) (cadr cursor) empty))
     template empty))))

(defun b1-printing-printable-integer (lib call integral)
  (proof-with-checked-results
      ((parts (proof-list-of-length call 3))
       (rational (b1-arithmetic-known-type lib *library-rationalp* (cadr parts) (list integral)))
       (opened (b1-printing-normalize
                lib call (list rational integral) (list *b1-printing-explode-atom*)))
       (template (list *b1-printing-characters* *proof-result*))
       (empty (b1-printing-character-list lib *proof-false* nil))
       (value (proof-rewritten-term opened))
       (result (b1-printing-printable-integer-paths
                1000000 (list :visit (cdr empty) value nil nil) template (car empty)))
       (lib (cdr result))
       (step (library-library-transport-argument lib (car result) opened 1)))
    (cons step lib)))

(defun b1-printing-printable-rational (lib call rational)
  (proof-with-checked-results
      ((actuals (if (integerp call)
                    '(:failure "failure" "")
                  (proof-list-of-length (cdr call) 2)))
       (number (car actuals))
       (test (library-integer number))
       (integral (proof-proof-assume (library-library-proof lib) test t))
       (yes (b1-printing-printable-integer lib call integral))
       (lib (cdr yes))
       (proof (library-library-proof lib))
       (not-int (proof-proof-assume proof test nil))
       (branch (b1-printing-normalize
                lib call (list rational not-int) (list *b1-printing-explode-atom*)))
       (axiom (library-library-axiom lib "RATIONAL-IMPLIES1" (list number)))
       (typed (proof-proof-modus-ponens proof axiom rational))
       (types (b1-logic-bookproof-split-conjuncts lib typed))
       (types (proof-list-of-length types 3))
       (int-num (cadr types))
       (value (proof-rewritten-term branch))
       (parts (if (integerp value)
                  '(:failure "failure" "")
                (proof-list-of-length (cdr value) 2)))
       (numerator (b1-printing-printable-integer lib (car parts) int-num))
       (argument (proof-term-at (cadr parts) 2))
       (empty (b1-printing-character-list (cdr numerator) *proof-false* nil))
       (denominator (b1-printing-explode-integer-chars (cdr empty) argument (car empty)))
       (result (b1-printing-character-list (cdr denominator) value
                                           (list (car numerator) (car denominator))))
       (lib (cdr result))
       (no (library-library-transport-argument lib (car result) branch 1))
       (step (proof-proof-cases (library-library-proof lib) test (car yes) no)))
    (cons step lib)))

(defun b1-printing-explode-atom-chars-lemma (lib)
  (let* ((term (list *b1-printing-explode-atom* *library-x* *b1-printing-base*))
         (rat-test (list *library-rationalp* *library-x*))
         (complex-test (list (proof-sym "COMPLEX-RATIONALP" "ACL2") *library-x*))
         (proof (library-library-proof lib))
         (unfold (list *b1-printing-explode-atom*)))
    (proof-with-checked-results
        ((rational (proof-proof-assume proof rat-test t))
         (other (proof-proof-assume proof rat-test nil))
         (is-complex (proof-proof-assume proof complex-test t))
         (noncomplex (proof-proof-assume proof complex-test nil))
         (yes (b1-printing-printable-rational lib term rational))
         (lib (cdr yes))
         (axiom (library-library-axiom lib "COMPLEX-IMPLIES1" (list *library-x*)))
         (types (b1-logic-bookproof-split-conjuncts lib axiom))
         (types (proof-list-of-length (seq-slice types 0 2) 2))
         (real (b1-printing-printable-rational
                lib (list *b1-printing-explode-atom*
                          (list *b1-printing-realpart* *library-x*) *b1-printing-base*)
                (car types)))
         (imaginary (b1-printing-printable-rational
                     (cdr real) (list *b1-printing-explode-atom*
                                      (list *b1-printing-imagpart* *library-x*) *b1-printing-base*)
                     (cadr types)))
         (lib (cdr imaginary))
         (opened (b1-printing-normalize lib term (list other is-complex) unfold))
         (value (proof-rewritten-term opened))
         (contents (b1-printing-character-list lib value (list (car real) (car imaginary))))
         (lib (cdr contents))
         (complex-branch (library-library-transport-argument lib (car contents) opened 1))
         (opened (b1-printing-normalize lib term (list other noncomplex) unfold))
         (value (proof-rewritten-term opened))
         (template (list *b1-printing-characters* *proof-result*))
         (other-result (b1-printing-character-list-paths
                        1000000 (list :visit lib value nil nil) template nil t))
         (lib (cdr other-result))
         (proof (library-library-proof lib))
         (other-branch (library-library-transport-argument lib (car other-result) opened 1))
         (not-rational (proof-proof-cases proof complex-test complex-branch other-branch))
         (step (proof-proof-cases proof rat-test (car yes) not-rational)))
      (library-library-lemma lib "EXPLODE-ATOM-CHARACTERS"
                             (list *b1-printing-characters* term) step nil))))

(defun b1-printing-explode-atom-chars (lib call)
  (let ((name (proof-sym "SELF-EXPLODE-ATOM-CHARACTERS" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-printing-explode-atom-chars-lemma lib)))
         (value (proof-term-at call 1))
         (base (proof-term-at call 2))
         (step (proof-proof-fact (library-library-proof lib) name
                                 (list (list *library-x* value)
                                       (list *b1-printing-base* base)))))
      (cons step lib))))

(defun b1-printing-pack-character-lists-proof-typed-leaf (items tests lib evidence)
  (declare (ignore tests))
  (if (proof-is-call items *b1-printing-explode-atom*)
      (b1-printing-explode-atom-chars lib items)
    (b1-printing-character-list lib items evidence)))

(defun b1-printing-pack-character-lists-paths (n cursor template evidence)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p cursor) cursor)
   ((zp n) '(:failure "fuel" "b1-printing-pack-character-lists-paths"))
   ((eq (car cursor) :done) (cadr cursor))
   (t
    (b1-printing-pack-character-lists-paths
     (1- n)
     (b1-printing-by-value-next
      cursor template
      (b1-printing-pack-character-lists-proof-typed-leaf
       (caddr cursor) (cadddr cursor) (cadr cursor) evidence))
     template evidence))))

(defun b1-printing-pack-character-lists-proof-typed (call lib cell evidence template)
  (proof-with-checked-results
      ((view (b1-revappend-open-list lib call (list cell)))
       (value (proof-rewritten-term view))
       (result (b1-printing-pack-character-lists-paths
                1000000 (list :visit lib value nil nil) template evidence))
       (lib (cdr result))
       (step (library-library-transport-argument lib (car result) view 1)))
    (cons step lib)))

(defun b1-printing-pack-character-lists-proof (cell evidence lib calls combined template)
  (proof-with-checked-results
      ((first (b1-printing-pack-character-lists-proof-typed
               (car calls) lib cell evidence template))
       (second (b1-printing-pack-character-lists-proof-typed
                (cadr calls) (cdr first) cell evidence template))
       (lib (cdr second))
       (step (b1-printing-normalize-proof lib combined (list (car first) (car second)))))
    (cons step lib)))

(defun b1-printing-pack-character-lists-lemma (lib)
  (let* ((calls (list (list *b1-printing-pack-list* *library-x*)
                      (list *b1-printing-pack-tree* *library-x*)))
         (combined (proof-ite (list *b1-printing-characters* (car calls))
                              (list *b1-printing-characters* (cadr calls))
                              *proof-false*))
         (induction (b1-induction-tree-induction-init lib combined *library-x*))
         (test (list *proof-consp* *library-x*))
         (proof (library-library-proof lib))
         (tests (list (list test t))))
    (proof-with-checked-results
        ((cons-step (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (head (b1-induction-tree-induction-hypothesis
                induction (list (cons *library-x* (list *library-car* *library-x*))) tests))
         (tail (b1-induction-tree-induction-hypothesis
                (cdr head) (list (cons *library-x* (list *library-cdr* *library-x*))) tests))
         (head-types (proof-proof-conjunct proof (car head)))
         (tail-types (proof-proof-conjunct proof (car tail)))
         (children (append head-types tail-types))
         (template (list *b1-printing-characters* *proof-result*))
         (yes (b1-printing-pack-character-lists-proof cons-step children lib calls combined template))
         (no (b1-printing-pack-character-lists-proof atom nil (cdr yes) calls combined template))
         (lib (cdr no))
         (cases (proof-proof-cases (library-library-proof lib) test (car yes) (car no)))
         (induction (b1-induction-tree-induction-with-lib (cdr tail) lib))
         (result (b1-induction-tree-induction-finish induction cases)))
      (library-library-lemma lib "PACK-CHARACTER-LISTS" combined result nil))))

(defun b1-printing-pack-character-lists (lib formula)
  (let ((name (proof-sym "SELF-PACK-CHARACTER-LISTS" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-printing-pack-character-lists-lemma lib)))
         (proof (library-library-proof lib))
         (call (proof-term-at formula 1))
         (argument (proof-term-at call 1))
         (packed (proof-proof-fact proof name (list (list *library-x* argument))))
         (both (proof-proof-conjunct proof packed))
         (head (proof-term-at call 0)))
      (cons (if (equal head *b1-printing-pack-list*) (car both) (cadr both)) lib))))
