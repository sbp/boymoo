(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-printing-character* (proof-cl "CHARACTERP"))
(defconst *h4-book-printing-coerce* (proof-cl "COERCE"))
(defconst *h4-book-printing-list* (proof-cl "LIST"))
(defconst *h4-book-printing-mod* (proof-cl "MOD"))
(defconst *h4-book-printing-rational* (proof-cl "RATIONALP"))
(defconst *h4-book-printing-characters* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *h4-book-printing-true-list* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h4-book-printing-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *h4-book-printing-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h4-book-printing-digit* (proof-sym "DIGIT-TO-CHAR" "ACL2"))
(defconst *h4-book-printing-explode-int* (proof-sym "EXPLODE-NONNEGATIVE-INTEGER" "ACL2"))
(defconst *h4-book-printing-explode-atom* (proof-sym "EXPLODE-ATOM" "ACL2"))
(defconst *h4-book-printing-print-base* (proof-sym "PRINT-BASE-P" "ACL2"))
(defconst *h4-book-printing-pack-list* (proof-sym "PACK-LIST" "ACL2"))
(defconst *h4-book-printing-pack-tree* (proof-sym "PACK-TREE" "ACL2"))
(defconst *h4-book-printing-ten* (proof-quote 10))
(defconst *h4-book-printing-logic*
  (list *proof-not* (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")
        (proof-cl "EQL") (proof-cl "NULL")))
(defconst *h4-book-printing-character-cons* (proof-sym "H4-CHARACTER-LIST-CONS" "ACL2"))
(defconst *h4-book-printing-character-true-list* (proof-sym "H4-CHARACTER-LIST-TRUE-LIST" "ACL2"))
(defconst *h4-book-printing-digit-character* (proof-sym "H4-DIGIT-IS-CHARACTER" "ACL2"))
(defconst *h4-book-printing-decimal-digits* (proof-sym "H4-DECIMAL-DIGITS-ARE-CHARACTERS" "ACL2"))
(defconst *h4-book-printing-decimal-integer* (proof-sym "H4-DECIMAL-INTEGER-IS-CHARACTERS" "ACL2"))
(defconst *h4-book-printing-decimal-rational* (proof-sym "H4-DECIMAL-RATIONAL-IS-CHARACTERS" "ACL2"))
(defconst *h4-book-printing-decimal-atom* (proof-sym "H4-DECIMAL-ATOM-IS-CHARACTERS" "ACL2"))

(defun h4-book-printing-unfold (p call premises)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((first (proof-proof-unfold pr call))
         (right (proof-rewritten-term first))
         (normalized (h4-tactics-tactics-normalize p right premises *h4-book-printing-logic* nil nil)))
      (proof-proof-chain pr first (list normalized)))))

(defun h4-book-printing-character-quotation-p (term)
  (if (proof-is-call term *proof-quote*)
      (proof-with-checked-results ((datum (proof-term-at term 1)))
        (if (or (consp datum) (null datum))
            (proof-with-checked-results ((tag (proof-term-at datum 0)))
              (equal tag "char"))
          nil))
    nil))

(defun h4-book-printing-quoted-character (p term)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results ((quoted (h4-book-printing-character-quotation-p term)))
      (if quoted
          (proof-with-checked-results
              ((equality (proof-proof-compute pr (list *h4-book-printing-character* term) *proof-t*)))
            (h4-tactics-tactics-non-nil p equality))
        '(:failure "failure" "")))))

(defun h4-book-printing-character-of (p term premises)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((given (proof-find-evidence premises (list (list *h4-book-printing-character* term)))))
      (cond (given given)
            ((proof-is-call term *h4-book-printing-digit*)
             (proof-with-checked-results ((argument (proof-term-at term 1)))
               (proof-proof-fact pr *h4-book-printing-digit-character*
                                 (list (list *library-x* argument)))))
            (t (h4-book-printing-quoted-character p term))))))

(defun h4-book-printing-characters-of-primitive (call p)
  (if (proof-is-call call *h4-book-printing-character*)
      (proof-with-checked-results ((argument (proof-term-at call 1)))
        (if (proof-is-call argument *proof-quote*)
            (proof-with-checked-results
                ((datum (proof-term-at argument 1))
                 (tag (proof-term-at datum 0)))
              (if (equal tag "char")
                  (proof-proof-compute (library-library-proof p) call *proof-t*)
                '(:failure "failure" "")))
          '(:failure "failure" "")))
    nil))

(defund h4-book-printing-quoted-characters-step (p target replies)
  (let ((result (h4-tactics-tactics-establish
                 p target nil (append *h4-book-printing-logic* (list *h4-book-printing-characters*))
                 nil (cons :h4-tactics-provider replies))))
    (if (h4-tactics-request-p result)
        (let ((term (h4-tactics-request-term result)))
          (proof-with-checked-results
              ((step (h4-book-printing-characters-of-primitive term p)))
            (cons :h4-book-printing-replies (table-put replies term step))))
      result)))

(defun h4-book-printing-establish-quoted-characters (n p target replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h4-book-printing-establish-quoted-characters")
    (let ((result (h4-book-printing-quoted-characters-step p target replies)))
      (if (eq (car result) :h4-book-printing-replies)
          (h4-book-printing-establish-quoted-characters (1- n) p target (cdr result))
        result))))

(mutual-recursion
 (defun h4-book-printing-characters-of-visit (n p term premises)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "h4-book-printing-characters-of-visit")
     (let ((pr (library-library-proof p))
           (target (list *h4-book-printing-characters* term)))
       (proof-with-checked-results ((given (proof-find-evidence premises (list target))))
         (cond
          (given given)
          ((proof-is-call term *proof-cons*)
           (proof-with-checked-results
               ((arguments (proof-list-of-length (cdr term) 2))
                (head (h4-book-printing-character-of p (car arguments) premises))
                (tail (h4-book-printing-characters-of-visit (1- n) p (cadr arguments) premises)))
             (proof-proof-use pr *h4-book-printing-character-cons*
                              (seq-zip (list *library-x* *library-y*) arguments) (list head tail))))
          ((proof-is-call term *h4-book-printing-append*)
           (proof-with-checked-results
               ((parts (h4-book-printing-characters-of-append-parts (1- n) p (cdr term) premises 3))
                (evidence (proof-list-of-length parts 2))
                (proper (proof-proof-use pr *h4-book-printing-character-true-list*
                                         (list (list *library-x* (cadr term))) (list (car evidence))))
                (append-rule (proof-proof-fact
                              pr (proof-sym "CHARACTER-LISTP-APPEND" "ACL2")
                              (seq-zip (list *library-x* *library-y*) (cdr term))))
                (equality (h4-tactics-tactics-modus-ponens p append-rule proper))
                (conjoined (h4-book-division-conjunction p evidence)))
             (proof-proof-transport pr conjoined equality)))
          ((proof-is-call term *h4-book-printing-explode-int*)
           (proof-with-checked-results ((base (proof-term-at term 2)))
             (if (equal base *h4-book-printing-ten*)
                 (proof-with-checked-results
                     ((accumulator (proof-term-at term 3))
                      (proof (proof-proof-fact pr *h4-book-printing-decimal-digits*
                                               (list (list *library-x* (cadr term))
                                                     (list *library-y* accumulator))))
                      (tail (h4-book-printing-characters-of-visit (1- n) p accumulator premises)))
                   (h4-tactics-tactics-modus-ponens p proof tail))
               '(:failure "failure" ""))))
          ((proof-is-call term *h4-book-printing-explode-atom*)
           (proof-with-checked-results ((base (proof-term-at term 2)))
             (if (and (equal base *h4-book-printing-ten*)
                      (assoc-equal *h4-book-printing-decimal-atom* (proof-proof-facts pr)))
                 (proof-proof-fact pr *h4-book-printing-decimal-atom*
                                   (list (list *library-x* (cadr term))))
               '(:failure "failure" ""))))
          ((proof-is-call term *h4-book-printing-coerce*)
           (proof-with-checked-results ((type (proof-term-at term 2)))
             (if (equal type (proof-quote *h4-book-printing-list*))
                 (proof-proof-fact pr (proof-sym "CHARACTER-LISTP-COERCE" "ACL2")
                                   (list (list (proof-sym "STR" "ACL2") (cadr term))))
               '(:failure "failure" ""))))
          ((proof-is-call term *proof-quote*)
           (h4-book-printing-establish-quoted-characters 1000000 p target nil))
          (t '(:failure "failure" "")))))))

 (defun h4-book-printing-characters-of-append-parts (n p parts premises left)
   (declare (xargs :measure (nfix n)))
   (cond ((or (endp parts) (zp left)) nil)
         ((zp n) '(:failure "Fuel" "h4-book-printing-characters-of-append-parts"))
         (t (proof-with-checked-results
                ((proof (h4-book-printing-characters-of-visit (1- n) p (car parts) premises))
                 (rest (h4-book-printing-characters-of-append-parts
                        (1- n) p (cdr parts) premises (1- left))))
              (cons proof rest))))))

(defun h4-book-printing-characters-of (p term premises)
  (h4-book-printing-characters-of-visit 1000000 p term premises))

(defun h4-book-printing-character-results-assumptions (p tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((step (proof-proof-assume (library-library-proof p) (caar tests) (cadar tests)))
         (rest (h4-book-printing-character-results-assumptions p (cdr tests))))
      (cons step rest))))

(defun h4-book-printing-character-results-leaf (value tests p premises)
  (proof-with-checked-results
      ((assumptions (h4-book-printing-character-results-assumptions p tests)))
    (h4-book-printing-characters-of p value (append premises assumptions))))

(defun h4-book-printing-by-value (n p value template tests premises)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h4-book-printing-by-value")
    (let ((pr (library-library-proof p)))
      (cond
       ((proof-is-call value *proof-if*)
        (proof-with-checked-results
            ((branches (proof-list-of-length (cdr value) 3))
             (yes (h4-book-printing-by-value (1- n) p (cadr branches) template
                                            (append tests (list (list (car branches) t))) premises))
             (no (h4-book-printing-by-value (1- n) p (caddr branches) template
                                           (append tests (list (list (car branches) nil))) premises)))
          (proof-by-value-join pr value template yes no)))
       ((null value) '(:failure "failure" ""))
       ((and (proof-compound value) (proof-compound (car value)))
        (proof-with-checked-results
            ((equality (proof-proof-beta pr value))
             (body (proof-rewritten-term equality))
             (opened (h4-book-printing-by-value (1- n) p body template tests premises))
             (reversed (proof-proof-symmetric pr equality)))
          (proof-proof-rewrite-result pr opened reversed template *proof-result*)))
       (t (proof-with-checked-results
              ((step (if (equal (car template) *h4-book-printing-character*)
                         (h4-book-printing-quoted-character p value)
                       (h4-book-printing-character-results-leaf value tests p premises))))
            (proof-proof-by-value pr value template (list (cons (list value tests) step)) tests)))))))

(defun h4-book-printing-character-results (p equation premises)
  (let ((template (list *h4-book-printing-characters* *proof-result*)))
    (proof-with-checked-results
        ((right (proof-rewritten-term equation))
         (step (h4-book-printing-by-value 1000000 p right template nil premises)))
      (library-library-transport-argument p step equation 1))))

(defun h4-book-printing-character-lemmas-atom (shape p given target)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first given))
         (opened (h4-book-printing-unfold p literal (list shape)))
         (empty (proof-proof-rewrite pr given opened '(1)))
         (equality (h4-book-printing-unfold p target (list shape))))
      (proof-proof-transport pr empty equality))))

(defun h4-book-printing-character-lemmas-cons-list (shape p given goal tail target)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first given))
         (opened (h4-book-printing-unfold p literal (list shape)))
         (rewritten (proof-proof-rewrite pr given opened '(1)))
         (types (h4-tactics-tactics-conjunct p rewritten))
         (builtin (library-library-builtin p 3 *library-x*))
         (descent (proof-proof-discharge pr builtin shape))
         (smaller (proof-step-first descent))
         (claim (proof-subst goal (list (cons *library-x* tail))))
         (assumption (proof-proof-assume pr (proof-ite smaller claim *proof-true*) t))
         (hypothesis (proof-proof-prove-if pr assumption descent))
         (tail-truth (h4-tactics-tactics-modus-ponens p hypothesis (cadr types)))
         (equality (h4-book-printing-unfold p target (list shape))))
      (proof-proof-transport pr tail-truth equality))))

(defun h4-book-printing-character-lemmas (p)
  (let* ((pr (library-library-proof p))
         (x *library-x*) (y *library-y*)
         (cell (list *proof-cons* x y)))
    (proof-with-checked-results
        ((first (proof-proof-assume pr (list *h4-book-printing-character* x) t))
         (rest (proof-proof-assume pr (list *h4-book-printing-characters* y) t))
         (shape (proof-proof-fact pr "consp-cons" nil))
         (car-cons (library-library-axiom p "CAR-CONS" (list x y)))
         (cdr-cons (library-library-axiom p "CDR-CONS" (list x y)))
         (proof (h4-tactics-tactics-establish
                 p (list *h4-book-printing-characters* cell) (list first rest shape)
                 (append *h4-book-printing-logic* (list *h4-book-printing-characters*))
                 (list car-cons cdr-cons) nil))
         (cons-lemma (h4-tactics-tactics-local-lemma p *h4-book-printing-character-cons* proof)))
      (let* ((p (cdr cons-lemma))
             (pr (library-library-proof p))
             (target (list *h4-book-printing-true-list* x))
             (tail (list *library-cdr* x))
             (test (list *proof-consp* x)))
        (proof-with-checked-results
            ((given (proof-proof-assume pr (list *h4-book-printing-characters* x) t))
             (literal (proof-step-first given)))
          (let ((goal (list *library-implies* literal target)))
            (proof-with-checked-results
                ((positive (proof-proof-assume pr test t))
                 (cell-proof (h4-book-printing-character-lemmas-cons-list positive p given goal tail target))
                 (negative (proof-proof-assume pr test nil))
                 (atom-proof (h4-book-printing-character-lemmas-atom negative p given target))
                 (cases (h4-tactics-tactics-case-of p target test cell-proof atom-proof))
                 (ordinal (library-library-builtin p 1 x))
                 (implication (h4-tactics-tactics-imply p goal cases))
                 (proof (proof-proof-induct pr ordinal implication goal (list *library-count* x)
                                           (list (list (list x tail)))))
                 (true-list (h4-tactics-tactics-modus-ponens p proof given))
                 (true-list-lemma (h4-tactics-tactics-local-lemma
                                   p *h4-book-printing-character-true-list* true-list)))
              (let ((p (cdr true-list-lemma))
                    (template (list *h4-book-printing-character* *proof-result*)))
                (proof-with-checked-results
                    ((digits (h4-book-printing-unfold p (list *h4-book-printing-digit* x) nil))
                     (right (proof-rewritten-term digits))
                     (char (h4-book-printing-by-value 1000000 p right template nil nil))
                     (digit-result (library-library-transport-argument p char digits 1))
                     (digit-lemma (h4-tactics-tactics-local-lemma
                                   p *h4-book-printing-digit-character* digit-result)))
                  (cdr digit-lemma))))))))))

(defun h4-book-printing-decimal-digits-stop (test p call good-base accumulator)
  (proof-with-checked-results
      ((equation (h4-book-printing-unfold p call (list test good-base))))
    (h4-book-printing-character-results p equation (list accumulator))))

(defun h4-book-printing-decimal-digits-continue- (test p child goal replacement digit call good-base accumulator)
  (let ((pr (library-library-proof p))
        (x *library-x*) (y *library-y*) (ten *h4-book-printing-ten*))
    (proof-with-checked-results
        ((integral (proof-proof-use pr (proof-sym "H4-COUNTDOWN-INTEGER" "ACL2") nil (list test)))
         (positive-x (proof-proof-use pr (proof-sym "H4-COUNTDOWN-POSITIVE" "ACL2") nil (list test)))
         (integer-base (library-library-type-of p ten nil))
         (large-base (h4-tactics-tactics-establish p (library-lt *proof-one* ten) nil nil nil nil))
         (lemma (proof-proof-fact pr *h4-book-division-floor-bounds* (list (list y ten))))
         (premise (h4-book-division-conjunction p (list integral positive-x integer-base large-base)))
         (bound (h4-tactics-tactics-modus-ponens p lemma premise))
         (parts (h4-tactics-tactics-conjunct p bound))
         (child-integer (library-library-cite p "NATURAL-INTEGER" (list child) (list (car parts))))
         (descent (library-library-cite p "NFIX-DECREASE" (list child x)
                                        (list child-integer integral positive-x (cadr parts))))
         (smaller (proof-step-first descent))
         (child-goal (proof-subst goal (proof-bindings-table replacement nil)))
         (assumption (proof-proof-assume pr (proof-ite smaller child-goal *proof-true*) t))
         (hypothesis (proof-proof-prove-if pr assumption descent))
         (characters (h4-book-printing-characters-of p (list *proof-cons* digit y) (list accumulator)))
         (recursive (h4-tactics-tactics-modus-ponens p hypothesis characters))
         (equation (h4-book-printing-unfold p call (list test good-base))))
      (h4-book-printing-character-results p equation (list recursive)))))

(defun h4-book-printing-decimal-digits (p)
  (let* ((pr (library-library-proof p))
         (x *library-x*) (y *library-y*) (ten *h4-book-printing-ten*)
         (call (list *h4-book-printing-explode-int* x ten y))
         (target (list *h4-book-printing-characters* call)))
    (proof-with-checked-results
        ((accumulator (proof-proof-assume pr (list *h4-book-printing-characters* y) t))
         (condition (proof-step-first accumulator))
         (good-base (h4-tactics-tactics-establish
                     p (list *h4-book-printing-print-base* ten) nil
                     (append *h4-book-printing-logic*
                             (list *h4-book-printing-print-base* *h4-book-printing-member*)) nil nil)))
      (let* ((goal (list *library-implies* condition target))
             (child (list *h4-book-division-floor* x ten))
             (digit (list *h4-book-printing-digit* (list *h4-book-printing-mod* x ten)))
             (replacement (list (list x child) (list y (list *proof-cons* digit y))))
             (test (list *h4-book-arithmetic-zp* x)))
        (proof-with-checked-results
            ((positive (proof-proof-assume pr test t))
             (stop (h4-book-printing-decimal-digits-stop positive p call good-base accumulator))
             (negative (proof-proof-assume pr test nil))
             (continue (h4-book-printing-decimal-digits-continue-
                        negative p child goal replacement digit call good-base accumulator))
             (cases (h4-tactics-tactics-case-of p target test stop continue))
             (ordinal (library-library-cite p "NFIX-ORDINAL" (list x) nil))
             (implication (h4-tactics-tactics-imply p goal cases))
             (proof (proof-proof-induct pr ordinal implication goal (list *library-nfix* x)
                                       (list replacement)))
             (digit-lemma (h4-tactics-tactics-local-lemma p *h4-book-printing-decimal-digits* proof)))
          (cdr digit-lemma))))))

(defun h4-book-printing-decimal-atom-printed-parts (p parts)
  (if (endp parts)
      nil
    (let ((pr (library-library-proof p)))
      (proof-with-checked-results
          ((literal (proof-step-first (car parts)))
           (argument (proof-term-at literal 1))
           (rule (proof-proof-fact pr *h4-book-printing-decimal-rational*
                                   (list (list *library-x* argument))))
           (part (h4-tactics-tactics-modus-ponens p rule (car parts)))
           (rest (h4-book-printing-decimal-atom-printed-parts p (cdr parts))))
        (cons part rest)))))

(defun h4-book-printing-decimal-atom (p)
  (let* ((pr (library-library-proof p))
         (x *library-x*)
         (call (list *h4-book-printing-explode-atom* x *h4-book-printing-ten*))
         (target (list *h4-book-printing-characters* call)))
    (proof-with-checked-results
        ((integral (proof-proof-assume pr (library-integer x) t))
         (rational-axiom (library-library-axiom p "INTEGER-IMPLIES-RATIONAL" (list x)))
         (integer-type (library-library-type-of p x (list integral)))
         (rational-type (h4-tactics-tactics-modus-ponens p rational-axiom integer-type))
         (opened (h4-book-printing-unfold p call (list integral rational-type)))
         (integer-result (h4-book-printing-character-results p opened nil))
         (integral-literal (proof-step-first integral))
         (integer-proof (h4-tactics-tactics-imply
                         p (list *library-implies* integral-literal target) integer-result))
         (integer-lemma (h4-tactics-tactics-local-lemma p *h4-book-printing-decimal-integer* integer-proof)))
      (let ((p (cdr integer-lemma))
            (test (list *h4-book-printing-rational* x)))
        (proof-with-checked-results
            ((rational (proof-proof-assume (library-library-proof p) test t))
             (axiom (library-library-axiom p "RATIONAL-IMPLIES1" (list x)))
             (representation (h4-tactics-tactics-modus-ponens p axiom rational))
             (numerator-parts (h4-tactics-tactics-conjunct p representation))
             (numerator-integer (h4-tactics-tactics-conjunct p (cadr numerator-parts)))
             (numerator-rule (proof-proof-fact
                              (library-library-proof p) *h4-book-printing-decimal-integer*
                              (list (list x (list *h4-book-division-numerator* x)))))
             (numerator-print (h4-tactics-tactics-modus-ponens p numerator-rule (car numerator-integer)))
             (opened (h4-book-printing-unfold p call (list rational)))
             (rational-result (h4-book-printing-character-results p opened (list numerator-print)))
             (rational-proof (h4-tactics-tactics-imply p (list *library-implies* test target) rational-result))
             (rational-lemma (h4-tactics-tactics-local-lemma
                              p *h4-book-printing-decimal-rational* rational-proof)))
          (let* ((p (cdr rational-lemma))
                 (pr (library-library-proof p)))
            (proof-with-checked-results
                ((complex-axiom (library-library-axiom p "COMPLEX-IMPLIES1" (list x)))
                 (parts (h4-tactics-tactics-conjunct p complex-axiom))
                 (printed-parts (h4-book-printing-decimal-atom-printed-parts p parts))
                 (positive (proof-proof-assume pr test t))
                 (rational-rule (proof-proof-fact pr *h4-book-printing-decimal-rational* nil))
                 (rational-result (h4-tactics-tactics-modus-ponens p rational-rule positive))
                 (negative (proof-proof-assume pr test nil))
                 (opened (h4-book-printing-unfold p call (list negative)))
                 (complex-result (h4-book-printing-character-results p opened printed-parts))
                 (proof (h4-tactics-tactics-case-of p target test rational-result complex-result))
                 (atom-lemma (h4-tactics-tactics-local-lemma p *h4-book-printing-decimal-atom* proof)))
              (cdr atom-lemma))))))))

; The facts that the printing lemmas added, in the order in which they
; were added: those after the first OLD-COUNT.
(defun h4-book-printing-new-facts (facts old-count)
  (nthcdr old-count facts))

(defun h4-book-printing-printing-support (p)
  (let ((old-count (len (proof-proof-facts (library-library-proof p)))))
    (proof-with-checked-results
        ((quotient (h4-book-division-quotient-bounds p))
         (floor-bounds (h4-book-division-floor-bounds (cdr quotient)))
         (characters (h4-book-printing-character-lemmas (cdr floor-bounds)))
         (digits (h4-book-printing-decimal-digits characters))
         (atoms (h4-book-printing-decimal-atom digits))
         (support (h4-book-printing-new-facts (proof-proof-facts (library-library-proof atoms)) old-count)))
      (cons support atoms))))

(defun h4-book-printing-packing-formula (formula)
  (if (proof-is-call formula *h4-book-printing-characters*)
      (proof-with-checked-results ((argument (proof-term-at formula 1)))
        (if (proof-compound argument)
            (proof-with-checked-results ((head (proof-term-at argument 0)))
              (and (or (equal head *h4-book-printing-pack-list*)
                       (equal head *h4-book-printing-pack-tree*))
                   (equal (len argument) 2)
                   (not (proof-compound (cadr argument)))))
          nil))
    nil))

(defun h4-book-printing-packing-proof-results (p calls shape premises)
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((opened (h4-book-printing-unfold p (car calls) (list shape)))
         (step (h4-book-printing-character-results p opened premises))
         (rest (h4-book-printing-packing-proof-results p (cdr calls) shape premises)))
      (cons step rest))))

(defun h4-book-printing-packing-proof-both (shape premises p calls)
  (proof-with-checked-results
      ((proofs (h4-book-printing-packing-proof-results p calls shape premises)))
    (h4-book-division-conjunction p proofs)))

(defund h4-book-printing-packing-proof-child (p shape target number child)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((builtin (library-library-builtin p number *library-x*))
         (descent (proof-proof-discharge pr builtin shape))
         (condition (proof-step-first descent))
         (instance (proof-subst target (list (cons *library-x* child))))
         (hypothesis (proof-proof-assume pr (proof-ite condition instance *proof-true*) t))
         (opened (proof-proof-prove-if pr hypothesis descent)))
      (h4-tactics-tactics-conjunct p opened))))

(defun h4-book-printing-packing-proof-premises (p shape target numbers children)
  (declare (xargs :measure (acl2-count numbers)))
  (if (or (endp numbers) (endp children))
      nil
    (proof-with-checked-results
        ((parts (h4-book-printing-packing-proof-child p shape target (car numbers) (car children)))
         (rest (h4-book-printing-packing-proof-premises p shape target (cdr numbers) (cdr children))))
      (append parts rest))))

(defun h4-book-printing-packing-proof-recursive (shape p target children calls)
  (proof-with-checked-results
      ((premises (h4-book-printing-packing-proof-premises p shape target '(2 3) children)))
    (h4-book-printing-packing-proof-both shape premises p calls)))

(defun h4-book-printing-packing-proof-joined (p formula)
  (let* ((pr (library-library-proof p))
         (x *library-x*)
         (list-call (list *h4-book-printing-pack-list* x))
         (tree-call (list *h4-book-printing-pack-tree* x))
         (calls (list list-call tree-call))
         (target (proof-ite (list *h4-book-printing-characters* list-call)
                            (list *h4-book-printing-characters* tree-call) *proof-false*))
         (test (list *proof-consp* x))
         (left (list *library-car* x))
         (right (list *library-cdr* x))
         (children (list left right))
         (replacements (list (list (list x left)) (list (list x right)))))
    (proof-with-checked-results
        ((pair (proof-proof-assume pr test t))
         (recursion (h4-book-printing-packing-proof-recursive pair p target children calls))
         (atom-case (proof-proof-assume pr test nil))
         (base (h4-book-printing-packing-proof-both atom-case nil p calls))
         (cases (h4-tactics-tactics-case-of p target test recursion base))
         (ordinal (library-library-builtin p 1 x))
         (joined (proof-proof-induct pr ordinal cases target (list *library-count* x) replacements))
         (parts (h4-tactics-tactics-conjunct p joined)))
      (proof-proof-instantiate
       pr (if (equal (caadr formula) *h4-book-printing-pack-list*) (car parts) (cadr parts))
       (list (list x (cadadr formula)))))))

(defun h4-book-printing-packing-proof (p formula support)
  (let* ((pr (library-library-proof p))
         (definitions (proof-proof-definitions pr)))
    (if (endp support)
        (cons nil p)
      (proof-with-checked-results ((matches (h4-book-printing-packing-formula formula)))
        (if (and matches (assoc-equal *h4-book-printing-pack-list* definitions)
                 (assoc-equal *h4-book-printing-pack-tree* definitions))
            (let ((p (library-library-with-proof
                      p (proof-proof-with-facts pr (table-update (proof-proof-facts pr) support)))))
              (proof-with-checked-results ((step (h4-book-printing-packing-proof-joined p formula)))
                (cons step p)))
          (cons nil p))))))
