(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro proof-with-checked-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             ,name
           (proof-with-checked-results ,(cdr bindings) ,result))))))

(defun proof-term-at (term index)
  (cond ((integerp term)
         '(:failure "type" ""))
        ((< index (len term)) (nth index term))
        (t (proof-index-failure))))

(defun proof-list-of-length (term size)
  (let ((actual (len term)))
    (cond ((integerp term)
           '(:failure "type" ""))
          ((equal actual size) term)
          (t (proof-length-failure size actual)))))

(defun proof-datum-head (datum)
  (and (consp datum) (car datum)))

(defun proof-uses-slice-rules-p (proof)
  (member-eq (proof-proof-kind proof) '(:slice :book)))

(defun proof-proof-unfold (proof term)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (let ((definition (assoc-equal head (proof-proof-definitions proof))))
      (cond ((not definition) (list :failure "key" ""))
            ((not (equal (len (cadr definition)) (len (cdr term))))
             '(:failure "assertion" ""))
            (t (proof-proof-fact proof head (seq-zip (cadr definition) (cdr term))))))))

(defun proof-proof-true-from-eq (proof equality)
  (proof-with-checked-results
      ((literal (proof-step-first equality))
       (parts (proof-list-of-length literal 3)))
    (if (not (equal (caddr parts) *proof-true*))
        '(:failure "assertion" "")
      (proof-with-checked-results
          ((step (proof-proof-fact proof "non-nil-true"
                                  (list (list (proof-sym "X" "ACL2") (cadr parts)))))
           (rewritten (proof-proof-rewrite proof step equality '(1 1)))
           (computed (proof-proof-compute proof
                                         (proof-eq *proof-true* *proof-false*)
                                         *proof-nil*))
           (result (proof-proof-rewrite proof rewritten computed '(1))))
        (proof-proof-tidy proof result)))))

(defun proof-proof-reflexive-base (proof term)
  (proof-with-checked-results
      ((identity (proof-proof-fact proof "equal-same"
                                  (list (list (proof-sym "X" "ACL2") term)))))
    (proof-proof-true-from-eq proof identity)))

(defun proof-proof-reflexive (proof term)
  (let ((lemma (proof-sym "SELF-EQUALITY-REFLEXIVE" "ACL2")))
    (if (and (proof-uses-slice-rules-p proof)
             (assoc-equal lemma (proof-proof-facts proof)))
        (proof-proof-fact proof lemma (list (list (proof-sym "X" "ACL2") term)))
      (proof-proof-reflexive-base proof term))))

(defun proof-proof-symmetric (proof equality)
  (proof-with-checked-results
      ((literal (proof-step-first equality))
       (left (proof-term-at literal 1))
       (reflexive (proof-proof-reflexive proof left)))
    (proof-proof-rewrite proof reflexive equality '(1 1))))

(defun proof-proof-chain (proof first rest)
  (cond ((endp rest) (proof-proof-tidy proof first))
        ((not (car rest)) (proof-proof-chain proof first (cdr rest)))
        (t (proof-with-checked-results
               ((next (proof-proof-rewrite proof first (car rest) '(1 2))))
             (proof-proof-chain proof next (cdr rest))))))

(defun proof-proof-nil-or-true (proof term)
  (proof-proof-fact proof "non-nil-true"
                    (list (list (proof-sym "X" "ACL2") term))))

(defun proof-proof-not-nil (proof)
  (proof-with-checked-results
      ((unfolded (proof-proof-unfold proof (proof-neg *proof-false*)))
       (computed (proof-proof-compute proof
                                     (proof-ite *proof-false* *proof-false* *proof-true*)
                                     *proof-t*))
       (chained (proof-proof-chain proof unfolded (list computed))))
    (proof-proof-true-from-eq proof chained)))

(defun proof-proof-excluded-middle (proof term)
  (proof-with-checked-results
      ((not-nil (proof-proof-not-nil proof))
       (nil-or-true (proof-proof-nil-or-true proof term))
       (reversed (proof-proof-symmetric proof nil-or-true))
       (rewritten (proof-proof-rewrite proof not-nil reversed '(1 1))))
    (proof-proof-tidy proof rewritten)))

(defun proof-proof-assume (proof term holds)
  (let ((lemma (proof-sym "SELF-EXCLUDED-MIDDLE" "ACL2")))
    (proof-with-checked-results
        ((excluded (if (assoc-equal lemma (proof-proof-facts proof))
                       (proof-proof-fact proof lemma
                                         (list (list (proof-sym "X" "ACL2") term)))
                     (proof-proof-excluded-middle proof term))))
      (if holds (proof-proof-front proof excluded term) excluded))))

(defun proof-proof-discharge (proof step evidence)
  (proof-discharge proof step evidence))

(defun proof-if-bindings (args)
  (seq-zip '(("sym" "ACL2" "X") ("sym" "ACL2" "Y") ("sym" "ACL2" "Z")) args))

(defun proof-if-nil-bindings (branches)
  (seq-zip '(("sym" "ACL2" "Y") ("sym" "ACL2" "Z")) branches))

(defun proof-proof-if-false (proof term)
  (proof-with-checked-results ((parts (proof-list-of-length term 4)))
    (let ((lemma (proof-sym "SELF-IF-FALSE" "ACL2")))
      (if (assoc-equal lemma (proof-proof-facts proof))
          (proof-proof-fact proof lemma (proof-if-bindings (cdr parts)))
        (proof-with-checked-results
            ((step (proof-proof-fact proof "if-nil" (proof-if-nil-bindings (cddr parts))))
             (nil-or-true (proof-proof-nil-or-true proof (cadr parts)))
             (reversed (proof-proof-symmetric proof nil-or-true)))
          (proof-proof-rewrite proof step reversed '(1 1 1)))))))

(defun proof-proof-if-true (proof term)
  (proof-with-checked-results ((parts (proof-list-of-length term 4)))
    (let ((lemma (proof-sym "SELF-IF-TRUE" "ACL2"))
          (bindings (proof-if-bindings (cdr parts))))
      (if (assoc-equal lemma (proof-proof-facts proof))
          (proof-proof-fact proof lemma bindings)
        (proof-with-checked-results
            ((step (proof-proof-fact proof "if-non-nil" bindings))
             (nil-test (proof-step-first step))
             (assumed (proof-proof-assume proof nil-test t))
             (test-is-nil (proof-proof-symmetric proof assumed))
             (not-nil (proof-proof-not-nil proof))
             (negated-test (proof-proof-rewrite proof not-nil test-is-nil '(1 1)))
             (guard (proof-proof-front proof negated-test (proof-neg nil-test)))
             (result (proof-proof-cut proof step guard)))
          (proof-proof-front proof result (proof-eq term (caddr parts))))))))

(defun proof-proof-select (proof term evidence)
  (proof-with-checked-results
      ((test (proof-term-at term 1))
       (literal (proof-step-first evidence))
       (step (cond ((equal literal test) (proof-proof-if-true proof term))
                   ((equal literal (proof-neg test)) (proof-proof-if-false proof term))
                   (t '(:failure "assertion" "")))))
    (proof-proof-discharge proof step evidence)))

(defun proof-proof-prove-if (proof step test-proof)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (selected (proof-proof-select proof literal test-proof))
       (rewritten (proof-proof-rewrite proof step selected '(1))))
    (proof-proof-tidy proof rewritten)))

(defun proof-proof-conjunct (proof step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (parts (proof-list-of-length literal 4)))
    (if (not (equal (cadddr parts) *proof-false*))
        '(:failure "assertion" "")
      (proof-with-checked-results
          ((false-branch (proof-proof-if-false proof literal))
           (rewritten (proof-proof-rewrite proof step false-branch '(1)))
           (tidied (proof-proof-tidy proof rewritten))
           (test-proof (proof-proof-front proof tidied (cadr parts)))
           (branch-proof (proof-proof-prove-if proof step test-proof)))
        (list test-proof branch-proof)))))

(defun proof-proof-modus-ponens (proof step evidence)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (head (proof-term-at literal 0)))
    (if (not (equal head (proof-sym "IMPLIES" "ACL2")))
        '(:failure "assertion" "")
      (proof-with-checked-results
          ((opened (proof-proof-unfold proof literal))
           (rewritten (proof-proof-rewrite proof step opened '(1)))
           (reduced (proof-proof-prove-if proof rewritten evidence))
           (remaining (proof-step-first reduced))
           (parts (proof-list-of-length remaining 4)))
        (if (not (and (equal (caddr parts) *proof-true*)
                      (equal (cadddr parts) *proof-false*)))
            '(:failure "assertion" "")
          (proof-with-checked-results
              ((false-branch (proof-proof-if-false proof remaining))
               (result (proof-proof-rewrite proof reduced false-branch '(1)))
               (tidied (proof-proof-tidy proof result)))
            (proof-proof-front proof tidied (cadr parts))))))))

(defun proof-proof-transport (proof step equality)
  (proof-with-checked-results
      ((reversed (proof-proof-symmetric proof equality))
       (rewritten (proof-proof-rewrite proof step reversed '(1))))
    (proof-proof-tidy proof rewritten)))

(defun proof-proof-cases (proof test yes no)
  (proof-with-checked-results
      ((claim (proof-step-first yes))
       (other-claim (proof-step-first no)))
    (cond ((not (equal claim other-claim)) '(:failure "assertion" ""))
          ((not (member-equal (proof-neg test) (proof-step-clause yes))) yes)
          ((not (member-equal test (proof-step-clause no))) no)
          (t (proof-with-checked-results
                 ((negative (proof-proof-front proof no test))
                  (positive (proof-proof-front proof yes (proof-neg test)))
                  (result (proof-proof-cut proof negative positive)))
               (proof-proof-front proof result claim))))))

(defun proof-rewritten-term (equality)
  (proof-with-checked-results ((literal (proof-step-first equality)))
    (proof-term-at literal 2)))

(defun proof-by-value-leaves-visit (n proof value tests)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "proof-by-value-leaves-visit"))
        ((proof-is-call value *proof-if*)
         (proof-with-checked-results
             ((branches (proof-list-of-length (cdr value) 3))
              (yes (proof-by-value-leaves-visit
                    (1- n) proof (cadr branches)
                    (append tests (list (list (car branches) t)))))
              (no (proof-by-value-leaves-visit
                   (1- n) proof (caddr branches)
                   (append tests (list (list (car branches) nil))))))
           (append yes no)))
        ((and (proof-compound value) (not (consp value)))
         '(:failure "index" ""))
        ((and (proof-compound value) (proof-compound (car value)))
         (proof-with-checked-results
             ((equality (proof-proof-beta proof value))
              (opened (proof-rewritten-term equality)))
           (proof-by-value-leaves-visit (1- n) proof opened tests)))
        (t (list (list value tests)))))

(defun proof-proof-by-value-leaves (proof value tests)
  (proof-by-value-leaves-visit 1000000 proof value tests))

(defun proof-by-value-transport-number (proof step equality)
  (proof-with-checked-results
      ((reversed (proof-proof-symmetric proof equality))
       (rewritten (proof-proof-rewrite proof step reversed '(1 1))))
    (proof-proof-tidy proof rewritten)))

(defun proof-by-value-join-number (proof value yes no lemma)
  (let ((test (cadr value)))
    (if (and (not (member-equal (proof-neg test) (proof-step-clause yes)))
             (not (member-equal test (proof-step-clause no))))
        (proof-proof-use proof lemma (proof-if-bindings (cdr value)) (list yes no))
      (proof-with-checked-results
          ((if-true (proof-proof-if-true proof value))
           (yes-proof (proof-by-value-transport-number proof yes if-true))
           (if-false (proof-proof-if-false proof value))
           (no-proof (proof-by-value-transport-number proof no if-false)))
        (proof-proof-cases proof test yes-proof no-proof)))))

(defun proof-by-value-join (proof value template yes no)
  (let ((lemma (proof-sym "SELF-NUMBER-IF" "ACL2")))
    (if (and (proof-uses-slice-rules-p proof)
             (equal template (list (proof-sym "ACL2-NUMBERP" "ACL2") *proof-result*))
             (assoc-equal lemma (proof-proof-facts proof)))
        (proof-by-value-join-number proof value yes no lemma)
      (proof-with-checked-results
          ((if-true (proof-proof-if-true proof value))
           (true-equality (proof-proof-symmetric proof if-true))
           (yes-proof (proof-proof-rewrite-result proof yes true-equality template *proof-result*))
           (if-false (proof-proof-if-false proof value))
           (false-equality (proof-proof-symmetric proof if-false))
           (no-proof (proof-proof-rewrite-result proof no false-equality template *proof-result*)))
        (proof-proof-cases proof (cadr value) yes-proof no-proof)))))

(defun proof-by-value-visit (n proof value template leaf tests)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "proof-by-value-visit"))
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results
        ((branches (proof-list-of-length (cdr value) 3))
         (yes (proof-by-value-visit
               (1- n) proof (cadr branches) template leaf
               (append tests (list (list (car branches) t)))))
         (no (proof-by-value-visit
              (1- n) proof (caddr branches) template leaf
              (append tests (list (list (car branches) nil))))))
      (proof-by-value-join proof value template yes no)))
   ((and (proof-compound value) (not (consp value)))
    '(:failure "index" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta proof value))
         (opened (proof-rewritten-term equality))
         (step (proof-by-value-visit (1- n) proof opened template leaf tests))
         (reversed (proof-proof-symmetric proof equality)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*)))
   (t (let ((entry (assoc-equal (list value tests) leaf)))
        (if (not entry)
            '(:failure "value" "")
          (proof-with-checked-results
              ((step (cdr entry))
               (literal (proof-step-first step))
               (target (proof-subst template (list (cons *proof-result* value)))))
            (if (equal literal target)
                step
              '(:failure "assertion" ""))))))))

(defun proof-proof-by-value (proof value template leaf tests)
  (proof-by-value-visit 1000000 proof value template leaf tests))

(defun proof-quoted-values (args)
  (if (endp args)
      nil
    (proof-with-checked-results
        ((value (proof-term-at (car args) 1))
         (rest (proof-quoted-values (cdr args))))
      (cons value rest))))

(defun proof-list-index-error ()
  '(:failure "index" ""))

(defun proof-constant-value (head values)
  (let ((first (car values))
        (second (cadr values)))
    (cond ((equal head *proof-equal*)
           (if (consp (cdr values))
               (if (equal first second) *proof-t* *proof-nil*)
             (proof-list-index-error)))
          ((equal head *proof-consp*)
           (cond ((endp values) (proof-list-index-error))
                 ((and (proof-compound first) (consp first)) *proof-t*)
                 (t *proof-nil*)))
          ((equal head *proof-integerp*)
           (cond ((endp values) (proof-list-index-error))
                 ((integerp first) *proof-t*)
                 (t *proof-nil*)))
          ((member-equal head (list (proof-cl "RATIONALP") (proof-cl "STRINGP")
                                    (proof-sym "COMPLEX-RATIONALP" "ACL2")))
           (if (endp values)
               (proof-list-index-error)
             (let* ((tag (proof-datum-head first))
                    (recognized
                     (cond ((equal head (proof-cl "RATIONALP"))
                            (or (equal tag "ratio") (integerp first)))
                           ((equal head (proof-cl "STRINGP")) (equal tag "str"))
                           (t (equal tag "complex")))))
               (if recognized *proof-t* *proof-nil*))))
          ((and (member-equal head (list *proof-less* *proof-plus* *proof-minus* *proof-times*))
                (integer-listp values))
           (cond ((equal head *proof-minus*)
                  (if (consp values) (- first) (proof-list-index-error)))
                 ((endp (cdr values)) (proof-list-index-error))
                 ((equal head *proof-less*) (if (< first second) *proof-t* *proof-nil*))
                 ((equal head *proof-plus*) (+ first second))
                 (t (* first second))))
          (t nil))))

(defun proof-constant-call-parts (term)
  (cond ((integerp term)
         '(:failure "type" ""))
        ((endp term)
         '(:failure "value" ""))
        (t term)))

(defun proof-proof-constant-base (proof term)
  (proof-with-checked-results ((parts (proof-constant-call-parts term)))
    (let ((head (car parts))
          (args (cdr parts)))
      (cond ((and (equal head *proof-equal*) (endp (cdr args)))
             (proof-list-index-error))
            ((and (equal head *proof-equal*) (equal (car args) (cadr args)))
             (proof-proof-fact proof "equal-same"
                               (list (list (proof-sym "X" "ACL2") (car args)))))
            ((not (proof-all-quoted-p args)) nil)
            (t (proof-with-checked-results
                   ((values (proof-quoted-values args))
                    (value (proof-constant-value head values)))
                 (if value (proof-proof-compute proof term value) nil)))))))

(defun proof-constant-slice (proof term)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (let ((numberp (proof-sym "ACL2-NUMBERP" "ACL2"))
          (characterp (proof-cl "CHARACTERP"))
          (symbolp (proof-cl "SYMBOLP")))
      (if (not (member-equal head (list numberp characterp symbolp)))
          (proof-proof-constant-base proof term)
        (proof-with-checked-results ((arg (proof-term-at term 1)))
          (if (not (proof-is-call arg *proof-quote*))
              (proof-proof-constant-base proof term)
            (proof-with-checked-results ((value (proof-term-at arg 1)))
              (let* ((tag (proof-datum-head value))
                     (matches (cond ((equal head numberp)
                                     (or (integerp value) (eq value t)
                                         (member-equal tag '("ratio" "complex"))))
                                    ((equal head characterp) (equal tag "char"))
                                    (t (equal tag "sym")))))
                (proof-proof-compute proof term (if matches *proof-t* *proof-nil*))))))))))

(defun proof-constant-book-argument (args index)
  (if (< index (len args))
      (nth index args)
    (proof-list-index-error)))

(defun proof-constant-cons-value (head tail)
  (cond ((equal tail *proof-nil*) (list head))
        ((proof-compound tail) (cons head tail))
        (t (list head (list "dot" tail)))))

(defun proof-constant-book-list (proof term)
  (let ((head (car term))
        (args (cdr term)))
    (proof-with-checked-results
        ((first (proof-constant-book-argument args 0))
         (value (proof-term-at first 1))
         (result (cond ((equal head *proof-cons*)
                        (proof-with-checked-results
                            ((second (proof-constant-book-argument args 1))
                             (tail (proof-term-at second 1)))
                          (proof-constant-cons-value value tail)))
                       ((or (not (proof-compound value)) (endp value)) *proof-nil*)
                       ((equal head (proof-cl "CAR")) (car value))
                       ((and (equal (len value) 2)
                             (equal (proof-datum-head (cadr value)) "dot"))
                        (proof-term-at (cadr value) 1))
                       (t (or (cdr value) *proof-nil*)))))
      (proof-proof-compute proof term result))))

(defun proof-constant-character-arg (head value)
  (cond ((equal head (proof-cl "CODE-CHAR"))
         (list "char" (if (or (eq value t) (and (integerp value) (<= 0 value) (< value 256)))
                          value
                        0)))
        ((equal (proof-datum-head value) "char") (proof-term-at value 1))
        (t 0)))

(defun proof-constant-book-character (proof term)
  (proof-with-checked-results ((arg (proof-constant-book-argument (cdr term) 0)))
    (if (not (proof-is-call arg *proof-quote*))
        (proof-constant-slice proof term)
      (proof-with-checked-results
          ((value (proof-term-at arg 1))
           (result (proof-constant-character-arg (car term) value)))
        (proof-proof-compute proof term result)))))

(defun proof-constant-character-data (chars)
  (if (endp chars)
      nil
    (cons (list "char" (char-code (car chars)))
          (proof-constant-character-data (cdr chars)))))

(defun proof-constant-character-bytes (elements)
  (cond ((endp elements) nil)
        ((and (endp (cdr elements)) (equal (proof-datum-head (car elements)) "dot")) nil)
        (t (proof-with-checked-results
               ((value (if (equal (proof-datum-head (car elements)) "char")
                           (proof-term-at (car elements) 1)
                         0)))
             (let ((byte (if (eq value t) 1 value)))
               (cond ((not (integerp byte))
                      '(:failure "type" ""))
                     ((or (< byte 0) (<= 256 byte))
                      '(:failure "value" ""))
                     (t (proof-with-checked-results
                            ((rest (proof-constant-character-bytes (cdr elements))))
                          (cons (code-char byte) rest)))))))))

(defun proof-constant-coerced-value (value kind)
  (if (equal kind (proof-cl "LIST"))
      (if (not (equal (proof-datum-head value) "str"))
          *proof-nil*
        (proof-with-checked-results ((contents (proof-term-at value 1)))
          (or (proof-constant-character-data (coerce contents 'list)) *proof-nil*)))
    (proof-with-checked-results
        ((chars (proof-constant-character-bytes (if (proof-compound value) value nil))))
      (list "str" (coerce chars 'string)))))

(defun proof-constant-book-coerce (proof term)
  (proof-with-checked-results
      ((values (proof-quoted-values (cdr term)))
       (parts (proof-list-of-length values 2))
       (result (proof-constant-coerced-value (car parts) (cadr parts))))
    (proof-proof-compute proof term result)))

(defun proof-constant-book (proof term)
  (proof-with-checked-results ((parts (proof-constant-call-parts term)))
    (let ((head (car parts))
          (args (cdr parts)))
      (cond ((and (member-equal head (list (proof-cl "CAR") (proof-cl "CDR") *proof-cons*))
                  (proof-all-quoted-p args))
             (proof-constant-book-list proof term))
            ((member-equal head (list (proof-cl "CODE-CHAR") (proof-cl "CHAR-CODE")))
             (proof-constant-book-character proof term))
            ((and (equal head (proof-cl "COERCE")) (proof-all-quoted-p args))
             (proof-constant-book-coerce proof term))
            (t (proof-constant-slice proof term))))))

(defun proof-proof-constant (proof term)
  (case (proof-proof-kind proof)
    (:book (proof-constant-book proof term))
    (:slice (proof-constant-slice proof term))
    (otherwise (proof-proof-constant-base proof term))))

(defun proof-find-evidence (evidence literals)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car evidence))))
      (if (member-equal literal literals)
          (car evidence)
        (proof-find-evidence (cdr evidence) literals)))))

(defun proof-simplify-if-select (proof redex evidence)
  (let ((test (cadr redex)))
    (cond ((equal test *proof-false*)
           (proof-proof-fact proof "if-nil" (proof-if-nil-bindings (cddr redex))))
          ((equal test *proof-true*)
           (proof-with-checked-results
               ((selection (proof-proof-fact proof "if-non-nil" (proof-if-bindings (cdr redex))))
                (yes (proof-term-at redex 2))
                (ordered (proof-proof-front proof selection (proof-eq redex yes)))
                (computed (proof-proof-compute proof (proof-eq *proof-true* *proof-false*)
                                              *proof-nil*))
                (rewritten (proof-proof-rewrite proof ordered computed '(2))))
             (proof-proof-tidy proof rewritten)))
          (t (proof-with-checked-results
                 ((premise (proof-find-evidence evidence (list test (proof-neg test)))))
               (and premise (proof-proof-select proof redex premise)))))))

(defun proof-simplify-if-redex (term first)
  (if (not first)
      term
    (proof-with-checked-results
        ((test (proof-rewritten-term first))
         (yes (proof-term-at term 2))
         (no (proof-term-at term 3)))
      (proof-ite test yes no))))

(defun proof-simplify-if-chain (proof term first selected)
  (if (not first)
      selected
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof term))
         (rewritten (proof-proof-rewrite proof reflexive first '(1 2 1))))
      (proof-proof-chain proof rewritten (list selected)))))

(defund proof-simplify-if-path (proof term first evidence)
  (proof-with-checked-results
      ((redex (proof-simplify-if-redex term first))
       (branch (proof-simplify-if-select proof redex evidence))
       (selected (proof-simplify-if-chain proof term first branch))
       (right (and selected (proof-rewritten-term selected))))
    (if (and selected (not (equal right redex)))
        (list :simplify selected right)
      selected)))

(defund proof-simplify-expansion (proof term)
  (proof-with-checked-results
      ((first (if (proof-compound (car term))
                  (proof-proof-beta proof term)
                (proof-proof-unfold proof term)))
       (right (proof-rewritten-term first)))
    (list first right)))

(defund proof-simplify-argument-result (proof term index result equality)
  (if (not equality)
      result
    (proof-with-checked-results
        ((previous (or result (proof-proof-reflexive proof term))))
      (proof-proof-rewrite proof previous equality (list 1 2 index)))))

(mutual-recursion
 (defun proof-simplify-visit (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((head (proof-datum-head term)))
     (cond
      ((zp n) '(:failure "Fuel" "proof-simplify-visit"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "index" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (next (proof-simplify-visit (1- n) proof (cadr expansion) evidence definitions)))
         (proof-proof-chain proof (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (proof-simplify-visit (1- n) proof test evidence definitions))
            (path (proof-simplify-if-path proof term first evidence)))
         (if (eq (car path) :simplify)
             (proof-with-checked-results
                 ((next (proof-simplify-visit (1- n) proof (caddr path) evidence definitions)))
               (proof-proof-chain proof (cadr path) (list next)))
           path)))
      (t (proof-with-checked-results
             ((result (proof-simplify-arguments (1- n) proof term (cdr term) 1 nil
                                                evidence definitions))
              (current (if result (proof-rewritten-term result) term))
              (constant (proof-proof-constant proof current)))
           (cond ((not constant) result)
                 (result (proof-proof-chain proof result (list constant)))
                 (t constant)))))))
 (defun proof-simplify-arguments (n proof term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "proof-simplify-arguments"))
         ((endp args) result)
         (t (proof-with-checked-results
                ((equality (proof-simplify-visit (1- n) proof (car args) evidence definitions))
                 (next (proof-simplify-argument-result proof term index result equality)))
              (proof-simplify-arguments (1- n) proof term (cdr args) (1+ index) next
                                        evidence definitions))))))

(defun proof-proof-simplify (proof term evidence definitions)
  (proof-simplify-visit 1000000 proof term evidence definitions))

(defun proof-proof-simplify-first (proof step evidence definitions)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (equality (proof-proof-simplify proof literal evidence definitions)))
    (if equality
        (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
          (proof-proof-tidy proof rewritten))
      step)))

(defun proof-prove-unproved-term (term)
  (proof-with-checked-results ((text (proof-write term)))
    (list :failure "value" (concatenate 'string "No proof of " text))))

(defund proof-prove-step (proof term evidence definitions)
  (cond ((equal term *proof-true*)
         (proof-with-checked-results
             ((step (proof-proof-nil-or-true proof *proof-true*))
              (computed (proof-proof-compute proof (proof-eq *proof-true* *proof-false*)
                                            *proof-nil*))
              (rewritten (proof-proof-rewrite proof step computed '(1))))
           (proof-proof-tidy proof rewritten)))
        (t (proof-with-checked-results
               ((premise (proof-find-evidence evidence (list term))))
             (if premise
                 premise
               (proof-with-checked-results
                   ((equality (proof-proof-simplify proof term evidence definitions))
                    (right (and equality (proof-rewritten-term equality))))
                 (cond ((or (not equality) (equal right term)) (proof-prove-unproved-term term))
                       ((equal right *proof-true*) (proof-proof-true-from-eq proof equality))
                       (t (list :transport right equality)))))))))

(defun proof-prove-visit (n proof term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "proof-prove-visit")
    (let ((result (proof-prove-step proof term evidence definitions)))
      (if (eq (car result) :transport)
          (proof-with-checked-results
              ((step (proof-prove-visit (1- n) proof (cadr result) evidence definitions)))
            (proof-proof-transport proof step (caddr result)))
        result))))

(defun proof-proof-prove (proof term evidence definitions)
  (proof-prove-visit 1000000 proof term evidence definitions))
