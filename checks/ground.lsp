; This script writes build/ground.txt, the ground theory of spec/logic.md,
; from what ACL2 itself holds, so that it can be compared, byte for
; byte, with spec/ground.txt.  It is run from the root of the repository
; by checks/run.sh.
;
; What it takes from ACL2's world:
;   - the primitive functions and their arities;
;   - the symbols of the package COMMON-LISP that ACL2 refuses as
;     variables, its constant *COMMON-LISP-SPECIALS-AND-CONSTANTS*;
;   - every axiom ACL2 has (each defaxiom event of its world);
;   - ACL2's built-in clauses, the value of its constant
;     *INITIAL-BUILT-IN-CLAUSES*: the clauses about ACL2-COUNT that its
;     prover holds as true with no proof;
;   - ACL2's definition of every function that an axiom, a built-in
;     clause, or a fact below, mentions, of O-P, O< and NOT, of
;     TRUE-LISTP and MV-NTH,
;     which the axiom of a function introduced by choice may mention,
;     of ACL2-COUNT, the measure of the size of an object, and of every
;     function those definitions call.  Each definition is written with
;     the ruler-extenders ACL2 stores for it, or NIL if it stores none
;     because the function does not call itself.
;
; What it asks ACL2 to prove: each fact stated below with BM-CLAUSE, and
; each built-in clause.  These are the facts that ACL2 has no axiom for,
; because they are part of its prover.  A fact reaches the output only
; if ACL2 proves it.  That ACL2 proves a built-in clause here shows only
; that ACL2 holds the clause as true: its prover has these clauses built
; in, with no proof, and what else it knows of ACL2-COUNT rests on a
; definition that it admitted with the proof of termination skipped.

(in-package "ACL2")

(ld "checks/version.lsp")
(ld "checks/canon.lsp")

; (bm-clause "name" lit ...) asks ACL2 to prove (or lit ...), and then
; records the clause.  Each literal is written as a translated term.

(defmacro bm-clause (name &rest lits)
  (let ((thm (intern (string-append "BM-CLAUSE-" (string-upcase name))
                     "ACL2")))
    `(progn (defthm ,thm (or ,@lits) :rule-classes nil)
            (table bm-clauses ,name '(,thm ,@lits)))))

; The meaning of IF and EQUAL, and of a term used as a formula.

(bm-clause "if-nil" (equal (if 'nil y z) z))
(bm-clause "if-non-nil" (equal x 'nil) (equal (if x y z) y))
(bm-clause "equal-same" (equal (equal x x) 't))
(bm-clause "equal-different" (equal x y) (equal (equal x y) 'nil))
(bm-clause "non-nil-true" (equal x 'nil) x)

; Each recognizer gives T or NIL, and so does <.

(bm-clause "booleanp-consp" (booleanp (consp x)))
(bm-clause "booleanp-integerp" (booleanp (integerp x)))
(bm-clause "booleanp-rationalp" (booleanp (rationalp x)))
(bm-clause "booleanp-complex-rationalp" (booleanp (complex-rationalp x)))
(bm-clause "booleanp-acl2-numberp" (booleanp (acl2-numberp x)))
(bm-clause "booleanp-stringp" (booleanp (stringp x)))
(bm-clause "booleanp-symbolp" (booleanp (symbolp x)))
(bm-clause "booleanp-<" (booleanp (< x y)))

; The kinds of object are disjoint.

(bm-clause "consp-not-acl2-numberp" (implies (consp x) (not (acl2-numberp x))))
(bm-clause "consp-not-characterp" (implies (consp x) (not (characterp x))))
(bm-clause "consp-not-stringp" (implies (consp x) (not (stringp x))))
(bm-clause "consp-not-symbolp" (implies (consp x) (not (symbolp x))))
(bm-clause "acl2-numberp-not-characterp"
           (implies (acl2-numberp x) (not (characterp x))))
(bm-clause "acl2-numberp-not-stringp"
           (implies (acl2-numberp x) (not (stringp x))))
(bm-clause "acl2-numberp-not-symbolp"
           (implies (acl2-numberp x) (not (symbolp x))))
(bm-clause "characterp-not-stringp" (implies (characterp x) (not (stringp x))))
(bm-clause "characterp-not-symbolp" (implies (characterp x) (not (symbolp x))))
(bm-clause "stringp-not-symbolp" (implies (stringp x) (not (symbolp x))))

; The numbers are the rationals and the complex rationals.

(bm-clause "rationalp-acl2-numberp" (implies (rationalp x) (acl2-numberp x)))
(bm-clause "complex-rationalp-acl2-numberp"
           (implies (complex-rationalp x) (acl2-numberp x)))
(bm-clause "acl2-numberp-cases"
           (implies (acl2-numberp x)
                    (if (rationalp x) 't (complex-rationalp x))))
(bm-clause "complex-rationalp-not-rationalp"
           (implies (complex-rationalp x) (not (rationalp x))))
(bm-clause "imagpart-rationalp" (implies (rationalp x) (equal (imagpart x) '0)))

; What the arithmetic functions give on integers and on rationals.

(bm-clause "integerp-binary-+"
           (implies (if (integerp x) (integerp y) 'nil)
                    (integerp (binary-+ x y))))
(bm-clause "integerp-binary-*"
           (implies (if (integerp x) (integerp y) 'nil)
                    (integerp (binary-* x y))))
(bm-clause "integerp-unary--" (implies (integerp x) (integerp (unary-- x))))
(bm-clause "rationalp-binary-+"
           (implies (if (rationalp x) (rationalp y) 'nil)
                    (rationalp (binary-+ x y))))
(bm-clause "rationalp-binary-*"
           (implies (if (rationalp x) (rationalp y) 'nil)
                    (rationalp (binary-* x y))))
(bm-clause "rationalp-unary--" (implies (rationalp x) (rationalp (unary-- x))))
(bm-clause "rationalp-unary-/" (implies (rationalp x) (rationalp (unary-/ x))))
(bm-clause "integer-discrete"
           (implies (if (integerp x) (< '0 x) 'nil) (not (< x '1))))

; What the other primitives give.

(bm-clause "consp-cons" (consp (cons x y)))
(bm-clause "stringp-symbol-name" (stringp (symbol-name x)))
(bm-clause "integerp-char-code" (integerp (char-code x)))
(bm-clause "char-code-non-negative" (not (< (char-code x) '0)))
(bm-clause "stringp-coerce"
           (implies (not (equal y 'list)) (stringp (coerce x y))))

; ACL2's built-in clauses.  They are taken from ACL2's constant as this
; script runs, in ACL2's order, with the literals of each in ACL2's
; order.  ACL2 gives them no names.  Here the clause at place N of the
; constant, counting from 1, is named "built-in-clause-N".

(defun bm-built-in-events (records n)
  (declare (xargs :mode :program))
  (cond ((endp records) nil)
        (t (cons (list* 'bm-clause
                        (string-append
                         "built-in-clause-"
                         (coerce (explode-nonnegative-integer n 10 nil)
                                 'string))
                        (access built-in-clause (car records) :clause))
                 (bm-built-in-events (cdr records) (+ 1 n))))))

(make-event
 (cons 'progn (bm-built-in-events *initial-built-in-clauses* 1)))

(program)

; The names of ACL2's axioms, oldest first.

(defun bm-axiom-names (wrld acc)
  (cond ((endp wrld) acc)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value)
              (consp (access-event-tuple-form (cddar wrld)))
              (eq (car (access-event-tuple-form (cddar wrld))) 'defaxiom))
         (bm-axiom-names
          (cdr wrld)
          (cons (cadr (access-event-tuple-form (cddar wrld))) acc)))
        (t (bm-axiom-names (cdr wrld) acc))))

(defun bm-formulas (names wrld)
  (cond ((endp names) nil)
        (t (cons (getpropc (car names) 'theorem nil wrld)
                 (bm-formulas (cdr names) wrld)))))

(defun bm-table-lits (alist)
  (cond ((endp alist) nil)
        (t (append (cddr (car alist)) (bm-table-lits (cdr alist))))))

; Every function reached from TODO through ACL2's definitions, the
; primitives left out.

(defun bm-closure (todo seen prims wrld)
  (cond ((endp todo) seen)
        ((or (member-eq (car todo) seen) (member-eq (car todo) prims))
         (bm-closure (cdr todo) seen prims wrld))
        (t (let ((body (getpropc (car todo) 'unnormalized-body nil wrld)))
             (if (null body)
                 (er hard 'bm-closure "~x0 has no definition" (car todo))
               (bm-closure (append (all-fnnames body) (cdr todo))
                           (cons (car todo) seen) prims wrld))))))

(defun bm-insert (fn fns wrld)
  (cond ((endp fns) (list fn))
        ((< (getpropc fn 'absolute-event-number 0 wrld)
            (getpropc (car fns) 'absolute-event-number 0 wrld))
         (cons fn fns))
        (t (cons (car fns) (bm-insert fn (cdr fns) wrld)))))

(defun bm-sort (fns acc wrld)
  (cond ((endp fns) acc)
        (t (bm-sort (cdr fns) (bm-insert (car fns) acc wrld) wrld))))

(defun bm-or (lits)
  (cond ((endp (cdr lits)) (car lits))
        (t (list 'if (car lits) (car lits) (bm-or (cdr lits))))))

(defun bm-package-lines (names wrld)
  (cond ((endp names) nil)
        (t (let ((rest (bm-package-lines (cdr names) wrld))
                 (formula (getpropc (car names) 'theorem nil wrld)))
             (case-match formula
               (('equal ('pkg-imports ('quote name)) ('quote imports))
                (cons (bm-line "package" (list name imports)) rest))
               (& rest))))))

(defun bm-primitive-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (bm-line "primitive"
                          (list (car (car alist)) (len (cadr (car alist)))))
                 (bm-primitive-lines (cdr alist))))))

(defun bm-rulers (fn wrld)
  (let ((just (getpropc fn 'justification nil wrld)))
    (and just (access justification just :ruler-extenders))))

(defun bm-define-lines (fns wrld)
  (cond ((endp fns) nil)
        (t (cons (bm-line "define"
                          (list (bm-rulers (car fns) wrld)
                                (list (car fns)
                                      (formals (car fns) wrld)
                                      (getpropc (car fns) 'unnormalized-body
                                                nil wrld))))
                 (bm-define-lines (cdr fns) wrld)))))

; A clause of the table is written only if ACL2 holds the theorem that
; BM-CLAUSE stated for it and every literal is a term.

(defun bm-clause-lines (alist wrld)
  (cond ((endp alist) nil)
        (t (let ((name (car (car alist)))
                 (thm (cadr (car alist)))
                 (lits (cddr (car alist))))
             (cons (if (and (term-listp lits wrld)
                            (equal (getpropc thm 'theorem nil wrld)
                                   (bm-or lits)))
                       (bm-line "clause" (cons name lits))
                     (string-append "NOT PROVED: " name))
                   (bm-clause-lines (cdr alist) wrld))))))

(defun bm-axiom-lines (names wrld)
  (cond ((endp names) nil)
        (t (let ((rest (bm-axiom-lines (cdr names) wrld))
                 (formula (getpropc (car names) 'theorem nil wrld)))
             (case-match formula
               (('equal ('pkg-imports ('quote &)) ('quote &)) rest)
               (& (cons (bm-line "clause" (list (car names) formula))
                        rest)))))))

(defun bm-ground-lines (state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state))
         (prims (strip-cars *primitive-formals-and-guards*))
         (axioms (bm-axiom-names wrld nil))
         (table (reverse (table-alist 'bm-clauses wrld)))
         (seeds (append '(not o-p o< true-listp mv-nth acl2-count)
                        (all-fnnames-lst (append (bm-table-lits table)
                                                 (bm-formulas axioms wrld)))))
         (fns (bm-sort (bm-closure seeds nil prims wrld) nil wrld)))
    (append (list (bm-line "package"
                           (list "COMMON-LISP" (pkg-imports "COMMON-LISP"))))
            (bm-package-lines axioms wrld)
            (list (bm-line "specials"
                           (list *common-lisp-specials-and-constants*)))
            (bm-primitive-lines *primitive-formals-and-guards*)
            (bm-define-lines fns wrld)
            (bm-clause-lines table wrld)
            (bm-axiom-lines axioms wrld))))

(bm-write-file (bm-ground-lines state) "build/ground.txt" state)

(cw "ground: ~x0 axioms, ~x1 facts and ~x2 built-in clauses proved, ~x3 lines~%"
    (len (bm-axiom-names (w state) nil))
    (- (len (table-alist 'bm-clauses (w state)))
       (len *initial-built-in-clauses*))
    (len *initial-built-in-clauses*)
    (len (bm-ground-lines state)))

(good-bye)
