; This script writes build/facts.txt: what ACL2 itself says on the points
; where the specification states something about ACL2.  checks/run.sh
; runs it from the root of the repository and compares the result, byte
; for byte, with checks/expected/facts.txt.
;
; Its lines:
;   (event NAME)           a kind of event: a member of ACL2's list
;   (value TERM V)         ACL2's value of a call of a primitive on
;                          constants, with guard checking off
;   (no-value TERM)        a call that ACL2 refuses to evaluate
;   (accepted "what")      a form that ACL2 accepts
;   (refused "what")       a form that ACL2 refuses
;   (package NAME IMPORTS) the imports ACL2 holds for a package
;   (packages NAMES)       the names of the packages ACL2 starts with
;   (imports NAME N)       how many symbols a package imports
;   (choose NAME V)        whether ACL2's axiom for a defchoose is the
;                          one spec/logic.md gives: V is T or NIL
;   (choose-axiom NAME A)  the axiom ACL2 stores for a defchoose
;   (constraint NAME L)    the constraint ACL2 stores for an encapsulate
;   (well-founded REL MP)  a relation ACL2 holds as well founded, and
;                          the recognizer of its domain
;   (stored-theorem NAME V)  whether the world holds a theorem of
;                          that name: V is T or NIL
;   (justification F MP REL M)  the domain, relation and measure with
;                          which ACL2 admitted a definition
;   (termination F TERM)   ACL2's termination theorem for a definition
;   (obligation F L ...)   an obligation of termination of spec/logic.md,
;                          computed here by the walk that document gives
;   (agrees "what" N M)    of M things, the N on which a rule of the
;                          specification, computed here, and ACL2 agree
;   (run TERM V)           ACL2's value of a call with attachments in
;                          force, as at its top level; (no-run TERM) if
;                          it gives none
;   (plain TERM V)         ACL2's value of the same call with no
;                          attachment in force; (no-plain TERM) if it
;                          gives none
;   (attachment F G)       the function ACL2 runs in place of F
;   (hidden-package NAME V)  whether ACL2 keeps the package hidden
;   (count "what" N)       a count over the world ACL2 starts with
;   (measure F TERM)       the measure ACL2 stores for a definition
;   (calls F NAMES)        the functions that the body ACL2 stores for a
;                          definition calls

(in-package "ACL2")

; The number of the last event of the world ACL2 starts with, taken
; before this script adds anything to it.

(make-event
 (list 'defconst '*bm-start* (max-absolute-event-number (w state))))

; The packages of that world.

(make-event
 (list 'defconst '*bm-packages*
       (list 'quote (strip-cars (known-package-alist state)))))

(ld "checks/canon.lsp")

; A package that ACL2 keeps hidden.  checks/run.sh certifies the book
; build/hidden in a world that declares the package BM-HIDDEN, and then
; the book build/outer, which includes it locally.  Including the outer
; book brings the package in, hidden.

(include-book "build/outer")

(set-guard-checking :none)

; (bm-try "what" form) records whether ACL2 accepts FORM.  The form is
; evaluated inside make-event, so that nothing it does stays.

(defmacro bm-try (what form)
  `(make-event
    (mv-let (erp val state)
      ,form
      (declare (ignore val))
      (value (list 'table 'bm-results ,what
                   (if erp ''refused ''accepted))))))

; Names that may not be defined, and variables that may not be bound.

(bm-try "define a function named QUOTE" (defun quote (x) x))
(bm-try "define a function named IF" (defun if (x y z) x))
(bm-try "define a function named CAR" (defun car (x) x))
(bm-try "define a function whose name is a keyword" (defun :f (x) x))
(bm-try "define a function with the formal T" (defun bm-f1 (t) t))
(bm-try "define a function with the formal NIL" (defun bm-f2 (nil) nil))
(bm-try "define a function with a keyword as formal" (defun bm-f3 (:a) :a))
(bm-try "define a function with a formal twice" (defun bm-f4 (x x) x))
(bm-try "define a function with a free variable" (defun bm-f5 (x) (cons x y)))
(bm-try "define a function with the formals X and Y" (defun bm-f6 (x y) (cons x y)))

(bm-try "define a function named by a symbol of COMMON-LISP"
        (defun constantly (x) x))
(bm-try "define a function named *BM*" (defun *bm* (x) x))
(bm-try "define a function named &BM" (defun &bm (x) x))
(bm-try "define a function with the formal *X*" (defun bm-f7 (*x*) *x*))
(bm-try "define a function with the formal &X" (defun bm-f8 (&x) &x))
(bm-try "attach a function to IDENTITY"
        (progn (defstub bm-pick (x) t) (defattach bm-pick identity)))
(bm-try "attach a function to IF"
        (progn (defstub bm-select (x y z) t) (defattach bm-select if)))
(bm-try "define a function with the formal PI" (defun bm-f9 (pi) pi))
(bm-try "define a function with the formal LIST" (defun bm-f10 (list) list))
(bm-try "define a function with a formal of COMMON-LISP that ACL2 does not import"
        (defun bm-f11 (common-lisp::bm-not-imported)
          common-lisp::bm-not-imported))
(bm-try "define a function with an unused formal" (defun bm-f12 (x y) x))
(bm-try "define the same function with the formal declared ignored"
        (defun bm-f12 (x y) (declare (ignore y)) x))
(bm-try "name a theorem by a keyword"
        (defthm :bm-thm (equal x x) :rule-classes nil))
(bm-try "name a theorem by a symbol of COMMON-LISP"
        (defthm constantly (equal x x) :rule-classes nil))
(bm-try "name a theorem T" (defthm t (equal x x) :rule-classes nil))
(bm-try "name a theorem NIL" (defthm nil (equal x x) :rule-classes nil))
(bm-try "name a theorem by the name of a function"
        (defthm binary-append (equal x x) :rule-classes nil))
(bm-try "define a function with the name of a macro" (defun defthmd (x) x))
(bm-try "define a function with the name of a constant"
        (defun *standard-co* (x) x))
(bm-try "name a theorem by the name of the rule of a package"
        (defthm acl2-user-package (equal x x) :rule-classes nil))

; An event that repeats an earlier one.

(defthm bm-t1 (equal (car (cons x y)) x) :rule-classes nil)
(defun bm-d1 (x) (cons x x))

(bm-try "repeat a theorem with the same formula"
        (defthm bm-t1 (equal (car (cons x y)) x) :rule-classes nil))
(bm-try "repeat the name of a theorem with another formula"
        (defthm bm-t1 (equal (cdr (cons x y)) y) :rule-classes nil))
(bm-try "repeat a definition" (defun bm-d1 (x) (cons x x)))
(bm-try "repeat the name of a definition with another body"
        (defun bm-d1 (x) x))

; Axioms inside local or encapsulate.

(bm-try "a local axiom"
        (encapsulate () (local (defaxiom bm-ax1 (equal (car (cons x y)) x)
                                 :rule-classes nil))))
(bm-try "an axiom inside encapsulate"
        (encapsulate () (defaxiom bm-ax2 (equal (car (cons x y)) x)
                          :rule-classes nil)))
(bm-try "an axiom at the top level"
        (defaxiom bm-ax3 (equal (car (cons x y)) x) :rule-classes nil))

; What ACL2 proves by computing.

(bm-try "prove (equal (bad-atom<= 1 2) nil)"
        (thm (equal (bad-atom<= 1 2) nil)))
(bm-try "prove (equal (pkg-imports \"COMMON-LISP\") nil)"
        (thm (equal (pkg-imports "COMMON-LISP") nil)))
(bm-try "prove (equal (symbol-package-name 'car) \"COMMON-LISP\")"
        (thm (equal (symbol-package-name 'car) "COMMON-LISP")))
(bm-try "prove (equal (pkg-witness \"ACL2\") 'acl2-pkg-witness)"
        (thm (equal (pkg-witness "ACL2") 'acl2-pkg-witness)))

; The conclusions of the seven steps of the proof of spec/example, each
; as the disjunction of its literals.

(bm-try "example step 1" (thm (or (equal x nil) x)))
(bm-try "example step 2" (thm (or (equal (equal x x) nil) (equal x x))))
(bm-try "example step 3" (thm (equal (equal x x) t)))
(bm-try "example step 4" (thm (or (equal t nil) (equal x x))))
(bm-try "example step 5" (thm (equal (equal t nil) nil)))
(bm-try "example step 6" (thm (or nil (equal x x))))
(bm-try "example step 7" (thm (equal x x)))

; Packages.

(bm-try "a package that imports two symbols with one name"
        (defpkg "BM-P1" '(common-lisp::car keyword::car)))
(bm-try "a package that imports a symbol named ACL2-PKG-WITNESS"
        (defpkg "BM-P2" '(acl2::acl2-pkg-witness)))
(bm-try "a package with the empty name" (defpkg "" nil))
(bm-try "a package whose name has a lower case letter" (defpkg "Bm-p3" nil))
(bm-try "a package named ACL2 with other imports" (defpkg "ACL2" '(:a)))

(defpkg "BM-P4" '(common-lisp::cons acl2::zebra common-lisp::car keyword::k
                  acl2::apple common-lisp::car))

; Functions introduced by choice.

(defchoose bm-c1 (v) (x y)
  (and (consp v) (equal (car v) x) (not (equal v y))))
(defchoose bm-c2 (v w) (x)
  (and (integerp v) (equal (cons v w) x)))
(defchoose bm-c3 (v) (x)
  (member-equal v x)
  :strengthen t)
(defchoose bm-c4 (v w) (x y)
  (equal (cons v (cons w y)) x)
  :strengthen t)

; Functions introduced by constraint.

(encapsulate
  (((bm-h *) => *))
  (local (defun bm-h (x) (if (consp x) (cdr x) x)))
  (defthm bm-h-twice
    (implies (not (consp x)) (equal (bm-h (bm-h x)) (bm-h x)))))

; A definition that ACL2 admits with a relation other than O<.  The
; relation BM-REL orders the true lists by length, and BM-FN embeds
; them in the ordinals.

(defun bm-mp (x) (true-listp x))
(defun bm-fn (x) (len x))
(defun bm-rel (x y) (< (len x) (len y)))

(defthm bm-rel-well-founded
  (and (implies (bm-mp x) (o-p (bm-fn x)))
       (implies (and (bm-mp x) (bm-mp y) (bm-rel x y))
                (o< (bm-fn x) (bm-fn y))))
  :rule-classes :well-founded-relation)

(bm-try "a rule of class :well-founded-relation that lacks the first conjunct"
        (defthm bm-rel-bad
          (implies (and (bm-mp x) (bm-mp y) (bm-rel x y))
                   (o< (bm-fn x) (bm-fn y)))
          :rule-classes :well-founded-relation))
(bm-try "a second rule of class :well-founded-relation for one relation"
        (defthm bm-rel-again
          (and (o-p (bm-fn x))
               (implies (bm-rel x y) (o< (bm-fn x) (bm-fn y))))
          :rule-classes :well-founded-relation))

(defun bm-rel2 (x y) (< (len x) (len y)))

(bm-try "a rule of class :well-founded-relation in the form with no recognizer"
        (defthm bm-rel2-well-founded
          (and (o-p (bm-fn x))
               (implies (bm-rel2 x y) (o< (bm-fn x) (bm-fn y))))
          :rule-classes :well-founded-relation))
(bm-try "a definition that names a relation with no such rule"
        (defun bm-w0 (x)
          (declare (xargs :well-founded-relation bm-mp :measure x))
          (if (consp x) (bm-w0 (cdr x)) 0)))

(defun bm-w (x)
  (declare (xargs :well-founded-relation bm-rel
                  :measure (true-list-fix x)))
  (if (consp x) (cons (car x) (bm-w (cdr x))) nil))

(bm-try "the same body with the relation O< and the embedded measure"
        (defun bm-w1 (x)
          (declare (xargs :measure (bm-fn (true-list-fix x))))
          (if (consp x) (cons (car x) (bm-w1 (cdr x))) nil)))

; Ruler-extenders.  BM-R1 ends only because a test inside an argument
; of CONS rules its call.

(bm-try "a recursion ruled by a test inside an argument, with the default ruler-extenders"
        (defun bm-r0 (x)
          (cons 1 (if (consp x) (bm-r0 (cdr x)) nil))))

(defun bm-r1 (x)
  (declare (xargs :ruler-extenders :all))
  (cons 1 (if (consp x) (bm-r1 (cdr x)) nil)))

(defun bm-r2 (x)
  (declare (xargs :ruler-extenders :lambdas))
  (let ((y (if (consp x) (bm-r2 (cdr x)) nil)))
    (cons 1 y)))

; Calls that ACL2 measures and calls that it does not.

(bm-try "a recursion in the first argument of PROG2$ that does not end"
        (defun bm-g0 (x)
          (declare (xargs :measure (acl2-count x)))
          (prog2$ (bm-g0 x) x)))

(defun bm-g1 (x)
  (declare (xargs :guard (natp x) :measure (nfix x) :verify-guards nil))
  (mbe :logic (if (zp x) 0 (bm-g1 (- x 1)))
       :exec (if (eql x 0) 0 (bm-g1 (- x 1)))))

; Recursion inside a quoted lambda of a loop$.

(defun bm-l1 (x)
  (declare (xargs :loop$-recursion t :measure (acl2-count x)))
  (if (consp x) (loop$ for e in x sum (bm-l1 e)) 1))

(bm-try "a recursion inside a loop$ that does not end"
        (defun bm-l2 (x)
          (declare (xargs :loop$-recursion t :measure (acl2-count x)))
          (if (consp x) (loop$ for e in (cons x x) sum (bm-l2 e)) 1)))

; Attachments.

(defstub bm-s (x) t)
(defun bm-s-impl (x) (declare (xargs :guard t)) (cons x x))
(defattach bm-s bm-s-impl)
(defun bm-s-user (x) (declare (xargs :guard t)) (list (bm-s x)))

(bm-try "prove (equal (bm-s 3) '(3 . 3)) while BM-S has an attachment"
        (thm (equal (bm-s 3) '(3 . 3))))
(bm-try "a constant whose value needs an attachment"
        (defconst *bm-s* (bm-s 3)))
(bm-try "attach a function to a function that has a definition"
        (defattach bm-s-user bm-s-impl))

; A function that ACL2 runs through a function whose constraint it does
; not record: APPLY$ on a function with a warrant.

(include-book "projects/apply/top" :dir :system)

(defun bm-sq (x) (declare (xargs :guard (acl2-numberp x))) (* x x))
(defwarrant bm-sq)

(bm-try "prove (equal (apply$ 'bm-sq '(3)) 9) with no hypothesis"
        (thm (equal (apply$ 'bm-sq '(3)) 9)))
(bm-try "prove it under the hypothesis of the warrant"
        (thm (implies (warrant bm-sq) (equal (apply$ 'bm-sq '(3)) 9))))

; A hidden package.

(bm-try "prove what a hidden package imports"
        (thm (equal (pkg-imports "BM-HIDDEN")
                    '(bm-hidden-import car))))
(bm-try "declare a hidden package openly with the same imports"
        (defpkg "BM-HIDDEN" '(common-lisp::car acl2::bm-hidden-import)))

; The axioms give to a proof what the evaluator refuses to compute.

(bm-try "prove (equal (symbol-package-name (pkg-witness \"\")) \"ACL2\") from the axiom"
        (thm (equal (symbol-package-name (pkg-witness "")) "ACL2")
             :hints (("Goal"
                      :in-theory (disable symbol-package-name-pkg-witness-name)
                      :use ((:instance symbol-package-name-pkg-witness-name
                                       (pkg-name "")))))))

(program)

; The walk of spec/logic.md, section 6, which finds the calls that must
; be measured and the tests that rule each.  NAMES are the functions of
; the definition and RULERS its ruler-extenders.
;
; Each record of the walk is a list (LITS CALL ATESTS ACALL).  LITS and
; CALL are what the specification says: the literals that the rulers
; give, and the call with the substitution applied.  ATESTS and ACALL
; are the same things as ACL2 writes them, with ACL2's own functions
; applied at the same places: REMOVE-GUARD-HOLDERS-WEAK and SUBLIS-VAR
; to a test, ADD-TEST-SMART and DUMB-NEGATE-LIT as a test is added, and
; SUBLIS-VAR to a call.  They are kept so that the walk can be compared
; with ACL2's termination machine.

(mutual-recursion

 (defun bm-subst (alist term)
   (cond ((variablep term)
          (let ((pair (assoc-eq term alist)))
            (if pair (cdr pair) term)))
         ((fquotep term) term)
         (t (cons (ffn-symb term) (bm-subst-lst alist (fargs term))))))

 (defun bm-subst-lst (alist terms)
   (cond ((endp terms) nil)
         (t (cons (bm-subst alist (car terms))
                  (bm-subst-lst alist (cdr terms)))))))

(defun bm-extends (g rulers)
  (or (eq rulers :all) (member-eq g rulers)))

(defun bm-mbe-callp (term)
  (and (eq (ffn-symb term) 'return-last)
       (equal (fargn term 1) ''mbe1-raw)))

; The calls of NAMES in a term, at any depth: a list of pairs of a call
; as the specification writes it and as ACL2 does, the last found first.

(mutual-recursion

 (defun bm-calls (term alist aalist names acc)
   (cond ((variablep term) acc)
         ((fquotep term) acc)
         ((flambda-applicationp term)
          (bm-calls (lambda-body (ffn-symb term))
                    (pairlis$ (lambda-formals (ffn-symb term))
                              (bm-subst-lst alist (fargs term)))
                    (pairlis$ (lambda-formals (ffn-symb term))
                              (sublis-var-lst aalist (fargs term)))
                    names
                    (bm-calls-lst (fargs term) alist aalist names acc)))
         ((bm-mbe-callp term)
          (bm-calls (fargn term 3) alist aalist names acc))
         (t (bm-calls-lst
             (fargs term) alist aalist names
             (if (and (member-eq (ffn-symb term) names)
                      (not (assoc-equal (bm-subst alist term) acc)))
                 (cons (cons (bm-subst alist term) (sublis-var aalist term))
                       acc)
               acc)))))

 (defun bm-calls-lst (terms alist aalist names acc)
   (cond ((endp terms) acc)
         (t (bm-calls-lst (cdr terms) alist aalist names
                          (bm-calls (car terms) alist aalist names acc))))))

(defun bm-records (pairs lits atests acc)
  (cond ((endp pairs) acc)
        (t (bm-records (cdr pairs) lits atests
                       (cons (list lits (car (car pairs))
                                   (reverse atests) (cdr (car pairs)))
                             acc)))))

(mutual-recursion

 (defun bm-machine (term lits atests alist aalist names rulers acc)
   (cond
    ((variablep term) acc)
    ((fquotep term) acc)
    ((flambda-applicationp term)
     (bm-machine
      (lambda-body (ffn-symb term))
      lits atests
      (pairlis$ (lambda-formals (ffn-symb term))
                (bm-subst-lst alist (fargs term)))
      (pairlis$ (lambda-formals (ffn-symb term))
                (sublis-var-lst aalist (fargs term)))
      names rulers
      (if (bm-extends :lambdas rulers)
          (bm-machine-lst (fargs term) lits atests alist aalist names rulers
                          acc)
        (bm-records (reverse (bm-calls-lst (fargs term) alist aalist names
                                           nil))
                    lits atests acc))))
    ((eq (ffn-symb term) 'if)
     (let* ((a (bm-subst alist (fargn term 1)))
            (at (sublis-var aalist
                            (remove-guard-holders-weak (fargn term 1) nil)))
            (acc (if (bm-extends 'if rulers)
                     (bm-machine (fargn term 1) lits atests alist aalist
                                 names rulers acc)
                   (bm-records (reverse (bm-calls (fargn term 1) alist aalist
                                                  names nil))
                               lits atests acc)))
            (acc (bm-machine (fargn term 2)
                             (append lits (list (list 'not a)))
                             (add-test-smart at atests)
                             alist aalist names rulers acc)))
       (bm-machine (fargn term 3)
                   (append lits (list a))
                   (add-test-smart (dumb-negate-lit at) atests)
                   alist aalist names rulers acc)))
    ((bm-mbe-callp term)
     (bm-machine (fargn term 3) lits atests alist aalist names rulers acc))
    ((bm-extends (ffn-symb term) rulers)
     (bm-machine-lst
      (fargs term) lits atests alist aalist names rulers
      (if (member-eq (ffn-symb term) names)
          (cons (list lits (bm-subst alist term)
                      (reverse atests) (sublis-var aalist term))
                acc)
        acc)))
    (t (bm-records (reverse (bm-calls term alist aalist names nil))
                   lits atests acc))))

 (defun bm-machine-lst (terms lits atests alist aalist names rulers acc)
   (cond ((endp terms) acc)
         (t (bm-machine-lst
             (cdr terms) lits atests alist aalist names rulers
             (bm-machine (car terms) lits atests alist aalist names rulers
                         acc))))))

; The records of one function of a definition, in the order of the walk.

(defun bm-machine-for (fn names rulers wrld)
  (let ((formals (formals fn wrld)))
    (reverse (bm-machine (getpropc fn 'unnormalized-body nil wrld)
                         nil nil (pairlis$ formals formals) nil
                         names rulers nil))))

; The obligations of a definition: MEASURES pairs each function with its
; measure.  A clause that repeats an earlier one is left out.

(defun bm-call-clauses (records m measures wrld)
  (cond ((endp records) nil)
        (t (let* ((call (cadr (car records)))
                  (callee (ffn-symb call)))
             (cons (append (car (car records))
                           (list (list 'o<
                                       (bm-subst (pairlis$ (formals callee wrld)
                                                           (fargs call))
                                                 (cdr (assoc-eq callee
                                                                measures)))
                                       m)))
                   (bm-call-clauses (cdr records) m measures wrld))))))

(defun bm-o-p-clauses (measures)
  (cond ((endp measures) nil)
        (t (cons (list (list 'o-p (cdr (car measures))))
                 (bm-o-p-clauses (cdr measures))))))

(defun bm-all-call-clauses (fns names rulers measures wrld)
  (cond ((endp fns) nil)
        (t (append (bm-call-clauses (bm-machine-for (car fns) names rulers
                                                    wrld)
                                    (cdr (assoc-eq (car fns) measures))
                                    measures wrld)
                   (bm-all-call-clauses (cdr fns) names rulers measures
                                        wrld)))))

(defun bm-first-copies (clauses seen)
  (cond ((endp clauses) (reverse seen))
        ((member-equal (car clauses) seen)
         (bm-first-copies (cdr clauses) seen))
        (t (bm-first-copies (cdr clauses) (cons (car clauses) seen)))))

(defun bm-obligations-for (names rulers measures wrld)
  (bm-first-copies (append (bm-o-p-clauses measures)
                           (bm-all-call-clauses names names rulers measures
                                                wrld))
                   nil))

(defun bm-obligations (fn m wrld)
  (bm-obligations-for
   (list fn)
   (access justification (getpropc fn 'justification nil wrld)
           :ruler-extenders)
   (list (cons fn m))
   wrld))

; Whether the walk, as ACL2 writes its tests and calls, is ACL2's
; termination machine for FN: the same calls under the same tests.

(defun bm-acl2-view (records)
  (cond ((endp records) nil)
        (t (cons (cons (caddr (car records)) (cadddr (car records)))
                 (bm-acl2-view (cdr records))))))

(defun bm-tests-and-calls-view (tcs)
  (cond ((endp tcs) nil)
        (t (cons (cons (access tests-and-call (car tcs) :tests)
                       (access tests-and-call (car tcs) :call))
                 (bm-tests-and-calls-view (cdr tcs))))))

(defun bm-machine-agrees (fn wrld)
  (let* ((names (getpropc fn 'recursivep nil wrld))
         (rulers (access justification (getpropc fn 'justification nil wrld)
                         :ruler-extenders))
         (mine (bm-acl2-view (bm-machine-for fn names rulers wrld)))
         (theirs (bm-tests-and-calls-view
                  (termination-machine nil nil names (formals fn wrld)
                                       (getpropc fn 'unnormalized-body nil
                                                 wrld)
                                       nil nil rulers))))
    (and (subsetp-equal mine theirs)
         (subsetp-equal theirs mine))))

(defun bm-count-agreeing (fns wrld n bad)
  (cond ((endp fns) (mv n bad))
        ((null (getpropc (car fns) 'justification nil wrld))
         (bm-count-agreeing (cdr fns) wrld n bad))
        ((bm-machine-agrees (car fns) wrld)
         (bm-count-agreeing (cdr fns) wrld (+ 1 n) bad))
        (t (bm-count-agreeing (cdr fns) wrld n (cons (car fns) bad)))))

(defun bm-count-ruled (fns wrld)
  (cond ((endp fns) 0)
        (t (+ (if (getpropc (car fns) 'justification nil wrld) 1 0)
              (bm-count-ruled (cdr fns) wrld)))))

; The rule of spec/language.md, section 5, for a variable.  SPECIALS and
; IMPORTS are the two lists that the ground theory holds: the symbols of
; COMMON-LISP that are never variables, and the imports of the package
; ACL2.

(defun bm-variablep (x specials imports)
  (and (symbolp x)
       (not (eq x t))
       (not (eq x nil))
       (let ((p (symbol-package-name x))
             (s (symbol-name x)))
         (and (not (equal p "KEYWORD"))
              (not (and (not (equal s ""))
                        (eql (char s 0) #\*)
                        (eql (char s (1- (length s))) #\*)))
              (not (and (not (equal s ""))
                        (eql (char s 0) #\&)))
              (or (not (equal p "COMMON-LISP"))
                  (and (not (member-eq x specials))
                       (member-eq x imports)
                       t))))))

(defun bm-count-variable-agreement (xs specials imports n)
  (cond ((endp xs) n)
        (t (bm-count-variable-agreement
            (cdr xs) specials imports
            (if (iff (bm-variablep (car xs) specials imports)
                     (legal-variablep (car xs)))
                (+ 1 n)
              n)))))

(defun bm-all-formals (fns wrld acc)
  (cond ((endp fns) acc)
        (t (bm-all-formals (cdr fns) wrld
                           (union-eq (formals (car fns) wrld) acc)))))

(defun bm-obligation-events (clauses i)
  (cond ((endp clauses) nil)
        (t (cons (list 'defthm
                       (packn (list 'bm-w-obligation- i))
                       (cons 'or (car clauses))
                       :rule-classes nil
                       :hints
                       '(("Goal"
                          :in-theory (disable bm-mp bm-fn bm-rel)
                          :use ((:termination-theorem bm-w)
                                (:instance (:termination-theorem bm-w)
                                           (x (cdr x)))
                                (:instance bm-rel-well-founded
                                           (x (true-list-fix x))
                                           (y (true-list-fix x)))
                                (:instance bm-rel-well-founded
                                           (x (true-list-fix (cdr x)))
                                           (y (true-list-fix x)))))))
                 (bm-obligation-events (cdr clauses) (+ 1 i))))))

(logic)

; ACL2 proves each obligation of the specification for BM-W with the
; measure (bm-fn (true-list-fix x)), using only its own termination
; theorem for BM-W and the theorem of the relation: BM-MP, BM-FN and
; BM-REL are disabled.

(make-event
 (value
  (cons 'progn
        (append
         (bm-obligation-events
          (bm-obligations 'bm-w '(bm-fn (true-list-fix x)) (w state))
          1)
         '((table bm-results
                  "prove the obligations of BM-W from ACL2's conjectures and the relation's theorem"
                  'accepted))))))

(program)

; Counts over the world ACL2 starts with.  A function belongs to that
; world if the number of its event is at most *BM-START*.

(defun bm-all-fns (tail wrld acc)
  (cond ((endp tail) acc)
        ((and (eq (cadar tail) 'formals)
              (not (eq (cddar tail) *acl2-property-unbound*))
              (<= (getpropc (caar tail) 'absolute-event-number 0 wrld)
                  *bm-start*))
         (bm-all-fns (cdr tail) wrld (cons (caar tail) acc)))
        (t (bm-all-fns (cdr tail) wrld acc))))

(defun bm-programp (fn wrld)
  (eq (getpropc fn 'symbol-class nil wrld) :program))

; The functions defined in logic mode.

(defun bm-definitions (fns wrld)
  (cond ((endp fns) nil)
        ((and (not (bm-programp (car fns) wrld))
              (getpropc (car fns) 'unnormalized-body nil wrld))
         (cons (car fns) (bm-definitions (cdr fns) wrld)))
        (t (bm-definitions (cdr fns) wrld))))

(defun bm-count-cliques (fns wrld)
  (cond ((endp fns) 0)
        (t (let ((clique (getpropc (car fns) 'recursivep nil wrld)))
             (+ (if (and (consp clique) (cdr clique)
                         (eq (car fns) (car clique)))
                    1
                  0)
                (bm-count-cliques (cdr fns) wrld))))))

; The functions in logic mode with no definition, the primitives apart.

(defun bm-undefined (fns wrld prims)
  (cond ((endp fns) nil)
        ((and (not (bm-programp (car fns) wrld))
              (not (member-eq (car fns) prims))
              (null (getpropc (car fns) 'unnormalized-body nil wrld)))
         (cons (car fns) (bm-undefined (cdr fns) wrld prims)))
        (t (bm-undefined (cdr fns) wrld prims))))

(defun bm-count-event (fns kind wrld)
  (cond ((endp fns) 0)
        (t (+ (if (eq (car (get-event (car fns) wrld)) kind) 1 0)
              (bm-count-event (cdr fns) kind wrld)))))

(defun bm-count-members (fns lst)
  (cond ((endp fns) 0)
        (t (+ (if (member-eq (car fns) lst) 1 0)
              (bm-count-members (cdr fns) lst)))))

(defun bm-count-prop (fns prop wrld)
  (cond ((endp fns) 0)
        (t (+ (if (getpropc (car fns) prop nil wrld) 1 0)
              (bm-count-prop (cdr fns) prop wrld)))))

; The constraint ACL2 stores for a function introduced by encapsulate:
; the first part of its property CONSTRAINT-LST-ETC, as the "Essay on
; Constraint-lst-etc pairs" in ACL2's source file history-management.lisp
; says.  It is a list of terms; the name of another function of the same
; encapsulate, which holds the list; the mark :UNKNOWN-CONSTRAINTS and the
; functions it may mention; or NIL if ACL2 stores none.

(defun bm-constraint (fn wrld)
  (car (getpropc fn 'constraint-lst-etc nil wrld)))

(defun bm-count-constrained (fns wrld)
  (cond ((endp fns) 0)
        (t (+ (if (bm-constraint (car fns) wrld) 1 0)
              (bm-count-constrained (cdr fns) wrld)))))

(defun bm-programs (fns wrld)
  (cond ((endp fns) nil)
        ((bm-programp (car fns) wrld)
         (cons (car fns) (bm-programs (cdr fns) wrld)))
        (t (bm-programs (cdr fns) wrld))))

; Whether the definitions can stand in an order in which each comes
; after every definition that its body calls, other than those of its
; own clique.  Those whose callees are all placed are placed, again and
; again, and what cannot be placed is returned.

(defun bm-callees (gs clique defs)
  (cond ((endp gs) nil)
        ((and (hons-get (car gs) defs) (not (member-eq (car gs) clique)))
         (cons (car gs) (bm-callees (cdr gs) clique defs)))
        (t (bm-callees (cdr gs) clique defs))))

(defun bm-set (fns acc)
  (cond ((endp fns) acc)
        (t (bm-set (cdr fns) (hons-acons (car fns) t acc)))))

(defun bm-deps (fns defs wrld acc)
  (cond ((endp fns) acc)
        (t (bm-deps
            (cdr fns) defs wrld
            (hons-acons
             (car fns)
             (bm-callees (all-fnnames (getpropc (car fns) 'unnormalized-body
                                                nil wrld))
                         (or (getpropc (car fns) 'recursivep nil wrld)
                             (list (car fns)))
                         defs)
             acc)))))

(defun bm-all-placed (gs placed)
  (or (endp gs)
      (and (hons-get (car gs) placed)
           (bm-all-placed (cdr gs) placed))))

(defun bm-pass (todo deps placed left)
  (cond ((endp todo) (mv placed left))
        ((bm-all-placed (cdr (hons-get (car todo) deps)) placed)
         (bm-pass (cdr todo) deps (hons-acons (car todo) t placed) left))
        (t (bm-pass (cdr todo) deps placed (cons (car todo) left)))))

(defun bm-peel (todo deps placed)
  (mv-let (placed left)
    (bm-pass todo deps placed nil)
    (cond ((or (null left) (= (len left) (len todo))) left)
          (t (bm-peel left deps placed)))))

; The definitions for which ACL2 stores no measure: a measure of the
; form (:? v ...) says only which formals the measure depends on.

(defun bm-count-unknown-measures (fns wrld)
  (cond ((endp fns) 0)
        (t (let ((just (getpropc (car fns) 'justification nil wrld)))
             (+ (if (and just
                         (consp (access justification just :measure))
                         (eq (car (access justification just :measure)) :?))
                    1
                  0)
                (bm-count-unknown-measures (cdr fns) wrld))))))

(defun bm-count-line (what n)
  (bm-line "count" (list what n)))

(defun bm-count-package (pkg fns wrld)
  (cond ((endp fns) 0)
        (t (+ (if (and (not (bm-programp (car fns) wrld))
                       (equal (symbol-package-name (car fns)) pkg))
                  1
                0)
              (bm-count-package pkg (cdr fns) wrld)))))

(defun bm-agreement-lines (fns wrld)
  (let* ((imports (pkg-imports "ACL2"))
         (specials *common-lisp-specials-and-constants*)
         (sample (append imports specials
                         (bm-all-formals fns wrld nil)
                         '(x acl2::* acl2::** acl2::*x* acl2::*x acl2::x*
                           acl2::& acl2::&x acl2::x& acl2::|| :k :*k*
                           bm-p4::q bm-p4::*q* bm-p4::&q bm-p4::zebra
                           common-lisp::bm-not-imported 0 "x" (x)))))
    (mv-let (n bad)
      (bm-count-agreeing fns wrld 0 nil)
      (list
       (bm-line "agrees"
                (list "definitions that call themselves: the walk and ACL2's termination machine"
                      n (bm-count-ruled fns wrld)))
       (bm-line "disagree" (list bad))
       (bm-line "agrees"
                (list "objects: the rule for a variable and ACL2's LEGAL-VARIABLEP"
                      (bm-count-variable-agreement sample specials imports 0)
                      (len sample)))))))

(defun bm-world-lines (wrld)
  (let* ((fns (remove-duplicates-eq (bm-all-fns wrld wrld nil)))
         (prims (strip-cars *primitive-formals-and-guards*))
         (defs (bm-definitions fns wrld))
         (undefined (bm-undefined fns wrld prims))
         (programs (bm-programs fns wrld))
         (defset (bm-set defs nil)))
    (append
     (bm-agreement-lines fns wrld)
     (list
     (bm-count-line "functions defined in logic mode" (len defs))
     (bm-count-line "cliques of more than one function among them"
                    (bm-count-cliques defs wrld))
     (bm-count-line "definitions that cannot stand after all that their bodies call"
                    (len (bm-peel defs (bm-deps defs defset wrld nil) nil)))
     (bm-count-line "definitions whose measure ACL2 does not store"
                    (bm-count-unknown-measures defs wrld))
     (bm-count-line "functions in logic mode with no definition, the primitives apart"
                    (len undefined))
     (bm-count-line "of those, functions that an encapsulate event introduced"
                    (bm-count-event undefined 'encapsulate wrld))
     (bm-count-line "of those, functions for which ACL2 stores no constraint"
                    (- (len undefined)
                       (bm-count-constrained undefined wrld)))
     (bm-count-line "of those, functions with an attachment"
                    (bm-count-prop undefined 'attachment wrld))
     (bm-count-line "functions in program mode" (len programs))
     (bm-count-line "of those, functions whose body the world stores"
                    (bm-count-prop programs 'unnormalized-body wrld))
     (bm-count-line "of those, functions that ACL2 lists as having raw code"
                    (bm-count-members programs
                                      *initial-program-fns-with-raw-code*))
     (bm-count-line "functions in logic mode named by a symbol of COMMON-LISP"
                    (bm-count-package "COMMON-LISP" fns wrld))))))

(defun bm-measure-line (fn wrld)
  (bm-line "measure"
           (list fn (access justification
                            (getpropc fn 'justification nil wrld)
                            :measure))))

(defun bm-calls-line (fn wrld)
  (bm-line "calls"
           (list fn (all-fnnames (getpropc fn 'unnormalized-body nil wrld)))))

(defun bm-well-founded-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (bm-line "well-founded"
                          (list (car (car alist)) (cadr (car alist))))
                 (bm-well-founded-lines (cdr alist))))))

(defun bm-clause-lines-for (fn clauses)
  (cond ((endp clauses) nil)
        (t (cons (bm-line "obligation" (cons fn (car clauses)))
                 (bm-clause-lines-for fn (cdr clauses))))))

(defun bm-relation-lines (wrld)
  (let ((just (getpropc 'bm-w 'justification nil wrld)))
    (append
     (bm-well-founded-lines (global-val 'well-founded-relation-alist wrld))
     (list (bm-line "stored-theorem"
                    (list 'well-founded-l<
                          (if (getpropc 'well-founded-l< 'theorem nil wrld)
                              t
                            nil)))
           (bm-line "justification"
                    (list 'bm-w
                          (access justification just :mp)
                          (access justification just :rel)
                          (access justification just :measure)))
           (bm-line "termination" (list 'bm-w (termination-theorem 'bm-w wrld))))
     (bm-clause-lines-for
      'bm-w
      (bm-obligations 'bm-w '(bm-fn (true-list-fix x)) wrld)))))

(defun bm-example-obligation-lines (fns wrld)
  (cond ((endp fns) nil)
        (t (let ((just (getpropc (car fns) 'justification nil wrld)))
             (append
              (list (bm-line "rulers"
                             (list (car fns)
                                   (access justification just
                                           :ruler-extenders))))
              (bm-clause-lines-for
               (car fns)
               (bm-obligations (car fns) (access justification just :measure)
                               wrld))
              (bm-example-obligation-lines (cdr fns) wrld))))))

(defun bm-attachment-line (fn wrld)
  (bm-line "attachment"
           (list fn (cdr (attachment-pair fn wrld)))))

(defun bm-hidden-line (name wrld)
  (let ((entry (find-package-entry
                name (global-val 'known-package-alist wrld))))
    (bm-line "hidden-package"
             (list name (and entry (package-entry-hidden-p entry) t)))))

(defun bm-kwote-lst (args)
  (cond ((endp args) nil)
        (t (cons (kwote (car args)) (bm-kwote-lst (cdr args))))))

; ACL2's value of each call of CALLS, a list of lists (fn arg ...).

(defun bm-value-lines (calls word state)
  (declare (xargs :stobjs state))
  (cond ((endp calls) nil)
        (t (let ((term (cons (car (car calls))
                             (bm-kwote-lst (cdr (car calls))))))
             (mv-let (erp val)
               (if (eq (car (car calls)) 'if)
                   (mv nil (if (cadr (car calls))
                               (caddr (car calls))
                             (cadddr (car calls))))
                 (magic-ev-fncall (car (car calls)) (cdr (car calls))
                                  state t nil))
               (cons (if erp
                         (bm-line (string-append "no-" word) (list term))
                       (bm-line word (list term val)))
                     (bm-value-lines (cdr calls) word state)))))))

; ACL2's value of each call with attachments in force.

(defun bm-run-lines (calls state)
  (declare (xargs :stobjs state))
  (cond ((endp calls) nil)
        (t (let ((term (cons (car (car calls))
                             (bm-kwote-lst (cdr (car calls))))))
             (mv-let (erp val)
               (magic-ev-fncall (car (car calls)) (cdr (car calls))
                                state t t)
               (cons (if erp
                         (bm-line "no-run" (list term))
                       (bm-line "run" (list term val)))
                     (bm-run-lines (cdr calls) state)))))))

(defconst *bm-attached-calls*
  '((bm-s 3) (bm-s-user 3) (apply$ bm-sq (3)) (bm-sq 3)))

(defconst *bm-hidden-calls*
  '((pkg-imports "BM-HIDDEN") (pkg-witness "BM-HIDDEN")))

(defconst *bm-calls*
  '((acl2-numberp 1) (acl2-numberp 1/2) (acl2-numberp #c(1 2))
    (acl2-numberp a) (acl2-numberp "s")
    (bad-atom<= 1 2) (bad-atom<= a "s")
    (binary-* 2 3) (binary-* 1/2 #c(0 1)) (binary-* a 2) (binary-* 2 "s")
    (binary-* #c(0 1) #c(0 1))
    (binary-+ 2 3) (binary-+ a 2) (binary-+ 2 a) (binary-+ a b)
    (binary-+ 1/2 #c(1 -1/2)) (binary-+ #c(1 2) #c(1 -2))
    (unary-- 3) (unary-- a) (unary-- #c(1 2)) (unary-- -1/2)
    (unary-/ 2) (unary-/ 0) (unary-/ a) (unary-/ #c(0 1)) (unary-/ -1/3)
    (< 1 2) (< 2 1) (< 1 1) (< #c(1 2) #c(1 3)) (< #c(1 3) 2) (< 2 #c(1 3))
    (< a 1) (< 1 a) (< "s" -1) (< -1 "s") (< #c(0 1) a)
    (car (1 . 2)) (car a) (car nil) (cdr (1 . 2)) (cdr a) (cdr nil)
    (char-code #\a) (char-code 7) (char-code a)
    (characterp #\a) (characterp 97)
    (code-char 97) (code-char 0) (code-char 255) (code-char 256)
    (code-char -1) (code-char 1/2) (code-char a)
    (complex 1 2) (complex 1 0) (complex a 2) (complex 1 a) (complex 1/2 -1/3)
    (complex 1 #c(1 2)) (complex #c(1 2) 1)
    (complex-rationalp #c(1 2)) (complex-rationalp 1) (complex-rationalp a)
    (coerce "ab" list) (coerce (#\a #\b) string) (coerce 7 list)
    (coerce a list) (coerce (1 #\a) string) (coerce "ab" foo) (coerce "ab" 7)
    (coerce ((#\a) . 7) string) (coerce nil string) (coerce "" list)
    (cons 1 2) (consp (1)) (consp nil) (consp a)
    (denominator 3/4) (denominator -3/4) (denominator 5) (denominator a)
    (denominator #c(1 2))
    (equal 1 1) (equal 1 2) (equal a a) (equal "a" a) (equal (1 2) (1 2))
    (if nil 1 2) (if 0 1 2) (if t 1 2)
    (imagpart #c(1 2)) (imagpart 3) (imagpart a)
    (integerp 1) (integerp -1) (integerp 1/2) (integerp a)
    (intern-in-package-of-symbol "CAR" acl2::foo)
    (intern-in-package-of-symbol "FOO" car)
    (intern-in-package-of-symbol "FOO" acl2::bar)
    (intern-in-package-of-symbol "X" :k)
    (intern-in-package-of-symbol "abc" acl2::foo)
    (intern-in-package-of-symbol "" acl2::foo)
    (intern-in-package-of-symbol "CAR" bm-p4::q)
    (intern-in-package-of-symbol "ZEBRA" bm-p4::q)
    (intern-in-package-of-symbol "CDR" bm-p4::q)
    (intern-in-package-of-symbol a acl2::foo)
    (intern-in-package-of-symbol "X" 3)
    (numerator 3/4) (numerator -3/4) (numerator 5) (numerator a)
    (numerator #c(1 2))
    (pkg-imports "KEYWORD") (pkg-imports "COMMON-LISP") (pkg-imports "BM-P4")
    (pkg-imports 3) (pkg-imports a) (pkg-imports "BM-NO-SUCH-PACKAGE")
    (pkg-imports "")
    (pkg-witness "ACL2") (pkg-witness "KEYWORD") (pkg-witness "COMMON-LISP")
    (pkg-witness "BM-P4") (pkg-witness "BM-NO-SUCH-PACKAGE") (pkg-witness "")
    (pkg-witness 7) (pkg-witness a)
    (rationalp 1/2) (rationalp 1) (rationalp #c(1 2)) (rationalp a)
    (realpart #c(1 2)) (realpart 3) (realpart a)
    (stringp "a") (stringp a)
    (symbol-name car) (symbol-name :k) (symbol-name 3) (symbol-name "s")
    (symbol-name nil)
    (symbol-package-name car) (symbol-package-name acl2::foo)
    (symbol-package-name :k) (symbol-package-name 3)
    (symbol-package-name nil) (symbol-package-name t)
    (symbol-package-name bm-p4::q) (symbol-package-name bm-p4::zebra)
    (symbolp a) (symbolp "a") (symbolp nil) (symbolp 1)))

(defun bm-event-lines (names)
  (cond ((endp names) nil)
        (t (cons (bm-line "event" (list (car names)))
                 (bm-event-lines (cdr names))))))

(defun bm-result-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (bm-line (if (eq (cdr (car alist)) 'refused)
                              "refused"
                            "accepted")
                          (list (car (car alist))))
                 (bm-result-lines (cdr alist))))))

; The axiom of spec/logic.md for a function introduced by choice, and a
; comparison with the axiom ACL2 holds.  Both are compared after every
; lambda application in them has been replaced by its body with the
; actuals put for the formals.

(mutual-recursion

 (defun bm-beta (term)
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((flambda-applicationp term)
          (bm-beta (subcor-var (lambda-formals (ffn-symb term))
                               (fargs term)
                               (lambda-body (ffn-symb term)))))
         (t (cons (ffn-symb term) (bm-beta-lst (fargs term))))))

 (defun bm-beta-lst (terms)
   (cond ((endp terms) nil)
         (t (cons (bm-beta (car terms)) (bm-beta-lst (cdr terms)))))))

(defun bm-choose-terms (k i call)
  (cond ((= i k) nil)
        (t (cons (list 'mv-nth (kwote i) call)
                 (bm-choose-terms k (+ 1 i) call)))))

(defun bm-choose-axiom (fn bound free body free2)
  (let* ((call (cons fn free))
         (terms (if (cdr bound)
                    (bm-choose-terms (len bound) 0 call)
                  (list call)))
         (inst (subcor-var bound terms body))
         (basic0 (list 'implies body inst))
         (basic (if (cdr bound)
                    (list 'if (list 'true-listp call) basic0 ''nil)
                  basic0)))
    (if (null free2)
        basic
      (let* ((call2 (cons fn free2))
             (terms2 (if (cdr bound)
                         (bm-choose-terms (len bound) 0 call2)
                       (list call2)))
             (body2 (subcor-var free free2 body))
             (d1 (list 'equal call call2))
             (d2 (list 'if inst
                       (list 'not (subcor-var bound terms body2))
                       ''nil))
             (d3 (list 'if (subcor-var bound terms2 body2)
                       (list 'not (subcor-var bound terms2 body))
                       ''nil)))
        (list 'if basic
              (list 'if d1 d1 (list 'if d2 d2 d3))
              ''nil)))))

; The second list of variables of a strengthened axiom, read from the
; axiom ACL2 holds: the arguments of the second call in its equality.

(defun bm-free2 (axiom)
  (case-match axiom
    (('if & ('if ('equal & (& . free2)) . &) ''nil) free2)
    (& nil)))

(defun bm-choose-line (fn bound free body strengthen wrld)
  (let* ((axiom (getpropc fn 'defchoose-axiom nil wrld))
         (free2 (and strengthen (bm-free2 axiom))))
    (bm-line "choose"
             (list fn
                   (and axiom
                        (or (not strengthen) (consp free2))
                        (equal (bm-beta axiom)
                               (bm-beta (bm-choose-axiom fn bound free body
                                                         free2))))))))

(defun bm-facts-lines (state)
  (declare (xargs :stobjs state))
  (let ((wrld (w state)))
    (append
     (bm-event-lines (primitive-event-macros))
     (bm-result-lines (reverse (table-alist 'bm-results wrld)))
     (list (bm-line "package" (list "BM-P4" (pkg-imports "BM-P4")))
           (bm-line "package" (list "ACL2-PC" (pkg-imports "ACL2-PC")))
           (bm-line "package" (list "BIB" (pkg-imports "BIB")))
           (bm-line "packages" (list *bm-packages*))
           (bm-line "imports" (list "ACL2" (len (pkg-imports "ACL2"))))
           (bm-line "imports" (list "ACL2-USER" (len (pkg-imports "ACL2-USER"))))
           (bm-choose-line 'bm-c1 '(v) '(x y)
                           '(if (consp v)
                                (if (equal (car v) x) (not (equal v y)) 'nil)
                              'nil)
                           nil wrld)
           (bm-choose-line 'bm-c2 '(v w) '(x)
                           '(if (integerp v) (equal (cons v w) x) 'nil)
                           nil wrld)
           (bm-choose-line 'bm-c3 '(v) '(x) '(member-equal v x) t wrld)
           (bm-choose-line 'bm-c4 '(v w) '(x y)
                           '(equal (cons v (cons w y)) x) t wrld)
           (bm-line "choose-axiom"
                    (list 'bm-c1 (getpropc 'bm-c1 'defchoose-axiom nil wrld)))
           (bm-line "choose-axiom"
                    (list 'bm-c2 (getpropc 'bm-c2 'defchoose-axiom nil wrld)))
           (bm-line "constraint"
                    (list 'bm-h (bm-constraint 'bm-h wrld))))
     (bm-relation-lines wrld)
     (bm-example-obligation-lines '(bm-r1 bm-r2 bm-g1 bm-l1) wrld)
     (list (bm-line "termination"
                    (list 'bm-l1 (termination-theorem 'bm-l1 wrld))))
     (list (bm-attachment-line 'bm-s wrld)
           (bm-attachment-line 'apply$-userfn wrld)
           (bm-line "constraint"
                    (list 'doppelganger-apply$-userfn
                          (bm-constraint 'doppelganger-apply$-userfn wrld)))
           (bm-hidden-line "BM-HIDDEN" wrld)
           (bm-hidden-line "BM-P4" wrld))
     (bm-value-lines *bm-hidden-calls* "plain" state)
     (bm-run-lines *bm-attached-calls* state)
     (bm-value-lines *bm-attached-calls* "plain" state)
     (bm-world-lines wrld)
     (list (bm-measure-line 'len wrld)
           (bm-measure-line 'apply$ wrld)
           (bm-measure-line 'ev$ wrld)
           (bm-measure-line 'acl2-count wrld)
           (bm-calls-line 'acl2-count wrld)
           (bm-calls-line 'length wrld))
     (bm-value-lines *bm-calls* "value" state))))

(bm-write-file (bm-facts-lines state) "build/facts.txt" state)

(cw "facts: ~x0 lines written~%" (len (bm-facts-lines state)))

(good-bye)
