; The exporter of PLAN.md, step 2.  It writes, in the formats of
; spec/formats.md, what ACL2's world holds for a range of its events:
; the statements, the program text for a runner, and, for a book, the
; prover's aids.  export/book.sh, which export/run.sh calls, loads
; checks/canon.lsp, the printer of the formats, and then this file, into
; ACL2 after the world to be exported is in place, and calls
; BX-EXPORT-LIBRARY or BX-EXPORT-BOOK.
;
; Every statement is taken from the properties that ACL2 stores, after it
; has processed the events, under each name that an event introduced:
;
;   define       the formals, the stored body (UNNORMALIZED-BODY), and the
;                ruler-extenders of the stored JUSTIFICATION, or NIL where
;                ACL2 stores none because the function does not call itself
;   constrain    the functions that share the constraint (SIBLINGS), their
;                numbers of formals, and the formulas of the constraint
;                (CONSTRAINT-INFO, from the property CONSTRAINT-LST-ETC),
;                each formula named by the event of the encapsulate that
;                states it; where ACL2 records no constraint, the
;                theorems of the encapsulate about its functions
;   choose       the stored axiom (DEFCHOOSE-AXIOM), from which the bound
;                variables, the body and the second list of free variables
;                are read; the axiom that spec/logic.md builds from them
;                must be the stored one, or no statement is written
;   theorem      the stored formula (THEOREM) of a DEFTHM event
;   axiom        the stored formula of a DEFAXIOM event
;   package      the imports that ACL2's axiom NAME-PACKAGE gives
;   hidden-package  the imports that ACL2 keeps for a hidden package
;   reserve      a name under which ACL2 holds a macro, a constant, a
;                label, a theory or a single-threaded object
;
; A book's statements stand in the order of ACL2's events, with one
; change: the constraint of an encapsulate stands after the events inside
; it that are not part of the constraint, since those cannot mention the
; functions it introduces and its formulas may mention theirs.  The
; library's statements are ordered by section 7.
;
; What cannot be written as the specification asks is recorded in a note
; (see BX-NOTE), and the notes are written beside the files.

(in-package "ACL2")

(program)
(set-state-ok t)

;;; 1. Small tools

(defun bx-names (namex)
  (cond ((eql namex 0) nil)
        ((or (symbolp namex) (stringp namex)) (list namex))
        (t namex)))

(defun bx-note (key data)
  (list :note key data))

(defun bx-stmt (word args)
  (list :stmt word args))

(defun bx-prog (word args)
  (list :prog word args))

(defun bx-function-p (sym wrld)

; Whether SYM is a function.  The formals of a function of no arguments
; are NIL, so the test is whether the property is present at all.

  (not (eq (getpropc sym 'formals t wrld) t)))

(defun bx-in-use-p (sym wrld)

; Whether ACL2 holds SYM as a name of any kind.

  (or (bx-function-p sym wrld)
      (getpropc sym 'theorem nil wrld)
      (getpropc sym 'macro-body nil wrld)
      (getpropc sym 'const nil wrld)
      (getpropc sym 'label nil wrld)
      (getpropc sym 'theory nil wrld)
      (getpropc sym 'stobj nil wrld)
      (getpropc sym 'stobj-live-var nil wrld)))

; The kinds of name with no logical content.  The last is the variable
; that holds a single-threaded object while ACL2 runs, which the event
; that introduces the object takes as a name.

(defun bx-reserve-kind-p (sym wrld)
  (or (getpropc sym 'macro-body nil wrld)
      (getpropc sym 'const nil wrld)
      (getpropc sym 'label nil wrld)
      (getpropc sym 'theory nil wrld)
      (getpropc sym 'stobj nil wrld)
      (getpropc sym 'stobj-live-var nil wrld)))

; Whether a function shares the constraint of an encapsulate.  ACL2 holds
; the constraint as the property CONSTRAINT-LST-ETC, a pair (X . ORIGINS),
; where X is the list of the formulas, a symbol naming the function that
; holds them, or a mark of unknown constraints; a function with no such
; property is defined, or introduced by choice, outside any constraint.
; This is how ACL2's source reads it (its "Essay on Constraint-lst-etc
; pairs").

(defun bx-constrained-p (fn wrld)
  (not (eq (car (getpropc fn 'constraint-lst-etc '(t . nil) wrld)) t)))

(defun bx-programp (fn wrld)
  (eq (getpropc fn 'symbol-class nil wrld) :program))

(defun bx-rulers (fn wrld)
  (let ((just (getpropc fn 'justification nil wrld)))
    (and just (access justification just :ruler-extenders))))

(defun bx-event-number (name wrld)
  (getpropc name 'absolute-event-number 0 wrld))

; The name given to a formula of a constraint that has no name of its own
; in ACL2.  The definition of a function defined inside the encapsulate,
; and the axiom of a function introduced there by choice, ACL2 holds under
; the function's name; but spec/logic.md lets no line introduce one name
; twice.  A corollary that a rule class of a theorem adds to the
; constraint has no name.  Such a formula is named by the function's name
; followed by the word "definition" or "choice", or by the name of the
; constraint followed by "constraint" and the formula's position, in the
; package of that name, with a number added if the name is in use.

(defun bx-fresh-name (base i fn wrld)
  (let ((sym (intern-in-package-of-symbol
              (if (= i 0)
                  base
                (concatenate 'string base " "
                             (coerce (explode-nonnegative-integer i 10 nil)
                                     'string)))
              fn)))
    (if (bx-in-use-p sym wrld)
        (bx-fresh-name base (+ i 1) fn wrld)
      sym)))

(defun bx-formula-name (fn word wrld)
  (bx-fresh-name (concatenate 'string (symbol-name fn) " " word) 0 fn wrld))

(defun bx-add-names (names table)
  (cond ((endp names) table)
        (t (bx-add-names (cdr names) (hons-acons (car names) t table)))))

; The functions a statement introduces, and the functions its terms call.

(defun bx-bodies (defs)
  (cond ((endp defs) nil)
        (t (cons (caddr (car defs)) (bx-bodies (cdr defs))))))

(defun bx-introduced (stmt)
  (let ((word (car stmt)) (args (cadr stmt)))
    (cond ((equal word "define") (strip-cars (cdr args)))
          ((equal word "constrain") (strip-cars (car args)))
          ((equal word "choose") (list (car args)))
          (t nil))))

(defun bx-used (stmt)
  (let ((word (car stmt)) (args (cadr stmt)))
    (cond ((equal word "define")
           (set-difference-eq (all-fnnames-lst (bx-bodies (cdr args)))
                              (strip-cars (cdr args))))
          ((equal word "constrain")
           (set-difference-eq (all-fnnames-lst (strip-cadrs (cadr args)))
                              (strip-cars (car args))))
          ((equal word "choose") (all-fnnames (cadddr args)))
          ((member-equal word '("theorem" "axiom")) (all-fnnames (cadr args)))
          (t nil))))

;;; 2. The events of a range of the world

; The event tuples of WRLD whose numbers are above LO and at most HI,
; oldest first.

(defun bx-events (wrld lo hi acc)
  (cond ((endp wrld) acc)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value))
         (let* ((ev (cddar wrld))
                (n (access-event-tuple-number ev)))
           (cond ((not (integerp n)) acc)
                 ((<= n lo) acc)
                 ((< hi n) (bx-events (cdr wrld) lo hi acc))
                 (t (bx-events (cdr wrld) lo hi (cons ev acc))))))
        (t (bx-events (cdr wrld) lo hi acc))))

; The name under which ACL2 stores the constraint of an encapsulate event
; with a signature, or NIL.

(defun bx-constrainer (ev wrld)
  (and (eq (access-event-tuple-type ev) 'encapsulate)
       (consp (access-event-tuple-namex ev))
       (mv-let (name lst origins)
         (constraint-info (car (access-event-tuple-namex ev)) wrld)
         (declare (ignore lst origins))
         name)))

; Each event is paired with the constrainer of the innermost encapsulate
; with a signature that contains it.  An encapsulate's own event stands
; after the events inside it, which have a greater depth.  EVS is newest
; first, STACK holds pairs (depth . constrainer) of the encapsulates whose
; events are being passed, and the result is oldest first.

(defun bx-pop (stack d)
  (cond ((endp stack) nil)
        ((<= d (car (car stack))) (bx-pop (cdr stack) d))
        (t stack)))

(defun bx-first-constrainer (stack)
  (cond ((endp stack) nil)
        ((cdr (car stack)) (cdr (car stack)))
        (t (bx-first-constrainer (cdr stack)))))

(defun bx-enclose (evs stack acc wrld)
  (cond ((endp evs) acc)
        (t (let* ((ev (car evs))
                  (d (access-event-tuple-depth ev))
                  (stack (bx-pop stack d))
                  (encl (bx-first-constrainer stack))
                  (stack (if (eq (access-event-tuple-type ev) 'encapsulate)
                             (cons (cons d (bx-constrainer ev wrld)) stack)
                           stack)))
             (bx-enclose (cdr evs) stack (cons (cons ev encl) acc) wrld)))))

;;; 3. Terms

(mutual-recursion

 (defun bx-beta (term)
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((flambda-applicationp term)
          (bx-beta (subcor-var (lambda-formals (ffn-symb term))
                               (fargs term)
                               (lambda-body (ffn-symb term)))))
         (t (cons (ffn-symb term) (bx-beta-lst (fargs term))))))

 (defun bx-beta-lst (terms)
   (cond ((endp terms) nil)
         (t (cons (bx-beta (car terms)) (bx-beta-lst (cdr terms)))))))

; The body that ACL2 runs for a function in program mode: each mbe is
; replaced by its executable half, that is, each call (return-last
; 'mbe1-raw EXEC LOGIC) by EXEC, since ACL2 runs such a function as its
; Common Lisp code (spec/language.md, section 7).

(mutual-recursion

 (defun bx-exec (term)
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((and (eq (ffn-symb term) 'return-last)
               (equal (fargn term 1) ''mbe1-raw))
          (bx-exec (fargn term 2)))
         ((flambda-applicationp term)
          (cons (list 'lambda (lambda-formals (ffn-symb term))
                      (bx-exec (lambda-body (ffn-symb term))))
                (bx-exec-lst (fargs term))))
         (t (cons (ffn-symb term) (bx-exec-lst (fargs term))))))

 (defun bx-exec-lst (terms)
   (cond ((endp terms) nil)
         (t (cons (bx-exec (car terms)) (bx-exec-lst (cdr terms)))))))

;;; 4. Functions introduced by choice

; The axiom of spec/logic.md, section 6, for (choose FN BOUND FREE BODY
; FREE2).

(defun bx-mv-nths (k i call)
  (cond ((= i k) nil)
        (t (cons (list 'mv-nth (kwote i) call)
                 (bx-mv-nths k (+ 1 i) call)))))

(defun bx-choose-axiom (fn bound free body free2)
  (let* ((call (cons fn free))
         (terms (if (cdr bound) (bx-mv-nths (len bound) 0 call) (list call)))
         (inst (subcor-var bound terms body))
         (basic0 (list 'implies body inst))
         (basic (if (cdr bound)
                    (list 'if (list 'true-listp call) basic0 ''nil)
                  basic0)))
    (if (null free2)
        basic
      (let* ((call2 (cons fn free2))
             (terms2 (if (cdr bound)
                         (bx-mv-nths (len bound) 0 call2)
                       (list call2)))
             (body2 (subcor-var free free2 body))
             (d1 (list 'equal call call2))
             (d2 (list 'if inst
                       (list 'not (subcor-var bound terms body2))
                       ''nil))
             (d3 (list 'if (subcor-var bound terms2 body2)
                       (list 'not (subcor-var bound terms2 body))
                       ''nil)))
        (list 'if basic (list 'if d1 d1 (list 'if d2 d2 d3)) ''nil)))))

; Reading BOUND, BODY and FREE2 from the axiom ACL2 stores.  The basic
; axiom is (implies BODY ((lambda VARS BODY) . ACTUALS)), where the bound
; variable is the formal whose actual is the call of FN; or, with several
; bound variables, (if (true-listp CALL) (implies BODY ((lambda (MV . R)
; ((lambda VARS BODY) . ACTUALS)) CALL . R)) 'nil), where the bound
; variables are the formals whose actuals are (mv-nth 'I MV), in the order
; of I.  A strengthened axiom is (if BASIC (if (equal CALL CALL2) ...)
; 'nil), and FREE2 is the arguments of CALL2.

(defun bx-bound-one (formals actuals call)
  (cond ((endp formals) nil)
        ((equal (car actuals) call) (list (car formals)))
        (t (bx-bound-one (cdr formals) (cdr actuals) call))))

(defun bx-bound-index (formals actuals mv i)
  (cond ((endp formals) nil)
        ((equal (car actuals) (list 'mv-nth (kwote i) mv)) (car formals))
        (t (bx-bound-index (cdr formals) (cdr actuals) mv i))))

(defun bx-bound-many (formals actuals mv i)
  (let ((v (bx-bound-index formals actuals mv i)))
    (if v
        (cons v (bx-bound-many formals actuals mv (+ i 1)))
      nil)))

(defun bx-choose-parts (axiom fn wrld)

; Returns (mv bound body free2), or (mv nil nil nil) if the axiom is not
; of a form above.

  (mv-let (basic free2)
    (case-match axiom
      (('if basic ('if ('equal (!fn . &) (!fn . free2)) . &) ''nil)
       (mv basic free2))
      (& (mv axiom nil)))
    (case-match basic
      (('implies body (('lambda vars &) . actuals))
       (mv (bx-bound-one vars actuals (cons fn (formals fn wrld))) body free2))
      (('if ('true-listp &) ('implies body (('lambda (mv . &) inner) . &)) ''nil)
       (case-match inner
         ((('lambda vars &) . actuals)
          (mv (bx-bound-many vars actuals mv 0) body free2))
         (& (mv nil nil nil))))
      (& (mv nil nil nil)))))

;;; 5. The items of one event

; An item is (:stmt WORD ARGS), a statement; (:prog WORD ARGS), a line of
; program text only; or (:note KEY DATA).  A definition in logic mode is
; both a statement and a line of program text.

; The definitions of an event form, each (NAME FORMALS ... BODY).

(defun bx-defun-forms (form)
  (case (car form)
    (defun (list (cdr form)))
    (defuns (cdr form))
    (mutual-recursion (strip-cdrs (cdr form)))
    (otherwise nil)))

; A function in program mode whose body the world does not store, as in
; the world ACL2 starts with: its body is translated from the event that
; defined it.  The result is (mv body-or-nil note-or-nil).

(defun bx-program-body (fn form wrld)
  (let ((body (getpropc fn 'unnormalized-body nil wrld)))
    (cond
     (body (mv body nil))
     ((member-eq fn *initial-program-fns-with-raw-code*)
      (mv nil (bx-note "program function with raw code" fn)))
     (t (let ((def (assoc-eq fn (bx-defun-forms form))))
          (if (null def)
              (mv nil (bx-note "program function whose event has no defun" fn))
            (mv-let (erp val)
              (translate-cmp (car (last def)) t nil t 'bx-program-body wrld
                             (default-state-vars nil :temp-touchable-fns t
                                                 :temp-touchable-vars t))
              (if erp
                  (mv nil (bx-note "program function whose body ACL2 does not translate"
                                   (list fn (fms-to-string "~@0" (list (cons #\0 val))))))
                (mv val nil)))))))))

(defun bx-program-defs (fns form wrld defs notes)
  (cond ((endp fns) (mv (reverse defs) (reverse notes)))
        (t (mv-let (body note)
             (bx-program-body (car fns) form wrld)
             (bx-program-defs (cdr fns) form wrld
                              (if body
                                  (cons (list (car fns)
                                              (formals (car fns) wrld)
                                              (bx-exec body))
                                        defs)
                                defs)
                              (if note (cons note notes) notes))))))

(defun bx-defs (fns wrld)
  (cond ((endp fns) nil)
        (t (cons (list (car fns)
                       (formals (car fns) wrld)
                       (getpropc (car fns) 'unnormalized-body nil wrld))
                 (bx-defs (cdr fns) wrld)))))

(defun bx-same-rulers (fns rulers wrld)
  (or (endp fns)
      (and (equal (bx-rulers (car fns) wrld) rulers)
           (bx-same-rulers (cdr fns) rulers wrld))))

(defun bx-all-program-p (fns wrld)
  (or (endp fns)
      (and (bx-programp (car fns) wrld)
           (bx-all-program-p (cdr fns) wrld))))

(defun bx-some-program-p (fns wrld)
  (and (consp fns)
       (or (bx-programp (car fns) wrld)
           (bx-some-program-p (cdr fns) wrld))))

(defun bx-all-constrained-p (fns wrld)
  (or (endp fns)
      (and (bx-constrained-p (car fns) wrld)
           (bx-all-constrained-p (cdr fns) wrld))))

(defun bx-some-constrained-p (fns wrld)
  (and (consp fns)
       (or (bx-constrained-p (car fns) wrld)
           (bx-some-constrained-p (cdr fns) wrld))))

(defun bx-define-items (fns wrld)
  (let ((rulers (bx-rulers (car fns) wrld))
        (defs (bx-defs fns wrld)))
    (append (if (bx-same-rulers fns rulers wrld)
                nil
              (list (bx-note "clique whose functions differ in ruler-extenders"
                             fns)))
            (list (bx-stmt "define" (cons rulers defs))
                  (bx-prog "define" (cons rulers defs))))))

; A candidate for naming a formula of a constraint: (NAME KIND DATA),
; where KIND is :formula and DATA a formula that must be equal to it, or
; KIND is :definition and DATA a function whose definition it must be.

(defun bx-add-candidates (encl cands pending)
  (put-assoc-eq encl
                (append (cdr (assoc-eq encl pending)) cands)
                pending))

(defun bx-definition-candidates (fns wrld)
  (cond ((endp fns) nil)
        (t (cons (list (bx-formula-name (car fns) "definition" wrld)
                       :definition (car fns))
                 (bx-definition-candidates (cdr fns) wrld)))))

(defun bx-mentions-some (term fns)
  (intersectp-eq (all-fnnames term) fns))

; The defined functions of a DEFSTOBJ or DEFABSSTOBJ event, in an order in
; which each follows the functions of the event that its body calls.

(defun bx-ready (todo placed wrld)
  (cond ((endp todo) nil)
        ((subsetp-eq (intersection-eq
                      (all-fnnames (getpropc (car todo) 'unnormalized-body
                                             nil wrld))
                      (set-difference-eq todo (list (car todo))))
                     placed)
         (cons (car todo) (bx-ready (cdr todo) placed wrld)))
        (t (bx-ready (cdr todo) placed wrld))))

(defun bx-local-order (todo placed acc wrld)
  (cond ((endp todo) (reverse acc))
        (t (let ((ready (bx-ready todo placed wrld)))
             (if (null ready)
                 (append (reverse acc) todo)
               (bx-local-order (set-difference-eq todo ready)
                               (append ready placed)
                               (revappend ready acc)
                               wrld))))))

(defun bx-stobj-define-items (fns wrld)
  (cond ((endp fns) nil)
        (t (append (bx-define-items (list (car fns)) wrld)
                   (bx-stobj-define-items (cdr fns) wrld)))))

(defun bx-stobj-items (names defined fns-acc wrld acc)

; The items for the names of a DEFSTOBJ or DEFABSSTOBJ event.  FNS-ACC
; collects the functions in logic mode with a body.  DEFINED maps each
; function that an earlier statement defines to T: a DEFABSSTOBJ event
; defines its functions by events of its own, which stand before it.

  (cond ((endp names)
         (append (reverse acc)
                 (bx-stobj-define-items
                  (bx-local-order (reverse fns-acc) nil nil wrld) wrld)))
        (t (let ((name (car names)))
             (cond ((and (bx-function-p name wrld) (hons-get name defined))
                    (bx-stobj-items (cdr names) defined fns-acc wrld acc))
                   ((bx-function-p name wrld)
                    (cond ((bx-programp name wrld)
                           (bx-stobj-items
                            (cdr names) defined fns-acc wrld
                            (cons (bx-prog "define"
                                           (list nil
                                                 (list name (formals name wrld)
                                                       (bx-exec
                                                        (getpropc name 'unnormalized-body
                                                                  nil wrld)))))
                                  acc)))
                          ((getpropc name 'unnormalized-body nil wrld)
                           (bx-stobj-items (cdr names) defined (cons name fns-acc) wrld acc))
                          (t (bx-stobj-items
                              (cdr names) defined fns-acc wrld
                              (cons (bx-note "stobj function with no definition" name)
                                    acc)))))
                   ((bx-reserve-kind-p name wrld)
                    (bx-stobj-items (cdr names) defined fns-acc wrld
                                    (cons (bx-stmt "reserve" (list name)) acc)))
                   (t (bx-stobj-items
                       (cdr names) defined fns-acc wrld
                       (cons (bx-note "name of no known kind" name) acc))))))))

; The formulas of a constraint.  ACL2 stores the constraint L as the
; conjuncts of the formulas of the encapsulate's events (FLATTEN-ANDS-IN-
; LIT), with repeated conjuncts merged, and sometimes with the functions
; that only carry guards removed (REMOVE-GUARD-HOLDERS).  The statement
; gives, for each event of the encapsulate that is part of the
; constraint, in the order of the events, the formula that ACL2 holds
; under its name; for a function defined there, the equation of L that
; defines it.  Then each term of L that is a conjunct of none of those is
; given under a name of the exporter's making (see BX-FRESH-NAME).

(defun bx-conjuncts (formula lst wrld)

; The conjuncts of FORMULA, as ACL2 puts them in a constraint, if they are
; all members of LST; otherwise :none.

  (let ((c1 (flatten-ands-in-lit formula)))
    (if (subsetp-equal c1 lst)
        c1
      (let ((c2 (flatten-ands-in-lit (remove-guard-holders formula wrld))))
        (if (subsetp-equal c2 lst) c2 :none)))))

(defun bx-equation-in (fn lst wrld)

; The member of LST that is an equation defining FN, or NIL.

  (if (endp lst)
      nil
    (let ((term (car lst)))
      (if (case-match term
            (('equal (!fn . args) &) (equal args (formals fn wrld)))
            (& nil))
          term
        (bx-equation-in fn (cdr lst) wrld)))))

; Returns (mv formulas covered notes): a formula (NAME TERM) for each
; candidate, and the terms of LST that they cover.

(defun bx-candidate-terms (cands lst c wrld formulas covered notes)
  (cond
   ((endp cands) (mv (reverse formulas) covered (reverse notes)))
   (t (let* ((cand (car cands))
             (term (if (eq (cadr cand) :formula)
                       (caddr cand)
                     (bx-equation-in (caddr cand) lst wrld)))
             (conj (if term (bx-conjuncts term lst wrld) :none)))
        (if (eq conj :none)
            (bx-candidate-terms (cdr cands) lst c wrld formulas covered
                                (cons (bx-note "event of an encapsulate whose formula is not in its constraint"
                                               (list c (car cand)))
                                      notes))
          (bx-candidate-terms (cdr cands) lst c wrld
                              (cons (list (car cand) term) formulas)
                              (union-equal conj covered)
                              notes))))))

(defun bx-uncovered (lst covered c i wrld formulas notes)
  (cond ((endp lst) (mv (reverse formulas) (reverse notes)))
        ((member-equal (car lst) covered)
         (bx-uncovered (cdr lst) covered c (+ i 1) wrld formulas notes))
        (t (let ((name (bx-formula-name
                        c
                        (concatenate 'string "constraint "
                                     (coerce (explode-nonnegative-integer i 10 nil)
                                             'string))
                        wrld)))
             (bx-uncovered (cdr lst) covered c (+ i 1) wrld
                           (cons (list name (car lst)) formulas)
                           (cons (bx-note "formula of a constraint that no event of the encapsulate states"
                                          (list c name))
                                 notes))))))

(defun bx-name-formulas (lst cands c wrld)

; Returns (mv formulas notes).

  (mv-let (formulas covered notes)
    (bx-candidate-terms cands lst c wrld nil nil nil)
    (mv-let (more notes2)
      (bx-uncovered lst covered c 1 wrld nil nil)
      (mv (append formulas more) (append notes notes2)))))

(defun bx-arities (fns wrld)
  (cond ((endp fns) nil)
        (t (cons (list (car fns) (len (formals (car fns) wrld)))
                 (bx-arities (cdr fns) wrld)))))

(defun bx-insert-by-event (fn fns wrld)
  (cond ((endp fns) (list fn))
        ((< (bx-event-number fn wrld) (bx-event-number (car fns) wrld))
         (cons fn fns))
        (t (cons (car fns) (bx-insert-by-event fn (cdr fns) wrld)))))

(defun bx-sort-by-event (fns wrld)

; FNS sorted by the numbers of the events that introduced them, the
; earliest first.  It is short, so insertion will do.

  (cond ((endp fns) nil)
        (t (bx-insert-by-event (car fns) (bx-sort-by-event (cdr fns) wrld) wrld))))

; Where ACL2 records no constraint, the formulas are those it holds: the
; theorems of the encapsulate about its functions, and the definitions of
; the functions defined there.

(defun bx-candidate-formulas (cands wrld)
  (cond ((endp cands) nil)
        (t (let* ((c (car cands))
                  (formula (if (eq (cadr c) :formula)
                               (caddr c)
                             (let ((fn (caddr c)))
                               (list 'equal (cons fn (formals fn wrld))
                                     (getpropc fn 'unnormalized-body nil wrld))))))
             (cons (list (car c) formula)
                   (bx-candidate-formulas (cdr cands) wrld))))))

(defun bx-constrain-items (names c pending wrld)
  (let* ((siblings (getpropc c 'siblings nil wrld))
         (fns (append names
                      (bx-sort-by-event (set-difference-eq siblings names) wrld)))
         (cands (cdr (assoc-eq c pending))))
    (mv-let (name lst origins)
      (constraint-info c wrld)
      (declare (ignore name origins))
      (if (unknown-constraints-p lst)
          (list (bx-note "constraint that ACL2 does not record" fns)
                (bx-stmt "constrain"
                         (list (bx-arities fns wrld)
                               (bx-candidate-formulas cands wrld))))
        (mv-let (formulas notes)
          (bx-name-formulas lst cands c wrld)
          (append notes
                  (list (bx-stmt "constrain"
                                 (list (bx-arities fns wrld) formulas)))))))))

; A package is hidden at its event if ACL2 keeps it hidden now, or if the
; event declared it hidden and a later event declared it openly.  ACL2
; records the second in the event, as the last of the arguments of the
; DEFPKG form it stores: (defpkg NAME IMPORTS DOC BOOK-PATH HIDDEN-P).

(defun bx-package-items (name form wrld)
  (let* ((entry (find-package-entry name (global-val 'known-package-alist wrld)))
         (rule (intern-in-package-of-symbol (concatenate 'string name "-PACKAGE")
                                            'acl2::x))
         (formula (getpropc rule 'theorem nil wrld)))
    (cond ((null entry)
           (list (bx-note "package that ACL2 does not know" name)))
          ((or (package-entry-hidden-p entry)
               (and (true-listp form) (equal (len form) 6) (eq (car (last form)) t)))
           (list (bx-stmt "hidden-package"
                          (list name (package-entry-imports entry)))))
          (t (case-match formula
               (('equal ('pkg-imports ('quote !name)) ('quote imports))
                (list (bx-stmt "package" (list name imports))))
               (& (list (bx-note "package with no axiom of its imports" name)
                        (bx-stmt "package"
                                 (list name (package-entry-imports entry))))))))))

(defun bx-choose-items (fn wrld)
  (let ((axiom (getpropc fn 'defchoose-axiom nil wrld))
        (free (formals fn wrld)))
    (mv-let (bound body free2)
      (bx-choose-parts axiom fn wrld)
      (if (and bound
               (equal (bx-beta axiom)
                      (bx-beta (bx-choose-axiom fn bound free body free2))))
          (list (bx-stmt "choose" (list fn bound free body free2)))
        (list (bx-note "defchoose axiom not of the form of spec/logic.md" fn))))))

(defun bx-reserve-items (names wrld)
  (cond ((endp names) nil)
        ((bx-reserve-kind-p (car names) wrld)
         (cons (bx-stmt "reserve" (list (car names)))
               (bx-reserve-items (cdr names) wrld)))
        (t (cons (bx-note "name of no known kind" (car names))
                 (bx-reserve-items (cdr names) wrld)))))

(defun bx-names-with-content (names wrld)
  (and (consp names)
       (or (and (symbolp (car names))
                (or (and (bx-function-p (car names) wrld)
                         (not (bx-programp (car names) wrld)))
                    (getpropc (car names) 'theorem nil wrld)))
           (bx-names-with-content (cdr names) wrld))))

; The items of one event.  ENCL is the constrainer of the innermost
; encapsulate with a signature that contains it, and PENDING maps each
; constrainer to the candidates found so far for naming the formulas of
; its constraint.  Returns (mv items pending).

(defun bx-event-items (ev encl pending defined wrld)
  (let* ((type (access-event-tuple-type ev))
         (names (bx-names (access-event-tuple-namex ev)))
         (class (access-event-tuple-symbol-class ev)))
    (case type
      ((defun defuns)
       (cond
        ((eq class :program)
         (if (bx-all-program-p names wrld)
             (mv-let (defs notes)
               (bx-program-defs names (access-event-tuple-form ev) wrld nil nil)
               (mv (append notes
                           (and defs (list (bx-prog "define" (cons nil defs)))))
                   pending))
           (mv nil pending)))
        ((bx-some-program-p names wrld)
         (mv (list (bx-note "logic event of a function now in program mode" names))
             pending))
        ((bx-all-constrained-p names wrld)
         (if encl
             (mv nil (bx-add-candidates encl (bx-definition-candidates names wrld)
                                        pending))
           (mv (list (bx-note "constrained definition outside an encapsulate" names))
               pending)))
        ((bx-some-constrained-p names wrld)
         (mv (list (bx-note "clique only partly constrained" names)) pending))
        (t (mv (bx-define-items names wrld) pending))))
      ((defthm defaxiom)
       (let* ((name (car names))
              (formula (getpropc name 'theorem nil wrld))
              (word (if (eq type 'defthm) "theorem" "axiom")))
         (cond
          ((and encl
                (eq type 'defthm)
                (mv-let (c lst origins)
                  (constraint-info encl wrld)
                  (declare (ignore c origins))
                  (and (bx-mentions-some formula (getpropc encl 'siblings nil wrld))
                       (or (unknown-constraints-p lst)
                           (not (eq (bx-conjuncts formula lst wrld) :none))))))
           (mv nil (bx-add-candidates encl (list (list name :formula formula))
                                      pending)))
          ((and encl
                (bx-mentions-some formula (getpropc encl 'siblings nil wrld)))
           (mv (list (bx-note "theorem of an encapsulate about its functions, outside its constraint"
                              name)
                     (bx-stmt word (list name formula)))
               pending))
          (t (mv (list (bx-stmt word (list name formula))) pending)))))
      (defchoose
       (let ((fn (car names)))
         (if (bx-constrained-p fn wrld)
             (if encl
                 (mv nil (bx-add-candidates
                          encl
                          (list (list (bx-formula-name fn "choice" wrld)
                                      :formula
                                      (getpropc fn 'defchoose-axiom nil wrld)))
                          pending))
               (mv (list (bx-note "constrained choice outside an encapsulate" fn))
                   pending))
           (mv (bx-choose-items fn wrld) pending))))
      (encapsulate
       (if (consp names)
           (let ((c (bx-constrainer ev wrld)))
             (mv (append (if (and encl (not (eq encl c)))
                             (list (bx-note "encapsulate with a signature inside another"
                                            names))
                           nil)
                         (bx-constrain-items names c pending wrld))
                 pending))
         (mv nil pending)))
      (defpkg (mv (bx-package-items (car names) (access-event-tuple-form ev) wrld)
                  pending))
      ((defmacro defconst deflabel deftheory)
       (mv (bx-reserve-items names wrld) pending))
      ((defstobj defabsstobj)
       (mv (bx-stobj-items names defined nil wrld nil) pending))
      (otherwise
       (mv (if (bx-names-with-content names wrld)
               (list (bx-note "event of an unexpected kind"
                              (list type names)))
             nil)
           pending)))))

; DEFINED maps each function that a statement already written defines to
; T.

(defun bx-add-defined (items defined)
  (cond ((endp items) defined)
        ((and (eq (car (car items)) :stmt)
              (member-equal (cadr (car items)) '("define" "constrain" "choose")))
         (bx-add-defined (cdr items)
                         (bx-add-names (bx-introduced (cdr (car items))) defined)))
        (t (bx-add-defined (cdr items) defined))))

(defun bx-items (pairs pending defined wrld acc)
  (cond ((endp pairs) (prog2$ (fast-alist-free defined) (reverse acc)))
        (t (mv-let (items pending)
             (bx-event-items (car (car pairs)) (cdr (car pairs)) pending defined
                             wrld)
             (bx-items (cdr pairs) pending (bx-add-defined items defined) wrld
                       (revappend items acc))))))

(defun bx-range-items (lo hi wrld)
  (let ((evs (bx-events wrld lo hi nil)))
    (bx-items (bx-enclose (reverse evs) nil nil wrld) nil nil wrld nil)))

;;; 6. Selecting items

(defun bx-select (key items)
  (cond ((endp items) nil)
        ((eq (car (car items)) key)
         (cons (cdr (car items)) (bx-select key (cdr items))))
        (t (bx-select key (cdr items)))))

;;; 7. The library

; The statements of the library stand in this order: packages; the
; definitions, constraints and choices, each after every function its
; terms call; the theorems; the reserved names.  Within each group they
; keep the order of ACL2's events, as far as the first rule allows.

(defun bx-words (words stmts)
  (cond ((endp stmts) nil)
        ((member-equal (car (car stmts)) words)
         (cons (car stmts) (bx-words words (cdr stmts))))
        (t (bx-words words (cdr stmts)))))

; A depth-first walk: each statement is placed after the statements that
; introduce the functions it uses.  INDEX maps each function to its
; statement, and DONE maps each statement placed, or being placed, to T
; or :pending.

(defun bx-index-fns (fns stmt acc)
  (cond ((endp fns) acc)
        (t (bx-index-fns (cdr fns) stmt (hons-acons (car fns) stmt acc)))))

(defun bx-index (stmts acc)
  (cond ((endp stmts) acc)
        (t (bx-index (cdr stmts)
                     (bx-index-fns (bx-introduced (car stmts)) (car stmts) acc)))))

(mutual-recursion

 (defun bx-place (stmt index done acc notes)
   (let ((mark (cdr (hons-get stmt done))))
     (cond ((eq mark t) (mv done acc notes))
           ((eq mark :pending)
            (mv done acc (cons (bx-note "cycle among definitions" (bx-introduced stmt))
                               notes)))
           (t (mv-let (done acc notes)
                (bx-place-fns (bx-used stmt) index
                              (hons-acons stmt :pending done) acc notes)
                (mv (hons-acons stmt t done) (cons stmt acc) notes))))))

 (defun bx-place-fns (fns index done acc notes)
   (cond ((endp fns) (mv done acc notes))
         (t (let ((stmt (cdr (hons-get (car fns) index))))
              (if stmt
                  (mv-let (done acc notes)
                    (bx-place stmt index done acc notes)
                    (bx-place-fns (cdr fns) index done acc notes))
                (bx-place-fns (cdr fns) index done acc notes)))))))

(defun bx-place-all (stmts index done acc notes)
  (cond ((endp stmts) (mv (reverse acc) notes))
        (t (mv-let (done acc notes)
             (bx-place (car stmts) index done acc notes)
             (bx-place-all (cdr stmts) index done acc notes)))))

(defun bx-not-ground (stmts ground)

; The statements that are not part of the ground theory: GROUND holds the
; functions that the ground theory defines.  Every axiom of ACL2 is in the
; ground theory, and so are the packages it declares and the constants T
; and NIL.

  (cond ((endp stmts) nil)
        ((or (equal (car (car stmts)) "axiom")
             (and (equal (car (car stmts)) "reserve")
                  (member-eq (car (cadr (car stmts))) '(t nil)))
             (and (equal (car (car stmts)) "define")
                  (subsetp-eq (bx-introduced (car stmts)) ground))
             (and (member-equal (car (car stmts)) '("package" "hidden-package"))
                  (member-equal (car (cadr (car stmts)))
                                '("COMMON-LISP" "KEYWORD" "ACL2"
                                  "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"))))
         (bx-not-ground (cdr stmts) ground))
        (t (cons (car stmts) (bx-not-ground (cdr stmts) ground)))))

(defun bx-library-order (stmts)
  (let* ((defs (bx-words '("define" "constrain" "choose") stmts))
         (index (bx-index defs nil)))
    (mv-let (placed notes)
      (bx-place-all defs index nil nil nil)
      (prog2$ (fast-alist-free index)
              (mv (append (bx-words '("package" "hidden-package") stmts)
                          placed
                          (bx-words '("theorem" "axiom") stmts)
                          (bx-words '("reserve") stmts))
                  notes)))))

;;; 8. A check of the order

; The exporter confirms that the lines it writes could be admitted in the
; order written, as far as names go: every function a term calls is in
; use, with its number of arguments; every name a line introduces is new;
; and every symbol is of a package declared before.  It proves nothing.
; FNS maps each function in use to its number of arguments, NAMES each
; name in use to T, and PKGS each package declared to T, or to (:hidden
; . IMPORTS) if it is hidden, which a package line with the same imports
; may declare again.

(mutual-recursion

 (defun bx-bad-calls (term fns own)

; The calls in TERM of a function that is not in use with that number of
; arguments.  OWN maps the functions of the line itself to theirs.

   (cond ((variablep term) nil)
         ((fquotep term) nil)
         ((flambda-applicationp term)
          (append (bx-bad-calls (lambda-body (ffn-symb term)) fns own)
                  (bx-bad-calls-lst (fargs term) fns own)))
         (t (let* ((fn (ffn-symb term))
                   (pair (or (assoc-eq fn own) (hons-get fn fns))))
              (append (if (and pair (eql (cdr pair) (len (fargs term))))
                          nil
                        (list fn))
                      (bx-bad-calls-lst (fargs term) fns own))))))

 (defun bx-bad-calls-lst (terms fns own)
   (cond ((endp terms) nil)
         (t (append (bx-bad-calls (car terms) fns own)
                    (bx-bad-calls-lst (cdr terms) fns own))))))

(defun bx-packages-of (x pkgs acc)

; The package names of the symbols in X that are not declared in PKGS.

  (cond ((consp x) (bx-packages-of (cdr x) pkgs (bx-packages-of (car x) pkgs acc)))
        ((and (symbolp x)
              (not (hons-get (symbol-package-name x) pkgs))
              (not (member-equal (symbol-package-name x) acc)))
         (cons (symbol-package-name x) acc))
        (t acc)))

(defun bx-new-names (names table)
  (cond ((endp names) nil)
        ((hons-get (car names) table) (cons (car names) (bx-new-names (cdr names) table)))
        (t (bx-new-names (cdr names) table))))

(defun bx-add-arities (pairs table)
  (cond ((endp pairs) table)
        (t (bx-add-arities (cdr pairs)
                           (hons-acons (car (car pairs)) (cadr (car pairs)) table)))))

(defun bx-def-arities (defs)
  (cond ((endp defs) nil)
        (t (cons (list (car (car defs)) (len (cadr (car defs))))
                 (bx-def-arities (cdr defs))))))

(defun bx-alist (pairs)
  (cond ((endp pairs) nil)
        (t (cons (cons (car (car pairs)) (cadr (car pairs)))
                 (bx-alist (cdr pairs))))))

(defun bx-package-rule (name)
  (intern-in-package-of-symbol (concatenate 'string name "-PACKAGE") 'acl2::x))

; Checks one statement.  Returns (mv problems fns names pkgs).

(defun bx-check-stmt (stmt fns names pkgs)
  (let* ((word (car stmt))
         (args (cadr stmt))
         (missing (bx-packages-of args pkgs nil)))
    (cond
     ((member-equal word '("package" "hidden-package"))
      (let ((rule (bx-package-rule (car args))))
        (mv (append (and missing (list (list :package-undeclared missing)))
                    (and (hons-get (car args) pkgs)
                         (not (and (equal word "package")
                                   (equal (cdr (hons-get (car args) pkgs))
                                          (cons :hidden (cadr args)))))
                         (list (list :package-declared (car args))))
                    (and (equal word "package") (hons-get rule names)
                         (list (list :name-in-use rule))))
            fns
            (if (equal word "package") (hons-acons rule t names) names)
            (hons-acons (car args)
                        (if (equal word "package") t (cons :hidden (cadr args)))
                        pkgs))))
     (t
      (let* ((intro (case-match word
                      ("define" (bx-def-arities (cdr args)))
                      ("constrain" (car args))
                      ("choose" (list (list (car args) (len (caddr args)))))
                      (& nil)))
             (formula-names (and (equal word "constrain") (strip-cars (cadr args))))
             (new (append (strip-cars intro)
                          formula-names
                          (if (member-equal word '("theorem" "axiom" "reserve"))
                              (list (car args))
                            nil)))
             (terms (case-match word
                      ("define" (bx-bodies (cdr args)))
                      ("constrain" (strip-cadrs (cadr args)))
                      ("choose" (list (cadddr args)))
                      ("theorem" (list (cadr args)))
                      ("axiom" (list (cadr args)))
                      (& nil)))
             (bad (bx-bad-calls-lst terms fns (bx-alist intro)))
             (used (bx-new-names new names)))
        (mv (append (and missing (list (list :package-undeclared missing)))
                    (and bad (list (list :not-in-use (remove-duplicates-eq bad))))
                    (and used (list (list :name-in-use used)))
                    (and (not (no-duplicatesp-equal new))
                         (list (list :name-twice new))))
            (bx-add-arities intro fns)
            (bx-add-names new names)
            pkgs))))))

; Checks the statements in order, a line that repeats an earlier one
; apart.  SEEN maps each line written to T.  Returns (mv notes fns names
; pkgs seen).

(defun bx-check-stmts (stmts fns names pkgs seen notes)
  (cond ((endp stmts) (mv (reverse notes) fns names pkgs seen))
        (t (let ((line (bm-line (car (car stmts)) (cadr (car stmts)))))
             (if (hons-get line seen)
                 (bx-check-stmts (cdr stmts) fns names pkgs seen notes)
               (mv-let (problems fns names pkgs)
                 (bx-check-stmt (car stmts) fns names pkgs)
                 (bx-check-stmts (cdr stmts) fns names pkgs
                                 (hons-acons line t seen)
                                 (if problems
                                     (cons (bx-note "line that could not be admitted in order"
                                                    (list (bx-introduced (car stmts))
                                                          (if (member-equal (car (car stmts))
                                                                            '("theorem" "axiom" "reserve"))
                                                              (car (cadr (car stmts)))
                                                            nil)
                                                          problems))
                                           notes)
                                   notes))))))))

;;; 9. The ground theory, as the check starts from it

; The ground theory declares five packages, its 32 primitives and 36
; definitions are functions in use, and its names are in use: those of
; the functions, of ACL2's axioms, T and NIL.  GROUND-FNS is the list of
; the functions it defines, read from spec/ground.txt by export/run.sh.

(defun bx-axiom-names (evs)
  (cond ((endp evs) nil)
        ((eq (access-event-tuple-type (car evs)) 'defaxiom)
         (cons (access-event-tuple-namex (car evs)) (bx-axiom-names (cdr evs))))
        (t (bx-axiom-names (cdr evs)))))

(defun bx-ground-tables (ground-fns boot-evs wrld)
  (let* ((prims (strip-cars *primitive-formals-and-guards*))
         (fns (bx-add-arities (bx-arities (append prims ground-fns) wrld) nil))
         (names (bx-add-names (append '(t nil) prims ground-fns
                                      (bx-axiom-names boot-evs))
                              nil))
         (pkgs (bx-add-names '("COMMON-LISP" "KEYWORD" "ACL2"
                               "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL")
                             nil)))
    (mv fns names pkgs)))

;;; 10. Attachments

; The attachments in force in the world WRLD, which may be an older world
; that is a tail of the present one: the pairs (F . G), where G is the
; function ACL2 runs in place of F.  ACL2 holds them in the ATTACHMENT
; property of F, which is either an alist of such pairs for F and the
; functions attached with it, or the name of a function that holds that
; alist, as its function ATTACHMENT-PAIR reads it.  The property is read
; from the triples of WRLD, the first of each symbol being its value.

(defun bx-attachment-props (wrld acc)
  (cond ((endp wrld) acc)
        ((and (eq (cadar wrld) 'attachment)
              (not (hons-get (caar wrld) acc)))
         (bx-attachment-props (cdr wrld) (hons-acons (caar wrld) (cddar wrld) acc)))
        (t (bx-attachment-props (cdr wrld) acc))))

(defun bx-attachment-value (sym props)
  (let ((v (cdr (hons-get sym props))))
    (if (eq v *acl2-property-unbound*) nil v)))

(defun bx-pairs-of (alist props acc)
  (cond ((endp alist) acc)
        (t (let* ((f (car (car alist)))
                  (prop (bx-attachment-value f props))
                  (fal (if (and prop (symbolp prop))
                           (bx-attachment-value prop props)
                         prop))
                  (pair (and (consp fal)
                             (not (eq (car fal) :attachment-disallowed))
                             (assoc-eq f fal))))
             (bx-pairs-of (cdr alist) props (if pair (cons pair acc) acc))))))

(defun bx-attachment-pairs (wrld)
  (let* ((props (bx-attachment-props wrld nil))
         (pairs (bx-pairs-of props props nil)))
    (prog2$ (fast-alist-free props)
            (merge-sort-lexorder pairs))))

(defun bx-attach-lines (pairs except)
  (cond ((endp pairs) nil)
        ((member-equal (car pairs) except) (bx-attach-lines (cdr pairs) except))
        (t (cons (list "attach" (list (car (car pairs)) (cdr (car pairs))))
                 (bx-attach-lines (cdr pairs) except)))))

; Program text holds no definition of HARD-ERROR or THROW-NONEXEC-ERROR.
; Their bodies are 'NIL, but ACL2 runs them as code that reports an error
; and gives no value, so a runner must stop at a call of either, as it
; does at a function with no program text (spec/language.md, section 4;
; EDGE-CASES.md, entries 2.2 and 2.3).

(defun bx-runnable (progs)
  (cond ((endp progs) nil)
        ((intersectp-eq (bx-introduced (car progs))
                        '(hard-error throw-nonexec-error))
         (bx-runnable (cdr progs)))
        (t (cons (car progs) (bx-runnable (cdr progs))))))

;;; 11. Writing

; The trust tags that books declared: ACL2 pairs each trust tag it has
; seen with the books that declared it, NIL standing for a declaration
; outside any book.

; The names introduced by the events among EVS whose proofs ACL2 skipped,
; as it records in each event.

(defun bx-skipped (evs)
  (cond ((endp evs) nil)
        ((access-event-tuple-skipped-proofs-p (car evs))
         (cons (access-event-tuple-namex (car evs)) (bx-skipped (cdr evs))))
        (t (bx-skipped (cdr evs)))))

(defun bx-book-ttags (alist)
  (cond ((endp alist) nil)
        ((remove-eq nil (cdr (car alist)))
         (cons (car (car alist)) (bx-book-ttags (cdr alist))))
        (t (bx-book-ttags (cdr alist)))))

(defun bx-lines (stmts)
  (cond ((endp stmts) nil)
        (t (cons (bm-line (car (car stmts)) (cadr (car stmts)))
                 (bx-lines (cdr stmts))))))

(defun bx-note-lines (notes)
  (cond ((endp notes) nil)
        (t (cons (bm-line "note" (list (car (car notes)) (cadr (car notes))))
                 (bx-note-lines (cdr notes))))))

(defun bx-count-word (word stmts)
  (cond ((endp stmts) 0)
        ((equal (car (car stmts)) word) (+ 1 (bx-count-word word (cdr stmts))))
        (t (bx-count-word word (cdr stmts)))))

(defun bx-count-lines (stmts)
  (list (bm-line "count" (list "package" (bx-count-word "package" stmts)))
        (bm-line "count" (list "hidden-package" (bx-count-word "hidden-package" stmts)))
        (bm-line "count" (list "define" (bx-count-word "define" stmts)))
        (bm-line "count" (list "constrain" (bx-count-word "constrain" stmts)))
        (bm-line "count" (list "choose" (bx-count-word "choose" stmts)))
        (bm-line "count" (list "theorem" (bx-count-word "theorem" stmts)))
        (bm-line "count" (list "axiom" (bx-count-word "axiom" stmts)))
        (bm-line "count" (list "reserve" (bx-count-word "reserve" stmts)))))

; The program text of the library: the definitions in logic mode in the
; order of the statements, then the functions in program mode in the
; order of ACL2's events.

(defun bx-program-only (progs wrld)
  (cond ((endp progs) nil)
        ((bx-all-program-p (strip-cars (cdr (cadr (car progs)))) wrld)
         (cons (car progs) (bx-program-only (cdr progs) wrld)))
        (t (bx-program-only (cdr progs) wrld))))

(defun bx-library-program-order (progs ordered wrld)
  (append (bx-words '("define") ordered)
          (bx-program-only progs wrld)))

; The definitions of the ground theory, which a runner needs as much as
; those of the library, stand first in the library's program text.

(defun bx-ground-defines (fns wrld)
  (cond ((endp fns) nil)
        (t (cons (list "define"
                       (list (bx-rulers (car fns) wrld)
                             (list (car fns) (formals (car fns) wrld)
                                   (getpropc (car fns) 'unnormalized-body nil wrld))))
                 (bx-ground-defines (cdr fns) wrld)))))

; The library: the events numbered at most HI, the end of the world ACL2
; starts with.  Writes PREFIX.statements, PREFIX.program and PREFIX.notes.

(defun bx-export-library (ground-fns hi prefix state)
  (let* ((wrld (w state))
         (boot-evs (bx-events wrld 0 hi nil))
         (items (bx-items (bx-enclose (reverse boot-evs) nil nil wrld) nil nil wrld nil))
         (stmts (bx-not-ground (bx-select :stmt items) ground-fns))
         (progs (bx-not-ground (bx-select :prog items) ground-fns)))
    (mv-let (ordered order-notes)
      (bx-library-order stmts)
      (mv-let (fns names pkgs)
        (bx-ground-tables ground-fns boot-evs wrld)
        (mv-let (check-notes fns names pkgs seen)
          (bx-check-stmts ordered fns names pkgs nil nil)
          (declare (ignore fns names pkgs))
          (let* ((notes (bx-select :note (append items order-notes check-notes)))
                 (attach (bx-attach-lines (bx-attachment-pairs wrld) nil)))
            (prog2$
             (fast-alist-free seen)
             (pprogn
              (bm-write-file (bx-lines ordered)
                             (concatenate 'string prefix ".statements") state)
              (bm-write-file (append (bx-lines (bx-ground-defines ground-fns wrld))
                                     (bx-lines (bx-runnable
                                                (bx-library-program-order progs ordered wrld)))
                                     (bx-lines attach))
                             (concatenate 'string prefix ".program") state)
              (bm-write-file (append (bx-count-lines ordered)
                                     (bx-note-lines notes))
                             (concatenate 'string prefix ".notes") state)
              (value (list (len ordered) (len notes)))))))))))


;;; 12. The prover's aids

; Beside each book, what has no logical content but may help a prover:
;
;   (local BOOK EVENT)      a local event of the book named BOOK, as the
;                           book's source writes it, read by ACL2's reader
;   (hints NAME HINTS)      the hints of the event that introduced NAME
;   (instructions NAME I)   its instructions for ACL2's proof builder
;   (measure F M REL HOW)   the measure M and the well-founded relation REL
;                           that ACL2 stores for the recursive function F;
;                           HOW is "declared" if the event declares a
;                           measure, and "default" if ACL2 chose it
;
; The hints, instructions and declarations are read from the event forms
; that ACL2 stores in its world; the measures from the JUSTIFICATION it
; stores.  Nothing that ACL2's prover found is written.

(defun bx-kwd-value (key kwds)
  (cond ((or (endp kwds) (endp (cdr kwds))) nil)
        ((eq (car kwds) key) (list (cadr kwds)))
        (t (bx-kwd-value key (cddr kwds)))))

(defun bx-xargs-items (items)
  (cond ((endp items) nil)
        ((and (consp (car items)) (eq (caar items) 'xargs))
         (append (cdar items) (bx-xargs-items (cdr items))))
        (t (bx-xargs-items (cdr items)))))

(defun bx-xargs (dcls)

; The keyword arguments of every XARGS declaration among DCLS.

  (cond ((endp dcls) nil)
        ((and (consp (car dcls)) (eq (caar dcls) 'declare))
         (append (bx-xargs-items (cdar dcls)) (bx-xargs (cdr dcls))))
        (t (bx-xargs (cdr dcls)))))

(defun bx-defun-aids (defs wrld)
  (cond ((endp defs) nil)
        (t (let* ((def (car defs))
                  (fn (car def))
                  (kwds (bx-xargs (butlast (cddr def) 1)))
                  (just (getpropc fn 'justification nil wrld))
                  (hints (bx-kwd-value :hints kwds)))
             (append
              (and hints (list (list "hints" (list fn (car hints)))))
              (and just
                   (list (list "measure"
                               (list fn
                                     (access justification just :measure)
                                     (access justification just :rel)
                                     (if (bx-kwd-value :measure kwds)
                                         "declared"
                                       "default")))))
              (bx-defun-aids (cdr defs) wrld))))))

(defun bx-event-aids (evs wrld)
  (cond ((endp evs) nil)
        (t (let* ((ev (car evs))
                  (form (access-event-tuple-form ev))
                  (type (access-event-tuple-type ev)))
             (append
              (case type
                ((defun defuns)
                 (if (eq (access-event-tuple-symbol-class ev) :program)
                     nil
                   (bx-defun-aids (bx-defun-forms form) wrld)))
                (defthm
                 (if (and (consp form) (eq (car form) 'defthm))
                     (let* ((name (cadr form))
                            (kwds (cdddr form))
                            (hints (bx-kwd-value :hints kwds))
                            (instrs (bx-kwd-value :instructions kwds)))
                       (append (and hints (list (list "hints" (list name (car hints)))))
                               (and instrs
                                    (list (list "instructions"
                                                (list name (car instrs)))))))
                   nil))
                (otherwise nil))
              (bx-event-aids (cdr evs) wrld))))))

; The local events of a list of forms read from a book: those at the top
; level, and those inside ENCAPSULATE, PROGN and a DEFSECTION.

(defun bx-skip-keywords (forms)
  (cond ((and (consp forms) (keywordp (car forms)) (consp (cdr forms)))
         (bx-skip-keywords (cddr forms)))
        (t forms)))

(defun bx-locals (forms)
  (cond ((atom forms) nil)
        (t (let ((form (car forms)))
             (append
              (cond ((atom form) nil)
                    ((eq (car form) 'local) (list (cadr form)))
                    ((eq (car form) 'encapsulate) (bx-locals (cddr form)))
                    ((member-eq (car form) '(progn progn!)) (bx-locals (cdr form)))
                    ((and (symbolp (car form))
                          (member-equal (symbol-name (car form))
                                        '("DEFSECTION" "DEFSECTION-PROGN"))
                          (consp (cdr form)))
                     (bx-locals (bx-skip-keywords (cddr form))))
                    (t nil))
              (bx-locals (cdr forms)))))))

(defun bx-read-forms (channel acc state)
  (mv-let (eofp obj state)
    (read-object channel state)
    (if eofp
        (mv (reverse acc) state)
      (bx-read-forms channel (cons obj acc) state))))

; The forms of the book whose source is the file FILE, read in the package
; its first form names.  Returns (mv forms state), with FORMS :error if
; the file cannot be opened.

(defun bx-book-forms (file state)
  (mv-let (channel state)
    (open-input-channel file :object state)
    (if (null channel)
        (mv :error state)
      (mv-let (eofp first state)
        (read-object channel state)
        (if eofp
            (pprogn (close-input-channel channel state) (mv nil state))
          (let ((pkg (case-match first
                       (('in-package (& . &)) nil)
                       (('in-package name) name)
                       (& nil)))
                (old (current-package state)))
            (if (and (stringp pkg)
                     (find-package-entry pkg (known-package-alist state)))
                (mv-let (erp val state)
                  (set-current-package pkg state)
                  (declare (ignore erp val))
                  (mv-let (forms state)
                    (bx-read-forms channel nil state)
                    (mv-let (erp val state)
                      (set-current-package old state)
                      (declare (ignore erp val))
                      (pprogn (close-input-channel channel state)
                              (mv (cons first forms) state)))))
              (mv-let (forms state)
                (bx-read-forms channel nil state)
                (pprogn (close-input-channel channel state)
                        (mv (cons first forms) state))))))))))

; A book's name as the aids give it: its file relative to ACL2's directory
; of books, or to the directory in which ACL2 runs, without ".lisp".

(defun bx-strip-prefix (prefix s)
  (if (and (<= (length prefix) (length s))
           (equal (subseq s 0 (length prefix)) prefix))
      (subseq s (length prefix) (length s))
    nil))

(defun bx-book-name (file state)
  (let* ((rel (or (bx-strip-prefix (system-books-dir state) file)
                  (bx-strip-prefix (cbd) file)
                  file))
         (n (length rel)))
    (if (and (< 5 n) (equal (subseq rel (- n 5) n) ".lisp"))
        (subseq rel 0 (- n 5))
      rel)))

(defun bx-local-items (name events)
  (cond ((endp events) nil)
        (t (cons (list "local" (list name (car events)))
                 (bx-local-items name (cdr events))))))

(defun bx-local-lines (files acc state)
  (cond ((endp files) (mv (reverse acc) state))
        (t (mv-let (forms state)
             (bx-book-forms (car files) state)
             (let ((name (bx-book-name (car files) state)))
               (bx-local-lines
                (cdr files)
                (if (eq forms :error)
                    (cons (bx-note "source of a book not read" name) acc)
                  (revappend (bx-local-items name (bx-locals forms)) acc))
                state))))))

(defun bx-book-files (evs)

; The source files of the books included in EVS, in the order of their
; events.

  (cond ((endp evs) nil)
        ((and (eq (access-event-tuple-type (car evs)) 'include-book)
              (stringp (access-event-tuple-namex (car evs))))
         (cons (access-event-tuple-namex (car evs)) (bx-book-files (cdr evs))))
        (t (bx-book-files (cdr evs)))))

; The aids of the events EVS, and the notes on the books whose source
; could not be read: (mv aids notes state).

(defun bx-remove-notes (items)
  (cond ((endp items) nil)
        ((eq (car (car items)) :note) (bx-remove-notes (cdr items)))
        (t (cons (car items) (bx-remove-notes (cdr items))))))

(defun bx-aids (evs state)
  (mv-let (locals state)
    (bx-local-lines (remove-duplicates-equal (bx-book-files evs)) nil state)
    (mv (append (bx-remove-notes locals) (bx-event-aids evs (w state)))
        (bx-select :note locals)
        state)))

; The books whose certificates carry the mark KEY, :skipped-proofsp or
; :axiomsp, among the entries (FULL-NAME USER-NAME FAMILIAR-NAME
; ANNOTATIONS . HASH) of ACL2's list of the books included.

(defun bx-marked-books (key alist state)
  (cond ((endp alist) nil)
        ((and (consp (car alist))
              (not (eq (car (car alist)) 'local))
              (consp (cdddr (car alist)))
              (cdr (assoc-eq key (cadddr (car alist)))))
         (let ((full (car (car alist))))
           (cons (cond ((stringp full) (bx-book-name full state))
                       ((and (consp full) (stringp (cdr full)))
                        (bx-book-name (cdr full) state))
                       (t full))
                 (bx-marked-books key (cdr alist) state))))
        (t (bx-marked-books key (cdr alist) state))))

; A book: the events numbered above LO and at most HI, which are those
; that including the book added to the world ACL2 starts with, whose last
; event is numbered BOOT-HI.  The statements of the library are computed
; again, so that the check of the order starts from the names they bring
; into use.  The program text has an attach line for each attachment in
; force that was not in force in the world ACL2 starts with.
; Writes PREFIX.statements, PREFIX.program, PREFIX.aids and PREFIX.notes.

(defun bx-export-book (ground-fns boot-hi lo hi prefix state)
  (let* ((wrld (w state))
         (boot-evs (bx-events wrld 0 boot-hi nil))
         (lib-items (bx-items (bx-enclose (reverse boot-evs) nil nil wrld)
                              nil nil wrld nil))
         (lib-stmts (bx-not-ground (bx-select :stmt lib-items) ground-fns))
         (items (bx-range-items lo hi wrld))
         (stmts (bx-select :stmt items))
         (progs (bx-select :prog items)))
    (mv-let (lib-ordered order-notes)
      (bx-library-order lib-stmts)
      (declare (ignore order-notes))
      (mv-let (fns names pkgs)
        (bx-ground-tables ground-fns boot-evs wrld)
        (mv-let (lib-notes fns names pkgs seen)
          (bx-check-stmts lib-ordered fns names pkgs nil nil)
          (declare (ignore lib-notes))
          (mv-let (check-notes fns names pkgs seen)
            (bx-check-stmts stmts fns names pkgs seen nil)
            (declare (ignore fns names pkgs))
            (mv-let (aids aid-notes state)
              (bx-aids (bx-events wrld lo hi nil) state)
            (let* ((pairs (bx-attachment-pairs wrld))
                   (boot-pairs (bx-attachment-pairs
                                (lookup-world-index 'event boot-hi wrld)))
                   (removed (set-difference-equal boot-pairs pairs))
                   (ttags (bx-book-ttags (global-val 'ttags-seen wrld)))
                   (skipped (bx-skipped (bx-events wrld lo hi nil)))
                   (book-alist (global-val 'include-book-alist wrld))
                   (skipped-books (bx-marked-books :skipped-proofsp book-alist state))
                   (axiom-books (bx-marked-books :axiomsp book-alist state))
                   (notes (bx-select :note
                                     (append items check-notes
                                             (if removed
                                                 (list (bx-note "attachment of the library not in force"
                                                                removed))
                                               nil)
                                             (if ttags
                                                 (list (bx-note "trust tags of the books, under which code beneath ACL2 may change what it does"
                                                                ttags))
                                               nil)
                                             (if skipped
                                                 (list (bx-note "events whose proofs ACL2 skipped"
                                                                skipped))
                                               nil)
                                             (if skipped-books
                                                 (list (bx-note "books whose certificates record skipped proofs"
                                                                skipped-books))
                                               nil)
                                             (if axiom-books
                                                 (list (bx-note "books whose certificates record axioms"
                                                                axiom-books))
                                               nil)
                                             (if (global-val 'redef-seen wrld)
                                                 (list (bx-note "redefinition, which ACL2 records"
                                                                (global-val 'redef-seen wrld)))
                                               nil)))))
              (prog2$
               (fast-alist-free seen)
               (pprogn
                (bm-write-file (bx-lines aids)
                               (concatenate 'string prefix ".aids") state)
                (bm-write-file (bx-lines stmts)
                               (concatenate 'string prefix ".statements") state)
                (bm-write-file (append (bx-lines (bx-runnable progs))
                                       (bx-lines (bx-attach-lines pairs boot-pairs)))
                               (concatenate 'string prefix ".program") state)
                (bm-write-file (append (bx-count-lines stmts)
                                       (bx-note-lines notes)
                                       (bx-note-lines aid-notes))
                               (concatenate 'string prefix ".notes") state)
                (value (list (len stmts) (len notes) (len aids)))))))))))))

