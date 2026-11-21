; The core of the exporter of PLAN.md, step 2: a pure function from
; ACL2's world, and the few things the shell hands it, to the lines that
; the exporter writes, as data.  It reads no file, writes none and takes
; no state.  export/export.lsp, the shell, takes the world from the
; session, calls BX-LIBRARY-LINES or BX-BOOK-LINES, prints each line with
; the printer of checks/canon.lisp and writes the files.  export/README.md
; says what each part does and what lies outside it.
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
;                must be the stored one, or no statement is written (a
;                function of no formals may have the longer axiom of
;                :STRENGTHEN T, which adds nothing; see BX-CHOOSE-ITEMS)
;   theorem      the stored formula (THEOREM) of a DEFTHM event
;   axiom        the stored formula of a DEFAXIOM event
;   package      the imports that ACL2's axiom NAME-PACKAGE gives
;   hidden-package  the imports that ACL2 keeps for a hidden package
;   reserve      a name under which ACL2 holds a macro, a constant, a
;                label, a theory or a single-threaded object
;
; A book's statements stand in the order of ACL2's events, with two
; changes.  The constraint of an encapsulate stands after the events
; inside it that are not part of the constraint, since its formulas may
; mention the functions those introduce.  But such an event may itself
; call a function of the constraint, and then its items stand right after
; the constraint (see BX-ITEMS).  The library's statements are ordered by
; section 7.
;
; What cannot be written as the specification asks is recorded in a note
; (see BX-NOTE), and the notes are written beside the files.
;
; Every function is in logic mode.  A recursion whose end is not plain
; from its arguments counts its steps with an argument FUEL.

(in-package "ACL2")

; REMOVE-GUARD-HOLDERS-WEAK, by which section 5 matches the formulas of a
; constraint, is in program mode in the world ACL2 starts with; this book
; of ACL2's distribution puts it in logic mode.

(include-book "system/remove-guard-holders-weak" :dir :system)

(set-verify-guards-eagerness 0)

;;; 0. Event tuples and guard holders

; A term with the calls of functions that only carry guards removed, as
; ACL2 stores some formulas of a constraint.  ACL2's REMOVE-GUARD-HOLDERS,
; in program mode, applies REMOVE-GUARD-HOLDERS-WEAK with the value of the
; function REMOVE-GUARD-HOLDERS-LAMP, whose attachment always gives T, and
; then also simplifies quoted lambda objects that it finds dirty; this
; does the first part only.

(defun bx-remove-guard-holders (term)
  (declare (xargs :guard (pseudo-termp term)))
  (remove-guard-holders-weak term t))

; ACL2 records each event as an event tuple, the value of the property
; GLOBAL-VALUE of the symbol EVENT-LANDMARK in the world.  These read its
; parts as ACL2's own functions ACCESS-EVENT-TUPLE-NUMBER and the rest do,
; which are in program mode.  A tuple, with (local . TUPLE) for one in a
; local context, is (N . FORM), or ((N . DEPTH) . FORM) when its depth is
; not 0, for an event in program mode whose names the form gives;
; otherwise FORM is preceded by ((TYPE . SKIPPED-PROOFS-P) NAMEX .
; SYMBOL-CLASS).  A cdr that is a symbol marks a tuple whose form ACL2
; did not keep.

(defun bx-ev-unlocal (x)
  (declare (xargs :guard (or (consp x) (null x))))
  (if (eq (car x) 'local) (cdr x) x))

; The event readers distinguish a compact program event form from a
; tuple with a separate header.  Only the fields they read are checked.

(defun bx-event-fields-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (or (integerp (car x))
           (and (consp (car x)) (rationalp (cdar x))))
       (true-listp (cdr x))
       (let ((header (cadr x)))
         (if (symbolp header)
             (case header
               (defuns (alistp (cddr x)))
               (mutual-recursion (all->=-len (cddr x) 2))
               (encapsulate (alistp (caddr x)))
               (otherwise t))
           (and (consp header)
                (or (consp (car header)) (null (car header)))
                (or (consp (cdr header)) (null (cdr header))))))))

(defun bx-event-tuple-p (x)
  (declare (xargs :guard t))
  (and (consp x) (bx-event-fields-p (bx-ev-unlocal x))))

(defun bx-ev-number (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (if (integerp (car x)) (car x) (car (car x)))))

(defun bx-ev-depth (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (if (integerp (car x)) 0 (cdr (car x)))))

(defun bx-ev-type (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (cond ((symbolp (cdr x)) nil)
          ((symbolp (cadr x))
           (if (eq (cadr x) 'mutual-recursion) 'defuns (cadr x)))
          (t (car (car (cadr x)))))))

(defun bx-ev-skipped-proofs-p (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (cond ((symbolp (cdr x)) nil)
          ((symbolp (cadr x)) nil)
          (t (cdr (car (cadr x)))))))

; The functions that the signatures of an encapsulate name, as ACL2's
; SIGNATURE-FNS gives them: each signature is ((FN ...) => VAL) or (FN
; ...).

(defun bx-signature-fns (signatures)
  (declare (xargs :guard (alistp signatures)))
  (cond ((endp signatures) nil)
        ((consp (car (car signatures)))
         (cons (car (car (car signatures)))
               (bx-signature-fns (cdr signatures))))
        (t (cons (car (car signatures))
                 (bx-signature-fns (cdr signatures))))))

(defun bx-ev-namex (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (cond ((symbolp (cdr x)) nil)
          ((symbolp (cadr x))
           (case (cadr x)
             (defuns (strip-cars (cddr x)))
             (mutual-recursion (strip-cadrs (cddr x)))
             ((verify-guards in-theory in-arithmetic-theory
               regenerate-tau-database push-untouchable remove-untouchable
               reset-prehistory set-body table)
              0)
             (encapsulate (bx-signature-fns (caddr x)))
             (t (caddr x))))
          (t (car (cdr (cadr x)))))))

(defun bx-ev-form (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (if (symbolp (cadr x)) (cdr x) (cddr x))))

(defun bx-ev-symbol-class (x)
  (declare (xargs :guard (bx-event-tuple-p x)))
  (let ((x (bx-ev-unlocal x)))
    (if (symbolp (cadr x)) :program (cdr (cdr (cadr x))))))

;;; 1. Small tools

(defun bx-names (namex)
  (declare (xargs :guard t))
  (cond ((eql namex 0) nil)
        ((or (symbolp namex) (stringp namex)) (list namex))
        (t namex)))

(defun bx-note (key data)
  (declare (xargs :guard t))
  (list :note key data))

(defun bx-stmt (word args)
  (declare (xargs :guard t))
  (list :stmt word args))

(defun bx-prog (word args)
  (declare (xargs :guard t))
  (list :prog word args))

; A definition form has a symbol for its name and a proper list of
; fields.  These predicates also apply to the compact forms of events.

(defun bx-definition-forms-p (defs)
  (declare (xargs :guard t))
  (if (consp defs)
      (and (consp (car defs))
           (symbolp (caar defs))
           (true-listp (car defs))
           (bx-definition-forms-p (cdr defs)))
    (null defs)))

(defun bx-defun-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (case (car form)
         (defun (and (consp (cdr form)) (symbolp (cadr form))))
         (defuns (bx-definition-forms-p (cdr form)))
         (mutual-recursion (and (alistp (cdr form))
                                (bx-definition-forms-p (strip-cdrs (cdr form)))))
         (otherwise t))))

; Only the kinds of event used for export constrain the type of a name.

(defun bx-event-names-p (ev)
  (declare (xargs :guard (bx-event-tuple-p ev)))
  (let ((names (bx-names (bx-ev-namex ev))))
    (case (bx-ev-type ev)
      ((defun defuns) (and (symbol-listp names)
                           (bx-defun-form-p (bx-ev-form ev))))
      ((defthm defaxiom defchoose encapsulate defmacro defconst
        deflabel deftheory defstobj defabsstobj)
       (symbol-listp names))
      (defpkg (and (consp names) (stringp (car names)) (true-listp names)))
      (otherwise (true-listp names)))))

(defun bx-event-list-p (evs)
  (declare (xargs :guard t))
  (if (consp evs)
      (and (bx-event-tuple-p (car evs))
           (bx-event-names-p (car evs))
           (bx-event-list-p (cdr evs)))
    (null evs)))

(defun bx-event-world-p (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (endp wrld)
      t
    (and (or (not (and (eq (caar wrld) 'event-landmark)
                       (eq (cadar wrld) 'global-value)))
             (let ((ev (cddar wrld)))
               (and (bx-event-tuple-p ev) (bx-event-names-p ev))))
         (bx-event-world-p (cdr wrld)))))

; The property values used by the exporter. Unbound properties are
; read using the caller's default. Other properties can have any value.

(defun bx-justification-p (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (>=-len x 4)
           (eq (car x) 'justification)
           (listp (caddr x))
           (listp (cdr (caddr x)))
           (listp (cadddr x)))))

(defun bx-attachment-property-p (x)
  (declare (xargs :guard t))
  (or (atom x) (eq (car x) :attachment-disallowed) (alistp x)))

(defun bx-ttags-alist-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (true-listp (cdar x))
           (bx-ttags-alist-p (cdr x)))
    (null x)))

(defun bx-book-alist-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (atom (car x))
               (eq (caar x) 'local)
               (and (listp (cdar x))
                    (listp (cddar x))
                    (listp (cdddar x))
                    (or (atom (cdddar x))
                        (alistp (car (cdddar x))))))
           (bx-book-alist-p (cdr x)))
    (null x)))

(defun bx-package-import-formula-p (rule formula)
  (declare (xargs :guard t))
  (case-match formula
    (('equal ('pkg-imports ('quote name)) ('quote imports))
     (or (not (and (stringp name)
                   (eq rule (intern-in-package-of-symbol
                             (concatenate 'string name "-PACKAGE") 'acl2::x))))
         (symbol-listp imports)))
    (& t)))

(defun bx-property-value-p (name key val)
  (declare (xargs :guard t))
  (or (eq val *acl2-property-unbound*)
      (case key
        (formals (and (not (eq name 'quote)) (symbol-listp val)))
        ((unnormalized-body defchoose-axiom) (pseudo-termp val))
        (theorem (and (pseudo-termp val) (bx-package-import-formula-p name val)))
        (constraint-lst-etc (listp val))
        (justification (bx-justification-p val))
        (siblings (symbol-listp val))
        (absolute-event-number (rationalp val))
        (attachment (bx-attachment-property-p val))
        (otherwise t))))

(defun bx-property-values-p (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (endp wrld)
      t
    (and (bx-property-value-p (caar wrld) (cadar wrld) (cddar wrld))
         (bx-property-values-p (cdr wrld)))))

(defun bx-world-properties-p (wrld)
  (declare (xargs :guard t))
  (and (plist-worldp wrld) (bx-property-values-p wrld)))

(defun bx-function-p (sym wrld)
  (declare (xargs :guard (and (symbolp sym) (plist-worldp wrld))))

; Whether SYM is a function.  The formals of a function of no arguments
; are NIL, so the test is whether the property is present at all.

  (not (eq (getpropc sym 'formals t wrld) t)))

(defun bx-functions-present-p (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld))))
  (if (endp fns)
      t
    (and (bx-function-p (car fns) wrld)
         (bx-functions-present-p (cdr fns) wrld))))

(defun bx-in-use-p (sym wrld)
  (declare (xargs :guard (and (symbolp sym) (plist-worldp wrld))))

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
  (declare (xargs :guard (and (symbolp sym) (plist-worldp wrld))))
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
  (declare (xargs :guard (and (symbolp fn) (bx-world-properties-p wrld))))
  (not (eq (car (getpropc fn 'constraint-lst-etc '(t . nil) wrld)) t)))

(defun bx-programp (fn wrld)
  (declare (xargs :guard (and (symbolp fn) (plist-worldp wrld))))
  (eq (getpropc fn 'symbol-class nil wrld) :program))

(defun bx-rulers (fn wrld)
  (declare (xargs :guard (and (symbolp fn) (bx-world-properties-p wrld))))
  (let ((just (getpropc fn 'justification nil wrld)))
    (and just (access justification just :ruler-extenders))))

(defun bx-event-number (name wrld)
  (declare (xargs :guard (and (symbolp name) (bx-world-properties-p wrld))))
  (getpropc name 'absolute-event-number 0 wrld))

; A constraint owner is the name under which ACL2 has stored the list
; of formulas or the mark for an unknown constraint.

(defun bx-constraint-owner-p (name wrld)
  (declare (xargs :guard (and (symbolp name) (plist-worldp wrld))))
  (let ((val (getpropc name 'constraint-lst-etc nil wrld)))
    (and (consp val)
         (or (unknown-constraints-p (car val)) (pseudo-term-listp (car val)))
         (let ((siblings (getpropc name 'siblings nil wrld)))
           (and (symbol-listp siblings)
                (bx-functions-present-p siblings wrld))))))

(defun bx-constrainer-input-p (name wrld)
  (declare (xargs :guard (and (symbolp name) (plist-worldp wrld))))
  (let ((val (getpropc name 'constraint-lst-etc nil wrld)))
    (and (consp val)
         (not (eq (car val) t))
         (bx-constraint-owner-p (if (and (car val) (symbolp (car val)))
                                    (car val)
                                  name)
                                wrld))))

; The name given to a formula of a constraint that has no name of its own
; in ACL2.  The definition of a function defined inside the encapsulate,
; and the axiom of a function introduced there by choice, ACL2 holds under
; the function's name; but spec/logic.md lets no line introduce one name
; twice.  A corollary that a rule class of a theorem adds to the
; constraint has no name.  Such a formula is named by the function's name
; followed by the word "definition" or "choice", or by the name of the
; constraint followed by "constraint" and the formula's position, in the
; package of that name, with a number added if the name is in use.

; A made name must be a symbol of the package of FN itself.  The package
; may import a symbol with the name tried, and interning then gives that
; symbol, which another package may import too, so that two constraints
; would take one name; or it may be a keyword, and a name is a symbol
; that is not a keyword (spec/language.md, section 6).  Such a name is
; passed over as one in use is.  So two names made for different formulas
; differ: in different packages they are different symbols, and in one
; package their texts differ, since a text NAME WORD or NAME WORD N, where
; WORD is "definition", "choice" or "constraint" and a position, and N a
; number of one or more digits with no leading zero, determines NAME, WORD
; and N.  Nor is a made name one that ACL2 holds in the world (see
; BX-IN-USE-P).  At most *BX-NAME-TRIES* numbers are tried; if every name
; tried is passed over, the result is NIL, and no statement is written
; for the constraint that needs the name (see BX-CONSTRAIN-STMT).

(defconst *bx-name-tries* 1000)

(defun bx-fresh-name (base i fn wrld fuel)
  (declare (xargs :guard (and (stringp base) (natp i) (symbolp fn)
                              (plist-worldp wrld) (natp fuel))
                  :measure (nfix fuel)))
  (let ((sym (intern-in-package-of-symbol
              (if (equal i 0)
                  base
                (concatenate 'string base " "
                             (coerce (explode-nonnegative-integer i 10 nil)
                                     'string)))
              fn)))
    (cond ((not (or (bx-in-use-p sym wrld)
                    (keywordp sym)
                    (not (equal (symbol-package-name sym)
                                (symbol-package-name fn)))))
           sym)
          ((zp fuel) nil)
          (t (bx-fresh-name base (+ 1 (nfix i)) fn wrld (- fuel 1))))))

(defun bx-formula-name (fn word wrld)
  (declare (xargs :guard (and (symbolp fn) (stringp word) (plist-worldp wrld))))
  (bx-fresh-name (concatenate 'string (symbol-name fn) " " word) 0 fn wrld
                 *bx-name-tries*))

(defun bx-add-names (names table)
  (declare (xargs :guard (true-listp names)))
  (cond ((endp names) table)
        (t (bx-add-names (cdr names) (hons-acons (car names) t table)))))

; The functions a statement introduces, and the functions its terms call.

(defun bx-bodies (defs)
  (declare (xargs :guard (true-list-listp defs)))
  (cond ((endp defs) nil)
        (t (cons (caddr (car defs)) (bx-bodies (cdr defs))))))

; A line's data must support the selectors and term walks used by the
; core. The format's requirements on names and arities are separate.

(defun bx-definitions-p (defs)
  (declare (xargs :guard t))
  (if (consp defs)
      (and (consp (car defs))
           (true-listp (car defs))
           (symbolp (caar defs))
           (pseudo-termp (caddar defs))
           (bx-definitions-p (cdr defs)))
    (null defs)))

(defun bx-named-formulas-p (formulas)
  (declare (xargs :guard t))
  (if (consp formulas)
      (and (>=-len (car formulas) 2)
           (symbolp (caar formulas))
           (pseudo-termp (cadar formulas))
           (bx-named-formulas-p (cdr formulas)))
    (null formulas)))

(defun bx-arity-list-p (pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (and (>=-len (car pairs) 2)
           (true-listp (car pairs))
           (symbolp (caar pairs))
           (bx-arity-list-p (cdr pairs)))
    (null pairs)))

(defun bx-line-p (line)
  (declare (xargs :guard t))
  (and (consp line)
       (true-listp line)
       (stringp (car line))
       (let ((word (car line)) (args (cadr line)))
         (and (true-listp args)
              (cond
                ((equal word "define") (bx-definitions-p (cdr args)))
                ((equal word "constrain") (and (bx-arity-list-p (car args))
                                               (bx-named-formulas-p (cadr args))))
                ((equal word "choose")
                 (and (symbolp (car args)) (pseudo-termp (cadddr args))))
                ((member-equal word '("theorem" "axiom"))
                 (and (symbolp (car args)) (pseudo-termp (cadr args))))
                ((equal word "reserve") (symbolp (car args)))
                ((member-equal word '("package" "hidden-package"))
                 (and (stringp (car args)) (symbol-listp (cadr args))))
                (t t))))))

(defun bx-line-list-p (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (bx-line-p (car lines)) (bx-line-list-p (cdr lines)))
    (null lines)))

(defun bx-definition-lines-p (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (bx-line-p (car lines))
           (equal (caar lines) "define")
           (bx-definition-lines-p (cdr lines)))
    (null lines)))

(defun bx-item-list-p (items)
  (declare (xargs :guard t))
  (if (consp items)
      (and (consp (car items))
           (case (caar items)
             (:stmt (bx-line-p (cdar items)))
             (:prog (and (bx-line-p (cdar items))
                         (equal (cadar items) "define")))
             (:note (true-listp (cdar items)))
             (otherwise t))
           (bx-item-list-p (cdr items)))
    (null items)))

(defun bx-introduced (stmt)
  (declare (xargs :guard (bx-line-p stmt)))
  (let ((word (car stmt)) (args (cadr stmt)))
    (cond ((equal word "define") (strip-cars (cdr args)))
          ((equal word "constrain") (strip-cars (car args)))
          ((equal word "choose") (list (car args)))
          (t nil))))

(defun bx-used (stmt)
  (declare (xargs :guard (bx-line-p stmt)))
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
  (declare (xargs :guard (and (plist-worldp wrld) (bx-event-world-p wrld)
                              (integerp lo) (integerp hi) (bx-event-list-p acc))))
  (cond ((endp wrld) acc)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value))
         (let* ((ev (cddar wrld))
                (n (bx-ev-number ev)))
           (cond ((not (integerp n)) acc)
                 ((<= n lo) acc)
                 ((< hi n) (bx-events (cdr wrld) lo hi acc))
                 (t (bx-events (cdr wrld) lo hi (cons ev acc))))))
        (t (bx-events (cdr wrld) lo hi acc))))

; The name under which ACL2 stores the constraint of an encapsulate event
; with a signature, or NIL.

(defun bx-event-constraint-p (ev wrld)
  (declare (xargs :guard (and (bx-event-tuple-p ev)
                              (bx-event-names-p ev)
                              (plist-worldp wrld))))
  (or (not (eq (bx-ev-type ev) 'encapsulate))
      (not (consp (bx-ev-namex ev)))
      (bx-constrainer-input-p (car (bx-ev-namex ev)) wrld)))

(defun bx-event-constraints-p (evs wrld)
  (declare (xargs :guard (and (bx-event-list-p evs) (plist-worldp wrld))))
  (if (endp evs)
      t
    (and (bx-event-constraint-p (car evs) wrld)
         (bx-event-constraints-p (cdr evs) wrld))))

(defun bx-constrainer (ev wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (bx-event-tuple-p ev)
                              (bx-event-names-p ev)
                              (bx-event-constraint-p ev wrld))))
  (and (eq (bx-ev-type ev) 'encapsulate)
       (consp (bx-ev-namex ev))
       (mv-let (name lst origins)
         (constraint-info (car (bx-ev-namex ev)) wrld)
         (declare (ignore lst origins))
         name)))

; Each event is paired with the constrainer of the innermost encapsulate
; with a signature that contains it.  An encapsulate's own event stands
; after the events inside it, which have a greater depth.  EVS is newest
; first, STACK holds pairs (depth . constrainer) of the encapsulates whose
; events are being passed, and the result is oldest first.

(defun bx-depth-stack-p (stack)
  (declare (xargs :guard t))
  (if (consp stack)
      (and (consp (car stack))
           (rationalp (caar stack))
           (symbolp (cdar stack))
           (bx-depth-stack-p (cdr stack)))
    (null stack)))

(defun bx-pop (stack d)
  (declare (xargs :guard (and (bx-depth-stack-p stack) (rationalp d))))
  (cond ((endp stack) nil)
        ((<= d (car (car stack))) (bx-pop (cdr stack) d))
        (t stack)))

(defun bx-first-constrainer (stack)
  (declare (xargs :guard (bx-depth-stack-p stack)))
  (cond ((endp stack) nil)
        ((cdr (car stack)) (cdr (car stack)))
        (t (bx-first-constrainer (cdr stack)))))

(defun bx-enclose (evs stack acc wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (bx-event-list-p evs)
                              (bx-event-constraints-p evs wrld)
                              (bx-depth-stack-p stack))))
  (cond ((endp evs) acc)
        (t (let* ((ev (car evs))
                  (d (bx-ev-depth ev))
                  (stack (bx-pop stack d))
                  (encl (bx-first-constrainer stack))
                  (stack (if (eq (bx-ev-type ev) 'encapsulate)
                             (cons (cons d (bx-constrainer ev wrld)) stack)
                           stack)))
             (bx-enclose (cdr evs) stack (cons (cons ev encl) acc) wrld)))))

;;; 3. Terms

; A term with every lambda application replaced by its body, with the
; actuals put for the formals.  ALIST maps the formals of the lambdas
; passed to the terms put for them.  Since the body of every lambda of a
; term is closed, this gives each term its one form with no lambda
; application.

(mutual-recursion

 (defun bx-beta-in (term alist)
   (declare (xargs :guard (and (pseudo-termp term) (alistp alist))))
   (cond ((variablep term)
          (let ((pair (assoc-eq term alist)))
            (if pair (cdr pair) term)))
         ((fquotep term) term)
         ((flambda-applicationp term)
          (bx-beta-in (lambda-body (ffn-symb term))
                      (pairlis$ (lambda-formals (ffn-symb term))
                                (bx-beta-in-lst (fargs term) alist))))
         (t (cons (ffn-symb term) (bx-beta-in-lst (fargs term) alist)))))

 (defun bx-beta-in-lst (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms) (alistp alist))))
   (cond ((endp terms) nil)
         (t (cons (bx-beta-in (car terms) alist)
                  (bx-beta-in-lst (cdr terms) alist))))))

(defun bx-beta (term)
  (declare (xargs :guard (pseudo-termp term)))
  (bx-beta-in term nil))

; The body that ACL2 runs for a function in program mode: each mbe is
; replaced by its executable half, that is, each call (return-last
; 'mbe1-raw EXEC LOGIC) by EXEC, since ACL2 runs such a function as its
; Common Lisp code (spec/language.md, section 7).

(mutual-recursion

 (defun bx-exec (term)
   (declare (xargs :guard (pseudo-termp term)))
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
   (declare (xargs :guard (pseudo-term-listp terms)))
   (cond ((endp terms) nil)
         (t (cons (bx-exec (car terms)) (bx-exec-lst (cdr terms)))))))

;;; 4. Functions introduced by choice

; The axiom of spec/logic.md, section 6, for (choose FN BOUND FREE BODY
; FREE2).

(defun bx-mv-nths (k i call)
  (declare (xargs :guard t
                  :measure (nfix (- k i))))
  (cond ((or (not (natp i)) (not (natp k)) (<= k i)) nil)
        (t (cons (list 'mv-nth (kwote i) call)
                 (bx-mv-nths k (+ 1 i) call)))))

; The basic axiom, or with STRONG the longer one, whose second call of FN
; is on FREE2.  The axiom of spec/logic.md is the longer one exactly when
; FREE2 is not NIL.

(defun bx-choose-literal (fn bound free body free2 strong)
  (declare (xargs :guard (and (symbolp fn) (not (eq fn 'quote))
                              (consp bound) (symbol-listp bound)
                              (pseudo-term-listp free) (pseudo-termp body)
                              (or (not strong)
                                  (and (symbol-listp free)
                                       (pseudo-term-listp free2)
                                       (equal (len free) (len free2)))))))
  (let* ((call (cons fn free))
         (terms (if (cdr bound) (bx-mv-nths (len bound) 0 call) (list call)))
         (inst (subcor-var bound terms body))
         (basic0 (list 'implies body inst))
         (basic (if (cdr bound)
                    (list 'if (list 'true-listp call) basic0 ''nil)
                  basic0)))
    (if (not strong)
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

(defun bx-choose-axiom (fn bound free body free2)
  (declare (xargs :guard (and (symbolp fn) (not (eq fn 'quote))
                              (consp bound) (symbol-listp bound)
                              (pseudo-term-listp free) (pseudo-termp body)
                              (or (null free2)
                                  (and (symbol-listp free)
                                       (pseudo-term-listp free2)
                                       (equal (len free) (len free2)))))))
  (bx-choose-literal fn bound free body free2 (not (null free2))))

; Reading BOUND, BODY and FREE2 from the axiom ACL2 stores.  The basic
; axiom is (implies BODY ((lambda VARS BODY) . ACTUALS)), where the bound
; variable is the formal whose actual is the call of FN; or, with several
; bound variables, (if (true-listp CALL) (implies BODY ((lambda (MV . R)
; ((lambda VARS BODY) . ACTUALS)) CALL . R)) 'nil), where the bound
; variables are the formals whose actuals are (mv-nth 'I MV), in the order
; of I.  A strengthened axiom is (if BASIC (if (equal CALL CALL2) ...)
; 'nil), and FREE2 is the arguments of CALL2.

(defun bx-bound-one (formals actuals call)
  (declare (xargs :guard (and (true-listp formals) (true-listp actuals)
                              (<= (len formals) (len actuals)))))
  (cond ((endp formals) nil)
        ((equal (car actuals) call) (list (car formals)))
        (t (bx-bound-one (cdr formals) (cdr actuals) call))))

(defun bx-bound-index (formals actuals mv i)
  (declare (xargs :guard (and (true-listp formals) (true-listp actuals)
                              (<= (len formals) (len actuals)))))
  (cond ((endp formals) nil)
        ((equal (car actuals) (list 'mv-nth (kwote i) mv)) (car formals))
        (t (bx-bound-index (cdr formals) (cdr actuals) mv i))))

; There are at most as many bound variables as formals: FUEL counts them.

(defun bx-bound-many (formals actuals mv i fuel)
  (declare (xargs :guard (and (true-listp formals) (true-listp actuals)
                              (<= (len formals) (len actuals)) (natp fuel))
                  :measure (nfix fuel)))
  (let ((v (bx-bound-index formals actuals mv i)))
    (if (and v (not (zp fuel)))
        (cons v (bx-bound-many formals actuals mv (+ 1 (nfix i)) (- fuel 1)))
      nil)))

(defun bx-choose-parts (axiom fn wrld)
  (declare (xargs :guard (and (pseudo-termp axiom) (symbolp fn)
                              (plist-worldp wrld) (bx-function-p fn wrld))))

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
          (mv (bx-bound-many vars actuals mv 0 (len vars)) body free2))
         (& (mv nil nil nil))))
      (& (mv nil nil nil)))))

; A strengthened choice axiom compares two calls of FN. Their argument
; lists have the same length as the stored formals of FN.

(defun bx-choice-input-p (fn wrld)
  (declare (xargs :guard (and (symbolp fn) (plist-worldp wrld))))
  (and (not (eq fn 'quote))
       (bx-function-p fn wrld)
       (let ((axiom (getpropc fn 'defchoose-axiom nil wrld)))
         (case-match axiom
           (('if & ('if ('equal (!fn . &) (!fn . free2)) . &) ''nil)
            (or (null free2) (equal (len free2) (len (formals fn wrld)))))
           (& t)))))

;;; 5. The items of one event

; An item is (:stmt WORD ARGS), a statement; (:prog WORD ARGS), a line of
; program text only; or (:note KEY DATA).  A definition in logic mode is
; both a statement and a line of program text.

; The definitions of an event form, each (NAME FORMALS ... BODY).

(defun bx-defun-forms (form)
  (declare (xargs :guard (bx-defun-form-p form)))
  (case (car form)
    (defun (list (cdr form)))
    (defuns (cdr form))
    (mutual-recursion (strip-cdrs (cdr form)))
    (otherwise nil)))

; A function in program mode whose body the world does not store, as in
; the world ACL2 starts with: its body is translated from the event that
; defined it.  Translation is the work of ACL2's function TRANSLATE-CMP,
; which needs the state of the session, so the shell does it: it asks
; BX-TRANSLATION-REQUESTS which bodies to translate, and hands back
; TRANSLATIONS, which pairs each function with (:ok . TERM) or with
; (:error . MESSAGE).  The result is (mv body-or-nil note-or-nil).

(defun bx-needs-translation-p (fn wrld)
  (declare (xargs :guard (and (symbolp fn) (plist-worldp wrld))))
  (and (null (getpropc fn 'unnormalized-body nil wrld))
       (not (member-eq fn *initial-program-fns-with-raw-code*))))

(defun bx-translations-p (translations)
  (declare (xargs :guard t))
  (if (consp translations)
      (and (consp (car translations))
           (listp (cdar translations))
           (or (not (eq (cadar translations) :ok))
               (pseudo-termp (cddar translations)))
           (bx-translations-p (cdr translations)))
    (null translations)))

(defun bx-program-body (fn form translations wrld)
  (declare (xargs :guard (and (symbolp fn) (bx-defun-form-p form)
                              (bx-translations-p translations)
                              (bx-world-properties-p wrld))))
  (let ((body (getpropc fn 'unnormalized-body nil wrld)))
    (cond
     (body (mv body nil))
     ((member-eq fn *initial-program-fns-with-raw-code*)
      (mv nil (bx-note "program function with raw code" fn)))
     (t (let ((def (assoc-eq fn (bx-defun-forms form)))
              (tr (cdr (assoc-eq fn translations))))
          (cond ((null def)
                 (mv nil (bx-note "program function whose event has no defun" fn)))
                ((eq (car tr) :ok) (mv (cdr tr) nil))
                (t (mv nil (bx-note "program function whose body ACL2 does not translate"
                                    (list fn (cdr tr)))))))))))

(defun bx-program-defs (fns form translations wrld defs notes)
  (declare (xargs :guard (and (symbol-listp fns) (bx-defun-form-p form)
                              (bx-translations-p translations)
                              (bx-world-properties-p wrld)
                              (bx-functions-present-p fns wrld)
                              (bx-definitions-p defs) (bx-item-list-p notes))))
  (cond ((endp fns) (mv (reverse defs) (reverse notes)))
        (t (mv-let (body note)
             (bx-program-body (car fns) form translations wrld)
             (bx-program-defs (cdr fns) form translations wrld
                              (if body
                                  (cons (list (car fns)
                                              (formals (car fns) wrld)
                                              (bx-exec body))
                                        defs)
                                defs)
                              (if note (cons note notes) notes))))))

(defun bx-defs (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld)
                              (bx-functions-present-p fns wrld))))
  (cond ((endp fns) nil)
        (t (cons (list (car fns)
                       (formals (car fns) wrld)
                       (getpropc (car fns) 'unnormalized-body nil wrld))
                 (bx-defs (cdr fns) wrld)))))

(defun bx-same-rulers (fns rulers wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld))))
  (or (endp fns)
      (and (equal (bx-rulers (car fns) wrld) rulers)
           (bx-same-rulers (cdr fns) rulers wrld))))

(defun bx-all-program-p (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld))))
  (or (endp fns)
      (and (bx-programp (car fns) wrld)
           (bx-all-program-p (cdr fns) wrld))))

(defun bx-some-program-p (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld))))
  (and (consp fns)
       (or (bx-programp (car fns) wrld)
           (bx-some-program-p (cdr fns) wrld))))

(defun bx-all-constrained-p (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld))))
  (or (endp fns)
      (and (bx-constrained-p (car fns) wrld)
           (bx-all-constrained-p (cdr fns) wrld))))

(defun bx-some-constrained-p (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld))))
  (and (consp fns)
       (or (bx-constrained-p (car fns) wrld)
           (bx-some-constrained-p (cdr fns) wrld))))

(defun bx-define-items (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld)
                              (bx-functions-present-p fns wrld))))
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

(defun bx-candidate-list-p (cands wrld allow-later)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (consp cands)
      (and (>=-len (car cands) 3)
           (symbolp (caar cands))
           (case (cadar cands)
             (:formula (pseudo-termp (caddar cands)))
             (:after (and allow-later (bx-item-list-p (caddar cands))))
             (otherwise
              (and (symbolp (caddar cands))
                   (not (eq (caddar cands) 'quote))
                   (bx-function-p (caddar cands) wrld))))
           (bx-candidate-list-p (cdr cands) wrld allow-later))
    (null cands)))

(defun bx-pending-p (pending wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (consp pending)
      (and (consp (car pending))
           (bx-candidate-list-p (cdar pending) wrld t)
           (bx-pending-p (cdr pending) wrld))
    (null pending)))

(defun bx-add-candidates (encl cands pending)
  (declare (xargs :guard (and (symbolp encl) (true-listp cands) (alistp pending)
                              (true-listp (cdr (assoc-eq encl pending))))))
  (put-assoc-eq encl
                (append (cdr (assoc-eq encl pending)) cands)
                pending))

(defun bx-definition-candidates (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld))))
  (cond ((endp fns) nil)
        (t (cons (list (bx-formula-name (car fns) "definition" wrld)
                       :definition (car fns))
                 (bx-definition-candidates (cdr fns) wrld)))))

(defun bx-mentions-some (term fns)
  (declare (xargs :guard (and (pseudo-termp term) (symbol-listp fns))))
  (intersectp-eq (all-fnnames term) fns))

; The defined functions of a DEFSTOBJ or DEFABSSTOBJ event, in an order in
; which each follows the functions of the event that its body calls.

(defun bx-ready (todo placed wrld)
  (declare (xargs :guard (and (symbol-listp todo) (symbol-listp placed)
                              (bx-world-properties-p wrld))))
  (cond ((endp todo) nil)
        ((subsetp-eq (intersection-eq
                      (all-fnnames (getpropc (car todo) 'unnormalized-body
                                             nil wrld))
                      (set-difference-eq todo (list (car todo))))
                     placed)
         (cons (car todo) (bx-ready (cdr todo) placed wrld)))
        (t (bx-ready (cdr todo) placed wrld))))

; Each round places at least one function, so FUEL, the number of the
; functions, bounds the rounds.

(defun bx-local-order (todo placed acc wrld fuel)
  (declare (xargs :guard (and (symbol-listp todo) (symbol-listp placed)
                              (symbol-listp acc) (bx-world-properties-p wrld)
                              (natp fuel))
                  :measure (nfix fuel)))
  (cond ((endp todo) (reverse acc))
        (t (let ((ready (bx-ready todo placed wrld)))
             (if (or (null ready) (zp fuel))
                 (append (reverse acc) todo)
               (bx-local-order (set-difference-eq todo ready)
                               (append ready placed)
                               (revappend ready acc)
                               wrld
                               (- fuel 1)))))))

(defun bx-stobj-define-items (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld)
                              (bx-functions-present-p fns wrld))))
  (cond ((endp fns) nil)
        (t (append (bx-define-items (list (car fns)) wrld)
                   (bx-stobj-define-items (cdr fns) wrld)))))

(defun bx-stobj-items (names defined fns-acc wrld acc)
  (declare (xargs :guard (and (symbol-listp names) (symbol-listp fns-acc)
                              (bx-world-properties-p wrld)
                              (bx-functions-present-p fns-acc wrld)
                              (bx-item-list-p acc))))

; The items for the names of a DEFSTOBJ or DEFABSSTOBJ event.  FNS-ACC
; collects the functions in logic mode with a body.  DEFINED maps each
; function that an earlier statement defines to T: a DEFABSSTOBJ event
; defines its functions by events of its own, which stand before it.

  (cond ((endp names)
         (append (reverse acc)
                 (bx-stobj-define-items
                  (bx-local-order (reverse fns-acc) nil nil wrld (len fns-acc)) wrld)))
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

(defun bx-conjuncts (formula lst)
  (declare (xargs :guard (and (pseudo-termp formula) (true-listp lst))))

; The conjuncts of FORMULA, as ACL2 puts them in a constraint, if they are
; all members of LST; otherwise :none.

  (let ((c1 (flatten-ands-in-lit formula)))
    (if (subsetp-equal c1 lst)
        c1
      (let ((c2 (flatten-ands-in-lit (bx-remove-guard-holders formula))))
        (if (subsetp-equal c2 lst) c2 :none)))))

(defun bx-equation-in (fn lst wrld)
  (declare (xargs :guard (and (symbolp fn) (true-listp lst) (plist-worldp wrld)
                              (bx-function-p fn wrld))))

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
  (declare (xargs :guard (and (plist-worldp wrld)
                              (bx-candidate-list-p cands wrld nil)
                              (pseudo-term-listp lst)
                              (bx-named-formulas-p formulas) (true-listp covered)
                              (bx-item-list-p notes))))
  (cond
   ((endp cands) (mv (reverse formulas) covered (reverse notes)))
   (t (let* ((cand (car cands))
             (term (if (eq (cadr cand) :formula)
                       (caddr cand)
                     (bx-equation-in (caddr cand) lst wrld)))
             (conj (if term (bx-conjuncts term lst) :none)))
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
  (declare (xargs :guard (and (pseudo-term-listp lst) (true-listp covered)
                              (symbolp c) (natp i) (plist-worldp wrld)
                              (bx-named-formulas-p formulas)
                              (bx-item-list-p notes))))
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
  (declare (xargs :guard (and (pseudo-term-listp lst) (symbolp c)
                              (plist-worldp wrld)
                              (bx-candidate-list-p cands wrld nil))))

; Returns (mv formulas notes).

  (mv-let (formulas covered notes)
    (bx-candidate-terms cands lst c wrld nil nil nil)
    (mv-let (more notes2)
      (bx-uncovered lst covered c 1 wrld nil nil)
      (mv (append formulas more) (append notes notes2)))))

(defun bx-arities (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld)
                              (bx-functions-present-p fns wrld))))
  (cond ((endp fns) nil)
        (t (cons (list (car fns) (len (formals (car fns) wrld)))
                 (bx-arities (cdr fns) wrld)))))

(defun bx-insert-by-event (fn fns wrld)
  (declare (xargs :guard (and (symbolp fn) (symbol-listp fns)
                              (bx-world-properties-p wrld))))
  (cond ((endp fns) (list fn))
        ((< (bx-event-number fn wrld) (bx-event-number (car fns) wrld))
         (cons fn fns))
        (t (cons (car fns) (bx-insert-by-event fn (cdr fns) wrld)))))

(defun bx-sort-by-event (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld))))

; FNS sorted by the numbers of the events that introduced them, the
; earliest first.  It is short, so insertion will do.

  (cond ((endp fns) nil)
        (t (bx-insert-by-event (car fns) (bx-sort-by-event (cdr fns) wrld) wrld))))

; Where ACL2 records no constraint, the formulas are those it holds: the
; theorems of the encapsulate about its functions, and the definitions of
; the functions defined there.

(defun bx-candidate-formulas (cands wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (bx-candidate-list-p cands wrld nil))))
  (cond ((endp cands) nil)
        (t (let* ((c (car cands))
                  (formula (if (eq (cadr c) :formula)
                               (caddr c)
                             (let ((fn (caddr c)))
                               (list 'equal (cons fn (formals fn wrld))
                                     (getpropc fn 'unnormalized-body nil wrld))))))
             (cons (list (car c) formula)
                   (bx-candidate-formulas (cdr cands) wrld))))))

; PENDING also holds, under a constrainer, the items of the events inside
; its encapsulate that stand after its constraint (see BX-ITEMS), each
; list of them as an entry (NIL :after ITEMS) among the candidates.

(defun bx-formula-cands (cands)
  (declare (xargs :guard (all->=-len cands 2)))
  (cond ((endp cands) nil)
        ((eq (cadr (car cands)) :after) (bx-formula-cands (cdr cands)))
        (t (cons (car cands) (bx-formula-cands (cdr cands))))))

(defun bx-later-item-lists-p (cands)
  (declare (xargs :guard t))
  (if (consp cands)
      (and (>=-len (car cands) 3)
           (or (not (eq (cadar cands) :after))
               (bx-item-list-p (caddar cands)))
           (bx-later-item-lists-p (cdr cands)))
    (null cands)))

(defun bx-later-items (cands)
  (declare (xargs :guard (bx-later-item-lists-p cands)))
  (cond ((endp cands) nil)
        ((eq (cadr (car cands)) :after)
         (append (caddr (car cands)) (bx-later-items (cdr cands))))
        (t (bx-later-items (cdr cands)))))

; The statement of the constraint, unless a formula has no name because
; every name tried for it is passed over (see BX-FRESH-NAME): then a note
; that names all the statement would have introduced, the functions and
; the names of the other formulas.

(defun bx-constrain-stmt (fns formulas wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld)
                              (bx-functions-present-p fns wrld)
                              (bx-named-formulas-p formulas))))
  (if (member-eq nil (strip-cars formulas))
      (list (bx-note "constraint with a formula for which no unused name was found"
                     (append fns (remove-eq nil (strip-cars formulas)))))
    (list (bx-stmt "constrain" (list (bx-arities fns wrld) formulas)))))

(defun bx-constrain-items (names c pending wrld)
  (declare (xargs :guard (and (symbol-listp names) (symbolp c)
                              (bx-world-properties-p wrld)
                              (bx-functions-present-p names wrld)
                              (bx-constraint-owner-p c wrld)
                              (bx-pending-p pending wrld))))
  (let* ((siblings (getpropc c 'siblings nil wrld))
         (fns (append names
                      (bx-sort-by-event (set-difference-eq siblings names) wrld)))
         (cands (bx-formula-cands (cdr (assoc-eq c pending))))
         (later (bx-later-items (cdr (assoc-eq c pending)))))
    (mv-let (name lst origins)
      (constraint-info c wrld)
      (declare (ignore name origins))
      (if (unknown-constraints-p lst)
          (append (list (bx-note "constraint that ACL2 does not record" fns))
                  (bx-constrain-stmt fns (bx-candidate-formulas cands wrld) wrld)
                  later)
        (mv-let (formulas notes)
          (bx-name-formulas lst cands c wrld)
          (append notes
                  (bx-constrain-stmt fns formulas wrld)
                  later))))))

; A package is hidden at its event if ACL2 keeps it hidden now, or if the
; event declared it hidden and a later event declared it openly.  ACL2
; records the second in the event, as the last of the arguments of the
; DEFPKG form it stores: (defpkg NAME IMPORTS DOC BOOK-PATH HIDDEN-P).

(defun bx-package-items (name form wrld)
  (declare (xargs :guard (and (stringp name) (plist-worldp wrld)
                              (known-package-alistp
                               (getpropc 'known-package-alist 'global-value :missing wrld)))))
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

; A function of no formals introduced with :STRENGTHEN T has the longer
; axiom in ACL2, whose second list of free variables is empty; its
; statement has FREE2 NIL and the basic axiom, since the longer one adds
; only that the call of the function equals itself (spec/logic.md,
; section 6).

(defun bx-choose-items (fn wrld)
  (declare (xargs :guard (and (symbolp fn) (bx-world-properties-p wrld)
                              (bx-choice-input-p fn wrld))))
  (let ((axiom (getpropc fn 'defchoose-axiom nil wrld))
        (free (formals fn wrld)))
    (mv-let (bound body free2)
      (bx-choose-parts axiom fn wrld)
      (if (and bound
               (or (equal (bx-beta axiom)
                          (bx-beta (bx-choose-axiom fn bound free body free2)))
                   (and (null free)
                        (null free2)
                        (equal (bx-beta axiom)
                               (bx-beta (bx-choose-literal fn bound free body
                                                           free2 t))))))
          (list (bx-stmt "choose" (list fn bound free body free2)))
        (list (bx-note "defchoose axiom not of the form of spec/logic.md" fn))))))

(defun bx-reserve-items (names wrld)
  (declare (xargs :guard (and (symbol-listp names) (plist-worldp wrld))))
  (cond ((endp names) nil)
        ((bx-reserve-kind-p (car names) wrld)
         (cons (bx-stmt "reserve" (list (car names)))
               (bx-reserve-items (cdr names) wrld)))
        (t (cons (bx-note "name of no known kind" (car names))
                 (bx-reserve-items (cdr names) wrld)))))

(defun bx-names-with-content (names wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (and (consp names)
       (or (and (symbolp (car names))
                (or (and (bx-function-p (car names) wrld)
                         (not (bx-programp (car names) wrld)))
                    (getpropc (car names) 'theorem nil wrld)))
           (bx-names-with-content (cdr names) wrld))))

(defun bx-names-reserved (names wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (and (consp names)
       (or (and (symbolp (car names))
                (bx-reserve-kind-p (car names) wrld))
           (bx-names-reserved (cdr names) wrld))))

; An event that supplies functions must have their formals in the world.
; Encapsulates and unconstrained choice events also supply the data read
; from their stored axioms.

(defun bx-event-data-p (ev wrld)
  (declare (xargs :guard (and (bx-world-properties-p wrld)
                              (bx-event-tuple-p ev)
                              (bx-event-names-p ev))))
  (let* ((type (bx-ev-type ev))
         (names (bx-names (bx-ev-namex ev)))
         (name (car names)))
    (case type
      ((defun defuns) (bx-functions-present-p names wrld))
      (encapsulate
       (and (bx-functions-present-p names wrld)
            (or (null names) (consp (bx-ev-namex ev)))
            (bx-event-constraint-p ev wrld)))
      (defchoose (or (bx-constrained-p name wrld) (bx-choice-input-p name wrld)))
      (otherwise t))))

(defun bx-event-data-list-p (evs wrld)
  (declare (xargs :guard (and (bx-world-properties-p wrld)
                              (bx-event-list-p evs))))
  (if (endp evs)
      t
    (and (bx-event-data-p (car evs) wrld)
         (bx-event-data-list-p (cdr evs) wrld))))

(defun bx-event-data-world-p (tail wrld)
  (declare (xargs :guard (and (plist-worldp tail) (bx-event-world-p tail)
                              (bx-world-properties-p wrld))))
  (if (endp tail)
      t
    (and (or (not (and (eq (caar tail) 'event-landmark)
                       (eq (cadar tail) 'global-value)))
             (bx-event-data-p (cddar tail) wrld))
         (bx-event-data-world-p (cdr tail) wrld))))

(defun bx-export-world-p (wrld)
  (declare (xargs :guard t))
  (and (bx-world-properties-p wrld)
       (bx-event-world-p wrld)
       (known-package-alistp
        (getpropc 'known-package-alist 'global-value :missing wrld))
       (bx-event-data-world-p wrld wrld)))

(defun bx-enclosed-events-p (pairs wrld)
  (declare (xargs :guard (bx-world-properties-p wrld)))
  (if (consp pairs)
      (and (consp (car pairs))
           (bx-event-tuple-p (caar pairs))
           (bx-event-names-p (caar pairs))
           (bx-event-data-p (caar pairs) wrld)
           (symbolp (cdar pairs))
           (or (not (cdar pairs)) (bx-constraint-owner-p (cdar pairs) wrld))
           (bx-enclosed-events-p (cdr pairs) wrld))
    (null pairs)))

; The items of one event.  ENCL is the constrainer of the innermost
; encapsulate with a signature that contains it, and PENDING maps each
; constrainer to the candidates found so far for naming the formulas of
; its constraint.  Returns (mv items pending).

(defun bx-event-items (ev encl pending defined translations wrld)
  (declare (xargs :guard (and (bx-world-properties-p wrld)
                              (bx-event-tuple-p ev) (bx-event-names-p ev)
                              (bx-event-data-p ev wrld)
                              (known-package-alistp
                               (getpropc 'known-package-alist 'global-value :missing wrld))
                              (symbolp encl)
                              (or (not encl) (bx-constraint-owner-p encl wrld))
                              (bx-pending-p pending wrld)
                              (bx-translations-p translations))))
  (let* ((type (bx-ev-type ev))
         (names (bx-names (bx-ev-namex ev)))
         (class (bx-ev-symbol-class ev)))
    (case type
      ((defun defuns)
       (cond
        ((eq class :program)
         (if (bx-all-program-p names wrld)
             (mv-let (defs notes)
               (bx-program-defs names (bx-ev-form ev) translations wrld nil nil)
               (mv (append notes
                           (and defs (list (bx-prog "define" (cons nil defs)))))
                   pending))
           (mv nil pending)))
        ((bx-some-program-p names wrld)
         (mv (list (bx-note "logic event of a function now in program mode" names))
             pending))
        ((bx-all-constrained-p names wrld)
         (cond ((null encl)
                (mv (list (bx-note "constrained definition outside an encapsulate" names))
                    pending))
               ((subsetp-eq names (getpropc encl 'siblings nil wrld))
                (mv nil (bx-add-candidates encl (bx-definition-candidates names wrld)
                                           pending)))
               (t (mv (list (bx-note "constrained definition of functions that its constraint does not list"
                                     names))
                      pending))))
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
                           (not (eq (bx-conjuncts formula lst) :none))))))
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
             (cond ((null encl)
                    (mv (list (bx-note "constrained choice outside an encapsulate" fn))
                        pending))
                   ((member-eq fn (getpropc encl 'siblings nil wrld))
                    (mv nil (bx-add-candidates
                             encl
                             (list (list (bx-formula-name fn "choice" wrld)
                                         :formula
                                         (getpropc fn 'defchoose-axiom nil wrld)))
                             pending)))
                   (t (mv (list (bx-note "constrained choice of a function that its constraint does not list"
                                         fn))
                          pending)))
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
      (defpkg (mv (bx-package-items (car names) (bx-ev-form ev) wrld)
                  pending))
      ((defmacro defconst deflabel deftheory)
       (mv (bx-reserve-items names wrld) pending))
      ((defstobj defabsstobj)
       (mv (bx-stobj-items names defined nil wrld nil) pending))
      (otherwise
       (mv (if (or (bx-names-with-content names wrld)
                   (bx-names-reserved names wrld))
               (list (bx-note "event of an unexpected kind"
                              (list type names)))
             nil)
           pending)))))

; DEFINED maps each function that a statement already written defines to
; T.

(defun bx-add-defined (items defined)
  (declare (xargs :guard (bx-item-list-p items)))
  (cond ((endp items) defined)
        ((and (eq (car (car items)) :stmt)
              (member-equal (cadr (car items)) '("define" "constrain" "choose")))
         (bx-add-defined (cdr items)
                         (bx-add-names (bx-introduced (cdr (car items))) defined)))
        (t (bx-add-defined (cdr items) defined))))

; The functions that the statements among ITEMS call, and those that they
; introduce.

(defun bx-items-used (items)
  (declare (xargs :guard (bx-item-list-p items)))
  (cond ((endp items) nil)
        ((eq (car (car items)) :stmt)
         (append (bx-used (cdr (car items))) (bx-items-used (cdr items))))
        (t (bx-items-used (cdr items)))))

(defun bx-items-introduced (items)
  (declare (xargs :guard (bx-item-list-p items)))
  (cond ((endp items) nil)
        ((eq (car (car items)) :stmt)
         (append (bx-introduced (cdr (car items))) (bx-items-introduced (cdr items))))
        (t (bx-items-introduced (cdr items)))))

; The items of the events, in order.  An event inside an encapsulate with
; a signature whose constraint ENCL introduces functions may be no part of
; the constraint and still call one of them, as ACL2 allows; or it may
; call a function of an event so placed.  Its items are then held in
; PENDING and stand right after the constraint (see BX-CONSTRAIN-ITEMS).

(defun bx-items (pairs pending defined translations wrld acc)
  (declare (xargs :guard (and (bx-world-properties-p wrld)
                              (known-package-alistp
                               (getpropc 'known-package-alist 'global-value :missing wrld))
                              (bx-enclosed-events-p pairs wrld)
                              (bx-pending-p pending wrld)
                              (bx-translations-p translations) (bx-item-list-p acc))))
  (cond ((endp pairs) (prog2$ (fast-alist-free defined) (reverse acc)))
        (t (mv-let (items pending)
             (bx-event-items (car (car pairs)) (cdr (car pairs)) pending defined
                             translations wrld)
             (let ((encl (cdr (car pairs))))
               (if (and encl
                        (intersectp-eq (bx-items-used items)
                                       (append (getpropc encl 'siblings nil wrld)
                                               (bx-items-introduced
                                                (bx-later-items
                                                 (cdr (assoc-eq encl pending)))))))
                   (bx-items (cdr pairs)
                             (bx-add-candidates encl (list (list nil :after items))
                                                pending)
                             (bx-add-defined items defined) translations wrld acc)
                 (bx-items (cdr pairs) pending (bx-add-defined items defined)
                           translations wrld (revappend items acc))))))))

(defun bx-range-items (lo hi translations wrld)
  (declare (xargs :guard (and (integerp lo) (integerp hi)
                              (bx-translations-p translations)
                              (bx-export-world-p wrld))))
  (let ((evs (bx-events wrld lo hi nil)))
    (bx-items (bx-enclose (reverse evs) nil nil wrld) nil nil translations wrld
              nil)))

; The bodies that the shell must translate for the events numbered above
; LO and at most HI: a pair (FN . BODY) for each function in program mode
; whose body the world does not store, of an event that defines functions
; all still in program mode.

(defun bx-requests-of (names form wrld)
  (declare (xargs :guard (and (symbol-listp names) (bx-defun-form-p form)
                              (plist-worldp wrld))))
  (cond ((endp names) nil)
        ((bx-needs-translation-p (car names) wrld)
         (let ((def (assoc-eq (car names) (bx-defun-forms form))))
           (if def
               (cons (cons (car names) (car (last def)))
                     (bx-requests-of (cdr names) form wrld))
             (bx-requests-of (cdr names) form wrld))))
        (t (bx-requests-of (cdr names) form wrld))))

(defun bx-requests (evs wrld)
  (declare (xargs :guard (and (bx-event-list-p evs) (plist-worldp wrld))))
  (cond ((endp evs) nil)
        ((and (member-eq (bx-ev-type (car evs)) '(defun defuns))
              (eq (bx-ev-symbol-class (car evs)) :program)
              (bx-all-program-p (bx-names (bx-ev-namex (car evs))) wrld))
         (append (bx-requests-of (bx-names (bx-ev-namex (car evs)))
                                 (bx-ev-form (car evs)) wrld)
                 (bx-requests (cdr evs) wrld)))
        (t (bx-requests (cdr evs) wrld))))

(defun bx-translation-requests (lo hi wrld)
  (declare (xargs :guard (and (integerp lo) (integerp hi)
                              (plist-worldp wrld) (bx-event-world-p wrld))))
  (bx-requests (bx-events wrld lo hi nil) wrld))

;;; 6. Selecting items

(defun bx-select (key items)
  (declare (xargs :guard (and (symbolp key) (alistp items))))
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
  (declare (xargs :guard (and (true-listp words) (alistp stmts))))
  (cond ((endp stmts) nil)
        ((member-equal (car (car stmts)) words)
         (cons (car stmts) (bx-words words (cdr stmts))))
        (t (bx-words words (cdr stmts)))))

; A depth-first walk: each statement is placed after the statements that
; introduce the functions it uses.  INDEX maps each function to its
; statement, and DONE maps each statement placed, or being placed, to T
; or :pending.

(defun bx-index-fns (fns stmt acc)
  (declare (xargs :guard (true-listp fns)))
  (cond ((endp fns) acc)
        (t (bx-index-fns (cdr fns) stmt (hons-acons (car fns) stmt acc)))))

(defun bx-line-index-p (index)
  (declare (xargs :guard t))
  (if (consp index)
      (and (consp (car index)) (bx-line-p (cdar index))
           (bx-line-index-p (cdr index)))
    (null index)))

(defun bx-index (stmts acc)
  (declare (xargs :guard (bx-line-list-p stmts)))
  (cond ((endp stmts) acc)
        (t (bx-index (cdr stmts)
                     (bx-index-fns (bx-introduced (car stmts)) (car stmts) acc)))))

; The walk keeps a stack of frames (STMT . FNS): STMT is being placed and
; FNS are the functions it uses that remain to be looked at.  TODO holds
; the statements still to be placed, in order.  Each statement is pushed
; at most once and popped at most once, and each of the functions it uses
; is looked at once, so BX-STEPS bounds the steps; FUEL counts them.

(defun bx-steps (stmts)
  (declare (xargs :guard (bx-line-list-p stmts)))
  (if (endp stmts)
      1
    (+ 3 (len (bx-used (car stmts))) (bx-steps (cdr stmts)))))

(defun bx-walk-stack-p (stack)
  (declare (xargs :guard t))
  (if (consp stack)
      (and (consp (car stack))
           (bx-line-p (caar stack))
           (true-listp (cdar stack))
           (bx-walk-stack-p (cdr stack)))
    (null stack)))

(defun bx-walk (stack todo index done acc notes fuel)
  (declare (xargs :guard (and (bx-walk-stack-p stack) (bx-line-list-p todo)
                              (bx-line-index-p index) (true-listp acc) (natp fuel))
                  :measure (nfix fuel)))
  (cond
   ((zp fuel)
    (mv (reverse acc)
        (cons (bx-note "order of the library not completed" nil) notes)))
   ((endp stack)
    (if (endp todo)
        (prog2$ (fast-alist-free done) (mv (reverse acc) notes))
      (let* ((s (car todo))
             (mark (cdr (hons-get s done))))
        (cond ((eq mark t)
               (bx-walk nil (cdr todo) index done acc notes (- fuel 1)))
              ((eq mark :pending)
               (bx-walk nil (cdr todo) index done acc
                        (cons (bx-note "cycle among definitions" (bx-introduced s))
                              notes)
                        (- fuel 1)))
              (t (bx-walk (list (cons s (bx-used s))) (cdr todo) index
                          (hons-acons s :pending done) acc notes (- fuel 1)))))))
   (t (let ((s (car (car stack)))
            (fns (cdr (car stack))))
        (if (endp fns)
            (bx-walk (cdr stack) todo index (hons-acons s t done) (cons s acc)
                     notes (- fuel 1))
          (let ((stack (cons (cons s (cdr fns)) (cdr stack)))
                (u (cdr (hons-get (car fns) index))))
            (if (null u)
                (bx-walk stack todo index done acc notes (- fuel 1))
              (let ((mark (cdr (hons-get u done))))
                (cond ((eq mark t)
                       (bx-walk stack todo index done acc notes (- fuel 1)))
                      ((eq mark :pending)
                       (bx-walk stack todo index done acc
                                (cons (bx-note "cycle among definitions"
                                               (bx-introduced u))
                                      notes)
                                (- fuel 1)))
                      (t (bx-walk (cons (cons u (bx-used u)) stack) todo index
                                  (hons-acons u :pending done) acc notes
                                  (- fuel 1))))))))))))

; ACL2's 84 axioms, the DEFAXIOM events of its source file axioms.lisp,
; which the ground theory holds: 80 as the lines (clause NAME LITERAL) of
; spec/ground.txt whose names are symbols, and four as package lines,
; whose rules have these names (spec/logic.md, section 3).  An axiom of
; the world not among them is not left to the ground theory: it has its
; own statement.

(defconst *bx-ground-axioms*
  '(car-cdr-elim car-cons cdr-cons cons-equal nonnegative-product closure
    associativity-of-+ commutativity-of-+ unicity-of-0 inverse-of-+
    associativity-of-* commutativity-of-* unicity-of-1 inverse-of-*
    distributivity <-on-others zero trichotomy positive rational-implies1
    rational-implies2 integer-implies-rational complex-implies1
    complex-definition nonzero-imagpart realpart-imagpart-elim
    realpart-complex imagpart-complex integer-0 integer-1 integer-step
    lowest-terms booleanp-characterp characterp-page characterp-tab
    characterp-rubout characterp-return coerce-inverse-1 coerce-inverse-2
    character-listp-coerce stringp-symbol-package-name
    symbolp-intern-in-package-of-symbol symbolp-pkg-witness
    intern-in-package-of-symbol-symbol-name symbol-name-pkg-witness
    symbol-package-name-pkg-witness-name
    symbol-name-intern-in-package-of-symbol
    symbol-package-name-intern-in-package-of-symbol
    intern-in-package-of-symbol-is-identity symbol-listp-pkg-imports
    no-duplicatesp-eq-pkg-imports completion-of-pkg-imports
    string-is-not-circular nil-is-not-circular char-code-linear
    code-char-type code-char-char-code-is-identity
    char-code-code-char-is-identity completion-of-symbol-name
    completion-of-symbol-package-name completion-of-+ completion-of-*
    completion-of-unary-minus completion-of-unary-/ completion-of-<
    completion-of-car completion-of-cdr completion-of-char-code
    completion-of-code-char completion-of-complex completion-of-coerce
    completion-of-denominator completion-of-imagpart
    completion-of-intern-in-package-of-symbol completion-of-numerator
    completion-of-realpart booleanp-bad-atom<= bad-atom<=-antisymmetric
    bad-atom<=-transitive bad-atom<=-total acl2-package keyword-package
    acl2-input-channel-package acl2-output-channel-package))

(defun bx-not-ground (stmts ground)
  (declare (xargs :guard (and (bx-line-list-p stmts) (symbol-listp ground))))

; The statements that are not part of the ground theory: GROUND holds the
; functions that the ground theory defines.  ACL2's axioms are in the
; ground theory, and so are the packages it declares and the constants T
; and NIL.

  (cond ((endp stmts) nil)
        ((or (and (equal (car (car stmts)) "axiom")
                  (member-eq (car (cadr (car stmts))) *bx-ground-axioms*))
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
  (declare (xargs :guard (bx-line-list-p stmts)))
  (let* ((defs (bx-words '("define" "constrain" "choose") stmts))
         (index (bx-index defs nil)))
    (mv-let (placed notes)
      (bx-walk nil defs index nil nil nil (bx-steps defs))
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
; and every symbol exists, by the rule of spec/language.md, section 2: it
; is of a package declared before, and that package imports no symbol of
; its name.  It proves nothing.  FNS maps each function in use to its
; number of arguments, NAMES each name in use to T, and PKGS each package
; declared to T, or to (:hidden . IMPORTS) if it is hidden, which a
; package line with the same imports may declare again.  PKGS also maps
; (PKG . NAME) to T for each symbol of name NAME that the package PKG
; imports.  The body of a choose is checked against the functions in use
; before the line, since the function it introduces is not yet in use
; there (spec/logic.md, section 6).

(mutual-recursion

 (defun bx-bad-calls (term fns own)
   (declare (xargs :guard (and (pseudo-termp term) (alistp own))))

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
   (declare (xargs :guard (and (pseudo-term-listp terms) (alistp own))))
   (cond ((endp terms) nil)
         (t (append (bx-bad-calls (car terms) fns own)
                    (bx-bad-calls-lst (cdr terms) fns own))))))

(defun bx-packages-of (x pkgs acc)
  (declare (xargs :guard (true-listp acc)))

; The package names of the symbols in X that are not declared in PKGS.

  (cond ((consp x) (bx-packages-of (cdr x) pkgs (bx-packages-of (car x) pkgs acc)))
        ((and (symbolp x)
              (not (hons-get (symbol-package-name x) pkgs))
              (not (member-equal (symbol-package-name x) acc)))
         (cons (symbol-package-name x) acc))
        (t acc)))

; The symbols in X whose packages, as PKGS declares them, import a symbol
; of the same name, so that they do not exist.

(defun bx-imported-names (x pkgs acc)
  (declare (xargs :guard (symbol-listp acc)))
  (cond ((consp x) (bx-imported-names (cdr x) pkgs (bx-imported-names (car x) pkgs acc)))
        ((and (symbolp x)
              (hons-get (cons (symbol-package-name x) (symbol-name x)) pkgs)
              (not (member-eq x acc)))
         (cons x acc))
        (t acc)))

(defun bx-add-imports (pkg imports table)
  (declare (xargs :guard (symbol-listp imports)))
  (cond ((endp imports) table)
        (t (bx-add-imports pkg (cdr imports)
                           (hons-acons (cons pkg (symbol-name (car imports))) t
                                       table)))))

(defun bx-new-names (names table)
  (declare (xargs :guard (true-listp names)))
  (cond ((endp names) nil)
        ((hons-get (car names) table) (cons (car names) (bx-new-names (cdr names) table)))
        (t (bx-new-names (cdr names) table))))

(defun bx-add-arities (pairs table)
  (declare (xargs :guard (all->=-len pairs 2)))
  (cond ((endp pairs) table)
        (t (bx-add-arities (cdr pairs)
                           (hons-acons (car (car pairs)) (cadr (car pairs)) table)))))

(defun bx-def-arities (defs)
  (declare (xargs :guard (true-list-listp defs)))
  (cond ((endp defs) nil)
        (t (cons (list (car (car defs)) (len (cadr (car defs))))
                 (bx-def-arities (cdr defs))))))

(defun bx-alist (pairs)
  (declare (xargs :guard (true-list-listp pairs)))
  (cond ((endp pairs) nil)
        (t (cons (cons (car (car pairs)) (cadr (car pairs)))
                 (bx-alist (cdr pairs))))))

(defun bx-package-rule (name)
  (declare (xargs :guard (stringp name)))
  (intern-in-package-of-symbol (concatenate 'string name "-PACKAGE") 'acl2::x))

; Checks one statement.  Returns (mv problems fns names pkgs).

(defun bx-check-stmt (stmt fns names pkgs)
  (declare (xargs :guard (bx-line-p stmt)))
  (let* ((word (car stmt))
         (args (cadr stmt))
         (missing (bx-packages-of args pkgs nil))
         (imported (bx-imported-names args pkgs nil)))
    (cond
     ((member-equal word '("package" "hidden-package"))
      (let ((rule (bx-package-rule (car args))))
        (mv (append (and missing (list (list :package-undeclared missing)))
                    (and imported (list (list :name-imported imported)))
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
                        (bx-add-imports (car args) (cadr args) pkgs)))))
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
             (bad (bx-bad-calls-lst terms fns
                                    (if (equal word "choose") nil (bx-alist intro))))
             (used (bx-new-names new names)))
        (mv (append (and missing (list (list :package-undeclared missing)))
                    (and imported (list (list :name-imported imported)))
                    (and bad (list (list :not-in-use (remove-duplicates-eq bad))))
                    (and used (list (list :name-in-use used)))
                    (and (not (no-duplicatesp-equal new))
                         (list (list :name-twice new))))
            (bx-add-arities intro fns)
            (bx-add-names new names)
            pkgs))))))

; Checks the statements in order, a line that repeats an earlier one
; apart.  Two lines are the same exactly when their data are, since each
; datum has one text, so SEEN maps the first name of each statement (see
; BX-STMT-KEY) to the statements checked that have it.  Returns (mv notes
; fns names pkgs seen).

(defun bx-stmt-key (stmt)
  (declare (xargs :guard (bx-line-p stmt)))
  (let ((word (car stmt)) (args (cadr stmt)))
    (cond ((equal word "define") (car (cadr args)))
          ((equal word "constrain") (car (car (car args))))
          (t (car args)))))

(defun bx-seen-lines-p (seen)
  (declare (xargs :guard t))
  (if (consp seen)
      (and (consp (car seen)) (true-listp (cdar seen))
           (bx-seen-lines-p (cdr seen)))
    (null seen)))

(defun bx-check-stmts (stmts fns names pkgs seen notes)
  (declare (xargs :guard (and (bx-line-list-p stmts) (bx-seen-lines-p seen)
                              (true-listp notes))))
  (cond ((endp stmts) (mv (reverse notes) fns names pkgs seen))
        (t (let* ((key (bx-stmt-key (car stmts)))
                  (same (cdr (hons-get key seen))))
             (if (member-equal (car stmts) same)
                 (bx-check-stmts (cdr stmts) fns names pkgs seen notes)
               (mv-let (problems fns names pkgs)
                 (bx-check-stmt (car stmts) fns names pkgs)
                 (bx-check-stmts (cdr stmts) fns names pkgs
                                 (hons-acons key (cons (car stmts) same) seen)
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

; The ground theory declares five packages, its 32 primitives and 37
; definitions are functions in use, and its names are in use: those of
; the functions, of ACL2's axioms (*BX-GROUND-AXIOMS*), T and NIL.
; GROUND-FNS is the list of the functions it defines, read from
; spec/ground.txt by export/book.sh.  The imports of its packages are
; those that ACL2 holds for them, which are those of its package lines.

(defun bx-add-package-imports (names known table)
  (declare (xargs :guard (and (true-listp names) (known-package-alistp known))))
  (cond ((endp names) table)
        (t (bx-add-package-imports
            (cdr names) known
            (bx-add-imports (car names)
                            (package-entry-imports (find-package-entry (car names) known))
                            table)))))

(defun bx-ground-tables (ground-fns wrld)
  (declare (xargs :guard (and (symbol-listp ground-fns) (bx-world-properties-p wrld)
                              (known-package-alistp
                               (getpropc 'known-package-alist 'global-value nil wrld))
                              (bx-functions-present-p ground-fns wrld)
                              (bx-functions-present-p
                               (strip-cars *primitive-formals-and-guards*) wrld))))
  (let* ((prims (strip-cars *primitive-formals-and-guards*))
         (fns (bx-add-arities (bx-arities (append prims ground-fns) wrld) nil))
         (names (bx-add-names (append '(t nil) prims ground-fns *bx-ground-axioms*)
                              nil))
         (pkg-names '("COMMON-LISP" "KEYWORD" "ACL2"
                      "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"))
         (pkgs (bx-add-package-imports pkg-names
                                       (getpropc 'known-package-alist 'global-value
                                                 nil wrld)
                                       (bx-add-names pkg-names nil))))
    (mv fns names pkgs)))

;;; 10. Attachments

; The world as it stood after the event numbered N: the tail of WRLD that
; begins with the landmark of that event.

(defun bx-world-at (n wrld)
  (declare (xargs :guard (and (integerp n) (plist-worldp wrld) (bx-event-world-p wrld))))
  (cond ((endp wrld) nil)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value)
              (eql (bx-ev-number (cddar wrld)) n))
         wrld)
        (t (bx-world-at n (cdr wrld)))))

; The attachments in force in the world WRLD, which may be an older world
; that is a tail of the present one: the pairs (F . G), where G is the
; function ACL2 runs in place of F.  ACL2 holds them in the ATTACHMENT
; property of F, which is either an alist of such pairs for F and the
; functions attached with it, or the name of a function that holds that
; alist, as its function ATTACHMENT-PAIR reads it.  The property is read
; from the triples of WRLD, the first of each symbol being its value.

(defun bx-attachment-props (wrld acc)
  (declare (xargs :guard (plist-worldp wrld)))
  (cond ((endp wrld) acc)
        ((and (eq (cadar wrld) 'attachment)
              (not (hons-get (caar wrld) acc)))
         (bx-attachment-props (cdr wrld) (hons-acons (caar wrld) (cddar wrld) acc)))
        (t (bx-attachment-props (cdr wrld) acc))))

(defun bx-attachment-value (sym props)
  (declare (xargs :guard t))
  (let ((v (cdr (hons-get sym props))))
    (if (eq v *acl2-property-unbound*) nil v)))

(defun bx-attachment-table-p (props)
  (declare (xargs :guard t))
  (if (consp props)
      (and (consp (car props))
           (symbolp (caar props))
           (bx-attachment-property-p (cdar props))
           (bx-attachment-table-p (cdr props)))
    (null props)))

(defun bx-pairs-of (alist props acc)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (bx-attachment-table-p props))))
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
  (declare (xargs :guard (bx-world-properties-p wrld)))
  (let* ((props (bx-attachment-props wrld nil))
         (pairs (bx-pairs-of props props nil)))
    (prog2$ (fast-alist-free props)
            (merge-sort-lexorder pairs))))

(defun bx-attach-lines (pairs except)
  (declare (xargs :guard (and (alistp pairs) (true-listp except))))
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
  (declare (xargs :guard (bx-line-list-p progs)))
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
  (declare (xargs :guard (bx-event-list-p evs)))
  (cond ((endp evs) nil)
        ((bx-ev-skipped-proofs-p (car evs))
         (cons (bx-ev-namex (car evs)) (bx-skipped (cdr evs))))
        (t (bx-skipped (cdr evs)))))

(defun bx-book-ttags (alist)
  (declare (xargs :guard (bx-ttags-alist-p alist)))
  (cond ((endp alist) nil)
        ((remove-eq nil (cdr (car alist)))
         (cons (car (car alist)) (bx-book-ttags (cdr alist))))
        (t (bx-book-ttags (cdr alist)))))

; Every line the core gives is (WORD ARGS): the word, a string, and the
; list of the data after it, which the printer of checks/canon.lisp writes
; as the text (WORD ARG ...).

(defun bx-note-lines (notes)
  (declare (xargs :guard (true-list-listp notes)))
  (cond ((endp notes) nil)
        (t (cons (list "note" (list (car (car notes)) (cadr (car notes))))
                 (bx-note-lines (cdr notes))))))

(defun bx-count-word (word stmts)
  (declare (xargs :guard (alistp stmts)))
  (cond ((endp stmts) 0)
        ((equal (car (car stmts)) word) (+ 1 (bx-count-word word (cdr stmts))))
        (t (bx-count-word word (cdr stmts)))))

(defun bx-count-lines (stmts)
  (declare (xargs :guard (alistp stmts)))
  (list (list "count" (list "package" (bx-count-word "package" stmts)))
        (list "count" (list "hidden-package" (bx-count-word "hidden-package" stmts)))
        (list "count" (list "define" (bx-count-word "define" stmts)))
        (list "count" (list "constrain" (bx-count-word "constrain" stmts)))
        (list "count" (list "choose" (bx-count-word "choose" stmts)))
        (list "count" (list "theorem" (bx-count-word "theorem" stmts)))
        (list "count" (list "axiom" (bx-count-word "axiom" stmts)))
        (list "count" (list "reserve" (bx-count-word "reserve" stmts)))))

; The program text of the library: the definitions in logic mode in the
; order of the statements, then the functions in program mode in the
; order of ACL2's events.

(defun bx-program-only (progs wrld)
  (declare (xargs :guard (and (bx-definition-lines-p progs) (plist-worldp wrld))))
  (cond ((endp progs) nil)
        ((bx-all-program-p (strip-cars (cdr (cadr (car progs)))) wrld)
         (cons (car progs) (bx-program-only (cdr progs) wrld)))
        (t (bx-program-only (cdr progs) wrld))))

(defun bx-library-program-order (progs ordered wrld)
  (declare (xargs :guard (and (bx-definition-lines-p progs)
                              (bx-line-list-p ordered) (plist-worldp wrld))))
  (append (bx-words '("define") ordered)
          (bx-program-only progs wrld)))

; The definitions of the ground theory, which a runner needs as much as
; those of the library, stand first in the library's program text.

(defun bx-ground-defines (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (bx-world-properties-p wrld)
                              (bx-functions-present-p fns wrld))))
  (cond ((endp fns) nil)
        (t (cons (list "define"
                       (list (bx-rulers (car fns) wrld)
                             (list (car fns) (formals (car fns) wrld)
                                   (getpropc (car fns) 'unnormalized-body nil wrld))))
                 (bx-ground-defines (cdr fns) wrld)))))

; The library: the events numbered at most HI, the end of the world ACL2
; starts with.  GROUND-FNS are the functions that the ground theory
; defines, and TRANSLATIONS the bodies the shell translated (see
; BX-PROGRAM-BODY).  Returns (mv statements program notes): the lines of
; the files PREFIX.statements, PREFIX.program and PREFIX.notes, in order.

(defun bx-library-lines (ground-fns hi translations wrld)
  (declare (xargs :guard (and (integerp hi) (symbol-listp ground-fns)
                              (bx-export-world-p wrld)
                              (bx-functions-present-p ground-fns wrld)
                              (bx-functions-present-p
                               (strip-cars *primitive-formals-and-guards*) wrld)
                              (bx-translations-p translations))))
  (let* ((boot-evs (bx-events wrld 0 hi nil))
         (items (bx-items (bx-enclose (reverse boot-evs) nil nil wrld) nil nil
                          translations wrld nil))
         (stmts (bx-not-ground (bx-select :stmt items) ground-fns))
         (progs (bx-not-ground (bx-select :prog items) ground-fns)))
    (mv-let (ordered order-notes)
      (bx-library-order stmts)
      (mv-let (fns names pkgs)
        (bx-ground-tables ground-fns wrld)
        (mv-let (check-notes fns names pkgs seen)
          (bx-check-stmts ordered fns names pkgs nil nil)
          (declare (ignore fns names pkgs))
          (let ((notes (bx-select :note (append items order-notes check-notes))))
            (prog2$
             (fast-alist-free seen)
             (mv ordered
                 (append (bx-ground-defines ground-fns wrld)
                         (bx-runnable (bx-library-program-order progs ordered wrld))
                         (bx-attach-lines (bx-attachment-pairs wrld) nil))
                 (append (bx-count-lines ordered)
                         (bx-note-lines notes))))))))))

;;; 12. The prover's aids of the events

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
; The local events are read from the books' sources, which only the shell
; can do.  The hints, instructions and declarations are read here from the
; event forms that ACL2 stores in its world; the measures from the
; JUSTIFICATION it stores.  Nothing that ACL2's prover found is written.

(defun bx-kwd-value (key kwds)
  (declare (xargs :guard (and (symbolp key) (true-listp kwds))))
  (cond ((or (endp kwds) (endp (cdr kwds))) nil)
        ((eq (car kwds) key) (list (cadr kwds)))
        (t (bx-kwd-value key (cddr kwds)))))

(defun bx-xargs-items-p (items)
  (declare (xargs :guard t))
  (if (consp items)
      (and (or (atom (car items))
               (not (eq (caar items) 'xargs))
               (true-listp (cdar items)))
           (bx-xargs-items-p (cdr items)))
    (null items)))

(defun bx-declarations-p (dcls)
  (declare (xargs :guard t))
  (if (consp dcls)
      (and (or (atom (car dcls))
               (not (eq (caar dcls) 'declare))
               (bx-xargs-items-p (cdar dcls)))
           (bx-declarations-p (cdr dcls)))
    (null dcls)))

(defun bx-xargs-items (items)
  (declare (xargs :guard (bx-xargs-items-p items)))
  (cond ((endp items) nil)
        ((and (consp (car items)) (eq (caar items) 'xargs))
         (append (cdar items) (bx-xargs-items (cdr items))))
        (t (bx-xargs-items (cdr items)))))

(defun bx-xargs (dcls)
  (declare (xargs :guard (bx-declarations-p dcls)))

; The keyword arguments of every XARGS declaration among DCLS.

  (cond ((endp dcls) nil)
        ((and (consp (car dcls)) (eq (caar dcls) 'declare))
         (append (bx-xargs-items (cdar dcls)) (bx-xargs (cdr dcls))))
        (t (bx-xargs (cdr dcls)))))

(defun bx-aid-definitions-p (defs)
  (declare (xargs :guard t))
  (if (consp defs)
      (and (consp (car defs))
           (symbolp (caar defs))
           (true-listp (car defs))
           (bx-declarations-p (butlast (cddar defs) 1))
           (bx-aid-definitions-p (cdr defs)))
    (null defs)))

(defun bx-defun-aids (defs wrld)
  (declare (xargs :guard (and (bx-aid-definitions-p defs)
                              (bx-world-properties-p wrld))))
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

(defun bx-event-aid-input-p (ev)
  (declare (xargs :guard (and (bx-event-tuple-p ev) (bx-event-names-p ev))))
  (or (not (member-eq (bx-ev-type ev) '(defun defuns)))
      (eq (bx-ev-symbol-class ev) :program)
      (bx-aid-definitions-p (bx-defun-forms (bx-ev-form ev)))))

(defun bx-event-aids-input-p (evs)
  (declare (xargs :guard (bx-event-list-p evs)))
  (if (endp evs)
      t
    (and (bx-event-aid-input-p (car evs))
         (bx-event-aids-input-p (cdr evs)))))

(defun bx-world-aids-p (wrld)
  (declare (xargs :guard (and (plist-worldp wrld) (bx-event-world-p wrld))))
  (if (endp wrld)
      t
    (and (or (not (and (eq (caar wrld) 'event-landmark)
                       (eq (cadar wrld) 'global-value)))
             (bx-event-aid-input-p (cddar wrld)))
         (bx-world-aids-p (cdr wrld)))))

(defun bx-event-aids (evs wrld)
  (declare (xargs :guard (and (bx-event-list-p evs) (bx-event-aids-input-p evs)
                              (bx-world-properties-p wrld))))
  (cond ((endp evs) nil)
        (t (let* ((ev (car evs))
                  (form (bx-ev-form ev))
                  (type (bx-ev-type ev)))
             (append
              (case type
                ((defun defuns)
                 (if (eq (bx-ev-symbol-class ev) :program)
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

(defun bx-book-files (evs)
  (declare (xargs :guard (bx-event-list-p evs)))

; The source files of the books included in EVS, in the order of their
; events.

  (cond ((endp evs) nil)
        ((and (eq (bx-ev-type (car evs)) 'include-book)
              (stringp (bx-ev-namex (car evs))))
         (cons (bx-ev-namex (car evs)) (bx-book-files (cdr evs))))
        (t (bx-book-files (cdr evs)))))

;;; 13. A book

; A book's name as the files give it: its file relative to ACL2's
; directory of books, BOOKS-DIR, or to the directory in which ACL2 runs,
; CBD, without ".lisp".  The shell hands over both directories.

(defun bx-strip-prefix (prefix s)
  (declare (xargs :guard (and (stringp prefix) (stringp s))))
  (if (and (<= (length prefix) (length s))
           (equal (subseq s 0 (length prefix)) prefix))
      (subseq s (length prefix) (length s))
    nil))

(defun bx-book-name (file books-dir cbd)
  (declare (xargs :guard (and (stringp file) (stringp books-dir) (stringp cbd))))
  (let* ((rel (or (bx-strip-prefix books-dir file)
                  (bx-strip-prefix cbd file)
                  file))
         (n (length rel)))
    (if (and (< 5 n) (equal (subseq rel (- n 5) n) ".lisp"))
        (subseq rel 0 (- n 5))
      rel)))

; The books whose certificates carry the mark KEY, :skipped-proofsp or
; :axiomsp, among the entries (FULL-NAME USER-NAME FAMILIAR-NAME
; ANNOTATIONS . HASH) of ACL2's list of the books included.

(defun bx-marked-books (key alist books-dir cbd)
  (declare (xargs :guard (and (symbolp key) (bx-book-alist-p alist)
                              (stringp books-dir) (stringp cbd))))
  (cond ((endp alist) nil)
        ((and (consp (car alist))
              (not (eq (car (car alist)) 'local))
              (consp (cdddr (car alist)))
              (cdr (assoc-eq key (cadddr (car alist)))))
         (let ((full (car (car alist))))
           (cons (cond ((stringp full) (bx-book-name full books-dir cbd))
                       ((and (consp full) (stringp (cdr full)))
                        (bx-book-name (cdr full) books-dir cbd))
                       (t full))
                 (bx-marked-books key (cdr alist) books-dir cbd))))
        (t (bx-marked-books key (cdr alist) books-dir cbd))))

; A book: the events numbered above LO and at most HI, which are those
; that including the book added to the world ACL2 starts with, whose last
; event is numbered BOOT-HI.  The statements of the library are computed
; again, so that the check of the order starts from the names they bring
; into use.  The program text has an attach line for each attachment in
; force that was not in force in the world ACL2 starts with.  Returns (mv
; statements program notes aids): the lines of PREFIX.statements and
; PREFIX.program; those of PREFIX.notes, to which the shell adds a note
; for each book whose source it could not read; and those of PREFIX.aids
; that the events give, before which the shell puts the local events.

(defun bx-book-globals-p (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (and (bx-ttags-alist-p (getpropc 'ttags-seen 'global-value :missing wrld))
       (bx-book-alist-p (getpropc 'include-book-alist 'global-value :missing wrld))
       (not (eq (getpropc 'redef-seen 'global-value :missing wrld) :missing))))

(defun bx-book-notes (items check-notes boot-hi lo hi books-dir cbd wrld)
  (declare (xargs :guard (and (bx-item-list-p items) (bx-item-list-p check-notes)
                              (integerp boot-hi) (integerp lo) (integerp hi)
                              (stringp books-dir) (stringp cbd)
                              (bx-world-properties-p wrld) (bx-event-world-p wrld)
                              (bx-book-globals-p wrld))))
  (let* ((pairs (bx-attachment-pairs wrld))
         (boot-pairs (bx-attachment-pairs (bx-world-at boot-hi wrld)))
         (removed (set-difference-equal boot-pairs pairs))
         (ttags (bx-book-ttags (global-val 'ttags-seen wrld)))
         (skipped (bx-skipped (bx-events wrld lo hi nil)))
         (book-alist (global-val 'include-book-alist wrld))
         (skipped-books (bx-marked-books :skipped-proofsp book-alist books-dir cbd))
         (axiom-books (bx-marked-books :axiomsp book-alist books-dir cbd)))
    (bx-select :note
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

; A checker reads a book's statements after those of the library and
; stops at the first line it cannot admit, so a book's lines rest on the
; library's being in order.  Where the library, as computed again here,
; is not, the book's notes say so, with the library's own notes of its
; order.

(defun bx-library-problems (notes)
  (declare (xargs :guard (alistp notes)))
  (let ((problems (bx-select :note notes)))
    (if problems
        (list (bx-note "library whose lines could not be admitted in order"
                       problems))
      nil)))

(defun bx-book-lines (ground-fns boot-hi lo hi translations books-dir cbd wrld)
  (declare (xargs :guard (and (integerp boot-hi) (integerp lo) (integerp hi)
                              (stringp books-dir) (stringp cbd)
                              (symbol-listp ground-fns) (bx-export-world-p wrld)
                              (bx-functions-present-p ground-fns wrld)
                              (bx-functions-present-p
                               (strip-cars *primitive-formals-and-guards*) wrld)
                              (bx-translations-p translations)
                              (bx-world-aids-p wrld) (bx-book-globals-p wrld))))
  (let* ((boot-evs (bx-events wrld 0 boot-hi nil))
         (lib-items (bx-items (bx-enclose (reverse boot-evs) nil nil wrld)
                              nil nil nil wrld nil))
         (lib-stmts (bx-not-ground (bx-select :stmt lib-items) ground-fns))
         (items (bx-range-items lo hi translations wrld))
         (stmts (bx-select :stmt items))
         (progs (bx-select :prog items)))
    (mv-let (lib-ordered order-notes)
      (bx-library-order lib-stmts)
      (mv-let (fns names pkgs)
        (bx-ground-tables ground-fns wrld)
        (mv-let (lib-notes fns names pkgs seen)
          (bx-check-stmts lib-ordered fns names pkgs nil nil)
          (mv-let (check-notes fns names pkgs seen)
            (bx-check-stmts stmts fns names pkgs seen nil)
            (declare (ignore fns names pkgs))
            (let ((notes (bx-book-notes items
                                        (append (bx-library-problems
                                                 (append order-notes lib-notes))
                                                check-notes)
                                        boot-hi lo hi books-dir cbd wrld))
                  (pairs (bx-attachment-pairs wrld))
                  (boot-pairs (bx-attachment-pairs (bx-world-at boot-hi wrld))))
              (prog2$
               (fast-alist-free seen)
               (mv stmts
                   (append (bx-runnable progs)
                           (bx-attach-lines pairs boot-pairs))
                   (append (bx-count-lines stmts)
                           (bx-note-lines notes))
                   (bx-event-aids (bx-events wrld lo hi nil) wrld))))))))))
