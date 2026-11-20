; Boymoo, the checker: admitting statements (spec/logic.md, section 6), with
; the obligations of termination and of witnesses.

(in-package "BOYMOO")

(include-book "rules")

; ---------------------------------------------------------------------------
; Names (spec/language.md, section 6)

(defun new-name-p (s w)
  (and (symbolp s)
       (not (keyword-sym-p s))
       (not (name-entry s w))))

; BOOK is true for a line of the statements or of the proofs, where a
; function may not be named by a symbol of COMMON-LISP.
(defun new-fn-name-p (s book w)
  (and (new-name-p s w)
       (not (equal s '|COMMON-LISP::QUOTE|))
       (not (and book (cl-sym-p s)))))

; Puts an entry for each of the names NAMES, with ARITIES, and with LINE
; on the first.
(defun put-entries (names arities facts line w)
  (if (consp names)
      (put-entries (cdr names) (cdr arities) (cdr facts) nil
                   (put-entry (car names)
                              (list (car arities) (car facts) line)
                              w))
    w))

; Sets the arity of each function of FNS, an association list from
; functions to their numbers of arguments, so that it is in use, keeping
; the rest of its entry.
(defun enable-fns (fns w)
  (if (consp fns)
      (enable-fns (cdr fns)
                  (let ((e (name-entry (car (car fns)) w)))
                    (put-entry (car (car fns))
                               (list (cdr (car fns)) (entry-fact e) (entry-line e))
                               w)))
    w))

; Sets the fact of each name of NAMES to the corresponding fact of FACTS,
; keeping the rest of its entry.
(defun add-facts (names facts w)
  (if (consp names)
      (add-facts (cdr names) (cdr facts)
                 (let ((e (name-entry (car names) w)))
                   (put-entry (car names)
                              (list (entry-arity e) (car facts) (entry-line e))
                              w)))
    w))

(defun unit-fact (term)
  (cons (list term) (list (size term))))

; ---------------------------------------------------------------------------
; Packages

(defun symbol-names (l)
  (if (consp l)
      (cons (sym-name (car l)) (symbol-names (cdr l)))
    nil))

; The characters A come before B by string<.
(defun chars-less-p (a b)
  (if (consp a)
      (if (consp b)
          (let ((x (char-code (car a)))
                (y (char-code (car b))))
            (if (< x y)
                t
              (if (equal x y) (chars-less-p (cdr a) (cdr b)) nil)))
        nil)
    (consp b)))

; Each name before the next by string<, so that no two are the same.
(defun ascending-p (names)
  (if (and (consp names) (consp (cdr names)))
      (and (chars-less-p (car names) (car (cdr names)))
           (ascending-p (cdr names)))
    t))

(defun lower-case-in-p (cs)
  (if (consp cs)
      (let ((n (char-code (car cs))))
        (if (and (< 96 n) (< n 123)) t (lower-case-in-p (cdr cs))))
    nil))

(defun import-trie (imports names node)
  (if (consp imports)
      (import-trie (cdr imports) (cdr names)
                   (trie-put (car names) (car imports) node))
    node))

; Conditions 2 to 6 of a package statement, on the name as characters and
; the imports.
(defun package-conditions (name imports)
  (and (symbol-listp imports)
       (let ((names (symbol-names imports)))
         (and (ascending-p names)
              (not (member-p (coerce "ACL2-PKG-WITNESS" 'list) names))))
       (not (lower-case-in-p name))
       (not (equal name (coerce "LISP" 'list)))
       (not (prefix-p (coerce "ACL2_*1*_" 'list) name))))

(defun declare-package (name imports hidden lines w)
  (set-pkgs (trie-put name
                      (list imports
                            (import-trie imports (symbol-names imports) nil)
                            hidden
                            lines)
                      (w-pkgs w))
            w))

; The name of ACL2's rule for the package NAME, NAME-PACKAGE interned in
; ACL2.
(defun package-rule-name (name w)
  (intern-sym (app name (coerce "-PACKAGE" 'list)) *acl2-chars* w))

(defun package-fact (string imports)
  (unit-fact (list '|COMMON-LISP::EQUAL|
                   (list '|ACL2::PKG-IMPORTS| (list '|COMMON-LISP::QUOTE| string))
                   (list '|COMMON-LISP::QUOTE| imports))))

(defun admit-package (data line w)
  (if (and (consp data) (consp (cdr data)) (equal (cdr (cdr data)) nil)
           (stringp (car data)) (not (equal (car data) "")))
      (let* ((string (car data))
             (name (coerce string 'list))
             (imports (car (cdr data)))
             (rec (trie-get name (w-pkgs w))))
        (if (and (package-conditions name imports)
                 (or (not rec)
                     (and (prec-hidden rec) (equal (prec-imports rec) imports))))
            (let ((rule (package-rule-name name w)))
              (if (new-name-p rule w)
                  (cons (put-entry rule (list nil (package-fact string imports) nil)
                                   (declare-package name imports nil
                                                    (cons line (prec-lines rec))
                                                    w))
                        nil)
                "the name of the package's rule is in use"))
          "a package that may not be declared"))
    "a package line needs a name and imports"))

(defun admit-hidden-package (data line w)
  (if (and (consp data) (consp (cdr data)) (equal (cdr (cdr data)) nil)
           (stringp (car data)) (not (equal (car data) "")))
      (let ((name (coerce (car data) 'list))
            (imports (car (cdr data))))
        (if (and (package-conditions name imports)
                 (not (trie-get name (w-pkgs w))))
            (cons (declare-package name imports t (list line) w) nil)
          "a hidden package that may not be declared"))
    "a hidden-package line needs a name and imports"))

; ---------------------------------------------------------------------------
; Definitions

; Each element of DEFS is a list (F FORMALS BODY).
(defun defs-shape-p (defs)
  (if (consp defs)
      (let ((d (car defs)))
        (and (consp d) (consp (cdr d)) (consp (cdr (cdr d)))
             (equal (cdr (cdr (cdr d))) nil)
             (defs-shape-p (cdr defs))))
    (equal defs nil)))

(defun def-names (defs)
  (if (consp defs) (cons (car (car defs)) (def-names (cdr defs))) nil))

(defun def-arities (defs)
  (if (consp defs)
      (cons (cons (car (car defs)) (len (car (cdr (car defs)))))
            (def-arities (cdr defs)))
    nil))

(defun def-bodies (defs)
  (if (consp defs)
      (cons (car (cdr (cdr (car defs)))) (def-bodies (cdr defs)))
    nil))

(defun fn-names-p (names book w)
  (if (consp names)
      (and (new-fn-name-p (car names) book w) (fn-names-p (cdr names) book w))
    t))

(defun names-p (names w)
  (if (consp names)
      (and (new-name-p (car names) w) (names-p (cdr names) w))
    t))

(defun defs-terms-p (defs extra w)
  (if (consp defs)
      (let ((formals (car (cdr (car defs)))))
        (and (variable-list-p formals w)
             (distinct-p formals)
             (term-p (car (cdr (cdr (car defs)))) formals extra w)
             (defs-terms-p (cdr defs) extra w)))
    t))

(defun equation (f formals body)
  (unit-fact (list '|COMMON-LISP::EQUAL| (cons f formals) body)))

(defun equations (defs)
  (if (consp defs)
      (cons (equation (car (car defs)) (car (cdr (car defs)))
                      (car (cdr (cdr (car defs)))))
            (equations (cdr defs)))
    nil))

(defun arities-of (fns)
  (if (consp fns) (cons (cdr (car fns)) (arities-of (cdr fns))) nil))

; Puts the functions of DEFS in use, with their equations.
(defun add-definitions (defs w)
  (add-facts (def-names defs) (equations defs)
             (enable-fns (def-arities defs) w)))

; The result of admitting a line is (W . PENDING), where PENDING is NIL or
; says what the line's entry in the proofs must show; or a string that says
; why the line fails.
(defun admit-define (data line book library w)
  (if (consp data)
      (let ((rulers (car data))
            (defs (cdr data)))
        (if (and (or (equal rulers '|KEYWORD::ALL|) (symbol-listp rulers))
                 (consp defs)
                 (defs-shape-p defs))
            (let ((names (def-names defs))
                  (extra (def-arities defs)))
              (if (and (fn-names-p names book w)
                       (distinct-p names)
                       (defs-terms-p defs extra w))
                  (let ((recursive (calls-list-p (def-bodies defs) names)))
                    (if (and recursive (not library))
                        (cons (put-entries names nil nil line w)
                              (list :define rulers defs))
                      (let ((w (add-definitions defs (put-entries names nil nil line w))))
                        (cons (if recursive (count-one 2 w) w) nil))))
                "a definition that may not be admitted"))
          "a define line needs ruler-extenders and definitions"))
    "a define line needs ruler-extenders and definitions"))

; ---------------------------------------------------------------------------
; Constraints

; Each element of FNS is a list (F N), N an integer that is not negative.
(defun constrain-fns-p (fns)
  (if (consp fns)
      (let ((x (car fns)))
        (and (consp x) (symbolp (car x)) (consp (cdr x)) (natp (car (cdr x)))
             (equal (cdr (cdr x)) nil)
             (constrain-fns-p (cdr fns))))
    (equal fns nil)))

(defun constrain-arities (fns)
  (if (consp fns)
      (cons (cons (car (car fns)) (car (cdr (car fns))))
            (constrain-arities (cdr fns)))
    nil))

; Each element of FORMULAS is a list (NAME TERM).
(defun formulas-shape-p (formulas)
  (if (consp formulas)
      (let ((x (car formulas)))
        (and (consp x) (consp (cdr x)) (equal (cdr (cdr x)) nil)
             (formulas-shape-p (cdr formulas))))
    (equal formulas nil)))

(defun formula-names (formulas)
  (if (consp formulas)
      (cons (car (car formulas)) (formula-names (cdr formulas)))
    nil))

(defun formula-terms (formulas)
  (if (consp formulas)
      (cons (car (cdr (car formulas))) (formula-terms (cdr formulas)))
    nil))

(defun unit-facts (terms)
  (if (consp terms) (cons (unit-fact (car terms)) (unit-facts (cdr terms))) nil))

(defun add-constraint (fns formulas w)
  (add-facts (formula-names formulas) (unit-facts (formula-terms formulas))
             (enable-fns fns w)))

(defun admit-constrain (data line book library w)
  (if (and (consp data) (consp (cdr data)) (equal (cdr (cdr data)) nil)
           (consp (car data))
           (constrain-fns-p (car data))
           (formulas-shape-p (car (cdr data))))
      (let* ((fns (constrain-arities (car data)))
             (formulas (car (cdr data)))
             (fnames (def-names fns))
             (names (formula-names formulas)))
        (if (and (fn-names-p fnames book w)
                 (names-p names w)
                 (distinct-p (app fnames names))
                 (terms-p (formula-terms formulas) :any fns w))
            (let ((w (put-entries names nil nil nil
                                  (put-entries fnames nil nil line w))))
              (if (and (consp formulas) (not library))
                  (cons w (list :constrain fns formulas))
                (let ((w (add-constraint fns formulas w)))
                  (cons (if (consp formulas) (count-one 2 w) w) nil))))
          "a constraint that may not be admitted"))
    "a constrain line needs functions and formulas"))

; ---------------------------------------------------------------------------
; Choice (spec/logic.md, section 6)

(defun mv-nth-terms (n k call)
  (if (zp k)
      nil
    (cons (list '|ACL2::MV-NTH| (list '|COMMON-LISP::QUOTE| n) call)
          (mv-nth-terms (+ 1 n) (+ -1 k) call))))

(defun choice-subst (bound call)
  (if (consp (cdr bound))
      (pair-up bound (mv-nth-terms 0 (len bound) call))
    (list (cons (car bound) call))))

(defun choice-axiom (f bound free body free2)
  (let* ((call (cons f free))
         (s (choice-subst bound call))
         (implication (list '|ACL2::IMPLIES| body (subst-term body s)))
         (basic (if (consp (cdr bound))
                    (list '|COMMON-LISP::IF| (list '|ACL2::TRUE-LISTP| call)
                          implication *nil-term*)
                  implication)))
    (if (equal free2 nil)
        basic
      (let* ((call2 (cons f free2))
             (s2 (choice-subst bound call2))
             (ren (pair-up free free2))
             (d1 (list '|COMMON-LISP::EQUAL| call call2))
             (d2 (list '|COMMON-LISP::IF| (subst-term body s)
                       (list '|COMMON-LISP::NOT| (subst-term body (app s ren)))
                       *nil-term*))
             (d3 (list '|COMMON-LISP::IF| (subst-term body (app s2 ren))
                       (list '|COMMON-LISP::NOT| (subst-term body s2))
                       *nil-term*)))
        (list '|COMMON-LISP::IF| basic
              (list '|COMMON-LISP::IF| d1 d1 (list '|COMMON-LISP::IF| d2 d2 d3))
              *nil-term*)))))

(defun admit-choose (data line book w)
  (if (and (consp data) (consp (cdr data)) (consp (cdr (cdr data)))
           (consp (cdr (cdr (cdr data))))
           (consp (cdr (cdr (cdr (cdr data)))))
           (equal (cdr (cdr (cdr (cdr (cdr data))))) nil))
      (let ((f (car data))
            (bound (car (cdr data)))
            (free (car (cdr (cdr data))))
            (body (car (cdr (cdr (cdr data)))))
            (free2 (car (cdr (cdr (cdr (cdr data)))))))
        (if (and (new-fn-name-p f book w)
                 (consp bound)
                 (variable-list-p bound w) (distinct-p bound)
                 (variable-list-p free w) (distinct-p free)
                 (disjoint-p bound free)
                 (term-p body (app bound free) nil w)
                 (or (equal free2 nil)
                     (and (variable-list-p free2 w) (distinct-p free2)
                          (equal (len free2) (len free))
                          (disjoint-p free2 (app bound free)))))
            (cons (put-entry f (list (len free)
                                     (unit-fact (choice-axiom f bound free body free2))
                                     line)
                             w)
                  nil)
          "a choice that may not be admitted"))
    "a choose line needs five data"))

; ---------------------------------------------------------------------------
; Theorems, axioms and reserved names

(defun admit-theorem (data line library w)
  (if (and (consp data) (consp (cdr data)) (equal (cdr (cdr data)) nil))
      (let ((name (car data))
            (term (car (cdr data))))
        (if (and (new-name-p name w) (term-p term :any nil w))
            (if library
                (cons (count-one 3 (put-entry name (list nil (unit-fact term) line) w))
                      nil)
              (cons (put-entry name (list nil nil line) w)
                    (list :theorem name term)))
          "a theorem that may not be admitted"))
    "a theorem line needs a name and a term"))

(defun admit-axiom (data line library w)
  (if (and (consp data) (consp (cdr data)) (equal (cdr (cdr data)) nil))
      (let ((name (car data))
            (term (car (cdr data))))
        (if (and (new-name-p name w) (term-p term :any nil w))
            (cons (count-one (if library 3 1)
                             (put-entry name (list nil (unit-fact term) line) w))
                  nil)
          "an axiom that may not be admitted"))
    "an axiom line needs a name and a term"))

(defun admit-reserve (data line w)
  (if (and (consp data) (equal (cdr data) nil))
      (if (new-name-p (car data) w)
          (cons (put-entry (car data) (list nil nil line) w) nil)
        "a reserved name that is in use or no name")
    "a reserve line needs one name"))

; ---------------------------------------------------------------------------
; A line that repeats an earlier one
;
; A line repeats an earlier line of the library or of the statements
; exactly when it repeats the line that introduced its first name, or, for
; a package, one of the lines that declared it: an admitted line's first
; name was new when it was read.  Two lines in the format are the same
; bytes exactly when their words and data are the same.

(defun first-name (line)
  (let ((word (car line))
        (data (cdr line)))
    (cond ((equal word :define) (car (car (cdr data))))
          ((equal word :constrain) (car (car (car data))))
          (t (car data)))))

(defun repeat-p (line w)
  (let ((word (car line)))
    (if (or (equal word :package) (equal word :hidden-package))
        (and (stringp (car (cdr line)))
             (member-p line
                       (prec-lines (trie-get (coerce (car (cdr line)) 'list)
                                             (w-pkgs w)))))
      (let ((name (first-name line)))
        (and (symbolp name)
             (equal (entry-line (name-entry name w)) line))))))

; ---------------------------------------------------------------------------
; A line of the library (INPUT :LIBRARY), of the statements (:STATEMENTS)
; or a define entry of the proofs (:PROOFS), whose line is kept nowhere.

(defun admit (line input w)
  (let ((word (car line))
        (data (cdr line))
        (book (not (equal input :library)))
        (library (equal input :library))
        (stored (if (equal input :proofs) nil line)))
    (if (and stored (repeat-p line w))
        (cons w nil)
      (cond ((equal word :package) (admit-package data stored w))
            ((equal word :hidden-package) (admit-hidden-package data stored w))
            ((equal word :define) (admit-define data stored book library w))
            ((equal word :constrain) (admit-constrain data stored book library w))
            ((equal word :choose) (admit-choose data stored book w))
            ((equal word :theorem) (admit-theorem data stored library w))
            ((equal word :axiom) (admit-axiom data stored library w))
            ((equal word :reserve) (admit-reserve data stored w))
            (t "a word that may not stand here")))))

; ---------------------------------------------------------------------------
; The obligations of termination (spec/logic.md, section 6)
;
; The walk goes through a body with the rulers so far, as the literals they
; give, reversed, with their sizes; and with the substitution of that
; moment, as an association list from variables to terms, ST, and one from
; variables to the sizes of those terms, SS.  The substituted terms share
; structure, so building them costs no more than the terms walked; their
; sizes, which may be far larger, are counted.  CTX is (FNS EXT MI MI-SIZE):
; FNS associates each function of the definition with its formals and its
; measure, EXT is the ruler-extenders, and MI is the measure of the
; function whose body is walked.  Each call recorded gives its clause,
; pushed on ACC.
;
; To record the calls in a lambda application, the walk records those in
; its actuals and then those in its body under the substitution that puts
; the actuals for the formals.  Taking the body with the formals replaced
; by the actuals would record the calls in an actual once more for each
; occurrence of its formal, under the same rulers and substitution: the
; same clauses, which are left out.

(defun extends-p (g ext)
  (if (equal ext '|KEYWORD::ALL|) t (member-p g ext)))

(defun lambdas-extend-p (ext)
  (if (equal ext '|KEYWORD::ALL|) t (member-p '|KEYWORD::LAMBDAS| ext)))

(defun call-clause (x rl rs st ss ctx)
  (let* ((fn (cdr (pair-of (car x) (car ctx))))
         (formals (car fn))
         (mj (car (cdr fn)))
         (mj2 (subst-term mj (pair-up formals (subst-terms (cdr x) st))))
         (size (subst-size mj (pair-up formals (subst-sizes (cdr x) ss)))))
    (cons (rev-onto rl (list (list '|ACL2::O<| mj2 (car (cdr (cdr ctx))))))
          (rev-onto rs (list (+ 5 size (car (cdr (cdr (cdr ctx))))))))))

(defun record-call-if (x rl rs st ss ctx acc)
  (if (pair-of (car x) (car ctx))
      (cons (call-clause x rl rs st ss ctx) acc)
    acc))

; The walk may record the calls in the very term it was given, so its
; measure is one more than that of recording them.
(mutual-recursion
 (defun walk (x rl rs st ss ctx acc)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count x)))))
   (if (consp x)
       (let ((ext (car (cdr ctx))))
         (if (equal (car x) '|COMMON-LISP::QUOTE|)
             acc
           (if (consp (car x))
               (let ((acc (if (lambdas-extend-p ext)
                              (walk-list (cdr x) rl rs st ss ctx acc)
                            (record-list (cdr x) rl rs st ss ctx acc)))
                     (formals (car (cdr (car x)))))
                 (walk (car (cdr (cdr (car x)))) rl rs
                       (pair-up formals (subst-terms (cdr x) st))
                       (pair-up formals (subst-sizes (cdr x) ss))
                       ctx acc))
             (if (equal (car x) '|COMMON-LISP::IF|)
                 (let* ((a (car (cdr x)))
                        (acc (if (extends-p '|COMMON-LISP::IF| ext)
                                 (walk a rl rs st ss ctx acc)
                               (record a rl rs st ss ctx acc)))
                        (a2 (subst-term a st))
                        (n (subst-size a ss)))
                   (walk (car (cdr (cdr (cdr x))))
                         (cons a2 rl) (cons n rs) st ss ctx
                         (walk (car (cdr (cdr x)))
                               (cons (list '|COMMON-LISP::NOT| a2) rl)
                               (cons (+ 4 n) rs) st ss ctx acc)))
               (if (mbe-p x)
                   (walk (car (cdr (cdr (cdr x)))) rl rs st ss ctx acc)
                 (if (extends-p (car x) ext)
                     (walk-list (cdr x) rl rs st ss ctx
                                (record-call-if x rl rs st ss ctx acc))
                   (record x rl rs st ss ctx acc)))))))
     acc))
 (defun walk-list (xs rl rs st ss ctx acc)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count xs)))))
   (if (consp xs)
       (walk-list (cdr xs) rl rs st ss ctx (walk (car xs) rl rs st ss ctx acc))
     acc))
 (defun record (x rl rs st ss ctx acc)
   (declare (xargs :measure (* 2 (acl2-count x))))
   (if (consp x)
       (if (equal (car x) '|COMMON-LISP::QUOTE|)
           acc
         (if (consp (car x))
             (let ((formals (car (cdr (car x)))))
               (record (car (cdr (cdr (car x)))) rl rs
                       (pair-up formals (subst-terms (cdr x) st))
                       (pair-up formals (subst-sizes (cdr x) ss))
                       ctx
                       (record-list (cdr x) rl rs st ss ctx acc)))
           (if (mbe-p x)
               (record (car (cdr (cdr (cdr x)))) rl rs st ss ctx acc)
             (record-list (cdr x) rl rs st ss ctx
                          (record-call-if x rl rs st ss ctx acc)))))
     acc))
 (defun record-list (xs rl rs st ss ctx acc)
   (declare (xargs :measure (* 2 (acl2-count xs))))
   (if (consp xs)
       (record-list (cdr xs) rl rs st ss ctx (record (car xs) rl rs st ss ctx acc))
     acc)))

; The association list from each function of DEFS to its formals and its
; measure, from MEASURES.
(defun measure-table (defs measures)
  (if (consp defs)
      (cons (list (car (car defs)) (car (cdr (car defs))) (car measures))
            (measure-table (cdr defs) (cdr measures)))
    nil))

; The clauses ((o-p Mi)), reversed onto ACC.
(defun o-p-clauses (measures acc)
  (if (consp measures)
      (o-p-clauses (cdr measures)
                   (cons (cons (list (list '|ACL2::O-P| (car measures)))
                               (list (+ 4 (size (car measures)))))
                         acc))
    acc))

; The clauses of the calls in each body, reversed onto ACC.
(defun call-clauses (defs measures fns ext acc)
  (if (consp defs)
      (call-clauses (cdr defs) (cdr measures) fns ext
                    (walk (car (cdr (cdr (car defs)))) nil nil nil nil
                          (list fns ext (car measures) (size (car measures)))
                          acc))
    acc))

; A clause of KEPT, a list of (SIZE LITS . SIZES), has the size N and the
; literals LITS.
(defun kept-p (n lits kept)
  (if (consp kept)
      (if (and (equal n (car (car kept))) (equal lits (car (cdr (car kept)))))
          t
        (kept-p n lits (cdr kept)))
    nil))

; The clauses CANDS without those that repeat an earlier one, reversed
; onto KEPT, or :OVER if their sizes sum to more than the budget.  Only a
; clause whose size is that of a clause kept can repeat it.
(defun keep-clauses (cands kept total)
  (if (consp cands)
      (let* ((c (car cands))
             (n (sum (cdr c))))
        (if (kept-p n (car c) kept)
            (keep-clauses (cdr cands) kept total)
          (if (< (- *budget* total) n)
              :over
            (keep-clauses (cdr cands) (cons (cons n c) kept) (+ total n)))))
    kept))

(defun kept-lits (kept acc)
  (if (consp kept)
      (kept-lits (cdr kept) (cons (car (cdr (car kept))) acc))
    acc))

; The obligations of termination of DEFS under the measures MEASURES and
; the ruler-extenders EXT, as a list of clauses, or :OVER.
(defun termination-obligations (defs measures ext)
  (let* ((fns (measure-table defs measures))
         (cands (rev (call-clauses defs measures fns ext
                                   (o-p-clauses measures nil))))
         (kept (keep-clauses cands nil 0)))
    (if (equal kept :over) :over (kept-lits kept nil))))

; The measures of a measure entry: one term for each definition, whose
; variables are among its formals, and which calls only functions in use.
(defun measures-p (measures defs w)
  (if (consp defs)
      (and (consp measures)
           (term-p (car measures) (car (cdr (car defs))) nil w)
           (measures-p (cdr measures) (cdr defs) w))
    (equal measures nil)))

; The witnesses of a witness entry: for each function (F . N), a function
; in use with N arguments.
(defun witnesses-p (gs fns w)
  (if (consp fns)
      (and (consp gs)
           (symbolp (car gs))
           (equal (entry-arity (name-entry (car gs) w)) (cdr (car fns)))
           (witnesses-p (cdr gs) (cdr fns) w))
    (equal gs nil)))

(defun witness-obligations (terms ren)
  (if (consp terms)
      (cons (list (rename-calls (car terms) ren))
            (witness-obligations (cdr terms) ren))
    nil))
