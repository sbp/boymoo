; The comparison of the obligations of termination that the checker
; computes with ACL2's measure conjectures, for every definition of ACL2's
; world that has a justification (review/termination/README.md).
; review/termination/one.sh loads it, from the root of the repository,
; after the book build/checker/acl2/check, the book of the printer
; checks/canon.lisp as export/certify.sh certifies it, and the tool
; review/termination/obligations.lisp.

(in-package "ACL2")

(program)
(set-state-ok t)

;;; 1. Files

(defun tt-read-bytes (channel acc state)
  (mv-let (byte state)
    (read-byte$ channel state)
    (if (null byte)
        (mv (coerce (reverse acc) 'string) state)
      (tt-read-bytes channel (cons (code-char byte) acc) state))))

; The bytes of the file NAME as a string, one character for each byte; or
; NIL if it cannot be opened.
(defun tt-file-string (name state)
  (mv-let (channel state)
    (open-input-channel name :byte state)
    (if (null channel)
        (mv nil state)
      (mv-let (string state)
        (tt-read-bytes channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv string state))))))

;;; 2. Lines

(defun tt-write-lines (lines chan state)
  (cond ((endp lines) state)
        (t (pprogn (princ$ (car lines) chan state)
                   (newline chan state)
                   (tt-write-lines (cdr lines) chan state)))))

(defun tt-write-file (lines file state)
  (mv-let (chan state)
    (open-output-channel file :character state)
    (pprogn (tt-write-lines lines chan state)
            (close-output-channel chan state))))

;;; 3. ACL2's side

; The functions that have a justification, introduced in the part of the
; world WRLD above its tail OLD, each once.
(defun tt-justified (wrld old acc)
  (cond ((or (endp wrld) (eq wrld old)) acc)
        (t (tt-justified
            (cdr wrld) old
            (let ((trip (car wrld)))
              (if (and (eq (cadr trip) 'justification)
                       (cddr trip)
                       (not (eq (cddr trip) *acl2-property-unbound*)))
                  (add-to-set-eq (car trip) acc)
                acc))))))

; ACL2's measure conjectures for the definition of the functions NAMES, the
; value of (getpropc F 'recursivep) for each F among them: the clauses of
; ACL2's function TERMINATION-THEOREM-CLAUSES, called as ACL2's function
; TERMINATION-THEOREM calls it, from the world's justification, body and
; ruler-extenders of each function; or :FAILED when a measure is a call of
; :?, for which ACL2 has no termination theorem.
(defun tt-acl2-clauses (names wrld)
  (let* ((fn (car names))
         (just (getpropc fn 'justification nil wrld))
         (measure-alist (measure-alist? names wrld)))
    (if (eq (car measure-alist) :failed)
        :failed
      (termination-theorem-clauses
       t
       (if (cdr names) nil (getpropc fn 'loop$-recursion nil wrld))
       names
       (if (cdr names) nil (list (formals fn wrld)))
       (get-unnormalized-bodies names wrld)
       measure-alist
       (access justification just :mp)
       (access justification just :rel)
       (ruler-extenders-lst names wrld)
       wrld))))

; ACL2's measure conjectures before ACL2 removes the clauses that repeat
; a later one: for each function of NAMES, in order, the clause (MP M) of
; its measure M, unless MP is T, and then the clause of each call that its
; termination machine records, as ACL2's functions MEASURE-CLAUSES-FOR-FN
; and MEASURE-CLAUSE-FOR-BRANCH build them; MEASURE-CLAUSES-FOR-CLIQUE
; joins these with CONJOIN-CLAUSE-TO-CLAUSE-SET, which keeps the last of
; two copies.  The termination machines are those that
; TERMINATION-THEOREM-CLAUSES builds, from the same arguments.

(defun tt-branch-clauses (name tcs measure-alist rel wrld)
  (cond ((endp tcs) nil)
        (t (cons (measure-clause-for-branch name (car tcs) measure-alist rel
                                            nil wrld)
                 (tt-branch-clauses name (cdr tcs) measure-alist rel wrld)))))

(defun tt-raw-clauses (names t-machines measure-alist mp rel wrld)
  (cond ((endp names) nil)
        (t (append (if (eq mp t)
                       nil
                     (list (add-literal
                            (mcons-term* mp (cdr (assoc-eq (car names)
                                                           measure-alist)))
                            nil t)))
                   (tt-branch-clauses (car names) (car t-machines)
                                      measure-alist rel wrld)
                   (tt-raw-clauses (cdr names) (cdr t-machines) measure-alist
                                   mp rel wrld)))))

(defun tt-acl2-raw (names wrld)
  (let* ((fn (car names))
         (just (getpropc fn 'justification nil wrld))
         (measure-alist (measure-alist? names wrld)))
    (tt-raw-clauses
     names
     (termination-machines t
                           (if (cdr names) nil
                             (getpropc fn 'loop$-recursion nil wrld))
                           names
                           (if (cdr names) nil (list (formals fn wrld)))
                           (get-unnormalized-bodies names wrld)
                           (ruler-extenders-lst names wrld))
     measure-alist
     (access justification just :mp)
     (access justification just :rel)
     wrld)))

(defun tt-measures (names wrld)
  (cond ((endp names) nil)
        (t (cons (access justification
                         (getpropc (car names) 'justification nil wrld)
                         :measure)
                 (tt-measures (cdr names) wrld)))))

(defun tt-chars (string)
  (append (coerce string 'list) (list #\Newline)))

(defun tt-text (x)
  (coerce (reverse (bm-obj x nil)) 'string))

(defun tt-clause-lines (clauses)
  (cond ((endp clauses) nil)
        (t (cons (tt-chars (bm-line "clause" (car clauses)))
                 (tt-clause-lines (cdr clauses))))))

; The trie that obligations.lisp reads (GIVEN there): for each function
; of FNS, the text of its name to the line (measure F1 M1 ... Mk) for the
; functions F1, ..., Fk of its definition, in the order of their
; RECURSIVEP property, with the measures of their justifications, and the
; lines of ACL2's measure conjectures.  DONE associates the first function
; of each definition already done with its lines.
(defun tt-given (fns done trie wrld)
  (cond
   ((endp fns) trie)
   (t (let* ((names (getpropc (car fns) 'recursivep nil wrld))
             (prev (assoc-eq (car names) done))
             (lines
              (or (cdr prev)
                  (let ((clauses (tt-acl2-clauses names wrld)))
                    (cons (tt-chars (bm-line "measure"
                                             (cons (car names)
                                                   (tt-measures names wrld))))
                          (if (eq clauses :failed)
                              nil
                            (tt-clause-lines clauses)))))))
        (tt-given (cdr fns)
                  (if prev done (acons (car names) lines done))
                  (boymoo::trie-put (coerce (tt-text (car fns)) 'list)
                                    lines trie)
                  wrld)))))

;;; 4. The normal form

; ACL2 writes a test as its termination machine finds it: with the guard
; holders removed by REMOVE-GUARD-HOLDERS-WEAK, its calls of primitives on
; constants folded by SUBLIS-VAR, and negated by DUMB-NEGATE-LIT.  The
; normal form applies the same three functions to every literal of both
; sides.  A literal (not S) becomes (dumb-negate-lit S'), and any other
; literal L becomes (dumb-negate-lit (dumb-negate-lit L')), where X' is
; (sublis-var nil (remove-guard-holders-weak X nil)).  Each step gives a
; literal that is equal to the one before, as a proposition.

(defun tt-tidy (x)
  (sublis-var nil (remove-guard-holders-weak x nil)))

(defun tt-lit (l)
  (if (and (consp l) (eq (car l) 'not))
      (dumb-negate-lit (tt-tidy (cadr l)))
    (dumb-negate-lit (dumb-negate-lit (tt-tidy l)))))

; ACL2 drops a test that a later one implies: when it adds a test that
; equates a term Y to a constant C, by EQUAL, EQ, EQL or =, it removes each
; earlier test that says that Y is not some other constant (ACL2's
; functions ADD-TEST-SMART and SIMPLIFY-TESTS).  In a clause, whose
; literals are the negations of the tests, that removes an earlier literal
; that says Y is C2 when a later one says Y is not C, C and C2 being
; different constants.  The normal form removes every such literal.  A
; literal says that Y is C when it is (E Y 'C) or (E 'C Y), E among those
; four, or when it is (not Y) and C is NIL; it says that Y is not C when
; it is (not (E Y 'C)) or (not (E 'C Y)), or when it is Y itself and C is
; NIL.  The literal removed is false whenever the later one is false, so
; the clause stays equal to the one before, as a proposition.

(defun tt-says (lit)
  (if (and (consp lit) (eq (car lit) 'not))
      (mv-let (y c) (term-equated-to-constant (cadr lit))
        (if y (mv :not y c) (mv :is (cadr lit) *nil*)))
    (mv-let (y c) (term-equated-to-constant lit)
      (if y (mv :is y c) (mv :not lit *nil*)))))

(defun tt-later-not (y c2 lits)
  (cond ((endp lits) nil)
        (t (mv-let (kind y1 c) (tt-says (car lits))
             (or (and (eq kind :not) (equal y1 y) (not (equal c c2)))
                 (tt-later-not y c2 (cdr lits)))))))

(defun tt-drop-implied (lits)
  (cond ((endp lits) nil)
        (t (mv-let (kind y c) (tt-says (car lits))
             (if (and (eq kind :is) (tt-later-not y c (cdr lits)))
                 (tt-drop-implied (cdr lits))
               (cons (car lits) (tt-drop-implied (cdr lits))))))))

; The literals of a clause in normal form, without those that are 'NIL; or
; :TRUE if one is 'T.
(defun tt-lits1 (lits)
  (cond ((endp lits) nil)
        (t (let ((l (tt-lit (car lits)))
                 (rest (tt-lits1 (cdr lits))))
             (cond ((or (equal l *t*) (eq rest :true)) :true)
                   ((equal l *nil*) rest)
                   (t (cons l rest)))))))

(defun tt-lits (lits)
  (let ((ls (tt-lits1 lits)))
    (if (eq ls :true) :true (tt-drop-implied ls))))

; The clauses in normal form, without those that are :TRUE and without
; those that repeat an earlier one; the clauses of one literal, a call of
; O-P, stand first, in their order.
(defun tt-norm1 (clauses)
  (cond ((endp clauses) nil)
        (t (let ((c (tt-lits (car clauses)))
                 (rest (tt-norm1 (cdr clauses))))
             (if (eq c :true) rest (cons c rest))))))

(defun tt-o-p-clause-p (c)
  (and (consp c) (null (cdr c)) (consp (car c)) (eq (caar c) 'o-p)))

(defun tt-split (clauses ops others)
  (cond ((endp clauses) (append (reverse ops) (reverse others)))
        ((tt-o-p-clause-p (car clauses))
         (tt-split (cdr clauses) (cons (car clauses) ops) others))
        (t (tt-split (cdr clauses) ops (cons (car clauses) others)))))

(defun tt-norm (clauses)
  (remove-duplicates-equal-from-end (tt-split (tt-norm1 clauses) nil nil) nil))

; The steps of the normal form that change something in the clauses of
; one side, as a list of strings, for the report: "guard-holders" when
; REMOVE-GUARD-HOLDERS-WEAK changes a literal, "constants" when SUBLIS-VAR
; then folds a call on constants, "negation" when DUMB-NEGATE-LIT then
; changes it, "false-literal" when a literal 'NIL is removed,
; "true-clause" when a clause with a literal 'T is removed,
; "implied-test" when a literal is removed because a later one implies it,
; "o-p-first" when the clauses of the o-p of the measures move to the
; front, and "repeat" when a clause that repeats an earlier one is removed.

(defun tt-lit-steps (l acc)
  (let* ((notp (and (consp l) (eq (car l) 'not)))
         (s (if notp (cadr l) l))
         (r (remove-guard-holders-weak s nil))
         (f (sublis-var nil r))
         (final (if notp
                    (dumb-negate-lit f)
                  (dumb-negate-lit (dumb-negate-lit f))))
         (acc (if (equal r s) acc (add-to-set-equal "guard-holders" acc)))
         (acc (if (equal f r) acc (add-to-set-equal "constants" acc))))
    (if (equal final (if notp (list 'not f) f))
        acc
      (add-to-set-equal "negation" acc))))

(defun tt-lits-steps (lits acc)
  (cond ((endp lits) acc)
        (t (tt-lits-steps (cdr lits) (tt-lit-steps (car lits) acc)))))

(defun tt-clauses-steps (clauses acc)
  (cond ((endp clauses) acc)
        (t (tt-clauses-steps
            (cdr clauses)
            (let* ((c (car clauses))
                   (acc (tt-lits-steps c acc))
                   (ls (tt-lits1 c)))
              (cond ((eq ls :true) (add-to-set-equal "true-clause" acc))
                    (t (let ((acc (if (< (len ls) (len c))
                                      (add-to-set-equal "false-literal" acc)
                                    acc)))
                         (if (equal (tt-drop-implied ls) ls)
                             acc
                           (add-to-set-equal "implied-test" acc))))))))))

(defun tt-steps (clauses)
  (let* ((acc (tt-clauses-steps clauses nil))
         (n1 (tt-norm1 clauses))
         (n2 (tt-split n1 nil nil))
         (acc (if (equal n2 n1) acc (add-to-set-equal "o-p-first" acc)))
         (n3 (remove-duplicates-equal-from-end n2 nil)))
    (if (equal n3 n2) acc (add-to-set-equal "repeat" acc))))

(defun tt-step-names (steps)
  (cond ((endp steps) "-")
        ((endp (cdr steps)) (car steps))
        (t (concatenate 'string (car steps) "," (tt-step-names (cdr steps))))))

; The note of a definition that agrees in the normal form: the steps that
; changed the checker's clauses and those that changed ACL2's.
(defun tt-steps-note (mine theirs)
  (concatenate 'string "checker=" (tt-step-names (merge-sort-lexorder (tt-steps mine)))
               " acl2=" (tt-step-names (merge-sort-lexorder (tt-steps theirs)))))

;;; 5. The checker's clauses as ACL2 terms

; MAP associates the text of each symbol of ACL2's data for a definition
; with the symbol.  A symbol of the checker's clauses that is not among
; them is :MISSING.

(defun tt-syms (x map)
  (cond ((consp x) (tt-syms (cdr x) (tt-syms (car x) map)))
        ((and (symbolp x) x (not (eq x t)))
         (let ((s (tt-text x)))
           (if (hons-get s map) map (hons-acons s x map))))
        (t map)))

(defun tt-from-reader (x map)
  (cond ((consp x) (cons (tt-from-reader (car x) map)
                         (tt-from-reader (cdr x) map)))
        ((or (eq x nil) (eq x t)) x)
        ((symbolp x) (let ((p (hons-get (symbol-name x) map)))
                       (if p (cdr p) :missing)))
        (t x)))

;;; 6. The comparison

(defun tt-fn-map (fns map)
  (cond ((endp fns) map)
        (t (tt-fn-map (cdr fns)
                      (hons-acons (tt-text (car fns)) (car fns) map)))))

(defun tt-acl2-texts (clauses)
  (cond ((endp clauses) nil)
        (t (cons (concatenate 'string "    " (bm-line "clause" (car clauses)))
                 (tt-acl2-texts (cdr clauses))))))

; ACL2's clauses with the relation REL read as O< and the domain MP as
; O-P, for a definition measured with another relation: a clause of one
; literal (MP M) becomes ((o-p M)), and the last literal (REL A B) of any
; other clause becomes (o< A B).  REL and MP may stand in the tests too,
; and there they are left as they are.
(defun tt-rename (clauses rel mp)
  (cond ((endp clauses) nil)
        (t (let* ((c (car clauses))
                  (last (car (last c))))
             (cons (cond ((and (null (cdr c)) (consp (car c)) (eq (caar c) mp))
                          (list (cons 'o-p (cdar c))))
                         ((and (consp last) (eq (car last) rel))
                          (append (butlast c 1) (list (cons 'o< (cdr last)))))
                         (t c))
                   (tt-rename (cdr clauses) rel mp))))))

(defun tt-call-clauses (clauses)
  (cond ((endp clauses) nil)
        ((tt-o-p-clause-p (car clauses)) (tt-call-clauses (cdr clauses)))
        (t (cons (car clauses) (tt-call-clauses (cdr clauses))))))

; The comparison of the record REC (N F RESULT CLAUSES) of a define line:
; (mv CLASS NOTE MINE THEIRS), CLASS a string, NOTE a string or NIL, and
; the two sides in normal form when they do not agree.
(defun tt-compare (rec fnmap wrld)
  (let* ((result (caddr rec))
         (clauses (cadddr rec))
         (fn (cdr (hons-get (cadr rec) fnmap)))
         (names (and fn (getpropc fn 'recursivep nil wrld)))
         (just (and fn (getpropc fn 'justification nil wrld)))
         (rel (and just (access justification just :rel)))
         (mp (and just (access justification just :mp))))
    (cond
     ((null fn) (mv "no-justification" nil nil nil))
     ((eq (car (measure-alist? names wrld)) :failed)
      (mv "measure-unknown" nil nil nil))
     ((getpropc fn 'loop$-recursion nil wrld) (mv "loop$" nil nil nil))
     ((stringp result) (mv "refused" result nil nil))
     ((eq clauses :unreadable) (mv "unreadable" nil nil nil))
     ((and (eq rel 'o<) (equal result clauses)) (mv "agree" nil nil nil))
     (t
      (let* ((theirs (tt-acl2-clauses names wrld))
             (map (tt-syms (list theirs
                                 (get-unnormalized-bodies names wrld)
                                 (tt-measures names wrld)
                                 '(not o< o-p))
                           nil))
             (mine (tt-from-reader result map)))
        (prog2$
         (fast-alist-free map)
         (cond
          ((not (eq rel 'o<))
           (mv "relation"
               (if (equal (tt-call-clauses (tt-norm mine))
                          (tt-call-clauses (tt-norm (tt-rename theirs rel mp))))
                   "calls-agree"
                 "calls-differ")
               (tt-norm mine) (tt-norm theirs)))
          ((equal (tt-norm mine) (tt-norm theirs))
           (mv "agree-tidy" (tt-steps-note mine theirs) nil nil))
          ((equal (tt-norm mine) (tt-norm (tt-acl2-raw names wrld)))
           (mv "agree-repeats" (tt-steps-note mine (tt-acl2-raw names wrld))
               (tt-norm mine) (tt-norm theirs)))
          ((let ((m (tt-norm mine)) (th (tt-norm theirs)))
             (and (subsetp-equal m th) (subsetp-equal th m)))
           (mv "agree-order" nil (tt-norm mine) (tt-norm theirs)))
          (t (mv "differ" nil (tt-norm mine) (tt-norm theirs))))))))))

(defun tt-concat (strings)
  (if (endp strings)
      ""
    (concatenate 'string (car strings) (tt-concat (cdr strings)))))

(defun tt-line (strings chan state)
  (pprogn (princ$ (tt-concat strings) chan state)
          (newline chan state)))

; Writes a line for each record of RECS, from the input SET, and returns
; the functions of the definitions compared, consed onto DONE.
(defun tt-report (set recs fnmap done wrld chan state)
  (cond
   ((endp recs) (mv done state))
   (t
    (let ((rec (car recs)))
      (if (symbolp (cadr rec))
          (pprogn
           (tt-line (list (string-downcase (symbol-name (cadr rec))) " " set " "
                          (tt-text (car rec))
                          (if (caddr rec) (concatenate 'string " " (caddr rec)) ""))
                    chan state)
           (tt-report set (cdr recs) fnmap done wrld chan state))
        (mv-let (class note mine theirs) (tt-compare rec fnmap wrld)
          (let* ((fn (cdr (hons-get (cadr rec) fnmap)))
                 (names (and fn (getpropc fn 'recursivep nil wrld))))
            (pprogn
             (tt-line (list "define " set " " (tt-text (car rec)) " " (cadr rec)
                            " " class " " (tt-text (len names)) " "
                            (tt-text (if (consp (caddr rec)) (len (caddr rec)) 0))
                            (if note (concatenate 'string " " note) ""))
                      chan state)
             (if (or mine theirs)
                 (pprogn (tt-line (list "  the checker, in normal form:") chan state)
                         (tt-write-lines (tt-acl2-texts mine) chan state)
                         (tt-line (list "  ACL2, in normal form:") chan state)
                         (tt-write-lines (tt-acl2-texts theirs) chan state))
               state)
             (tt-report set (cdr recs) fnmap (append names done) wrld chan
                        state)))))))))

; A line for each function of FNS that is not among DONE, the functions of
; the definitions compared: a function with a justification whose
; definition has no record, with "loop$" when its recursion is in the
; quoted lambda of a loop$ (EDGE-CASES.md, entry 6.14), and "subversive"
; when ACL2 holds its recursion as subversive, so that its equation is
; part of the constraint of an encapsulate (entry 6.6).
(defun tt-uncovered (fns done chan state wrld)
  (cond ((endp fns) state)
        ((member-eq (car fns) done) (tt-uncovered (cdr fns) done chan state wrld))
        (t (pprogn (tt-line (list "uncovered " (tt-text (car fns))
                                  (cond ((getpropc (car fns) 'loop$-recursion nil wrld)
                                         " loop$")
                                        ((access justification
                                                 (getpropc (car fns) 'justification nil wrld)
                                                 :subversive-p)
                                         " subversive")
                                        (t "")))
                            chan state)
                   (tt-uncovered (cdr fns) done chan state wrld)))))

; The line (measure F M REL) for each function of FNS, from its
; justification, to compare with the prover's aids.
(defun tt-measure-lines (fns wrld)
  (cond ((endp fns) nil)
        (t (let ((just (getpropc (car fns) 'justification nil wrld)))
             (cons (bm-line "measure"
                            (list (car fns)
                                  (access justification just :measure)
                                  (access justification just :rel)))
                   (tt-measure-lines (cdr fns) wrld))))))

; The comparison for the functions with a justification in the part of
; the world (w state) between HI and its tail OLD: for the library, those
; of the ground theory and of build/export/library.statements, when BOOK is
; NIL; for a book, those of the statements BOOK.  It writes OUT.txt, a
; line for each definition, and OUT.measures.
(defun tt-run (hi old book out state)
  (let* ((wrld (w state))
         (fns (tt-justified hi old nil))
         (given (tt-given fns nil nil wrld))
         (fnmap (tt-fn-map fns nil)))
    (mv-let (ground state) (tt-file-string "spec/ground.txt" state)
      (mv-let (library state)
        (tt-file-string "build/export/library.statements" state)
        (mv-let (stmts state)
          (if book (tt-file-string book state) (mv nil state))
          (let ((recs (boymoo::all-records ground library stmts given)))
            (mv-let (chan state)
              (open-output-channel (concatenate 'string out ".txt")
                                   :character state)
              (if (stringp recs)
                  (pprogn (tt-line (list "error " recs) chan state)
                          (close-output-channel chan state)
                          (value nil))
                (mv-let (done state)
                  (tt-report "ground" (car recs) fnmap nil wrld chan state)
                  (mv-let (done state)
                    (tt-report "library" (cadr recs) fnmap done wrld chan state)
                    (mv-let (done state)
                      (tt-report "book" (caddr recs) fnmap done wrld chan state)
                      (pprogn
                       (tt-uncovered fns done chan state wrld)
                       (tt-line (list "functions " (tt-text (len fns))) chan state)
                       (close-output-channel chan state)
                       (tt-write-file (tt-measure-lines fns wrld)
                                      (concatenate 'string out ".measures")
                                      state)
                       (value t)))))))))))))
