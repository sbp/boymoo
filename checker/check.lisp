; Boymoo, the checker: the order of checking and the verdict
; (spec/formats.md, sections 5 to 9).
;
; (check-four GROUND LIBRARY STATEMENTS PROOFS LIBRARY-PROOFS) takes the
; bytes of spec/ground.txt and the four inputs as strings. It returns a
; list of the verdict without its line feed (spec/formats.md, section 9)
; and an explanation that is empty if every line was admitted.
; (check GROUND LIBRARY STATEMENTS PROOFS) uses empty library proofs.

(in-package "BOYMOO")

(include-book "admit")

; ---------------------------------------------------------------------------
; Words

(defun strings-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (stringp (car xs)) (strings-p (cdr xs)))
    (equal xs nil)))

(defun word-table (strings keywords)
  (declare (xargs :guard (and (strings-p strings)
                              (true-listp keywords))))
  (if (consp strings)
      (cons (cons (coerce (car strings) 'list) (car keywords))
            (word-table (cdr strings) (cdr keywords)))
    nil))

(defconst *ground-words*
  (word-table '("package" "specials" "primitive" "define" "clause")
              '(:package :specials :primitive :define :clause)))

(defconst *statement-words*
  (word-table '("package" "hidden-package" "define" "constrain" "choose"
                "theorem" "axiom" "reserve")
              '(:package :hidden-package :define :constrain :choose
                :theorem :axiom :reserve)))

(defconst *proof-words*
  (word-table '("define" "lemma" "choose" "theorem" "measure" "witness" "skip"
                "fact" "instantiate" "subsume" "cut" "substitute" "beta"
                "compute" "induct" "qed")
              '(:define :lemma :choose :theorem :measure :witness :skip
                :fact :instantiate :subsume :cut :substitute :beta
                :compute :induct :qed)))

(defconst *step-words*
  '(:fact :instantiate :subsume :cut :substitute :beta :compute :induct))

(defconst *unreadable*
  "not a line of the format, a word that may not stand here, or a symbol that does not exist")

; ---------------------------------------------------------------------------
; The ground theory (spec/logic.md, section 3)

(defun set-sfacts (v w)
  (declare (xargs :guard (true-listp w)))
  (make-world (w-pkgs w) (w-names w) v (w-specials w) (w-counts w) (w-acl2 w)))

(defun set-specials (v w)
  (declare (xargs :guard (true-listp w)))
  (make-world (w-pkgs w) (w-names w) (w-sfacts w) v (w-counts w) (w-acl2 w)))

(defun set-acl2 (v w)
  (declare (xargs :guard (true-listp w)))
  (make-world (w-pkgs w) (w-names w) (w-sfacts w) (w-specials w) (w-counts w) v))

(defun specials-trie (l node)
  (declare (xargs :guard (symbol-listp l)))
  (if (consp l)
      (specials-trie (cdr l) (trie-put (sym-text (car l)) t node))
    node))

; Before the ground theory, the package COMMON-LISP, which its first line
; names, and the names T and NIL.
(defun initial-world ()
  (declare (xargs :guard t
                  :verify-guards nil))
  (put-entry t (list nil nil nil)
             (put-entry nil (list nil nil nil)
                        (declare-package *cl-chars* nil nil nil
                                         (make-world nil nil nil nil
                                                     (list 0 0 0 0) nil)))))

(defun guard-ground-line-p (line)
  (declare (xargs :guard t))
  (and (true-listp line)
       (let ((data (cdr line)))
         (case (car line)
           (:package (and (stringp (car data)) (symbol-listp (cadr data))))
           (:specials (symbol-listp (car data)))
           (:primitive (and (symbolp (car data)) (natp (cadr data))))
           (:define (and (true-listp (cadr data)) (symbolp (car (cadr data)))))
           (:clause (or (symbolp (car data)) (stringp (car data))))
           (otherwise t)))))

; The ground theory is part of the specification and is taken as it
; stands.  Its packages bring the names of their rules into use, all but
; COMMON-LISP, for which ACL2 has no axiom (spec/logic.md, section 4).
(defun ground-line (line w)
  (declare (xargs :guard
                  (and (guard-ground-line-p line)
                       (guard-world-p w))
                  :verify-guards nil))
  (let ((word (car line))
        (data (cdr line)))
    (cond
     ((equal word :package)
      (let* ((string (car data))
             (name (coerce string 'list))
             (imports (car (cdr data)))
             (w (declare-package name imports nil nil w))
             (w (if (equal name *acl2-chars*)
                    (set-acl2 (import-trie imports (symbol-names imports) nil) w)
                  w)))
        (if (equal name *cl-chars*)
            w
          (put-entry (package-rule-name name w)
                     (list nil (package-fact string imports) nil)
                     w))))
     ((equal word :specials)
      (set-specials (specials-trie (car data) nil) w))
     ((equal word :primitive)
      (put-entry (car data) (list (car (cdr data)) nil nil) w))
     ((equal word :define)
      (let ((d (car (cdr data))))
        (put-entry (car d)
                   (list (len (car (cdr d)))
                         (equation (car d) (car (cdr d)) (car (cdr (cdr d))))
                         nil)
                   w)))
     ((equal word :clause)
      (let ((name (car data))
            (fact (cons (cdr data) (sizes (cdr data)))))
        (if (stringp name)
            (set-sfacts (cons (cons name fact) (w-sfacts w)) w)
          (put-entry name (list nil fact nil) w))))
     (t w))))

(defun load-ground (lines w)
  (declare (xargs :guard (guard-world-p w)
                  :verify-guards nil))
  (if (consp lines)
      (let ((line (parse-line (car lines) *ground-words* (w-pkgs w))))
        (if (and line (guard-ground-line-p line))
            (load-ground (cdr lines) (ground-line line w))
          :bad))
    w))

; ---------------------------------------------------------------------------
; Rejections

(defun rejection (input n reason)
  (declare (xargs :guard t))
  (list :rejected input n reason))

(defun rejected-p (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :rejected)))

; ---------------------------------------------------------------------------
; The proofs
;
; While a statement with obligations waits for its entry, the checker reads
; the proofs one line at a time, in a context:
;
;   (:ENTRY P)             a define, lemma or choose entry comes next, or
;                          the entry of the pending statement P;
;   (:DEFINE-ENTRY D P)    the measure or the skip of the define entry D,
;                          and then P again;
;   (:PROOF GOALS FIN BACK STEPS COUNT TOTAL)
;                          a step or a qed line of the proof of the first
;                          clause of GOALS.  When all are proved, FIN, a
;                          pending statement or entry, is finished and the
;                          context is BACK, NIL if FIN is the statement.
;                          STEPS are the conclusions so far, the latest
;                          first, COUNT their number and TOTAL the sum of
;                          their sizes.
;
; A pending statement or entry is (:THEOREM NAME TERM), (:DEFINE RULERS
; DEFS), (:CONSTRAIN FNS FORMULAS) or (:LEMMA NAME FACT).  Each function
; below gives (CONTEXT . W), or a string if the line fails.

(defun guard-pending-p (p)
  (declare (xargs :guard t))
  (and (true-listp p)
       (case (car p)
         (:theorem (symbolp (cadr p)))
         (:define (guard-definition-list-p (caddr p)))
         (:constrain (and (guard-function-arities-p (cadr p))
                          (formulas-shape-p (caddr p))
                          (symbol-listp (formula-names (caddr p)))))
         (:lemma (and (symbolp (cadr p)) (guard-sized-clause-p (caddr p))))
         (otherwise nil))))

; A proof in progress has proper goal and clause lists and numeric
; counters, and the context to resume is itself well shaped.
(defun guard-proof-context-p (ctx)
  (declare (xargs :guard t :measure (acl2-count ctx)))
  (and (true-listp ctx)
       (if (consp ctx)
           (case (car ctx)
             (:entry (guard-pending-p (cadr ctx)))
             (:define-entry (and (guard-pending-p (cadr ctx))
                                 (guard-pending-p (caddr ctx))))
             (:proof (let ((steps-and-counts (cddddr ctx)))
                       (and (true-listp (cadr ctx))
                            (guard-pending-p (caddr ctx))
                            (guard-proof-context-p (cadddr ctx))
                            (proof-clauses-p (car steps-and-counts))
                            (natp (cadr steps-and-counts))
                            (integerp (caddr steps-and-counts)))))
             (otherwise nil))
         t)))

(defun pending-name (p)
  (declare (xargs :guard
                  (and (true-listp p)
                       (cond ((equal (car p) :define)
                              (defs-shape-p (caddr p)))
                             ((equal (car p) :constrain)
                              (let ((fns (cadr p)))
                                (and (or (consp fns) (equal fns nil))
                                     (or (consp (car fns)) (equal (car fns) nil)))))
                             (t t)))))
  (let ((kind (car p)))
    (cond ((equal kind :define) (car (car (car (cdr (cdr p))))))
          ((equal kind :constrain) (car (car (car (cdr p)))))
          (t (car (cdr p))))))

; The facts of P become facts, and its functions are in use.
(defun finish (p w)
  (declare (xargs :guard (and (guard-pending-p p)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((kind (car p)))
    (cond ((equal kind :theorem)
           (add-facts (list (car (cdr p))) (list (unit-fact (car (cdr (cdr p))))) w))
          ((equal kind :define)
           (add-definitions (car (cdr (cdr p))) w))
          ((equal kind :constrain)
           (add-constraint (car (cdr p)) (car (cdr (cdr p))) w))
          ((equal kind :lemma)
           (add-facts (list (car (cdr p))) (list (car (cdr (cdr p)))) w))
          (t w))))

(defun give-statement (p w)
  (declare (xargs :guard (and (guard-pending-p p) (guard-world-p w))
                  :verify-guards nil))
  (count-one (if (equal (car p) :theorem) 3 2) (finish p w)))

; Admit a single line, taking library obligations as given.
(defun admit (line input w)
  (declare (xargs :guard (and (true-listp line) (guard-world-p w))
                  :verify-guards nil))
  (let ((r (prepare-statement line input w)))
    (if (and (equal input :library) (consp r) (cdr r))
        (cons (give-statement (cdr r) (car r)) nil)
      r)))

(defun start-proofs (goals p back w)
  (declare (xargs :guard (true-listp w)))
  (cons (list :proof goals p back nil 0 0) w))

; (measure F M1 ... Mk), for the pending definition P.
(defun measure-entry (data p back w)
  (declare (xargs :guard (and (guard-pending-p p)
                              (equal (car p) :define)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((defs (car (cdr (cdr p)))))
    (if (and (consp data)
             (equal (car data) (pending-name p))
             (measures-p (cdr data) defs w))
        (let ((obligations (termination-obligations defs (cdr data) (car (cdr p)))))
          (if (equal obligations :over)
              "the obligations of termination pass the budget"
            (start-proofs obligations p back (enable-fns (def-arities defs) w))))
      "a measure entry that does not fit the definition")))

; (witness F G1 ... Gk), for the pending constraint P.
(defun witness-entry (data p back w)
  (declare (xargs :guard (and (guard-pending-p p)
                              (equal (car p) :constrain)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((fns (car (cdr p)))
        (formulas (car (cdr (cdr p)))))
    (if (and (consp data)
             (equal (car data) (pending-name p))
             (witnesses-p (cdr data) fns w))
        (start-proofs (witness-obligations (formula-terms formulas)
                                           (pair-up (def-names fns) (cdr data)))
                      p back w)
      "a witness entry that does not fit the constraint")))

; The entry of the pending statement or define entry P. GIVE-ON-SKIP
; holds for a statement of the library.
(defun pending-entry (line p back give-on-skip w)
  (declare (xargs :guard (and (true-listp line)
                              (guard-pending-p p)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((word (car line))
        (data (cdr line))
        (kind (car p)))
    (cond ((equal word :skip)
           (if (and (consp data) (equal (cdr data) nil)
                    (equal (car data) (pending-name p)))
               (cons back (if give-on-skip
                              (give-statement p w)
                            (count-one 0 (finish p w))))
             "a skip entry that is not the entry of the statement"))
          ((and (equal word :theorem) (equal kind :theorem))
           (if (and (consp data) (equal (cdr data) nil)
                    (equal (car data) (pending-name p)))
               (start-proofs (list (list (car (cdr (cdr p))))) p back w)
             "a theorem entry that is not the entry of the statement"))
          ((and (equal word :measure) (equal kind :define))
           (measure-entry data p back w))
          ((and (equal word :witness) (equal kind :constrain))
           (witness-entry data p back w))
          (t "a line that is not the entry of the statement"))))

; (lemma NAME L1 ... Ln), while P is pending.
(defun lemma-head (data p w)
  (declare (xargs :guard (guard-world-p w)
                  :verify-guards nil))
  (if (and (consp data) (consp (cdr data))
           (new-name-p (car data) w)
           (terms-p (cdr data) :any nil w))
      (let ((lits (cdr data)))
        (start-proofs (list lits)
                      (list :lemma (car data) (cons lits (sizes lits)))
                      (list :entry p)
                      (put-entry (car data) (list nil nil nil) w)))
    "a lemma that may not be admitted"))

(defun entry-head (line p library w)
  (declare (xargs :guard (and (true-listp line)
                              (guard-pending-p p)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((word (car line)))
    (cond ((or (equal word :define) (equal word :choose))
           (let ((r (prepare-statement line :proofs w)))
             (if (stringp r)
                 r
               (cons (if (cdr r)
                         (list :define-entry (cdr r) p)
                       (list :entry p))
                     (car r)))))
          ((equal word :lemma) (lemma-head (cdr line) p w))
          (t (pending-entry line p nil library w)))))

(defun proof-step (line ctx w)
  (declare (xargs :guard (and (true-listp line)
                              (guard-proof-context-p ctx)
                              (equal (car ctx) :proof)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((word (car line))
        (data (cdr line))
        (goals (car (cdr ctx)))
        (p (car (cdr (cdr ctx))))
        (back (car (cdr (cdr (cdr ctx)))))
        (steps (car (cdr (cdr (cdr (cdr ctx))))))
        (count (car (cdr (cdr (cdr (cdr (cdr ctx)))))))
        (total (car (cdr (cdr (cdr (cdr (cdr (cdr ctx)))))))))
    (if (equal word :qed)
        (if (and (equal data nil)
                 (consp steps)
                 (equal (car (car steps)) (car goals)))
            (if (consp (cdr goals))
                (start-proofs (cdr goals) p back w)
              (cons back (finish p w)))
          "a qed line that does not end a proof of its clause")
      (if (member-p word *step-words*)
          (let ((c (check-step word data steps count (- *budget* total) w)))
            (if c
                (cons (list :proof goals p back (cons c steps) (+ 1 count)
                            (+ total (sum (cdr c))))
                      w)
              "a step that does not follow, or passes the budget"))
        "a head line inside a proof"))))

(defun proof-line (line ctx library w)
  (declare (xargs :guard (and (true-listp line)
                              (guard-proof-context-p ctx)
                              (consp ctx)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((kind (car ctx)))
    (cond ((equal kind :entry) (entry-head line (car (cdr ctx)) library w))
          ((equal kind :define-entry)
           (if (or (equal (car line) :measure) (equal (car line) :skip))
               (pending-entry line (car (cdr ctx))
                              (list :entry (car (cdr (cdr ctx)))) nil w)
             "a line that is not the measure or the skip of the define entry"))
          (t (proof-step line ctx w)))))

; ---------------------------------------------------------------------------
; The lines of an input, read from its string.

; The K characters of the string S before the position J, followed by ACC.
(defun string-chars (s j k acc)
  (declare (xargs :guard (and (stringp s) (natp j) (natp k) (<= k j)
                              (<= j (length s)) (character-listp acc))
                  :verify-guards nil
                  :measure (acl2-count k)))
  (if (zp k)
      acc
    (string-chars s (+ -1 j) (+ -1 k) (cons (char s (+ -1 j)) acc))))

; The lines of the string S from the position I on, as LINES-OF gives
; them, but each written (S START . END), for the characters of S from
; START up to END: each line with its line feed, and last, if S does not
; end with a line feed, what follows the last line feed.  START is where
; the line that holds I begins, K is the number of characters of S from I
; on, and ACC holds the lines before START, the last first.  Only CHAR
; reads S, and every line shares it, so that an input is held once, as its
; string, and RUN makes a line a list of characters only when it reads
; that line (LINE-CHARS).
(defun string-lines (s start i k acc)
  (declare (xargs :guard (and (stringp s) (natp start) (natp i) (natp k)
                              (<= start i) (equal (+ i k) (length s))
                              (true-listp acc))
                  :verify-guards nil
                  :measure (acl2-count k)))
  (if (zp k)
      (rev (if (< start i) (cons (cons s (cons start i)) acc) acc))
    (if (equal (char s i) #\Newline)
        (string-lines s (+ 1 i) (+ 1 i) (+ -1 k)
                      (cons (cons s (cons start (+ 1 i))) acc))
      (string-lines s start (+ 1 i) (+ -1 k) acc))))

; The characters of a line: of a line (S START . END) of STRING-LINES,
; those of S from START up to END; and anything else is taken as the list
; of its characters already.
(defun line-chars (x)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp x) (stringp (car x)) (consp (cdr x))
           (natp (car (cdr x))) (natp (cdr (cdr x)))
           (<= (car (cdr x)) (cdr (cdr x)))
           (<= (cdr (cdr x)) (length (car x))))
      (string-chars (car x) (cdr (cdr x)) (- (cdr (cdr x)) (car (cdr x))) nil)
    x))

(defun text-lines (text)
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (string-lines text 0 0 (length text) nil))

; ---------------------------------------------------------------------------
; One pair of statements and proofs (spec/formats.md, section 7).
; SN and PN count the lines read from each input so far.

(defun run (slines sn plines pn ctx input w)
  (declare (xargs :guard (and (natp sn)
                              (natp pn)
                              (guard-proof-context-p ctx)
                              (guard-world-p w))
                  :verify-guards nil
                  :measure (+ (len slines) (len plines))
                  :hints (("Goal" :in-theory (disable admit parse-line
                                                    prepare-statement proof-line)))))
  (let* ((library (equal input :library))
         (sname (if library "library" "statements"))
         (pname (if library "library-proofs" "proofs")))
    (if (equal ctx nil)
        (if (consp slines)
            (let* ((text (car slines))
                   (line (parse-line (line-chars text) *statement-words* (w-pkgs w))))
              (if line
                  (let ((r (if (and library (not (consp plines)))
                               (admit line input w)
                             (prepare-statement line input w))))
                    (if (stringp r)
                        (rejection sname (+ 1 sn) r)
                      (run (cdr slines) (+ 1 sn) plines pn
                           (if (cdr r) (list :entry (cdr r)) nil) input (car r))))
                (rejection sname (+ 1 sn) *unreadable*)))
          (if (consp plines)
              (rejection pname (+ 1 pn) "a line of the proofs after the statements are done")
            w))
      (if (consp plines)
          (let* ((text (car plines))
                 (line (parse-line (line-chars text) *proof-words* (w-pkgs w))))
            (if line
                (let ((r (proof-line line ctx library w)))
                  (if (stringp r)
                      (rejection pname (+ 1 pn) r)
                    (run slines sn (cdr plines) (+ 1 pn) (car r) input (cdr r))))
              (rejection pname (+ 1 pn) *unreadable*)))
        (rejection sname sn "the proofs end before those of the statement")))))

(defun check-library (lines n w)
  (declare (xargs :guard (and (natp n) (guard-world-p w))
                  :verify-guards nil))
  (run lines n nil 0 nil :library w))

; ---------------------------------------------------------------------------
; The verdict (spec/formats.md, section 9)

(defun verdict (w)
  (declare (xargs :guard (and (true-listp w) (true-listp (w-counts w)))
                  :verify-guards nil))
  (let* ((c (w-counts w))
         (s (car c))
         (a (car (cdr c)))
         (d (car (cdr (cdr c))))
         (f (car (cdr (cdr (cdr c))))))
    (if (and (equal s 0) (equal a 0) (equal d 0) (equal f 0))
        "accepted"
      (coerce (app (coerce "provisional skipped " 'list)
                   (app (decimal s)
                        (app (coerce " assumed " 'list)
                             (app (decimal a)
                                  (app (coerce " given-definitions " 'list)
                                       (app (decimal d)
                                            (app (coerce " given-facts " 'list)
                                                 (decimal f))))))))
              'string))))

(defun rejection-verdict (r)
  (declare (xargs :guard (and (true-listp r) (stringp (car (cdr r))))
                  :verify-guards nil))
  (list (coerce (app (coerce "rejected " 'list)
                     (app (coerce (car (cdr r)) 'list)
                          (cons #\Space (decimal (car (cdr (cdr r)))))))
                'string)
        (car (cdr (cdr (cdr r))))))

(defun lines-of (string)
  (declare (xargs :guard (stringp string)))
  (split-lines (coerce string 'list) nil nil))

(defun check-four (ground library statements proofs library-proofs)
  (declare (xargs :guard (and (stringp ground) (stringp library)
                             (stringp statements) (stringp proofs)
                             (stringp library-proofs))
                  :verify-guards nil))
  (let ((g (load-ground (lines-of ground) (initial-world))))
    (if (equal g :bad)
        (list "the ground theory could not be read" "")
      (let ((w (run (text-lines library) 0 (text-lines library-proofs) 0 nil :library g)))
        (if (rejected-p w)
            (rejection-verdict w)
          (let ((w (run (text-lines statements) 0 (text-lines proofs) 0 nil :statements w)))
            (if (rejected-p w)
                (rejection-verdict w)
              (list (verdict w) ""))))))))

(defun check (ground library statements proofs)
  (declare (xargs :guard (and (stringp ground) (stringp library)
                             (stringp statements) (stringp proofs))
                  :verify-guards nil))
  (check-four ground library statements proofs ""))
