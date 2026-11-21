; Boymoo, the checker: the order of checking and the verdict
; (spec/formats.md, sections 5 to 9).
;
; (check GROUND LIBRARY STATEMENTS PROOFS), on four strings, the bytes of
; spec/ground.txt and of the three inputs, gives a list of two strings: the
; verdict, the line of spec/formats.md, section 9, without its line feed;
; and a few words on what failed, empty if nothing did.

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
  (word-table '("define" "lemma" "theorem" "measure" "witness" "skip"
                "fact" "instantiate" "subsume" "cut" "substitute" "beta"
                "compute" "induct" "qed")
              '(:define :lemma :theorem :measure :witness :skip
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
; The library (spec/formats.md, section 7, step 2)

(defun check-library (lines n w)
  (declare (xargs :guard (and (natp n)
                              (guard-world-p w))
                  :verify-guards nil))
  (if (consp lines)
      (let ((line (parse-line (car lines) *statement-words* (w-pkgs w))))
        (if line
            (let ((r (admit line :library w)))
              (if (stringp r)
                  (rejection "library" (+ 1 n) r)
                (check-library (cdr lines) (+ 1 n) (car r))))
          (rejection "library" (+ 1 n) *unreadable*)))
    w))

; ---------------------------------------------------------------------------
; The proofs
;
; While a statement with obligations waits for its entry, the checker reads
; the proofs one line at a time, in a context:
;
;   (:ENTRY P)             a head line comes next: a define or a lemma entry,
;                          or the entry of the pending statement P;
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

; The entry of the pending statement or define entry P.
(defun pending-entry (line p back w)
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
               (cons back (count-one 0 (finish p w)))
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

(defun entry-head (line p w)
  (declare (xargs :guard (and (true-listp line)
                              (guard-pending-p p)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((word (car line)))
    (cond ((equal word :define)
           (let ((r (admit line :proofs w)))
             (if (stringp r)
                 r
               (cons (if (cdr r)
                         (list :define-entry (cdr r) p)
                       (list :entry p))
                     (car r)))))
          ((equal word :lemma) (lemma-head (cdr line) p w))
          (t (pending-entry line p nil w)))))

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

(defun proof-line (line ctx w)
  (declare (xargs :guard (and (true-listp line)
                              (guard-proof-context-p ctx)
                              (consp ctx)
                              (guard-world-p w))
                  :verify-guards nil))
  (let ((kind (car ctx)))
    (cond ((equal kind :entry) (entry-head line (car (cdr ctx)) w))
          ((equal kind :define-entry)
           (if (or (equal (car line) :measure) (equal (car line) :skip))
               (pending-entry line (car (cdr ctx))
                              (list :entry (car (cdr (cdr ctx)))) w)
             "a line that is not the measure or the skip of the define entry"))
          (t (proof-step line ctx w)))))

; ---------------------------------------------------------------------------
; The statements, with the proofs (spec/formats.md, section 7, steps 3 and
; 4).  SN and PN are the numbers of the lines of each input read so far.

(defun run (slines sn plines pn ctx w)
  (declare (xargs :guard (and (natp sn)
                              (natp pn)
                              (guard-proof-context-p ctx)
                              (guard-world-p w))
                  :verify-guards nil
                  :measure (+ (len slines) (len plines))))
  (if (equal ctx nil)
      (if (consp slines)
          (let ((line (parse-line (car slines) *statement-words* (w-pkgs w))))
            (if line
                (let ((r (admit line :statements w)))
                  (if (stringp r)
                      (rejection "statements" (+ 1 sn) r)
                    (run (cdr slines) (+ 1 sn) plines pn
                         (if (cdr r) (list :entry (cdr r)) nil)
                         (car r))))
              (rejection "statements" (+ 1 sn) *unreadable*)))
        (if (consp plines)
            (rejection "proofs" (+ 1 pn) "a line of the proofs after the statements are done")
          w))
    (if (consp plines)
        (let ((line (parse-line (car plines) *proof-words* (w-pkgs w))))
          (if line
              (let ((r (proof-line line ctx w)))
                (if (stringp r)
                    (rejection "proofs" (+ 1 pn) r)
                  (run slines sn (cdr plines) (+ 1 pn) (car r) (cdr r))))
            (rejection "proofs" (+ 1 pn) *unreadable*)))
      (rejection "statements" sn "the proofs end before those of the statement"))))

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

(defun check (ground library statements proofs)
  (declare (xargs :guard (and (stringp ground) (stringp library)
                             (stringp statements) (stringp proofs))
                  :verify-guards nil))
  (let ((g (load-ground (lines-of ground) (initial-world))))
    (if (equal g :bad)
        (list "the ground theory could not be read" "")
      (let ((w (check-library (lines-of library) 0 g)))
        (if (rejected-p w)
            (rejection-verdict w)
          (let ((w (run (lines-of statements) 0 (lines-of proofs) 0 nil w)))
            (if (rejected-p w)
                (rejection-verdict w)
              (list (verdict w) ""))))))))
