; This script writes build/edge.txt: what ACL2 itself says on each entry
; of EDGE-CASES.md.  checks/run.sh runs it from the root of the
; repository, after it has certified build/edge-hidden and copied
; build/edge-false, and compares the result, byte for byte, with
; checks/expected/edge.txt.
;
; Every label begins with the number of the entry of EDGE-CASES.md that
; it confirms.  The lines:
;   (accepted "what")    a form that ACL2 accepts
;   (refused "what")     a form that ACL2 refuses
;   (top "what" V)       ACL2's value of a form, evaluated as at its top
;                        level, with attachments in force and with the
;                        guard checking that the label names
;   (no-top "what")      the same, where ACL2 gives no value
;   (stored "what" V)    something that ACL2 holds in its world
;   (read "TEXT" V)      the object ACL2's reader makes of TEXT
;   (no-read "TEXT")     a text ACL2's reader refuses
;   (value TERM V)       ACL2's value of a call on constants, with guard
;                        checking off; (no-value TERM) if it gives none
;   (count "what" N)     a count over the world ACL2 starts with
;
; A form that may end in an error of the Lisp under ACL2, rather than an
; error of ACL2, is evaluated inside a nested LD of a file that this
; script writes into build/, so that the error ends only that LD.

(in-package "ACL2")

(make-event
 (list 'defconst '*bm-start* (max-absolute-event-number (w state))))

(ld "checks/canon.lsp")

(include-book "build/edge-hidden")

(include-book "projects/apply/top" :dir :system)

(program)

; The value of a form that TRANS-EVAL returns: its only value, or the
; first of several.

(defun bm-single (val)
  (if (cdr (car val)) (car (cdr val)) (cdr val)))

; Whether TRANS-EVAL, or the event or command it evaluated, failed.

(defun bm-triple-erp (erp val)
  (or erp
      (and (equal (car val) '(nil nil state))
           (car (cdr val)))))

; A string as ACL2 reads it: between double quotes, with the backslash
; and the double quote escaped.

(defun bm-quote-chars (chars)
  (cond ((endp chars) nil)
        ((member (car chars) '(#\\ #\"))
         (list* #\\ (car chars) (bm-quote-chars (cdr chars))))
        (t (cons (car chars) (bm-quote-chars (cdr chars))))))

(defun bm-quote-string (s)
  (coerce (cons #\" (append (bm-quote-chars (coerce s 'list)) (list #\")))
          'string))

(defun bm-write-text (file text state)
  (declare (xargs :stobjs state))
  (mv-let (chan state)
    (open-output-channel file :character state)
    (pprogn (princ$ text chan state)
            (close-output-channel chan state))))

(defun bm-read-file (file state)
  (declare (xargs :stobjs state))
  (mv-let (chan state)
    (open-input-channel file :object state)
    (if (null chan)
        (mv t nil state)
      (mv-let (eofp obj state)
        (read-object chan state)
        (let ((state (close-input-channel chan state)))
          (mv eofp obj state))))))

(defconst *bm-newline* (coerce (list #\Newline) 'string))

; The marks of the certificate of an included book, found by the name of
; its file: the first part of what follows its names in the entry of
; ACL2's include-book-alist, which is NIL for a book with no certificate.

(defun bm-members (xs lst)
  (cond ((endp xs) nil)
        (t (cons (if (member-eq (car xs) lst) t nil)
                 (bm-members (cdr xs) lst)))))

(defun bm-known (names alist)
  (cond ((endp names) nil)
        (t (cons (if (find-package-entry (car names) alist) t nil)
                 (bm-known (cdr names) alist)))))

(defun bm-book-marks (familiar alist)
  (cond ((endp alist) :bm-not-included)
        ((equal (caddr (car alist)) familiar) (car (cdddr (car alist))))
        (t (bm-book-marks familiar (cdr alist)))))

(logic)

; (bm-try "what" form): whether ACL2 accepts FORM, an event or a command.
; It is evaluated inside make-event, so that nothing it does stays.

(defmacro bm-try (what form)
  `(make-event
    (mv-let (erp val state)
      (trans-eval ',form 'bm-try state t)
      (value (list 'table 'bm-results ,what
                   (if (bm-triple-erp erp val) ''refused ''accepted))))))

; (bm-top "what" form): ACL2's value of FORM, as at its top level.

(defmacro bm-top (what form)
  `(make-event
    (mv-let (erp val state)
      (trans-eval ',form 'bm-top state t)
      (value (list 'table 'bm-tops ,what
                   (if erp :bm-no-value (kwote (bm-single val))))))))

; (bm-stored "what" form): something ACL2 holds, computed now.

(defmacro bm-stored (what form)
  `(make-event (value (list 'table 'bm-stored ,what (kwote ,form)))))

; (bm-guarded MACRO "what" "text" PRESET): the form (MACRO "what" text),
; written into build/edge-guarded.lsp and evaluated by a nested LD, after
; the entry for "what" has been set to PRESET.  If the form ends in an
; error of the Lisp under ACL2, the entry stays PRESET.

(defmacro bm-guarded (macro what text table preset)
  `(pprogn
    (bm-write-text
     "build/edge-guarded.lsp"
     (concatenate 'string
                  "(in-package \"ACL2\")" *bm-newline*
                  "(table " ,(symbol-name table) " "
                  (bm-quote-string ,what) " " ,preset ")" *bm-newline*
                  "(" ,(symbol-name macro) " "
                  (bm-quote-string ,what) " " ,text ")" *bm-newline*)
     state)
    (mv-let (erp val state)
      (ld "build/edge-guarded.lsp" :ld-error-action :return!)
      (declare (ignore erp val))
      (value :done))))

(defmacro bm-guarded-top (what text)
  `(bm-guarded bm-top ,what ,text bm-tops ":bm-no-value"))

(defmacro bm-guarded-try (what text)
  `(bm-guarded bm-try ,what ,text bm-results "'refused"))

; (bm-guarded-event "what" "text"): whether ACL2 accepts the event TEXT
; at the top level of a nested LD, not inside make-event.

(defmacro bm-guarded-event (what text)
  `(pprogn
    (bm-write-text
     "build/edge-guarded.lsp"
     (concatenate 'string
                  "(in-package \"ACL2\")" *bm-newline*
                  "(table bm-results " (bm-quote-string ,what) " 'refused)"
                  *bm-newline*
                  ,text *bm-newline*
                  "(table bm-results " (bm-quote-string ,what) " 'accepted)"
                  *bm-newline*)
     state)
    (mv-let (erp val state)
      (ld "build/edge-guarded.lsp" :ld-error-action :return!)
      (declare (ignore erp val))
      (value :done))))

; (bm-read-test text): the object ACL2's reader makes of TEXT, read by
; READ-OBJECT from build/edge-read.txt inside a nested LD.  The nested LD
; takes its file names from the directory of its file, build/.

(defmacro bm-read-test (text)
  `(pprogn
    (bm-write-text "build/edge-read.txt"
                   (concatenate 'string ,text *bm-newline*)
                   state)
    (bm-write-text
     "build/edge-read.lsp"
     (concatenate
      'string
      "(in-package \"ACL2\")" *bm-newline*
      "(table bm-reads " (bm-quote-string ,text) " :bm-no-read)"
      *bm-newline*
      "(make-event (er-let* ((obj (bm-read-file \"edge-read.txt\" state)))"
      " (value (list 'table 'bm-reads " (bm-quote-string ,text)
      " (kwote obj)))))" *bm-newline*)
     state)
    (mv-let (erp val state)
      (ld "build/edge-read.lsp" :ld-error-action :return!)
      (declare (ignore erp val))
      (value :done))))

(defconst *bm-c* 7)

(set-guard-checking :none)

; ----------------------------------------------------------------------
; 1. The axioms leave a value open and ACL2 computes one.

; 1.1 BAD-ATOM<= on data.

(bm-top "1.1 (bad-atom<= 1 2), guard checking :none" (bad-atom<= 1 2))
(bm-try "1.1 prove (equal (bad-atom<= 1 2) nil)"
        (thm (equal (bad-atom<= 1 2) nil)))

; 1.2 The imports of COMMON-LISP.

(bm-top "1.2 (pkg-imports \"COMMON-LISP\"), guard checking :none"
        (pkg-imports "COMMON-LISP"))
(bm-top "1.2 (intern-in-package-of-symbol \"BM-NEW\" 'car), guard checking :none"
        (intern-in-package-of-symbol "BM-NEW" 'car))
(bm-try "1.2 prove (equal (pkg-imports \"COMMON-LISP\") nil)"
        (thm (equal (pkg-imports "COMMON-LISP") nil)))

; 1.3 INTERN-IN-PACKAGE-OF-SYMBOL at a symbol of a hidden package.
; BM-HIDDEN imports COMMON-LISP::CAR and ACL2::BM-HIDDEN-IMPORT.

(bm-stored "1.3 whether ACL2 keeps BM-HIDDEN hidden"
           (let ((entry (find-package-entry "BM-HIDDEN"
                                            (known-package-alist state))))
             (and entry (package-entry-hidden-p entry) t)))
(bm-top "1.3 (intern-in-package-of-symbol \"CAR\" (bm-hidden-symbol)), guard checking :none"
        (intern-in-package-of-symbol "CAR" (bm-hidden-symbol)))
(bm-top "1.3 (intern-in-package-of-symbol \"BM-HIDDEN-IMPORT\" (bm-hidden-symbol)), guard checking :none"
        (intern-in-package-of-symbol "BM-HIDDEN-IMPORT" (bm-hidden-symbol)))
(bm-top "1.3 (symbol-name (intern-in-package-of-symbol \"NEW\" (bm-hidden-symbol))), guard checking :none"
        (symbol-name (intern-in-package-of-symbol "NEW" (bm-hidden-symbol))))
(bm-top "1.3 (symbol-name (bm-hidden-symbol)), guard checking :none"
        (symbol-name (bm-hidden-symbol)))
(bm-try "1.3 prove (equal (intern-in-package-of-symbol \"CAR\" (bm-hidden-symbol)) 'car)"
        (thm (equal (intern-in-package-of-symbol "CAR" (bm-hidden-symbol))
                    'car)))

; 1.4 The character functions whose constraints ACL2 does not record.

(bm-stored "1.4 where ACL2 keeps the constraint of CHAR-UPCASE-NON-STANDARD"
           (getpropc 'char-upcase-non-standard 'constraint-lst nil (w state)))
(bm-stored "1.4 the constraint of ALPHA-CHAR-P-NON-STANDARD"
           (getpropc 'alpha-char-p-non-standard 'constraint-lst nil (w state)))
(bm-stored "1.4 the attachment of CHAR-UPCASE-NON-STANDARD"
           (cdr (attachment-pair 'char-upcase-non-standard (w state))))
(bm-top "1.4 (char-upcase (code-char 233)), guard checking :none"
        (char-upcase (code-char 233)))
(bm-top "1.4 (char-downcase (code-char 201)), guard checking :none"
        (char-downcase (code-char 201)))
(bm-top "1.4 (upper-case-p (code-char 201)), guard checking :none"
        (upper-case-p (code-char 201)))
(bm-try "1.4 prove (equal (char-upcase (code-char 233)) (code-char 201))"
        (thm (equal (char-upcase (code-char 233)) (code-char 201))))
(bm-try "1.4 prove (equal (char-downcase (code-char 201)) (code-char 233))"
        (thm (equal (char-downcase (code-char 201)) (code-char 233))))

; 1.5 Double-floats.

(bm-stored "1.5 the constraint of CONSTRAINED-TO-DF"
           (getpropc 'constrained-to-df 'constraint-lst nil (w state)))
(bm-stored "1.5 the body of TO-DF"
           (getpropc 'to-df 'unnormalized-body nil (w state)))
(bm-top "1.5 (to-dfp 1/3), guard checking :none" (to-dfp 1/3))
(bm-top "1.5 (to-dfp 1/10), guard checking :none" (to-dfp 1/10))
(bm-top "1.5 (from-df (df-sqrt (to-df 2))), guard checking :none"
        (from-df (df-sqrt (to-df 2))))
(bm-try "1.5 prove (equal (to-dfp 1/3) 6004799503160661/18014398509481984)"
        (thm (equal (to-dfp 1/3) 6004799503160661/18014398509481984)))
(bm-try "1.5 prove (equal (from-df (df-sqrt (to-df 2))) 6369051672525773/4503599627370496)"
        (thm (equal (from-df (df-sqrt (to-df 2)))
                    6369051672525773/4503599627370496)))

; ----------------------------------------------------------------------
; 2. The axioms give a value and ACL2 computes none.

; 2.1 A constrained function with no attachment.

(encapsulate
  (((bm-three *) => *))
  (local (defun bm-three (x) (declare (ignore x)) 3))
  (defthm bm-three-is-3 (equal (bm-three x) 3) :rule-classes nil))

(bm-top "2.1 (bm-three 5), guard checking :none" (bm-three 5))
(bm-try "2.1 prove (equal (bm-three 5) 3)"
        (thm (equal (bm-three 5) 3)
             :hints (("Goal" :use ((:instance bm-three-is-3 (x 5)))))))

; 2.2 HARD-ERROR and ILLEGAL.

(bm-stored "2.2 the body of HARD-ERROR"
           (getpropc 'hard-error 'unnormalized-body nil (w state)))
(bm-stored "2.2 the body of ILLEGAL"
           (getpropc 'illegal 'unnormalized-body nil (w state)))
(bm-stored "2.2 the body of THROW-NONEXEC-ERROR"
           (getpropc 'throw-nonexec-error 'unnormalized-body nil (w state)))
(bm-top "2.2 (hard-error 'bm \"BM\" nil), guard checking :none"
        (hard-error 'bm "BM" nil))
(bm-top "2.2 (illegal 'bm \"BM\" nil), guard checking :none"
        (illegal 'bm "BM" nil))
(bm-top "2.2 (prog2$ (er hard 'bm \"BM\") 3), guard checking :none"
        (prog2$ (er hard 'bm "BM") 3))
(bm-try "2.2 prove (equal (hard-error 'bm \"BM\" nil) nil)"
        (thm (equal (hard-error 'bm "BM" nil) nil)))
(bm-try "2.2 prove (equal (illegal 'bm \"BM\" nil) nil)"
        (thm (equal (illegal 'bm "BM" nil) nil)))

; 2.3 Non-executable functions.

(defun-nx bm-nx (x) (cons x x))

(bm-stored "2.3 the body of BM-NX" (getpropc 'bm-nx 'unnormalized-body nil (w state)))
(bm-top "2.3 (bm-nx 3), guard checking :none" (bm-nx 3))
(bm-try "2.3 prove (equal (bm-nx 3) '(3 . 3))"
        (thm (equal (bm-nx 3) '(3 . 3))))
(bm-try "2.3 prove (equal (throw-nonexec-error 'bm nil) nil)"
        (thm (equal (throw-nonexec-error 'bm nil) nil)))

; 2.4 Guard violations under each setting of guard checking.

(defun bm-gc (x) (declare (xargs :guard (consp x))) (car x))
(defun bm-gu (x) (declare (xargs :guard (consp x) :verify-guards nil)) (car x))

(set-guard-checking t)
(bm-top "2.4 (car 7), guard checking t" (car 7))
(bm-top "2.4 (bm-gc 7), guard checking t" (bm-gc 7))
(bm-top "2.4 (bm-gu 7), guard checking t" (bm-gu 7))
(set-guard-checking :all)
(bm-top "2.4 (car 7), guard checking :all" (car 7))
(bm-top "2.4 (bm-gc 7), guard checking :all" (bm-gc 7))
(bm-top "2.4 (bm-gu 7), guard checking :all" (bm-gu 7))
(set-guard-checking :nowarn)
(bm-top "2.4 (car 7), guard checking :nowarn" (car 7))
(bm-top "2.4 (bm-gc 7), guard checking :nowarn" (bm-gc 7))
(bm-top "2.4 (bm-gu 7), guard checking :nowarn" (bm-gu 7))
(set-guard-checking nil)
(bm-top "2.4 (car 7), guard checking nil" (car 7))
(bm-top "2.4 (bm-gc 7), guard checking nil" (bm-gc 7))
(bm-top "2.4 (bm-gu 7), guard checking nil" (bm-gu 7))
(set-guard-checking :none)
(bm-top "2.4 (car 7), guard checking :none" (car 7))
(bm-top "2.4 (bm-gc 7), guard checking :none" (bm-gc 7))
(bm-top "2.4 (bm-gu 7), guard checking :none" (bm-gu 7))

; 2.5 The executable half of an MBE.

(defun bm-mbe-err (x)
  (declare (xargs :guard t))
  (mbe :logic nil
       :exec (hard-error 'bm "BM" (list (cons #\0 x)))))

(bm-top "2.5 (bm-mbe-err 1), guard checking :none" (bm-mbe-err 1))
(set-guard-checking t)
(bm-top "2.5 (bm-mbe-err 1), guard checking t" (bm-mbe-err 1))
(set-guard-checking :none)
(bm-try "2.5 prove (equal (bm-mbe-err 1) nil)" (thm (equal (bm-mbe-err 1) nil)))

(defun bm-mx (x)
  (declare (xargs :guard t))
  (mbe :logic x :exec (car (cons (bm-mx x) nil))))

(bm-stored "2.5 whether ACL2 holds the guards of BM-MX as verified"
           (eq (getpropc 'bm-mx 'symbol-class nil (w state)) :common-lisp-compliant))
(bm-guarded-try "2.5 prove (equal (bm-mx 3) 3)" "(thm (equal (bm-mx 3) 3))")
(bm-try "2.5 prove (equal (bm-mx 3) 3) with the executable counterpart of BM-MX disabled"
        (thm (equal (bm-mx 3) 3) :hints (("Goal" :in-theory (disable (:e bm-mx))))))
(bm-guarded-top "2.5 (bm-mx 3), guard checking :none" "(bm-mx 3)")
(bm-top "2.5 a do$ loop$ whose measure does not decrease, guard checking :none"
        (loop$ with x = 0 do :measure 5
               (if (< 3 x) (return x) (setq x (+ x 1)))))

; 2.6 Exhaustion of the stack.

(defun bm-deep (n) (if (zp n) 0 (+ 1 (bm-deep (- n 1)))))

(bm-top "2.6 (bm-deep 1000), guard checking :none" (bm-deep 1000))
(bm-guarded-top "2.6 (bm-deep 10000000), guard checking :none"
                "(bm-deep 10000000)")

; 2.7 Single-threaded objects.

(defstobj bm-st
  (bm-arr :type (array integer (3)) :initially 0)
  (bm-fld :initially 0))

(bm-stored "2.7 the body of UPDATE-BM-ARRI"
           (getpropc 'update-bm-arri 'unnormalized-body nil (w state)))
(bm-top "2.7 (update-bm-arri 5 7 bm-st), guard checking :none"
        (update-bm-arri 5 7 bm-st))
(bm-top "2.7 (create-bm-st), guard checking :none" (create-bm-st))
(bm-top "2.7 (update-bm-arri 1 7 '((0 0 0) 0)), guard checking :none"
        (update-bm-arri 1 7 '((0 0 0) 0)))
(bm-top "2.7 (resize-bm-arr 5 bm-st), guard checking :none" (resize-bm-arr 5 bm-st))
(bm-try "2.7 prove (equal (update-nth 5 7 '(0 0 0)) '(0 0 0 nil nil 7))"
        (thm (equal (update-nth 5 7 '(0 0 0)) '(0 0 0 nil nil 7))))

; 2.8 PKG-WITNESS and PKG-IMPORTS where the name is no package: the
; lines no-value of checks/expected/facts.txt.

(bm-top "2.8 (pkg-witness \"\"), guard checking :none" (pkg-witness ""))
(bm-top "2.8 (pkg-imports \"BM-NO-SUCH-PACKAGE\"), guard checking :none"
        (pkg-imports "BM-NO-SUCH-PACKAGE"))

; 2.9 SYMBOL-PACKAGE-NAME at a symbol of a hidden package.

(bm-guarded-top "2.9 (symbol-package-name (bm-hidden-symbol)), guard checking :none"
                "(symbol-package-name (bm-hidden-symbol))")
(bm-guarded-try "2.9 prove (equal (symbol-package-name (bm-hidden-symbol)) \"BM-HIDDEN\")"
                "(thm (equal (symbol-package-name (bm-hidden-symbol)) \"BM-HIDDEN\"))")

; ----------------------------------------------------------------------
; 3. ACL2 computes a value that the axioms do not prove.

; 3.1 Attachments: the lines run, plain and attachment of
; checks/expected/facts.txt.  3.2 APPLY$ with a warrant: the same lines,
; and a function with no warrant.

(defun bm-nobadge (x) (cons x x))

(bm-top "3.2 (apply$ 'bm-nobadge '(3)), guard checking :none"
        (apply$ 'bm-nobadge '(3)))
(bm-top "3.2 (apply$ 'car '((1 . 2))), guard checking :none"
        (apply$ 'car '((1 . 2))))
(bm-try "3.2 prove (equal (apply$ 'car '((1 . 2))) 1)"
        (thm (equal (apply$ 'car '((1 . 2))) 1)))

; 3.4 State, the oracle, time, random numbers and wormholes.

(bm-top "3.4 whether (read-run-time state) gives a rational, guard checking :none"
        (mv-let (r state) (read-run-time state) (mv (rationalp r) state)))
(bm-top "3.4 whether (random$ 10 state) gives a natural number below 10, guard checking :none"
        (mv-let (r state) (random$ 10 state)
          (mv (and (natp r) (< r 10)) state)))
(bm-top "3.4 (read-acl2-oracle state), guard checking :none"
        (mv-let (erp r state) (read-acl2-oracle state) (mv (list erp r) state)))
(bm-top "3.4 (wormhole-eval 'bm-wormhole '(lambda () 7) nil), guard checking :none"
        (wormhole-eval 'bm-wormhole '(lambda () 7) nil))
(bm-try "3.4 prove (equal (mv-nth 0 (random$ 10 state)) 0)"
        (thm (equal (mv-nth 0 (random$ 10 state)) 0)))
(bm-top "3.4 (read-run-time '(1 2)), guard checking :none"
        (read-run-time '(1 2)))
(bm-try "3.4 call sys-call with no trust tag"
        (value (sys-call "true" nil)))

; 3.3 Functions whose Common Lisp code is not their definition.

(bm-stored "3.3 which of LEN, NTH, FLOOR, MEMBER-EQUAL, HARD-ERROR, THROW-NONEXEC-ERROR, CHAR-UPCASE, TO-DF, FMT-TO-COMMENT-WINDOW, HONS-COPY, SLEEP, READ-RUN-TIME, RANDOM$ and READ-ACL2-ORACLE ACL2 lists as having raw code"
           (bm-members '(len nth floor member-equal hard-error
                             throw-nonexec-error char-upcase to-df
                             fmt-to-comment-window hons-copy sleep
                             read-run-time random$ read-acl2-oracle)
                       *initial-logic-fns-with-raw-code*))

; 3.5 Memoization.

(defun bm-fib (n)
  (if (zp n) 0 (if (= n 1) 1 (+ (bm-fib (- n 1)) (bm-fib (- n 2))))))

(bm-top "3.5 (bm-fib 25) before memoization, guard checking :none" (bm-fib 25))
(memoize 'bm-fib)
(bm-top "3.5 (bm-fib 25) after memoization, guard checking :none" (bm-fib 25))

; ----------------------------------------------------------------------
; 4. The values that the axioms give to arguments outside the guards.
; The calls of the primitives are lines value of this file and of
; checks/expected/facts.txt; those of library functions are below.

(program)

(defun bm-kwote-lst (args)
  (cond ((endp args) nil)
        (t (cons (kwote (car args)) (bm-kwote-lst (cdr args))))))

(defun bm-value-lines (calls state)
  (declare (xargs :stobjs state))
  (cond ((endp calls) nil)
        (t (let ((term (cons (car (car calls))
                             (bm-kwote-lst (cdr (car calls))))))
             (mv-let (erp val)
               (magic-ev-fncall (car (car calls)) (cdr (car calls))
                                state nil nil)
               (cons (if erp
                         (bm-line "no-value" (list term))
                       (bm-line "value" (list term val)))
                     (bm-value-lines (cdr calls) state)))))))

(logic)

(defconst *bm-calls*
  '(; The primitives.
    (car 7) (cdr "ab") (binary-+ a 1) (binary-* a 3) (unary-- a) (unary-/ 0)
    (< a 1) (< 1 a) (< #c(1 2) #c(1 3)) (char-code a) (code-char 256)
    (complex 1 0) (complex a 2) (complex 1 #c(1 2)) (numerator #c(1 2))
    (denominator a) (realpart a) (imagpart 3) (symbol-name 7)
    (symbol-package-name 7) (coerce "ab" string) (coerce (1 #\a) string)
    (coerce a list) (intern-in-package-of-symbol "X" 3)
    (intern-in-package-of-symbol "abc" bm-gc) (pkg-witness 7) (pkg-imports 7)
    (bad-atom<= a "s")
    ; Library functions.
    (floor 7 0) (mod 7 0) (truncate 7 0) (rem 7 0) (ceiling 7 0) (round 7 0)
    (floor #c(1 2) 1) (floor a 2) (expt 0 0) (expt 0 -1) (expt 2 1/2)
    (expt a 2) (expt 2 a) (nth -1 (a b)) (nth x (a b)) (char "abc" 5)
    (char "abc" -1) (subseq "abc" 1 5) (take 3 (1)) (update-nth 3 x nil)
    (length abc) (abs a) (max a -1) (min a 1) (evenp 1/2) (oddp 1/2)
    (evenp a) (zp 1/2) (zp -3) (zip 1/2) (= a 0) (zerop a)
    (assoc-equal nil (1 (a . 2))) (string 7) (binary-append 1 2)
    (binary-append (1 . 2) (3)) (len (1 2 . 3)) (reverse (1 2 . 3))
    (char-upcase 7) (char< a #\a) (nthcdr -1 (1 2)) (last 7) (ash 1/2 1)
    (binary-logand 1/2 3) (integer-length a) (signum a)
    (string-append "a" b) (code-char 255)))

(bm-top "4.2 (list (1+ 'a) (<= 'a 0) (>= 'a 0) (= 'a 0)), guard checking :none"
        (list (1+ 'a) (<= 'a 0) (>= 'a 0) (= 'a 0)))

; ----------------------------------------------------------------------
; 5. Data.

; 5.1 Exactly 256 characters.

(bm-try "5.1 prove (implies (characterp c) (< (char-code c) 256))"
        (thm (implies (characterp c) (< (char-code c) 256))))
(bm-try "5.1 prove (implies (characterp c) (equal (code-char (char-code c)) c))"
        (thm (implies (characterp c) (equal (code-char (char-code c)) c))))

; 5.7 Bad atoms.

(bm-try "5.7 prove that every object is a cons, a number, a character, a string or a symbol"
        (thm (or (consp x) (acl2-numberp x) (characterp x) (stringp x)
                 (symbolp x))))

; 5.2 to 5.6 What ACL2's reader makes of each text.  BM-DUP imports
; COMMON-LISP::CAR.

(defpkg "BM-DUP" '(car car))

(bm-read-test "1/2")
(bm-read-test "2/4")
(bm-read-test "-3/6")
(bm-read-test "-0")
(bm-read-test "+5")
(bm-read-test "1.")
(bm-read-test "#c(1 0)")
(bm-read-test "#c(1/2 0)")
(bm-read-test "#C(1 2)")
(bm-read-test "#x10")
(bm-read-test "#b101")
(bm-read-test "#o17")
(bm-read-test "#36rZ")
(bm-read-test "#u1_000")
(bm-read-test "#d1.5")
(bm-read-test "#d0.1")
(bm-read-test "#f0.1")
(bm-read-test "#x-1F")
(bm-read-test "#.*bm-c*")
(bm-read-test "1.5")
(bm-read-test "1e3")
(bm-read-test "1.5d0")
(bm-read-test "#c(1.0 2)")
(bm-read-test "1/0")
(bm-read-test "#\\a")
(bm-read-test "#\\A")
(bm-read-test "#\\Space")
(bm-read-test "#\\space")
(bm-read-test "#\\Newline")
(bm-read-test "#\\Tab")
(bm-read-test "#\\Page")
(bm-read-test "#\\Rubout")
(bm-read-test "#\\Return")
(bm-read-test "#\\Linefeed")
(bm-read-test "#\\Backspace")
(bm-read-test "#\\Nul")
(bm-read-test "#\\Null")
(bm-read-test "#\\Escape")
(bm-read-test "#\\U+41")
(bm-read-test "#\\LATIN_SMALL_LETTER_A_WITH_MACRON")
(bm-read-test (coerce (list #\# #\\ (code-char 233)) 'string))
(bm-read-test (coerce (list #\" (code-char 233) (code-char 0) #\") 'string))
(bm-read-test "foo")
(bm-read-test "Foo")
(bm-read-test "|foo|")
(bm-read-test "\\foo")
(bm-read-test "||")
(bm-read-test "()")
(bm-read-test "acl2::car")
(bm-read-test "bm-dup::car")
(bm-read-test "common-lisp::bm-new")
(bm-read-test ":k")
(bm-read-test "keyword::k")
(bm-read-test "bm-no-such-package::x")
(bm-read-test "sb-ext::gc")
(bm-read-test "#:foo")
(bm-read-test "#(1 2)")
(bm-read-test "#*101")
(bm-read-test "#p\"x\"")
(bm-read-test "'x")
(bm-read-test "#'car")
(bm-read-test "`(a ,b)")
(bm-read-test "#{\"\"\"abc\"\"\"}")
(bm-read-test "\"a\\nb\"")
(bm-read-test "#|c|# 1")
(bm-read-test "#+sbcl 1")
(bm-read-test "#-sbcl 1 2")
(bm-read-test "#+acl2-loop-only 1")

; ----------------------------------------------------------------------
; 6. Admission.

; 6.1 Names that the Lisp under ACL2 uses.

(bm-try "6.1 define a function named LOAD-ACL2" (defun load-acl2 (x) x))
(bm-try "6.1 define a function named EXIT-LISP" (defun exit-lisp (x) x))
(bm-try "6.1 define a function named BM-NOT-IN-THE-LISP" (defun bm-not-in-the-lisp (x) x))
(bm-try "6.1 call BIG-N, a function that ACL2 holds untouchable"
        (thm (natp (big-n))))
(bm-try "6.10 repeat ACL2's own definition of ZIP"
        (defun zip (x)
          (declare (xargs :mode :logic :guard (integerp x)))
          (if (integerp x) (= x 0) t)))

; 6.3 Measures that ACL2 guesses.

(defun bm-guess (x y) (if (consp y) (bm-guess x (cdr y)) x))

(bm-stored "6.3 the measure ACL2 stores for BM-GUESS"
           (access justification (getpropc 'bm-guess 'justification nil (w state))
                   :measure))
(bm-try "6.3 define BM-UP with no measure"
        (defun bm-up (i n)
          (if (and (integerp i) (integerp n) (< i n)) (bm-up (+ i 1) n) i)))
(bm-try "6.3 define BM-UP with the measure (nfix (- n i))"
        (defun bm-up (i n)
          (declare (xargs :measure (nfix (- n i))))
          (if (and (integerp i) (integerp n) (< i n)) (bm-up (+ i 1) n) i)))

; 6.5 The body ACL2 stores.

(defun bm-body (x)
  (let ((y (car x)))
    (cond ((and y (< *bm-c* 9)) (mbe :logic y :exec y))
          (t (list x (prog2$ (cw "x") x))))))

(bm-stored "6.5 the body ACL2 stores for BM-BODY"
           (getpropc 'bm-body 'unnormalized-body nil (w state)))
(bm-stored "6.5 the normalized body ACL2 uses for BM-BODY"
           (access def-body (car (getpropc 'bm-body 'def-bodies nil (w state)))
                   :concl))

; 6.6 Definitions inside an encapsulate.  BM-K2 recurs under tests that
; do not mention BM-K; BM-K3 recurs under a test that does.

(encapsulate
  (((bm-k *) => *))
  (local (defun bm-k (x) x))
  (defun bm-k2 (x) (if (consp x) (bm-k2 (cdr x)) (bm-k x)))
  (defun bm-k3 (x) (if (consp x) (if (bm-k x) (bm-k3 (cdr x)) nil) nil))
  (defthm bm-k-idempotent (equal (bm-k (bm-k x)) (bm-k x)) :rule-classes nil))

(bm-stored "6.6 the constraint of BM-K"
           (getpropc 'bm-k 'constraint-lst nil (w state)))
(bm-stored "6.6 the constraint of BM-K2"
           (getpropc 'bm-k2 'constraint-lst nil (w state)))
(bm-stored "6.6 the constraint of BM-K3"
           (getpropc 'bm-k3 'constraint-lst nil (w state)))
(bm-stored "6.6 the siblings of BM-K"
           (getpropc 'bm-k 'siblings nil (w state)))
(bm-stored "6.6 whether ACL2 stores a body for BM-K3"
           (if (getpropc 'bm-k3 'unnormalized-body nil (w state)) t nil))

; BM-Q2 calls BM-Q and does not call itself; an exported theorem
; mentions it.

(encapsulate
  (((bm-q *) => *))
  (local (defun bm-q (x) x))
  (defun bm-q2 (x) (cons (bm-q x) x))
  (defthm bm-q2-car (equal (car (bm-q2 x)) (bm-q x)) :rule-classes nil))

(bm-stored "6.6 the constraint of BM-Q"
           (getpropc 'bm-q 'constraint-lst nil (w state)))
(bm-stored "6.6 the constraint of BM-Q2"
           (getpropc 'bm-q2 'constraint-lst nil (w state)))

; 6.7 Where the constraint is stored.

(encapsulate
  (((bm-m1 *) => *) ((bm-m2 *) => *))
  (local (defun bm-m1 (x) x))
  (local (defun bm-m2 (x) x))
  (defthm bm-m1-m2 (equal (bm-m1 x) (bm-m2 x)) :rule-classes nil))

(bm-stored "6.7 the constraint of BM-M1"
           (getpropc 'bm-m1 'constraint-lst nil (w state)))
(bm-stored "6.7 the constraint of BM-M2"
           (getpropc 'bm-m2 'constraint-lst nil (w state)))

; 6.9 DEFUN-SK.

(defun-sk bm-exists (x) (exists y (equal y (cons x x))))

(bm-stored "6.9 the body of BM-EXISTS"
           (getpropc 'bm-exists 'unnormalized-body nil (w state)))
(bm-stored "6.9 the constraint of BM-EXISTS-WITNESS"
           (getpropc 'bm-exists-witness 'constraint-lst nil (w state)))
(bm-stored "6.9 the constraint of BM-EXISTS"
           (getpropc 'bm-exists 'constraint-lst nil (w state)))
(bm-stored "6.9 the axiom of a DEFCHOOSE stored for BM-EXISTS-WITNESS"
           (getpropc 'bm-exists-witness 'defchoose-axiom nil (w state)))
(bm-stored "6.9 the event that introduced BM-EXISTS-WITNESS"
           (get-event 'bm-exists-witness (w state)))

; 6.12 Tests that leave nothing in a statement.

(bm-try "6.12 define a function whose formal is irrelevant"
        (defun bm-irr (x y) (if (consp x) (bm-irr (cdr x) y) nil)))
(bm-try "6.12 the same, with the formal declared irrelevant"
        (defun bm-irr (x y)
          (declare (irrelevant y))
          (if (consp x) (bm-irr (cdr x) y) nil)))
(bm-try "6.12 a rewrite rule whose two sides are the same term"
        (defthm bm-same (equal (bm-k x) (bm-k x))))
(bm-try "6.12 the same theorem with no rule class"
        (defthm bm-same (equal (bm-k x) (bm-k x)) :rule-classes nil))

; 6.14 A lambda object with a free variable.

(bm-try "6.14 a lambda object with a free variable"
        (defun bm-free-lambda (x) (apply$ '(lambda (x) (cons x y)) (list x))))

; ----------------------------------------------------------------------
; 7. Packages.

(bm-stored "7.1 the axiom ACL2 holds for the package ACL2-USER"
           (if (getpropc 'acl2-user-package 'theorem nil (w state)) t nil))

(defpkg "BM-A::B" nil)
(defpkg "BM A" nil)
(defpkg "ACL2-PKG-BM" nil)
(bm-try "7.2 a package named IN, whose rule would be named IN-PACKAGE"
        (defpkg "IN" nil))
(bm-try "7.2 a package named LISP" (defpkg "LISP" nil))
(bm-try "7.2 a package named ACL2_*1*_BM" (defpkg "ACL2_*1*_BM" nil))
(bm-guarded-event "7.2 a package whose name is BM and the character 233"
                  (concatenate 'string "(defpkg \"BM" (string (code-char 233))
                               "\" nil)"))
(bm-guarded-event "7.2 a package whose name is BM and the character 201"
                  (concatenate 'string "(defpkg \"BM" (string (code-char 201))
                               "\" nil)"))
(bm-guarded-try "7.2 a package named SB-EXT" "(defpkg \"SB-EXT\" nil)")
(bm-guarded-try "7.2 a package named CL-USER" "(defpkg \"CL-USER\" nil)")

(bm-stored "7.2 which of BM-A::B, BM A, ACL2-PKG-BM, IN, SB-EXT and CL-USER ACL2 knows as packages, after the attempts"
           (bm-known '("BM-A::B" "BM A" "ACL2-PKG-BM" "IN" "SB-EXT" "CL-USER")
                     (known-package-alist state)))
(bm-stored "7.3 (pkg-imports \"BM-DUP\"), declared with the imports (car car)"
           (pkg-imports "BM-DUP"))
(defpkg "BM-ORDER" '(zebra :apple car))
(bm-stored "7.3 (pkg-imports \"BM-ORDER\"), declared with the imports (zebra :apple car)"
           (pkg-imports "BM-ORDER"))
(bm-stored "7.3 the formula ACL2 holds for BM-DUP-PACKAGE"
           (getpropc 'bm-dup-package 'theorem nil (w state)))

(bm-try "7.4 a package declared inside encapsulate"
        (encapsulate () (defpkg "BM-IN-ENCAPSULATE" nil)))
(bm-try "7.4 a package declared inside progn"
        (progn (defpkg "BM-IN-PROGN" nil)))
(bm-try "7.4 a package declared by the expansion of make-event"
        (make-event '(defpkg "BM-MADE-BY-MAKE-EVENT" nil)))

; ----------------------------------------------------------------------
; 9. Where the logic is not a set of axioms.

(bm-try "9.1 prove (equal (len (append x y)) (+ (len x) (len y))) without induction"
        (thm (equal (len (append x y)) (+ (len x) (len y)))
             :hints (("Goal" :do-not-induct t))))
(bm-try "9.1 prove (equal (len (append x y)) (+ (len x) (len y)))"
        (thm (equal (len (append x y)) (+ (len x) (len y)))))
(bm-try "9.2 define BM-ZERO, which 0 satisfies but which does not terminate"
        (defun bm-zero (x) (if (zp x) 0 (bm-zero (+ x 1)))))

(defun bm-hh (x) (if (consp x) (cdr x) x))

(encapsulate
  (((bm-h *) => *))
  (local (defun bm-h (x) (if (consp x) (cdr x) x)))
  (defthm bm-h-twice
    (implies (not (consp x)) (equal (bm-h (bm-h x)) (bm-h x)))
    :rule-classes nil))

(bm-try "9.3 prove a theorem about BM-HH by functional instantiation of BM-H-TWICE"
        (defthm bm-hh-twice
          (implies (not (consp x)) (equal (bm-hh (bm-hh x)) (bm-hh x)))
          :hints (("Goal" :use ((:functional-instance bm-h-twice
                                                      (bm-h bm-hh)))))
          :rule-classes nil))

; ----------------------------------------------------------------------
; 10. Program mode.

(defun bm-pm (x)
  (declare (xargs :mode :program))
  (mbe :logic (list 'logic x) :exec (list 'exec x)))
(defun bm-peq (x y) (declare (xargs :mode :program)) (eq x y))
(defun bm-pcc (x) (declare (xargs :mode :program)) (code-char x))
(defun bm-pco (x y) (declare (xargs :mode :program)) (coerce x y))
(defun bm-pcar (x) (declare (xargs :mode :program)) (car x))

(bm-top "10.1 (bm-pm 1), guard checking :none" (bm-pm 1))
(bm-top "10.2 (bm-peq (coerce '(#\\a) 'string) (coerce '(#\\a) 'string)), guard checking :none"
        (bm-peq (coerce '(#\a) 'string) (coerce '(#\a) 'string)))
(bm-top "10.2 (char-code (bm-pcc 300)), guard checking :none"
        (char-code (bm-pcc 300)))
(bm-top "10.2 (bm-pco \"ab\" 'string), guard checking :none"
        (bm-pco "ab" 'string))
(set-guard-checking t)
(bm-top "10.1 (bm-pm 1), guard checking t" (bm-pm 1))
(bm-top "10.2 (bm-peq (coerce '(#\\a) 'string) (coerce '(#\\a) 'string)), guard checking t"
        (bm-peq (coerce '(#\a) 'string) (coerce '(#\a) 'string)))
(bm-top "10.2 (char-code (bm-pcc 300)), guard checking t"
        (char-code (bm-pcc 300)))
(bm-top "10.2 (< (char-code (bm-pcc 300)) 256), guard checking t"
        (< (char-code (bm-pcc 300)) 256))
(bm-top "10.2 (bm-pco \"ab\" 'string), guard checking t"
        (bm-pco "ab" 'string))
(set-guard-checking :none)

; ----------------------------------------------------------------------
; 8. Ways a session leaves the axioms.  These come last, because some of
; them leave in the world what no proof should rest on.

; 8.2 SKIP-PROOFS.

(bm-try "8.2 a theorem (equal 1 2) under skip-proofs"
        (skip-proofs (defthm bm-one-is-two (equal 1 2) :rule-classes nil)))
(bm-try "8.2 a definition that does not terminate, without skip-proofs"
        (defun bm-bad (x)
          (declare (xargs :measure (acl2-count x)))
          (if (consp x) (not (bm-bad x)) nil)))
(bm-try "8.2 the same definition under skip-proofs, and then a proof of NIL"
        (progn
          (skip-proofs (defun bm-bad (x)
                         (declare (xargs :measure (acl2-count x)))
                         (if (consp x) (not (bm-bad x)) nil)))
          (defthm bm-nil nil
            :rule-classes nil
            :hints (("Goal" :use ((:instance (:definition bm-bad) (x '(1))))
                            :in-theory (disable bm-bad (:e bm-bad)))))))

(bm-stored "8.2 what ACL2 records of skipped proofs, before any"
           (global-val 'skip-proofs-seen (w state)))
(skip-proofs (defthm bm-skipped (equal 3 3) :rule-classes nil))
(bm-stored "8.2 what ACL2 records of skipped proofs, after one"
           (global-val 'skip-proofs-seen (w state)))

; 8.3 A book with no certificate.

(bm-try "8.3 include the uncertified book build/edge-false, and then prove NIL"
        (progn (include-book "build/edge-false")
               (defthm bm-nil-2 nil :rule-classes nil
                 :hints (("Goal" :use bm-false)))))
(include-book "build/edge-false")
(bm-stored "8.3 the marks ACL2 records for the certified book build/edge-hidden"
           (bm-book-marks "edge-hidden" (global-val 'include-book-alist (w state))))
(bm-stored "8.3 the marks ACL2 records for the uncertified book build/edge-false"
           (bm-book-marks "edge-false" (global-val 'include-book-alist (w state))))

; 8.6 MAKE-EVENT.

(make-event (list 'defun 'bm-made '()
                  (list 'quote (len (strip-cars (known-package-alist state))))))

(bm-stored "8.6 the event ACL2 stores for BM-MADE"
           (get-event 'bm-made (w state)))

; 8.5 Redefinition.

(defun bm-one () (declare (xargs :guard t)) 1)
(defthm bm-one-is-1 (equal (bm-one) 1) :rule-classes nil)
(bm-stored "8.5 what ACL2 records of redefinition, before any"
           (global-val 'redef-seen (w state)))
(redef!)
(defun bm-one () (declare (xargs :guard t)) 3)
(bm-top "8.5 (bm-one) after redefinition, guard checking :none" (bm-one))
(bm-try "8.5 prove NIL from the theorem about the first definition"
        (thm nil :hints (("Goal" :use bm-one-is-1))))
(bm-stored "8.5 what ACL2 records of redefinition, after one"
           (global-val 'redef-seen (w state)))

; 8.4 Trust tags, progn! and raw Lisp.

(bm-try "8.4 progn! with no trust tag" (progn! (value nil)))
(bm-try "8.4 an attachment with :skip-checks and no trust tag"
        (progn (defstub bm-s0 (x) t)
               (defun bm-s0-impl (x) x)
               (defattach (bm-s0 bm-s0-impl) :skip-checks t)))
(defun bm-two () (declare (xargs :guard t)) 2)
(bm-stored "8.4 the trust tags ACL2 records, before any"
           (global-val 'ttags-seen (w state)))
(defttag :bm-edge)
(bm-stored "8.4 the trust tags ACL2 records, after one"
           (global-val 'ttags-seen (w state)))
(bm-top "8.4 (sys-call \"true\" nil) with a trust tag, guard checking :none"
        (sys-call "true" nil))
(progn! (set-raw-mode t) (defun bm-two () 5))
(bm-top "8.4 (bm-two) after a definition in raw Lisp, guard checking :none" (bm-two))
(bm-try "8.4 prove (equal (bm-two) 5)" (thm (equal (bm-two) 5)))
(defthm bm-two-is-5 (equal (bm-two) 5) :rule-classes nil)
(bm-try "8.4 prove NIL from BM-TWO-IS-5 and the definition of BM-TWO"
        (thm nil :hints (("Goal" :use (bm-two-is-5 (:definition bm-two))
                                 :in-theory (disable bm-two (:e bm-two))))))

; 10.2 CAR of 7 in program mode, with guard checking t.  This is the last
; form evaluated, because the Lisp under ACL2 may report damage to its
; memory.

(set-guard-checking t)
(bm-guarded-top "10.2 (bm-pcar 7), guard checking t" "(bm-pcar 7)")
(set-guard-checking :none)

; ----------------------------------------------------------------------
; The lines.

(program)

(defun bm-result-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (bm-line (if (eq (cdr (car alist)) 'refused)
                              "refused"
                            "accepted")
                          (list (car (car alist))))
                 (bm-result-lines (cdr alist))))))

(defun bm-top-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (if (eq (cdr (car alist)) :bm-no-value)
                     (bm-line "no-top" (list (car (car alist))))
                   (bm-line "top" (list (car (car alist)) (cdr (car alist)))))
                 (bm-top-lines (cdr alist))))))

(defun bm-stored-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (bm-line "stored" (list (car (car alist)) (cdr (car alist))))
                 (bm-stored-lines (cdr alist))))))

(defun bm-read-lines (alist)
  (cond ((endp alist) nil)
        (t (cons (if (eq (cdr (car alist)) :bm-no-read)
                     (bm-line "no-read" (list (car (car alist))))
                   (bm-line "read" (list (car (car alist)) (cdr (car alist)))))
                 (bm-read-lines (cdr alist))))))

; The functions of the world ACL2 starts with, in logic mode, that have
; a definition which ACL2 holds in the constraint of an encapsulate.

(defun bm-start-fns (tail wrld acc)
  (cond ((endp tail) acc)
        ((and (eq (cadar tail) 'formals)
              (not (eq (cddar tail) *acl2-property-unbound*))
              (<= (getpropc (caar tail) 'absolute-event-number 0 wrld)
                  *bm-start*))
         (bm-start-fns (cdr tail) wrld (cons (caar tail) acc)))
        (t (bm-start-fns (cdr tail) wrld acc))))

(defun bm-defined-in-constraint (fns wrld)
  (cond ((endp fns) nil)
        ((and (not (eq (getpropc (car fns) 'symbol-class nil wrld) :program))
              (getpropc (car fns) 'unnormalized-body nil wrld)
              (getpropc (car fns) 'constraint-lst nil wrld))
         (cons (car fns) (bm-defined-in-constraint (cdr fns) wrld)))
        (t (bm-defined-in-constraint (cdr fns) wrld))))

(defun bm-unknown-constraints (fns wrld)
  (cond ((endp fns) nil)
        ((let* ((c0 (getpropc (car fns) 'constraint-lst nil wrld))
                (c (if (and c0 (symbolp c0))
                       (getpropc c0 'constraint-lst nil wrld)
                     c0)))
           (and (consp c) (eq (car c) :unknown-constraints)))
         (cons (car fns) (bm-unknown-constraints (cdr fns) wrld)))
        (t (bm-unknown-constraints (cdr fns) wrld))))

(defun bm-edge-lines (state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state))
         (fns (remove-duplicates-eq (bm-start-fns wrld wrld nil))))
    (append
     (bm-result-lines (reverse (table-alist 'bm-results wrld)))
     (bm-top-lines (reverse (table-alist 'bm-tops wrld)))
     (bm-stored-lines (reverse (table-alist 'bm-stored wrld)))
     (bm-read-lines (reverse (table-alist 'bm-reads wrld)))
     (bm-value-lines *bm-calls* state)
     (list
      (bm-line "count"
               (list "3.3 functions in logic mode that ACL2 lists as having raw code"
                     (len *initial-logic-fns-with-raw-code*)))
      (bm-line "count"
               (list "1.4 functions with constraints that ACL2 does not record"
                     (len (bm-unknown-constraints fns wrld))))
      (bm-line "stored"
               (list "1.4 those functions"
                     (merge-sort-symbol< (bm-unknown-constraints fns wrld))))
      (bm-line "count"
               (list "6.6 functions with a definition that ACL2 holds in a constraint"
                     (len (bm-defined-in-constraint fns wrld))))
      (bm-line "stored"
               (list "6.6 those functions"
                     (merge-sort-symbol< (bm-defined-in-constraint fns wrld))))))))

(logic)

(bm-write-file (bm-edge-lines state) "build/edge.txt" state)

(cw "edge: ~x0 lines written~%" (len (bm-edge-lines state)))

(good-bye)
