; The shell of the exporter of PLAN.md, step 2.  export/book.sh loads it
; into ACL2 after the world to be exported is in place and after the books
; build/export/acl2/canon and build/export/acl2/core, which export/certify.sh
; certifies from checks/canon.lisp and export/core.lisp, and calls
; BX-EXPORT-LIBRARY or BX-EXPORT-BOOK.  The core decides every line that
; is written; the shell does what needs the state of the session:
;
;   - it takes the world from the session;
;   - it translates the bodies of functions in program mode that the world
;     does not store, which the core asks for (BX-TRANSLATION-REQUESTS),
;     with ACL2's TRANSLATE-CMP, and hands the results to the core;
;   - it reads the local events of each book from the book's source, for
;     the prover's aids, and hands the core the directory of ACL2's books
;     and the directory in which ACL2 runs, by which books are named;
;   - it prints each line with BM-LINE of checks/canon.lisp and writes the
;     files.
;
; It is in program mode, and nothing in it is proved.

(in-package "ACL2")

(program)
(set-state-ok t)

;;; Translation

; The pair (FN . (:ok . TERM)), or (FN . (:error . MESSAGE)), for the body
; BODY of the function FN in program mode.  Calls of functions that ACL2
; holds untouchable are allowed, as when ACL2 built itself.

(defun bx-translate (fn body wrld)
  (mv-let (erp val)
    (translate-cmp body t nil t 'bx-translate wrld
                   (default-state-vars nil :temp-touchable-fns t
                                       :temp-touchable-vars t))
    (if erp
        (cons fn (cons :error (fms-to-string "~@0" (list (cons #\0 val)))))
      (cons fn (cons :ok val)))))

(defun bx-translations (requests wrld)
  (cond ((endp requests) nil)
        (t (cons (bx-translate (car (car requests)) (cdr (car requests)) wrld)
                 (bx-translations (cdr requests) wrld)))))

;;; The local events of the books, for the prover's aids

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

(defun bx-local-items (name events)
  (cond ((endp events) nil)
        (t (cons (list "local" (list name (car events)))
                 (bx-local-items name (cdr events))))))

; The lines (local BOOK EVENT) of the books whose sources are FILES, and a
; note for each book whose source cannot be read: (mv lines notes state).

(defun bx-local-lines (files lines notes state)
  (cond ((endp files) (mv (reverse lines) (reverse notes) state))
        (t (mv-let (forms state)
             (bx-book-forms (car files) state)
             (let ((name (bx-book-name (car files) (system-books-dir state)
                                       (cbd))))
               (if (eq forms :error)
                   (bx-local-lines (cdr files) lines
                                   (cons (bx-note "source of a book not read" name)
                                         notes)
                                   state)
                 (bx-local-lines (cdr files)
                                 (revappend (bx-local-items name (bx-locals forms))
                                            lines)
                                 notes state)))))))

;;; Writing

(defun bx-text-lines (lines)
  (cond ((endp lines) nil)
        (t (cons (bm-line (car (car lines)) (cadr (car lines)))
                 (bx-text-lines (cdr lines))))))

(defun bx-write-lines (lines chan state)
  (cond ((endp lines) state)
        (t (pprogn (princ$ (car lines) chan state)
                   (newline chan state)
                   (bx-write-lines (cdr lines) chan state)))))

; Writes LINES, each (WORD ARGS), to the file FILE, one text on each line.

(defun bx-write-file (lines file state)
  (mv-let (chan state)
    (open-output-channel file :character state)
    (cond ((null chan)
           (prog2$ (er hard 'bx-write-file "Cannot write ~x0" file) state))
          (t (pprogn (bx-write-lines (bx-text-lines lines) chan state)
                     (close-output-channel chan state))))))

;;; The two entries

; The library: the events numbered at most HI, the end of the world ACL2
; starts with.  Writes PREFIX.statements, PREFIX.program and PREFIX.notes.

(defun bx-export-library (ground-fns hi prefix state)
  (let* ((wrld (w state))
         (translations (bx-translations (bx-translation-requests 0 hi wrld)
                                        wrld)))
    (mv-let (stmts progs notes)
      (bx-library-lines ground-fns hi translations wrld)
      (pprogn
       (bx-write-file stmts (concatenate 'string prefix ".statements") state)
       (bx-write-file progs (concatenate 'string prefix ".program") state)
       (bx-write-file notes (concatenate 'string prefix ".notes") state)
       (value (list (len stmts) (len notes)))))))

; A book: the events numbered above LO and at most HI, which including it
; added to the world ACL2 starts with, whose last event is numbered
; BOOT-HI.  Writes PREFIX.statements, PREFIX.program, PREFIX.aids and
; PREFIX.notes.

(defun bx-export-book (ground-fns boot-hi lo hi prefix state)
  (let* ((wrld (w state))
         (translations (bx-translations (bx-translation-requests lo hi wrld)
                                        wrld)))
    (mv-let (locals local-notes state)
      (bx-local-lines (remove-duplicates-equal
                       (bx-book-files (bx-events wrld lo hi nil)))
                      nil nil state)
      (mv-let (stmts progs notes aids)
        (bx-book-lines ground-fns boot-hi lo hi translations
                       (system-books-dir state) (cbd) wrld)
        (pprogn
         (bx-write-file (append locals aids)
                        (concatenate 'string prefix ".aids") state)
         (bx-write-file stmts (concatenate 'string prefix ".statements") state)
         (bx-write-file progs (concatenate 'string prefix ".program") state)
         (bx-write-file (append notes (bx-note-lines (bx-select :note local-notes)))
                        (concatenate 'string prefix ".notes") state)
         (value (list (len stmts) (len notes) (+ (len locals) (len aids)))))))))
