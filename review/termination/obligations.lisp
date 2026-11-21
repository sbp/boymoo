; The obligations of termination that the checker computes, given as data
; for the comparison of review/termination/run.sh with ACL2's measure
; conjectures.  It is no part of the checker: it is not exported with it
; and not counted in its size.  It calls the checker's own functions:
; PARSE-LINE reads each line, ADMIT admits it, FINISH ends a statement as
; a skip entry does, and MEASURE-ENTRY reads a measure entry for a define
; that has obligations and computes them with TERMINATION-OBLIGATIONS
; (checker/check.lisp and checker/admit.lisp).  So the clauses are those
; that the checker would ask a proof of, given the same lines.
;
; review/termination/one.sh loads it with LD, after the book
; build/checker/acl2/check.

(in-package "BOYMOO")

; Its functions are in program mode, so that loading it proves nothing in
; the world of the book that was included before it.
(program)

(defconst *measure-words* (word-table '("measure") '(:measure)))

(defconst *clause-words* (word-table '("clause") '(:clause)))

; GIVEN is a trie from the characters of the text of the name of a
; function, as spec/formats.md writes it, to a list (M C1 ... Cn) of
; lines, each the list of its characters with its line feed: M the line
; (measure F M1 ... Mk) for the definition of that function, and each Ci a
; line (clause L1 ... Lp), one of the clauses that it is compared with.

; The clauses of the lines CS, as the checker reads them in a world whose
; packages are PKGS, or :UNREADABLE.
(defun read-clauses (cs pkgs)
  (if (consp cs)
      (let ((line (parse-line (car cs) *clause-words* pkgs))
            (rest (read-clauses (cdr cs) pkgs)))
        (if (and line (not (equal rest :unreadable)))
            (cons (cdr line) rest)
          :unreadable))
    nil))

; The record of the pending define P, whose functions are entered in W but
; not yet in use: (F RESULT CLAUSES), where F is the text of the name of
; its first function; RESULT is the list of the clauses that the checker
; computes as its obligations of termination from the measure entry that
; GIVEN holds for F, or a string that says why there are none; and CLAUSES
; are the clauses that GIVEN holds for F, as the checker reads them.
(defun define-record (p w given)
  (let* ((f (symbol-name (pending-name p)))
         (g (trie-get (coerce f 'list) given)))
    (if (consp g)
        (let ((m (parse-line (car g) *measure-words* (w-pkgs w)))
              (clauses (read-clauses (cdr g) (w-pkgs w))))
          (if m
              (let ((r (measure-entry (cdr m) p nil w)))
                (list f (if (stringp r) r (car (cdr (car r)))) clauses))
            (list f "the measure entry cannot be read" clauses)))
      (list f "no measure is given for its first function" nil))))

; The pending define of LINE, a define line of the library, if its bodies
; call its functions.
(defun library-pending (line)
  (let ((data (cdr line)))
    (if (and (equal (car line) :define)
             (consp data)
             (defs-shape-p (cdr data))
             (calls-list-p (def-bodies (cdr data)) (def-names (cdr data))))
        (list :define (car data) (cdr data))
      nil)))

; The records of the define lines among LINES that have obligations,
; reversed onto ACC, for the lines read from line N + 1 of INPUT, :LIBRARY
; or :STATEMENTS, in the world W; the result is (ACC . W), W the world
; after them.  A record is (N F RESULT CLAUSES), N the number of the line
; and the rest as for DEFINE-RECORD.  A line that repeats an earlier one
; gives (N :REPEAT).  A line that cannot be read or admitted gives
; (N :REFUSED REASON) and ends the walk.
(defun obligation-records (lines n input w given acc)
  (if (consp lines)
      (let ((line (parse-line (car lines) *statement-words* (w-pkgs w)))
            (n (+ 1 n)))
        (if line
            (if (repeat-p line w)
                (obligation-records (cdr lines) n input w given
                                    (cons (list n :repeat) acc))
              (let ((r (admit line input w)))
                (if (stringp r)
                    (cons (cons (list n :refused r) acc) w)
                  (let ((w2 (car r))
                        (p (cdr r)))
                    (if p
                        (obligation-records
                         (cdr lines) n input (finish p w2) given
                         (if (equal (car p) :define)
                             (cons (cons n (define-record p w2 given)) acc)
                           acc))
                      (let ((lp (if (equal input :library)
                                    (library-pending line)
                                  nil)))
                        (obligation-records
                         (cdr lines) n input w2 given
                         (if lp
                             (cons (cons n (define-record
                                            lp
                                            (put-entries
                                             (def-names (car (cdr (cdr lp))))
                                             nil nil line w)
                                            given))
                                   acc)
                           acc))))))))
          (cons (cons (list n :refused *unreadable*) acc) w)))
    (cons acc w)))

; The records of the define lines of the ground theory, LINES, whose
; bodies call their function, reversed onto ACC, from line N + 1, in W,
; the world of the whole ground theory.  The checker never asks for these
; obligations; they are computed as for any define, from the same entry.
(defun ground-records (lines n w given acc)
  (if (consp lines)
      (let ((line (parse-line (car lines) *ground-words* (w-pkgs w)))
            (n (+ 1 n)))
        (if (and line
                 (equal (car line) :define)
                 (consp (cdr line))
                 (consp (cdr (cdr line)))
                 (defs-shape-p (list (car (cdr (cdr line)))))
                 (calls-list-p (def-bodies (list (car (cdr (cdr line)))))
                               (def-names (list (car (cdr (cdr line)))))))
            (ground-records (cdr lines) n w given
                            (cons (cons n (define-record
                                           (list :define (car (cdr line))
                                                 (list (car (cdr (cdr line)))))
                                           w given))
                                  acc))
          (ground-records (cdr lines) n w given acc)))
    acc))

; The records for the ground theory and the library, when BOOK is NIL; or
; for the statements of a book, after the library, which is admitted as
; the checker admits it (CHECK-LIBRARY).  GROUND, LIBRARY and BOOK are
; strings of the bytes of each.  The result is (GROUND LIBRARY BOOK), each
; a list of records in the order of the lines, or a string if the ground
; theory or the library cannot be read.
(defun all-records (ground library book given)
  (let ((g (load-ground (lines-of ground) (initial-world))))
    (if (equal g :bad)
        "the ground theory could not be read"
      (if book
          (let ((w (check-library (lines-of library) 0 g)))
            (if (rejected-p w)
                "the library could not be admitted"
              (list nil nil
                    (rev (car (obligation-records (lines-of book) 0 :statements
                                                  w given nil))))))
        (list (rev (ground-records (lines-of ground) 0 g given nil))
              (rev (car (obligation-records (lines-of library) 0 :library g
                                            given nil)))
              nil)))))
