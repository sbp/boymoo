; The printer of the formats, for the scripts of this repository: the
; book checks/canon.lisp, which defines it, and two functions that write a
; list of lines to a file.  A script loads it with
;
;     (ld "checks/canon.lsp")
;
; from the root of the repository.

(in-package "ACL2")

(ld "canon.lisp")

(program)

(defun bm-write-lines (lines chan state)
  (declare (xargs :stobjs state))
  (cond ((endp lines) state)
        (t (pprogn (princ$ (car lines) chan state)
                   (newline chan state)
                   (bm-write-lines (cdr lines) chan state)))))

(defun bm-write-file (lines file state)
  (declare (xargs :stobjs state))
  (mv-let (chan state)
    (open-output-channel file :character state)
    (cond ((null chan)
           (prog2$ (er hard 'bm-write-file "Cannot write ~x0" file) state))
          (t (pprogn (bm-write-lines lines chan state)
                     (close-output-channel chan state))))))

(logic)
