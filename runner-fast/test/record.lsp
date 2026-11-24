; ACL2's value of each term of a file, for the tests of the fast runner
; (runner-fast/test/record.sh).  (rf-record "IN" "OUT" state) reads IN, a
; file of terms in the text of spec/formats.md, one a line, in which every
; datum is an integer, a string with no escape, or a symbol or a list of
; these, so that ACL2's reader takes each line for the term that a runner
; takes it for.  It writes OUT.read, each term as ACL2 read it, in the
; text of spec/formats.md, and OUT.values, on the same line, ACL2's value
; of the term in the same text, or "no value".  It evaluates each term as
; ACL2's top level does.  It needs checks/canon.lsp.

(in-package "ACL2")

(program)
(set-state-ok t)

(defun rf-text (x) (coerce (reverse (bm-obj x nil)) 'string))

(defun rf-lines (terms read values state)
  (if (endp terms)
      (mv (reverse read) (reverse values) state)
    (mv-let (erp val state)
      (trans-eval (car terms) 'rf-record state t)
      (rf-lines (cdr terms)
                (cons (rf-text (car terms)) read)
                (cons (if erp "no value" (rf-text (cdr val))) values)
                state))))

(defun rf-record (in out state)
  (mv-let (erp terms state)
    (read-file in state)
    (if erp
        (mv erp nil state)
      (mv-let (read values state)
        (rf-lines terms nil nil state)
        (let ((state (bm-write-file read (concatenate 'string out ".read")
                                    state)))
          (let ((state (bm-write-file values
                                      (concatenate 'string out ".values")
                                      state)))
            (mv nil (len terms) state)))))))
