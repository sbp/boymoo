; ACL2's value of each call of a file, for the tests of the reference
; runner (runner/test.sh).  (rt-expect "IN" "OUT" state) reads IN, a file
; of calls (FN ARG ...) whose arguments are data, and writes OUT.terms,
; the term (FN 'ARG ...) of each call in the text of spec/formats.md,
; and OUT.values, on the same line, ACL2's value of the term in the same
; text, or "no value".  It evaluates each term as ACL2's top level does,
; with attachments in force and guard checking :none, the setting of a
; runner (spec/language.md, section 4).  It needs
; checks/canon.lsp.

(in-package "ACL2")

(set-guard-checking :none)

(program)
(set-state-ok t)

(defun rt-text (x) (coerce (reverse (bm-obj x nil)) 'string))

(defun rt-kwote-lst (args)
  (if (endp args) nil (cons (kwote (car args)) (rt-kwote-lst (cdr args)))))

(defun rt-lines (calls terms values state)
  (if (endp calls)
      (mv (reverse terms) (reverse values) state)
    (let ((term (cons (car (car calls)) (rt-kwote-lst (cdr (car calls))))))
      (mv-let (erp val state)
        (trans-eval term 'rt-expect state t)
        (rt-lines (cdr calls)
                  (cons (rt-text term) terms)
                  (cons (if erp "no value" (rt-text (cdr val))) values)
                  state)))))

(defun rt-expect (in out state)
  (mv-let (erp calls state)
    (read-file in state)
    (if erp
        (mv erp nil state)
      (mv-let (terms values state)
        (rt-lines calls nil nil state)
        (let ((state (bm-write-file terms (concatenate 'string out ".terms")
                                    state)))
          (let ((state (bm-write-file values
                                      (concatenate 'string out ".values")
                                      state)))
            (mv nil (len calls) state)))))))
