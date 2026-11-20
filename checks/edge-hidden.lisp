; A book for the check of EDGE-CASES.md.  checks/run.sh copies it into
; build/ and certifies it there.  It includes the book hidden locally,
; so that ACL2 keeps the package BM-HIDDEN hidden wherever this book is
; included, and it defines a function whose value is a symbol of that
; package.  The symbol is made while the package is known, by
; make-event, because ACL2 reads the whole book before it includes
; anything.

(in-package "ACL2")

(local (include-book "hidden"))

(make-event
 (list 'defun 'bm-hidden-symbol '()
       (list 'quote (intern$ "FOO" "BM-HIDDEN"))))
