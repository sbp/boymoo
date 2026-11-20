; A book for the check of hidden packages.  It includes the book hidden
; locally, so that its certificate records the package BM-HIDDEN as one
; that ACL2 must keep, hidden, wherever this book is included.
; checks/run.sh copies it into build/ and certifies it there.

(in-package "ACL2")

(local (include-book "hidden"))

(defun bm-outer-function (x) x)
