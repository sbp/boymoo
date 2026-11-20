; A book for the check of hidden packages.  checks/run.sh copies it into
; build/ and certifies it there, after the commands of checks/hidden.lsp,
; which declare the package BM-HIDDEN.  checks/facts.lsp then includes
; the certified book locally, so that ACL2 keeps the package hidden.

(in-package "ACL2")

(defun bm-hidden-function (x) x)
