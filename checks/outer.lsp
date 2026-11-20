; This script certifies build/outer.lisp, a copy of checks/outer.lisp,
; in the world ACL2 starts with.  It is run from the root of the
; repository by checks/run.sh, after checks/hidden.lsp.

(in-package "ACL2")

(certify-book "build/outer" 0 nil)

(good-bye)
