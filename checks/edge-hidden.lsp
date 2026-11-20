; This script certifies build/edge-hidden.lisp, a copy of
; checks/edge-hidden.lisp, in the world ACL2 starts with.  It is run from
; the root of the repository by checks/run.sh, after checks/hidden.lsp.

(in-package "ACL2")

(certify-book "build/edge-hidden" 0 nil)

(good-bye)
