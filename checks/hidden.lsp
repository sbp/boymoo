; This script certifies build/hidden.lisp, a copy of checks/hidden.lisp,
; in a world that declares the package BM-HIDDEN.  It is run from the
; root of the repository by checks/run.sh.

(in-package "ACL2")

(defpkg "BM-HIDDEN" '(common-lisp::car acl2::bm-hidden-import))

(certify-book "build/hidden" 1 nil)

(good-bye)
