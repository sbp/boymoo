; The package of the prover.  Every book of prover/ is loaded and
; certified after this form.

(in-package "ACL2")

(defpkg "BOYMOO-PROVER"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
