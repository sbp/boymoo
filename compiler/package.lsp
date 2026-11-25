(in-package "ACL2")

; The compiler books share the ACL2 Core functions and the names of the
; Common Lisp package.
(defpkg "BOYMOO-COMPILER"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
