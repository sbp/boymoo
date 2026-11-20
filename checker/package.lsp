; The package of the checker.  Every book of checker/ is certified with
; this form in its portcullis; checker/build.sh says how.

(in-package "ACL2")

(defpkg "BOYMOO"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
