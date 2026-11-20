; The one version of ACL2 under which the checks and the exporter run.
; This file is the only place that names it.
;
; checks/run.sh and export/book.sh have ACL2 load this file first, in a
; run that they make anyway.  Under any other version it prints a line
; that begins "version: " and ends ACL2 at once with exit status 3; the
; script then prints that line and stops with the same status.
;
; The scripts read properties of ACL2's world, which can change from one
; version to the next without notice: ACL2 8.7, for example, stores the
; constraint of an encapsulate under the property CONSTRAINT-LST-ETC,
; where ACL2 8.6 stored it under CONSTRAINT-LST.  Under another version
; they could give a wrong answer and report no error.

(in-package "ACL2")

(let ((version "ACL2 Version 8.7"))
  (if (equal (@ acl2-version) version)
      :version-ok
    (prog2$ (cw "~%version: needs ~s0, not ~s1~%" version (@ acl2-version))
            (good-bye 3))))
