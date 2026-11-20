; A book for the check of EDGE-CASES.md that is never certified.
; checks/run.sh copies it into build/, and checks/edge.lsp includes it
; without a certificate: ACL2 then admits its theorem without a proof.

(in-package "ACL2")

(defthm bm-false (equal 1 2) :rule-classes nil)
