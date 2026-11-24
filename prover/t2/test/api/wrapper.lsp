; Run with sh prover/t2/build.sh --run-acl2 1800 < prover/t2/test/api/wrapper.lsp.

(set-ld-error-action '(:exit 1) state)
(ld "prover/package.lsp" :ld-error-action :error)
(in-package "BOYMOO-PROVER")
(set-guard-checking :none)
(set-verify-guards-eagerness 0)
(set-inhibit-output-lst '(proof-tree prove warning observation event summary))
(ld "prover/basics.lisp" :ld-skip-proofsp t :ld-error-action :error)

; The engine responses exercise a proof, an empty answer, and a failure.
(defun t2-api-engine-prove (statement earlier library aids prefix)
  (cond ((equal statement "failure") '(:failure "failure" ""))
        ((equal statement "skip") nil)
        (t (list (list prefix statement earlier library aids) "entry"))))

(ld "prover/t2/api.lisp" :ld-error-action :error)
(assert-event
 (equal (t2-api-prove "statement" '("earlier") "library" '("aid"))
        '(("T2" "statement" ("earlier") "library" ("aid")) "entry")))
(assert-event (equal (t2-api-prove "skip" nil nil nil) nil))
(assert-event (equal (t2-api-prove "failure" nil nil nil) nil))
(value-triple :t2-api-wrapper-passed)
(good-bye)
