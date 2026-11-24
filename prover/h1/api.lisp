(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-api-prefix* "H1")

(defun h1-api-prove (statement earlier library aids)
  (let ((result (h1-api-engine-prove statement earlier library aids)))
    (if (failure-p result)
        nil
      result)))
