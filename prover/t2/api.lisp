(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-api-prefix* "T2")

(defun t2-api-prove (statement earlier library aids)
  (let ((result (t2-api-engine-prove statement earlier library aids
                                    *t2-api-prefix*)))
    (if (failure-p result)
        nil
      result)))
