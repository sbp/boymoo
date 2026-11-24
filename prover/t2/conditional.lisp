(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t2-conditional-shared-test (arguments test)
  (if (endp arguments)
      nil
    (let ((arg (car arguments)))
      (if (proof-is-call arg *proof-if*)
          (proof-with-checked-results ((arg-test (proof-term-at arg 1)))
            (or (equal arg-test test)
                (t2-conditional-shared-test (cdr arguments) test)))
        (t2-conditional-shared-test (cdr arguments) test)))))

(defun t2-conditional-branch (proof application result test holds)
  (proof-with-checked-results
      ((premise (proof-proof-assume proof test holds))
       (left (t2-arithmetic-simplify proof application (list premise) nil))
       (right (t2-arithmetic-simplify proof result (list premise) nil)))
    (and left right
         (proof-with-checked-results
             ((left-first (proof-step-first left))
              (left-value (proof-term-at left-first 2))
              (right-first (proof-step-first right))
              (right-value (proof-term-at right-first 2)))
           (and (equal left-value right-value)
                (proof-with-checked-results ((reverse (proof-proof-symmetric proof right)))
                  (proof-proof-chain proof left (list reverse))))))))

(defun t2-conditional-prove-branches (lib condition application result test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((yes (t2-conditional-branch proof application result test t)))
      (and yes
           (proof-with-checked-results ((no (t2-conditional-branch proof application result test nil)))
             (and no
                  (proof-with-checked-results ((step (proof-proof-cases proof test yes no)))
                    (if (eq condition :none)
                        step
                      (t2-power-implication lib condition step)))))))))

(defun t2-conditional-prove-claim (lib condition claim)
  (and (proof-is-call claim *proof-equal*)
       (proof-with-checked-results ((parts (proof-list-of-length (cdr claim) 2)))
         (let* ((application (car parts))
                (result (cadr parts))
                (head (and (proof-is-call result *proof-if*) (t2-book-logic-head application))))
           (and head (not (equal head 0))
                (proof-with-checked-results
                    ((test (proof-term-at result 1))
                     (shared (t2-conditional-shared-test (cdr application) test)))
                  (and shared (t2-conditional-prove-branches lib condition application result test))))))))

(defun t2-conditional-prove (lib formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
        (t2-conditional-prove-claim lib (car parts) (cadr parts)))
    (t2-conditional-prove-claim lib :none formula)))

(defun t2-conditional-default-value (lib domain outside-domain)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first outside-domain))
         (parts (if (integerp literal)
                    '(:failure "failure" "")
                  (proof-list-of-length (cdr literal) 2))))
      (let ((conditional (proof-ite domain (car parts) (cadr parts))))
        (proof-with-checked-results
            ((if-true (proof-proof-if-true proof conditional))
             (yes (proof-proof-symmetric proof if-true))
             (if-false (proof-proof-if-false proof conditional))
             (no (library-library-transport-argument lib outside-domain if-false 2)))
          (proof-proof-cases proof domain yes no))))))
