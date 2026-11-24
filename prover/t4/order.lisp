(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defund t4-order-unfold-return-last-step (proof equation)
  (proof-with-checked-results
      ((literal (proof-step-first equation))
       (body (proof-term-at literal 2)))
    (if (proof-is-call body *termination-return-last*)
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof body))
             (next (proof-proof-chain proof equation (list opened))))
          (cons :continue next))
      equation)))

(defun t4-order-unfold-return-last (n proof equation)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t4-order-unfold-return-last")
    (let ((next (t4-order-unfold-return-last-step proof equation)))
      (if (eq (car next) :continue)
          (t4-order-unfold-return-last (1- n) proof (cdr next))
        next))))

(defun t4-order-strict-equation (lib relation)
  (let ((proof (library-library-proof lib)))
    (and (proof-compound relation)
         (equal (len relation) 3)
         (assoc-equal (car relation) (proof-proof-definitions proof))
      (proof-with-checked-results
          ((opened (proof-proof-unfold proof relation))
           (equation (t4-order-unfold-return-last 1000000 proof opened))
           (literal (proof-step-first equation))
           (body (proof-term-at literal 2)))
        (let ((x (cadr relation))
              (y (caddr relation)))
          (and (proof-is-call body *proof-if*)
               (equal (cddr body)
                      (list (proof-neg (proof-eq x y)) *proof-false*))
               (proof-compound (cadr body))
               (equal (cdadr body) (list x y))
            equation))))))

(defun t4-order-imply (lib antecedent consequent)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first consequent))
         (equation (proof-proof-unfold proof
                     (list *library-implies* antecedent literal)))
         (first (proof-step-first equation))
         (body (proof-term-at first 2))
         (assumed (proof-proof-assume proof antecedent t))
         (selected (proof-proof-select proof body assumed))
         (inner (proof-term-at body 2))
         (conclusion (proof-proof-select proof inner consequent))
         (yes (proof-proof-chain proof equation (list selected conclusion)))
         (denied (proof-proof-if-false proof body))
         (no (proof-proof-chain proof equation (list denied)))
         (yes (proof-proof-true-from-eq proof yes))
         (no (proof-proof-true-from-eq proof no)))
      (proof-proof-cases proof antecedent yes no))))

(defun t4-order-request-p (value)
  (and (consp value) (eq (car value) :t4-order-request)))

(defun t4-order-request-operation (request)
  (cadr request))

(defun t4-order-request-arguments (request)
  (caddr request))

(defun t4-order-request-library (request)
  (cadddr request))

(defund t4-order-reply (operation arguments lib replies)
  (cond ((endp replies) (list :t4-order-request operation arguments lib))
        ((failure-p (car replies)) (car replies))
        (t replies)))

(defmacro t4-order-with-reply (binding result)
  (let ((name (car binding))
        (request (cadr binding)))
    `(let ((,name ,request))
       (if (or (failure-p ,name) (t4-order-request-p ,name))
           ,name
         ,result))))

(defun t4-order-strict-order-parts (step lib order-name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first step))
         (opening (t4-order-strict-equation lib first)))
      (if (or (not opening)
              (not (equal (caadr (caddr (proof-step-first opening))) order-name)))
          '(:failure "SearchMiss" "")
        (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step opening '(1))))
          (proof-proof-conjunct proof rewritten))))))

(defun t4-order-strict-order-introduce (opening ordered unequal lib replies)
  (proof-with-checked-results
      ((literal (proof-step-first opening))
       (body (proof-term-at literal 2)))
    (t4-order-with-reply
        (answer (t4-order-reply :prove (list body (list ordered unequal) nil) lib replies))
      (let ((lib (cdar answer)))
        (proof-with-checked-results
            ((step (proof-proof-transport (library-library-proof lib) (caar answer) opening)))
          (cons (cons step lib) (cdr answer)))))))

(defun t4-order-strict-order-refute (test yes no lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((step (proof-proof-cut proof yes no)))
      (let ((denied (proof-neg test))
            (clause (proof-step-clause step)))
        (if (member-equal denied clause)
            (proof-proof-front proof step denied)
          (proof-proof-subsume proof step (cons denied clause)))))))

(defun t4-order-strict-order-rule (formula premises lib replies)
  (t4-order-with-reply
      (answer (t4-order-reply :fact-proof (list formula premises) lib replies))
    (if (caar answer)
        answer
      '(:failure "SearchMiss" ""))))

(defun t4-order-negated-reflexivity (lib relation x order-name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof relation t))
         (parts (t4-order-strict-order-parts assumed lib order-name))
         (same (proof-proof-reflexive proof x))
         (step (t4-order-strict-order-refute relation same (cadr parts) lib)))
      (cons step lib))))

(defun t4-order-negated-reverse (lib premise relation x z order-name replies)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof premise t))
         (forward (t4-order-strict-order-parts assumed lib order-name))
         (assumed (proof-proof-assume proof relation t))
         (reverse (t4-order-strict-order-parts assumed lib order-name)))
      (t4-order-with-reply
          (answer (t4-order-strict-order-rule
                   (proof-eq z x) (list (car forward) (car reverse)) lib replies))
        (let ((lib (cdar answer)))
          (proof-with-checked-results
              ((denied (t4-order-strict-order-refute relation
                         (caar answer) (cadr forward) lib))
               (step (t4-order-imply lib premise denied)))
            (cons step lib)))))))

(defun t4-order-transitive (lib premise x mid z order-name equation parts replies)
  (proof-with-checked-results
      ((left (t4-order-strict-order-parts (car parts) lib order-name))
       (right (t4-order-strict-order-parts (cadr parts) lib order-name)))
    (t4-order-with-reply
        (ordered (t4-order-strict-order-rule (list order-name x z)
                   (list (car left) (car right)) lib replies))
      (let* ((lib (cdar ordered))
             (proof (library-library-proof lib))
             (same (proof-eq x z)))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof same t))
             (back (proof-proof-symmetric proof assumed))
             (reverse (proof-proof-rewrite proof (car right) back '(1 2))))
          (t4-order-with-reply
              (sameness (t4-order-strict-order-rule (proof-eq x mid)
                          (list (car left) reverse) lib (cdr ordered)))
            (let ((lib (cdar sameness)))
              (proof-with-checked-results
                  ((unequal (t4-order-strict-order-refute same
                              (caar sameness) (cadr left) lib)))
                (t4-order-with-reply
                    (introduced (t4-order-strict-order-introduce
                                 equation (caar ordered) unequal lib (cdr sameness)))
                  (let ((lib (cdar introduced)))
                    (proof-with-checked-results
                        ((step (t4-order-imply lib premise (caar introduced))))
                      (cons step lib))))))))))))

(defun t4-order-total-from-match (lib premise equation reverse-equation
                                  ordered reverse-neq parts name bindings replies)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof name (table-items bindings)))
         (assumed (proof-proof-assume proof ordered nil))
         (reverse (proof-proof-prove-if proof fact assumed)))
      (t4-order-with-reply
          (introduced (t4-order-strict-order-introduce reverse-equation reverse
                       reverse-neq lib replies))
        (let* ((lib (cdar introduced))
               (proof (library-library-proof lib)))
          (proof-with-checked-results
              ((impossible (proof-proof-cut proof (caar introduced) (car parts)))
               (ordered (proof-proof-front proof impossible ordered)))
            (t4-order-with-reply
                (introduced (t4-order-strict-order-introduce equation ordered
                             (cadr parts) lib (cdr introduced)))
              (let ((lib (cdar introduced)))
                (proof-with-checked-results
                    ((step (t4-order-imply lib premise (caar introduced))))
                  (cons step lib))))))))))

(defun t4-order-find-total (facts lib total premise equation reverse-equation
                            ordered reverse-neq parts replies)
  (if (endp facts)
      (cons nil lib)
    (let* ((fact (car facts))
           (clause (cdr fact))
           (pattern (car clause)))
      (if (and (equal (len clause) 1) (proof-is-call pattern *proof-if*))
          (t4-order-with-reply
              (answer (t4-order-reply :match (list pattern total) lib replies))
            (if (caar answer)
                (t4-order-total-from-match lib premise equation reverse-equation
                 ordered reverse-neq parts (car fact) (cdar answer) (cdr answer))
              (t4-order-find-total (cdr facts) lib total premise equation reverse-equation
               ordered reverse-neq parts (cdr answer))))
        (t4-order-find-total (cdr facts) lib total premise equation reverse-equation
         ordered reverse-neq parts replies)))))

(defun t4-order-total (lib premise equation x z reverse order-name parts replies)
  (let* ((proof (library-library-proof lib))
         (reverse-same (proof-eq z x)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof reverse-same t))
         (symmetric (proof-proof-symmetric proof assumed))
         (reverse-neq (t4-order-strict-order-refute reverse-same symmetric (cadr parts) lib))
         (reverse-equation (t4-order-strict-equation lib reverse)))
      (if (not reverse-equation)
          (cons nil lib)
        (let* ((ordered (list order-name x z))
               (reversed-order (list order-name z x))
               (total (proof-ite ordered ordered reversed-order)))
          (t4-order-find-total (proof-proof-facts proof) lib total premise equation
           reverse-equation ordered reverse-neq parts replies))))))

(defun t4-order-positive-case (lib premise equation relation-name x z order-name replies)
  (let ((proof (library-library-proof lib))
        (first (cadr premise))
        (second (caddr premise)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof premise t))
         (parts (proof-proof-conjunct proof assumed)))
      (proof-with-checked-results
          ((mid (and (proof-is-call first relation-name)
                     (proof-is-call second relation-name)
                  (proof-with-checked-results ((left (proof-term-at first 1)))
                    (and (equal left x)
                      (proof-with-checked-results ((mid (proof-term-at first 2)))
                        (and (equal (cdr second) (list mid z))
                          (list mid))))))))
        (if mid
            (t4-order-transitive lib premise x (car mid) z order-name equation parts replies)
          (let ((reverse (list relation-name z x))
                (same (proof-eq x z)))
            (if (and (equal first (proof-neg reverse))
                     (equal second (proof-neg same)))
                (t4-order-total lib premise equation x z reverse order-name parts replies)
              (cons nil lib))))))))

(defun t4-order-strict-order (lib claim replies)
  (proof-with-checked-results
      ((parts (if (proof-is-call claim *library-implies*)
                  (proof-list-of-length (cdr claim) 2)
                (list :none claim))))
    (let* ((premise (car parts))
           (goal (cadr parts))
           (negative (proof-is-call goal *proof-not*)))
      (proof-with-checked-results
          ((relation (if negative (proof-term-at goal 1) goal))
           (equation (t4-order-strict-equation lib relation)))
        (if (not equation)
            (cons nil lib)
          (let* ((relation-name (car relation))
                 (x (cadr relation))
                 (z (caddr relation))
                 (order-name (caadr (caddr (proof-step-first equation)))))
            (cond
             ((and negative (eq premise :none) (equal x z))
              (t4-order-negated-reflexivity lib relation x order-name))
             ((and negative (equal premise (list relation-name z x)))
              (t4-order-negated-reverse lib premise relation x z order-name replies))
             ((or negative (not (proof-is-call premise *proof-if*))) (cons nil lib))
             (t (proof-with-checked-results ((no (proof-term-at premise 3)))
                  (if (equal no *proof-false*)
                      (t4-order-positive-case lib premise equation relation-name
                       x z order-name replies)
                    (cons nil lib)))))))))))
