(in-package "BOYMOO-COMPILER")

(include-book "values")

(logic)
(set-verify-guards-eagerness 0)

; Fuel bounds recursive evaluation depth. A result is a Core value,
; :no-value, :out-of-fuel, or :malformed for an invalid model input.
(defund l1-eval-step (kind input env definitions constants program fuel)
  (declare (xargs :measure (nfix fuel) :ruler-extenders :all))
  (if (zp fuel)
      :out-of-fuel
    (let ((next (1- fuel)))
      (case kind
        (:term
         (case (car input)
           (:var (let ((binding (assoc-equal (cadr input) env)))
                   (if binding (boymoo-model::core-value (cdr binding)) :malformed)))
           (:const (model-constant (cadr input) constants))
           (:if (let ((test (l1-eval-step :term (cadr input) env definitions
                                           constants program next)))
                  (if (boymoo-model::core-value-p test)
                      (l1-eval-step :term (if (boymoo-model::core-datum test)
                                                 (caddr input)
                                               (cadddr input))
                                       env definitions constants program next)
                    test)))
           (:let (let ((args (l1-eval-step :terms (caddr input) env definitions
                                             constants program next)))
                   (cond ((not (boymoo-model::core-value-p args)) args)
                         ((not (equal (len (cadr input))
                                      (len (boymoo-model::core-datum args))))
                          :malformed)
                         (t (l1-eval-step :term (cadddr input)
                                             (append (pairlis$ (cadr input)
                                                               (boymoo-model::core-datum args))
                                                     env)
                                             definitions constants program next)))))
           ((:call :prim :undef)
            (let ((args (l1-eval-step :terms (caddr input) env definitions
                                        constants program next)))
              (if (not (boymoo-model::core-value-p args))
                  args
                (let ((values (boymoo-model::core-datum args)))
                  (case (car input)
                    (:call (l1-eval-step :call (cadr input) values definitions
                                            constants program next))
                    (:prim (model-routine (cadr input) values program))
                    (otherwise :no-value))))))
           (otherwise :malformed)))
        (:terms
         (if (endp input)
             (boymoo-model::core-value nil)
           (let ((first (l1-eval-step :term (car input) env definitions
                                         constants program next)))
             (if (not (boymoo-model::core-value-p first))
                 first
               (let ((rest (l1-eval-step :terms (cdr input) env definitions
                                            constants program next)))
                 (if (boymoo-model::core-value-p rest)
                     (boymoo-model::core-value
                      (cons (boymoo-model::core-datum first)
                            (boymoo-model::core-datum rest)))
                   rest))))))
        (:call
         (let ((definition (assoc-equal input definitions)))
           (if (and definition (equal (len (cadr definition)) (len env)))
               (l1-eval-step :term (caddr definition) (pairlis$ (cadr definition) env)
                                definitions constants program next)
             :malformed)))
        (otherwise :malformed)))))

(defun l1-eval (term env definitions constants program fuel)
  (l1-eval-step :term term env definitions constants program fuel))

(defun l1-call (name args definitions constants program fuel)
  (l1-eval-step :call name args definitions constants program fuel))

(defthmd l1-eval-step-more-fuel
  (implies (not (eq (l1-eval-step kind input env definitions constants program fuel)
                    :out-of-fuel))
           (equal (l1-eval-step kind input env definitions constants program
                                   (+ (nfix extra) (nfix fuel)))
                  (l1-eval-step kind input env definitions constants program fuel)))
  :hints (("Goal" :induct (l1-eval-step kind input env definitions constants program fuel)
           :in-theory (enable l1-eval-step))))

(defthmd l1-eval-of-constant
  (implies (posp fuel)
           (equal (l1-eval (list :const word) env definitions constants program fuel)
                  (model-constant word constants)))
  :hints (("Goal" :in-theory (enable l1-eval-step))))

(assert-event
 (equal (l1-eval '(:let (2 3) ((:const 15) (:var 2))
                     (:prim "ACL2::BINARY-+" ((:var 2) (:var 3))))
                    '((2 . 11)) nil nil nil 20)
        (boymoo-model::core-value 18)))

(assert-event
 (equal (l1-call "ACL2::MAIN" '(nil)
                    '(("ACL2::MAIN" (0)
                       (:if (:var 0) (:undef 82 ()) (:const 7))))
                    nil nil 20)
        (boymoo-model::core-value 3)))

(assert-event
 (equal (l1-eval '(:undef 82 ()) nil nil nil nil 2) :no-value))
