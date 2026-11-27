(in-package "BOYMOO-COMPILER")

(include-book "../simplify")
(include-book "l1-well-formed")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable simplify-term simplify-terms simplify-live-term
                    l1-eval-step model-constant table-tree-get))

(defthmd p2-simplify-nil-test
  (and (equal (mv-nth 0 (simplify-term (list :if (list :const 34) yes no)
                                          offset aliases facts inlinees depth next))
              (mv-nth 0 (simplify-term no offset aliases facts inlinees depth next)))
       (equal (mv-nth 1 (simplify-term (list :if (list :const 34) yes no)
                                          offset aliases facts inlinees depth next))
              (mv-nth 1 (simplify-term no offset aliases facts inlinees depth next))))
  :hints (("Goal" :expand ((simplify-term (list :if (list :const 34) yes no)
                                             offset aliases facts inlinees depth next)
                           (simplify-term (list :const 34) offset aliases facts inlinees depth next)))))

(defthmd p2-simplify-nil-test-preserves-literal-result
  (implies (and (natp fuel) (<= 2 fuel))
           (let ((term (list :if (list :const 34) yes (list :const datum))))
             (equal (l1-eval (mv-nth 0 (simplify-term term offset aliases facts inlinees depth next))
                                env definitions constants program fuel)
                    (l1-eval term env definitions constants program fuel))))
  :hints (("Goal" :expand ((simplify-term (list :const datum) offset aliases facts inlinees depth next))
           :in-theory (enable p2-simplify-nil-test l1-eval-step))))

(defthmd p2-fold-reflexive-equality-preserves-result
  (implies (and (natp fuel) (<= 4 fuel)
                (boymoo-model::core-value-p (model-constant word constants)))
           (let* ((args (list (list :const word) (list :const word)))
                  (name "COMMON-LISP::EQUAL"))
             (equal (l1-eval (simplify-primitive name args) env definitions constants program fuel)
                    (l1-eval (list :prim name args) env definitions constants program fuel))))
  :hints (("Goal" :in-theory (enable l1-eval-step model-routine boymoo-model::core-primitive)
           :expand ((:free (input args-env steps)
                     (l1-eval-step :term input args-env definitions constants program steps))
                    (:free (input args-env steps)
                     (l1-eval-step :terms input args-env definitions constants program steps)))
           :do-not-induct t)))

(defthmd p2-unused-constant-binding-preserves-literal-result
  (implies (and (natp fuel) (<= 3 fuel)
                (boymoo-model::core-value-p (model-constant unused constants)))
           (let ((term (list :let (list slot) (list (list :const unused)) (list :const datum))))
             (equal (l1-eval (mv-nth 0 (simplify-live-term term nil))
                                env definitions constants program fuel)
                    (l1-eval term env definitions constants program fuel))))
  :hints (("Goal" :expand ((simplify-live-term
                            (list :let (list slot) (list (list :const unused)) (list :const datum)) nil)
                           (simplify-live-term (list :const datum) nil)
                           (:free (input args-env steps)
                            (l1-eval-step :term input args-env definitions constants program steps))
                           (:free (input args-env steps)
                            (l1-eval-step :terms input args-env definitions constants program steps)))
           :in-theory (enable l1-eval-step table-tree-get))))

(assert-event
 (let* ((definitions '(("ACL2::MAIN" (0)
                        (:if (:const 34) (:undef 82 ()) (:call "ACL2::ID" ((:var 0)))))
                       ("ACL2::ID" (0) (:var 0))))
        (simplified (simplify-definitions definitions)))
   (and (l1-program-p simplified)
        (equal (l1-call "ACL2::MAIN" '(31) simplified nil nil 30)
               (l1-call "ACL2::MAIN" '(31) definitions nil nil 30)))))
