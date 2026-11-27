(in-package "BOYMOO-COMPILER")

(include-book "../lower")
(include-book "l1-well-formed")
(include-book "qir-semantics")
(include-book "word-properties")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable low-term low-terms low-bind qir-eval-step l1-eval-step))

(defthmd p3-lower-constant-definition
  (equal (lower-def (list name formals (list :const word)))
         (list :fn name (low-temps 0 (len formals))
               (list (list 0 nil nil (list :ret (cons :k word))))))
  :hints (("Goal" :expand ((:free (env st)
                            (low-term (list :const word) env t name nil st))))))

(defthm p3-parameter-count
  (equal (len (low-temps first count)) (nfix count)))

(local
 (defthm p3-low-bits-of-a-word
   (implies (unsigned-byte-p 64 word) (equal (low-bits word 64) word))
   :hints (("Goal" :use (:instance model-word-in-range (x word))
            :in-theory (disable low-bits model-word-in-range)))))

(defthmd p3-lower-constant-branch
  (implies (unsigned-byte-p 64 word)
           (let ((branch (if (equal word 34) no yes)))
             (and (equal (mv-nth 0 (low-term (list :if (list :const word) yes no)
                                             env tail name loop st))
                         (mv-nth 0 (low-term branch env tail name loop st)))
                  (equal (mv-nth 1 (low-term (list :if (list :const word) yes no)
                                             env tail name loop st))
                         (mv-nth 1 (low-term branch env tail name loop st))))))
  :hints (("Goal"
           :expand ((:free (w) (low-term (list :if (list :const w) yes no) env tail name loop st))
                    (:free (w) (low-term (list :const w) env nil name loop st)))
           :in-theory (disable low-bits)
           :do-not-induct t)))

(defthmd p3-constant-definition-preserves-value
  (let* ((definitions (list (list name formals (list :const word))))
         (qir (lower-definitions definitions)))
    (implies (and (natp fuel) (<= 4 fuel) (unsigned-byte-p 64 word)
                  (equal (len formals) (len args)))
             (and (equal (mv-nth 0 (qir-run name args qir :a program heap fuel))
                         (l1-call name args definitions (model-heap-objects heap) program fuel))
                  (equal (mv-nth 1 (qir-run name args qir :a program heap fuel)) heap))))
  :hints (("Goal" :in-theory (enable p3-lower-constant-definition qir-phi-bindings qir-operand)
           :expand ((:free (input fns frame steps)
                     (qir-eval-step :call input fns :a program frame heap steps))
                    (:free (input fns frame steps)
                     (qir-eval-step :block input fns :a program frame heap steps))
                    (:free (input fns frame steps)
                     (qir-eval-step :insts input fns :a program frame heap steps))
                    (:free (input fns frame steps)
                     (qir-eval-step :jump input fns :a program frame heap steps))
                    (:free (defs constants steps)
                     (l1-eval-step :call name args defs constants program steps))
                    (:free (env defs constants steps)
                     (l1-eval-step :term (list :const word) env defs constants program steps)))
           :do-not-induct t)))

(defthmd p3-nullary-constant-function-is-qir-a
  (implies (and (stringp name) (unsigned-byte-p 64 word))
           (qir-a-p (lower-definitions (list (list name nil (list :const word))))))
  :hints (("Goal" :in-theory (enable p3-lower-constant-definition)
           :do-not-induct t)))

(assert-event
 (let* ((definitions '(("ACL2::CHOOSE" (0)
                        (:let (1) ((:if (:var 0) (:const 3) (:const 5)))
                          (:prim "ACL2::BINARY-+" ((:var 1) (:const 7)))))))
        (fns (lower-definitions definitions)))
   (mv-let (yes yes-heap)
     (qir-run "ACL2::CHOOSE" '(t) fns :a nil nil 40)
     (declare (ignore yes-heap))
     (mv-let (no no-heap)
       (qir-run "ACL2::CHOOSE" '(nil) fns :a nil nil 40)
       (declare (ignore no-heap))
       (and (qir-a-p fns)
            (equal yes (l1-call "ACL2::CHOOSE" '(t) definitions nil nil 40))
            (equal no (l1-call "ACL2::CHOOSE" '(nil) definitions nil nil 40)))))))
