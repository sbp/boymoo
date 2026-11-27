(in-package "BOYMOO-COMPILER")

(include-book "../opt")
(include-book "qir-semantics")
(include-book "word-properties")

(logic)
(set-verify-guards-eagerness 0)

(defthm p5-optimizer-word-is-model-word
  (implies (integerp x) (equal (opt-word x) (model-word x)))
  :hints (("Goal" :in-theory (disable low-bits))))

(in-theory (disable opt-word model-word low-bits))

(defthm p5-folds-addition-as-word-operation
  (implies (and (unsigned-byte-p 64 a) (unsigned-byte-p 64 b))
           (equal (opt-binary-word :add a b) (model-word-op :add a b)))
  :hints (("Goal" :in-theory (enable model-word-op))))

(defthmd p5-signed-word-agrees
  (implies (unsigned-byte-p 64 x)
           (equal (opt-signed x) (model-signed x))))

(defthmd p5-overflow-test-agrees
  (implies (integerp x)
           (equal (opt-signed-overflow-p x) (not (signed-byte-p 64 x))))
  :hints (("Goal" :in-theory (enable signed-byte-p integer-range-p))))

(local
 (defthm p5-signed-word-is-integer
   (integerp (model-signed x))
   :rule-classes :type-prescription))

(defthmd p5-folds-arithmetic-and-comparison-word-operations
  (implies (and (qir-word-op-p op) (not (member-equal op '(:and :or)))
                (unsigned-byte-p 64 a) (unsigned-byte-p 64 b))
           (equal (opt-binary-word op a b) (model-word-op op a b)))
  :hints (("Goal" :in-theory (e/d (model-word-op p5-signed-word-agrees
                                   p5-overflow-test-agrees)
                                  (opt-signed model-signed opt-signed-overflow-p))
           :do-not-induct t)))

(defthmd p5-constant-addition-replacement-preserves-value
  (implies (and (unsigned-byte-p 64 a) (unsigned-byte-p 64 b))
           (let* ((inst (list dest :add (cons :k a) (cons :k b)))
                  (replacement (opt-inst-replacement inst))
                  (args (qir-operands (qir-inst-uses inst) env :m heap)))
             (equal (qir-operand replacement env :m heap)
                    (mv-nth 0 (qir-compute inst (boymoo-model::core-datum args)
                                             slots nslots :m heap program)))))
  :hints (("Goal" :in-theory (enable qir-compute qir-operand qir-operands model-word-op)
           :do-not-induct t)))

(defthmd p5-copy-replacement-preserves-value
  (implies (boymoo-model::core-value-p (qir-operand operand env :m heap))
           (let* ((inst (list dest :copy operand))
                  (args (qir-operands (qir-inst-uses inst) env :m heap)))
             (equal (qir-operand (opt-inst-replacement inst) env :m heap)
                    (mv-nth 0 (qir-compute inst (boymoo-model::core-datum args)
                                             slots nslots :m heap program)))))
  :hints (("Goal" :in-theory (enable qir-compute qir-operands qir-operand))))

(defthmd p5-unused-word-computation-has-no-effects
  (implies (qir-word-op-p op)
           (and (equal (mv-nth 1 (qir-compute (list dest op a b) args slots nslots :m heap program)) slots)
                (equal (mv-nth 2 (qir-compute (list dest op a b) args slots nslots :m heap program)) heap)))
  :hints (("Goal" :in-theory (enable qir-compute))))

(defthmd p5-dead-word-computation-is-removed
  (implies (and (qir-word-op-p op) (not (qir-get (cdr dest) marked)))
           (equal (opt-live-insts (cons (list dest op a b) rest) marked)
                  (opt-live-insts rest marked))))

(defthmd p5-select-agrees-with-single-phi
  (let* ((yes-operand (qir-phi-arg phi yes))
         (no-operand (qir-phi-arg phi no))
         (condition (qir-operand test env :m heap))
         (yes-value (qir-operand yes-operand env :m heap))
         (no-value (qir-operand no-operand env :m heap))
         (selected (if (equal (boymoo-model::core-datum condition) 0) no yes))
         (inst (list (qir-phi-dest phi) :sel test yes-operand no-operand)))
    (implies (and (boymoo-model::core-value-p condition)
                  (boymoo-model::core-value-p yes-value)
                  (boymoo-model::core-value-p no-value))
             (equal (mv-nth 0
                      (qir-compute inst (list (boymoo-model::core-datum condition)
                                                 (boymoo-model::core-datum yes-value)
                                                 (boymoo-model::core-datum no-value))
                                      slots nslots :m heap program))
                    (boymoo-model::core-value
                     (cdar (boymoo-model::core-datum
                            (qir-phi-bindings (list phi) selected env :m heap)))))))
  :hints (("Goal" :in-theory (enable qir-compute qir-phi-bindings))))

(defthmd p5-convert-diamond-uses-phi-arguments
  (let* ((phi (list dest (list (cons 1 yes-operand) (cons 2 no-operand))))
         (blocks (list (list 0 nil nil (list :jnz test 1 2))
                       '(1 nil nil (:jmp 3)) '(2 nil nil (:jmp 3))
                       (list 3 (list phi) nil (list :ret dest))))
         (after (mv-nth 0 (opt-convert-diamond 0 (qir-block-map blocks nil) (qir-preds blocks))))
         (entry (qir-get 0 after)))
    (and (equal (qir-block-insts entry) (list (list dest :sel test yes-operand no-operand)))
         (equal (qir-block-jump entry) '(:jmp 3))
         (not (qir-block-phis (qir-get 3 after)))
         (not (qir-get 1 after)) (not (qir-get 2 after))))
  :hints (("Goal" :do-not-induct t)))

(assert-event
 (let* ((before '((:fn "ACL2::MAIN" ()
                   ((0 nil (((:w . 0) :add (:k . 3) (:k . 4))
                            ((:w . 1) :mul (:k . 9) (:k . 7))
                            ((:d . 2) :copy (:w . 0)))
                       (:ret (:d . 2)))))))
        (after (opt-program before)))
   (mv-let (reference reference-heap)
     (qir-run "ACL2::MAIN" nil before :m nil nil 30)
     (declare (ignore reference-heap))
     (mv-let (result heap)
       (qir-run "ACL2::MAIN" nil after :m nil nil 30)
       (declare (ignore heap))
       (and (qir-m-p before) (qir-m-p after) (equal reference result))))))
