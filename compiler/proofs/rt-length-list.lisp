(in-package "BOYMOO-COMPILER")

(include-book "rt-semantics")

(logic)
(set-verify-guards-eagerness 0)

(defconst *rt-length-block-map*
  (qir-block-map (qir-fn-blocks (qir-function "rt-qir:LENGTH" (rt-qir-functions))) nil))

; Enter the CDR loop from its initial predecessor or from its back edge.
(defund rt-length-loop-run (pred env fns heap fuel)
  (qir-eval-step :block 3 fns :m nil
                    (qir-activation *rt-length-block-map* pred env nil nil)
                    heap fuel))

(defund rt-length-loop-inputs-p (pred word count env)
  (cond ((equal pred 2)
         (and (equal count 1)
              (equal (qir-operand '(:d . 0) env :m nil) (boymoo-model::core-value word))))
        ((equal pred 4)
         (and (equal (qir-operand '(:d . 13) env :m nil) (boymoo-model::core-value word))
              (equal (qir-operand '(:w . 14) env :m nil) (boymoo-model::core-value count))))
        (t nil)))

(defund rt-length-cdr-word (word heap)
  (model-heap-read 8 (model-word (+ word 8)) heap))

(defund rt-length-after-cons (word count tail env)
  (let* ((phis (acons '(:d . 11) word (acons '(:w . 12) count env)))
         (tag (qir-bind '(:w . 15) 0 phis))
         (saved-tail (qir-bind '(:d . 13) tail tag)))
    (qir-bind '(:w . 14) (model-word-op :add count 2) saved-tail)))

(defthmd rt-length-loop-advances-over-cons
  (implies (and (rt-length-loop-inputs-p pred word count env)
                (equal (model-word-op :and word 7) 0)
                (equal (rt-length-cdr-word word heap) (boymoo-model::core-value tail))
                (natp fuel) (<= 9 fuel))
           (equal (rt-length-loop-run pred env fns heap fuel)
                  (rt-length-loop-run 4 (rt-length-after-cons word count tail env)
                                         fns heap (- fuel 9))))
  :hints (("Goal"
           :in-theory (e/d (rt-length-loop-run rt-length-loop-inputs-p rt-length-cdr-word
                            rt-length-after-cons qir-phi-bindings qir-operand qir-operands
                            qir-compute qir-branch)
                           (qir-eval-step model-word put-assoc-equal))
           :expand ((:free (frame) (qir-eval-step :block 3 fns :m nil frame heap fuel))
                    (:free (frame remaining) (qir-eval-step :block 4 fns :m nil frame heap remaining))
                    (:free (input frame remaining) (qir-eval-step :insts input fns :m nil frame heap remaining))
                    (:free (input frame remaining) (qir-eval-step :jump input fns :m nil frame heap remaining)))
           :do-not-induct t)))

(defthmd rt-length-loop-returns-count-at-nil
  (implies (and (rt-length-loop-inputs-p pred 34 count env) (natp fuel) (<= 8 fuel))
           (equal (rt-length-loop-run pred env fns heap fuel)
                  (mv (boymoo-model::core-value count) heap)))
  :hints (("Goal"
           :in-theory (e/d (rt-length-loop-run rt-length-loop-inputs-p
                            qir-phi-bindings qir-operand qir-operands qir-compute qir-branch)
                           (qir-eval-step model-word put-assoc-equal))
           :expand ((:free (frame) (qir-eval-step :block 3 fns :m nil frame heap fuel))
                    (:free (frame remaining) (qir-eval-step :block 5 fns :m nil frame heap remaining))
                    (:free (input frame remaining) (qir-eval-step :insts input fns :m nil frame heap remaining))
                    (:free (input frame remaining) (qir-eval-step :jump input fns :m nil frame heap remaining)))
           :do-not-induct t)))

; The list spine needs readable CDR words and the NIL terminator. The
; routine ignores every CAR, so they need no byte-level premises here.
(defund rt-list-spine-p (data word heap)
  (if (atom data)
      (and (null data) (equal word 34))
    (let* ((read (rt-length-cdr-word word heap))
           (tail (boymoo-model::core-datum read)))
      (and (equal (model-word-op :and word 7) 0)
           (equal read (boymoo-model::core-value tail))
           (rt-list-spine-p (cdr data) tail heap)))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthmd rt-length-add-two-increments-encoded-count
   (implies (unsigned-byte-p 62 count)
            (equal (model-word-op :add (model-integer-word count) 2)
                   (model-integer-word (1+ count))))
   :hints (("Goal" :in-theory (e/d (model-word-op model-integer-word) (model-word))))))

(local
 (defthm rt-length-cons-leaves-next-loop-inputs
   (implies (unsigned-byte-p 62 count)
            (rt-length-loop-inputs-p 4 tail (model-integer-word (1+ count))
                                        (rt-length-after-cons word (model-integer-word count) tail env)))
   :hints (("Goal" :in-theory (e/d (rt-length-loop-inputs-p rt-length-after-cons
                                    rt-length-add-two-increments-encoded-count qir-operand)
                                   (put-assoc-equal model-integer-word model-word))))))

(local
 (defun rt-length-spine-induction (data word count env pred heap fuel)
   (if (atom data)
       (list count env pred fuel)
     (let* ((cdr-word (boymoo-model::core-datum (rt-length-cdr-word word heap)))
            (after (rt-length-after-cons word (model-integer-word count) cdr-word env)))
       (rt-length-spine-induction (cdr data) cdr-word (1+ count) after 4 heap (- fuel 9))))))

(defthmd rt-length-loop-counts-represented-list
  (let ((init (model-integer-word count))
        (total (+ count (len data))))
    (implies (and (rt-list-spine-p data word heap)
                  (rt-length-loop-inputs-p pred word init env)
                  (natp count) (unsigned-byte-p 62 total)
                  (natp fuel) (<= (+ 8 (* 9 (len data))) fuel))
             (equal (rt-length-loop-run pred env fns heap fuel)
                    (mv (boymoo-model::core-value (model-integer-word total)) heap))))
  :hints (("Goal" :induct (rt-length-spine-induction data word count env pred heap fuel)
           :in-theory (e/d (rt-list-spine-p rt-length-add-two-increments-encoded-count)
                            (model-integer-word model-word)))
          ("Subgoal *1/2"
           :use (:instance rt-length-loop-advances-over-cons
                           (count (model-integer-word count))
                           (tail (boymoo-model::core-datum (rt-length-cdr-word word heap)))))
          ("Subgoal *1/1"
           :use (:instance rt-length-loop-returns-count-at-nil (count (model-integer-word count))))))

(defund rt-length-entry-env (word header)
  (let ((tag (model-word-op :and word 7))
        (type (model-word-op :and header 255)))
    (list (cons '(:d . 0) word)
          (cons '(:w . 1) tag)
          (cons '(:w . 2) (model-word-op :ceq tag 2))
          (cons '(:d . 3) 34)
          (cons '(:w . 4) header)
          (cons '(:w . 5) type)
          (cons '(:w . 6) 0))))

(defthmd rt-length-list-call-follows-loop-result
  (let* ((fns (rt-call-functions "rt-qir:LENGTH" '((:d . 0))))
         (loop-result (rt-length-loop-run 2 (rt-length-entry-env word header) fns heap (- fuel 16)))
         (call-result (rt-call "rt-qir:LENGTH" (list word) heap fuel)))
    (implies (and (or (equal word 34) (equal (model-word-op :and word 7) 0))
                  (equal (rt-header-read 34 heap) (boymoo-model::core-value header))
                  (not (equal (model-word-op :and header 255) 1))
                  (boymoo-model::core-value-p (mv-nth 0 loop-result))
                  (natp fuel) (<= 24 fuel))
             (and (equal (mv-nth 0 call-result) (mv-nth 0 loop-result))
                  (equal (mv-nth 1 call-result) (mv-nth 1 loop-result)))))
  :hints (("Goal"
           :in-theory (e/d (rt-call rt-length-loop-run rt-length-entry-env rt-header-read
                            qir-phi-bindings qir-operand qir-operands qir-compute qir-branch
                            model-word-equality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (fns frame memory steps)
                     (qir-eval-step :block 0 fns :m nil frame memory steps))
                    (:free (fns frame memory steps)
                     (qir-eval-step :block 2 fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(local
 (defthm rt-list-spine-starts-with-nil-or-cons
   (implies (rt-list-spine-p data word heap)
            (or (equal word 34) (equal (model-word-op :and word 7) 0)))
   :rule-classes nil
   :hints (("Goal" :expand ((rt-list-spine-p data word heap)) :do-not-induct t))))

(defthmd rt-length-of-represented-list-agrees-with-core
  (implies (and (true-listp data)
                (equal (model-heap-datum word heap) (boymoo-model::core-value data))
                (rt-list-spine-p data word heap)
                (equal (rt-header-read 34 heap) (boymoo-model::core-value header))
                (not (equal (model-word-op :and header 255) 1))
                (unsigned-byte-p 62 (len data))
                (natp fuel) (<= (+ 24 (* 9 (len data))) fuel))
           (equal (rt-observe "rt-qir:LENGTH" (list word) heap fuel)
                  (boymoo-model::core-prelude 'length (list data))))
  :hints (("Goal"
           :use (rt-list-spine-starts-with-nil-or-cons
                 rt-length-list-call-follows-loop-result
                 (:instance model-constant-of-immediate-integer
                            (datum 0) (constants (model-heap-objects heap)))
                 (:instance rt-length-loop-counts-represented-list
                            (count 0) (pred 2) (env (rt-length-entry-env word header))
                            (fns (rt-call-functions "rt-qir:LENGTH" '((:d . 0))))
                            (fuel (- fuel 16))))
           :in-theory (e/d (rt-observe rt-length-loop-inputs-p rt-length-entry-env
                            qir-operand boymoo-model::core-prelude length
                            model-constant-of-immediate-integer)
                           (rt-call qir-run model-word model-integer-word))
           :do-not-induct t)))
