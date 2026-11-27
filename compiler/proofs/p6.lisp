(in-package "BOYMOO-COMPILER")

(include-book "../abi")
(include-book "qir-semantics")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-copy-snapshot (copies env heap)
  (if (endp copies)
      (boymoo-model::core-value nil)
    (let ((first (qir-operand (cdar copies) env :m heap)))
      (if (not (boymoo-model::core-value-p first))
          first
        (let ((rest (p6-copy-snapshot (cdr copies) env heap)))
          (if (boymoo-model::core-value-p rest)
              (boymoo-model::core-value
               (acons (caar copies) (boymoo-model::core-datum first) (boymoo-model::core-datum rest)))
            rest))))))

(defund p6-run-copy-instructions (insts env heap)
  (if (endp insts)
      (boymoo-model::core-value env)
    (let* ((instruction (car insts))
           (source (qir-operand (caddr instruction) env :l heap)))
      (cond ((not (eq (qir-inst-op instruction) :copy)) :malformed)
            ((not (boymoo-model::core-value-p source)) source)
            (t (mv-let (result slots heap)
                 (qir-compute instruction (list (boymoo-model::core-datum source)) nil 0 :l heap nil)
                 (declare (ignore slots))
                 (p6-run-copy-instructions
                  (cdr insts) (qir-bind (qir-inst-dest instruction) (boymoo-model::core-datum result) env)
                  heap)))))))

(defthm p6-phi-covers-predecessor
  (implies (and (member-equal pred preds) (qir-phi-covers-p preds args))
           (assoc-equal pred args))
  :hints (("Goal" :induct (qir-phi-covers-p preds args))))

(defthmd p6-copy-snapshot-is-phi-bindings
  (implies (and (member-equal pred preds) (qir-phis-match-p phis preds))
           (equal (p6-copy-snapshot (abi-phi-copies phis pred) env heap)
                  (qir-phi-bindings phis pred env :m heap)))
  :hints (("Goal" :induct (abi-phi-copies phis pred)
           :in-theory (enable p6-copy-snapshot qir-phi-bindings))))

(defthm p6-free-copy-does-not-change-sources
  (implies (abi-free-copy rest copies)
           (not (abi-source-p (car (abi-free-copy rest copies)) copies)))
  :hints (("Goal" :induct (abi-free-copy rest copies))))

(defthmd p6-operand-of-unrelated-update
  (implies (not (equal operand dest))
           (equal (qir-operand operand (qir-bind dest value env) level heap)
                  (qir-operand operand env level heap)))
  :hints (("Goal" :in-theory (enable qir-operand))))

(defthmd p6-snapshot-of-non-source-update
  (implies (not (abi-source-p dest copies))
           (equal (p6-copy-snapshot copies (qir-bind dest value env) heap)
                  (p6-copy-snapshot copies env heap)))
  :hints (("Goal" :induct (abi-source-p dest copies)
           :in-theory (e/d (p6-copy-snapshot p6-operand-of-unrelated-update)
                            (qir-bind)))))

(defthm p6-operand-of-own-update
  (implies (qir-temp-p dest)
           (equal (qir-operand dest (qir-bind dest value env) level heap)
                  (boymoo-model::core-value value)))
  :hints (("Goal" :in-theory (enable qir-operand))))

(defthmd p6-snapshot-of-saving-cycle-source
  (let ((old-value (qir-operand old env :m heap)))
    (implies (and (qir-temp-p new) (not (abi-source-p new copies))
                  (boymoo-model::core-value-p old-value))
             (equal (p6-copy-snapshot (abi-replace-source old new copies)
                                         (qir-bind new (boymoo-model::core-datum old-value) env) heap)
                    (p6-copy-snapshot copies env heap))))
  :hints (("Goal" :induct (abi-replace-source old new copies)
           :in-theory (e/d (p6-copy-snapshot p6-operand-of-unrelated-update)
                            (qir-bind)))))

(defthmd p6-two-cycle-preserves-parallel-values
  (let* ((first '(:d . 0))
         (second '(:d . 1))
         (copies (list (cons first second) (cons second first)))
         (insts (mv-nth 0 (abi-sequence-copies copies 2)))
         (result (p6-run-copy-instructions insts (acons first a (acons second b env)) heap))
         (bindings (boymoo-model::core-datum result)))
    (and (boymoo-model::core-value-p result)
         (equal (assoc-equal first bindings) (cons first b))
         (equal (assoc-equal second bindings) (cons second a))))
  :hints (("Goal" :in-theory (enable p6-run-copy-instructions qir-compute qir-operand)
           :do-not-induct t)))

; Check the fragment in which every copy destination is absent from the
; sources of all the pending copies.
(defund p6-disjoint-copies-p (copies all)
  (if (endp copies)
      (null copies)
    (and (qir-temp-p (caar copies))
         (not (equal (caar copies) (cdar copies)))
         (not (abi-source-p (caar copies) all))
         (p6-disjoint-copies-p (cdr copies) all))))

(local
 (defthm p6-disjoint-copies-after-dropping-a-source
   (implies (p6-disjoint-copies-p copies all)
            (p6-disjoint-copies-p copies (cdr all)))
   :hints (("Goal" :induct (p6-disjoint-copies-p copies all)
            :in-theory (enable p6-disjoint-copies-p)))))

(local
 (defthm p6-tail-is-disjoint
   (implies (p6-disjoint-copies-p copies copies)
            (p6-disjoint-copies-p (cdr copies) (cdr copies)))
   :hints (("Goal"
            :use (:instance p6-disjoint-copies-after-dropping-a-source
                            (copies (cdr copies)) (all copies))
            :in-theory (enable p6-disjoint-copies-p)))))

(local
 (defthm p6-disjoint-copies-need-no-self-copy-removal
   (implies (p6-disjoint-copies-p copies all)
            (equal (abi-drop-self copies) copies))
   :hints (("Goal" :induct (p6-disjoint-copies-p copies all)
            :in-theory (enable p6-disjoint-copies-p)))))

(local
 (defthm p6-disjoint-copy-list-needs-no-self-removal
   (implies (p6-disjoint-copies-p copies copies)
            (equal (abi-drop-self copies) copies))
   :hints (("Goal"
            :use (:instance p6-disjoint-copies-need-no-self-copy-removal (all copies))
            :in-theory (disable abi-drop-self p6-disjoint-copies-need-no-self-copy-removal)))))

(local
 (defthm p6-disjoint-head-is-a-free-copy
   (implies (and (consp copies) (p6-disjoint-copies-p copies copies))
            (and (consp (car copies)) (not (abi-source-p (caar copies) copies))))
   :hints (("Goal" :expand ((p6-disjoint-copies-p copies copies))
            :in-theory (disable abi-source-p)))))

(defund p6-copies-in-order (copies)
  (if (endp copies)
      nil
    (cons (list (caar copies) :copy (cdar copies))
          (p6-copies-in-order (cdr copies)))))

(local
 (defun p6-copy-order-induction (copies out fuel)
   (if (endp copies)
       (list out fuel)
     (p6-copy-order-induction (cdr copies)
                                 (cons (list (caar copies) :copy (cdar copies)) out)
                                 (1- fuel)))))

(local
 (defthmd p6-scheduling-step-on-disjoint-copies
   (implies (and (consp copies) (p6-disjoint-copies-p copies copies) (posp fuel))
            (equal (mv-nth 0 (abi-sequence copies fresh out fuel))
                   (mv-nth 0 (abi-sequence (cdr copies) fresh
                                           (cons (list (caar copies) :copy (cdar copies)) out)
                                           (1- fuel)))))
   :hints (("Goal" :use p6-disjoint-head-is-a-free-copy
            :expand ((abi-sequence copies fresh out fuel)
                     (abi-free-copy copies copies) (abi-remove-copy (car copies) copies))
            :in-theory (disable abi-sequence abi-drop-self abi-source-p
                                p6-disjoint-head-is-a-free-copy)))))

(local
 (defthm p6-scheduling-with-no-copies-gives-output
   (implies (atom copies)
            (equal (mv-nth 0 (abi-sequence copies fresh out fuel)) out))
   :hints (("Goal" :expand ((abi-sequence copies fresh out fuel))))))

(local
 (defthm p6-reversed-disjoint-copy-code
   (implies (and (p6-disjoint-copies-p copies copies) (natp fuel) (<= (len copies) fuel))
            (equal (mv-nth 0 (abi-sequence copies fresh out fuel))
                   (reverse-onto (p6-copies-in-order copies) out)))
   :hints (("Goal" :induct (p6-copy-order-induction copies out fuel)
            :in-theory (e/d (p6-scheduling-step-on-disjoint-copies p6-copies-in-order)
                             (abi-sequence abi-drop-self))))))

(local
 (defthm p6-double-reverse-onto
   (equal (reverse-onto (reverse-onto xs ys) zs) (reverse-onto ys (append xs zs)))
   :hints (("Goal" :induct (reverse-onto xs ys)))))

(local
 (defthm p6-copy-order-is-a-list
   (true-listp (p6-copies-in-order copies))
   :hints (("Goal" :in-theory (enable p6-copies-in-order)))))

(defthmd p6-disjoint-copies-are-emitted-in-order
  (implies (p6-disjoint-copies-p copies copies)
           (equal (mv-nth 0 (abi-sequence-copies copies fresh)) (p6-copies-in-order copies)))
  :hints (("Goal" :in-theory (disable abi-sequence))))

(defund p6-install-snapshot (bindings env)
  (if (endp bindings)
      env
    (p6-install-snapshot (cdr bindings) (qir-bind (caar bindings) (cdar bindings) env))))

(local
 (defun p6-snapshot-order-induction (copies env heap)
   (if (endp copies)
       env
     (let ((value (qir-operand (cdar copies) env :m heap)))
       (p6-snapshot-order-induction
        (cdr copies) (qir-bind (caar copies) (boymoo-model::core-datum value) env) heap)))))

(local
 (defthm p6-operand-is-the-same-in-qir-l-and-m
   (equal (qir-operand operand env :l heap) (qir-operand operand env :m heap))
   :hints (("Goal" :in-theory (enable qir-operand)))))

(defthmd p6-disjoint-copy-order-installs-snapshot
  (let ((snapshot (p6-copy-snapshot copies env heap)))
    (implies (and (p6-disjoint-copies-p copies copies) (boymoo-model::core-value-p snapshot))
             (equal (p6-run-copy-instructions (p6-copies-in-order copies) env heap)
                    (boymoo-model::core-value (p6-install-snapshot (boymoo-model::core-datum snapshot) env)))))
  :hints (("Goal" :induct (p6-snapshot-order-induction copies env heap)
           :expand ((p6-disjoint-copies-p copies copies))
           :in-theory (e/d (p6-copy-snapshot p6-copies-in-order p6-run-copy-instructions
                            p6-install-snapshot p6-snapshot-of-non-source-update qir-compute)
                           (qir-bind)))))

(defthmd p6-disjoint-schedule-installs-parallel-snapshot
  (let ((snapshot (p6-copy-snapshot copies env heap)))
    (implies (and (p6-disjoint-copies-p copies copies) (boymoo-model::core-value-p snapshot))
             (equal (p6-run-copy-instructions (mv-nth 0 (abi-sequence-copies copies fresh)) env heap)
                    (boymoo-model::core-value (p6-install-snapshot (boymoo-model::core-datum snapshot) env)))))
  :hints (("Goal" :in-theory (e/d (p6-disjoint-copies-are-emitted-in-order
                                   p6-disjoint-copy-order-installs-snapshot)
                                  (abi-sequence-copies)))))
