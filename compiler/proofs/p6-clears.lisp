(in-package "BOYMOO-COMPILER")

(include-book "p6")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-clear-stores (stale temp)
  (if (atom stale)
      nil
    (cons (list nil :spill (car stale) temp)
          (p6-clear-stores (cdr stale) temp))))

(local
 (defthm p6-clear-stores-are-generated-in-reverse
   (equal (abi-clear-spills stale temp out)
          (revappend (p6-clear-stores stale temp) out))
   :hints (("Goal" :induct (abi-clear-spills stale temp out)
            :in-theory (enable p6-clear-stores)))))

(local
 (defthm p6-revappend-of-revappend
   (equal (revappend (revappend xs ys) zs)
          (revappend ys (append xs zs)))
   :hints (("Goal" :induct (revappend xs ys)))))

(local
 (defthm p6-clear-stores-are-a-list
   (true-listp (p6-clear-stores stale temp))
   :hints (("Goal" :induct (p6-clear-stores stale temp)
            :in-theory (enable p6-clear-stores)))))

(defthmd p6-clear-code-is-copy-and-stores
  (equal (reverse (abi-clears stale temp nil))
         (if (atom stale) nil
           (cons (list temp :copy '(:k . 1)) (p6-clear-stores stale temp)))))

(defund p6-clear-slots-fit-p (stale nslots)
  (if (atom stale)
      t
    (and (qir-slot-p (car stale) nslots)
         (p6-clear-slots-fit-p (cdr stale) nslots))))

; QIR-L execution up to the point where the collector may see the slots.
; The usual function evaluator exposes only the returned value and heap.
(defund p6-run-slot-code (insts env slots nslots heap)
  (if (atom insts)
      (boymoo-model::core-value slots)
    (let* ((inst (car insts))
           (args (qir-operands (qir-inst-uses inst) env :l heap)))
      (if (not (boymoo-model::core-value-p args))
          args
        (mv-let (result slots heap)
          (qir-compute inst (boymoo-model::core-datum args) slots nslots :l heap nil)
          (if (not (boymoo-model::core-value-p result))
              result
            (p6-run-slot-code (cdr insts)
                                 (qir-bind (qir-inst-dest inst) (boymoo-model::core-datum result) env)
                                 slots nslots heap)))))))

(local
 (defun p6-run-clear-stores-induct (stale slots)
   (if (atom stale)
       slots
     (p6-run-clear-stores-induct (cdr stale) (put-assoc-equal (car stale) 1 slots)))))

(local
 (defthmd p6-clear-stores-write-only-selected-slots
   (implies (and (p6-clear-slots-fit-p stale nslots)
                 (equal (qir-operand temp env :l heap) (boymoo-model::core-value 1)))
            (let* ((result (p6-run-slot-code (p6-clear-stores stale temp) env slots nslots heap))
                   (after (boymoo-model::core-datum result)))
              (and (boymoo-model::core-value-p result)
                   (equal (qir-slot-value slot after)
                          (if (member-equal slot stale) (boymoo-model::core-value 1)
                            (qir-slot-value slot slots))))))
   :hints (("Goal" :induct (p6-run-clear-stores-induct stale slots)
            :in-theory (e/d (p6-clear-stores p6-clear-slots-fit-p p6-run-slot-code
                              qir-operands qir-compute)
                             (put-assoc-equal))))))

(local
 (defthm p6-clear-operand-is-word-one
   (equal (qir-operand '(:k . 1) env :l heap) (boymoo-model::core-value 1))
   :hints (("Goal" :in-theory (enable qir-operand)))))

(defthmd p6-emitted-clears-write-only-selected-slots
  (implies (and (qir-dtemp-p temp) (p6-clear-slots-fit-p stale nslots))
           (let* ((result (p6-run-slot-code (reverse (abi-clears stale temp nil)) env slots nslots heap))
                  (after (boymoo-model::core-datum result)))
             (and (boymoo-model::core-value-p result)
                  (equal (qir-slot-value slot after)
                         (if (member-equal slot stale) (boymoo-model::core-value 1)
                           (qir-slot-value slot slots))))))
  :hints (("Goal" :cases ((atom stale))
           :use (:instance p6-clear-stores-write-only-selected-slots
                           (env (qir-bind temp 1 env)))
           :in-theory (e/d (p6-clear-code-is-copy-and-stores qir-operands qir-compute)
                            (qir-bind abi-clears))
           :expand ((p6-run-slot-code nil env slots nslots heap)
                    (p6-run-slot-code (cons (list temp :copy '(:k . 1))
                                               (p6-clear-stores stale temp))
                                         env slots nslots heap))
           :do-not-induct t)))

(defthmd p6-state-transfer-matches-rewrite
  (equal (abi-state-insts insts needs slots current dirty)
         (mv (mv-nth 1 (abi-rewrite-insts insts needs slots temp current dirty out))
             (mv-nth 2 (abi-rewrite-insts insts needs slots temp current dirty out))))
  :hints (("Goal" :induct (abi-rewrite-insts insts needs slots temp current dirty out)
           :in-theory (disable abi-spills abi-loads abi-clears abi-slot-set
                               abi-undef nset-minus nset-union nset-intersect))))

(defun p6-slot-set-p (slots)
  (if (atom slots)
      (null slots)
    (and (natp (car slots))
         (or (atom (cdr slots)) (< (car slots) (cadr slots)))
         (p6-slot-set-p (cdr slots)))))

(local
 (defthm p6-later-slot-is-larger
   (implies (and (p6-slot-set-p slots) (member-equal slot (cdr slots)))
            (< (car slots) slot))
   :rule-classes :linear
   :hints (("Goal" :induct (p6-slot-set-p slots)))))

(defthmd p6-slot-difference-selects-unneeded-slots
  (implies (and (p6-slot-set-p dirty) (p6-slot-set-p needed))
           (iff (member-equal slot (nset-minus dirty needed))
                (and (member-equal slot dirty) (not (member-equal slot needed)))))
  :hints (("Goal" :induct (nset-minus dirty needed))))

(defthmd p6-clearing-stale-slots-preserves-needed-slot
  (let ((stale (nset-minus dirty needed)))
    (implies (and (member-equal slot needed) (p6-slot-set-p needed) (p6-slot-set-p dirty)
                  (qir-dtemp-p temp) (p6-clear-slots-fit-p stale nslots))
             (let* ((code (reverse (abi-clears stale temp nil)))
                    (result (p6-run-slot-code code env slots nslots heap)))
               (equal (qir-slot-value slot (boymoo-model::core-datum result))
                      (qir-slot-value slot slots)))))
  :hints (("Goal"
           :use (:instance p6-emitted-clears-write-only-selected-slots (stale (nset-minus dirty needed)))
           :in-theory (e/d (p6-slot-difference-selects-unneeded-slots)
                            (p6-slot-set-p nset-minus abi-clears qir-slot-value reverse member-equal))
           :do-not-induct t)))
