(in-package "BOYMOO-PROOFS")

(include-book "linked-loads")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-instruction-at-p proof-instruction-effect proof-instruction-access-p
                    proof-instructions-at-p generated-path-p generated-if-path expt))

(defthm generated-conditional-dispatch-has-checked-path-from-linked-code
  (let* ((pc (proof-world-pc before)) (test '(:arithmetic-imm 3 64 31 0 34))
         (select (list :branch-cond (- yes (+ pc 4)) 1)) (alternate (list :branch (- no (+ pc 8)) nil)))
    (implies (and (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no) (< (+ pc 8) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (not (member-equal pc cuts)) (not (member-equal (+ pc 4) cuts))
                  (implies (equal (proof-world-reg 0 before) *proof-nil*)
                           (not (member-equal (+ pc 8) cuts)))
                  (proof-instructions-at-p (list test select alternate) pc before))
             (generated-path-p (generated-if-path yes no before) cuts before)))
  :hints (("Goal" :in-theory (enable generated-path-p generated-instruction-p generated-if-path
                                     proof-instructions-at-p)))
  :rule-classes nil)

(defthm generated-linked-if-dispatch-items-have-checked-path
  (let* ((pc (proof-world-pc before)) (yes (proof-label-address yes-label base labels))
         (no (proof-label-address no-label base labels)))
    (implies (and (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no) (< (+ pc 8) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (not (member-equal pc cuts)) (not (member-equal (+ pc 4) cuts))
                  (implies (equal (proof-world-reg 0 before) *proof-nil*)
                           (not (member-equal (+ pc 8) cuts)))
                  (generated-linked-item-p '(:cmp 0 34) '(:arithmetic-imm 3 64 31 0 34) pc base labels before)
                  (generated-linked-item-p (list :b-cond :ne yes-label) (list :branch-cond (- yes (+ pc 4)) 1)
                                           (+ pc 4) base labels before)
                  (generated-linked-item-p (list :b no-label) (list :branch (- no (+ pc 8)) nil)
                                           (+ pc 8) base labels before))
             (generated-path-p (generated-if-path yes no before) cuts before)))
  :hints (("Goal"
           :use (:instance generated-conditional-dispatch-has-checked-path-from-linked-code
                           (yes (proof-label-address yes-label base labels)) (no (proof-label-address no-label base labels)))
           :in-theory (e/d (proof-instructions-at-p generated-linked-item-p) (proof-label-address))))
  :rule-classes nil)
