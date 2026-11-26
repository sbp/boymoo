(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-paths")
(include-book "immediate-views")
(include-book "pair-access")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-instruction-effect proof-execute proof-segment-p proof-world-machine
                    proof-world-reg proof-world-pc proof-world-stop proof-reg proof-reg-value-p
                    proof-machine-value-p proof-heap-p proof-heap-base proof-value-p proof-word-tag
                    generated-compare-flags generated-path-p boymoo-model::a64-execute
                    boymoo-model::a64-condition boymoo-model::a64-unsigned
                    acl2::binary-logand acl2::binary-logior evenp oddp expt))

(defun generated-equal-items (serial)
  (let ((yes (boymoo-compiler::gen-local serial))
        (no (boymoo-compiler::gen-local (+ serial 1)))
        (done (boymoo-compiler::gen-local (+ serial 2))))
    (list '(:cmp-reg 0 1) (list :b-cond :eq yes)
          '(:orr-reg 9 0 1) '(:tst-mask 9 1) (list :b-cond :ne no)
          '(:and-mask 9 0 3) '(:cmp 9 4) (list :b-cond :eq no)
          '(:and-mask 9 1 3) '(:cmp 9 4) (list :b-cond :eq no)
          '(:bl "prim:COMMON-LISP::EQUAL") (list :b done)
          (list :label yes) '(:movz 0 58 0) (list :b done)
          (list :label no) '(:movz 0 34 0) (list :label done))))

(defthm generated-equal-emission
  (equal (boymoo-compiler::gen-routine "COMMON-LISP::EQUAL" label serial code)
         (mv (boymoo-compiler::reverse-onto (generated-equal-items serial) code) (+ serial 3)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-routine boymoo-compiler::gen-equal
                                    boymoo-compiler::gen-emit))))

(local
 (defthm generated-compare-and-mask-effect
   (equal (proof-instruction-effect (list :logical-imm 0 64 9 rn 7) world)
          (generated-set-reg 9 (proof-word-tag (proof-world-reg rn world))
                             (generated-set-pc (+ (proof-world-pc world) 4) world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute proof-word-tag
                                     boymoo-model::a64-execute boymoo-model::a64-unsigned
                                     proof-world-machine proof-world-reg proof-reg proof-world-pc
                                     generated-set-machine generated-set-reg generated-set-pc)))))

(local
 (defthm generated-equality-tag-bounds
   (and (natp (proof-word-tag word)) (< (proof-word-tag word) 8))
   :hints (("Goal" :in-theory (enable proof-word-tag)))
   :rule-classes ((:type-prescription :corollary (natp (proof-word-tag word)))
                  (:linear :corollary (< (proof-word-tag word) 8)))))

(local
 (defthm generated-equality-tag-fits-in-a-register
   (equal (boymoo-model::a64-unsigned 64 (proof-word-tag word)) (proof-word-tag word))
   :hints (("Goal" :in-theory (enable proof-word-tag)))))

(local
 (defthm generated-equality-operand-or-effect
   (equal (proof-instruction-effect '(:logical-reg 1 64 9 0 1 0 0 nil) world)
          (generated-set-reg 9 (logior (proof-world-reg 0 world) (proof-world-reg 1 world))
                             (generated-set-pc (+ (proof-world-pc world) 4) world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                                     proof-world-machine proof-world-reg proof-reg proof-world-pc
                                     generated-set-machine generated-set-reg generated-set-pc)))))

(local
 (defthm generated-equality-or-is-even-when-both-are-even
   (implies (and (integerp left) (integerp right))
            (equal (evenp (logior left right)) (and (evenp left) (evenp right))))
   :hints (("Goal" :use (:instance generated-logior-recurrence (x left) (y right))))))

(defun generated-equality-atom-edge-p (left right)
  (or (oddp left) (oddp right) (equal (proof-word-tag left) 4) (equal (proof-word-tag right) 4)))

(defun generated-unequal-equality-path (left right)
  (let ((prefix '((:arithmetic-reg 3 64 31 0 1 0 0) (:branch-cond 48 0)
                  (:logical-reg 1 64 9 0 1 0 0 nil) (:logical-imm 3 64 31 9 1)
                  (:branch-cond 44 1)))
        (no '((:move-wide 2 64 0 34 0))))
    (append prefix
            (if (or (oddp left) (oddp right))
                no
              (append '((:logical-imm 0 64 9 0 7) (:arithmetic-imm 3 64 31 9 4) (:branch-cond 32 0))
                      (if (equal (proof-word-tag left) 4)
                          no
                        (append '((:logical-imm 0 64 9 1 7) (:arithmetic-imm 3 64 31 9 4) (:branch-cond 20 0))
                                (if (equal (proof-word-tag right) 4) no nil))))))))

(defthm generated-unequal-equality-selects-false-or-runtime
  (let* ((pc (proof-world-pc before))
         (left (proof-world-reg 0 before)) (right (proof-world-reg 1 before))
         (fast (generated-equality-atom-edge-p left right))
         (path (generated-unequal-equality-path left right))
         (after (generated-path-after path before))
         (end (+ pc (if fast 64 44))))
    (implies (and (not (equal left right)) (< (+ pc 64) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (proof-world-reg 0 after) (if fast *proof-nil* left))
                  (equal (proof-world-reg 1 after) right)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-unequal-equality-path (proof-world-reg 0 before)
                                                                          (proof-world-reg 1 before)))
                           (cuts (list (+ (proof-world-pc before)
                                          (if (generated-equality-atom-edge-p (proof-world-reg 0 before)
                                                                               (proof-world-reg 1 before)) 64 44)))))
           :in-theory (e/d (oddp) (generated-cut-is-segment))))
  :rule-classes nil)

(local
 (defthm generated-canonical-atomic-word-cannot-match-different-bits
   (implies (and (not (equal left right)) (generated-equality-atom-edge-p left right)
                 (proof-value-p left x base objects packages machine)
                 (proof-value-p right y base objects packages machine))
            (not (equal x y)))
   :hints (("Goal"
            :use ((:instance generated-fast-atomic-word-has-atomic-value (word left) (value x))
                  (:instance generated-fast-atomic-word-has-atomic-value (word right) (value y))
                  (:instance generated-fast-atomic-values-have-canonical-words (word left) (value x))
                  (:instance generated-fast-atomic-values-have-canonical-words (word right) (value y)))))
   :rule-classes nil))

(defthm generated-unequal-atomic-equality-returns-source-false
  (let* ((pc (proof-world-pc before))
         (left (proof-world-reg 0 before)) (right (proof-world-reg 1 before))
         (path (generated-unequal-equality-path left right))
         (after (generated-path-after path before)))
    (implies (and (not (equal left right)) (generated-equality-atom-edge-p left right)
                  (< (+ pc 64) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 x before objects packages)
                  (proof-reg-value-p 1 y before objects packages)
                  (generated-path-p path (list (+ pc 64)) before))
             (and (proof-segment-p (len path) (list (+ pc 64)) before :cut after)
                  (proof-reg-value-p 0 (equal x y) after objects packages)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use (generated-unequal-equality-selects-false-or-runtime
                 (:instance generated-canonical-atomic-word-cannot-match-different-bits
                            (left (proof-world-reg 0 before)) (right (proof-world-reg 1 before))
                            (base (proof-heap-base before)) (machine (proof-world-machine before)))
                 (:instance generated-static-booleans-in-published-heap (world before)))
           :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p)
                           (generated-unequal-equality-path generated-equality-atom-edge-p))))
  :rule-classes nil)
