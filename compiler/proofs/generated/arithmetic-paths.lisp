(in-package "BOYMOO-PROOFS")

(include-book "fast-arithmetic")
(include-book "inlines")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-execute
                    proof-world-reg proof-world-pc proof-world-stop proof-world-machine
                    boymoo-model::a64-execute boymoo-model::a64-condition boymoo-model::a64-unsigned
                    generated-compare-flags generated-add-flags
                    proof-immediate-integer-p proof-integer-word expt))

(defthm generated-effect-of-subs-register
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :arithmetic-reg 3 64 rd rn rm 0 0) world)
                  (let ((left (proof-world-reg rn world)) (right (proof-world-reg rm world)))
                    (generated-set-flags
                     (generated-compare-flags left right)
                     (generated-set-reg rd (- left right)
                                        (generated-set-pc (+ 4 (proof-world-pc world)) world))))))
  :hints (("Goal" :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                                   proof-world-machine proof-world-pc proof-world-reg proof-reg
                                   generated-compare-flags generated-set-machine generated-set-pc
                                   generated-set-reg generated-set-flags)
                                  (generated-signed-64-of-unsigned)))))

(defun generated-integer-result-path (binary-p overflow-p)
  (append (if binary-p
              '((:arithmetic-imm 2 64 9 1 1) (:arithmetic-reg 1 64 9 0 9 0 0))
            '((:move-wide 2 64 9 2 0) (:arithmetic-reg 3 64 9 9 0 0 0)))
          '((:branch-cond 12 6))
          (if overflow-p nil
            '((:logical-reg 1 64 0 31 9 0 0 nil) (:branch 8 nil)))))

(defthm generated-inline-arithmetic-result-or-slow-edge
  (let* ((pc (proof-world-pc before))
         (datum (if binary-p (+ x y) (- x)))
         (overflow-p (not (proof-immediate-integer-p datum)))
         (path (generated-integer-result-path binary-p overflow-p))
         (end (+ pc (if overflow-p 20 24)))
         (after (generated-path-after path before)))
    (implies (and (proof-immediate-integer-p x)
                  (equal (proof-world-reg 0 before) (proof-integer-word x))
                  (implies binary-p (and (proof-immediate-integer-p y)
                                         (equal (proof-world-reg 1 before) (proof-integer-word y))))
                  (< (+ pc 24) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (if overflow-p 3 5) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (proof-world-reg 0 after)
                         (proof-integer-word (if overflow-p x datum)))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-ordinary-machine-p after)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use ((:instance generated-placed-path-to-cut
                            (instructions (generated-integer-result-path
                                           binary-p (not (proof-immediate-integer-p
                                                          (if binary-p (+ x y) (- x))))))
                            (cuts (list (+ (proof-world-pc before)
                                           (if (proof-immediate-integer-p
                                                (if binary-p (+ x y) (- x))) 24 20)))))
                 generated-fast-addition-word-and-overflow generated-fast-negation-word-and-overflow)
           :in-theory (disable generated-path-p generated-fast-addition-word-and-overflow
                               generated-fast-negation-word-and-overflow)))
  :rule-classes nil)

(defconst *generated-integer-less-than-path*
  '((:arithmetic-reg 3 64 31 0 1 0 0) (:move-wide 2 64 9 58 0)
    (:move-wide 2 64 10 34 0) (:select 64 0 9 10 11 nil) (:branch 8 nil)))

(defthm generated-inline-immediate-less-than-path
  (let* ((pc (proof-world-pc before))
         (after (generated-path-after *generated-integer-less-than-path* before)))
    (implies (and (proof-immediate-integer-p x) (proof-immediate-integer-p y)
                  (equal (proof-world-reg 0 before) (proof-integer-word x))
                  (equal (proof-world-reg 1 before) (proof-integer-word y))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (< (+ pc 24) (expt 2 64))
                  (generated-path-p *generated-integer-less-than-path* (list (+ pc 24)) before))
             (and (proof-segment-p 5 (list (+ pc 24)) before :cut after)
                  (equal (proof-world-reg 0 after) (if (< x y) *proof-t* *proof-nil*))
                  (equal (proof-world-pc after) (+ pc 24))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-ordinary-machine-p after)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions *generated-integer-less-than-path*)
                           (cuts (list (+ 24 (proof-world-pc before)))))
           :in-theory (disable generated-path-p)))
  :rule-classes nil)

(local
 (defthm generated-and-parity
   (implies (and (integerp left) (integerp right))
            (equal (evenp (logand left right)) (or (evenp left) (evenp right))))
   :hints (("Goal" :use (:instance generated-logand-recurrence (x left) (y right))))))

(defthm generated-parity-of-unsigned-word
  (implies (integerp word)
           (equal (evenp (boymoo-model::a64-unsigned 64 word)) (evenp word)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned))))

(local
 (defthm generated-effect-of-and-register
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :logical-reg 0 64 rd rn rm 0 0 nil) world)
                   (generated-set-reg rd (logand (proof-world-reg rn world) (proof-world-reg rm world))
                                      (generated-set-pc (+ 4 (proof-world-pc world)) world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                                     proof-world-machine proof-world-pc proof-world-reg proof-reg
                                     generated-set-machine generated-set-reg generated-set-pc)))))

(local
 (defthm generated-one-bit-test-flags
   (implies (integerp word)
            (equal (boymoo-model::a64-result-flags 64 (logand word 1) nil nil)
                   (if (evenp word) 4 0)))
   :hints (("Goal"
            :use ((:instance generated-logand-recurrence (x word) (y 1)))
            :in-theory (enable boymoo-model::a64-result-flags)))))

(defthm generated-effect-of-tst-one
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect (list :logical-imm 3 64 31 rn 1) world)
                  (generated-set-flags (if (evenp (proof-world-reg rn world)) 4 0)
                                       (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                                    proof-world-machine proof-world-pc proof-world-reg proof-reg
                                    generated-ordinary-machine-p generated-set-machine
                                    generated-set-pc generated-set-flags))))

(defun generated-integer-tag-path (binary-p)
  (if binary-p
      '((:logical-reg 0 64 9 0 1 0 0 nil) (:logical-imm 3 64 31 9 1) (:branch-cond 24 0))
    '((:logical-imm 3 64 31 0 1) (:branch-cond 24 0))))

(defthm generated-integer-tag-guard-selects-edge
  (let* ((pc (proof-world-pc before))
         (slow (or (evenp (proof-world-reg 0 before))
                   (and binary-p (evenp (proof-world-reg 1 before)))))
         (path (generated-integer-tag-path binary-p))
         (end (+ pc (* 4 (len path)) (if slow 20 0)))
         (after (generated-path-after path before)))
    (implies (and (< (+ pc 32) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-ordinary-machine-p after)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-integer-tag-path binary-p))
                           (cuts (list (+ (proof-world-pc before)
                                          (* 4 (len (generated-integer-tag-path binary-p)))
                                          (if (or (evenp (proof-world-reg 0 before))
                                                  (and binary-p (evenp (proof-world-reg 1 before))))
                                              20 0)))))
           :in-theory (disable generated-path-p)))
  :rule-classes nil)

(defun generated-integer-routine-items (name label serial)
  (let* ((unary (equal name "ACL2::UNARY--"))
         (slow (boymoo-compiler::gen-local serial))
         (done (boymoo-compiler::gen-local (1+ serial))))
    (append (if unary nil '((:and-reg 9 0 1)))
            (list (list :tst-mask (if unary 0 9) 1) (list :b-cond :eq slow))
            (cond (unary (list '(:movz 9 2 0) '(:subs-reg 9 9 0 0)
                               (list :b-cond :vs slow) '(:mov 0 9)))
                  ((equal name "ACL2::BINARY-+")
                   (list '(:sub 9 1 1) '(:adds-reg 9 0 9 0)
                         (list :b-cond :vs slow) '(:mov 0 9)))
                  (t '((:cmp-reg 0 1) (:movz 9 58 0) (:movz 10 34 0) (:csel 0 9 10 :lt))))
            (list (list :b done) (list :label slow) (list :bl label) (list :label done)))))

(defthm generated-integer-routine-emission
  (implies (member-equal name '("ACL2::UNARY--" "ACL2::BINARY-+" "COMMON-LISP::<"))
           (equal (boymoo-compiler::gen-routine name label serial code)
                  (mv (boymoo-compiler::reverse-onto
                       (generated-integer-routine-items name label serial) code)
                      (+ 2 serial))))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-routine boymoo-compiler::gen-arithmetic
                                    boymoo-compiler::gen-boolean boymoo-compiler::gen-emit))))
