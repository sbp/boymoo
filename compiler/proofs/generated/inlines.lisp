(in-package "BOYMOO-PROOFS")

(include-book "terms")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-execute
                    proof-world-pc proof-world-reg proof-world-machine proof-world-stop
                    proof-word-tag proof-view proof-view-step proof-heap-p proof-stack-prefix
                    proof-reg-value-p proof-machine-value-p proof-value-p proof-heap-base
                    proof-linux-svc generated-flags boymoo-model::a64-execute
                    boymoo-model::a64-unsigned boymoo-model::a64-condition
                    boymoo-model::a64-result-flags logbitp evenp oddp acl2::binary-logand
                    boymoo-compiler::gen-routine expt ash mod floor))

(local
 (defthm generated-tag-of-word-is-mask
   (implies (integerp word)
            (equal (logand word 7) (proof-word-tag word)))
   :hints (("Goal" :in-theory (enable proof-word-tag boymoo-model::a64-unsigned)))))

(local
 (defthm generated-tag-bounds
   (unsigned-byte-p 3 (proof-word-tag word))
   :hints (("Goal" :in-theory (enable proof-word-tag)))))

(local
 (defthm generated-three-bit-test-flags
   (implies (unsigned-byte-p 3 bits)
            (equal (boymoo-model::a64-result-flags 64 bits nil nil)
                   (if (equal bits 0) 4 0)))
   :hints (("Goal" :use (:instance generated-logbitp-of-bounded (bit 63) (x bits))
                   :in-theory (enable boymoo-model::a64-result-flags)))))

(defthm generated-effect-of-tst-three
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect '(:logical-imm 3 64 31 0 7) world)
                  (generated-set-flags
                   (if (equal (proof-word-tag (proof-world-reg 0 world)) 0) 4 0)
                   (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-machine proof-world-pc
                                    proof-world-reg proof-reg generated-ordinary-machine-p
                                    generated-set-machine generated-set-pc generated-set-flags))))

(defthm generated-effect-of-csel
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :select 64 rd first second condition nil) world)
                  (generated-set-reg rd
                                     (proof-world-reg
                                      (if (boymoo-model::a64-condition condition (generated-flags world))
                                          first second)
                                      world)
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-machine proof-world-pc
                                    proof-world-reg proof-reg generated-flags
                                    generated-set-machine generated-set-pc generated-set-reg))))

(local
 (defthm generated-tag-zero-multiple
   (implies (and (integerp word) (equal (proof-word-tag word) 0))
            (equal word (* 8 (floor word 8))))
   :hints (("Goal" :use (:instance generated-unsigned-as-mod (n 3) (x word))
                   :in-theory (enable proof-word-tag mod)))
   :rule-classes nil))

(local
 (defthm generated-even-when-multiple-of-eight
   (implies (and (integerp quotient) (equal word (* 8 quotient)))
            (evenp word))
   :hints (("Goal" :use (:instance associativity-of-*
                                   (acl2::x 1/2) (acl2::y 8) (acl2::z quotient))
                   :in-theory (e/d (evenp) (associativity-of-*))))
   :rule-classes nil))

(local
 (defthm generated-tag-zero-is-even
   (implies (and (integerp word) (equal (proof-word-tag word) 0))
            (evenp word))
   :hints (("Goal" :use (generated-tag-zero-multiple
                         (:instance generated-even-when-multiple-of-eight
                                    (quotient (floor word 8))))))))

(defthm generated-cons-tag-in-value-view-step
  (implies (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view value))
           (equal (equal (proof-word-tag word) 0) (consp value)))
  :hints (("Goal" :expand (proof-view-step :word word 0 depth base objects packages machine)
                  :in-theory (enable oddp proof-cons-value proof-symbol-value proof-rational-value
                                     proof-complex-value proof-integer-view)))
  :rule-classes nil)

(defthm generated-cons-tag-in-value-view
  (implies (proof-value-p word value base objects packages machine)
           (equal (equal (proof-word-tag word) 0) (consp value)))
  :hints (("Goal"
           :use (:instance generated-cons-tag-in-value-view-step
                           (depth (1+ (nfix (proof-object-rank
                                             (assoc-equal (proof-pointer-address word base)
                                                          objects))))))
           :in-theory (enable proof-view proof-value-p))))

(defconst *generated-consp-path*
  '((:logical-imm 3 64 31 0 7) (:move-wide 2 64 9 58 0)
    (:move-wide 2 64 10 34 0) (:select 64 0 9 10 0 nil)))

(defthm generated-consp-emission
  (equal (mv-nth 0 (boymoo-compiler::gen-routine "COMMON-LISP::CONSP" label serial code))
         (boymoo-compiler::reverse-onto
          '((:tst-mask 0 3) (:movz 9 58 0) (:movz 10 34 0) (:csel 0 9 10 :eq)) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-routine))))

(defthm generated-consp-checked-path
  (let* ((pc (proof-world-pc before))
         (after (generated-path-after *generated-consp-path* before)))
    (implies (and (< (+ 16 pc) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (generated-path-p *generated-consp-path* (list (+ pc 16)) before)
                  (proof-value-p (proof-world-reg 0 before) input (proof-heap-base before)
                                 objects packages (proof-world-machine before)))
             (and (proof-segment-p 4 (list (+ pc 16)) before :cut after)
                  (equal (proof-world-reg 0 after) (if (consp input) *proof-t* *proof-nil*))
                  (generated-heap-world-equiv after before))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions *generated-consp-path*)
                                  (cuts (list (+ 16 (proof-world-pc before)))))
                  :in-theory (disable generated-path-p)))
  :rule-classes nil)

(defthm generated-routine-noninline-emission
  (implies (not (member-equal name '("COMMON-LISP::CAR" "COMMON-LISP::CDR" "COMMON-LISP::CONSP"
                                      "COMMON-LISP::EQUAL" "ACL2::BINARY-+" "ACL2::UNARY--"
                                      "COMMON-LISP::<")))
           (equal (mv-nth 0 (boymoo-compiler::gen-routine name label serial code))
                  (cons (list :bl label) code)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-routine))))
