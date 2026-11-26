(in-package "BOYMOO-PROOFS")

(include-book "classification")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-load boymoo-model::a64-pc boymoo-model::a64-nzcv
                     boymoo-model::a64-sp boymoo-model::a64-set-pc
                     boymoo-model::a64-set-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory proof-execute proof-instruction-effect
                     proof-reg proof-load-word proof-world-machine proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-run proof-segment-p proof-view proof-value-p
                     proof-number-checked-block-p proof-word-tag proof-pointer-address
                     proof-number-integer-parity
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior
                     oddp evenp mod floor ash)))

(defund proof-number-invert-instructions (entry zero negative box)
  (list '(:arithmetic-imm 3 64 31 0 1)
        (list :branch-cond (- zero (+ entry 4)) 0)
        '(:logical-imm 3 64 31 0 1)
        '(:branch-cond 24 1)
        '(:arithmetic-imm 2 64 2 0 2)
        '(:arithmetic-reg 0 64 2 28 2 0 0)
        '(:single 1 8 2 2 :offset 8)
        (list :branch-zero (- negative (+ entry 28)) 64 2 t)
        '(:branch 12 nil)
        '(:arithmetic-imm 3 64 31 0 0)
        (list :branch-cond (- negative (+ entry 40)) 11)
        '(:logical-reg 1 64 2 31 0 0 0 nil)
        '(:logical-reg 1 64 0 31 1 0 0 nil)
        '(:logical-reg 1 64 1 31 2 0 0 nil)
        (list :branch (- box (+ entry 56)) nil)))

(defthm proof-number-invert-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((entry (boymoo-compiler::a64-offset "rt:q-invert-parts" labels))
           (zero (boymoo-compiler::a64-offset "rt:zero" labels))
           (negative (boymoo-compiler::a64-offset "rt:q-invert-negative" labels))
           (box (boymoo-compiler::a64-offset "rt:q-box" labels)))
      (equal
       (proof-number-decode-items
        (proof-number-instruction-items
         (take 18 (proof-number-code-at-label "rt:q-invert-parts"
                                             (boymoo-compiler::runtime-rational-code))))
        entry labels)
       (proof-number-invert-instructions entry zero negative box))))
  :rule-classes nil)

(defund proof-number-invert-path (a zero negative box world)
  (let ((code (proof-number-invert-instructions (proof-world-pc world) zero negative box)))
    (cond ((equal a 0) (take 2 code))
          ((oddp (proof-world-reg 0 world))
           (append (take 4 code)
                   (take (if (< a 0) 2 6) (nthcdr 9 code))))
          ((< a 0) (take 8 code))
          (t (append (take 9 code) (nthcdr 11 code))))))

(defund proof-number-invert-target (a zero negative box)
  (cond ((equal a 0) zero)
        ((< a 0) negative)
        (t box)))

(local
 (defthm test-low-bit-condition
   (equal (boymoo-model::a64-condition 1 (if test 0 4)) (if test t nil))))

(local
 (defthm header-address-range
   (unsigned-byte-p 64 (proof-pointer-address word base))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary (natp (proof-pointer-address word base)))
                  (:linear :corollary (< (proof-pointer-address word base) (expt 2 64))))))

(local
 (defthm invert-signed-test
   (implies (proof-immediate-integer-p a)
            (equal (< (boymoo-model::a64-signed 64 (proof-integer-word a)) 0)
                   (< a 0)))
   :hints (("Goal" :cases ((< a 0))
                   :in-theory (disable proof-integer-word proof-number-immediate-word-bits)))))

(defthm proof-number-invert-dispatch
  (let* ((machine (proof-world-machine world))
         (path (proof-number-invert-path a zero negative box world))
         (target (proof-number-invert-target a zero negative box))
         (after (proof-number-execute-block path world))
         (swapped (and (not (equal a 0)) (not (< a 0)))))
    (implies (and (proof-number-reduced-p a b)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-checked-block-p path (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 56 (proof-world-pc world)))
                  (unsigned-byte-p 64 target))
             (and (proof-segment-p (len path) (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after) (proof-world-reg (if swapped 1 0) world))
                  (equal (proof-world-reg 1 after) (proof-world-reg (if swapped 0 1) world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-invert-path a zero negative box world))
                            (cuts (list (proof-number-invert-target a zero negative box))))
                 (:instance proof-number-tagged-zero-and-one (value a)
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-boxed-integer-sign (value a)
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-value-has-immediate-word (value a)
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world))))
           :in-theory (e/d (proof-number-invert-path proof-number-invert-instructions
                                                     proof-number-invert-target
                                                     proof-number-reduced-p)
                           (proof-number-immediate-word-bits proof-integer-word))
           :do-not-induct t))
  :rule-classes nil)
