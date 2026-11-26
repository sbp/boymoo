(in-package "BOYMOO-PROOFS")

(include-book "effects")
(include-book "shifts")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor mod expt acl2::binary-logand acl2::binary-logior
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defun division-left-mask-induct (shift)
   (declare (xargs :measure (nfix shift)))
   (if (zp shift)
       0
     (division-left-mask-induct (1- shift)))))

(local
 (defthm division-logand-scales-with-bit-position
   (implies (and (natp shift) (integerp left) (integerp right))
            (equal (logand (* (expt 2 shift) left) (* (expt 2 shift) right))
                   (* (expt 2 shift) (logand left right))))
   :hints (("Goal" :induct (division-left-mask-induct shift))
           ("Subgoal *1/2"
            :expand ((expt 2 shift))
            :use ((:instance division-logand-split (x (* 2 (expt 2 (1- shift)) left))
                             (y (* 2 (expt 2 (1- shift)) right)))
                  (:instance division-signed-quotient-unique (a (* 2 (expt 2 (1- shift)) left))
                             (b 2) (q (* (expt 2 (1- shift)) left)) (r 0))
                  (:instance division-signed-quotient-unique (a (* 2 (expt 2 (1- shift)) right))
                             (b 2) (q (* (expt 2 (1- shift)) right)) (r 0))
                  (:instance division-signed-remainder-unique (a (* 2 (expt 2 (1- shift)) left))
                             (b 2) (q (* (expt 2 (1- shift)) left)) (r 0))
                  (:instance division-signed-remainder-unique (a (* 2 (expt 2 (1- shift)) right))
                             (b 2) (q (* (expt 2 (1- shift)) right)) (r 0))))
           ("Subgoal *1/1" :expand ((expt 2 shift))))
   :rule-classes nil))

(local
 (defthm division-left-bitfield-scaled-word-fits
   (implies (and (posp shift) (< shift 64) (unsigned-byte-p (- 64 shift) word))
            (unsigned-byte-p 64 (* word (expt 2 shift))))
   :hints (("Goal"
            :use ((:instance division-power-of-two-sum (left shift) (right (- 64 shift)))
                  (:instance division-power-of-two-positive (width shift))
                  (:instance division-positive-product-order (a word) (b (expt 2 (- 64 shift)))
                             (factor (expt 2 shift))))))
   :rule-classes nil))

(local
 (defthm division-left-bitfield-double-negation
   (implies (integerp value)
            (equal (- (- value)) value))))

(local
 (defthm division-rotation-of-fitted-left-shift
   (implies (and (posp shift) (< shift 64)
                 (unsigned-byte-p (- 64 shift) word) (unsigned-byte-p 64 word))
            (equal (boymoo-model::a64-ror 64 word (- 64 shift)) (* word (expt 2 shift))))
   :hints (("Goal"
            :use ((:instance division-signed-remainder-unique (a (- 64 shift)) (b 64) (q 0) (r (- 64 shift)))
                  (:instance division-signed-quotient-unique (a word) (b (expt 2 (- 64 shift))) (q 0) (r word))
                  (:instance division-power-of-two-positive (width (- 64 shift)))
                  (:instance division-ash-right (x word) (width (- 64 shift)))
                  (:instance division-ash-left (x word) (width shift))
                  (:instance division-left-bitfield-scaled-word-fits))
            :in-theory (e/d (boymoo-model::a64-ror) (division-ash-left division-ash-right))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-left-bitfield-fitted-value
  (implies (and (posp shift) (< shift 64)
                (unsigned-byte-p (- 64 shift) word) (unsigned-byte-p 64 word))
           (equal (logand (logand (boymoo-model::a64-ror 64 word (- 64 shift))
                                  (- *division-word-modulus* (expt 2 shift)))
                          (1- *division-word-modulus*))
                  (* word (expt 2 shift))))
  :hints (("Goal"
           :use ((:instance division-rotation-of-fitted-left-shift)
                 (:instance division-left-bitfield-scaled-word-fits)
                 (:instance division-power-of-two-sum (left shift) (right (- 64 shift)))
                 (:instance division-logand-scales-with-bit-position
                            (left word) (right (1- (expt 2 (- 64 shift)))))
                 (:instance division-unsigned-mask-is-logand (width (- 64 shift)))
                 (:instance division-unsigned-mask-is-logand (width 64) (word (* word (expt 2 shift)))))
           :in-theory (disable boymoo-model::a64-ror division-unsigned-mask-is-logand)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-bitfield-source-after-pc
   (equal (boymoo-model::a64-read-reg register 64 nil (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-read-reg register 64 nil machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc boymoo-model::a64-read-reg)))))

(local
 (defthmd division-bitfield-pc-of-world
   (equal (boymoo-model::a64-pc (proof-world-machine world)) (proof-world-pc world))))

(local
 (defthmd division-bitfield-source-of-world
   (equal (boymoo-model::a64-read-reg register 64 nil (proof-world-machine world))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(local
 (defthm division-bitfield-world-reads-replaced-machine
   (equal (proof-world-machine (cons machine rest)) machine)
   :hints (("Goal" :in-theory (enable proof-world-machine)))))

(local
 (defthm division-bitfield-set-pc-keeps-machine-kind
   (and (equal (car (boymoo-model::a64-set-pc value machine)) (car machine))
        (consp (boymoo-model::a64-set-pc value machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)
                   :expand ((update-nth 2 (boymoo-model::a64-unsigned 64 value) machine))))))

(defthm division-effect-logical-left-bitfield-without-wrap
  (implies (and (division-ordinary-world-p world)
                (unsigned-byte-p 5 dest) (unsigned-byte-p 5 source)
                (posp rotate) (< rotate 64)
                (equal last (1- rotate))
                (equal mask (- *division-word-modulus* (expt 2 (- 64 rotate))))
                (unsigned-byte-p rotate (proof-world-reg source world)))
           (equal (proof-instruction-effect (list :bitfield 2 64 dest source rotate last mask
                                                 (1- *division-word-modulus*)) world)
                  (division-write-reg dest nil (* (expt 2 (- 64 rotate)) (proof-world-reg source world))
                                      (division-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal"
           :use ((:instance division-left-bitfield-fitted-value
                            (shift (- 64 rotate)) (word (proof-world-reg source world)))
                 (:instance division-world-register-in-word (register source)))
           :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                            boymoo-model::a64-exec-bitfield division-ordinary-world-p
                            division-set-pc division-write-reg division-bitfield-pc-of-world
                            division-bitfield-source-of-world)
                           (proof-world-machine proof-world-pc proof-world-reg
                            boymoo-model::a64-read-reg boymoo-model::a64-set-pc boymoo-model::a64-ror
                            division-unsigned-mask-is-logand))
           :do-not-induct t)))
