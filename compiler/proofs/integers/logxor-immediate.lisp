(in-package "BOYMOO-PROOFS")

; The immediate path of the entry for BINARY-LOGXOR.  When both
; arguments are tagged immediate integers, the entry
; jet:ACL2::BINARY-LOGXOR in compiler/runtime.lisp computes the XOR of
; the two tagged words and adds one.  The theorems below show that the
; result is the tagged word of the XOR of the integers, both as
; arithmetic and as the execution of those two instructions on the
; A64 model.

(include-book "ash-right-branch")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp lognot
                           acl2::binary-logand acl2::binary-logior
                           acl2::binary-logxor
                           boymoo-model::a64-unsigned)))

(defthm integer-logxor-type
  (implies (and (integerp x) (integerp y))
           (integerp (logxor x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable acl2::binary-logxor))))

(local
 (defthm integer-floor-of-immediate-by-2^62
   (implies (proof-immediate-integer-p v)
            (equal (floor v 4611686018427387904) (if (< v 0) -1 0)))
   :hints (("Goal" :use ((:instance integer-floor-of-immediate-by-large-power
                                    (k 62)))))))

(defthm integer-logxor-of-immediates-is-immediate
  (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b))
           (proof-immediate-integer-p (logxor a b)))
  :hints (("Goal"
           :in-theory (disable proof-immediate-integer-p
                               integer-floor-of-logxor)
           :use ((:instance integer-floor-of-logxor (x a) (y b) (width 62))
                 (:instance integer-floor-scaled-bounds
                            (x (logxor a b)) (y 4611686018427387904))
                 (:instance (:definition proof-immediate-integer-p)
                            (value (logxor a b))))
           :cases ((< a 0)))
          ("Subgoal 2" :cases ((< b 0)))
          ("Subgoal 1" :cases ((< b 0)))))

(local (in-theory (enable integer-a64-unsigned-is-mod)))

; The XOR of the tagged words of two immediate integers, reduced modulo
; 2^64, plus one and reduced again, is the tagged word of their XOR.
(defthm integer-logxor-immediate-words
  (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b))
           (equal (mod (+ 1 (mod (logxor (proof-integer-word a)
                                         (proof-integer-word b))
                                 18446744073709551616))
                       18446744073709551616)
                  (proof-integer-word (logxor a b))))
  :hints (("Goal"
           :in-theory (disable proof-immediate-integer-p
                               integer-mod-of-logxor)
           :use ((:instance integer-mod-of-logxor
                            (x (+ 1 (* 2 a))) (y (+ 1 (* 2 b))) (width 64))
                 (:instance integer-logxor-of-doubled-integers
                            (x a) (y b) (low 1))
                 (:instance integer-mod-of-mod
                            (x (+ 1 (* 2 a))) (d 18446744073709551616))
                 (:instance integer-mod-minus-multiple
                            (z (+ 1 (* 2 (logxor a b))))
                            (m 18446744073709551616)
                            (tt (floor (* 2 (logxor a b)) 18446744073709551616)))
                 (:instance integer-mod-as-difference
                            (x (* 2 (logxor a b))) (d 18446744073709551616))))))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-nzcv boymoo-model::a64-pc
                     integer-run-straight boymoo-model::a64-ror)))

; The two instructions at offset 12 of jet:ACL2::BINARY-LOGXOR, the XOR
; of x0 with x1 and the addition of one, leave in x0 the XOR of the two
; registers plus one, each step reduced modulo 2^64.
(defthm integer-logxor-immediate-steps
  (equal (boymoo-model::a64-read-reg
          0 64 nil
          (integer-run-straight
           (integer-runtime-instructions "jet:ACL2::BINARY-LOGXOR" 12 2) machine))
         (mod (+ 1 (mod (logxor (boymoo-model::a64-read-reg 0 64 nil machine)
                                (boymoo-model::a64-read-reg 1 64 nil machine))
                        18446744073709551616))
              18446744073709551616)))

; On a machine whose x0 and x1 hold the tagged words of immediate
; integers A and B, those two instructions leave in x0 the tagged word
; of (logxor A B), which is again immediate.
(defthm integer-logxor-immediate-path-correct
  (implies (and (proof-immediate-integer-p a)
                (proof-immediate-integer-p b)
                (equal (boymoo-model::a64-read-reg 0 64 nil machine)
                       (proof-integer-word a))
                (equal (boymoo-model::a64-read-reg 1 64 nil machine)
                       (proof-integer-word b)))
           (and (proof-immediate-integer-p (logxor a b))
                (equal (boymoo-model::a64-read-reg
                        0 64 nil
                        (integer-run-straight
                         (integer-runtime-instructions "jet:ACL2::BINARY-LOGXOR" 12 2)
                         machine))
                       (proof-integer-word (logxor a b)))))
  :hints (("Goal"
           :in-theory (disable proof-integer-word proof-immediate-integer-p
                               integer-runtime-instructions
                               (:executable-counterpart integer-runtime-instructions)
                               integer-logxor-immediate-steps
                               integer-logxor-immediate-words)
           :use (integer-logxor-immediate-steps
                 integer-logxor-immediate-words
                 integer-logxor-of-immediates-is-immediate))))
