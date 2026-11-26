(in-package "BOYMOO-PROOFS")

; The whole immediate path of the entry for BINARY-LOGXOR.  The first
; five instructions of jet:ACL2::BINARY-LOGXOR are the AND of x0 and x1,
; the test of its low bit, the branch away from the immediate path, the
; XOR of x0 with x1 and the addition of one.  The theorem below runs
; all five on a machine whose x0 and x1 hold the tagged words of two
; immediate integers.  It shows that the branch falls through, so that
; the program counter ends 20 bytes on, at the return instruction, and
; that x0 then holds the tagged word of their XOR.

(include-book "entry-tests")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp lognot
                           acl2::binary-logand acl2::binary-logior
                           acl2::binary-logxor
                           boymoo-model::a64-unsigned)))

(local (in-theory (enable integer-a64-unsigned-is-mod)))

(defthm integer-pc-after-pc
  (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
         (mod (ifix pc) 18446744073709551616))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-pc boymoo-model::a64-set-pc))))

(defthm integer-mod-sum-of-mod
  (implies (and (integerp x) (integerp y))
           (equal (mod (+ y (mod x 18446744073709551616)) 18446744073709551616)
                  (mod (+ x y) 18446744073709551616)))
  :hints (("Goal"
           :use ((:instance integer-mod-as-difference (d 18446744073709551616))
                 (:instance integer-mod-minus-multiple
                            (z (+ x y)) (m 18446744073709551616)
                            (tt (floor x 18446744073709551616)))))))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-nzcv boymoo-model::a64-pc
                     integer-run-straight proof-integer-word)))

(defthm integer-logxor-path-steps
  (let ((after (integer-run-straight
                (integer-runtime-instructions "jet:ACL2::BINARY-LOGXOR" 0 5) machine)))
    (implies (and (equal (mod (boymoo-model::a64-read-reg 0 64 nil machine) 2) 1)
                  (equal (mod (boymoo-model::a64-read-reg 1 64 nil machine) 2) 1))
             (and (equal (boymoo-model::a64-read-reg 0 64 nil after)
                         (mod (+ 1 (mod (logxor (boymoo-model::a64-read-reg 0 64 nil machine)
                                                (boymoo-model::a64-read-reg 1 64 nil machine))
                                        18446744073709551616))
                              18446744073709551616))
                  (equal (boymoo-model::a64-pc after)
                         (mod (+ 20 (boymoo-model::a64-pc machine))
                              18446744073709551616))))))

(defthm integer-logxor-immediate-whole-path
  (implies (and (proof-immediate-integer-p a)
                (proof-immediate-integer-p b)
                (equal (boymoo-model::a64-read-reg 0 64 nil machine)
                       (proof-integer-word a))
                (equal (boymoo-model::a64-read-reg 1 64 nil machine)
                       (proof-integer-word b)))
           (let ((after (integer-run-straight
                         (integer-runtime-instructions "jet:ACL2::BINARY-LOGXOR" 0 5)
                         machine)))
             (and (equal (boymoo-model::a64-read-reg 0 64 nil after)
                         (proof-integer-word (logxor a b)))
                  (equal (boymoo-model::a64-pc after)
                         (mod (+ 20 (boymoo-model::a64-pc machine))
                              18446744073709551616)))))
  :hints (("Goal"
           :in-theory (e/d (proof-integer-word)
                           (integer-runtime-instructions
                            (:executable-counterpart integer-runtime-instructions)
                            integer-logxor-path-steps
                            integer-logxor-immediate-words
                            proof-immediate-integer-p))
           :use (integer-logxor-path-steps
                 integer-logxor-immediate-words
                 (:instance integer-immediate-word-odd (value a))
                 (:instance integer-immediate-word-odd (value b))))))
