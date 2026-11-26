(in-package "BOYMOO-PROOFS")

; The first tests of the entries for ASH and BINARY-LOGXOR.  Both
; entries form the bitwise AND of x0 and x1, test its low bit, and
; branch away from the immediate path when that bit is clear.  The ASH
; entry first compares x0 with the tagged word 1 of zero.  The theorems
; below give, from the flags that the model computes, the outcome of
; each of these branches.

(include-book "ash-count")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp lognot
                           acl2::binary-logand acl2::binary-logior
                           acl2::binary-logxor
                           boymoo-model::a64-unsigned)))

(local (in-theory (enable integer-a64-unsigned-is-mod)))

(defthm integer-mod-even-then-2
  (implies (and (integerp x) (posp h))
           (equal (mod (mod x (* 2 h)) 2) (mod x 2)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable integer-mod-minus-multiple)
           :use ((:instance integer-mod-as-difference (d (* 2 h)))
                 (:instance integer-mod-minus-multiple
                            (z x) (m 2) (tt (* h (floor x (* 2 h)))))))))

(defthm integer-mod-64-then-2
  (implies (integerp x)
           (equal (mod (mod x 18446744073709551616) 2) (mod x 2)))
  :hints (("Goal" :use ((:instance integer-mod-even-then-2 (h 9223372036854775808))))))

(defthm integer-low-bit-mask
  (implies (integerp x)
           (equal (logand x 1) (mod x 2)))
  :hints (("Goal" :use ((:instance integer-logand-low-mask (width 1))))))

(defthm integer-logand-type
  (implies (and (integerp x) (integerp y))
           (integerp (logand x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable acl2::binary-logand))))

(defthm integer-low-bit-of-logand
  (implies (and (integerp x) (integerp y))
           (equal (mod (logand x y) 2)
                  (if (and (equal (mod x 2) 1) (equal (mod y 2) 1)) 1 0)))
  :hints (("Goal"
           :use ((:instance integer-logand-split)
                 (:instance integer-mod-of-double-plus-bit
                            (high (logand (floor x 2) (floor y 2)))
                            (low (if (and (oddp x) (oddp y)) 1 0)))))))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-nzcv boymoo-model::a64-pc
                     integer-run-straight proof-integer-word)))

; The AND of x0 and x1 followed by the test of its low bit, at byte
; offset 0 of the LOGXOR entry and byte offset 8 of the ASH entry, set
; the flags so that the condition "equal" of the branch that follows
; holds exactly when x0 or x1 is even.
(defthm integer-immediate-pair-test
  (implies (member-equal (list name offset)
                         '(("jet:ACL2::BINARY-LOGXOR" 0)
                           ("jet:COMMON-LISP::ASH" 8)))
           (equal (boymoo-model::a64-condition
                   0 (boymoo-model::a64-nzcv
                      (integer-run-straight
                       (integer-runtime-instructions name offset 2) machine)))
                  (not (and (equal (mod (boymoo-model::a64-read-reg 0 64 nil machine) 2) 1)
                            (equal (mod (boymoo-model::a64-read-reg 1 64 nil machine) 2) 1)))))
  :hints (("Goal" :in-theory (disable integer-runtime-instructions))))

; The tagged words of two immediate integers make that condition false,
; so both entries go on along their immediate paths.
(defthm integer-immediate-pair-test-of-words
  (implies (and (member-equal (list name offset)
                              '(("jet:ACL2::BINARY-LOGXOR" 0)
                                ("jet:COMMON-LISP::ASH" 8)))
                (proof-immediate-integer-p a)
                (proof-immediate-integer-p b)
                (equal (boymoo-model::a64-read-reg 0 64 nil machine)
                       (proof-integer-word a))
                (equal (boymoo-model::a64-read-reg 1 64 nil machine)
                       (proof-integer-word b)))
           (not (boymoo-model::a64-condition
                 0 (boymoo-model::a64-nzcv
                    (integer-run-straight
                     (integer-runtime-instructions name offset 2) machine)))))
  :hints (("Goal"
           :in-theory (e/d (proof-integer-word)
                           (integer-runtime-instructions proof-immediate-integer-p))
           :use ((:instance integer-immediate-word-odd (value a))
                 (:instance integer-immediate-word-odd (value b))))))

(defthm integer-equal-one-test
  (implies (and (natp r) (< r 18446744073709551616))
           (equal (equal (mod (+ 18446744073709551615 r) 18446744073709551616) 0)
                  (equal r 1)))
  :rule-classes nil
  :hints (("Goal" :cases ((< r 1) (equal r 1))
           :use ((:instance integer-mod-unique
                            (x (+ 18446744073709551615 r)) (d 18446744073709551616)
                            (q 1) (r (- r 1)))))))

; The comparison at byte offset 0 of the ASH entry sets the flags so
; that the condition "equal" of the branch at byte offset 4, which
; returns x0 at once, holds exactly when x0 is 1.
(defthm integer-ash-zero-test
  (equal (boymoo-model::a64-condition
          0 (boymoo-model::a64-nzcv
             (integer-run-straight
              (integer-runtime-instructions "jet:COMMON-LISP::ASH" 0 1) machine)))
         (equal (boymoo-model::a64-read-reg 0 64 nil machine) 1))
  :hints (("Goal"
           :use ((:instance integer-equal-one-test
                            (r (boymoo-model::a64-read-reg 0 64 nil machine)))))))

; The tagged word of an immediate integer is 1 exactly when the integer
; is zero.
(defthm integer-tagged-word-is-one
  (implies (proof-immediate-integer-p v)
           (equal (equal (proof-integer-word v) 1) (equal v 0)))
  :hints (("Goal" :in-theory (enable proof-integer-word)
           :cases ((< v 0)))))
