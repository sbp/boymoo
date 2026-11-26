(in-package "BOYMOO-PROOFS")

; The count of the entry for ASH on immediate operands.  The instruction
; at byte offset 20 of jet:COMMON-LISP::ASH shifts the tagged word in x1
; right arithmetically by one into x2.  The first theorem below shows
; that x2 then holds the 64-bit pattern of the count, which is the form
; that ash-right-branch.lisp and ash-left-branch.lisp assume.  The
; others show how the two comparisons that follow choose between the
; right-shift branch, the left-shift branch and rt:n-ash.

(include-book "ash-left-branch")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp lognot
                           acl2::binary-logand acl2::binary-logior
                           acl2::binary-logxor
                           boymoo-model::a64-unsigned)))

(local (in-theory (enable integer-a64-unsigned-is-mod)))

(defthm integer-half-of-tagged-word
  (implies (proof-immediate-integer-p c)
           (equal (floor (proof-integer-word c) 2)
                  (if (< c 0) (+ 9223372036854775808 c) c)))
  :hints (("Goal" :cases ((< c 0))
           :use ((:instance integer-floor-of-double-plus-bit (high c) (low 1))
                 (:instance integer-floor-of-double-plus-bit
                            (high (+ 9223372036854775808 c)) (low 1))))))

(defthm integer-top-bit-of-tagged-word
  (implies (proof-immediate-integer-p c)
           (equal (logbitp 63 (proof-integer-word c)) (< c 0)))
  :hints (("Goal" :cases ((< c 0))
           :use ((:instance integer-floor-of-in-range
                            (x (proof-integer-word c)) (d 9223372036854775808))
                 (:instance integer-floor-unique
                            (x (proof-integer-word c)) (y 9223372036854775808) (q 1))))))

(defthm integer-logior-zero-right
  (implies (integerp x)
           (equal (logior x 0) x))
  :hints (("Goal" :in-theory (enable acl2::binary-logior lognot))))

(local
 (defthm integer-count-product-swap
   (equal (* x (* y z)) (* y (* x z)))
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-* (acl2::x x) (acl2::y y) (acl2::z z))
                  (:instance associativity-of-* (acl2::x y) (acl2::y x) (acl2::z z)))))))

(local
 (defun integer-high-disjoint-induction (n a)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       a
     (integer-high-disjoint-induction (1- n) (floor a 2)))))

(defthm integer-logior-disjoint-high
  (implies (and (natp n) (natp a) (< a (expt 2 n)) (integerp b))
           (equal (logior (* b (expt 2 n)) a) (+ a (* b (expt 2 n)))))
  :hints (("Goal" :induct (integer-high-disjoint-induction n a))
          ("Subgoal *1/1" :in-theory (enable expt))
          ("Subgoal *1/2"
           :use ((:instance integer-logior-split (x (* b (expt 2 n))) (y a))
                 (:instance integer-floor-and-mod-decomposition (x a) (d 2))
                 (:instance integer-floor-of-double-plus-bit
                            (high (* b (expt 2 (1- n)))) (low 0))
                 (:instance integer-mod-of-double-plus-bit
                            (high (* b (expt 2 (1- n)))) (low 0))
                 (:instance integer-floor-bounds (x a) (y 2)))
           :in-theory (enable integer-power-of-two-step))))

(defthm integer-sign-fill
  (implies (and (integerp c) (<= -4611686018427387904 c) (< c 0))
           (equal (logior -9223372036854775808 (+ 9223372036854775808 c)) c))
  :hints (("Goal"
           :in-theory (disable integer-logior-disjoint-high)
           :use ((:instance integer-logior-disjoint-high
                            (n 63) (a (+ 9223372036854775808 c)) (b -1))))))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-nzcv boymoo-model::a64-pc
                     integer-run-straight proof-integer-word)))

; When x1 holds the tagged word of an immediate count C, the
; instruction at byte offset 20 leaves the 64-bit pattern of C in x2.
(defthm integer-ash-count-step
  (implies (and (proof-immediate-integer-p c)
                (equal (boymoo-model::a64-read-reg 1 64 nil machine)
                       (proof-integer-word c)))
           (equal (boymoo-model::a64-read-reg
                   2 64 nil
                   (integer-run-straight
                    (integer-runtime-instructions "jet:COMMON-LISP::ASH" 20 1) machine))
                  (mod c 18446744073709551616)))
  :hints (("Goal" :cases ((< c 0))
           :use ((:instance integer-mod-plus-multiple
                            (z (+ 9223372036854775808 c)) (m 9223372036854775808)
                            (tt (proof-integer-word c)))
                 (:instance integer-mod-plus-multiple
                            (z c) (m 9223372036854775808)
                            (tt (proof-integer-word c)))))))

(defthm integer-signed-of-count-pattern
  (implies (proof-immediate-integer-p c)
           (equal (boymoo-model::a64-signed 64 (mod c 18446744073709551616)) c))
  :hints (("Goal" :cases ((< c 0)))))

(defthm integer-top-bit-of-count-pattern
  (implies (and (integerp c)
                (<= -9223372036854775808 c) (< c 9223372036854775808))
           (equal (logbitp 63 (mod c 18446744073709551616)) (< c 0)))
  :hints (("Goal" :cases ((< c 0))
           :use ((:instance integer-floor-of-in-range
                            (x c) (d 9223372036854775808))
                 (:instance integer-floor-unique
                            (x (+ 18446744073709551616 c)) (y 9223372036854775808)
                            (q 1))))))

(defthm integer-count-minus-62
  (implies (and (integerp c) (<= 0 c) (< c 4611686018427387904))
           (equal (mod (+ 18446744073709551554 c) 18446744073709551616)
                  (if (< c 62) (+ 18446744073709551554 c) (- c 62))))
  :hints (("Goal" :cases ((< c 62))
           :use ((:instance integer-mod-unique
                            (x (+ 18446744073709551554 c)) (d 18446744073709551616)
                            (q 1) (r (- c 62)))))))

; With the 64-bit pattern of an immediate count C in x2, the comparison
; at byte offset 24 makes the condition "less than" of the branch at
; byte offset 28 hold exactly when C is negative, so the entry goes to
; rt:ash-right exactly for a negative count.
(defthm integer-ash-count-sign-test
  (implies (and (proof-immediate-integer-p c)
                (equal (boymoo-model::a64-read-reg 2 64 nil machine)
                       (mod c 18446744073709551616)))
           (equal (boymoo-model::a64-condition
                   11 (boymoo-model::a64-nzcv
                       (integer-run-straight
                        (integer-runtime-instructions "jet:COMMON-LISP::ASH" 24 1)
                        machine)))
                  (< c 0)))
  :hints (("Goal" :cases ((< c 0))
           :use ((:instance integer-top-bit-of-count-pattern)
                 (:instance integer-mod-plus-multiple
                            (z (boymoo-model::a64-read-reg 2 64 nil machine))
                            (m 18446744073709551616) (tt 1))
                 (:instance integer-floor-unique
                            (x (+ 18446744073709551616
                                  (boymoo-model::a64-read-reg 2 64 nil machine)))
                            (y 18446744073709551616) (q 1))))))

; With a count C from 0 to 2^62 - 1 in x2, the comparison at byte
; offset 32 makes the condition "greater than" of the branch at byte
; offset 36 hold exactly when C exceeds 62, so the entry goes on to
; byte offset 40 exactly for a count from 0 to 62.
(defthm integer-ash-count-size-test
  (implies (and (integerp c) (<= 0 c) (< c 4611686018427387904)
                (equal (boymoo-model::a64-read-reg 2 64 nil machine) c))
           (equal (boymoo-model::a64-condition
                   12 (boymoo-model::a64-nzcv
                       (integer-run-straight
                        (integer-runtime-instructions "jet:COMMON-LISP::ASH" 32 1)
                        machine)))
                  (< 62 c)))
  :hints (("Goal" :cases ((< c 62))
           :use ((:instance integer-top-bit-of-count-pattern (c (- c 62)))
                 (:instance integer-signed-of-count-pattern (c (- c 62)))))))
