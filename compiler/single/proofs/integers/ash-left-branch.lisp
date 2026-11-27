(in-package "BOYMOO-PROOFS")

; The left-shift branch of the entry for ASH on immediate integers.
; The entry subtracts one from the tagged word of V, giving the 64-bit
; pattern X of 2V, shifts X left by the count C, shifts the result Y
; back right arithmetically by C, and compares the outcome with X.
; When they are equal it returns Y plus one.  The theorems below show
; that equality implies that V times 2^C is immediate and that Y plus
; one is its tagged word, first as arithmetic and then as the execution
; of the instructions of the entry on the A64 model.

(include-book "logxor-immediate")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp lognot
                           acl2::binary-logand acl2::binary-logior
                           acl2::binary-logxor
                           boymoo-model::a64-unsigned)))

(local
 (defthm integer-left-product-swap
   (equal (* x (* y z)) (* y (* x z)))
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-* (acl2::x x) (acl2::y y) (acl2::z z))
                  (:instance associativity-of-* (acl2::x y) (acl2::y x) (acl2::z z)))))))

; Two integers of the signed 64-bit range that agree modulo 2^64 are
; equal.
(defthm integer-signed-window-equal
  (implies (and (integerp a) (integerp b)
                (<= -9223372036854775808 a) (< a 9223372036854775808)
                (<= -9223372036854775808 b) (< b 9223372036854775808)
                (equal (mod a 18446744073709551616) (mod b 18446744073709551616)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :cases ((and (< a 0) (< b 0))
                          (and (< a 0) (<= 0 b))
                          (and (<= 0 a) (< b 0))))))

(defthm integer-signed-of-pattern
  (implies (and (natp y) (< y 18446744073709551616))
           (equal (boymoo-model::a64-signed 64 y)
                  (if (< y 9223372036854775808) y (- y 18446744073709551616))))
  :hints (("Goal" :use ((:instance integer-a64-signed-test (width 64) (x y))))))

(defthm integer-signed-64-range
  (implies (and (natp y) (< y 18446744073709551616))
           (and (<= -9223372036854775808 (boymoo-model::a64-signed 64 y))
                (< (boymoo-model::a64-signed 64 y) 9223372036854775808)))
  :rule-classes nil)

(defthm integer-pattern-of-double
  (implies (proof-immediate-integer-p v)
           (equal (mod (* 2 v) 18446744073709551616)
                  (if (< v 0) (+ 18446744073709551616 (* 2 v)) (* 2 v)))))

(defthm integer-shifted-pattern
  (implies (and (proof-immediate-integer-p v) (natp p))
           (equal (mod (* (mod (* 2 v) 18446744073709551616) p) 18446744073709551616)
                  (mod (* 2 v p) 18446744073709551616)))
  :hints (("Goal" :cases ((< v 0))
           :use ((:instance integer-mod-plus-multiple
                            (z (* 2 v p)) (m 18446744073709551616) (tt p))))))

(defthm integer-left-shift-test-sound
  (implies (and (proof-immediate-integer-p v)
                (natp c) (<= c 62)
                (equal (mod (floor (boymoo-model::a64-signed
                                    64 (mod (* 2 v (expt 2 c)) 18446744073709551616))
                                   (expt 2 c))
                            18446744073709551616)
                       (mod (* 2 v) 18446744073709551616)))
           (and (proof-immediate-integer-p (* v (expt 2 c)))
                (equal (mod (+ 1 (mod (* 2 v (expt 2 c)) 18446744073709551616))
                            18446744073709551616)
                       (proof-integer-word (* v (expt 2 c))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable integer-pattern-of-double)
           :use ((:instance integer-power-of-two-at-least (a c) (b 62))
                 (:instance integer-signed-64-range
                            (y (mod (* 2 v (expt 2 c)) 18446744073709551616)))
                 (:instance integer-signed-window-equal
                            (a (floor (boymoo-model::a64-signed
                                       64 (mod (* 2 v (expt 2 c)) 18446744073709551616))
                                      (expt 2 c)))
                            (b (* 2 v)))
                 (:instance integer-floor-scaled-bounds
                            (x (boymoo-model::a64-signed
                                64 (mod (* 2 v (expt 2 c)) 18446744073709551616)))
                            (y (expt 2 c)))
                 (:instance integer-floor-and-mod-decomposition
                            (x (* 2 v (expt 2 c))) (d 18446744073709551616))
                 (:instance integer-mod-unique
                            (x (+ 1 (* 2 v (expt 2 c)))) (d 18446744073709551616)
                            (q (floor (* 2 v (expt 2 c)) 18446744073709551616))
                            (r (+ 1 (mod (* 2 v (expt 2 c)) 18446744073709551616)))))
           :nonlinearp t)))

(local (in-theory (enable integer-a64-unsigned-is-mod)))

(defthm integer-tagged-word-minus-one
  (implies (proof-immediate-integer-p v)
           (equal (mod (+ 18446744073709551615 (proof-integer-word v))
                       18446744073709551616)
                  (mod (* 2 v) 18446744073709551616)))
  :hints (("Goal" :cases ((< v 0))
           :use ((:instance integer-mod-plus-multiple
                            (z (* 2 v)) (m 18446744073709551616) (tt 1))
                 (:instance integer-mod-plus-multiple
                            (z (+ 18446744073709551616 (* 2 v)))
                            (m 18446744073709551616) (tt 1))))))

; The arithmetic of the left-shift branch, with the model's shifts.
; X is the tagged word of V minus one modulo 2^64, Y is X shifted left
; by C and the test compares Y shifted right arithmetically by C with X.
(defthm integer-ash-immediate-left-shift
  (implies (and (proof-immediate-integer-p v)
                (natp c)
                (<= c 62)
                (equal (boymoo-model::a64-shift
                        2 64
                        (boymoo-model::a64-shift
                         0 64 (mod (+ 18446744073709551615 (proof-integer-word v))
                                   18446744073709551616)
                         c)
                        c)
                       (mod (+ 18446744073709551615 (proof-integer-word v))
                            18446744073709551616)))
           (and (proof-immediate-integer-p (ash v c))
                (equal (mod (+ 1 (boymoo-model::a64-shift
                                  0 64 (mod (+ 18446744073709551615 (proof-integer-word v))
                                            18446744073709551616)
                                  c))
                            18446744073709551616)
                       (proof-integer-word (ash v c)))))
  :hints (("Goal"
           :in-theory (e/d (integer-ash-right)
                           (proof-integer-word proof-immediate-integer-p))
           :use ((:instance integer-left-shift-test-sound)
                 (:instance integer-shifted-pattern (p (expt 2 c)))))))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-nzcv boymoo-model::a64-pc
                     integer-run-straight boymoo-model::a64-ror)))

; The three instructions at byte offset 40 of jet:COMMON-LISP::ASH
; subtract one from x0 into x3, shift x3 left by x2 into x4, and shift
; x4 right arithmetically by x2 into x5.
(defthm integer-ash-left-shift-steps
  (let ((after (integer-run-straight
                (integer-runtime-instructions "jet:COMMON-LISP::ASH" 40 3) machine))
        (x (mod (+ 18446744073709551615 (boymoo-model::a64-read-reg 0 64 nil machine))
                18446744073709551616))
        (n (mod (boymoo-model::a64-read-reg 2 64 nil machine) 64)))
    (and (equal (boymoo-model::a64-read-reg 3 64 nil after) x)
         (equal (boymoo-model::a64-read-reg 4 64 nil after)
                (boymoo-model::a64-shift 0 64 x n))
         (equal (boymoo-model::a64-read-reg 5 64 nil after)
                (boymoo-model::a64-shift 2 64 (boymoo-model::a64-shift 0 64 x n) n))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-shift))))

; The instruction at byte offset 60 adds one to x4 and puts the sum in
; x0.
(defthm integer-ash-left-return-step
  (equal (boymoo-model::a64-read-reg
          0 64 nil
          (integer-run-straight
           (integer-runtime-instructions "jet:COMMON-LISP::ASH" 60 1) machine))
         (mod (+ 1 (boymoo-model::a64-read-reg 4 64 nil machine))
              18446744073709551616)))

; On a machine whose x0 holds the tagged word of an immediate integer V
; and whose x2 holds a count C from 0 to 62, the instructions at byte
; offset 40 compute X, Y and the shifted-back value.  When the shifted
; back value in x5 equals X in x3, which is the comparison after which
; the entry goes on to byte offset 60, the instruction there leaves in
; x0 the tagged word of (ash V C), and that integer is immediate.
(defthm integer-ash-left-branch-correct
  (implies (and (proof-immediate-integer-p v)
                (natp c)
                (<= c 62)
                (equal (boymoo-model::a64-read-reg 0 64 nil machine)
                       (proof-integer-word v))
                (equal (boymoo-model::a64-read-reg 2 64 nil machine) c)
                (equal (boymoo-model::a64-read-reg
                        5 64 nil
                        (integer-run-straight
                         (integer-runtime-instructions "jet:COMMON-LISP::ASH" 40 3)
                         machine))
                       (boymoo-model::a64-read-reg
                        3 64 nil
                        (integer-run-straight
                         (integer-runtime-instructions "jet:COMMON-LISP::ASH" 40 3)
                         machine))))
           (and (proof-immediate-integer-p (ash v c))
                (equal (boymoo-model::a64-read-reg
                        0 64 nil
                        (integer-run-straight
                         (integer-runtime-instructions "jet:COMMON-LISP::ASH" 60 1)
                         (integer-run-straight
                          (integer-runtime-instructions "jet:COMMON-LISP::ASH" 40 3)
                          machine)))
                       (proof-integer-word (ash v c)))))
  :hints (("Goal"
           :in-theory (disable proof-integer-word proof-immediate-integer-p
                               boymoo-model::a64-shift integer-runtime-instructions
                               (:executable-counterpart integer-runtime-instructions)
                               integer-ash-left-shift-steps
                               integer-ash-left-return-step
                               integer-ash-immediate-left-shift
                               integer-tagged-word-minus-one
                               ash)
           :use ((:instance integer-ash-left-shift-steps)
                 (:instance integer-ash-left-return-step
                            (machine (integer-run-straight
                                      (integer-runtime-instructions
                                       "jet:COMMON-LISP::ASH" 40 3)
                                      machine)))
                 (:instance integer-ash-immediate-left-shift)))))

(defthm integer-zero-difference-test
  (implies (and (natp a) (< a 18446744073709551616)
                (natp b) (< b 18446744073709551616))
           (equal (equal (mod (+ 18446744073709551616 a (- b)) 18446744073709551616) 0)
                  (equal a b)))
  :rule-classes nil
  :hints (("Goal" :cases ((< a b) (equal a b))
           :use ((:instance integer-mod-plus-multiple
                            (z (- a b)) (m 18446744073709551616) (tt 1))))))

; The comparison at byte offset 52 of jet:COMMON-LISP::ASH sets the
; flags so that the condition "not equal" of the branch at byte offset
; 56 holds exactly when x5 differs from x3.  The branch therefore falls
; through to byte offset 60 exactly when x5 equals x3.
(defthm integer-ash-left-compare-step
  (equal (boymoo-model::a64-condition
          1 (boymoo-model::a64-nzcv
             (integer-run-straight
              (integer-runtime-instructions "jet:COMMON-LISP::ASH" 52 1) machine)))
         (not (equal (boymoo-model::a64-read-reg 5 64 nil machine)
                     (boymoo-model::a64-read-reg 3 64 nil machine))))
  :hints (("Goal"
           :use ((:instance integer-zero-difference-test
                            (a (boymoo-model::a64-read-reg 5 64 nil machine))
                            (b (boymoo-model::a64-read-reg 3 64 nil machine)))))))
