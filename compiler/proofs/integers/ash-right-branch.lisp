(in-package "BOYMOO-PROOFS")

; The right-shift branch of the entry for ASH, executed instruction by
; instruction on the A64 model.  The eight instructions that follow the
; label rt:ash-right in compiler/runtime.lisp are decoded from the
; assembled runtime image and executed with a64-execute on a machine
; whose x0 holds the tagged word of an immediate integer V and whose x2
; holds the negative shift count -K.  The theorem at the end shows that
; x0 then holds the tagged word of (ash V (- K)).

(include-book "ash-immediate")
(include-book "runtime-image")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp lognot
                           acl2::binary-logand acl2::binary-logior
                           acl2::binary-logxor)))

; Straight-line execution of a list of decoded instructions.
(defun integer-run-straight (instructions machine)
  (if (atom instructions)
      machine
    (integer-run-straight (cdr instructions)
                          (boymoo-model::a64-execute (car instructions) machine))))

; The register file.

(defthm integer-assoc-of-put-assoc
  (implies (and (natp key) (natp other))
           (equal (assoc-equal key (put-assoc-equal other value alist))
                  (if (equal key other)
                      (cons other value)
                    (assoc-equal key alist)))))

(local (in-theory (disable integer-a64-unsigned-is-mod boymoo-model::a64-unsigned)))

(defthm integer-read-written-register
  (implies (and (natp r) (< r 31) (natp s) (< s 31))
           (equal (boymoo-model::a64-read-reg
                   r 64 use (boymoo-model::a64-write-reg s 64 use2 value machine))
                  (if (equal r s)
                      (boymoo-model::a64-unsigned 64 value)
                    (boymoo-model::a64-read-reg r 64 use machine)))))

(defthm integer-read-register-ignores-use
  (implies (and (natp r) (< r 31) use)
           (equal (boymoo-model::a64-read-reg r 64 use machine)
                  (boymoo-model::a64-read-reg r 64 nil machine))))

(defthm integer-read-zero-register
  (equal (boymoo-model::a64-read-reg 31 64 nil machine) 0))

(defthm integer-write-zero-register
  (equal (boymoo-model::a64-write-reg 31 64 nil value machine) machine))

(defthm integer-read-register-after-pc
  (equal (boymoo-model::a64-read-reg r w use (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-read-reg r w use machine)))

(defthm integer-read-register-after-flags
  (equal (boymoo-model::a64-read-reg r w use (boymoo-model::a64-set-nzcv n machine))
         (boymoo-model::a64-read-reg r w use machine)))

(defthm integer-flags-after-pc
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-nzcv machine)))

(defthm integer-flags-after-flags
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-nzcv n machine))
         (boymoo-model::a64-unsigned 4 (boymoo-model::a64-unsigned 4 n))))

(defthm integer-flags-after-register
  (implies (and (natp r) (< r 31))
           (equal (boymoo-model::a64-nzcv
                   (boymoo-model::a64-write-reg r 64 use value machine))
                  (boymoo-model::a64-nzcv machine))))

(defthm integer-pc-after-register
  (implies (and (natp r) (< r 31))
           (equal (boymoo-model::a64-pc
                   (boymoo-model::a64-write-reg r 64 use value machine))
                  (boymoo-model::a64-pc machine))))

(defthm integer-pc-after-flags
  (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv n machine))
         (boymoo-model::a64-pc machine)))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-nzcv boymoo-model::a64-pc)))

; Word arithmetic.

(local (in-theory (enable integer-a64-unsigned-is-mod)))

(defthm integer-logior-zero
  (implies (integerp x)
           (equal (logior 0 x) x))
  :hints (("Goal" :in-theory (enable acl2::binary-logior lognot))))

(defthm integer-logxor-minus-one
  (implies (integerp x)
           (equal (logxor x -1) (- -1 x)))
  :hints (("Goal" :in-theory (enable acl2::binary-logxor acl2::binary-logeqv
                                     logorc1 acl2::binary-logior lognot))))

(defthm integer-logxor-all-ones
  (implies (and (natp x) (< x (expt 2 64)))
           (equal (logxor x 18446744073709551615)
                  (- 18446744073709551615 x)))
  :hints (("Goal" :use ((:instance integer-mod-of-logxor (y -1) (width 64))))))

(defthm integer-negative-count-word
  (implies (and (posp k) (<= k (expt 2 62)))
           (equal (boymoo-model::a64-unsigned 64 (- k))
                  (- 18446744073709551616 k))))

(defthm integer-compare-carry
  (implies (and (posp k) (<= k (expt 2 62)))
           (equal (logbitp 64 (+ 18446744073709551553 k))
                  (<= 63 k)))
  :hints (("Goal" :cases ((<= 63 k))
           :use ((:instance integer-floor-unique
                            (x (+ 18446744073709551553 k)) (y (expt 2 64)) (q 1))
                 (:instance integer-floor-unique
                            (x (+ 18446744073709551553 k)) (y (expt 2 64)) (q 0))))))

(defthm integer-compare-difference
  (implies (and (posp k) (<= k (expt 2 62)))
           (equal (mod (+ 18446744073709551553 k) 18446744073709551616)
                  (if (<= 63 k) (- k 63) (+ 18446744073709551553 k))))
  :hints (("Goal" :cases ((<= 63 k))
           :use ((:instance integer-mod-unique
                            (x (+ 18446744073709551553 k)) (d (expt 2 64))
                            (q 1) (r (- k 63)))))))

(local
 (defthm integer-product-swap
   (equal (* x (* y z)) (* y (* x z)))
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-* (acl2::x x) (acl2::y y) (acl2::z z))
                  (:instance associativity-of-* (acl2::x y) (acl2::y x) (acl2::z z)))))))

(local
 (defun integer-disjoint-induction (n a)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       a
     (integer-disjoint-induction (1- n) (floor a 2)))))

(defthm integer-logior-disjoint
  (implies (and (natp n) (natp a) (< a (expt 2 n)) (integerp b))
           (equal (logior a (* b (expt 2 n))) (+ a (* b (expt 2 n)))))
  :hints (("Goal" :induct (integer-disjoint-induction n a))
          ("Subgoal *1/1" :in-theory (enable expt))
          ("Subgoal *1/2"
           :use ((:instance integer-logior-split (x a) (y (* b (expt 2 n))))
                 (:instance integer-floor-and-mod-decomposition (x a) (d 2))
                 (:instance integer-floor-of-double-plus-bit
                            (high (* b (expt 2 (1- n)))) (low 0))
                 (:instance integer-mod-of-double-plus-bit
                            (high (* b (expt 2 (1- n)))) (low 0))
                 (:instance integer-floor-bounds (x a) (y 2)))
           :in-theory (enable integer-power-of-two-step))))

(local
 (defthm integer-branch-product-negation
   (implies (and (rationalp a) (rationalp b))
            (equal (* a (- b)) (- (* a b))))
   :hints (("Goal" :in-theory (disable distributivity)
            :use ((:instance distributivity (acl2::x a)
                                            (acl2::y b) (acl2::z (- b))))))))

(local
 (defthm integer-double-negation
   (equal (- (- x)) (fix x))))

(defthm integer-mod-plus-multiple
  (implies (and (integerp z) (integerp tt) (posp m))
           (equal (mod (+ z (* m tt)) m) (mod z m)))
  :hints (("Goal" :use ((:instance integer-mod-minus-multiple (tt (- tt)))))))

(local
 (defthm integer-fold-power
   (equal (* 9223372036854775808 (* 2 y)) (* 18446744073709551616 y))
   :hints (("Goal" :in-theory (disable associativity-of-* integer-product-swap)
            :use ((:instance associativity-of-*
                             (acl2::x 9223372036854775808) (acl2::y 2) (acl2::z y)))))))

(defthm integer-mod-64-then-63
  (implies (integerp x)
           (equal (mod (mod x 18446744073709551616) 9223372036854775808)
                  (mod x 9223372036854775808)))
  :hints (("Goal" :in-theory (disable integer-product-swap)
           :use ((:instance integer-mod-as-difference (d 18446744073709551616))
                 (:instance integer-mod-minus-multiple
                            (z x) (m 9223372036854775808)
                            (tt (* 2 (floor x 18446744073709551616))))))))

(defthm integer-low-64-mask
  (implies (and (natp r) (< r 18446744073709551616))
           (equal (logand r 18446744073709551615) r))
  :hints (("Goal" :use ((:instance integer-logand-low-mask (x r) (width 64))))))

(defthm integer-low-63-mask
  (implies (integerp r)
           (equal (logand r 9223372036854775807) (mod r 9223372036854775808)))
  :hints (("Goal" :use ((:instance integer-logand-low-mask (x r) (width 63))))))

(defthm integer-rotate-right-one
  (implies (and (natp s) (< s 18446744073709551616))
           (equal (boymoo-model::a64-ror 64 s 1)
                  (mod (+ (floor s 2) (* s 9223372036854775808))
                       18446744073709551616)))
  :hints (("Goal"
           :in-theory (enable integer-ash-right)
           :use ((:instance integer-logior-disjoint (n 63) (a (floor s 2)) (b s))
                 (:instance integer-floor-bounds (x s) (y 2))))))

(defthm integer-rotate-right-63
  (implies (and (natp f) (< f 9223372036854775808))
           (equal (boymoo-model::a64-ror 64 f 63) (* 2 f)))
  :hints (("Goal"
           :in-theory (enable integer-ash-right)
           :use ((:instance integer-floor-of-in-range
                            (x f) (d 9223372036854775808))))))

(defthm integer-logical-shift-right-one
  (implies (and (natp s) (< s 18446744073709551616))
           (equal (logior 0 (logand (logand (boymoo-model::a64-ror 64 s 1)
                                            18446744073709551615)
                                    9223372036854775807))
                  (floor s 2)))
  :hints (("Goal"
           :in-theory (disable boymoo-model::a64-ror)
           :use ((:instance integer-floor-bounds (x s) (y 2))
                 (:instance integer-mod-plus-multiple
                            (z (floor s 2)) (m 9223372036854775808) (tt s))))))

(defthm integer-clear-high-and-low
  (implies (and (natp f) (< f 9223372036854775808))
           (equal (logand (* 2 f) 18446744073709551614) (* 2 f)))
  :hints (("Goal"
           :use ((:instance integer-logand-split
                            (x (* 2 f)) (y 18446744073709551614))
                 (:instance integer-floor-of-double-plus-bit (high f) (low 0))
                 (:instance integer-mod-of-double-plus-bit (high f) (low 0))))))

(defthm integer-logical-shift-left-one
  (implies (and (natp f) (< f 9223372036854775808))
           (equal (logior 0 (logand (logand (boymoo-model::a64-ror 64 f 63)
                                            18446744073709551614)
                                    18446744073709551615))
                  (* 2 f)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-ror))))

(defthm integer-mod-of-mod
  (implies (and (integerp x) (posp d))
           (equal (mod (mod x d) d) (mod x d))))

(defthm integer-run-straight-step
  (implies (consp instructions)
           (equal (integer-run-straight instructions machine)
                  (integer-run-straight
                   (cdr instructions)
                   (boymoo-model::a64-execute (car instructions) machine))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-execute))))

(defthm integer-run-straight-end
  (implies (atom instructions)
           (equal (integer-run-straight instructions machine) machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-execute))))

(local (in-theory (disable integer-run-straight boymoo-model::a64-ror)))

(defthm integer-run-straight-append
  (equal (integer-run-straight (append first second) machine)
         (integer-run-straight second (integer-run-straight first machine)))
  :hints (("Goal" :in-theory (e/d (integer-run-straight) (boymoo-model::a64-execute)))))

(defthm integer-a64-shift-64-type
  (natp (boymoo-model::a64-shift kind 64 x n))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance integer-a64-unsigned-type
                                   (width 64)
                                   (x (case kind
                                        (0 (ash x n))
                                        (1 (ash x (- n)))
                                        (2 (ash (boymoo-model::a64-signed 64 x) (- n)))
                                        (otherwise (boymoo-model::a64-ror 64 x n))))))
           :in-theory (e/d (unsigned-byte-p integer-range-p)
                           (integer-a64-unsigned-type)))))

(defthm integer-a64-shift-64-bound
  (< (boymoo-model::a64-shift kind 64 x n) 18446744073709551616)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance integer-a64-unsigned-type
                                   (width 64)
                                   (x (case kind
                                        (0 (ash x n))
                                        (1 (ash x (- n)))
                                        (2 (ash (boymoo-model::a64-signed 64 x) (- n)))
                                        (otherwise (boymoo-model::a64-ror 64 x n))))))
           :in-theory (e/d (unsigned-byte-p integer-range-p)
                           (integer-a64-unsigned-type)))))

(defthm integer-read-register-type
  (natp (boymoo-model::a64-read-reg r 64 use machine))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-read-reg unsigned-byte-p
                                   integer-range-p)
                                  (integer-a64-unsigned-type integer-a64-unsigned-is-mod))
           :use ((:instance integer-a64-unsigned-type
                            (width 64)
                            (x (if (and (natp r) (< r 31))
                                   (cdr (assoc-equal r (boymoo-model::a64-registers machine)))
                                 (if (and (equal r 31) use)
                                     (boymoo-model::a64-sp machine)
                                   0))))))))

(defthm integer-read-register-bound
  (< (boymoo-model::a64-read-reg r 64 use machine) 18446744073709551616)
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-read-reg unsigned-byte-p
                                   integer-range-p)
                                  (integer-a64-unsigned-type integer-a64-unsigned-is-mod))
           :use ((:instance integer-a64-unsigned-type
                            (width 64)
                            (x (if (and (natp r) (< r 31))
                                   (cdr (assoc-equal r (boymoo-model::a64-registers machine)))
                                 (if (and (equal r 31) use)
                                     (boymoo-model::a64-sp machine)
                                   0))))))))

(defthm integer-compare-carry-of-pattern
  (implies (and (natp r) (<= 13835058055282163712 r) (< r 18446744073709551616))
           (equal (logbitp 64 (+ 36893488147419103169 (- r)))
                  (<= r 18446744073709551553)))
  :hints (("Goal" :use ((:instance integer-compare-carry
                                   (k (- 18446744073709551616 r)))))))

(defthm integer-compare-difference-of-pattern
  (implies (and (natp r) (<= 13835058055282163712 r) (< r 18446744073709551616))
           (equal (mod (+ 36893488147419103169 (- r)) 18446744073709551616)
                  (if (<= r 18446744073709551553)
                      (- 18446744073709551553 r)
                    (+ 36893488147419103169 (- r)))))
  :hints (("Goal" :use ((:instance integer-compare-difference
                                   (k (- 18446744073709551616 r)))))))

; The first four instructions at rt:ash-right negate the count in x2
; and limit it to 63, leaving x0 unchanged.  Here x2 holds the 64-bit
; pattern R of a negative count from -2^62 to -1, so the count is
; R - 2^64.
(defthm integer-ash-right-limit-instructions
  (implies (<= 13835058055282163712 (boymoo-model::a64-read-reg 2 64 nil machine))
           (let ((after (integer-run-straight
                         (integer-runtime-instructions "rt:ash-right" 0 4) machine)))
             (and (equal (boymoo-model::a64-read-reg 2 64 nil after)
                         (integer-ash-right-limit
                          (- 18446744073709551616
                             (boymoo-model::a64-read-reg 2 64 nil machine))))
                  (equal (boymoo-model::a64-read-reg 0 64 nil after)
                         (boymoo-model::a64-read-reg 0 64 nil machine))))))

(defthm integer-half-word-bounds
  (implies (and (natp s) (< s 18446744073709551616))
           (and (natp (floor s 2))
                (< (floor s 2) 9223372036854775808)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance integer-floor-bounds (x s) (y 2))))))

; The last four instructions at rt:ash-right shift x0 right
; arithmetically by x2, clear its low bit and add one.
(defthm integer-ash-right-shift-instructions
  (implies (and (natp limit)
                (< limit 64)
                (equal (boymoo-model::a64-read-reg 2 64 nil machine) limit))
           (equal (boymoo-model::a64-read-reg
                   0 64 nil
                   (integer-run-straight
                    (integer-runtime-instructions "rt:ash-right" 16 4) machine))
                  (boymoo-model::a64-unsigned
                   64 (+ 1 (* 2 (floor (boymoo-model::a64-shift
                                        2 64 (boymoo-model::a64-read-reg 0 64 nil machine)
                                        limit)
                                       2))))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-shift)
           :use ((:instance integer-half-word-bounds
                            (s (boymoo-model::a64-shift
                                2 64 (boymoo-model::a64-read-reg 0 64 nil machine)
                                limit)))))))

(defthm integer-ash-right-code-split
  (equal (integer-run-straight
          (integer-runtime-instructions "rt:ash-right" 0 8) machine)
         (integer-run-straight
          (integer-runtime-instructions "rt:ash-right" 16 4)
          (integer-run-straight
           (integer-runtime-instructions "rt:ash-right" 0 4) machine)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable integer-run-straight-step)
           :use ((:instance integer-run-straight-append
                            (first (integer-runtime-instructions "rt:ash-right" 0 4))
                            (second (integer-runtime-instructions "rt:ash-right" 16 4)))))))

(defthm integer-ash-right-limit-bounds
  (implies (posp k)
           (and (natp (integer-ash-right-limit k))
                (< (integer-ash-right-limit k) 64)))
  :rule-classes nil)

; The eight instructions that follow the label rt:ash-right, run on a
; machine whose x0 holds the tagged word of an immediate integer V and
; whose x2 holds the 64-bit pattern R of a negative count from -2^62 to
; -1, leave in x0 the tagged word of (ash V (- R 2^64)).
(defthm integer-ash-right-branch-correct
  (implies (and (proof-immediate-integer-p v)
                (equal (boymoo-model::a64-read-reg 0 64 nil machine)
                       (proof-integer-word v))
                (<= 13835058055282163712
                    (boymoo-model::a64-read-reg 2 64 nil machine)))
           (equal (boymoo-model::a64-read-reg
                   0 64 nil
                   (integer-run-straight
                    (integer-runtime-instructions "rt:ash-right" 0 8) machine))
                  (proof-integer-word
                   (ash v (- (- 18446744073709551616
                                (boymoo-model::a64-read-reg 2 64 nil machine)))))))
  :hints (("Goal"
           :in-theory (disable proof-integer-word proof-immediate-integer-p
                               boymoo-model::a64-shift integer-runtime-instructions
                               (:executable-counterpart integer-runtime-instructions)
                               integer-run-straight-step
                               integer-ash-right-limit
                               integer-ash-right-limit-instructions
                               integer-ash-right-shift-instructions
                               integer-ash-immediate-right-shift)
           :use (integer-ash-right-code-split
                 integer-ash-right-limit-instructions
                 (:instance integer-ash-right-shift-instructions
                            (limit (integer-ash-right-limit
                                    (- 18446744073709551616
                                       (boymoo-model::a64-read-reg 2 64 nil machine))))
                            (machine (integer-run-straight
                                      (integer-runtime-instructions "rt:ash-right" 0 4)
                                      machine)))
                 (:instance integer-ash-immediate-right-shift
                            (k (- 18446744073709551616
                                  (boymoo-model::a64-read-reg 2 64 nil machine))))
                 (:instance integer-ash-right-limit-bounds
                            (k (- 18446744073709551616
                                  (boymoo-model::a64-read-reg 2 64 nil machine))))))))
