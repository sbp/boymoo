(in-package "BOYMOO-PROOFS")

(include-book "bits")
(include-book "../foundations/heap")

(logic)
(set-verify-guards-eagerness 0)

; The running hash uses two additions per byte. Each instruction
; keeps the low 64 bits of its result.
(defun symbols-hash-byte (hash byte)
  (boymoo-model::a64-unsigned
   64 (+ byte (boymoo-model::a64-unsigned
               64 (+ hash (boymoo-model::a64-unsigned 64 (ash hash 5)))))))

(local
 (defthm symbols-combine-hash-additions
   (implies (and (integerp hash) (integerp byte))
            (equal (+ byte hash (* 32 hash)) (+ byte (* 33 hash))))
   :hints (("Goal" :nonlinearp t))))

(defthm symbols-hash-byte-is-polynomial-step
  (implies (and (integerp hash) (integerp byte))
           (equal (symbols-hash-byte hash byte)
                  (boymoo-model::a64-unsigned 64 (+ byte (* 33 hash)))))
  :hints (("Goal"
           :in-theory (disable boymoo-model::a64-unsigned ash expt floor)
           :use ((:instance symbols-unsigned-sum-right
                            (width 64) (x (ash hash 5)) (y hash)))
           :nonlinearp t)))

(defun symbols-machine-name-hash (characters hash)
  (if (atom characters)
      (boymoo-model::a64-unsigned 64 hash)
    (symbols-machine-name-hash
     (cdr characters)
     (symbols-hash-byte hash (char-code (car characters))))))

(defthm symbols-machine-name-hash-agrees
  (implies (integerp hash)
           (equal (symbols-machine-name-hash characters hash)
                  (proof-hash-characters characters hash 64)))
  :hints (("Goal" :induct (proof-hash-characters characters hash 64)
                  :in-theory (disable boymoo-model::a64-unsigned symbols-hash-byte))))

(defun symbols-machine-key-hash (number name)
  (boymoo-model::a64-unsigned
   64 (+ (symbols-machine-name-hash (coerce name 'list) 0)
         (boymoo-model::a64-unsigned 64 (* 7919 number)))))

(defthm symbols-machine-key-hash-agrees
  (implies (natp number)
           (equal (symbols-machine-key-hash number name)
                  (proof-symbol-hash number name 64)))
  :hints (("Goal" :in-theory (disable proof-hash-characters symbols-machine-name-hash
                                      boymoo-model::a64-unsigned))))

(local
 (defthm symbols-unsigned-affine-agrees-on-residues
   (implies (and (integerp left) (integerp right) (integerp scale) (integerp byte)
                 (equal (boymoo-model::a64-unsigned width left)
                        (boymoo-model::a64-unsigned width right)))
            (equal (boymoo-model::a64-unsigned width (+ byte (* scale left)))
                   (boymoo-model::a64-unsigned width (+ byte (* scale right)))))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-of-scaled-sum (x left) (addend byte))
                  (:instance symbols-unsigned-of-scaled-sum (x right) (addend byte)))
            :in-theory (disable boymoo-model::a64-unsigned
                                symbols-unsigned-of-scaled-sum)))
   :rule-classes nil))

(local
 (defun symbols-hash-width-induction (characters wide-hash narrow-hash wide narrow)
   (if (atom characters)
       (cons wide-hash narrow-hash)
     (let* ((byte (char-code (car characters)))
            (next-wide (boymoo-model::a64-unsigned wide (+ (* 33 wide-hash) byte)))
            (next-narrow (boymoo-model::a64-unsigned narrow (+ (* 33 narrow-hash) byte))))
       (symbols-hash-width-induction (cdr characters) next-wide next-narrow wide narrow)))))

(local
 (defthm symbols-character-hash-agrees-on-low-bits
   (implies
    (and (natp wide) (natp narrow) (<= narrow wide)
         (integerp wide-hash) (integerp narrow-hash)
         (equal (boymoo-model::a64-unsigned narrow wide-hash)
                (boymoo-model::a64-unsigned narrow narrow-hash)))
    (equal (boymoo-model::a64-unsigned
            narrow (proof-hash-characters characters wide-hash wide))
           (proof-hash-characters characters narrow-hash narrow)))
   :hints (("Goal" :induct (symbols-hash-width-induction
                            characters wide-hash narrow-hash wide narrow)
                   :in-theory (disable boymoo-model::a64-unsigned))
           ("Subgoal *1/2"
            :use ((:instance symbols-unsigned-affine-agrees-on-residues
                             (width narrow) (left wide-hash) (right narrow-hash)
                             (scale 33) (byte (char-code (car characters)))))))))

(defthm symbols-key-hash-agrees-on-low-bits
  (implies (and (natp number) (natp narrow) (<= narrow 64))
           (equal (boymoo-model::a64-unsigned
                   narrow (symbols-machine-key-hash number name))
                  (proof-symbol-hash number name narrow)))
  :hints (("Goal"
           :use ((:instance symbols-character-hash-agrees-on-low-bits
                            (wide 64) (wide-hash 0) (narrow-hash 0)
                            (characters (coerce name 'list)))
                 (:instance symbols-unsigned-sum-left
                            (width narrow)
                            (x (proof-hash-characters (coerce name 'list) 0 64))
                            (y (* 7919 number))))
           :in-theory (disable symbols-machine-key-hash proof-hash-characters
                               boymoo-model::a64-unsigned symbols-unsigned-sum-left))))

(defthm symbols-machine-static-hash
  (implies (natp number)
           (equal (logand (symbols-machine-key-hash number name) 4095)
                  (proof-symbol-hash number name 12)))
  :hints (("Goal"
           :use ((:instance symbols-logand-low-mask
                            (width 12) (x (symbols-machine-key-hash number name)))
                 (:instance symbols-unsigned-as-mod
                            (width 12) (x (symbols-machine-key-hash number name)))
                 (:instance symbols-key-hash-agrees-on-low-bits (narrow 12)))
           :in-theory (disable symbols-key-hash-agrees-on-low-bits
                               symbols-machine-key-hash proof-symbol-hash
                               acl2::binary-logand boymoo-model::a64-unsigned))))

(local
 (defthm symbols-tagged-dividend-split
   (implies (and (integerp hash) (integerp quotient))
            (equal (+ (* (expt 2 64) quotient)
                      (+ 1 (* 2 (+ hash (- (* (expt 2 63) quotient))))))
                   (+ 1 (* 2 hash))))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x 2) (acl2::y (expt 2 63)) (acl2::z quotient)))
            :in-theory (disable acl2::associativity-of-*)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm symbols-tagged-word-as-unsigned-payload
   (implies (integerp hash)
            (equal (proof-integer-word hash)
                   (+ 1 (* 2 (boymoo-model::a64-unsigned 63 hash)))))
   :hints (("Goal"
            :use ((:instance symbols-mod-of-decomposition
                             (q (floor hash (expt 2 63)))
                             (divisor (expt 2 64))
                             (r (+ 1 (* 2 (mod hash (expt 2 63))))))
                  (:instance symbols-mod-natural (x hash) (divisor (expt 2 63)))
                  (:instance symbols-mod-bounds (x hash) (divisor (expt 2 63)))
                  (:instance symbols-tagged-dividend-split (quotient (floor hash (expt 2 63)))))
            :in-theory (e/d (symbols-unsigned-as-mod)
                            (boymoo-model::a64-unsigned
                             floor symbols-mod-of-decomposition))
            :nonlinearp t))))

(defthm symbols-machine-tagged-hash
  (implies (natp number)
           (equal (proof-integer-word
                   (boymoo-model::a64-signed 63 (proof-symbol-hash number name 63)))
                  (proof-integer-word (symbols-machine-key-hash number name))))
  :hints (("Goal"
           :use ((:instance symbols-tagged-word-as-unsigned-payload
                            (hash (boymoo-model::a64-signed
                                   63 (proof-symbol-hash number name 63))))
                 (:instance symbols-tagged-word-as-unsigned-payload
                            (hash (symbols-machine-key-hash number name)))
                 (:instance symbols-key-hash-agrees-on-low-bits (narrow 63)))
           :in-theory (disable proof-integer-word proof-symbol-hash
                               symbols-machine-key-hash symbols-machine-key-hash-agrees
                               symbols-key-hash-agrees-on-low-bits
                               boymoo-model::a64-signed boymoo-model::a64-unsigned
                               symbols-tagged-word-as-unsigned-payload))))

(local
 (defthm symbols-logical-shift-of-tagged-hash
   (implies (integerp hash)
            (equal (ash (proof-integer-word hash) -1)
                   (boymoo-model::a64-unsigned 63 hash)))
   :hints (("Goal"
            :use ((:instance symbols-floor-of-decomposition
                             (q (boymoo-model::a64-unsigned 63 hash))
                             (r 1) (divisor 2)))
            :in-theory (e/d (floor)
                            (proof-integer-word boymoo-model::a64-unsigned
                             symbols-floor-of-decomposition))))))

(defthm symbols-machine-dynamic-hash
  (implies (and (natp number) (natp bits) (<= bits 63))
           (equal (logand (ash (proof-integer-word (symbols-machine-key-hash number name)) -1)
                          (1- (expt 2 bits)))
                  (logand (1- (expt 2 bits))
                          (boymoo-model::a64-signed
                           63 (proof-symbol-hash number name 63)))))
  :hints (("Goal"
           :use ((:instance symbols-key-hash-agrees-on-low-bits (narrow 63))
                 (:instance symbols-signed-retains-low-bits
                            (wide 63) (narrow bits) (x (proof-symbol-hash number name 63)))
                 (:instance symbols-logand-commutes
                            (x (1- (expt 2 bits)))
                            (y (boymoo-model::a64-signed
                                63 (proof-symbol-hash number name 63)))))
           :in-theory (e/d (symbols-unsigned-as-mod)
                           (proof-integer-word proof-symbol-hash acl2::binary-logand
                            symbols-tagged-word-as-unsigned-payload
                            symbols-signed-retains-low-bits
                            symbols-machine-key-hash symbols-machine-key-hash-agrees
                            symbols-key-hash-agrees-on-low-bits
                            boymoo-model::a64-signed boymoo-model::a64-unsigned
                            mod floor expt ash)))))

(local
 (defthm symbols-high-word-bit-range
   (implies (and (natp word) (< word (expt 2 64)))
            (and (natp (floor word (expt 2 63))) (< (floor word (expt 2 63)) 2)))
   :hints (("Goal" :use ((:instance symbols-floor-bounds (x word) (divisor (expt 2 63))))
                   :in-theory (disable floor)))
   :rule-classes nil))

(local
 (defthm symbols-ash-right-63
   (implies (integerp word)
            (equal (ash word -63) (floor word (expt 2 63))))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm symbols-double-word-decomposition
   (implies (and (integerp word) (integerp low))
            (equal (+ (* (expt 2 64) (floor word (expt 2 63)))
                      (+ low (* 2 (mod word (expt 2 63)))))
                   (+ low (* 2 word))))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x 2) (acl2::y (expt 2 63))
                             (acl2::z (floor word (expt 2 63)))))
            :in-theory (e/d (mod) (floor acl2::associativity-of-*))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm symbols-double-preserves-low-bit
   (implies (and (integerp word) (natp low) (< low 2))
            (equal (boymoo-model::a64-unsigned 64 (+ low (* 2 word)))
                   (+ low (* 2 (boymoo-model::a64-unsigned 63 word)))))
   :hints (("Goal"
            :use ((:instance symbols-mod-of-decomposition
                             (q (floor word (expt 2 63))) (divisor (expt 2 64))
                             (r (+ low (* 2 (mod word (expt 2 63))))))
                  (:instance symbols-mod-bounds (x word) (divisor (expt 2 63)))
                  (:instance symbols-mod-natural (x word) (divisor (expt 2 63)))
                  (:instance symbols-double-word-decomposition))
            :in-theory (e/d (symbols-unsigned-as-mod)
                            (boymoo-model::a64-unsigned mod floor symbols-mod-of-decomposition))))
   :rule-classes nil))

(local
 (defthm symbols-word-rotation-by-63
   (implies (and (natp word) (< word (expt 2 64)))
            (equal (boymoo-model::a64-ror 64 word 63)
                   (+ (floor word (expt 2 63)) (* 2 (boymoo-model::a64-unsigned 63 word)))))
   :hints (("Goal"
            :use ((:instance symbols-high-word-bit-range)
                  (:instance symbols-or-of-low-and-aligned-fields
                             (width 1) (low (floor word (expt 2 63))) (high word))
                  (:instance symbols-double-preserves-low-bit (low (floor word (expt 2 63)))))
            :in-theory (e/d (boymoo-model::a64-ror)
                            (boymoo-model::a64-unsigned floor
                             acl2::binary-logior symbols-or-of-low-and-aligned-fields))))
   :rule-classes nil))

(local
 (defthm symbols-mask-by-zero
   (equal (logand word 0) 0)
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(defthmd symbols-left-shift-one-from-rotate
  (implies (and (natp word) (< word (expt 2 64)))
           (equal (logand (logand (boymoo-model::a64-ror 64 word 63) #xfffffffffffffffe)
                          #xffffffffffffffff)
                  (boymoo-model::a64-unsigned 64 (* 2 word))))
  :hints (("Goal"
           :use ((:instance symbols-high-word-bit-range)
                 (:instance symbols-word-rotation-by-63)
                 (:instance symbols-double-preserves-low-bit (low 0))
                 (:instance symbols-and-of-joined-fields
                            (width 1) (low-left (floor word (expt 2 63)))
                            (high-left (boymoo-model::a64-unsigned 63 word))
                            (low-right 0) (high-right #x7fffffffffffffff))
                 (:instance symbols-mask-is-unsigned
                            (width 63) (value (boymoo-model::a64-unsigned 63 word)))
                 (:instance symbols-mask-is-unsigned
                            (width 64) (value (* 2 (boymoo-model::a64-unsigned 63 word)))))
           :in-theory (disable boymoo-model::a64-ror boymoo-model::a64-unsigned floor
                               symbols-and-of-joined-fields symbols-unsigned-as-mod
                               acl2::binary-logand))))
