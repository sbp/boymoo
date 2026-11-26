(in-package "BOYMOO-PROOFS")

(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-compiler::low-bits ash floor)))

(defthmd data-immediate-integer-twos-complement
  (implies (proof-immediate-integer-p integer)
           (equal (proof-integer-word integer)
                  (+ 1 (* 2 integer) (if (< integer 0) (expt 2 64) 0))))
  :hints (("Goal" :cases ((< integer 0))
                  :use ((:instance data-low-bits-unique
                                   (word (+ 1 (* 2 integer))) (width 64)
                                   (q (if (< integer 0) -1 0))
                                   (residue (+ 1 (* 2 integer) (if (< integer 0) (expt 2 64) 0)))))
                  :in-theory (enable data-machine-unsigned-is-low-bits))))

(defthm data-immediate-integer-word-is-unsigned
  (implies (proof-immediate-integer-p integer)
           (unsigned-byte-p 64 (proof-integer-word integer)))
  :hints (("Goal" :use data-immediate-integer-twos-complement
                  :in-theory (disable proof-integer-word))))

(defthm data-immediate-integer-word-is-odd
  (implies (proof-immediate-integer-p integer)
           (oddp (proof-integer-word integer)))
  :hints (("Goal" :use (data-immediate-integer-twos-complement
                       (:instance data-low-bit-parity (word (proof-integer-word integer)))
                       (:instance data-low-bits-unique (width 1) (residue 1)
                                  (word (proof-integer-word integer))
                                  (q (+ integer (if (< integer 0) (expt 2 63) 0)))))
                  :in-theory (disable proof-integer-word data-low-bit-parity evenp))))

(local
 (defthm sign-bit-of-immediate-word
   (implies (proof-immediate-integer-p integer)
            (equal (logbitp 63 (proof-integer-word integer)) (< integer 0)))
   :hints (("Goal" :use (data-immediate-integer-twos-complement
                        (:instance data-floor-unique (x (proof-integer-word integer))
                                   (d (expt 2 63)) (q (if (< integer 0) 1 0))))
                   :in-theory (disable proof-integer-word)))))

(local
 (defthm unsigned-of-immediate-is-identity
   (implies (proof-immediate-integer-p integer)
            (equal (boymoo-model::a64-unsigned 64 (proof-integer-word integer))
                   (proof-integer-word integer)))
   :hints (("Goal" :use data-immediate-integer-twos-complement
                   :in-theory (e/d (data-machine-unsigned-is-low-bits) (proof-integer-word))))))

(defthmd data-immediate-integer-decodes
  (implies (proof-immediate-integer-p integer)
           (equal (ash (boymoo-model::a64-signed 64 (proof-integer-word integer)) -1) integer))
  :hints (("Goal" :use (data-immediate-integer-twos-complement
                       (:instance data-floor-unique (x (+ 1 (* 2 integer))) (d 2) (q integer)))
                  :in-theory (e/d (data-ash-right) (proof-integer-word logbitp)))))

(defthmd data-proof-view-of-odd-word
  (implies (and (unsigned-byte-p 64 word) (oddp word))
           (equal (proof-view word base objects packages machine)
                  (proof-value-view (ash (boymoo-model::a64-signed 64 word) -1))))
  :hints (("Goal" :in-theory (disable proof-word-tag proof-pointer-address proof-object-rank
                                      boymoo-model::a64-signed evenp))))

(defthmd data-view-of-immediate-integer
  (implies (proof-immediate-integer-p integer)
           (proof-value-p (proof-integer-word integer) integer base objects packages machine))
  :hints (("Goal" :in-theory (e/d (data-proof-view-of-odd-word data-immediate-integer-decodes)
                                 (proof-view proof-integer-word boymoo-model::a64-signed evenp)))))

(defthmd data-proof-view-of-character-word
  (implies (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 4)
                (unsigned-byte-p 8 (ash word -3)))
           (equal (proof-view word base objects packages machine)
                  (proof-value-view (code-char (ash word -3)))))
  :hints (("Goal" :in-theory (disable proof-word-tag proof-pointer-address proof-object-rank
                                      boymoo-model::a64-signed evenp))))

(defthmd data-view-of-character
  (implies (characterp byte)
           (proof-value-p (proof-character-word byte) byte base objects packages machine))
  :hints (("Goal" :use ((:instance data-proof-view-of-character-word (word (proof-character-word byte)))
                       (:instance data-low-bit-parity (word (proof-character-word byte)))
                       (:instance data-low-bits-unique (width 1) (residue 0)
                                  (word (proof-character-word byte)) (q (+ 2 (* 4 (char-code byte)))))
                       (:instance data-low-bits-unique (width 3) (residue 4)
                                  (word (proof-character-word byte)) (q (char-code byte)))
                       (:instance data-floor-unique (x (proof-character-word byte))
                                  (d 8) (q (char-code byte))))
                  :in-theory (e/d (data-machine-unsigned-is-low-bits data-ash-right)
                                 (proof-view code-char evenp data-low-bit-parity)))))
