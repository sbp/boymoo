(in-package "BOYMOO-COMPILER")

(include-book "word-ops")
(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthmd model-word-as-mod
  (equal (model-word x) (mod (ifix x) #x10000000000000000))
  :hints (("Goal" :in-theory (enable ash floor mod))))

(defthm model-word-range
  (unsigned-byte-p 64 (model-word x))
  :hints (("Goal" :in-theory (e/d (model-word-as-mod unsigned-byte-p integer-range-p)
                                   (model-word mod)))))

(defthm model-word-is-natural
  (natp (model-word x))
  :hints (("Goal" :use model-word-range
           :in-theory (e/d (unsigned-byte-p integer-range-p) (model-word model-word-range))))
  :rule-classes :type-prescription)

(defthm model-integer-word-is-natural
  (natp (model-integer-word datum))
  :hints (("Goal" :in-theory (disable model-word)))
  :rule-classes :type-prescription)

(defthm model-integer-word-in-range
  (unsigned-byte-p 64 (model-integer-word datum))
  :hints (("Goal" :in-theory (e/d (model-integer-word) (model-word)))))

(defthm model-word-in-range
  (implies (unsigned-byte-p 64 x)
           (equal (model-word x) x))
  :hints (("Goal" :in-theory (e/d (model-word-as-mod unsigned-byte-p integer-range-p)
                                   (model-word mod)))))

(defthm model-word-idempotent
  (equal (model-word (model-word x)) (model-word x))
  :hints (("Goal" :in-theory (disable model-word))))

(defthm model-integer-word-canonical
  (equal (model-word (model-integer-word datum)) (model-integer-word datum))
  :hints (("Goal" :in-theory (disable model-word))))

(defthm model-signed-of-word
  (equal (model-signed (model-word x)) (model-signed x))
  :hints (("Goal" :in-theory (disable model-word))))

(defthmd model-negative-word
  (implies (and (integerp x) (< x 0) (<= (- #x10000000000000000) x))
           (equal (model-word x) (+ x #x10000000000000000)))
  :hints (("Goal" :in-theory (e/d (model-word-as-mod) (model-word mod)))))

(defthm model-signed-of-signed-64
  (implies (signed-byte-p 64 x)
           (equal (model-signed x) x))
  :hints (("Goal" :cases ((< x 0))
           :in-theory (e/d (model-negative-word signed-byte-p integer-range-p)
                            (model-word)))))

(defthmd model-immediate-signed-word
  (implies (model-immediate-integer-p datum)
           (equal (model-signed (model-integer-word datum)) (1+ (* 2 datum))))
  :hints (("Goal" :use (:instance model-signed-of-signed-64 (x (1+ (* 2 datum))))
           :in-theory (e/d (signed-byte-p integer-range-p)
                            (model-signed model-word model-signed-of-signed-64)))))

(defthmd model-immediate-word-is-odd
  (implies (model-immediate-integer-p datum)
           (logbitp 0 (model-integer-word datum)))
  :hints (("Goal" :cases ((< datum 0))
           :in-theory (e/d (model-negative-word unsigned-byte-p signed-byte-p
                            integer-range-p logbitp oddp)
                            (model-word mod floor)))))

(defthmd model-constant-of-immediate-integer
  (implies (model-immediate-integer-p datum)
           (equal (model-constant (model-integer-word datum) constants)
                  (boymoo-model::core-value datum)))
  :hints (("Goal" :use (model-immediate-word-is-odd model-immediate-signed-word)
           :in-theory (e/d (model-constant signed-byte-p integer-range-p ash)
                            (model-word model-signed model-integer-word logbitp mod floor)))))

(local (include-book "ihs/logops-lemmas" :dir :system))

(defthm model-word-and-in-range
  (unsigned-byte-p 64 (model-word-op :and left right))
  :hints (("Goal"
           :use (:instance acl2::unsigned-byte-p-logand
                           (acl2::size 64) (acl2::i (model-word left)) (acl2::j (model-word right)))
           :in-theory (e/d (model-word-op) (model-word (:definition acl2::binary-logand))))))

(defthm model-word-and-is-canonical
  (equal (model-word (model-word-op :and left right)) (model-word-op :and left right))
  :hints (("Goal" :in-theory (disable model-word))))

(defthmd model-word-equality-computes-flag
  (equal (model-word-op :ceq left right)
         (model-flag (equal (model-word left) (model-word right))))
  :hints (("Goal" :in-theory (e/d (model-word-op) (model-word)))))
