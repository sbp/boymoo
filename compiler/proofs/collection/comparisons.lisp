(in-package "BOYMOO-PROOFS")

(include-book "actions")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-model::a64-unsigned (:definition logbitp))))

(defthm collection-flags-fit-four-bits
  (unsigned-byte-p 4 (boymoo-model::a64-result-flags 64 result carry overflow)))

(local
 (defthm collection-conditions-read-result-flags
   (let ((flags (boymoo-model::a64-result-flags 64 result carry overflow)))
     (and (equal (boymoo-model::a64-condition 0 flags) (equal result 0))
          (equal (boymoo-model::a64-condition 1 flags) (not (equal result 0)))
          (equal (boymoo-model::a64-condition 2 flags) (if carry t nil))
          (equal (boymoo-model::a64-condition 3 flags) (not carry))
          (equal (boymoo-model::a64-condition 4 flags) (logbitp 63 result))
          (equal (boymoo-model::a64-condition 8 flags)
                 (and carry (not (equal result 0))))
          (equal (boymoo-model::a64-condition 9 flags)
                 (or (not carry) (equal result 0)))))
   :hints (("Goal" :cases ((logbitp 63 result) (equal result 0) carry overflow)))))

(local
 (defthm collection-top-bit-of-word-with-carry
   (implies (unsigned-byte-p 65 value)
            (equal (logbitp 64 value) (<= #x10000000000000000 value)))
   :hints (("Goal" :cases ((< value #x10000000000000000))
                   :in-theory (e/d (logbitp)
                                     (floor acl2::floor-unique-equal-version
                                            acl2::equal-of-0-and-floor-gen))
                   :use ((:instance acl2::floor-unique (acl2::i value)
                                    (acl2::j #x10000000000000000) (acl2::n 0))
                         (:instance acl2::floor-unique (acl2::i value)
                                    (acl2::j #x10000000000000000) (acl2::n 1)))))))

(defthm collection-flags-of-subtract-fit-four-bits
  (unsigned-byte-p 4 (collection-subtract-flags left right))
  :hints (("Goal" :in-theory (disable unsigned-byte-p
                                      boymoo-model::a64-result-flags
                                      boymoo-model::a64-signed))))

(defthm collection-unsigned-comparisons
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (let ((flags (collection-subtract-flags left right)))
             (and (equal (boymoo-model::a64-condition 0 flags) (equal left right))
                  (equal (boymoo-model::a64-condition 1 flags) (not (equal left right)))
                  (equal (boymoo-model::a64-condition 2 flags) (<= right left))
                  (equal (boymoo-model::a64-condition 3 flags) (< left right))
                  (equal (boymoo-model::a64-condition 8 flags) (< right left))
                  (equal (boymoo-model::a64-condition 9 flags) (<= left right)))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                      boymoo-model::a64-signed
                                      boymoo-model::a64-result-flags))))

(defthm collection-compare-with-zero-tests-high-bit
  (implies (unsigned-byte-p 64 word)
           (equal (boymoo-model::a64-condition 4 (collection-subtract-flags word 0))
                  (logbitp 63 word)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                      boymoo-model::a64-signed
                                      boymoo-model::a64-result-flags))))
