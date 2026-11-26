(in-package "BOYMOO-PROOFS")

(include-book "machine")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm collection-swap-logand
   (equal (logand first second) (logand second first))
   :rule-classes nil))

(local
 (make-event
  (let* ((witness (pkg-witness "BITOPS"))
         (rule (intern-in-package-of-symbol "LOGAND-WITH-BITMASK" witness))
         (mask (intern-in-package-of-symbol "MASK" witness))
         (input (intern-in-package-of-symbol "I" witness)))
    `(defthm collection-unsigned-is-loghead
       (equal (boymoo-model::a64-unsigned width value)
              (acl2::loghead (nfix width) value))
       :hints (("Goal" :in-theory (e/d (boymoo-model::a64-unsigned
                                       boymoo-model::a64-ones)
                                      (,rule acl2::commutativity-of-logand
                                             acl2::logand-with-mask))
                       :use ((:instance ,rule
                                        (,mask (1- (ash 1 (nfix width))))
                                        (,input (ifix value)))
                             (:instance collection-swap-logand
                                        (first (ifix value))
                                        (second (1- (ash 1 (nfix width))))))))))))

(defthm collection-unsigned-width
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-unsigned width value))))

(defthm collection-unsigned-identity
  (implies (unsigned-byte-p width value)
           (equal (boymoo-model::a64-unsigned width value) value)))

(defthm collection-unsigned-idempotent
  (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned width value))
         (boymoo-model::a64-unsigned width value)))

(defthm collection-word-range
  (and (<= 0 (boymoo-model::a64-unsigned 64 value))
       (< (boymoo-model::a64-unsigned 64 value) (expt 2 64)))
  :rule-classes :linear)

(defthm collection-word-p
  (natp (boymoo-model::a64-unsigned 64 value))
  :rule-classes :type-prescription)

(defthm collection-word-of-wrapped-addend
  (implies (and (integerp left) (integerp right))
           (equal (boymoo-model::a64-unsigned
                   64 (+ left (boymoo-model::a64-unsigned 64 right)))
                  (boymoo-model::a64-unsigned 64 (+ left right)))))

(defthm collection-word-ignore-modulus
  (implies (integerp value)
           (equal (boymoo-model::a64-unsigned 64 (+ #x10000000000000000 value))
                  (boymoo-model::a64-unsigned 64 value)))
  :hints (("Goal" :in-theory (disable collection-unsigned-is-loghead)
                  :use ((:instance collection-word-of-wrapped-addend
                                   (left value) (right (expt 2 64)))))))

(defthm collection-word-ignore-modulus-in-sum
  (implies (and (integerp first) (integerp second))
           (equal (boymoo-model::a64-unsigned 64 (+ #x10000000000000000 first second))
                  (boymoo-model::a64-unsigned 64 (+ first second))))
  :hints (("Goal" :in-theory (disable collection-unsigned-is-loghead)
                  :use ((:instance collection-word-ignore-modulus
                                   (value (+ first second)))))))

(defthm collection-ash-by-zero
  (equal (ash value 0) (ifix value)))

(defthm collection-or-zero
  (equal (logior 0 value) (ifix value))
  :hints (("Goal" :cases ((integerp value))
                  :in-theory (enable acl2::binary-logior))))

(make-event
 (let* ((witness (pkg-witness "BITOPS"))
        (rule (intern-in-package-of-symbol "LOGHEAD-OF-LOGXOR" witness))
        (a (intern-in-package-of-symbol "A" witness))
        (x (intern-in-package-of-symbol "X" witness))
        (y (intern-in-package-of-symbol "Y" witness)))
   `(defthm collection-word-complement
      (implies (unsigned-byte-p 64 value)
               (equal (logxor value #xffffffffffffffff)
                      (- #xffffffffffffffff value)))
      :hints (("Goal" :use ((:instance ,rule (,a 64) (,x -1) (,y value)))
                      :in-theory (enable acl2::loghead lognot))))))

(defthm collection-cons-forwarding-tag-has-no-view
  (not (proof-view 6 base objects packages machine))
  :hints (("Goal" :in-theory (enable proof-view proof-view-step proof-word-tag
                                    boymoo-model::a64-unsigned boymoo-model::a64-ones))))

(defthm collection-mask-selects-datum-tag
  (implies (integerp value)
           (equal (logand value 7) (proof-word-tag value)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned
                                      boymoo-model::a64-ones))))

(defthm collection-datum-tag-is-natural
  (natp (proof-word-tag value))
  :rule-classes :type-prescription)

(defthm collection-datum-tag-bounds
  (and (<= 0 (proof-word-tag value)) (< (proof-word-tag value) 8))
  :rule-classes :linear)

(defthm collection-header-forwarding-bit-is-set
  (logbitp 63 (logior #x8000000000000000 word)))

(defthm collection-mask-recovers-forwarded-header
  (implies (unsigned-byte-p 63 word)
           (equal (logand (logior #x8000000000000000 word) #x7fffffffffffffff) word)))

(defthm collection-word-difference-is-zero
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (equal (boymoo-model::a64-unsigned 64 (- left right)) 0)
                  (equal left right)))
  :hints (("Goal" :in-theory (disable acl2::loghead-+-cancel)
                  :use ((:instance acl2::loghead-+-cancel
                                   (acl2::size 64) (acl2::i (- right))
                                   (acl2::j left) (acl2::k right))))))

(local
 (make-event
  (let* ((witness (pkg-witness "BITOPS"))
         (induction (intern-in-package-of-symbol "IHSEXT-INDUCTIONS" witness))
         (recursion (intern-in-package-of-symbol "IHSEXT-RECURSIVE-REDEFS" witness)))
    `(defthm collection-shift-and-or-as-logapp
       (implies (and (unsigned-byte-p width low) (integerp high))
                (equal (logior (ash high width) low)
                       (acl2::logapp width low high)))
       :hints (("Goal" :in-theory
                (acl2::e/d* (,induction ,recursion)
                            (unsigned-byte-p acl2::commutativity-of-logior))))))))

(local
 (defthm collection-right-shift-byte-as-logtail
   (implies (integerp value)
            (equal (ash value -8) (acl2::logtail 8 value)))
   :hints (("Goal" :in-theory (enable ash acl2::logtail)))))

(defthm collection-pack-byte-and-remaining-bits
  (implies (and (natp width) (integerp value))
           (equal (logior (boymoo-model::a64-unsigned 8 value)
                          (ash (boymoo-model::a64-unsigned width (ash value -8)) 8))
                  (boymoo-model::a64-unsigned (+ 8 width) value)))
  :hints (("Goal"
           :use ((:instance collection-shift-and-or-as-logapp
                            (width 8)
                            (low (acl2::loghead 8 value))
                            (high (acl2::loghead width (acl2::logtail 8 value)))))
           :in-theory (disable collection-shift-and-or-as-logapp
                               acl2::logapp acl2::logtail))))

(defthm collection-width-of-byte-and-shifted-high-bits
  (implies (and (natp width) (unsigned-byte-p 8 low) (unsigned-byte-p width high))
           (unsigned-byte-p (+ 8 width) (logior low (ash high 8))))
  :hints (("Goal"
           :use ((:instance collection-shift-and-or-as-logapp (width 8)))
           :in-theory (disable collection-shift-and-or-as-logapp unsigned-byte-p
                               acl2::logapp))))

(defthm collection-zero-width-is-zero
  (equal (boymoo-model::a64-unsigned 0 value) 0))

(local
 (defthm collection-right-shifts-as-logtails
   (implies (integerp value)
            (and (equal (ash value -3) (acl2::logtail 3 value))
                 (equal (ash value -8) (acl2::logtail 8 value))
                 (equal (ash value -16) (acl2::logtail 16 value))))
   :hints (("Goal" :in-theory (enable ash acl2::logtail)))))

(defthm collection-rotated-word-truncates-to-right-shift
  (implies (and (unsigned-byte-p 64 word) (member-equal shift '(3 8 16)))
           (equal (boymoo-model::a64-unsigned (- 64 shift)
                                               (boymoo-model::a64-ror 64 word shift))
                  (ash word (- shift))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-ror)
                                  (unsigned-byte-p acl2::logtail)))))

(defthm collection-right-shift-with-rotation-mask
  (implies (unsigned-byte-p 64 word)
           (and (equal (logand (boymoo-model::a64-ror 64 word 3) #x1fffffffffffffff)
                       (ash word -3))
                (equal (logand (boymoo-model::a64-ror 64 word 8) #x00ffffffffffffff)
                       (ash word -8))
                (equal (logand (boymoo-model::a64-ror 64 word 16) #x0000ffffffffffff)
                       (ash word -16))))
  :hints (("Goal"
           :use ((:instance collection-rotated-word-truncates-to-right-shift (shift 3))
                 (:instance collection-rotated-word-truncates-to-right-shift (shift 8))
                 (:instance collection-rotated-word-truncates-to-right-shift (shift 16)))
           :in-theory (disable boymoo-model::a64-ror acl2::logtail))))

(defthm collection-rotation-is-word
  (unsigned-byte-p 64 (boymoo-model::a64-ror 64 word shift))
  :hints (("Goal" :in-theory (disable unsigned-byte-p collection-unsigned-is-loghead
                                      boymoo-model::a64-unsigned))))

(defthm collection-all-word-bits
  (implies (unsigned-byte-p 64 word)
           (equal (logand word #xffffffffffffffff) word)))

(local
 (make-event
  (let* ((witness (pkg-witness "BITOPS"))
         (rule (intern-in-package-of-symbol "LOGHEAD-OF-LOGAND" witness))
         (a (intern-in-package-of-symbol "A" witness))
         (x (intern-in-package-of-symbol "X" witness))
         (y (intern-in-package-of-symbol "Y" witness)))
    `(progn
       (defthm collection-clear-low-bit-of-loghead
         (equal (logand (acl2::loghead 64 word) #xfffffffffffffffe)
                (acl2::loghead 64 (logand -2 word)))
         :hints (("Goal" :use ((:instance ,rule (,a 64) (,x -2) (,y word)))
                         :in-theory (disable ,rule))))
       (defthm collection-clear-low-page-bits-of-loghead
         (equal (logand (acl2::loghead 64 word) #xffffffffffff0000)
                (acl2::loghead 64 (logand -65536 word)))
         :hints (("Goal" :use ((:instance ,rule (,a 64) (,x -65536) (,y word)))
                         :in-theory (disable ,rule))))))))

(local
 (defthm collection-clear-shifted-low-bit
   (equal (logand -2 (ash word 1)) (ash word 1))))

(defthm collection-mask-rotated-word-is-left-shift-by-one
  (implies (unsigned-byte-p 63 word)
           (equal (logand (boymoo-model::a64-ror 64 word 63) #xfffffffffffffffe)
                  (boymoo-model::a64-unsigned 64 (ash word 1))))
  :hints (("Goal"
           :use ((:instance acl2::ash-goes-to-0 (acl2::size 63)
                            (acl2::i word) (acl2::count -63))
                 (:instance collection-clear-low-bit-of-loghead (word (ash word 1))))
           :in-theory (disable acl2::ash-goes-to-0 collection-clear-low-bit-of-loghead))))

(defthm collection-shift-left-one-is-double
  (implies (integerp word)
           (equal (ash word 1) (* 2 word)))
  :hints (("Goal" :in-theory (e/d (ash) (floor)))))

(local
 (defthm collection-clear-shifted-page-bits
   (equal (logand -65536 (ash word 16)) (ash word 16))))

(defthm collection-mask-rotated-word-is-left-shift-by-sixteen
  (implies (unsigned-byte-p 48 word)
           (equal (logand (boymoo-model::a64-ror 64 word 48) #xffffffffffff0000)
                  (boymoo-model::a64-unsigned 64 (ash word 16))))
  :hints (("Goal"
           :use ((:instance acl2::ash-goes-to-0 (acl2::size 48)
                            (acl2::i word) (acl2::count -48))
                 (:instance collection-clear-low-page-bits-of-loghead (word (ash word 16))))
           :in-theory (disable acl2::ash-goes-to-0
                               collection-clear-low-page-bits-of-loghead))))

(defthm collection-right-shift-by-sixteen-fits
  (implies (unsigned-byte-p 64 word)
           (unsigned-byte-p 48 (ash word -16)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p acl2::logtail))))

(defthm collection-left-shift-by-sixteen-fits
  (implies (unsigned-byte-p 48 word)
           (unsigned-byte-p 64 (ash word 16)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))
