(in-package "BOYMOO-PROOFS")

(include-book "instructions")

(logic)
(set-verify-guards-eagerness 0)

(sequence-def-low-mask sequence-logand-four-bits 4)
(sequence-def-low-mask sequence-logand-forty-six-bits 46)
(sequence-def-low-mask sequence-logand-fifty-six-bits 56)
(sequence-def-low-mask sequence-logand-sixty-one-bits 61)
(sequence-def-low-mask sequence-logand-sixty-three-bits 63)

(defmacro sequence-def-lsr (name count)
  (let ((mask (1- (expt 2 (- 64 count)))))
    `(defthm ,name
       (equal (boymoo-model::a64-exec-bitfield
               2 64 target source ,count 63 #xffffffffffffffff ,mask machine)
              (boymoo-model::a64-write-reg
               target 64 nil
               (floor (boymoo-model::a64-read-reg source 64 nil machine) ,(expt 2 count))
               machine))
       :hints (("Goal"
                :use ((:instance sequence-low-bits-of-rotated-word
                                 (value (boymoo-model::a64-read-reg source 64 nil machine))
                                 (rotation ,count))))))))

(sequence-def-lsr sequence-lsr-one 1)
(sequence-def-lsr sequence-lsr-three 3)
(sequence-def-lsr sequence-lsr-eight 8)
(sequence-def-lsr sequence-lsr-eighteen 18)
(sequence-def-lsr sequence-lsr-thirty-two 32)
(sequence-def-lsr sequence-lsr-sixty 60)

(defmacro sequence-def-lsl (name count)
  (let* ((rotation (- 64 count))
         (mask (* (expt 2 count) (1- (expt 2 rotation)))))
    `(defthm ,name
       (let ((value (boymoo-model::a64-read-reg source 64 nil machine)))
         (implies
          (unsigned-byte-p ,rotation value)
          (equal (boymoo-model::a64-exec-bitfield
                  2 64 target source ,rotation ,(1- rotation) ,mask #xffffffffffffffff machine)
                 (boymoo-model::a64-write-reg target 64 nil (* ,(expt 2 count) value)
                                              machine))))
       :hints (("Goal"
                :use ((:instance sequence-high-bits-of-rotated-word
                                 (value (boymoo-model::a64-read-reg source 64 nil machine))
                                 (shift ,count))))))))

(sequence-def-lsl sequence-lsl-one 1)
(sequence-def-lsl sequence-lsl-three 3)
(sequence-def-lsl sequence-lsl-four 4)
(sequence-def-lsl sequence-lsl-eight 8)

(local
 (defthm sequence-logand-symmetric
   (implies (and (integerp left) (integerp right))
            (equal (logand left right) (logand right left)))
   :hints (("Goal" :induct (logand left right)
                   :in-theory (enable acl2::binary-logand)))))

(local
 (defthm sequence-logior-symmetric
   (implies (and (integerp left) (integerp right))
            (equal (logior left right) (logior right left)))
   :hints (("Goal" :in-theory (enable acl2::binary-logior)))))

(local
 (defthm sequence-logior-sign-extension
   (implies (unsigned-byte-p 63 value)
            (equal (logior (- (expt 2 63)) value)
                   (+ (- (expt 2 63)) value)))
   :hints (("Goal" :in-theory (disable sequence-logior-symmetric
                                       sequence-logior-of-aligned-and-short)
                   :use ((:instance sequence-logior-symmetric
                                    (left (- (expt 2 63))) (right value))
                         (:instance sequence-logior-of-aligned-and-short
                                    (bits 63) (low value) (high -1)))))))

(defthm sequence-signed-word
  (implies (unsigned-byte-p 64 value)
           (equal (boymoo-model::a64-signed 64 value)
                  (if (< value (expt 2 63)) value (- value (expt 2 64)))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-signed)
                  :use ((:instance sequence-sign-bit (bit 63))))))

(defthm sequence-signed-word-of-fitting-value
  (implies (signed-byte-p 64 value)
           (equal (boymoo-model::a64-signed 64 (boymoo-model::a64-unsigned 64 value))
                  value))
  :hints (("Goal" :cases ((< value 0)))
          ("Subgoal 1" :in-theory (disable sequence-truncate-word-plus-modulus)
           :use ((:instance sequence-truncate-word-plus-modulus)))))

(local
 (defthm sequence-signed-word-half
   (implies (unsigned-byte-p 64 value)
            (equal (floor (boymoo-model::a64-signed 64 value) 2)
                   (+ (floor value 2) (if (< value (expt 2 63)) 0 (- (expt 2 63))))))
   :hints (("Goal" :use ((:instance sequence-floor-add-multiple
                                    (divisor 2) (multiple (- (expt 2 63)))))))))

(defthm sequence-asr-one
  (equal (boymoo-model::a64-exec-bitfield
          0 64 target source 1 63 #xffffffffffffffff #x7fffffffffffffff machine)
         (boymoo-model::a64-write-reg
          target 64 nil
          (floor (boymoo-model::a64-signed
                  64 (boymoo-model::a64-read-reg source 64 nil machine)) 2)
          machine))
  :hints (("Goal"
           :in-theory (disable sequence-logand-symmetric sequence-logior-symmetric
                               sequence-logior-sign-extension)
           :use ((:instance sequence-low-bits-of-rotated-word
                            (value (boymoo-model::a64-read-reg source 64 nil machine))
                            (rotation 1))
                 (:instance sequence-floor-of-unsigned
                            (value (boymoo-model::a64-read-reg source 64 nil machine))
                            (dropped 1) (kept 63))
                 (:instance sequence-logior-sign-extension
                            (value (floor (boymoo-model::a64-read-reg
                                           source 64 nil machine)
                                          2)))
                 (:instance sequence-floor-add-multiple
                            (value (boymoo-model::a64-read-reg source 64 nil machine))
                            (divisor 2) (multiple (- (expt 2 63))))))))

(in-theory (disable boymoo-model::a64-exec-bitfield))
