(in-package "BOYMOO-PROOFS")

(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-read-byte-run-at-split
  (implies (and (natp lower) (natp upper) (integerp address))
           (equal (boymoo-model::a64-read-bytes (+ lower upper) address memory)
                  (+ (boymoo-model::a64-read-bytes lower address memory)
                     (* (expt 2 (* 8 lower))
                        (boymoo-model::a64-read-bytes upper (+ address lower) memory)))))
  :hints
  (("Goal" :in-theory (enable (:induction boymoo-model::a64-read-bytes))
           :induct (boymoo-model::a64-read-bytes lower address memory))
   ("Subgoal *1/2"
    :use ((:instance sequence-read-bytes-as-sum (count lower))
          (:instance sequence-read-bytes-as-sum (count (+ lower upper)))
          (:instance sequence-powers-add (left 8) (right (* 8 (1- lower)))))))
  :rule-classes nil)

(defthm sequence-low-four-bytes-of-word-load
  (implies (integerp address)
           (equal (boymoo-model::a64-unsigned 32 (proof-load-word address machine))
                  (boymoo-model::a64-load 4 address machine)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-a64-unsigned-as-mod proof-load-word)
                    (sequence-mod-add-multiple sequence-mod-of-bounded sequence-read-bytes-bits))
    :use ((:instance sequence-read-byte-run-at-split
                     (lower 4) (upper 4) (memory (boymoo-model::a64-memory machine)))
          (:instance sequence-read-bytes-bits
                     (count 4) (memory (boymoo-model::a64-memory machine)))
          (:instance sequence-mod-add-multiple
                     (value (boymoo-model::a64-read-bytes 4 address (boymoo-model::a64-memory machine)))
                     (multiple (boymoo-model::a64-read-bytes
                                4 (+ address 4) (boymoo-model::a64-memory machine)))
                     (divisor (expt 2 32)))
          (:instance sequence-mod-of-bounded
                     (value (boymoo-model::a64-read-bytes 4 address (boymoo-model::a64-memory machine)))
                     (divisor (expt 2 32)))))))

(local
 (defthm sequence-literal-byte-and-quotient
   (implies (integerp packed)
            (equal (+ (boymoo-model::a64-unsigned 8 packed) (* 256 (floor packed 256)))
                   packed))
   :hints (("Goal" :in-theory (enable mod sequence-a64-unsigned-as-mod)))
   :rule-classes nil))

(defthm sequence-packed-word-test-peels-byte
  (implies (and (posp count) (integerp address) (integerp packed))
           (equal (equal (boymoo-model::a64-read-bytes count address memory) packed)
                  (and (equal (boymoo-model::a64-byte address memory)
                              (boymoo-model::a64-unsigned 8 packed))
                       (equal (boymoo-model::a64-read-bytes (1- count) (1+ address) memory)
                              (floor packed 256)))))
  :hints (("Goal"
           :use (sequence-read-bytes-as-sum sequence-literal-byte-and-quotient
                 sequence-low-byte-of-read)
           :in-theory (disable sequence-low-byte-of-read)))
  :rule-classes nil)

(local
 (defthm sequence-load-four-bytes-of-list-name
   (implies (integerp address)
            (equal (equal (boymoo-model::a64-load 4 address machine) #x5453494c)
                   (let ((memory (boymoo-model::a64-memory machine)))
                     (and (equal (boymoo-model::a64-byte address memory) 76)
                          (equal (boymoo-model::a64-byte (+ address 1) memory) 73)
                          (equal (boymoo-model::a64-byte (+ address 2) memory) 83)
                          (equal (boymoo-model::a64-byte (+ address 3) memory) 84)))))
   :hints
   (("Goal"
     :use ((:instance sequence-packed-word-test-peels-byte
                      (count 4) (packed #x5453494c) (memory (boymoo-model::a64-memory machine)))
           (:instance sequence-packed-word-test-peels-byte
                      (count 3) (packed #x545349) (address (+ address 1))
                      (memory (boymoo-model::a64-memory machine)))
           (:instance sequence-packed-word-test-peels-byte
                      (count 2) (packed #x5453) (address (+ address 2))
                      (memory (boymoo-model::a64-memory machine)))
           (:instance sequence-packed-word-test-peels-byte
                      (count 1) (packed #x54) (address (+ address 3))
                      (memory (boymoo-model::a64-memory machine))))))
   :rule-classes nil))

(local
 (defthm sequence-single-byte-character-test
   (implies (unsigned-byte-p 8 byte)
            (and (equal (equal (code-char byte) #\L) (equal byte 76))
                 (equal (equal (code-char byte) #\I) (equal byte 73))
                 (equal (equal (code-char byte) #\S) (equal byte 83))
                 (equal (equal (code-char byte) #\T) (equal byte 84))))
   :hints (("Goal"
            :in-theory (disable acl2::char-code-code-char-is-identity)
            :use ((:instance acl2::char-code-code-char-is-identity (acl2::n byte)))))))

(local
 (defthm sequence-decode-list-name-from-bytes
   (implies (integerp address)
            (let ((memory (boymoo-model::a64-memory machine)))
              (equal (equal (proof-byte-characters (proof-byte-list 4 address machine))
                            '(#\L #\I #\S #\T))
                     (and (equal (boymoo-model::a64-byte address memory) 76)
                          (equal (boymoo-model::a64-byte (+ address 1) memory) 73)
                          (equal (boymoo-model::a64-byte (+ address 2) memory) 83)
                          (equal (boymoo-model::a64-byte (+ address 3) memory) 84)))))
   :hints (("Goal"
            :expand ((proof-byte-list 4 address machine)
                     (proof-byte-list 3 (+ 1 address) machine)
                     (proof-byte-list 2 (+ 2 address) machine)
                     (proof-byte-list 1 (+ 3 address) machine)
                     (proof-byte-list 0 (+ 4 address) machine))))
   :rule-classes nil))

(defthm sequence-packed-list-name-test
  (implies (integerp address)
           (equal (equal (boymoo-model::a64-unsigned 32 (proof-load-word address machine))
                         #x5453494c)
                  (equal (proof-load-string 4 address machine) "LIST")))
  :hints
  (("Goal"
    :in-theory (disable proof-load-string proof-load-word proof-byte-list proof-byte-characters
                        sequence-load-string-characters acl2::coerce-inverse-2)
    :use (sequence-load-four-bytes-of-list-name sequence-decode-list-name-from-bytes
          (:instance sequence-load-string-characters (count 4))
          (:instance acl2::coerce-inverse-2 (acl2::x (proof-load-string 4 address machine))))))
  :rule-classes nil)
