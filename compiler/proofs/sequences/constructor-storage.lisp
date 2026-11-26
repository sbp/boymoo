(in-package "BOYMOO-PROOFS")

(include-book "active-frame")
(include-book "constructor-calls")
(include-book "register-only")
(include-book "span-composition")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-constructor-store-keeps-byte-outside-reservation
   (let* ((extent (sequence-small-string-allocation length))
          (end (+ address extent)))
     (implies
      (and (natp length) (natp address) (unsigned-byte-p 64 end)
           (unsigned-byte-p 64 byte) (or (< byte address) (<= end byte)))
      (equal (boymoo-model::a64-byte byte (sequence-small-string-stores length address memory))
             (boymoo-model::a64-byte byte memory))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-small-string-stores proof-subspan-p mod sequence-a64-unsigned-as-mod)
                     (sequence-small-string-allocation sequence-byte-outside-write
                      boymoo-model::a64-write-bytes proof-span-p floor))
     :use (sequence-small-string-write-extents
           (:instance sequence-byte-outside-write (address byte) (start address)
                      (value (+ 1 (* 256 length))) (count 8))
           (:instance sequence-byte-outside-write (address byte) (start (+ address 8 (* 8 (floor length 8))))
                      (value 0) (count 8)
                      (memory (boymoo-model::a64-write-bytes 8 address (+ 1 (* 256 length)) memory))))
     :cases ((equal (mod length 8) 0))))
   :rule-classes nil))

(local
 (defthm sequence-constructor-store-keeps-word-addresses
   (implies (sequence-memory-addresses-p memory)
            (sequence-memory-addresses-p (sequence-small-string-stores length address memory)))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-small-string-stores)
                     (sequence-memory-addresses-p boymoo-model::a64-write-bytes))
     :use ((:instance sequence-a64-writes-keep-word-addresses (count 8) (value (+ 1 (* 256 length))))
           (:instance sequence-a64-writes-keep-word-addresses
                      (count 8) (address (+ address 8 (* 8 (floor length 8)))) (value 0)
                      (memory (boymoo-model::a64-write-bytes 8 address (+ 1 (* 256 length)) memory))))))
   :rule-classes nil))

(local
 (defthm sequence-constructor-store-keeps-entries-outside-reservation
   (implies
    (and (natp length) (natp address)
         (unsigned-byte-p 64 (+ address (sequence-small-string-allocation length)))
         (sequence-memory-addresses-p entries)
         (proof-disjoint-p lower upper address (+ address (sequence-small-string-allocation length))))
    (proof-byte-entries-agree-p entries lower upper memory (sequence-small-string-stores length address memory)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-disjoint-p proof-byte-entries-agree-p)
                     (sequence-small-string-stores sequence-small-string-allocation))
     :induct (sequence-memory-addresses-p entries))
    ("Subgoal *1/2"
     :use ((:instance sequence-constructor-store-keeps-byte-outside-reservation (byte (caar entries))))))
   :rule-classes nil))

(defthm sequence-small-constructor-store-is-confined
  (let* ((memory (boymoo-model::a64-memory first))
         (end (+ address (sequence-small-string-allocation length))))
    (implies
     (and (natp length) (natp address) (unsigned-byte-p 64 end)
          (sequence-memory-addresses-p memory)
          (equal (boymoo-model::a64-memory last) (sequence-small-string-stores length address memory)))
     (sequence-machine-write-confined-p address end first last)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-machine-write-confined-p sequence-machine-span-agrees-p proof-disjoint-p)
                    (sequence-small-string-stores sequence-small-string-allocation
                     sequence-memory-addresses-p proof-byte-entries-agree-p))
    :use ((:instance sequence-constructor-store-keeps-word-addresses (memory (boymoo-model::a64-memory first)))
          (:instance sequence-constructor-store-keeps-entries-outside-reservation
                     (entries (boymoo-model::a64-memory first)) (memory (boymoo-model::a64-memory first))
                     (lower 0) (upper address))
          (:instance sequence-constructor-store-keeps-entries-outside-reservation
                     (entries (boymoo-model::a64-memory last)) (memory (boymoo-model::a64-memory first))
                     (lower 0) (upper address))
          (:instance sequence-constructor-store-keeps-entries-outside-reservation
                     (entries (boymoo-model::a64-memory first)) (memory (boymoo-model::a64-memory first))
                     (lower (+ address (sequence-small-string-allocation length))) (upper (expt 2 64)))
          (:instance sequence-constructor-store-keeps-entries-outside-reservation
                     (entries (boymoo-model::a64-memory last)) (memory (boymoo-model::a64-memory first))
                     (lower (+ address (sequence-small-string-allocation length))) (upper (expt 2 64))))))
  :rule-classes nil)

(local
 (defthm sequence-active-space-addresses-are-natural
   (and (natp (proof-active-floor before)) (natp (proof-active-end before)))
   :hints (("Goal" :in-theory (enable proof-active-floor proof-active-end proof-runtime-word proof-load-word)))
   :rule-classes nil))

(local
 (defthm sequence-constructor-reservation-is-in-active-space
   (implies (and (proof-heap-layout-p before)
                 (proof-reserved-span-p :header address bytes before objects))
            (proof-subspan-p address bytes (proof-active-floor before) (proof-active-end before)))
   :hints (("Goal"
            :in-theory (e/d (proof-reserved-span-p proof-subspan-p)
                            (proof-heap-layout-p proof-object-disjoint-p proof-span-p
                             proof-regions-p proof-align-up))
            :use sequence-active-space-addresses-are-natural
            :expand ((proof-heap-layout-p before))))
   :rule-classes nil))

(defthm sequence-small-constructor-init-is-an-active-write
  (let* ((first (proof-world-machine before))
         (stack (boymoo-model::a64-sp first))
         (address (proof-world-reg 0 before))
         (length (proof-load-word stack first))
         (bytes (sequence-small-string-allocation length))
         (after (sequence-execute (sequence-small-string-finish-path length) before)))
    (implies
     (and (proof-heap-layout-p before)
          (proof-reserved-span-p :header address bytes before objects)
          (sequence-memory-addresses-p (boymoo-model::a64-memory first))
          (consp (boymoo-model::a64-registers first))
          (unsigned-byte-p 18 length)
          (proof-subspan-p (+ stack 16) 0
                           (sequence-machine-stack-base before) (sequence-machine-stack-end before))
          (equal (mod stack 16) 0))
     (sequence-active-write-p address (+ address bytes) before after)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-active-write-p proof-span-p proof-subspan-p)
                    (proof-heap-layout-p proof-reserved-span-p proof-world-machine proof-world-reg
                     proof-load-word sequence-machine-write-confined-p sequence-heap-registers-agree-p
                     sequence-execute sequence-small-string-allocation sequence-small-string-finish-path
                     sequence-small-string-stores sequence-machine-stack-base sequence-machine-stack-end))
    :use
    (sequence-small-string-finish-effects
     (:instance sequence-reserved-header-in-mapped-heap (world before) (address (proof-world-reg 0 before))
                (bytes (sequence-small-string-allocation
                        (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before)))))
     (:instance sequence-constructor-reservation-is-in-active-space (address (proof-world-reg 0 before))
                (bytes (sequence-small-string-allocation
                        (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before)))))
     (:instance sequence-register-frame-on-prefix (limit 29) (prefix 28) (clobbers '(0 1 2 3))
                (after (sequence-execute (sequence-small-string-finish-path
                                          (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                                           (proof-world-machine before))) before)))
     (:instance sequence-frame-keeps-heap-registers (clobbers '(0 1 2 3))
                (after (sequence-execute (sequence-small-string-finish-path
                                          (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                                           (proof-world-machine before))) before)))
     (:instance sequence-mod-add-multiple (divisor 16) (multiple 1)
                (value (boymoo-model::a64-sp (proof-world-machine before))))
     (:instance sequence-small-constructor-store-is-confined (address (proof-world-reg 0 before))
                (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before)))
                (first (proof-world-machine before))
                (last (proof-world-machine
                       (sequence-execute (sequence-small-string-finish-path
                                          (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                                           (proof-world-machine before))) before)))))))
  :rule-classes nil)
