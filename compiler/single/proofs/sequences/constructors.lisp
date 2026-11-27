(in-package "BOYMOO-PROOFS")

(include-book "helpers")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-small-string-allocation (length)
  (* 8 (floor (+ 15 length) 8)))

(defthm sequence-small-string-allocation-size
  (implies (natp length)
           (let ((whole (* 8 (floor length 8))))
             (equal (sequence-small-string-allocation length)
                    (+ 8 whole (if (equal length whole) 0 8)))))
  :hints (("Goal"
           :use ((:instance sequence-floor-bounds (value length) (divisor 8))
                 (:instance sequence-floor-unique
                            (value (+ length 15)) (divisor 8)
                            (quotient (+ (floor length 8)
                                         (if (equal length (* 8 (floor length 8))) 1 2)))))
           :cases ((equal length (* 8 (floor length 8))))))
  :rule-classes nil)

(defthm sequence-small-string-write-extents
  (let* ((payload (+ address 8))
         (whole (* 8 (floor length 8)))
         (end (+ address (sequence-small-string-allocation length))))
    (implies (and (natp length) (natp address) (unsigned-byte-p 64 end))
             (and (proof-subspan-p address 8 address end)
                  (proof-subspan-p payload length address end)
                  (implies (not (equal length whole))
                           (proof-subspan-p (+ payload whole) 8 address end)))))
  :hints (("Goal"
           :use (sequence-small-string-allocation-size
                 (:instance sequence-floor-bounds (value length) (divisor 8)))
           :in-theory (disable sequence-small-string-allocation)))
  :rule-classes nil)

(sequence-defpath *sequence-small-string-finish-aligned*
  ("rt:new-string" 8 9)
  ("rt:string-made" 0 1))

(sequence-defpath *sequence-small-string-finish-unaligned*
  ("rt:new-string" 8 13))

(defun sequence-small-string-finish-path (length)
  (if (equal (boymoo-model::a64-unsigned 3 length) 0)
      *sequence-small-string-finish-aligned*
    *sequence-small-string-finish-unaligned*))

(defun sequence-small-string-stores (length address memory)
  (let ((header-memory (boymoo-model::a64-write-bytes
                        8 address (+ 1 (* 256 length)) memory)))
    (if (equal (boymoo-model::a64-unsigned 3 length) 0)
        header-memory
      (boymoo-model::a64-write-bytes
       8 (+ address 8 (* 8 (floor length 8))) 0 header-memory))))

(local
 (defthm sequence-rounding-down-fits-word
   (implies (unsigned-byte-p 19 length)
            (and (unsigned-byte-p 16 (floor length 8))
                 (unsigned-byte-p 61 (floor length 8))
                 (equal (boymoo-model::a64-unsigned 64 (floor length 8))
                        (floor length 8))
                 (equal (boymoo-model::a64-unsigned 64 (* 8 (floor length 8)))
                        (* 8 (floor length 8)))))
   :hints (("Goal" :use ((:instance sequence-floor-of-unsigned
                                    (dropped 3) (kept 16) (value length)))))))

(defthm sequence-small-string-finish-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (length (proof-load-word stack machine))
         (link (proof-load-word (+ stack 8) machine))
         (payload (+ address 8))
         (path (sequence-small-string-finish-path length))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 18 length)
          (unsigned-byte-p 64 (+ stack 16))
          (unsigned-byte-p 64 (+ address (sequence-small-string-allocation length))))
     (and (equal (proof-world-reg 0 after)
                 (boymoo-model::a64-unsigned 64 (+ 2 (- address base))))
          (equal (proof-world-reg 1 after) payload)
          (equal (proof-world-reg 2 after) length)
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-pc after) link)
          (proof-register-frame-p 29 '(0 1 2 3) before after)
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (proof-heap-base after) base)
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 stack))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (sequence-small-string-stores length address
                                               (boymoo-model::a64-memory machine))))))
  :hints (("Goal"
           :use ((:instance sequence-small-string-allocation-size
                            (length (proof-load-word
                                     (boymoo-model::a64-sp (proof-world-machine before))
                                     (proof-world-machine before))))
                 (:instance sequence-floor-bounds
                            (value (proof-load-word
                                    (boymoo-model::a64-sp (proof-world-machine before))
                                    (proof-world-machine before)))
                            (divisor 8)))
           :in-theory (e/d (sequence-execute) (sequence-small-string-allocation
                                              sequence-unsigned-of-difference))
           :expand ((:free (limit clobbers first last)
                           (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defconst *sequence-new-string-offset* (sequence-offset "rt:new-string"))
(defconst *sequence-new-large-string-offset* (sequence-offset "rt:new-large-string"))
(defconst *sequence-empty-string-offset* (sequence-offset "rt:empty-string"))
(defconst *sequence-header-allocator-offset* (sequence-offset "rt:alloc"))

(sequence-defpath *sequence-small-string-request*
  ("rt:new-string" 0 8))

(sequence-defpath *sequence-large-string-dispatch*
  ("rt:new-string" 0 2))

(sequence-defpath *sequence-empty-string-dispatch*
  ("rt:empty-string" 0 2))

(local
 (defthm sequence-floor-below-divisor
   (implies (and (natp value) (posp divisor) (< value divisor))
            (equal (floor value divisor) 0))
   :hints (("Goal" :use ((:instance sequence-floor-unique (quotient 0)))))))

(local
 (defthm sequence-add-with-flags-without-carry
   (let* ((left (boymoo-model::a64-read-reg rn 64 t machine))
          (sum (+ left right))
          (overflow
           (not (equal (boymoo-model::a64-signed 64 sum)
                       (+ (boymoo-model::a64-signed 64 left)
                          (boymoo-model::a64-signed 64 right))))))
     (implies (and (unsigned-byte-p 64 right) (unsigned-byte-p 64 sum))
              (equal (boymoo-model::a64-exec-arithmetic 1 64 target rn right t machine)
                     (boymoo-model::a64-set-nzcv
                      (boymoo-model::a64-result-flags 64 sum nil overflow)
                      (boymoo-model::a64-write-reg target 64 nil sum machine)))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-exec-arithmetic)
                                   (sequence-signed-word))
                   :use ((:instance sequence-sign-bit (bit 64)
                                    (value (+ right (boymoo-model::a64-read-reg rn 64 t
                                                                              machine)))))))))

(defthm sequence-small-string-allocation-request
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (length (proof-world-reg 0 before))
         (after (sequence-execute *sequence-small-string-request* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-new-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-new-string-offset* 32))
          (unsigned-byte-p 18 length)
          (<= 16 stack))
     (and (equal (proof-world-pc after) (+ image-base *sequence-header-allocator-offset*))
          (equal (proof-world-reg 30 after) (+ image-base *sequence-new-string-offset* 32))
          (equal (proof-world-reg 0 after) (sequence-small-string-allocation length))
          (proof-register-frame-p 29 '(0 1) before after)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (- stack 16))
          (equal (proof-machine-limit after) (proof-machine-limit before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-write-bytes
                  8 (- stack 8) (proof-world-reg 30 before)
                  (boymoo-model::a64-write-bytes
                   8 (- stack 16) length (boymoo-model::a64-memory machine)))))))
  :hints (("Goal"
           :in-theory (e/d (sequence-execute)
                           (sequence-signed-word sequence-rounding-down-fits-word))
           :use ((:instance sequence-rounding-down-fits-word
                            (length (+ 15 (proof-world-reg 0 before)))))
           :expand ((:free (limit clobbers first last)
                           (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-empty-string-tail-call
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-empty-string-dispatch* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-empty-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-empty-string-offset* 8)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-new-string-offset*))
          (equal (proof-world-reg 0 after) 0)
          (proof-register-frame-p 30 '(0) before after)
          (equal (cdr after) (cdr before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)
           :expand ((:free (limit clobbers first last)
                           (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-large-string-tail-call
  (let* ((machine (proof-world-machine before))
         (length (proof-world-reg 0 before))
         (after (sequence-execute *sequence-large-string-dispatch* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-new-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-new-string-offset* 8))
          (<= 262144 length))
     (and (equal (proof-world-pc after) (+ image-base *sequence-new-large-string-offset*))
          (equal (proof-world-reg 0 after) length)
          (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :in-theory (enable sequence-execute)
           :use ((:instance sequence-floor-of-unsigned
                            (dropped 18) (kept 46) (value (proof-world-reg 0 before)))
                 (:instance sequence-floor-bounds
                            (value (proof-world-reg 0 before)) (divisor 262144)))))
  :rule-classes nil)

(local
 (defthm sequence-small-string-padding-test
   (implies (integerp length)
            (equal (equal (boymoo-model::a64-unsigned 3 length) 0)
                   (equal length (* 8 (floor length 8)))))
   :hints (("Goal" :in-theory (enable sequence-a64-unsigned-as-mod mod)))))

(local
 (defthm sequence-allocation-return-address-is-natural
   (natp (proof-world-reg 0 world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-small-string-stores-initialize-header
   (implies (and (unsigned-byte-p 18 length) (natp address)
                 (unsigned-byte-p 64 (+ address (sequence-small-string-allocation length))))
            (equal (boymoo-model::a64-read-bytes
                    8 address (sequence-small-string-stores length address memory))
                   (+ 1 (* 256 length))))
   :hints (("Goal"
            :use (sequence-small-string-allocation-size
                  (:instance sequence-floor-bounds (value length) (divisor 8))
                  (:instance sequence-read-outside-write
                             (count 8) (start (+ address 8 (* 8 (floor length 8))))
                             (size 8) (value 0)
                             (memory (boymoo-model::a64-write-bytes
                                      8 address (+ 1 (* 256 length)) memory))))
            :in-theory (disable sequence-small-string-allocation)))
   :rule-classes nil))

(local
 (defthm sequence-small-string-stores-initialize-padding
   (implies (and (unsigned-byte-p 18 length) (natp address) (integerp padding-byte)
                 (<= (+ 8 address length) padding-byte)
                 (< padding-byte (+ address (sequence-small-string-allocation length)))
                 (unsigned-byte-p 64 (+ address (sequence-small-string-allocation length))))
            (equal (boymoo-model::a64-byte
                    padding-byte (sequence-small-string-stores length address memory))
                   0))
   :hints (("Goal"
            :use (sequence-small-string-allocation-size
                  (:instance sequence-floor-bounds (value length) (divisor 8))
                  (:instance sequence-byte-in-zero-span
                             (start (+ address 8 (* 8 (floor length 8))))
                             (address padding-byte) (count 8)
                             (memory (boymoo-model::a64-write-bytes
                                      8 address (+ 1 (* 256 length)) memory))))
            :in-theory (disable sequence-small-string-allocation)))
   :rule-classes nil))

(defthm sequence-small-string-initialized-storage
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 0 before))
         (length (proof-load-word stack machine))
         (payload (+ address 8))
         (bytes (sequence-small-string-allocation length))
         (end (+ address bytes))
         (path (sequence-small-string-finish-path length))
         (after (sequence-execute path before))
         (result-machine (proof-world-machine after)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 18 length)
          (unsigned-byte-p 64 (+ stack 16))
          (unsigned-byte-p 64 end)
          (proof-covered-p address bytes :write (proof-world-regions before)))
     (and (equal (proof-load-word address result-machine) (+ 1 (* 256 length)))
          (equal (proof-world-reg 1 after) payload)
          (equal (proof-world-reg 2 after) length)
          (proof-covered-p payload length :write (proof-world-regions after))
          (implies (and (integerp padding-byte)
                        (<= (+ payload length) padding-byte)
                        (< padding-byte end))
                   (equal (boymoo-model::a64-load 1 padding-byte result-machine) 0)))))
  :hints
  (("Goal"
    :in-theory (disable sequence-execute sequence-small-string-finish-path
                        sequence-small-string-stores sequence-small-string-allocation proof-covered-p
                        proof-world-reg proof-world-machine)
    :use (sequence-small-string-finish-effects
          (:instance sequence-small-string-stores-initialize-header
                     (address (proof-world-reg 0 before))
                     (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before)))
                     (memory (boymoo-model::a64-memory (proof-world-machine before))))
          (:instance sequence-small-string-stores-initialize-padding
                     (address (proof-world-reg 0 before))
                     (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before)))
                     (memory (boymoo-model::a64-memory (proof-world-machine before))))
          (:instance sequence-small-string-allocation-size
                     (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before))))
          (:instance sequence-floor-bounds
                     (value (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                             (proof-world-machine before)))
                     (divisor 8))
          (:instance sequence-covered-subspan
                     (start (proof-world-reg 0 before))
                     (count (sequence-small-string-allocation
                             (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before))))
                     (address (+ 8 (proof-world-reg 0 before)))
                     (size (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                            (proof-world-machine before)))
                     (access :write) (regions (proof-world-regions before))))))
  :rule-classes nil)

(defthm sequence-allocator-keeps-small-string-saves
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine returned))
         (stack (boymoo-model::a64-sp first))
         (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                 *proof-machine-reservation*)))
    (implies
     (and (proof-allocator-return-p :header bytes before returned
                                    old-objects new-objects packages)
          (proof-subspan-p stack 16 stack end))
     (and (equal (boymoo-model::a64-sp last) stack)
          (equal (proof-load-word stack last) (proof-load-word stack first))
          (equal (proof-load-word (+ stack 8) last)
                 (proof-load-word (+ stack 8) first)))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-p proof-memory-span-agrees-p proof-register-frame-p
                        proof-prefix-preserved-p proof-dynamic-table-preserved-p
                        proof-reserved-span-p proof-streams-preserved-p
                        proof-world-reg proof-world-machine)
    :use ((:instance sequence-agreement-preserves-load
                     (count 8)
                     (address (boymoo-model::a64-sp (proof-world-machine before)))
                     (start (boymoo-model::a64-sp (proof-world-machine before)))
                     (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                             *proof-machine-reservation*))
                     (after returned))
          (:instance sequence-agreement-preserves-load
                     (count 8)
                     (address (+ 8 (boymoo-model::a64-sp (proof-world-machine before))))
                     (start (boymoo-model::a64-sp (proof-world-machine before)))
                     (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                             *proof-machine-reservation*))
                     (after returned)))))
  :rule-classes nil)

(local
 (defthm sequence-string-header-fields
   (implies (natp length)
            (and (equal (proof-header-type (+ 1 (* 256 length))) 1)
                 (equal (proof-header-size (+ 1 (* 256 length))) length)))
   :hints (("Goal"
            :in-theory (enable sequence-a64-unsigned-as-mod)
            :use ((:instance sequence-mod-add-multiple (value 1) (divisor 256) (multiple length))
                  (:instance sequence-floor-unique
                             (value (+ 1 (* 256 length))) (divisor 256) (quotient length)))))))

(local
 (defthm sequence-string-aligned-offset
   (implies (and (integerp offset) (equal (mod offset 8) 0))
            (equal (* 8 (floor offset 8)) offset))
   :hints (("Goal" :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm sequence-string-tag-from-aligned-offset
   (implies (and (integerp offset) (equal (mod offset 8) 0))
            (equal (boymoo-model::a64-unsigned 3 (+ 2 offset)) 2))
   :hints (("Goal"
            :in-theory (e/d (sequence-a64-unsigned-as-mod) (sequence-mod-add-multiple))
            :use (sequence-string-aligned-offset
                  (:instance sequence-mod-add-multiple
                             (value 2) (divisor 8) (multiple (floor offset 8))))))))

(defthm sequence-string-pointer-fields
  (implies (and (natp base) (natp address) (<= base address)
                (unsigned-byte-p 64 (+ 8 address))
                (equal (mod (- address base) 8) 0))
           (let ((word (boymoo-model::a64-unsigned 64 (+ 2 (- address base)))))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-pointer-address word base) address)
                  (not (oddp word)))))
  :hints (("Goal"
           :in-theory (disable sequence-string-tag-from-aligned-offset
                               sequence-even-tags-mark-even-words oddp evenp)
           :use ((:instance sequence-string-tag-from-aligned-offset (offset (- address base)))
                 (:instance sequence-even-tags-mark-even-words (word (+ 2 (- address base)))))))
  :rule-classes nil)

(local
 (defthm sequence-constructor-heap-base-is-natural
   (natp (proof-heap-base world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-view-of-new-string-header
   (implies
    (and (unsigned-byte-p 64 word) (not (oddp word))
         (equal (proof-word-tag word) 2)
         (equal (proof-pointer-address word base) address)
         (natp length) (proof-span-p address (+ 8 length))
         (equal (proof-load-word address machine) (+ 1 (* 256 length))))
    (equal (proof-view word base (cons (proof-object address :active :header 0) old-objects)
                       packages machine)
           (proof-value-view (proof-load-string length (+ 8 address) machine))))
   :hints (("Goal" :in-theory (disable proof-pointer-address proof-word-tag
                                       proof-load-word proof-load-string)))
   :rule-classes nil))

(defthm sequence-string-result-with-published-header
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (objects (cons (proof-object address :active :header 0) old-objects)))
    (implies
     (and (natp length) (natp address) (<= base address)
          (unsigned-byte-p 64 (+ 8 address))
          (proof-span-p address (+ 8 length))
          (equal (mod (- address base) 8) 0)
          (equal (proof-world-reg 0 world)
                 (boymoo-model::a64-unsigned 64 (+ 2 (- address base))))
          (equal (proof-world-reg 1 world) (+ 8 address))
          (equal (proof-world-reg 2 world) length)
          (equal (proof-load-word address machine) (+ 1 (* 256 length)))
          (proof-covered-p (+ 8 address) length :write (proof-world-regions world)))
     (proof-string-result-p length world objects packages)))
  :hints
  (("Goal"
    :in-theory (disable proof-covered-p proof-load-word proof-load-string
                        proof-world-reg proof-heap-base proof-world-machine
                        proof-pointer-address proof-word-tag proof-view
                        oddp evenp sequence-even-tags-mark-even-words)
    :use ((:instance sequence-string-pointer-fields (base (proof-heap-base world)))
          (:instance sequence-view-of-new-string-header
                     (base (proof-heap-base world)) (word (proof-world-reg 0 world))
                     (machine (proof-world-machine world))))))
  :rule-classes nil)

(defthm sequence-small-string-finish-contract
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (length (proof-load-word stack machine))
         (bytes (sequence-small-string-allocation length))
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (path (sequence-small-string-finish-path length))
         (after (sequence-execute path before))
         (published (cons (proof-object address :active :header 0) objects)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 18 length)
          (unsigned-byte-p 64 (+ stack 16))
          (unsigned-byte-p 64 (+ address bytes))
          (<= base address)
          (equal (mod (- address base) 8) 0)
          (proof-covered-p address bytes :write (proof-world-regions before))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-string-result-p length after published packages))))
  :hints
  (("Goal"
    :in-theory (disable proof-string-result-p proof-covered-p proof-segment-p
                        proof-load-word proof-world-reg proof-world-machine proof-heap-base
                        sequence-small-string-allocation sequence-small-string-finish-path)
    :use
    (sequence-small-string-finish-effects sequence-small-string-initialized-storage
     (:instance sequence-small-string-write-extents
                (address (proof-world-reg 0 before))
                (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before))))
     (:instance sequence-string-result-with-published-header
                (old-objects objects)
                (address (proof-world-reg 0 before))
                (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before)))
                (world
                 (sequence-execute
                  (sequence-small-string-finish-path
                   (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                    (proof-world-machine before)))
                  before)))
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-small-string-finish-path
                               (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                                (proof-world-machine before))))
                (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                             (proof-world-machine before))))
                (after (sequence-execute
                        (sequence-small-string-finish-path
                         (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                          (proof-world-machine before)))
                        before))))))
  :rule-classes nil)
