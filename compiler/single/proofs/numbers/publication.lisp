(in-package "BOYMOO-PROOFS")

(include-book "boxing")
(include-book "state-views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-world-machine proof-world-reg
                     proof-world-pc proof-view proof-load-word proof-heap-p
                     proof-frame-return-p proof-preserved-heap-p
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                     acl2::binary-logand acl2::binary-logior
                     (:definition nth) (:definition update-nth) floor mod ash)))

(defthm proof-number-box-select-by-value
  (let* ((collapsed (if (equal kind 4) (equal b 1) (equal b 0)))
         (after (proof-number-box-select-after kind unchanged fields world)))
    (implies (and (proof-number-box-select-pre-p kind unchanged fields world)
                  (proof-reg-value-p 1 b world objects packages))
             (and (equal (proof-number-box-without-allocation-p kind world) collapsed)
                  (equal (proof-world-pc after) (if collapsed unchanged fields))
                  (implies (not collapsed)
                           (equal (proof-world-reg 2 after) (+ 4096 kind))))))
  :hints (("Goal"
           :use (proof-number-box-select
                 (:instance proof-number-tagged-zero-and-one (value b)
                            (word (proof-world-reg 1 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world))))
           :in-theory (enable proof-number-box-without-allocation-p
                              proof-number-box-select-target)))
  :rule-classes nil)

(defthm proof-number-reserve-preserves-machine-saves
  (let* ((stack (boymoo-model::a64-sp (proof-world-machine before)))
         (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                 *proof-machine-reservation*))
         (saved (+ stack offset)))
    (implies (and (proof-integer-reserve-return-p a b bytes before after
                                                  old-objects new-objects packages)
                  (member-equal offset '(0 8))
                  (natp stack) (<= (+ 16 stack) end) (<= end (expt 2 64)))
             (equal (proof-load-word saved (proof-world-machine after))
                    (proof-load-word saved (proof-world-machine before)))))
  :hints (("Goal"
           :use ((:instance proof-number-load-agrees-inside-saved-span
                            (start (boymoo-model::a64-sp (proof-world-machine before)))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*))
                            (address (+ (boymoo-model::a64-sp (proof-world-machine before))
                                        offset))))
           :in-theory (e/d (proof-preserved-heap-p) (proof-memory-span-agrees-p
                                                   proof-fixed-heap-p
                                                   proof-reserved-span-p
                                                   proof-prefix-preserved-p
                                                   proof-dynamic-table-preserved-p))))
  :rule-classes nil)

(local
 (defthm address-offset-sign
   (implies (integerp slots)
            (equal (* 8 (- slots)) (- (* 8 slots))))
   :hints (("Goal"
            :use ((:instance acl2::distributivity
                             (acl2::x 8) (acl2::y slots) (acl2::z (- slots))))
            :in-theory (disable acl2::distributivity)))))

(local
 (defthm two-times-four
   (equal (* 2 4 slots) (* 8 slots))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x 2) (acl2::y 4) (acl2::z slots)))
            :in-theory (disable acl2::associativity-of-*)))))

(defthm proof-number-box-word-address
  (let ((word (+ 2 (- address base))))
    (implies (and (natp base) (<= base address) (proof-span-p address 24)
                  (equal (mod address 8) 0) (equal (mod base 8) 0))
             (and (unsigned-byte-p 64 word)
                  (equal (proof-word-tag word) 2)
                  (not (oddp word))
                  (equal (proof-pointer-address word base) address))))
  :hints (("Goal"
           :use ((:instance proof-number-quotient-and-remainder (a address) (b 8))
                 (:instance proof-number-quotient-and-remainder (a base) (b 8))
                 (:instance proof-number-a64-unsigned-is-modulo (width 3)
                            (a (+ 2 (- address base))))
                 (:instance proof-number-mod-with-remainder
                            (a (+ 2 (- address base))) (b 8)
                            (q (- (floor address 8) (floor base 8))) (r 2))
                 (:instance proof-number-mod-with-remainder
                            (a (+ 2 (- address base))) (b 2)
                            (q (+ 1 (* 4 (- (floor address 8) (floor base 8))))) (r 0)))))
  :rule-classes nil)

; The reserve call can move the operands. The two words to preserve
; during publication are the ones in X0 and X1 at the reserve return.
(defund proof-number-box-field-views-preserved-p (rank before after old-objects objects packages)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after))
        (base (proof-heap-base before)))
    (and (equal (proof-view-step :word (proof-world-reg 0 before) 0 rank
                                 base objects packages last)
                (proof-view (proof-world-reg 0 before) base old-objects packages first))
         (equal (proof-view-step :word (proof-world-reg 1 before) 0 rank
                                 base objects packages last)
                (proof-view (proof-world-reg 1 before) base old-objects packages first)))))

(defthm proof-number-field-stores-form-box
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (base (proof-heap-base world))
         (address (proof-world-reg 2 world))
         (word (+ 2 (- address base)))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world))
         (link (proof-load-word (+ 8 stack) machine)))
    (implies (and (proof-number-checked-block-p *proof-number-box-publish-instructions*
                                               (list link) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p address 24)
                  (unsigned-byte-p 64 (+ 16 stack))
                  (<= base address)
                  (equal (mod address 8) 0)
                  (equal (mod base 8) 0)
                  (member-equal kind '(4 5))
                  (equal (proof-load-word stack machine) (+ 4096 kind))
                  (proof-reg-value-p 0 a world old-objects packages)
                  (proof-reg-value-p 1 b world old-objects packages)
                  (natp rank)
                  (equal (assoc-equal address objects) (proof-object address :active :header rank))
                  (proof-number-box-field-views-preserved-p
                   rank world after old-objects objects packages))
             (and (proof-segment-p 6 (list link) world :cut after)
                  (equal (proof-world-reg 0 after) word)
                  (proof-number-box-fields-p kind word a b base objects packages
                                             (proof-world-machine after)))))
  :hints (("Goal"
           :use (proof-number-box-publishes-fields
                 (:instance proof-number-box-word-address
                            (base (proof-heap-base world)) (address (proof-world-reg 2 world))))
           :in-theory (e/d (proof-number-box-fields-p proof-number-box-field-views-preserved-p
                                                     proof-world-reg)
                           (proof-view-step proof-word-tag proof-pointer-address
                            proof-number-integer-parity oddp proof-reg))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-publication-value
  (implies (and (proof-number-box-fields-p kind word a b base objects packages machine)
                (if (equal kind 4)
                    (and (proof-number-reduced-p a b) (< 1 b))
                  (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0)))))
           (proof-value-p word (if (equal kind 4) (/ a b) (complex a b))
                          base objects packages machine))
  :hints (("Goal" :use (proof-number-published-fraction proof-number-published-complex)
                  :in-theory (disable proof-number-published-fraction
                                      proof-number-published-complex)))
  :rule-classes nil)

(local
 (defthm immediate-view-at-any-rank
   (implies (and (unsigned-byte-p 64 word) (oddp word))
            (equal (proof-view-step :word word 0 rank base objects packages machine)
                   (proof-value-view (ash (boymoo-model::a64-signed 64 word) -1))))
   :hints (("Goal"
            :expand ((proof-view-step :word word 0 rank base objects packages machine))
            :in-theory (disable proof-view-step proof-number-ash-half
                                proof-number-integer-parity oddp)))))

(defthm proof-number-box-keeps-immediate-fields
  (implies (and (oddp (proof-world-reg 0 before)) (oddp (proof-world-reg 1 before)))
           (proof-number-box-field-views-preserved-p rank before after old-objects objects packages))
  :hints (("Goal"
           :in-theory (e/d (proof-number-box-field-views-preserved-p proof-world-reg)
                           (proof-number-integer-parity proof-reg proof-view-step oddp)))))

(defthm proof-number-box-publishes-canonical-value
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (base (proof-heap-base world))
         (address (proof-world-reg 2 world))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world))
         (link (proof-load-word (+ 8 stack) machine))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (proof-number-checked-block-p *proof-number-box-publish-instructions*
                                               (list link) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p address 24)
                  (unsigned-byte-p 64 (+ 16 stack))
                  (<= base address)
                  (equal (mod address 8) 0)
                  (equal (mod base 8) 0)
                  (equal (proof-load-word stack machine) (+ 4096 kind))
                  (proof-reg-value-p 0 a world old-objects packages)
                  (proof-reg-value-p 1 b world old-objects packages)
                  (natp rank)
                  (equal (assoc-equal address objects) (proof-object address :active :header rank))
                  (or (and (oddp (proof-world-reg 0 world)) (oddp (proof-world-reg 1 world)))
                      (proof-number-box-field-views-preserved-p
                       rank world after old-objects objects packages)))
             (and (proof-segment-p 6 (list link) world :cut after)
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use (proof-number-field-stores-form-box
                 proof-number-box-publishes-fields
                 (:instance proof-number-box-keeps-immediate-fields
                            (before world)
                            (after (proof-number-execute-block
                                    *proof-number-box-publish-instructions* world)))
                 (:instance proof-number-box-publication-value
                            (word (+ 2 (- (proof-world-reg 2 world) (proof-heap-base world))))
                            (base (proof-heap-base world))
                            (machine (proof-world-machine
                                       (proof-number-execute-block
                                        *proof-number-box-publish-instructions* world)))))
           :in-theory (disable proof-number-box-keeps-immediate-fields
                               proof-number-box-fields-p proof-heap-base
                               proof-number-integer-parity oddp)
           :do-not-induct t))
  :rule-classes nil)
