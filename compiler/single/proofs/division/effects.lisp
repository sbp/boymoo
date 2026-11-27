(in-package "BOYMOO-PROOFS")

(include-book "emission")
(include-book "memory")
(include-book "shifts")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor mod truncate logbitp acl2::binary-logior acl2::binary-logand
                     acl2::binary-logxor proof-reg proof-instruction-effect proof-execute
                     boymoo-model::a64-execute boymoo-model::a64-unsigned
                     boymoo-model::a64-load boymoo-model::a64-store
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-sp boymoo-model::a64-pc boymoo-model::a64-nzcv
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-memory boymoo-model::a64-condition boymoo-model::a64-shift
                     division-a64-unsigned-is-remainder)))

(defund division-set-pc (pc world)
  (update-nth 0 (boymoo-model::a64-set-pc pc (proof-world-machine world)) world))

(defund division-write-reg (register use-sp value world)
  (update-nth 0 (boymoo-model::a64-write-reg register 64 use-sp value (proof-world-machine world))
              world))

(defund division-set-flags (flags world)
  (update-nth 0 (boymoo-model::a64-set-nzcv flags (proof-world-machine world)) world))

(defund division-store-word (address value world)
  (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine world)) world))

(defund division-ordinary-world-p (world)
  (not (eq (car (proof-world-machine world)) :svc)))

(defund division-base-reg (register world)
  (if (equal register 31)
      (boymoo-model::a64-sp (proof-world-machine world))
    (proof-world-reg register world)))

(local
 (defthm division-effect-register-assoc
   (equal (assoc-equal key (put-assoc-equal register value registers))
          (if (equal key register) (cons key value) (assoc-equal key registers)))
   :hints (("Goal" :induct (put-assoc-equal register value registers)))))

(local
 (defthm division-nth-of-other-slot
   (implies (and (natp slot) (natp index) (not (equal slot index)))
            (equal (nth slot (update-nth index value xs)) (nth slot xs)))
   :hints (("Goal" :induct (nth slot xs))
           ("Subgoal *1/2" :expand ((update-nth index value xs))))))

(local
 (defthm division-nth-of-updated-slot
   (implies (natp index)
            (equal (nth index (update-nth index value xs)) value))
   :hints (("Goal" :induct (update-nth index value xs)))))

(local
 (defthm division-update-slot-twice
   (equal (update-nth index value (update-nth index previous xs))
          (update-nth index value xs))
   :hints (("Goal" :induct (update-nth index previous xs)))))

(local
 (defthm division-car-of-other-slot
   (implies (posp index)
            (equal (car (update-nth index value xs)) (car xs)))
   :hints (("Goal" :expand ((update-nth index value xs))))))

(local
 (defthmd division-number-of-read-register
   (equal (boymoo-model::a64-read-reg register 64 nil machine) (proof-reg register machine))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(defthm division-read-zero-register
  (equal (proof-world-reg 31 world) 0)
  :hints (("Goal" :in-theory (enable proof-reg boymoo-model::a64-read-reg))))

(defthm division-world-register-in-word
  (unsigned-byte-p 64 (proof-world-reg register world))
  :hints (("Goal" :in-theory (e/d (proof-reg boymoo-model::a64-read-reg)
                                  (division-number-of-read-register unsigned-byte-p
                                   integer-range-p))))
  :rule-classes nil)

(defthm division-world-sp-in-word
  (unsigned-byte-p 64 (boymoo-model::a64-sp (proof-world-machine world)))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-sp) (unsigned-byte-p integer-range-p))))
  :rule-classes nil)

(defthm division-world-pc-in-word
  (unsigned-byte-p 64 (proof-world-pc world))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-pc) (unsigned-byte-p integer-range-p))))
  :rule-classes nil)

(defthm division-word-register-bounds
  (let ((word (proof-world-reg register world)))
    (and (natp word) (< word *division-word-modulus*)))
  :hints (("Goal" :use (:instance division-world-register-in-word)
                  :in-theory (disable proof-world-reg)))
  :rule-classes ((:type-prescription :corollary (natp (proof-world-reg register world)))
                 (:linear :corollary (< (proof-world-reg register world) *division-word-modulus*))))

(defthm division-stack-pointer-bounds
  (let ((sp (boymoo-model::a64-sp (proof-world-machine world))))
    (and (natp sp) (< sp *division-word-modulus*)))
  :hints (("Goal" :use (:instance division-world-sp-in-word)))
  :rule-classes ((:type-prescription :corollary (natp (boymoo-model::a64-sp (proof-world-machine world))))
                 (:linear :corollary (< (boymoo-model::a64-sp (proof-world-machine world))
                                        *division-word-modulus*))))

(defthm division-program-counter-bounds
  (let ((pc (proof-world-pc world)))
    (and (natp pc) (< pc *division-word-modulus*)))
  :hints (("Goal" :use (:instance division-world-pc-in-word)
                  :in-theory (disable proof-world-pc)))
  :rule-classes ((:type-prescription :corollary (natp (proof-world-pc world)))
                 (:linear :corollary (< (proof-world-pc world) *division-word-modulus*))))

(local
 (defthm division-sp-register-read
   (equal (boymoo-model::a64-read-reg 31 64 t machine) (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg boymoo-model::a64-sp)))))

(local
 (defthm division-base-register-read
   (equal (boymoo-model::a64-read-reg register 64 t (proof-world-machine world))
          (division-base-reg register world))
   :hints (("Goal"
            :in-theory (e/d (division-base-reg proof-reg boymoo-model::a64-read-reg boymoo-model::a64-sp)
                            (division-number-of-read-register))))))

(defthm division-effects-of-setting-pc
  (let ((after (division-set-pc pc world)))
    (and (equal (proof-world-pc after) (boymoo-model::a64-unsigned 64 pc))
         (equal (proof-world-reg register after) (proof-world-reg register world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (division-ordinary-world-p after) (division-ordinary-world-p world))))
  :hints (("Goal" :in-theory (enable division-set-pc division-ordinary-world-p
                                     boymoo-model::a64-set-pc boymoo-model::a64-pc
                                     boymoo-model::a64-sp boymoo-model::a64-nzcv boymoo-model::a64-memory
                                     proof-reg boymoo-model::a64-read-reg))))

(defthm division-effects-of-writing-register
  (let ((after (division-write-reg dest use-sp value world)))
    (and (equal (proof-world-reg register after)
                (if (and (equal register dest) (natp dest) (< dest 31))
                    (boymoo-model::a64-unsigned 64 value)
                  (proof-world-reg register world)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (if (and (equal dest 31) use-sp)
                    (boymoo-model::a64-unsigned 64 value)
                  (boymoo-model::a64-sp (proof-world-machine world))))
         (equal (proof-world-pc after) (proof-world-pc world))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (division-ordinary-world-p after)
                (or (and (natp dest) (< dest 31)) (division-ordinary-world-p world)))))
  :hints (("Goal"
           :in-theory (e/d (division-write-reg division-ordinary-world-p
                            boymoo-model::a64-write-reg boymoo-model::a64-pc
                            boymoo-model::a64-sp boymoo-model::a64-nzcv boymoo-model::a64-memory
                            proof-reg boymoo-model::a64-read-reg)
                           (division-number-of-read-register)))))

(defthm division-effects-of-setting-flags
  (let ((after (division-set-flags flags world)))
    (and (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-unsigned 4 flags))
         (equal (proof-world-reg register after) (proof-world-reg register world))
         (equal (proof-world-pc after) (proof-world-pc world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (division-ordinary-world-p after) (division-ordinary-world-p world))))
  :hints (("Goal" :in-theory (enable division-set-flags division-ordinary-world-p
                                     boymoo-model::a64-set-nzcv boymoo-model::a64-nzcv
                                     boymoo-model::a64-pc boymoo-model::a64-sp boymoo-model::a64-memory
                                     proof-reg boymoo-model::a64-read-reg))))

(defthm division-effects-of-storing-word
  (let ((after (division-store-word address value world)))
    (and (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 address value (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-reg register after) (proof-world-reg register world))
         (equal (proof-world-pc after) (proof-world-pc world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (division-ordinary-world-p after) (division-ordinary-world-p world))))
  :hints (("Goal"
           :in-theory (e/d (division-store-word division-ordinary-world-p
                            boymoo-model::a64-store boymoo-model::a64-pc boymoo-model::a64-sp
                            boymoo-model::a64-nzcv boymoo-model::a64-memory
                            proof-reg boymoo-model::a64-read-reg)
                           (boymoo-model::a64-write-bytes)))))

(defthm division-loads-after-nonmemory-effects
  (and (equal (proof-load-word address (proof-world-machine (division-set-pc pc world)))
              (proof-load-word address (proof-world-machine world)))
       (equal (proof-load-word address
                              (proof-world-machine (division-write-reg register use-sp value world)))
              (proof-load-word address (proof-world-machine world)))
       (equal (proof-load-word address (proof-world-machine (division-set-flags flags world)))
              (proof-load-word address (proof-world-machine world))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (proof-world-machine boymoo-model::a64-read-bytes)))))

(defthm division-load-after-disjoint-word-store
  (implies (and (proof-span-p address 8) (proof-span-p target 8)
                (proof-disjoint-p address (+ 8 address) target (+ 8 target)))
           (equal (proof-load-word address (proof-world-machine (division-store-word target value world)))
                  (proof-load-word address (proof-world-machine world))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (proof-world-machine boymoo-model::a64-read-bytes
                                   boymoo-model::a64-write-bytes)))))

(defthm division-load-word-after-word-store
  (implies (and (proof-span-p address 8) (unsigned-byte-p 64 value))
           (equal (proof-load-word address (proof-world-machine (division-store-word address value world)))
                  value))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (proof-world-machine boymoo-model::a64-read-bytes
                                   boymoo-model::a64-write-bytes)))))

(local
 (defthm division-world-machine-after-update
   (equal (proof-world-machine (update-nth 0 machine world)) machine)))

(local
 (defthm division-world-machine-of-cons
   (equal (proof-world-machine (cons machine rest)) machine)))

(local
 (defthm division-read-reg-after-raw-pc
   (equal (boymoo-model::a64-read-reg register 64 use-sp (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-read-reg register 64 use-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc
                                      boymoo-model::a64-read-reg boymoo-model::a64-sp)))))

(local
 (defthm division-load-after-raw-pc
   (equal (boymoo-model::a64-load 8 address (boymoo-model::a64-set-pc pc machine))
          (proof-load-word address machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc boymoo-model::a64-memory
                                      boymoo-model::a64-load)))))

(local
 (defthm division-flags-after-raw-pc
   (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-nzcv machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc boymoo-model::a64-nzcv)))))

(local
 (defthm division-actual-pc-after-raw-pc
   (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-unsigned 64 pc))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc boymoo-model::a64-pc)))))

(local
 (defthm division-raw-pc-overwrites-raw-pc
   (equal (boymoo-model::a64-set-pc pc (boymoo-model::a64-set-pc previous machine))
          (boymoo-model::a64-set-pc pc machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-raw-read-of-world-reg
   (equal (boymoo-model::a64-read-reg register 64 nil (proof-world-machine world))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(local
 (defthmd division-raw-pc-of-world
   (equal (boymoo-model::a64-pc (proof-world-machine world)) (proof-world-pc world))))

(local
 (defthm division-raw-car-after-pc
   (equal (car (boymoo-model::a64-set-pc pc machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-raw-car-after-store
   (equal (car (boymoo-model::a64-store count address value machine)) (car machine))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-store)
                                   (boymoo-model::a64-write-bytes))))))

(local
 (defthm division-raw-car-after-flags
   (equal (car (boymoo-model::a64-set-nzcv flags machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-nzcv)))))

(local
 (defthm division-raw-car-after-write-reg
   (implies (not (equal (car machine) :svc))
            (not (equal (car (boymoo-model::a64-write-reg register 64 use-sp value machine))
                        :svc)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-raw-updates-make-machine-conses
   (and (consp (boymoo-model::a64-set-pc pc machine))
        (consp (boymoo-model::a64-set-nzcv flags machine))
        (consp (boymoo-model::a64-store count address value machine))
        (implies (consp machine)
                 (consp (boymoo-model::a64-write-reg register 64 use-sp value machine))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                                    boymoo-model::a64-store boymoo-model::a64-write-reg)
                                   (boymoo-model::a64-write-bytes))))))

(local
 (defthm division-ash-zero
   (implies (integerp word) (equal (ash word 0) word))
   :hints (("Goal" :use (:instance division-ash-left (x word) (width 0))))))

(local
 (defthm division-zero-shift
   (implies (integerp word)
            (equal (boymoo-model::a64-shift 0 64 word 0)
                   (boymoo-model::a64-unsigned 64 word)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-shift)))))

(local
 (defthm division-natural-register-offset
   (equal (boymoo-model::a64-register-offset register 3 0 (proof-world-machine world))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-register-offset)
                                   (proof-world-machine proof-world-reg))))))

(local
 (defthm division-offset-after-raw-pc
   (equal (boymoo-model::a64-register-offset
           register 3 0 (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-register-offset register 3 0 machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-register-offset)))))

(defmacro division-prove-effect (name instruction outcome &optional hypotheses enables)
  `(defthm ,name
     (implies (and (division-ordinary-world-p world) ,@hypotheses)
              (equal (proof-instruction-effect ,instruction world) ,outcome))
     :hints (("Goal"
              :in-theory
              (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                    division-ordinary-world-p division-set-pc division-write-reg
                    division-set-flags division-store-word division-raw-pc-of-world ,@enables)
                   (proof-world-machine proof-world-pc proof-world-reg
                    boymoo-model::a64-register-offset proof-load-word))
              :do-not-induct t))))

(defthm division-a64-unsigned-given-register
   (equal (boymoo-model::a64-unsigned 64 (proof-world-reg register world))
          (proof-world-reg register world))
   :hints (("Goal" :use (:instance division-world-register-in-word)
                  :in-theory (disable proof-world-reg))))

(defthm division-a64-unsigned-given-pc
   (equal (boymoo-model::a64-unsigned 64 (proof-world-pc world))
          (proof-world-pc world))
   :hints (("Goal" :use (:instance division-world-pc-in-word)
                  :in-theory (disable proof-world-pc))))

(division-prove-effect division-effect-move
  (list :logical-reg 1 64 dest 31 source 0 0 nil)
  (division-write-reg dest nil (proof-world-reg source world)
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-movz
  (list :move-wide 2 64 dest value place)
  (division-write-reg dest nil (ash value place)
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-movn
  (list :move-wide 0 64 dest value place)
  (division-write-reg dest nil (lognot (ash value place))
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-branch
  (list :branch delta nil)
  (division-set-pc (+ (proof-world-pc world) delta) world))

(division-prove-effect division-effect-branch-link
  (list :branch delta t)
  (division-set-pc (+ (proof-world-pc world) delta)
                   (division-write-reg 30 nil
                                       (boymoo-model::a64-unsigned 64 (+ 4 (proof-world-pc world)))
                                       (division-set-pc (+ 4 (proof-world-pc world)) world))))

(division-prove-effect division-effect-branch-register
  (list :branch-reg register nil)
  (division-set-pc (proof-world-reg register world) world))

(division-prove-effect division-effect-branch-zero
  (list :branch-zero delta 64 source nonzero)
  (division-set-pc (+ (proof-world-pc world)
                      (if (if nonzero (not (equal (proof-world-reg source world) 0))
                            (equal (proof-world-reg source world) 0))
                          delta 4))
                   world))

(division-prove-effect division-effect-branch-conditional
  (list :branch-cond delta condition)
  (division-set-pc (+ (proof-world-pc world)
                      (if (boymoo-model::a64-condition
                           condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                          delta 4))
                   world))

(division-prove-effect division-effect-select
  (list :select 64 dest left right condition nil)
  (division-write-reg dest nil
   (if (boymoo-model::a64-condition condition (boymoo-model::a64-nzcv (proof-world-machine world)))
       (proof-world-reg left world)
     (proof-world-reg right world))
   (division-set-pc (+ (proof-world-pc world) 4) world)))

(division-prove-effect division-effect-unsigned-divide
  (list :divide dest source divisor nil)
  (division-write-reg dest nil
   (if (equal (proof-world-reg divisor world) 0) 0
     (floor (proof-world-reg source world) (proof-world-reg divisor world)))
   (division-set-pc (+ (proof-world-pc world) 4) world)))

(division-prove-effect division-effect-multiply
  (list :multiply dest left right)
  (division-write-reg dest nil (* (proof-world-reg left world) (proof-world-reg right world))
                      (division-set-pc (+ (proof-world-pc world) 4) world)))

(division-prove-effect division-effect-multiply-subtract
  (list :multiply-subtract dest left right addend)
  (division-write-reg dest nil
   (- (proof-world-reg addend world) (* (proof-world-reg left world) (proof-world-reg right world)))
   (division-set-pc (+ (proof-world-pc world) 4) world)))

(defthm division-unsigned-plus-modulus
  (implies (integerp value)
           (equal (boymoo-model::a64-unsigned 64 (+ *division-word-modulus* value))
                  (boymoo-model::a64-unsigned 64 value)))
  :hints (("Goal"
           :use ((:instance division-signed-remainder-unique
                            (a (+ *division-word-modulus* value))
                            (b *division-word-modulus*)
                            (q (+ 1 (floor value *division-word-modulus*)))
                            (r (mod value *division-word-modulus*)))
                 (:instance division-signed-mod-bounds (a value) (b *division-word-modulus*))
                 (:instance division-floor-mod-identity (a value) (b *division-word-modulus*)))
           :in-theory (e/d (division-a64-unsigned-is-remainder)
                           (division-floor-mod-identity)))))

(local
 (defthm division-low-word-write
   (equal (boymoo-model::a64-write-reg register 64 use-sp
                                      (boymoo-model::a64-unsigned 64 value) machine)
          (boymoo-model::a64-write-reg register 64 use-sp value machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-complement-subtracts-from-mask
   (implies (unsigned-byte-p 64 right)
            (equal (logxor right #xffffffffffffffff) (- #xffffffffffffffff right)))
   :hints (("Goal" :use (:instance division-xor-word-complement (word right))))))

(local
 (defthm division-write-word-plus-modulus
   (implies (integerp value)
            (equal (boymoo-model::a64-write-reg register 64 use-sp
                                              (+ *division-word-modulus* value) machine)
                   (boymoo-model::a64-write-reg register 64 use-sp value machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-base-word-natural
   (natp (division-base-reg register world))
   :hints (("Goal" :in-theory (e/d (division-base-reg)
                                   (proof-world-machine proof-world-reg))))
   :rule-classes :type-prescription))

(local
 (defthm division-shift-result-in-word
   (unsigned-byte-p 64 (boymoo-model::a64-shift 0 64 value amount))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-shift)
                                   (unsigned-byte-p integer-range-p))))))

(division-prove-effect division-effect-add-immediate
  (list :arithmetic-imm 0 64 dest source immediate)
  (division-write-reg dest t (+ (division-base-reg source world) immediate)
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-subtract-immediate
  (list :arithmetic-imm 2 64 dest source immediate)
  (division-write-reg dest t (- (division-base-reg source world) immediate)
                      (division-set-pc (+ 4 (proof-world-pc world)) world))
  ((unsigned-byte-p 64 immediate)))

(division-prove-effect division-effect-add-register
  (list :arithmetic-reg 0 64 dest left right 0 amount)
  (division-write-reg
   dest nil (+ (proof-world-reg left world)
               (boymoo-model::a64-shift 0 64 (proof-world-reg right world) amount))
   (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-subtract-register
  (list :arithmetic-reg 2 64 dest left right 0 amount)
  (division-write-reg
   dest nil (- (proof-world-reg left world)
               (boymoo-model::a64-shift 0 64 (proof-world-reg right world) amount))
   (division-set-pc (+ 4 (proof-world-pc world)) world)))

(defund division-subtract-flags (left right)
  (let* ((sum (+ left (logxor right #xffffffffffffffff) 1))
         (result (boymoo-model::a64-unsigned 64 sum))
         (signed (- (boymoo-model::a64-signed 64 left) (boymoo-model::a64-signed 64 right))))
    (boymoo-model::a64-result-flags
     64 result (logbitp 64 sum) (not (equal signed (boymoo-model::a64-signed 64 result))))))

(division-prove-effect division-effect-subtract-flags-immediate
  (list :arithmetic-imm 3 64 dest source immediate)
  (let ((left (division-base-reg source world)))
    (division-set-flags
     (division-subtract-flags left immediate)
     (division-write-reg dest nil (- left immediate)
                         (division-set-pc (+ 4 (proof-world-pc world)) world))))
  ((unsigned-byte-p 64 immediate))
  (division-subtract-flags))

(division-prove-effect division-effect-subtract-flags-register
  (list :arithmetic-reg 3 64 dest left right 0 amount)
  (let ((a (proof-world-reg left world))
        (b (boymoo-model::a64-shift 0 64 (proof-world-reg right world) amount)))
    (division-set-flags
     (division-subtract-flags a b)
     (division-write-reg dest nil (- a b)
                         (division-set-pc (+ 4 (proof-world-pc world)) world))))
  nil
  (division-subtract-flags))

(local
 (defthm division-bit-64-below-modulus
   (implies (unsigned-byte-p 64 word) (not (logbitp 64 word)))
   :hints (("Goal" :expand ((logbitp 64 word))))))

(local
 (defthm division-subtract-carry-is-no-borrow
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (equal (logbitp 64 (+ *division-word-modulus* left (- right))) (<= right left)))
   :hints (("Goal"
            :cases ((< left right))
            :use (:instance division-word-plus-modulus (word (- left right)))))))

(local
 (defthm division-word-difference-zero
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (equal (equal (boymoo-model::a64-unsigned 64 (- left right)) 0)
                   (equal left right)))
   :hints (("Goal"
            :use ((:instance division-negative-in-word (value (- left right)))
                  (:instance division-a64-unsigned-of-bounded (width 64) (x (- left right))))
            :in-theory (disable division-negative-in-word division-a64-unsigned-of-bounded)))))

(defthm division-subtract-flags-fit
  (equal (boymoo-model::a64-unsigned 4 (division-subtract-flags left right))
         (division-subtract-flags left right))
  :hints (("Goal" :in-theory (enable division-subtract-flags boymoo-model::a64-result-flags))))

(defthm division-unsigned-conditions-after-subtract
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (let ((flags (division-subtract-flags left right)))
             (and (equal (boymoo-model::a64-condition 0 flags) (equal left right))
                  (equal (boymoo-model::a64-condition 1 flags) (not (equal left right)))
                  (equal (boymoo-model::a64-condition 2 flags) (<= right left))
                  (equal (boymoo-model::a64-condition 3 flags) (< left right))
                  (equal (boymoo-model::a64-condition 8 flags) (< right left))
                  (equal (boymoo-model::a64-condition 9 flags) (<= left right)))))
  :hints (("Goal" :in-theory (enable division-subtract-flags boymoo-model::a64-result-flags
                                     boymoo-model::a64-condition))))

(defthm division-base-reg-is-general
  (implies (not (equal register 31))
           (equal (division-base-reg register world) (proof-world-reg register world)))
  :hints (("Goal" :in-theory (enable division-base-reg))))

(defthm division-base-reg-is-stack-pointer
  (equal (division-base-reg 31 world) (boymoo-model::a64-sp (proof-world-machine world)))
  :hints (("Goal" :in-theory (enable division-base-reg))))

(defthm division-register-shift-left-value
  (implies (and (integerp word) (natp amount))
           (equal (boymoo-model::a64-shift 0 64 word amount)
                  (boymoo-model::a64-unsigned 64 (* word (expt 2 amount)))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-shift))))

(local
 (defthm division-load-in-word
   (unsigned-byte-p 64 (proof-load-word address machine))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8) (memory (boymoo-model::a64-memory machine)))
            :in-theory (enable boymoo-model::a64-load)))
   :rule-classes nil))

(division-prove-effect division-effect-load-offset
  (list :single 1 8 base dest :offset offset)
  (division-write-reg dest nil
   (proof-load-word (+ (division-base-reg base world) offset) (proof-world-machine world))
   (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-store-offset
  (list :single 0 8 base source :offset offset)
  (division-store-word (+ (division-base-reg base world) offset) (proof-world-reg source world)
                       (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-load-register
  (list :single 1 8 base dest :register offset 3 0)
  (division-write-reg
   dest nil
   (proof-load-word (+ (division-base-reg base world) (proof-world-reg offset world))
                    (proof-world-machine world))
   (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-store-register
  (list :single 0 8 base source :register offset 3 0)
  (division-store-word (+ (division-base-reg base world) (proof-world-reg offset world))
                       (proof-world-reg source world)
                       (division-set-pc (+ 4 (proof-world-pc world)) world)))

(defthm division-access-load-store-offset
  (implies (or (equal op 0) (equal op 1))
           (equal (proof-instruction-access-p (list :single op 8 base register :offset offset) world)
                  (and (or (not (equal base 31))
                           (equal (mod (division-base-reg base world) 16) 0))
                       (proof-covered-p
                        (boymoo-model::a64-unsigned 64 (+ (division-base-reg base world) offset))
                        8 (if (equal op 1) :read :write) (proof-world-regions world)))))
  :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-register-offset
                                      proof-world-machine proof-world-regions proof-world-reg))))

(defthm division-access-load-store-register
  (implies (or (equal op 0) (equal op 1))
           (equal (proof-instruction-access-p (list :single op 8 base register :register offset 3 0) world)
                  (and (or (not (equal base 31))
                           (equal (mod (division-base-reg base world) 16) 0))
                       (proof-covered-p
                        (boymoo-model::a64-unsigned
                         64 (+ (division-base-reg base world) (proof-world-reg offset world)))
                        8 (if (equal op 1) :read :write) (proof-world-regions world)))))
  :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-register-offset
                                      proof-world-machine proof-world-regions proof-world-reg))))

(local
 (defthm division-logand-all-word-bits
   (implies (unsigned-byte-p 64 word)
            (equal (logand word #xffffffffffffffff) word))
   :hints (("Goal" :use (:instance division-unsigned-mask-is-logand (width 64))))))

(local
 (defthm division-rotated-word-in-word
   (unsigned-byte-p 64 (boymoo-model::a64-ror 64 word shift))
   :hints (("Goal"
            :in-theory (e/d (boymoo-model::a64-ror) (unsigned-byte-p integer-range-p))))))

(local
 (defthm division-logical-right-bitfield-value
   (implies (and (unsigned-byte-p 64 word) (natp shift) (< shift 64))
            (equal (logand (logand (boymoo-model::a64-ror 64 word shift) #xffffffffffffffff)
                           (1- (expt 2 (- 64 shift))))
                   (ash word (- shift))))
   :hints (("Goal"
            :use (:instance division-unsigned-mask-is-logand
                            (width (- 64 shift)) (word (boymoo-model::a64-ror 64 word shift)))
            :in-theory (disable boymoo-model::a64-ror expt division-ash-right)))))

(local (in-theory (disable boymoo-model::a64-ror division-ash-right)))

(division-prove-effect division-effect-logical-right-bitfield
  (list :bitfield 2 64 dest source shift 63 #xffffffffffffffff tmask)
  (division-write-reg dest nil (ash (proof-world-reg source world) (- shift))
                      (division-set-pc (+ 4 (proof-world-pc world)) world))
  ((natp shift) (< shift 64) (equal tmask (1- (expt 2 (- 64 shift))))))

(division-prove-effect division-effect-left-variable-shift
  (list :shift-variable 0 64 dest source shift-register)
  (division-write-reg dest nil
   (boymoo-model::a64-shift 0 64 (proof-world-reg source world)
                           (mod (proof-world-reg shift-register world) 64))
   (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-right-variable-shift
  (list :shift-variable 1 64 dest source shift-register)
  (division-write-reg dest nil
   (ash (proof-world-reg source world) (- (mod (proof-world-reg shift-register world) 64)))
   (division-set-pc (+ 4 (proof-world-pc world)) world))
  nil
  (boymoo-model::a64-shift))

(local
 (defthmd division-model-register-of-world
   (equal (proof-reg register (proof-world-machine world)) (proof-world-reg register world))))

(division-prove-effect division-effect-clz
  (list :clz dest source)
  (division-write-reg dest nil
   (- 64 (integer-length (proof-world-reg source world)))
   (division-set-pc (+ 4 (proof-world-pc world)) world))
  nil
  (division-model-register-of-world))

(division-prove-effect division-effect-pair-store
  (list :pair nil base first second mode offset)
  (let* ((pointer (division-base-reg base world))
         (updated (+ pointer offset))
         (address (if (eq mode :post) pointer updated))
         (next (division-set-pc (+ 4 (proof-world-pc world)) world))
         (stored (division-store-word
                  (+ 8 address) (proof-world-reg second world)
                  (division-store-word address (proof-world-reg first world) next))))
    (if (or (eq mode :pre) (eq mode :post))
        (division-write-reg base t updated stored)
      stored)))

(division-prove-effect division-effect-pair-load
  (list :pair t base first second mode offset)
  (let* ((pointer (division-base-reg base world))
         (updated (+ pointer offset))
         (address (if (eq mode :post) pointer updated))
         (machine (proof-world-machine world))
         (next (division-set-pc (+ 4 (proof-world-pc world)) world))
         (loaded (division-write-reg
                  second nil (proof-load-word (+ 8 address) machine)
                  (division-write-reg first nil (proof-load-word address machine) next))))
    (if (or (eq mode :pre) (eq mode :post))
        (division-write-reg base t updated loaded)
      loaded)))

(defthm division-access-pair
  (equal (proof-instruction-access-p (list :pair load base first second mode offset) world)
         (let* ((pointer (division-base-reg base world))
                (address (if (eq mode :post) pointer (+ pointer offset))))
           (and (or (not (equal base 31)) (equal (mod pointer 16) 0))
                (proof-covered-p (boymoo-model::a64-unsigned 64 address)
                                 16 (if load :read :write) (proof-world-regions world)))))
  :hints (("Goal" :in-theory (disable proof-covered-p proof-world-machine proof-world-regions))))

(division-prove-effect division-effect-or-registers
  (list :logical-reg 1 64 dest left right 0 0 nil)
  (division-write-reg dest nil (logior (proof-world-reg left world) (proof-world-reg right world))
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-and-registers
  (list :logical-reg 0 64 dest left right 0 0 nil)
  (division-write-reg dest nil (logand (proof-world-reg left world) (proof-world-reg right world))
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-xor-registers
  (list :logical-reg 2 64 dest left right 0 0 nil)
  (division-write-reg dest nil (logxor (proof-world-reg left world) (proof-world-reg right world))
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(division-prove-effect division-effect-and-mask
  (list :logical-imm 0 64 dest source mask)
  (division-write-reg dest t (logand (proof-world-reg source world) mask)
                      (division-set-pc (+ 4 (proof-world-pc world)) world)))

(local
 (defthm division-writing-zero-register-is-inert
   (equal (boymoo-model::a64-write-reg 31 64 nil value machine) machine)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(division-prove-effect division-effect-test-mask
  (list :logical-imm 3 64 31 source mask)
  (division-set-flags
   (boymoo-model::a64-result-flags 64 (logand (proof-world-reg source world) mask) nil nil)
   (division-set-pc (+ 4 (proof-world-pc world)) world)))
