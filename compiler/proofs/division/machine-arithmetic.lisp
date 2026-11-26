(in-package "BOYMOO-PROOFS")

(include-book "emission")
(include-book "limbs")
(include-book "bitfields")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-one-limb-instructions*
  '((:arithmetic-imm 2 64 4 4 8)
    (:single 1 8 0 6 :register 4 3 0)
    (:arithmetic-reg 0 64 6 6 5 0 32)
    (:divide 7 6 3 nil)
    (:multiply-subtract 5 7 3 6)
    (:single 0 8 21 7 :register 4 3 0)
    (:branch-zero -24 64 4 t)))

(defthm division-one-limb-instructions-are-emitted
  (let* ((items (division-linked-example-items))
         (offset (division-label-offset "rt:z-divide-one-limb" items))
         (image (boymoo-compiler::a64-bytes items))
         (machine (proof-load-cleared-string image 0
                                             (boymoo-model::a64-state nil 0 0 0 nil))))
    (equal (division-decode-instructions 7 offset machine)
           *division-one-limb-instructions*))
  :rule-classes nil)

(defconst *division-one-limb-computation*
  (take 3 (nthcdr 2 *division-one-limb-instructions*)))

(local
 (in-theory (disable floor mod truncate ash
                     proof-step proof-reg proof-instruction-effect
                     proof-world-stop proof-world-reg proof-world-pc
                     boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                     boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     division-mask-is-remainder division-a64-unsigned-is-remainder)))

(local
 (defthm division-general-register-read
   (equal (boymoo-model::a64-read-reg register 64 nil machine) (proof-reg register machine))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(local
 (defthm division-read-register-after-pc
   (equal (proof-reg register (boymoo-model::a64-set-pc pc machine))
          (proof-reg register machine))
   :hints (("Goal"
            :in-theory (e/d (proof-reg boymoo-model::a64-set-pc boymoo-model::a64-read-reg)
                            (division-general-register-read))))))

(local
 (defthm division-unsigned-word-natural
   (natp (boymoo-model::a64-unsigned 64 value))
   :hints (("Goal" :use (:instance division-a64-unsigned-bounded (width 64) (x value))
                   :in-theory (disable division-a64-unsigned-bounded)))
   :rule-classes :type-prescription))

(local
 (defthm division-unsigned-word-limit
   (< (boymoo-model::a64-unsigned 64 value) (expt 2 64))
   :hints (("Goal" :use (:instance division-a64-unsigned-bounded (width 64) (x value))
                   :in-theory (disable division-a64-unsigned-bounded)))
   :rule-classes :linear))

(local
 (defthm division-register-bounded
   (unsigned-byte-p 64 (proof-reg register machine))
   :hints (("Goal"
            :in-theory (e/d (proof-reg boymoo-model::a64-read-reg)
                            (division-general-register-read))))
   :rule-classes :rewrite))

(local
 (defthm division-register-natural
   (natp (proof-reg register machine))
   :hints (("Goal" :use (:instance division-register-bounded)
                   :in-theory (disable division-register-bounded)))
   :rule-classes :type-prescription))

(local
 (defthm division-register-limit
   (< (proof-reg register machine) (expt 2 64))
   :hints (("Goal" :use (:instance division-register-bounded)
                   :in-theory (disable division-register-bounded)))
   :rule-classes :linear))

(local
 (defthm division-assoc-of-put-assoc
   (equal (assoc-equal key (put-assoc-equal put-key value table))
          (if (equal key put-key) (cons key value) (assoc-equal key table)))
   :hints (("Goal" :induct (put-assoc-equal put-key value table)))))

(local
 (defthm division-read-register-after-write
   (implies (and (natp read) (< read 31) (natp write) (< write 31))
            (equal (proof-reg read (boymoo-model::a64-write-reg write 64 nil value machine))
                   (if (equal read write)
                       (boymoo-model::a64-unsigned 64 value)
                     (proof-reg read machine))))
   :hints (("Goal"
            :in-theory (e/d (proof-reg boymoo-model::a64-read-reg boymoo-model::a64-write-reg)
                            (division-general-register-read))))))

(local
 (defthm division-write-register-ordinary
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-write-reg register 64 t value machine)
                   (boymoo-model::a64-write-reg register 64 nil value machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-pc-after-write
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-pc
                    (boymoo-model::a64-write-reg register 64 nil value machine))
                   (boymoo-model::a64-pc machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-pc-after-set
   (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-unsigned 64 pc))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-pc-natural
   (natp (boymoo-model::a64-pc machine))
   :rule-classes :type-prescription))

(local
 (defthm division-memory-after-write
   (equal (boymoo-model::a64-memory
           (boymoo-model::a64-write-reg register 64 nil value machine))
          (boymoo-model::a64-memory machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-memory-after-pc
   (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-memory machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-state-after-register-write
   (implies (and (natp register) (< register 31))
            (and (consp (boymoo-model::a64-write-reg register 64 nil value machine))
                 (consp (car (boymoo-model::a64-write-reg register 64 nil value machine)))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-register-write-is-an-instruction-state
   (implies (and (natp register) (< register 31))
            (and (not (equal (car (boymoo-model::a64-write-reg register 64 nil value machine)) :svc))
                 (not (equal (boymoo-model::a64-write-reg register 64 nil value machine) :undefined))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-shift-limb-into-high-word
   (implies (division-digit-p digit)
            (equal (boymoo-model::a64-shift 0 64 digit 32)
                   (* *division-radix* digit)))))

(local
 (defthm division-compute-add-effect
   (equal (proof-instruction-effect '(:arithmetic-reg 0 64 6 6 5 0 32) world)
          (let* ((machine (proof-world-machine world))
                 (sum (+ (proof-reg 6 machine)
                         (boymoo-model::a64-shift 0 64 (proof-reg 5 machine) 32))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           6 64 nil (boymoo-model::a64-unsigned 64 sum)
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect)
                            (boymoo-model::a64-shift division-shift-limb-into-high-word))))))

(local
 (defthm division-compute-udiv-effect
   (equal (proof-instruction-effect '(:divide 7 6 3 nil) world)
          (let* ((machine (proof-world-machine world))
                 (divisor (proof-reg 3 machine))
                 (q (if (equal divisor 0) 0 (floor (proof-reg 6 machine) divisor))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           7 64 nil q
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm division-compute-msub-effect
   (equal (proof-instruction-effect '(:multiply-subtract 5 7 3 6) world)
          (let* ((machine (proof-world-machine world))
                 (r (- (proof-reg 6 machine) (* (proof-reg 7 machine) (proof-reg 3 machine)))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           5 64 nil r
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defthm division-one-limb-arithmetic-effects
  (implies (and (division-digit-p (proof-world-reg 6 world))
                (division-digit-p (proof-world-reg 3 world))
                (posp (proof-world-reg 3 world))
                (< (proof-world-reg 5 world) (proof-world-reg 3 world))
                (unsigned-byte-p 64 (+ (proof-world-pc world) 12)))
           (let* ((after (division-instruction-sequence *division-one-limb-computation* world))
                  (step (division-one-limb-step (proof-world-reg 6 world)
                                                 (proof-world-reg 5 world)
                                                 (proof-world-reg 3 world))))
             (and (equal (proof-world-reg 7 after) (mv-nth 0 step))
                  (equal (proof-world-reg 5 after) (mv-nth 1 step))
                  (equal (proof-world-pc after) (+ (proof-world-pc world) 12))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use (:instance division-one-limb-step-correct
                           (digit (proof-world-reg 6 world))
                           (remainder (proof-world-reg 5 world))
                           (divisor (proof-world-reg 3 world)))
           :in-theory (e/d (proof-world-pc proof-world-reg proof-world-stop)
                           (boymoo-model::a64-shift boymoo-model::a64-pc
                            boymoo-model::a64-memory))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-one-limb-arithmetic-run
  (let* ((cuts (list (+ (proof-world-pc world) 12)))
         (after (division-instruction-sequence *division-one-limb-computation* world))
         (step (division-one-limb-step (proof-world-reg 6 world)
                                       (proof-world-reg 5 world)
                                       (proof-world-reg 3 world))))
    (implies (and (division-digit-p (proof-world-reg 6 world))
                  (division-digit-p (proof-world-reg 3 world))
                  (posp (proof-world-reg 3 world))
                  (< (proof-world-reg 5 world) (proof-world-reg 3 world))
                  (unsigned-byte-p 64 (+ (proof-world-pc world) 12))
                  (division-instruction-sequence-ready-p *division-one-limb-computation* cuts world))
             (and (proof-segment-p 3 cuts world :cut after)
                  (equal (proof-world-reg 7 after) (mv-nth 0 step))
                  (equal (proof-world-reg 5 after) (mv-nth 1 step)))))
  :hints (("Goal"
           :use ((:instance division-one-limb-arithmetic-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-one-limb-computation*)
                            (cuts (list (+ (proof-world-pc world) 12)))))
           :in-theory (disable division-instruction-sequence division-instruction-sequence-ready-p
                               proof-segment-p)))
  :rule-classes nil)

(local
 (defthm division-subtract-eight-without-wrap
   (implies (and (unsigned-byte-p 64 value) (<= 8 value))
            (equal (boymoo-model::a64-unsigned 64 (+ value (- (expt 2 64) 8)))
                   (- value 8)))
   :hints (("Goal"
            :use ((:instance division-a64-unsigned-is-remainder
                             (width 64) (x (+ value (- (expt 2 64) 8))))
                  (:instance division-signed-remainder-unique
                             (a (+ value (- (expt 2 64) 8))) (b (expt 2 64))
                             (q 1) (r (- value 8))))))))

(local
 (defthm division-read-register-for-address
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-read-reg register 64 t machine)
                   (proof-reg register machine)))
   :hints (("Goal"
            :in-theory (e/d (proof-reg boymoo-model::a64-read-reg)
                            (division-general-register-read))))))

(local
 (defthm division-car-after-update-nth
   (implies (posp index)
            (equal (car (update-nth index value sequence)) (car sequence)))
   :hints (("Goal" :expand ((update-nth index value sequence))))))

(local
 (defthm division-car-after-set-pc
   (equal (car (boymoo-model::a64-set-pc pc machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local (in-theory (disable boymoo-model::a64-load boymoo-model::a64-store proof-load-word)))

(local
 (defthm division-car-after-store
   (equal (car (boymoo-model::a64-store count address value machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store)))))

(local
 (defthm division-read-register-after-store
   (equal (proof-reg register (boymoo-model::a64-store count address value machine))
          (proof-reg register machine))
   :hints (("Goal"
            :in-theory (e/d (proof-reg boymoo-model::a64-read-reg boymoo-model::a64-store)
                            (division-general-register-read))))))

(local
 (defthm division-pc-after-store
   (equal (boymoo-model::a64-pc (boymoo-model::a64-store count address value machine))
          (boymoo-model::a64-pc machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store)))))

(local
 (defthm division-sp-after-write
   (equal (boymoo-model::a64-sp (boymoo-model::a64-write-reg register 64 nil value machine))
          (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-sp-after-set-pc
   (equal (boymoo-model::a64-sp (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-sp-after-store
   (equal (boymoo-model::a64-sp (boymoo-model::a64-store count address value machine))
          (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store)))))

(local
 (defthm division-load-word-after-register-write
   (equal (proof-load-word address (boymoo-model::a64-write-reg register 64 nil value machine))
          (proof-load-word address machine))
   :hints (("Goal"
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes boymoo-model::a64-memory))))))

(local
 (defthm division-load-word-after-set-pc
   (equal (proof-load-word address (boymoo-model::a64-set-pc pc machine))
          (proof-load-word address machine))
   :hints (("Goal"
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes boymoo-model::a64-memory))))))

(local
 (defthm division-memory-of-store
   (equal (boymoo-model::a64-memory (boymoo-model::a64-store count address value machine))
          (boymoo-model::a64-write-bytes count address value (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store)))))

(local
 (defthm division-update-nth-twice
   (equal (update-nth index value (update-nth index previous sequence))
          (update-nth index value sequence))
   :hints (("Goal" :induct (update-nth index previous sequence)))))

(local
 (defthm division-set-pc-twice
   (equal (boymoo-model::a64-set-pc target (boymoo-model::a64-set-pc previous machine))
          (boymoo-model::a64-set-pc target machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-one-limb-offset-effect
   (equal (proof-instruction-effect '(:arithmetic-imm 2 64 4 4 8) world)
          (let* ((machine (proof-world-machine world))
                 (value (boymoo-model::a64-unsigned
                         64 (+ (proof-reg 4 machine) (- (expt 2 64) 8)))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           4 64 nil value
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm division-one-limb-load-effect
   (equal (proof-instruction-effect '(:single 1 8 0 6 :register 4 3 0) world)
          (let* ((machine (proof-world-machine world))
                 (address (+ (proof-reg 0 machine) (proof-reg 4 machine))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           6 64 nil (proof-load-word address machine)
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect boymoo-model::a64-load proof-load-word)
                            (boymoo-model::a64-read-bytes))))))

(local
 (defthm division-one-limb-store-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:single 0 8 21 7 :register 4 3 0) world)
                   (let* ((machine (proof-world-machine world))
                          (address (+ (proof-reg 21 machine) (proof-reg 4 machine))))
                     (update-nth 0 (boymoo-model::a64-store
                                    8 address (proof-reg 7 machine)
                                    (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine))
                                                               machine))
                                 world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect boymoo-model::a64-store)))))

(local
 (defthm division-one-limb-branch-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:branch-zero -24 64 4 t) world)
                   (let* ((machine (proof-world-machine world))
                          (pc (boymoo-model::a64-pc machine))
                          (target (if (equal (proof-reg 4 machine) 0) (+ pc 4) (- pc 24))))
                     (update-nth 0 (boymoo-model::a64-set-pc target machine) world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect boymoo-model::a64-set-pc)))))

(defun division-one-limb-iteration-inputs-p (world)
  (let* ((offset (- (proof-world-reg 4 world) 8))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 21 world) offset))
         (digit (proof-load-word source (proof-world-machine world)))
         (divisor (proof-world-reg 3 world)))
    (and (natp offset)
         (proof-span-p source 8) (proof-span-p target 8)
         (division-digit-p digit)
         (division-digit-p divisor) (posp divisor)
         (< (proof-world-reg 5 world) divisor)
         (unsigned-byte-p 64 (+ (proof-world-pc world) 28)))))

(defun division-one-limb-iteration-output-p (world after)
  (let* ((offset (- (proof-world-reg 4 world) 8))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 21 world) offset))
         (digit (proof-load-word source (proof-world-machine world))))
    (mv-let (q r)
      (division-one-limb-step digit (proof-world-reg 5 world) (proof-world-reg 3 world))
      (and (equal (proof-world-reg 4 after) offset)
           (equal (proof-world-reg 5 after) r)
           (equal (proof-world-reg 7 after) q)
           (equal (proof-world-pc after)
                  (if (equal offset 0) (+ (proof-world-pc world) 28) (proof-world-pc world)))
           (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
           (equal (proof-world-reg 3 after) (proof-world-reg 3 world))
           (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
           (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
           (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
           (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
           (equal (proof-world-regions after) (proof-world-regions world))
           (equal (boymoo-model::a64-sp (proof-world-machine after))
                  (boymoo-model::a64-sp (proof-world-machine world)))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (boymoo-model::a64-write-bytes
                   8 target q (boymoo-model::a64-memory (proof-world-machine world))))
           (equal (proof-world-stop after) (proof-world-stop world))))))

(defthm division-one-limb-iteration-effects
  (implies (division-one-limb-iteration-inputs-p world)
           (division-one-limb-iteration-output-p
            world (division-instruction-sequence *division-one-limb-instructions* world)))
  :hints (("Goal"
           :use ((:instance division-one-limb-step-correct
                            (digit (proof-load-word (+ (proof-world-reg 0 world)
                                                       (- (proof-world-reg 4 world) 8))
                                                    (proof-world-machine world)))
                            (remainder (proof-world-reg 5 world))
                            (divisor (proof-world-reg 3 world)))
                 (:instance division-subtract-eight-without-wrap (value (proof-world-reg 4 world)))
                 (:instance division-register-bounded (register 4) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-world-pc proof-world-reg proof-world-stop)
                           (boymoo-model::a64-shift boymoo-model::a64-pc boymoo-model::a64-memory
                            boymoo-model::a64-sp
                            boymoo-model::a64-write-bytes division-subtract-eight-without-wrap
                            division-register-bounded))
           :do-not-induct t))
  :rule-classes nil)

(defconst *division-one-limb-before-branch* (take 6 *division-one-limb-instructions*))

(local
 (defthm division-one-limb-before-branch-ready-from-code
   (implies (and (division-one-limb-iteration-inputs-p world)
                 (not (proof-world-stop world))
                 (proof-instructions-at-p
                  *division-one-limb-instructions* (proof-world-pc world) world)
                 (proof-covered-p (+ (proof-world-reg 0 world) (- (proof-world-reg 4 world) 8))
                                  8 :read (proof-world-regions world))
                 (proof-covered-p (+ (proof-world-reg 21 world) (- (proof-world-reg 4 world) 8))
                                  8 :write (proof-world-regions world)))
            (division-instruction-sequence-ready-p
             *division-one-limb-before-branch* (list (+ (proof-world-pc world) 24)) world))
   :hints (("Goal"
            :use ((:instance division-one-limb-step-correct
                             (digit (proof-load-word (+ (proof-world-reg 0 world)
                                                        (- (proof-world-reg 4 world) 8))
                                                     (proof-world-machine world)))
                             (remainder (proof-world-reg 5 world))
                             (divisor (proof-world-reg 3 world)))
                  (:instance division-subtract-eight-without-wrap (value (proof-world-reg 4 world)))
                  (:instance division-register-bounded (register 4) (machine (proof-world-machine world))))
            :in-theory (e/d (proof-world-pc proof-world-reg proof-world-stop
                                            division-instruction-at-depends-on-bytes)
                            (boymoo-model::a64-shift boymoo-model::a64-pc boymoo-model::a64-memory
                             boymoo-model::a64-write-bytes boymoo-model::a64-read-bytes
                             proof-decode proof-covered-p proof-instruction-at-p
                             division-decoded-word-at-p
                             division-subtract-eight-without-wrap division-register-bounded))
            :do-not-induct t))))

(local
 (defthm division-one-limb-before-branch-frame
   (implies (division-one-limb-iteration-inputs-p world)
            (let* ((after (division-instruction-sequence *division-one-limb-before-branch* world))
                   (offset (- (proof-world-reg 4 world) 8))
                   (source (+ (proof-world-reg 0 world) offset))
                   (target (+ (proof-world-reg 21 world) offset))
                   (digit (proof-load-word source (proof-world-machine world)))
                   (q (mv-nth 0 (division-one-limb-step
                                 digit (proof-world-reg 5 world) (proof-world-reg 3 world)))))
              (and (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-write-bytes
                           8 target q (boymoo-model::a64-memory (proof-world-machine world)))))))
   :hints (("Goal"
            :use ((:instance division-one-limb-step-correct
                             (digit (proof-load-word (+ (proof-world-reg 0 world)
                                                        (- (proof-world-reg 4 world) 8))
                                                     (proof-world-machine world)))
                             (remainder (proof-world-reg 5 world))
                             (divisor (proof-world-reg 3 world)))
                  (:instance division-subtract-eight-without-wrap (value (proof-world-reg 4 world)))
                  (:instance division-register-bounded (register 4) (machine (proof-world-machine world))))
            :in-theory (e/d (proof-world-pc proof-world-reg)
                            (boymoo-model::a64-shift boymoo-model::a64-pc boymoo-model::a64-memory
                             boymoo-model::a64-write-bytes division-subtract-eight-without-wrap
                             division-register-bounded))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-one-limb-sequence-split
   (equal (division-instruction-sequence *division-one-limb-instructions* world)
          (proof-instruction-effect
           (nth 6 *division-one-limb-instructions*)
           (division-instruction-sequence *division-one-limb-before-branch* world)))
   :hints (("Goal"
            :in-theory (disable division-one-limb-offset-effect division-one-limb-load-effect
                                division-compute-add-effect division-compute-udiv-effect
                                division-compute-msub-effect division-one-limb-store-effect
                                division-one-limb-branch-effect)))
   :rule-classes nil))

(defun division-one-limb-iteration-ready-p (world)
  (let* ((cut (+ (proof-world-pc world) 24))
         (branch (nth 6 *division-one-limb-instructions*))
         (at-branch (division-instruction-sequence *division-one-limb-before-branch* world)))
    (and (division-one-limb-iteration-inputs-p world)
         (division-instruction-sequence-ready-p *division-one-limb-before-branch* (list cut) world)
         (proof-instruction-at-p branch cut at-branch))))

(defthm division-one-limb-iteration-ready-from-spans
  (let* ((pc (proof-world-pc world))
         (offset (- (proof-world-reg 4 world) 8))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 21 world) offset)))
    (implies (and (division-one-limb-iteration-inputs-p world)
                  (not (proof-world-stop world))
                  (proof-instructions-at-p *division-one-limb-instructions* pc world)
                  (proof-covered-p source 8 :read (proof-world-regions world))
                  (proof-covered-p target 8 :write (proof-world-regions world))
                  (proof-disjoint-p target (+ target 8) pc (+ pc 28)))
             (division-one-limb-iteration-ready-p world)))
  :hints (("Goal"
           :use ((:instance division-one-limb-before-branch-frame)
                 (:instance division-one-limb-before-branch-ready-from-code)
                 (:instance division-instruction-at-after-disjoint-write
                            (pc (+ (proof-world-pc world) 24))
                            (instruction (nth 6 *division-one-limb-instructions*))
                            (before world)
                            (after (division-instruction-sequence *division-one-limb-before-branch* world))
                            (address (+ (proof-world-reg 21 world) (- (proof-world-reg 4 world) 8)))
                            (count 8)
                            (value (mv-nth 0 (division-one-limb-step
                                              (proof-load-word (+ (proof-world-reg 0 world)
                                                                  (- (proof-world-reg 4 world) 8))
                                                               (proof-world-machine world))
                                              (proof-world-reg 5 world) (proof-world-reg 3 world))))))
           :in-theory (disable division-one-limb-before-branch-ready-from-code
                               division-instruction-sequence division-instruction-sequence-ready-p
                               proof-instruction-at-p proof-covered-p proof-world-machine
                               proof-world-regions boymoo-model::a64-memory boymoo-model::a64-write-bytes)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-one-limb-iteration-runs
  (let* ((cuts (list (+ (proof-world-pc world) 24)))
         (at-branch (division-instruction-sequence *division-one-limb-before-branch* world)))
    (implies (division-one-limb-iteration-ready-p world)
             (and (proof-segment-p 6 cuts world :cut at-branch)
                  (division-one-limb-iteration-output-p world (proof-step at-branch)))))
  :hints (("Goal"
           :use ((:instance division-one-limb-iteration-effects)
                 (:instance division-one-limb-sequence-split)
                 (:instance division-instruction-sequence-finishes-at-ready-cut
                            (instructions *division-one-limb-before-branch*)
                            (cuts (list (+ (proof-world-pc world) 24))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-one-limb-before-branch*)
                            (cuts (list (+ (proof-world-pc world) 24))))
                 (:instance proof-step-from-instruction
                            (world (division-instruction-sequence *division-one-limb-before-branch* world))
                            (instruction (nth 6 *division-one-limb-instructions*))))
           :in-theory (disable proof-step-from-instruction proof-instruction-at-p
                               division-instruction-sequence division-instruction-sequence-ready-p
                               division-one-limb-iteration-output-p division-one-limb-iteration-inputs-p
                               proof-segment-p division-one-limb-branch-effect)))
  :rule-classes nil)

(local
 (defthm division-advance-one-step
   (equal (proof-advance 1 world) (proof-step world))
   :hints (("Goal" :expand ((proof-advance 1 world) (proof-advance 0 (proof-step world)))))))

(defthm division-one-limb-iteration-advances
  (implies (division-one-limb-iteration-ready-p world)
           (division-one-limb-iteration-output-p world (proof-advance 7 world)))
  :hints (("Goal"
           :use ((:instance division-one-limb-iteration-runs)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-one-limb-before-branch*)
                            (cuts (list (+ (proof-world-pc world) 24))))
                 (:instance proof-advance-append (prefix 6) (suffix 1)))
           :in-theory (disable proof-advance proof-instruction-at-p proof-segment-p proof-step
                               division-instruction-sequence division-instruction-sequence-ready-p
                               division-one-limb-iteration-inputs-p division-one-limb-iteration-output-p)))
  :rule-classes nil)

(defconst *division-immediate-quotient-instructions*
  '((:bitfield 0 64 0 0 1 63 #xffffffffffffffff #x7fffffffffffffff)
    (:bitfield 0 64 1 1 1 63 #xffffffffffffffff #x7fffffffffffffff)
    (:divide 0 0 1 t)
    (:bitfield 2 64 0 0 63 62 #xfffffffffffffffe #xffffffffffffffff)
    (:arithmetic-imm 0 64 0 0 1)
    (:branch-reg 30 nil)))

(defthm division-immediate-quotient-instructions-are-emitted
  (let* ((items (division-linked-example-items))
         (offset (division-label-offset "rt:z-quotient-immediate" items))
         (image (boymoo-compiler::a64-bytes items))
         (machine (proof-load-cleared-string image 0
                                             (boymoo-model::a64-state nil 0 0 0 nil))))
    (equal (division-decode-instructions 6 offset machine)
           *division-immediate-quotient-instructions*))
  :rule-classes nil)

(local
 (defthm division-immediate-asr-x0-effect
   (equal (proof-instruction-effect
           '(:bitfield 0 64 0 0 1 63 #xffffffffffffffff #x7fffffffffffffff) world)
          (let ((machine (proof-world-machine world)))
            (update-nth 0 (boymoo-model::a64-write-reg
                           0 64 nil (division-asr-one-result (proof-reg 0 machine))
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect)
                            (boymoo-model::a64-ror logbitp acl2::binary-logand acl2::binary-logior))))))

(local
 (defthm division-immediate-asr-x1-effect
   (equal (proof-instruction-effect
           '(:bitfield 0 64 1 1 1 63 #xffffffffffffffff #x7fffffffffffffff) world)
          (let ((machine (proof-world-machine world)))
            (update-nth 0 (boymoo-model::a64-write-reg
                           1 64 nil (division-asr-one-result (proof-reg 1 machine))
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect)
                            (boymoo-model::a64-ror logbitp acl2::binary-logand acl2::binary-logior))))))

(local
 (defthm division-immediate-sdiv-effect
   (equal (proof-instruction-effect '(:divide 0 0 1 t) world)
          (let* ((machine (proof-world-machine world))
                 (left (proof-reg 0 machine))
                 (right (proof-reg 1 machine))
                 (result (if (equal right 0)
                             0
                           (truncate (boymoo-model::a64-signed 64 left)
                                     (boymoo-model::a64-signed 64 right)))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           0 64 nil result
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (e/d (proof-instruction-effect) (boymoo-model::a64-signed))))))

(local
 (defthm division-immediate-lsl-x0-effect
   (equal (proof-instruction-effect
           '(:bitfield 2 64 0 0 63 62 #xfffffffffffffffe #xffffffffffffffff) world)
          (let ((machine (proof-world-machine world)))
            (update-nth 0 (boymoo-model::a64-write-reg
                           0 64 nil (division-lsl-one-result (proof-reg 0 machine))
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect)
                            (boymoo-model::a64-ror acl2::binary-logand acl2::binary-logior))))))

(local
 (defthm division-immediate-add-tag-effect
   (equal (proof-instruction-effect '(:arithmetic-imm 0 64 0 0 1) world)
          (let* ((machine (proof-world-machine world))
                 (result (boymoo-model::a64-unsigned 64 (1+ (proof-reg 0 machine)))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           0 64 nil result
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm division-immediate-ret-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:branch-reg 30 nil) world)
                   (let ((machine (proof-world-machine world)))
                     (update-nth 0 (boymoo-model::a64-set-pc (proof-reg 30 machine) machine) world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defun division-immediate-quotient-inputs-p (a b quotient world)
  (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
       (proof-immediate-integer-p quotient)
       (posp b) (proof-exact-quotient-p a b quotient)
       (equal (proof-world-reg 0 world) (proof-integer-word a))
       (equal (proof-world-reg 1 world) (proof-integer-word b))))

(defthm division-immediate-quotient-effects
  (implies (division-immediate-quotient-inputs-p a b quotient world)
           (let ((after (division-instruction-sequence *division-immediate-quotient-instructions* world)))
             (and (equal (proof-world-reg 0 after) (proof-integer-word quotient))
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance division-asr-decodes-immediate (value a))
                 (:instance division-asr-decodes-immediate (value b))
                 (:instance division-signed-word-round-trip (value a))
                 (:instance division-signed-word-round-trip (value b))
                 (:instance division-truncate-exact (q quotient))
                 (:instance division-lsl-one-result-in-word (word (boymoo-model::a64-unsigned 64 quotient)))
                 (:instance division-a64-unsigned-bounded (width 64) (x quotient))
                 (:instance division-lsl-and-add-encode-immediate (value quotient)))
           :in-theory (e/d (proof-world-reg proof-world-pc proof-world-stop)
                           (boymoo-model::a64-signed boymoo-model::a64-pc boymoo-model::a64-memory
                            division-signed-interpretation-of-word division-signed-word-round-trip
                            proof-integer-word division-asr-one-result division-lsl-one-result
                            division-a64-unsigned-bounded))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-immediate-quotient-returns
  (let* ((cuts (list (proof-world-reg 30 world)))
         (after (division-instruction-sequence *division-immediate-quotient-instructions* world)))
    (implies (and (division-immediate-quotient-inputs-p a b quotient world)
                  (division-instruction-sequence-ready-p *division-immediate-quotient-instructions*
                                                         cuts world))
             (and (proof-segment-p 6 cuts world :cut after)
                  (equal (proof-world-reg 0 after) (proof-integer-word quotient)))))
  :hints (("Goal"
           :use ((:instance division-immediate-quotient-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-immediate-quotient-instructions*)
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-instruction-sequence division-instruction-sequence-ready-p
                               proof-segment-p division-immediate-quotient-inputs-p)))
  :rule-classes nil)

(defconst *division-gcd-word-instructions*
  '((:divide 2 0 1 nil)
    (:multiply-subtract 2 2 1 0)
    (:logical-reg 1 64 0 31 1 0 0 nil)
    (:logical-reg 1 64 1 31 2 0 0 nil)
    (:branch-zero -16 64 1 t)))

(defthm division-gcd-word-instructions-are-emitted
  (let* ((items (division-linked-example-items))
         (offset (division-label-offset "rt:z-gcd-word-loop" items))
         (image (boymoo-compiler::a64-bytes items))
         (machine (proof-load-cleared-string image 0
                                             (boymoo-model::a64-state nil 0 0 0 nil))))
    (equal (division-decode-instructions 5 offset machine) *division-gcd-word-instructions*))
  :rule-classes nil)

(local
 (defthm division-gcd-udiv-effect
   (equal (proof-instruction-effect '(:divide 2 0 1 nil) world)
          (let* ((machine (proof-world-machine world))
                 (b (proof-reg 1 machine))
                 (q (if (equal b 0) 0 (floor (proof-reg 0 machine) b))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           2 64 nil q
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm division-gcd-msub-effect
   (equal (proof-instruction-effect '(:multiply-subtract 2 2 1 0) world)
          (let* ((machine (proof-world-machine world))
                 (r (- (proof-reg 0 machine) (* (proof-reg 1 machine) (proof-reg 2 machine)))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           2 64 nil r
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm division-zero-register
   (equal (proof-reg 31 machine) 0)
   :hints (("Goal"
            :in-theory (e/d (proof-reg boymoo-model::a64-read-reg)
                            (division-general-register-read))))))

(local
 (defthm division-gcd-move-left-effect
   (equal (proof-instruction-effect '(:logical-reg 1 64 0 31 1 0 0 nil) world)
          (let ((machine (proof-world-machine world)))
            (update-nth 0 (boymoo-model::a64-write-reg
                           0 64 nil (proof-reg 1 machine)
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect)
                            (acl2::binary-logior))))))

(local
 (defthm division-gcd-move-right-effect
   (equal (proof-instruction-effect '(:logical-reg 1 64 1 31 2 0 0 nil) world)
          (let ((machine (proof-world-machine world)))
            (update-nth 0 (boymoo-model::a64-write-reg
                           1 64 nil (proof-reg 2 machine)
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect)
                            (acl2::binary-logior))))))

(local
 (defthm division-gcd-branch-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:branch-zero -16 64 1 t) world)
                   (let* ((machine (proof-world-machine world))
                          (pc (boymoo-model::a64-pc machine))
                          (target (if (equal (proof-reg 1 machine) 0) (+ pc 4) (- pc 16))))
                     (update-nth 0 (boymoo-model::a64-set-pc target machine) world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect boymoo-model::a64-set-pc)))))

(defun division-gcd-word-iteration-output-p (world after)
  (let* ((a (proof-world-reg 0 world))
         (b (proof-world-reg 1 world))
         (r (mod a b)))
    (and (equal (proof-world-reg 0 after) b)
         (equal (proof-world-reg 1 after) r)
         (natp r) (< r b)
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after)
                (if (equal r 0) (+ 20 (proof-world-pc world)) (proof-world-pc world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world)))))

(local
 (defthm division-floor-is-a-word
   (implies (and (unsigned-byte-p 64 a) (posp b))
            (unsigned-byte-p 64 (floor a b)))
   :hints (("Goal"
            :use (:instance division-floor-at-least (q (expt 2 64)))
            :cases ((< a (* (expt 2 64) b)))))
   :rule-classes nil))

(defthm division-gcd-word-iteration-effects
  (implies (and (posp (proof-world-reg 1 world))
                (unsigned-byte-p 64 (+ 20 (proof-world-pc world))))
           (division-gcd-word-iteration-output-p
            world (division-instruction-sequence *division-gcd-word-instructions* world)))
  :hints (("Goal"
           :use ((:instance division-register-bounded (register 0) (machine (proof-world-machine world)))
                 (:instance division-register-bounded (register 1) (machine (proof-world-machine world)))
                 (:instance division-floor-is-a-word (a (proof-world-reg 0 world))
                            (b (proof-world-reg 1 world)))
                 (:instance division-mod-bounds (a (proof-world-reg 0 world))
                            (b (proof-world-reg 1 world)))
                 (:instance division-floor-mod-identity (a (proof-world-reg 0 world))
                            (b (proof-world-reg 1 world))))
           :in-theory (e/d (proof-world-reg proof-world-pc proof-world-stop)
                           (boymoo-model::a64-pc boymoo-model::a64-memory division-floor-mod-identity
                            division-register-bounded))
           :do-not-induct t))
  :rule-classes nil)

(defconst *division-gcd-word-before-branch* (take 4 *division-gcd-word-instructions*))

(defun division-gcd-word-iteration-ready-p (world)
  (let* ((cut (+ 16 (proof-world-pc world)))
         (middle (division-instruction-sequence *division-gcd-word-before-branch* world)))
    (and (posp (proof-world-reg 1 world))
         (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
         (division-instruction-sequence-ready-p *division-gcd-word-before-branch* (list cut) world)
         (proof-instruction-at-p (nth 4 *division-gcd-word-instructions*) cut middle))))

(local
 (defthm division-gcd-word-sequence-split
   (equal (division-instruction-sequence *division-gcd-word-instructions* world)
          (proof-instruction-effect
           (nth 4 *division-gcd-word-instructions*)
           (division-instruction-sequence *division-gcd-word-before-branch* world)))
   :hints (("Goal"
            :in-theory (disable division-gcd-udiv-effect division-gcd-msub-effect
                                division-gcd-move-left-effect division-gcd-move-right-effect
                                division-gcd-branch-effect)))
   :rule-classes nil))

(defthm division-gcd-word-iteration-advances
  (implies (division-gcd-word-iteration-ready-p world)
           (division-gcd-word-iteration-output-p world (proof-advance 5 world)))
  :hints (("Goal"
           :use ((:instance division-gcd-word-iteration-effects)
                 (:instance division-gcd-word-sequence-split)
                 (:instance division-instruction-sequence-then-one-step
                            (prefix *division-gcd-word-before-branch*)
                            (cuts (list (+ 16 (proof-world-pc world))))
                            (last (nth 4 *division-gcd-word-instructions*)))
                 (:instance division-instruction-sequence-finishes-at-ready-cut
                            (instructions *division-gcd-word-before-branch*)
                            (cuts (list (+ 16 (proof-world-pc world))))))
           :in-theory (disable proof-advance proof-instruction-at-p division-gcd-word-iteration-output-p
                               division-instruction-sequence division-instruction-sequence-ready-p
                               division-gcd-branch-effect)))
  :rule-classes nil)

(defun division-gcd-word-loop-entry-p (world)
  (and (not (proof-world-stop world))
       (posp (proof-world-reg 1 world))
       (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
       (proof-instructions-at-p *division-gcd-word-instructions* (proof-world-pc world) world)))

(defthm division-gcd-word-iteration-ready-from-code
  (implies (division-gcd-word-loop-entry-p world)
           (division-gcd-word-iteration-ready-p world))
  :hints (("Goal"
           :in-theory (e/d (proof-world-reg proof-world-pc proof-world-stop boymoo-model::a64-load)
                           (boymoo-model::a64-pc boymoo-model::a64-memory boymoo-model::a64-read-bytes
                            proof-decode proof-covered-p))
           :do-not-induct t))
  :rule-classes nil)

(defconst *division-gcd-immediate-setup-instructions*
  '((:bitfield 0 64 0 0 1 63 #xffffffffffffffff #x7fffffffffffffff)
    (:bitfield 0 64 1 1 1 63 #xffffffffffffffff #x7fffffffffffffff)
    (:arithmetic-imm 3 64 31 0 0)
    (:arithmetic-reg 2 64 2 31 0 0 0)
    (:select 64 0 2 0 11 nil)))

(defconst *division-immediate-return-instructions*
  (nthcdr 3 *division-immediate-quotient-instructions*))

(defthm division-gcd-immediate-setup-and-return-are-emitted
  (let* ((items (division-linked-example-items))
         (setup (division-label-offset "rt:z-gcd-immediate" items))
         (loop-entry (division-label-offset "rt:z-gcd-word-loop" items))
         (image (boymoo-compiler::a64-bytes items))
         (machine (proof-load-cleared-string image 0
                                             (boymoo-model::a64-state nil 0 0 0 nil))))
    (and (equal (+ setup 20) loop-entry)
         (equal (division-decode-instructions 5 setup machine)
                *division-gcd-immediate-setup-instructions*)
         (equal (division-decode-instructions 3 (+ loop-entry 20) machine)
                *division-immediate-return-instructions*)))
  :rule-classes nil)

(local
 (defthm division-write-to-zero-register
   (equal (boymoo-model::a64-write-reg 31 64 nil value machine) machine)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-frame-after-set-flags
   (let ((next (boymoo-model::a64-set-nzcv flags machine)))
     (and (equal (car next) (car machine))
          (equal (proof-reg register next) (proof-reg register machine))
          (equal (boymoo-model::a64-pc next) (boymoo-model::a64-pc machine))
          (equal (boymoo-model::a64-memory next) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-nzcv next) (boymoo-model::a64-unsigned 4 flags))))
   :hints (("Goal" :cases ((consp machine))
                   :in-theory (e/d (boymoo-model::a64-set-nzcv proof-reg boymoo-model::a64-read-reg)
                                   (division-general-register-read))))))

(local
 (defthm division-flags-after-set-pc
   (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-nzcv machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm division-flags-after-register-write
   (equal (boymoo-model::a64-nzcv (boymoo-model::a64-write-reg register 64 nil value machine))
          (boymoo-model::a64-nzcv machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm division-compare-zero-flags-fit
   (unsigned-byte-p 4 (division-word-compare-zero-flags word))))

(local
 (defthm division-gcd-compare-zero-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:arithmetic-imm 3 64 31 0 0) world)
                   (let ((machine (proof-world-machine world)))
                     (update-nth 0
                                 (boymoo-model::a64-set-nzcv
                                  (division-word-compare-zero-flags (proof-reg 0 machine))
                                  (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                                 world))))
   :hints (("Goal"
            :use ((:instance division-word-plus-modulus (word (proof-reg 0 (proof-world-machine world))))
                  (:instance division-result-flags-for-zero-comparison
                             (word (proof-reg 0 (proof-world-machine world))))
                  (:instance division-register-bounded (register 0) (machine (proof-world-machine world))))
            :in-theory (e/d (proof-instruction-effect)
                            (boymoo-model::a64-result-flags boymoo-model::a64-set-nzcv
                             division-word-compare-zero-flags division-register-bounded logbitp))))))

(local
 (defthm division-gcd-negate-effect
   (equal (proof-instruction-effect '(:arithmetic-reg 2 64 2 31 0 0 0) world)
          (let* ((machine (proof-world-machine world))
                 (result (boymoo-model::a64-unsigned 64
                                                     (- *division-word-modulus* (proof-reg 0 machine)))))
            (update-nth 0
                        (boymoo-model::a64-write-reg
                         2 64 nil result
                         (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :use ((:instance division-xor-word-complement (word (proof-reg 0 (proof-world-machine world))))
                  (:instance division-register-bounded (register 0) (machine (proof-world-machine world))))
            :in-theory (e/d (proof-instruction-effect)
                            (acl2::binary-logxor division-register-bounded))))))

(local
 (defthm division-gcd-select-sign-effect
   (equal (proof-instruction-effect '(:select 64 0 2 0 11 nil) world)
          (let* ((machine (proof-world-machine world))
                 (word (if (boymoo-model::a64-condition 11 (boymoo-model::a64-nzcv machine))
                           (proof-reg 2 machine)
                         (proof-reg 0 machine))))
            (update-nth 0
                        (boymoo-model::a64-write-reg
                         0 64 nil word
                         (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (e/d (proof-instruction-effect) (boymoo-model::a64-condition))))))

(defun division-gcd-immediate-inputs-p (a b world)
  (and (proof-immediate-integer-p a) (proof-immediate-integer-p b) (posp b)
       (equal (proof-world-reg 0 world) (proof-integer-word a))
       (equal (proof-world-reg 1 world) (proof-integer-word b))
       (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))))

(defthm division-gcd-immediate-setup-effects
  (implies (division-gcd-immediate-inputs-p a b world)
           (let ((after (division-instruction-sequence
                         *division-gcd-immediate-setup-instructions* world)))
             (and (equal (proof-world-reg 0 after) (abs a))
                  (equal (proof-world-reg 1 after) b)
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-world-pc after) (+ 20 (proof-world-pc world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance division-asr-decodes-immediate (value a))
                 (:instance division-asr-decodes-immediate (value b))
                 (:instance division-negated-signed-word (value a))
                 (:instance division-compare-zero-selects-negative (value a)))
           :in-theory (e/d (proof-world-reg proof-world-pc proof-world-stop)
                           (boymoo-model::a64-pc boymoo-model::a64-memory boymoo-model::a64-nzcv
                            boymoo-model::a64-set-nzcv boymoo-model::a64-condition
                            division-word-compare-zero-flags proof-integer-word division-asr-one-result))
           :cases ((< a 0))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-immediate-result-return-effects
  (implies (and (proof-immediate-integer-p value)
                (equal (proof-world-reg 0 world) (boymoo-model::a64-unsigned 64 value)))
           (let ((after (division-instruction-sequence *division-immediate-return-instructions* world)))
             (and (equal (proof-world-reg 0 after) (proof-integer-word value))
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance division-lsl-one-result-in-word (word (boymoo-model::a64-unsigned 64 value)))
                 (:instance division-a64-unsigned-bounded (width 64) (x value))
                 (:instance division-lsl-and-add-encode-immediate))
           :in-theory (e/d (proof-world-reg proof-world-pc proof-world-stop)
                           (boymoo-model::a64-pc boymoo-model::a64-memory division-lsl-one-result
                            division-a64-unsigned-bounded proof-integer-word))
           :do-not-induct t))
  :rule-classes nil)

(defconst *division-step-call-instructions*
  '((:logical-reg 1 64 0 31 21 0 0 nil)
    (:logical-reg 1 64 1 31 22 0 0 nil)
    (:logical-reg 1 64 2 31 19 0 0 nil)
    (:single 1 8 31 3 :offset 80)
    (:arithmetic-reg 0 64 4 19 20 0 1)
    (:branch 36 nil)))

(defthm division-step-call-instructions-are-emitted
  (let* ((items (division-linked-example-items))
         (entry (division-label-offset "rt:z-division-step" items))
         (target (division-label-offset "rt:z-divide" items))
         (image (boymoo-compiler::a64-bytes items))
         (machine (proof-load-cleared-string image 0
                                             (boymoo-model::a64-state nil 0 0 0 nil))))
    (and (equal (+ entry 56) target)
         (equal (division-decode-instructions 6 entry machine)
                *division-step-call-instructions*)))
  :rule-classes nil)

(local
 (defmacro division-prove-move-effect (name target source)
   `(defthm ,name
      (equal (proof-instruction-effect '(:logical-reg 1 64 ,target 31 ,source 0 0 nil) world)
             (let ((machine (proof-world-machine world)))
               (update-nth 0 (boymoo-model::a64-write-reg
                              ,target 64 nil (proof-reg ,source machine)
                              (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                           world)))
      :hints (("Goal" :in-theory (e/d (proof-instruction-effect) (acl2::binary-logior)))))))

(local (division-prove-move-effect division-step-move-left 0 21))
(local (division-prove-move-effect division-step-move-right 1 22))
(local (division-prove-move-effect division-step-move-quotient 2 19))

(local
 (defthm division-stack-pointer-is-address-base
   (equal (boymoo-model::a64-read-reg 31 64 t machine) (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))))

(local
 (defthm division-step-load-remainder
   (equal (proof-instruction-effect '(:single 1 8 31 3 :offset 80) world)
          (let* ((machine (proof-world-machine world))
                 (address (+ 80 (boymoo-model::a64-sp machine))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           3 64 nil (proof-load-word address machine)
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes))))))

(local
 (defthm division-step-add-scratch-offset
   (equal (proof-instruction-effect '(:arithmetic-reg 0 64 4 19 20 0 1) world)
          (let* ((machine (proof-world-machine world))
                 (offset (boymoo-model::a64-unsigned 64 (* 2 (proof-reg 20 machine))))
                 (sum (boymoo-model::a64-unsigned 64 (+ (proof-reg 19 machine) offset))))
            (update-nth 0 (boymoo-model::a64-write-reg
                           4 64 nil sum
                           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                        world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm division-step-branch-effect
   (implies (not (equal (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect '(:branch 36 nil) world)
                   (let ((machine (proof-world-machine world)))
                     (update-nth 0 (boymoo-model::a64-set-pc
                                    (+ 36 (boymoo-model::a64-pc machine)) machine)
                                 world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defun division-step-inputs-p (world)
  (let* ((machine (proof-world-machine world))
         (stride (proof-world-reg 20 world))
         (base (proof-world-reg 19 world)))
    (and (posp stride)
         (proof-span-p base (* 5 stride))
         (proof-span-p (+ 80 (boymoo-model::a64-sp machine)) 8)
         (unsigned-byte-p 64 (+ 56 (proof-world-pc world))))))

(defthm division-step-call-effects
  (implies (division-step-inputs-p world)
           (let* ((after (division-instruction-sequence *division-step-call-instructions* world))
                  (machine (proof-world-machine world)))
             (and (equal (proof-world-reg 0 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 2 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 3 after)
                         (boymoo-model::a64-unsigned
                          64 (proof-load-word (+ 80 (boymoo-model::a64-sp machine)) machine)))
                  (equal (proof-world-reg 4 after)
                         (+ (proof-world-reg 19 world) (* 2 (proof-world-reg 20 world))))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-world-pc after) (+ 56 (proof-world-pc world)))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :in-theory (e/d (proof-world-reg proof-world-pc)
                           (boymoo-model::a64-pc boymoo-model::a64-memory boymoo-model::a64-sp))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-step-reaches-divide
  (let* ((cuts (list (+ 56 (proof-world-pc world))))
         (machine (proof-world-machine world))
         (after (division-instruction-sequence *division-step-call-instructions* world)))
    (implies (and (division-step-inputs-p world)
                  (division-instruction-sequence-ready-p *division-step-call-instructions* cuts world))
             (and (proof-segment-p 6 cuts world :cut after)
                  (equal (proof-world-reg 0 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 2 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 3 after)
                         (boymoo-model::a64-unsigned
                          64 (proof-load-word (+ 80 (boymoo-model::a64-sp machine)) machine)))
                  (equal (proof-world-reg 4 after)
                         (+ (proof-world-reg 19 world) (* 2 (proof-world-reg 20 world))))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance division-step-call-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-step-call-instructions*)
                            (cuts (list (+ 56 (proof-world-pc world))))))
           :in-theory (disable proof-segment-p division-step-inputs-p
                               division-instruction-sequence division-instruction-sequence-ready-p)))
  :rule-classes nil)
