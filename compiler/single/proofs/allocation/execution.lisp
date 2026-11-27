(in-package "BOYMOO-PROOFS")

(include-book "bitfields")

(logic)
(set-verify-guards-eagerness 0)

; A path gives the decoded instruction at each visited address. Its
; premises check placement, memory permissions and absence of early cuts.
(defun allocation-path-ready-p (instructions cuts world)
  (if (atom instructions)
      (null instructions)
    (let ((instruction (car instructions)))
      (and (not (proof-world-stop world))
           (not (member-equal (proof-world-pc world) cuts))
           (proof-instruction-at-p instruction (proof-world-pc world) world)
           (proof-instruction-access-p instruction world)
           (allocation-path-ready-p
            (cdr instructions) cuts (proof-instruction-effect instruction world))))))

(defun allocation-path-end (instructions world)
  (if (atom instructions)
      world
    (allocation-path-end
     (cdr instructions) (proof-instruction-effect (car instructions) world))))

(defthm allocation-checked-path
  (implies (allocation-path-ready-p instructions cuts world)
           (equal (proof-run (len instructions) cuts world)
                  (proof-run 0 cuts (allocation-path-end instructions world))))
  :hints (("Goal" :induct (allocation-path-ready-p instructions cuts world)
           :in-theory (disable proof-step proof-instruction-at-p
                               proof-instruction-access-p proof-instruction-effect
                               proof-world-stop proof-world-pc))))

(defthm allocation-checked-cut
  (implies (and (allocation-path-ready-p instructions cuts world)
                (equal after (allocation-path-end instructions world))
                (not (proof-world-stop after))
                (member-equal (proof-world-pc after) cuts))
           (proof-segment-p (len instructions) cuts world :cut after))
  :hints (("Goal" :use allocation-checked-path
           :in-theory (disable allocation-path-ready-p allocation-path-end
                               allocation-checked-path proof-step
                               proof-world-stop proof-world-pc))))

(defun allocation-set-pc (pc world)
  (update-nth 0 (boymoo-model::a64-set-pc pc (proof-world-machine world)) world))

(defun allocation-next (world)
  (allocation-set-pc (+ 4 (proof-world-pc world)) world))

(defun allocation-write-reg (register value world)
  (update-nth 0 (boymoo-model::a64-write-reg register 64 nil value
                                            (proof-world-machine world))
              world))

(defun allocation-write-sp (value world)
  (update-nth 0 (boymoo-model::a64-write-reg 31 64 t value
                                            (proof-world-machine world))
              world))

(defun allocation-set-flags (flags world)
  (update-nth 0 (boymoo-model::a64-set-nzcv flags (proof-world-machine world)) world))

(defun allocation-sp (world)
  (boymoo-model::a64-sp (proof-world-machine world)))

(defun allocation-nzcv (world)
  (boymoo-model::a64-nzcv (proof-world-machine world)))

(defun allocation-memory (world)
  (boymoo-model::a64-memory (proof-world-machine world)))

(defun allocation-store-word (address word world)
  (update-nth 0 (boymoo-model::a64-store 8 address word (proof-world-machine world)) world))

(defun allocation-load-word (address world)
  (proof-load-word address (proof-world-machine world)))

(defun allocation-machine-state-p (world)
  (not (equal (car (proof-world-machine world)) :svc)))

(defthm allocation-word-register-range
  (and (unsigned-byte-p 64 (proof-world-reg register world))
       (unsigned-byte-p 64 (proof-world-pc world))
       (unsigned-byte-p 64 (allocation-sp world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm allocation-word-in-range
  (implies (and (integerp value) (<= 0 value) (< value *allocation-word-modulus*))
           (equal (boymoo-model::a64-unsigned 64 value) value))
  :hints (("Goal" :use allocation-unsigned-64-identity
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (boymoo-model::a64-unsigned)))))

(defthm allocation-world-field-of-machine
  (implies (posp field)
           (equal (nth field (update-nth 0 machine world))
                  (nth field world))))

(defthm allocation-machine-update-preserves-world
  (implies (posp field)
           (and (equal (nth field (allocation-set-pc pc world)) (nth field world))
                (equal (nth field (allocation-write-reg reg value world)) (nth field world))
                (equal (nth field (allocation-write-sp value world)) (nth field world))
                (equal (nth field (allocation-set-flags flags world)) (nth field world))
                (equal (nth field (allocation-store-word address word world)) (nth field world))))
  :hints (("Goal" :in-theory (disable nth update-nth boymoo-model::a64-set-pc
                                     boymoo-model::a64-write-reg boymoo-model::a64-set-nzcv
                                     boymoo-model::a64-store proof-world-machine))))

(defthm allocation-pc-of-machine-update
  (and (equal (proof-world-pc (allocation-set-pc pc world))
              (boymoo-model::a64-unsigned 64 pc))
       (equal (proof-world-pc (allocation-write-reg reg value world))
              (proof-world-pc world))
       (equal (proof-world-pc (allocation-write-sp value world))
              (proof-world-pc world))
       (equal (proof-world-pc (allocation-set-flags flags world))
              (proof-world-pc world))
       (equal (proof-world-pc (allocation-store-word address word world))
              (proof-world-pc world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                     boymoo-model::a64-write-bytes))))

(defthm allocation-sp-of-machine-update
  (and (equal (allocation-sp (allocation-set-pc pc world)) (allocation-sp world))
       (equal (allocation-sp (allocation-write-reg reg value world)) (allocation-sp world))
       (equal (allocation-sp (allocation-write-sp value world))
              (boymoo-model::a64-unsigned 64 value))
       (equal (allocation-sp (allocation-set-flags flags world)) (allocation-sp world))
       (equal (allocation-sp (allocation-store-word address word world)) (allocation-sp world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                     boymoo-model::a64-write-bytes))))

(defthm allocation-reg-of-machine-update
  (and (equal (proof-world-reg reg (allocation-set-pc pc world))
              (proof-world-reg reg world))
       (equal (proof-world-reg reg (allocation-write-sp value world))
              (proof-world-reg reg world))
       (equal (proof-world-reg reg (allocation-set-flags flags world))
              (proof-world-reg reg world))
       (equal (proof-world-reg reg (allocation-store-word address word world))
              (proof-world-reg reg world)))
  :hints (("Goal" :in-theory (disable nth update-nth boymoo-model::a64-unsigned
                                     boymoo-model::a64-write-bytes))))

(defthm allocation-assoc-of-update
  (equal (assoc-equal key (put-assoc-equal other value entries))
         (if (equal key other)
             (cons key value)
           (assoc-equal key entries)))
  :hints (("Goal" :induct (put-assoc-equal other value entries))))

(defthm allocation-reg-of-reg-update
  (equal (proof-world-reg reg (allocation-write-reg target value world))
         (if (and (equal reg target) (natp reg) (< reg 31))
             (boymoo-model::a64-unsigned 64 value)
           (proof-world-reg reg world)))
  :hints (("Goal" :in-theory (disable nth update-nth
                                     boymoo-model::a64-unsigned put-assoc-equal))))

(defthm allocation-memory-of-machine-update
  (and (equal (allocation-memory (allocation-set-pc pc world))
              (allocation-memory world))
       (equal (allocation-memory (allocation-write-reg reg value world))
              (allocation-memory world))
       (equal (allocation-memory (allocation-write-sp value world))
              (allocation-memory world))
       (equal (allocation-memory (allocation-set-flags flags world))
              (allocation-memory world))
       (equal (allocation-memory (allocation-store-word address word world))
              (boymoo-model::a64-write-bytes 8 address word (allocation-memory world))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                     boymoo-model::a64-write-bytes))))

(defthm allocation-load-of-machine-update
  (and (equal (allocation-load-word address (allocation-set-pc pc world))
              (allocation-load-word address world))
       (equal (allocation-load-word address (allocation-write-reg reg value world))
              (allocation-load-word address world))
       (equal (allocation-load-word address (allocation-write-sp value world))
              (allocation-load-word address world))
       (equal (allocation-load-word address (allocation-set-flags flags world))
              (allocation-load-word address world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes
                                     boymoo-model::a64-unsigned))))

(defthm allocation-nzcv-of-machine-update
  (and (equal (allocation-nzcv (allocation-set-pc pc world))
              (allocation-nzcv world))
       (equal (allocation-nzcv (allocation-write-reg reg value world))
              (allocation-nzcv world))
       (equal (allocation-nzcv (allocation-write-sp value world))
              (allocation-nzcv world))
       (equal (allocation-nzcv (allocation-store-word address word world))
              (allocation-nzcv world))
       (equal (allocation-nzcv (allocation-set-flags flags world))
              (boymoo-model::a64-unsigned 4 flags)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                     boymoo-model::a64-write-bytes))))

(in-theory (disable allocation-set-pc allocation-write-reg allocation-write-sp
                    allocation-set-flags allocation-store-word allocation-load-word
                    allocation-sp allocation-nzcv allocation-memory
                    proof-world-pc proof-world-reg proof-world-machine
                    proof-instruction-effect proof-decode-at
                    boymoo-model::a64-unsigned))

(local (include-book "ihs/logops-lemmas" :dir :system))

(defthm allocation-load-word-range
  (unsigned-byte-p 64 (allocation-load-word address world))
  :hints (("Goal" :in-theory (e/d (allocation-load-word)
                                (boymoo-model::a64-read-bytes))))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm allocation-read-register
   (equal (boymoo-model::a64-read-reg reg 64 nil (proof-world-machine world))
          (proof-world-reg reg world))
   :hints (("Goal" :in-theory (enable proof-world-reg)))))

(local
 (defthm allocation-read-register-or-sp
   (equal (boymoo-model::a64-read-reg reg 64 t (proof-world-machine world))
          (if (equal reg 31) (allocation-sp world) (proof-world-reg reg world)))
   :hints (("Goal" :in-theory (e/d (proof-world-reg allocation-sp)
                                   (allocation-read-register))))))

(defthm allocation-register-31-is-zero
  (equal (proof-world-reg 31 world) 0)
  :hints (("Goal" :in-theory (e/d (proof-world-reg)
                                 (allocation-read-register)))))

(defthm allocation-write-zero-register
  (implies (consp world)
           (equal (allocation-write-reg 31 value world) world))
  :hints (("Goal" :in-theory (enable allocation-write-reg proof-world-machine))))

(local
 (defthm allocation-machine-of-machine-update
   (equal (proof-world-machine (update-nth 0 machine world)) machine)
   :hints (("Goal" :in-theory (enable proof-world-machine)))))

(local
 (defthm allocation-machine-of-world-cons
   (equal (proof-world-machine (cons machine rest)) machine)
   :hints (("Goal" :in-theory (enable proof-world-machine)))))

(local
 (defthm allocation-update-machine-twice
   (equal (update-nth 0 last (update-nth 0 first world))
          (update-nth 0 last world))))

(local
 (defthm allocation-car-of-update-nth
   (equal (car (update-nth index value entries))
          (if (zp index) value (car entries)))
   :hints (("Goal" :expand ((update-nth index value entries))))))

(local
 (defthm allocation-assoc-update-is-cons
   (consp (put-assoc-equal key value entries))
   :rule-classes :type-prescription
   :hints (("Goal" :expand ((put-assoc-equal key value entries))))))

(local
 (defthm allocation-update-does-not-produce-svc
   (implies (not (equal (car machine) :svc))
            (and (not (equal (car (boymoo-model::a64-set-pc pc machine)) :svc))
                 (not (equal (car (boymoo-model::a64-set-nzcv flags machine)) :svc))
                 (not (equal (car (boymoo-model::a64-write-reg reg 64 use-sp word machine))
                             :svc))
                 (not (equal (car (boymoo-model::a64-store count address word machine))
                             :svc))))
   :hints (("Goal" :in-theory (disable put-assoc-equal boymoo-model::a64-write-bytes)))))

(local
 (defthm allocation-machine-update-projections
   (and (equal (car (boymoo-model::a64-set-pc pc machine)) (car machine))
        (equal (car (boymoo-model::a64-set-nzcv flags machine)) (car machine))
        (equal (car (boymoo-model::a64-store count address word machine)) (car machine)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-write-bytes)))))

(local
 (defthm allocation-cons-machine-after-register-write
   (implies (consp machine)
            (consp (boymoo-model::a64-write-reg reg 64 use-sp word machine)))))

(defthm allocation-state-of-machine-update
  (implies (allocation-machine-state-p world)
           (and (allocation-machine-state-p (allocation-set-pc pc world))
                (allocation-machine-state-p (allocation-write-reg reg value world))
                (allocation-machine-state-p (allocation-write-sp value world))
                (allocation-machine-state-p (allocation-set-flags flags world))
                (allocation-machine-state-p (allocation-store-word address word world))))
  :hints (("Goal" :in-theory (e/d (allocation-set-pc allocation-write-reg
                                   allocation-write-sp allocation-set-flags
                                   allocation-store-word)
                                  (boymoo-model::a64-set-pc boymoo-model::a64-write-reg
                                   boymoo-model::a64-set-nzcv boymoo-model::a64-store)))))

(local
 (defthm allocation-read-after-pc-change
   (equal (boymoo-model::a64-read-reg reg 64 sp
                                      (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-read-reg reg 64 sp machine))))

(local
 (defthm allocation-load-after-pc-change
   (equal (boymoo-model::a64-load n address (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-load n address machine))))

(local
 (defthm allocation-flags-after-pc-change
   (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-nzcv machine))))

(local
 (defthm allocation-write-register-without-sp
   (implies (not (equal reg 31))
            (equal (boymoo-model::a64-write-reg reg 64 t word machine)
                   (boymoo-model::a64-write-reg reg 64 nil word machine)))))

(local
 (defthm allocation-pc-from-machine-update
   (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc address machine))
          (boymoo-model::a64-unsigned 64 address))
   :hints (("Goal" :in-theory (disable nth update-nth)))))

; Each equation below is an instance of the decoded instruction semantics.
(local
 (defmacro allocation-effect-theory ()
   '(e/d (proof-instruction-effect proof-world-pc allocation-machine-state-p
          allocation-set-pc allocation-write-reg allocation-write-sp
          allocation-set-flags allocation-load-word allocation-store-word
          allocation-nzcv allocation-sp allocation-next)
         (nth update-nth proof-linux-svc
          boymoo-model::a64-exec-arithmetic boymoo-model::a64-read-reg
          boymoo-model::a64-write-reg boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
          boymoo-model::a64-nzcv boymoo-model::a64-pc boymoo-model::a64-sp
          boymoo-model::a64-load boymoo-model::a64-store
          boymoo-model::a64-condition boymoo-model::a64-shift
          boymoo-model::a64-unsigned allocation-flags
          allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-arithmetic-reg-effect
  (implies (and (allocation-machine-state-p world)
                (member-equal opcode '(0 1 2 3))
                (member-equal shift '(0 1)))
           (equal (proof-instruction-effect
                   (list :arithmetic-reg opcode 64 rd rn rm 0 shift) world)
                  (let* ((left (proof-world-reg rn world))
                         (right (if (equal shift 0)
                                    (proof-world-reg rm world)
                                  (boymoo-model::a64-unsigned
                                   64 (+ (proof-world-reg rm world)
                                         (proof-world-reg rm world)))))
                         (subtract (or (equal opcode 2) (equal opcode 3)))
                         (answer (if subtract (- left right) (+ left right)))
                         (updated (allocation-write-reg rd answer (allocation-next world))))
                    (if (or (equal opcode 1) (equal opcode 3))
                        (allocation-set-flags (allocation-flags subtract left right) updated)
                      updated))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-arithmetic-imm-effect
  (implies (and (allocation-machine-state-p world)
                (member-equal opcode '(0 1 2 3))
                (unsigned-byte-p 64 right))
           (equal (proof-instruction-effect
                   (list :arithmetic-imm opcode 64 rd rn right) world)
                  (let* ((left (if (equal rn 31) (allocation-sp world)
                                 (proof-world-reg rn world)))
                         (subtract (or (equal opcode 2) (equal opcode 3)))
                         (set-flags (or (equal opcode 1) (equal opcode 3)))
                         (answer (if subtract (- left right) (+ left right)))
                         (next (allocation-next world))
                         (updated (if (and (equal rd 31) (not set-flags))
                                      (allocation-write-sp answer next)
                                    (allocation-write-reg rd answer next))))
                    (if set-flags
                        (allocation-set-flags (allocation-flags subtract left right) updated)
                      updated))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-mov-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect
                   (list :logical-reg 1 64 rd 31 rm 0 0 nil) world)
                  (allocation-write-reg rd (proof-world-reg rm world) (allocation-next world))))
  :hints (("Goal"
           :in-theory (union-theories (allocation-effect-theory)
                                      '(boymoo-model::a64-exec-logical
                                        allocation-register-31-is-zero)))))

(defthm allocation-movz-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect
                   (list :move-wide 2 64 rd value position) world)
                  (allocation-write-reg rd (ash value position) (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-movn-zero-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :move-wide 0 64 rd 0 0) world)
                  (allocation-write-reg rd -1 (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defmacro allocation-shift-effect (name operation shift)
   (let* ((left (eq operation :left))
          (rotate (if left (- 64 shift) shift))
          (last (if left (- 63 shift) 63))
          (write-mask (if left (- (expt 2 64) (expt 2 shift)) #xffffffffffffffff))
          (test-mask (if left #xffffffffffffffff (1- (expt 2 (- 64 shift)))))
          (effect (if left 'allocation-exec-left-shift 'allocation-exec-right-shift)))
     `(defthm ,name
        (implies (allocation-machine-state-p world)
                 (equal (proof-instruction-effect
                         (list :bitfield 2 64 rd rn ,rotate ,last ,write-mask ,test-mask) world)
                        (allocation-write-reg rd (ash (proof-world-reg rn world) ,(if left shift (- shift)))
                                              (allocation-next world))))
        :hints (("Goal"
                 :use ((:instance ,effect (shift ,shift)
                        (machine (boymoo-model::a64-set-pc
                                  (+ 4 (proof-world-pc world)) (proof-world-machine world)))))
                 :in-theory (set-difference-theories
                             (allocation-effect-theory)
                             '(boymoo-model::a64-exec-bitfield ,effect)))))))

(allocation-shift-effect allocation-lsr-16-effect :right 16)
(allocation-shift-effect allocation-lsr-32-effect :right 32)
(allocation-shift-effect allocation-lsl-1-effect :left 1)
(allocation-shift-effect allocation-lsl-8-effect :left 8)
(allocation-shift-effect allocation-lsl-16-effect :left 16)

(defthm allocation-svc-effect
  (equal (proof-instruction-effect (list :svc immediate) world)
         (proof-linux-svc (list :svc immediate (proof-world-reg 16 world)
                                (proof-world-reg 8 world)) world))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-svc-return-effect
  (equal (proof-svc-return reply world)
         (update-nth 6 (cdr (proof-world-replies world))
                     (allocation-write-reg 0 reply (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-branch-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :branch displacement link) world)
                  (allocation-set-pc
                   (+ (proof-world-pc world) displacement)
                   (if link (allocation-write-reg 30 (+ 4 (proof-world-pc world))
                                                  (allocation-next world))
                     (allocation-next world)))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-conditional-branch-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :branch-cond displacement condition) world)
                  (if (boymoo-model::a64-condition condition (allocation-nzcv world))
                      (allocation-set-pc (+ (proof-world-pc world) displacement)
                                         (allocation-next world))
                    (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-zero-branch-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :branch-zero displacement 64 reg nonzero) world)
                  (if (iff nonzero (not (equal (proof-world-reg reg world) 0)))
                      (allocation-set-pc (+ (proof-world-pc world) displacement)
                                         (allocation-next world))
                    (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-return-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect '(:branch-reg 30 nil) world)
                  (allocation-set-pc (proof-world-reg 30 world) (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-select-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :select 64 rd first second condition nil) world)
                  (allocation-write-reg
                   rd (if (boymoo-model::a64-condition condition (allocation-nzcv world))
                          (proof-world-reg first world)
                        (proof-world-reg second world))
                   (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-load-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :single 1 8 rn rt :offset delta) world)
                  (allocation-write-reg
                   rt (allocation-load-word
                       (+ (if (equal rn 31) (allocation-sp world) (proof-world-reg rn world)) delta)
                       world)
                   (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-store-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :single 0 8 rn rt :offset delta) world)
                  (allocation-store-word
                   (+ (if (equal rn 31) (allocation-sp world) (proof-world-reg rn world)) delta)
                   (proof-world-reg rt world)
                   (allocation-next world))))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defun allocation-pair-effect (load rn rt rt2 mode delta world)
  (let* ((base (if (equal rn 31) (allocation-sp world) (proof-world-reg rn world)))
         (updated (+ base delta))
         (first (if (eq mode :post) base updated))
         (second (+ first 8))
         (next (allocation-next world))
         (next (if load
                   (allocation-write-reg
                    rt2 (allocation-load-word second world)
                    (allocation-write-reg rt (allocation-load-word first world) next))
                 (allocation-store-word
                  second (proof-world-reg rt2 world)
                  (allocation-store-word first (proof-world-reg rt world) next)))))
    (if (member-eq mode '(:pre :post))
        (if (equal rn 31) (allocation-write-sp updated next)
          (allocation-write-reg rn updated next))
      next)))

(defthm allocation-pair-instruction-effect
  (implies (allocation-machine-state-p world)
           (equal (proof-instruction-effect (list :pair load rn rt rt2 mode delta) world)
                  (allocation-pair-effect load rn rt rt2 mode delta world)))
  :hints (("Goal" :in-theory (allocation-effect-theory))))

(defthm allocation-runtime-word-as-load
  (equal (proof-runtime-word offset world)
         (allocation-load-word (+ -128 offset (proof-heap-base world)) world))
  :hints (("Goal" :in-theory (enable allocation-load-word))))

(defthm allocation-read-sp-as-sp
  (equal (boymoo-model::a64-sp (proof-world-machine world))
         (allocation-sp world))
  :hints (("Goal" :in-theory (enable allocation-sp))))

(defthm allocation-read-memory-as-memory
  (equal (boymoo-model::a64-memory (proof-world-machine world))
         (allocation-memory world))
  :hints (("Goal" :in-theory (enable allocation-memory))))

(defthm allocation-world-register-natural
  (natp (proof-world-reg register world))
  :hints (("Goal" :in-theory (e/d (proof-world-reg) (allocation-read-register))))
  :rule-classes :type-prescription)

(defthm allocation-world-register-upper-bound
  (< (proof-world-reg register world) *allocation-word-modulus*)
  :hints (("Goal" :in-theory (e/d (proof-world-reg) (allocation-read-register))))
  :rule-classes :linear)

(defthm allocation-load-word-natural
  (natp (allocation-load-word address world))
  :hints (("Goal" :use allocation-load-word-range
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (allocation-load-word-range))))
  :rule-classes :type-prescription)

(defthm allocation-load-word-upper-bound
  (< (allocation-load-word address world) *allocation-word-modulus*)
  :hints (("Goal" :use allocation-load-word-range
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (allocation-load-word-range))))
  :rule-classes :linear)

(defthm allocation-register-frame-of-zero-write
  (equal (proof-register-frame-p register clobbers before
                                 (allocation-write-reg 31 value world))
         (proof-register-frame-p register clobbers before world))
  :hints (("Goal" :induct (proof-register-frame-p register clobbers before world))))

(defmacro allocation-preserved-world-slot (theorem accessor)
  `(defthm ,theorem
     (and (equal (,accessor (allocation-set-pc pc world)) (,accessor world))
          (equal (,accessor (allocation-write-reg reg value world)) (,accessor world))
          (equal (,accessor (allocation-write-sp value world)) (,accessor world))
          (equal (,accessor (allocation-set-flags flags world)) (,accessor world))
          (equal (,accessor (allocation-store-word address word world)) (,accessor world)))
     :hints (("Goal" :in-theory (disable nth)))))

(allocation-preserved-world-slot allocation-stop-of-machine-update proof-world-stop)
(allocation-preserved-world-slot allocation-mappings-of-machine-update proof-world-regions)
(allocation-preserved-world-slot allocation-page-of-machine-update proof-world-page-size)
(allocation-preserved-world-slot allocation-input-of-machine-update proof-world-input)
(allocation-preserved-world-slot allocation-stdout-of-machine-update proof-world-stdout)
(allocation-preserved-world-slot allocation-stderr-of-machine-update proof-world-stderr)
(allocation-preserved-world-slot allocation-replies-of-machine-update proof-world-replies)

(defthm allocation-register-frame-reflexive
  (proof-register-frame-p register clobbers world world))

(defthm allocation-register-frame-of-machine-update
  (and (equal (proof-register-frame-p register clobbers before
                                     (allocation-set-pc pc world))
              (proof-register-frame-p register clobbers before world))
       (equal (proof-register-frame-p register clobbers before
                                     (allocation-set-flags flags world))
              (proof-register-frame-p register clobbers before world))
       (equal (proof-register-frame-p register clobbers before
                                     (allocation-store-word address word world))
              (proof-register-frame-p register clobbers before world))
       (equal (proof-register-frame-p register clobbers before
                                     (allocation-write-sp value world))
              (proof-register-frame-p register clobbers before world)))
  :hints (("Goal" :induct (proof-register-frame-p register clobbers before world))))

(defthm allocation-register-frame-of-clobber
  (implies (member-equal target clobbers)
           (equal (proof-register-frame-p register clobbers before
                                          (allocation-write-reg target value world))
                  (proof-register-frame-p register clobbers before world)))
  :hints (("Goal" :induct (proof-register-frame-p register clobbers before world)
           :expand ((proof-register-frame-p register clobbers before world)
                    (proof-register-frame-p register clobbers before
                                            (allocation-write-reg target value world))))))

(in-theory (disable allocation-flags proof-instruction-at-p proof-instruction-access-p
                    allocation-machine-state-p proof-step proof-load-word proof-register-frame-p
                    proof-world-stop proof-world-regions proof-world-page-size
                    proof-world-input proof-world-stdout proof-world-stderr proof-world-replies
                    boymoo-model::a64-condition boymoo-model::a64-read-bytes
                    boymoo-model::a64-write-bytes))
