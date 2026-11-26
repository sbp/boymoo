(in-package "BOYMOO-PROOFS")

(include-book "words")
(local (include-book "std/lists/update-nth" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

; A non-trapping instruction keeps the register file distinct from the
; system-call event returned by the instruction model.
(defun collection-cpu-p (world)
  (alistp (boymoo-model::a64-registers (proof-world-machine world))))

(defun collection-next-instruction (world)
  (collection-write-pc (+ 4 (proof-world-pc world)) world))

(local
 (in-theory (disable proof-linux-svc
                     boymoo-model::a64-unsigned boymoo-model::a64-load
                     boymoo-model::a64-store
                     (:definition ash) (:definition acl2::binary-logior)
                     (:definition acl2::binary-logand) (:definition acl2::binary-logxor)
                     acl2::update-nth-when-zp acl2::update-nth-of-cons
                     acl2::update-nth-when-atom
                     nth update-nth)))

(local
 (defthm collection-lookup-updated-register
   (implies (alistp registers)
            (equal (assoc-equal query (put-assoc-equal register value registers))
                   (if (equal query register)
                       (cons register value)
                     (assoc-equal query registers))))))

(local
 (defthm collection-register-assignment-preserves-alist
   (implies (alistp registers)
            (alistp (put-assoc-equal register value registers)))))

(defthm collection-register-after-assignment
  (implies (collection-cpu-p world)
           (equal (proof-world-reg query (collection-write-register register value world))
                  (if (and (natp register) (< register 31) (equal query register))
                      (boymoo-model::a64-unsigned 64 value)
                    (proof-world-reg query world)))))

(defthm collection-register-after-pc-change
  (equal (proof-world-reg query (collection-write-pc address world))
         (proof-world-reg query world)))

(defthm collection-register-after-word-store
  (equal (proof-world-reg query (collection-write-word address value world))
         (proof-world-reg query world))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm collection-pc-after-assignment
  (equal (proof-world-pc (collection-write-register register value world))
         (proof-world-pc world)))

(defthm collection-pc-after-word-store
  (equal (proof-world-pc (collection-write-word address value world))
         (proof-world-pc world))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm collection-pc-after-pc-change
  (equal (proof-world-pc (collection-write-pc address world))
         (boymoo-model::a64-unsigned 64 address)))

(defthm collection-cpu-after-assignment
  (implies (collection-cpu-p world)
           (collection-cpu-p (collection-write-register register value world))))

(defthm collection-cpu-after-pc-change
  (equal (collection-cpu-p (collection-write-pc address world))
         (collection-cpu-p world)))

(defthm collection-cpu-after-word-store
  (equal (collection-cpu-p (collection-write-word address value world))
         (collection-cpu-p world))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm collection-world-register-is-word
  (unsigned-byte-p 64 (proof-world-reg register world)))

(defthm collection-read-zero-register
  (equal (proof-world-reg 31 world) 0))

(defthm collection-world-register-is-natural
  (natp (proof-world-reg register world))
  :rule-classes :type-prescription)

(defthm collection-world-register-bounds
  (and (<= 0 (proof-world-reg register world))
       (< (proof-world-reg register world) (expt 2 64)))
  :rule-classes :linear)

(defthm collection-world-pc-is-word
  (unsigned-byte-p 64 (proof-world-pc world)))

(defthm collection-world-pc-is-natural
  (natp (proof-world-pc world))
  :rule-classes :type-prescription)

(defthm collection-world-pc-bounds
  (and (<= 0 (proof-world-pc world)) (< (proof-world-pc world) (expt 2 64)))
  :rule-classes :linear)

(defthm collection-pc-change-folds-wrapped-addend
  (implies (and (integerp left) (integerp right))
           (equal (collection-write-pc (+ left (boymoo-model::a64-unsigned 64 right)) world)
                  (collection-write-pc (+ left right) world))))

(local
 (defthm collection-first-after-store
   (equal (car (boymoo-model::a64-store count address value machine)) (car machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store)))))

(local
 (defthm collection-alist-register-file-is-not-svc
   (implies (alistp (nth 0 machine))
            (not (equal (car machine) :svc)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm collection-set-pc-twice
  (equal (collection-write-pc second (collection-write-pc first world))
         (collection-write-pc second world)))

(defthm collection-pc-over-register
  (equal (collection-write-register register value (collection-write-pc address world))
         (collection-write-pc address (collection-write-register register value world))))

(defthm collection-pc-over-word-store
  (equal (collection-write-word address value (collection-write-pc pc world))
         (collection-write-pc pc (collection-write-word address value world)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm collection-word-after-pc-change
  (equal (collection-read-word address (collection-write-pc pc world))
         (collection-read-word address world))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-word-after-assignment
  (equal (collection-read-word address (collection-write-register register value world))
         (collection-read-word address world))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-word-after-flags-change
  (equal (collection-read-word address (collection-write-flags flags world))
         (collection-read-word address world))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-effect-return
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect '(:branch-reg 30 nil) world)
                  (collection-write-pc (proof-world-reg 30 world) world))))

(defthm collection-effect-and-immediate
  (implies (and (collection-cpu-p world) (natp target) (< target 31))
           (equal (proof-instruction-effect
                   (list :logical-imm 0 64 target source mask) world)
                  (collection-write-register target
                                             (logand (proof-world-reg source world) mask)
                                             (collection-next-instruction world)))))

(defthm collection-effect-move-register
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :logical-reg 1 64 target 31 source 0 0 nil) world)
                  (collection-write-register target (proof-world-reg source world)
                                             (collection-next-instruction world)))))

(defthm collection-effect-move-wide-zero
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :move-wide 2 64 target bits shift) world)
                  (collection-write-register target (ash bits shift)
                                             (collection-next-instruction world)))))

(defthm collection-effect-add-immediate
  (implies (and (collection-cpu-p world) (natp target) (< target 31)
                (not (equal source 31)))
           (equal (proof-instruction-effect
                   (list :arithmetic-imm 0 64 target source number) world)
                  (collection-write-register target (+ (proof-world-reg source world) number)
                                             (collection-next-instruction world)))))

(defthm collection-effect-subtract-immediate
  (implies (and (collection-cpu-p world) (natp target) (< target 31)
                (not (equal source 31)) (unsigned-byte-p 64 number))
           (equal (proof-instruction-effect
                   (list :arithmetic-imm 2 64 target source number) world)
                  (collection-write-register
                   target (- (proof-world-reg source world) number)
                   (collection-next-instruction world)))))

(defthm collection-effect-add-register
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :arithmetic-reg 0 64 target left right 0 0) world)
                  (collection-write-register
                   target (+ (proof-world-reg left world) (proof-world-reg right world))
                   (collection-next-instruction world)))))

(defthm collection-effect-subtract-register
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :arithmetic-reg 2 64 target left right 0 0) world)
                  (collection-write-register
                   target (- (proof-world-reg left world) (proof-world-reg right world))
                   (collection-next-instruction world)))))

(defthm collection-effect-load-word
  (implies (and (collection-cpu-p world) (not (equal base 31)))
           (equal (proof-instruction-effect (list :single 1 8 base target :offset delta)
                                            world)
                  (collection-write-register
                   target (collection-read-word (+ (proof-world-reg base world) delta) world)
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-effect-store-word
  (implies (and (collection-cpu-p world) (not (equal base 31)))
           (equal (proof-instruction-effect (list :single 0 8 base source :offset delta)
                                            world)
                  (collection-write-word (+ (proof-world-reg base world) delta)
                                         (proof-world-reg source world)
                                         (collection-next-instruction world)))))

(defthm collection-effect-store-pair
  (implies (and (collection-cpu-p world) (not (equal base 31)))
           (equal (proof-instruction-effect
                   (list :pair nil base first second :offset delta) world)
                  (let ((address (+ (proof-world-reg base world) delta)))
                    (collection-write-word
                     (+ address 8) (proof-world-reg second world)
                     (collection-write-word address (proof-world-reg first world)
                                            (collection-next-instruction world)))))))

(defthm collection-effect-load-pair
  (implies (and (collection-cpu-p world) (not (equal base 31)))
           (equal (proof-instruction-effect
                   (list :pair t base first second :offset delta) world)
                  (let ((address (+ (proof-world-reg base world) delta)))
                    (collection-write-register
                     second (collection-read-word (+ address 8) world)
                     (collection-write-register first (collection-read-word address world)
                                                (collection-next-instruction world))))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-effect-branch
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :branch offset nil) world)
                  (collection-write-pc (+ (proof-world-pc world) offset) world))))

(defthm collection-effect-branch-zero
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :branch-zero offset 64 register nonzero) world)
                  (collection-write-pc
                   (+ (proof-world-pc world)
                      (if (if nonzero (not (equal (proof-world-reg register world) 0))
                              (equal (proof-world-reg register world) 0))
                          offset 4))
                   world))))

(defthm collection-effect-conditional-branch
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :branch-cond offset condition) world)
                  (collection-write-pc
                   (+ (proof-world-pc world)
                      (if (boymoo-model::a64-condition
                           condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                          offset 4))
                   world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-condition))))

(defun collection-subtract-flags (left right)
  (let* ((sum (+ #x10000000000000000 (- right) left))
         (result (boymoo-model::a64-unsigned 64 (- left right)))
         (signed (- (boymoo-model::a64-signed 64 left)
                    (boymoo-model::a64-signed 64 right))))
    (boymoo-model::a64-result-flags
     64 result (logbitp 64 sum)
     (not (equal signed (boymoo-model::a64-signed 64 result))))))

(defthm collection-effect-subtract-immediate-with-flags
  (implies (and (collection-cpu-p world)
                (not (equal source 31)) (unsigned-byte-p 64 number))
           (equal (proof-instruction-effect
                   (list :arithmetic-imm 3 64 target source number) world)
                  (collection-write-flags
                   (collection-subtract-flags (proof-world-reg source world) number)
                   (collection-write-register
                    target (- (proof-world-reg source world) number)
                    (collection-next-instruction world)))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-result-flags
                                      boymoo-model::a64-signed
                                      (:definition logbitp)))))

(defthm collection-effect-compare-register
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :arithmetic-reg 3 64 31 left right 0 0) world)
                  (collection-write-flags
                   (collection-subtract-flags
                    (proof-world-reg left world) (proof-world-reg right world))
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-result-flags
                                      boymoo-model::a64-signed
                                      (:definition logbitp)))))

(defthm collection-write-to-zero-after-setting-pc
  (equal (collection-write-register 31 value (collection-write-pc pc world))
         (collection-write-pc pc world)))

(defthm collection-cpu-after-flags-change
  (equal (collection-cpu-p (collection-write-flags flags world))
         (collection-cpu-p world)))

(defthm collection-register-after-flags-change
  (equal (proof-world-reg query (collection-write-flags flags world))
         (proof-world-reg query world)))

(defthm collection-pc-after-flags-change
  (equal (proof-world-pc (collection-write-flags flags world))
         (proof-world-pc world)))

(defthm collection-pc-over-flags
  (equal (collection-write-flags flags (collection-write-pc pc world))
         (collection-write-pc pc (collection-write-flags flags world))))

(defthm collection-flags-after-pc-change
  (equal (boymoo-model::a64-nzcv (proof-world-machine (collection-write-pc pc world)))
         (boymoo-model::a64-nzcv (proof-world-machine world))))

(defthm collection-flags-after-flags-change
  (equal (boymoo-model::a64-nzcv (proof-world-machine (collection-write-flags flags world)))
         (boymoo-model::a64-unsigned 4 flags)))

(defthm collection-memory-after-assignment
  (equal (boymoo-model::a64-memory
          (proof-world-machine (collection-write-register register value world)))
         (boymoo-model::a64-memory (proof-world-machine world))))

(defthm collection-memory-after-pc-change
  (equal (boymoo-model::a64-memory (proof-world-machine (collection-write-pc pc world)))
         (boymoo-model::a64-memory (proof-world-machine world))))

(defthm collection-memory-after-flags-change
  (equal (boymoo-model::a64-memory (proof-world-machine (collection-write-flags flags world)))
         (boymoo-model::a64-memory (proof-world-machine world))))

(defthm collection-memory-after-word-store
  (equal (boymoo-model::a64-memory
          (proof-world-machine (collection-write-word address value world)))
         (boymoo-model::a64-write-bytes
          8 address value (boymoo-model::a64-memory (proof-world-machine world))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-store)
                                  (boymoo-model::a64-write-bytes)))))

(defthm collection-effect-or-registers
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :logical-reg 1 64 target left right 0 0 nil) world)
                  (collection-write-register
                   target (logior (proof-world-reg left world) (proof-world-reg right world))
                   (collection-next-instruction world)))))

(defmacro collection-define-lsr-effect (name shift mask)
  `(defthm ,name
     (implies (collection-cpu-p world)
              (equal (proof-instruction-effect
                      (list :bitfield 2 64 target source ,shift 63 #xffffffffffffffff ,mask)
                      world)
                     (collection-write-register
                      target (ash (proof-world-reg source world) ,(- shift))
                      (collection-next-instruction world))))
     :hints (("Goal" :in-theory (disable boymoo-model::a64-ror)))))

(collection-define-lsr-effect collection-effect-lsr-3 3 #x1fffffffffffffff)
(collection-define-lsr-effect collection-effect-lsr-8 8 #x00ffffffffffffff)
(collection-define-lsr-effect collection-effect-lsr-16 16 #x0000ffffffffffff)

(defthm collection-effect-branch-with-link
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :branch offset t) world)
                  (collection-write-pc
                   (+ (proof-world-pc world) offset)
                   (collection-write-register 30 (+ (proof-world-pc world) 4) world)))))

(defthm collection-effect-conditional-select
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :select 64 target first second condition nil)
                                            world)
                  (collection-write-register
                   target
                   (if (boymoo-model::a64-condition
                        condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                       (proof-world-reg first world)
                     (proof-world-reg second world))
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-condition))))

(defthm collection-effect-load-stack-word
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :single 1 8 31 target :offset delta)
                                            world)
                  (collection-write-register
                   target (collection-read-word
                           (+ (boymoo-model::a64-sp (proof-world-machine world)) delta) world)
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-sp-after-register-change
  (equal (boymoo-model::a64-sp (proof-world-machine (collection-write-register r v world)))
         (boymoo-model::a64-sp (proof-world-machine world))))

(defthm collection-sp-after-pc-change
  (equal (boymoo-model::a64-sp (proof-world-machine (collection-write-pc pc world)))
         (boymoo-model::a64-sp (proof-world-machine world))))

(defthm collection-sp-after-flags-change
  (equal (boymoo-model::a64-sp (proof-world-machine (collection-write-flags flags world)))
         (boymoo-model::a64-sp (proof-world-machine world))))

(defthm collection-sp-after-word-store
  (equal (boymoo-model::a64-sp (proof-world-machine (collection-write-word addr value world)))
         (boymoo-model::a64-sp (proof-world-machine world)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm collection-effect-lsl-one
  (implies (and (collection-cpu-p world)
                (unsigned-byte-p 63 (proof-world-reg source world)))
           (equal (proof-instruction-effect
                   (list :bitfield 2 64 target source 63 62
                         #xfffffffffffffffe #xffffffffffffffff)
                   world)
                  (collection-write-register
                   target (* 2 (proof-world-reg source world))
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-ror))))

(defthm collection-effect-add-with-shifted-register
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :arithmetic-reg 0 64 target left right 0 shift) world)
                  (collection-write-register
                   target
                   (+ (proof-world-reg left world)
                      (boymoo-model::a64-unsigned 64 (ash (proof-world-reg right world) shift)))
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (disable collection-word-of-wrapped-addend))))

(defun collection-write-sp (address world)
  (update-nth 0
              (boymoo-model::a64-write-reg 31 64 t address (proof-world-machine world))
              world))

(defthm collection-sp-is-natural
  (natp (boymoo-model::a64-sp machine))
  :rule-classes :type-prescription)

(defthm collection-sp-bounds
  (and (<= 0 (boymoo-model::a64-sp machine))
       (< (boymoo-model::a64-sp machine) (expt 2 64)))
  :rule-classes :linear)

(defthm collection-sp-after-sp-change
  (equal (boymoo-model::a64-sp (proof-world-machine (collection-write-sp address world)))
         (boymoo-model::a64-unsigned 64 address)))

(defthm collection-pc-after-sp-change
  (equal (proof-world-pc (collection-write-sp address world))
         (proof-world-pc world)))

(defthm collection-register-after-sp-change
  (equal (proof-world-reg register (collection-write-sp address world))
         (proof-world-reg register world)))

(defthm collection-cpu-after-sp-change
  (equal (collection-cpu-p (collection-write-sp address world))
         (collection-cpu-p world)))

(defthm collection-memory-after-sp-change
  (equal (boymoo-model::a64-memory (proof-world-machine (collection-write-sp address world)))
         (boymoo-model::a64-memory (proof-world-machine world))))

(defthm collection-word-after-sp-change
  (equal (collection-read-word address (collection-write-sp sp world))
         (collection-read-word address world))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-effect-push-register-pair
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :pair nil 31 first second :pre delta) world)
                  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
                         (address (+ sp delta))
                         (next (collection-next-instruction world))
                         (next (collection-write-word address (proof-world-reg first world) next))
                         (next (collection-write-word (+ address 8)
                                                      (proof-world-reg second world) next)))
                    (collection-write-sp address next)))))

(defthm collection-effect-pop-register-pair
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect (list :pair t 31 first second :post delta) world)
                  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
                         (next (collection-next-instruction world))
                         (next (collection-write-register
                                first (collection-read-word sp world) next))
                         (next (collection-write-register
                                second (collection-read-word (+ sp 8) world) next)))
                    (collection-write-sp (+ sp delta) next))))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-effect-lsl-sixteen
  (implies (and (collection-cpu-p world)
                (unsigned-byte-p 48 (proof-world-reg source world)))
           (equal (proof-instruction-effect
                   (list :bitfield 2 64 target source 48 47
                         #xffffffffffff0000 #xffffffffffffffff)
                   world)
                  (collection-write-register
                   target (ash (proof-world-reg source world) 16)
                   (collection-next-instruction world))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-ror))))

(defthm collection-effect-subtract-register-with-flags
  (implies (collection-cpu-p world)
           (equal (proof-instruction-effect
                   (list :arithmetic-reg 3 64 target left right 0 0) world)
                  (collection-write-flags
                   (collection-subtract-flags
                    (proof-world-reg left world) (proof-world-reg right world))
                   (collection-write-register
                    target (- (proof-world-reg left world) (proof-world-reg right world))
                    (collection-next-instruction world)))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-result-flags
                                      boymoo-model::a64-signed
                                      (:definition logbitp)))))
