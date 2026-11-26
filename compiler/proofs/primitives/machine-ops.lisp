(in-package "BOYMOO-PROOFS")

(include-book "paths")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-set-pc (address world)
  (update-nth 0 (boymoo-model::a64-set-pc address (proof-world-machine world)) world))

(defund p6-set-register (register value world)
  (update-nth 0 (boymoo-model::a64-write-reg register 64 nil value
                                           (proof-world-machine world))
              world))

(defund p6-set-flags (flags world)
  (update-nth 0 (boymoo-model::a64-set-nzcv flags (proof-world-machine world)) world))

(defmacro p6-next (world)
  `(p6-set-pc (+ 4 (proof-world-pc ,world)) ,world))

(defthm p6-world-register-range
  (unsigned-byte-p 64 (proof-world-reg register world))
  :hints (("Goal" :in-theory (enable proof-world-reg))))

(defthm p6-world-register-natural
  (natp (proof-world-reg register world))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable proof-world-reg))))

(defthm p6-world-pc-range
  (unsigned-byte-p 64 (proof-world-pc world))
  :hints (("Goal" :in-theory (enable proof-world-pc))))

(defthm p6-world-pc-natural
  (natp (proof-world-pc world))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable proof-world-pc))))

(defthm p6-world-pc-under-update
  (and (equal (proof-world-pc (p6-set-pc address world))
              (boymoo-model::a64-unsigned 64 address))
       (equal (proof-world-pc (p6-set-register register value world))
              (proof-world-pc world))
       (equal (proof-world-pc (p6-set-flags flags world)) (proof-world-pc world)))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags
                                   proof-world-pc proof-world-machine))))

(local
 (defthm p6-assoc-after-put
   (equal (cdr (assoc-equal register (put-assoc-equal dest value registers)))
          (if (equal register dest) value (cdr (assoc-equal register registers))))))

(defthm p6-world-register-under-update
  (and (equal (proof-world-reg register (p6-set-pc address world))
              (proof-world-reg register world))
       (equal (proof-world-reg register (p6-set-flags flags world))
              (proof-world-reg register world))
       (equal (proof-world-reg register (p6-set-register dest value world))
              (if (and (equal register dest) (natp dest) (< dest 31))
                  (boymoo-model::a64-unsigned 64 value)
                (proof-world-reg register world))))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags
                                   proof-world-reg proof-world-machine))))

(defthm p6-world-flags-under-update
  (and (equal (boymoo-model::a64-nzcv (proof-world-machine (p6-set-pc address world)))
              (boymoo-model::a64-nzcv (proof-world-machine world)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine (p6-set-register dest value world)))
              (boymoo-model::a64-nzcv (proof-world-machine world)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine (p6-set-flags flags world)))
              (boymoo-model::a64-unsigned 4 flags)))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags
                                   proof-world-machine))))

(defthm p6-world-sp-under-update
  (and (equal (boymoo-model::a64-sp (proof-world-machine (p6-set-pc address world)))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (boymoo-model::a64-sp (proof-world-machine (p6-set-register dest value world)))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (boymoo-model::a64-sp (proof-world-machine (p6-set-flags flags world)))
              (boymoo-model::a64-sp (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags
                                   proof-world-machine))))

(defthm p6-world-memory-under-update
  (and (equal (boymoo-model::a64-memory (proof-world-machine (p6-set-pc address world)))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (boymoo-model::a64-memory (proof-world-machine (p6-set-register dest value world)))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (boymoo-model::a64-memory (proof-world-machine (p6-set-flags flags world)))
              (boymoo-model::a64-memory (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags
                                   proof-world-machine boymoo-model::a64-memory))))

(defthm p6-world-environment-under-update
  (and (equal (cdr (p6-set-pc address world)) (cdr world))
       (equal (cdr (p6-set-register dest value world)) (cdr world))
       (equal (cdr (p6-set-flags flags world)) (cdr world)))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags))))

(defthm p6-world-stop-and-map-under-update
  (and (equal (proof-world-stop (p6-set-pc address world)) (proof-world-stop world))
       (equal (proof-world-stop (p6-set-register dest value world)) (proof-world-stop world))
       (equal (proof-world-stop (p6-set-flags flags world)) (proof-world-stop world))
       (equal (proof-world-regions (p6-set-pc address world)) (proof-world-regions world))
       (equal (proof-world-regions (p6-set-register dest value world)) (proof-world-regions world))
       (equal (proof-world-regions (p6-set-flags flags world)) (proof-world-regions world)))
  :hints (("Goal" :in-theory (enable p6-set-pc p6-set-register p6-set-flags
                                   proof-world-stop proof-world-regions))))

; A running machine is a record with a register file, distinct from
; a system-call event.
(defund p6-register-file-p (world)
  (let ((machine (proof-world-machine world)))
    (and (consp machine) (not (eq (boymoo-model::a64-registers machine) :svc)))))

(defthm p6-register-file-under-update
  (implies (p6-register-file-p world)
           (and (p6-register-file-p (p6-set-pc address world))
                (p6-register-file-p (p6-set-register dest value world))
                (p6-register-file-p (p6-set-flags flags world))))
  :hints (("Goal" :in-theory (enable p6-register-file-p p6-set-pc p6-set-register
                                   p6-set-flags proof-world-machine))))

(local
 (defthm p6-update-nth-car-and-consp
   (and (equal (car (update-nth n value list))
               (if (zp n) value (car list)))
        (consp (update-nth n value list)))))

(local
 (defthm p6-update-nth-overwrite
   (equal (update-nth n new (update-nth n old list))
          (update-nth n new list))
   :hints (("Goal" :induct (update-nth n old list)))))

(local (in-theory (disable update-nth proof-linux-svc)))

; For a decoded instruction, the following rules express the effects
; used in the paths. The conditions and flags retain their A64 meaning.
(defthm p6-effect-movz
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect (list :move-wide 2 64 dest immediate position) world)
                  (p6-set-register dest (ash immediate position) (p6-next world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                   p6-set-pc p6-set-register proof-world-machine
                                   proof-world-pc p6-register-file-p))))

(defthm p6-effect-ret
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect '(:branch-reg 30 nil) world)
                  (p6-set-pc (proof-world-reg 30 world) world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                   p6-set-pc proof-world-machine proof-world-reg proof-world-pc
                                   proof-reg p6-register-file-p))))

(defthm p6-effect-b
  (implies (and (p6-register-file-p world) (integerp delta))
           (equal (proof-instruction-effect (list :branch delta nil) world)
                  (p6-set-pc (+ (proof-world-pc world) delta) world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                   p6-set-pc proof-world-machine proof-world-pc p6-register-file-p))))

(defthm p6-effect-b-cond
  (implies (and (p6-register-file-p world) (integerp delta))
           (equal (proof-instruction-effect (list :branch-cond delta condition) world)
                  (if (boymoo-model::a64-condition condition
                                                   (boymoo-model::a64-nzcv (proof-world-machine world)))
                      (p6-set-pc (+ (proof-world-pc world) delta) world)
                    (p6-next world))))
  :hints (("Goal" :in-theory (e/d (proof-instruction-effect proof-execute p6-set-pc
                                  proof-world-machine proof-world-pc p6-register-file-p)
                                 (boymoo-model::a64-condition)))))

(defthm p6-effect-select
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect (list :select 64 dest left right condition nil) world)
                  (p6-set-register dest
                                   (if (boymoo-model::a64-condition
                                        condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                                       (proof-world-reg left world)
                                     (proof-world-reg right world))
                                   (p6-next world))))
  :hints (("Goal" :in-theory (e/d (proof-instruction-effect proof-execute p6-set-pc
                                  p6-set-register proof-world-machine proof-world-pc
                                  proof-world-reg proof-reg p6-register-file-p)
                                 (boymoo-model::a64-condition)))))

(defthm p6-access-without-memory-instruction
  (implies (not (member-eq (car instruction) '(:single :pair)))
           (proof-instruction-access-p instruction world))
  :hints (("Goal" :in-theory (enable proof-instruction-access-p))))

(in-theory (disable boymoo-model::a64-execute boymoo-model::a64-read-reg
                    boymoo-model::a64-sp boymoo-model::a64-nzcv
                    boymoo-model::a64-condition proof-reg))

(defthm p6-flags-range
  (unsigned-byte-p 4 (boymoo-model::a64-result-flags width bits carry overflow)))

(defthm p6-condition-from-flags
  (let ((flags (boymoo-model::a64-result-flags width bits carry overflow)))
    (and (equal (boymoo-model::a64-condition 0 flags) (equal bits 0))
         (equal (boymoo-model::a64-condition 1 flags) (not (equal bits 0)))
         (equal (boymoo-model::a64-condition 2 flags) (if carry t nil))
         (equal (boymoo-model::a64-condition 3 flags) (not carry))
         (equal (boymoo-model::a64-condition 8 flags) (and carry (not (equal bits 0)) t))
         (equal (boymoo-model::a64-condition 9 flags) (or (not carry) (equal bits 0)))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-condition))))

(in-theory (disable boymoo-model::a64-result-flags))

(defthm p6-effect-and-mask
  (implies (and (p6-register-file-p world) (natp dest) (< dest 31))
           (equal (proof-instruction-effect (list :logical-imm 0 64 dest source mask) world)
                  (p6-set-register dest (logand (proof-world-reg source world) mask)
                                   (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-pc p6-set-register proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p))))

(defthm p6-effect-tst-mask
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect (list :logical-imm 3 64 31 source mask) world)
                  (p6-set-flags
                   (boymoo-model::a64-result-flags 64 (logand (proof-world-reg source world) mask)
                                                  nil nil)
                   (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-pc p6-set-flags proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p))))

(defthm p6-effect-branch-zero
  (implies (and (p6-register-file-p world) (integerp delta))
           (equal (proof-instruction-effect (list :branch-zero delta 64 source nonzero) world)
                  (if (if nonzero (not (equal (proof-world-reg source world) 0))
                        (equal (proof-world-reg source world) 0))
                      (p6-set-pc (+ (proof-world-pc world) delta) world)
                    (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p))))

(defund p6-compare-flags (left right)
  (let* ((difference (boymoo-model::a64-unsigned 64 (- left right)))
         (signed-difference (- (boymoo-model::a64-signed 64 left)
                               (boymoo-model::a64-signed 64 right))))
    (boymoo-model::a64-result-flags 64 difference (<= right left)
                                   (not (equal signed-difference
                                               (boymoo-model::a64-signed 64 difference))))))

(defthm p6-compare-flags-range
  (unsigned-byte-p 4 (p6-compare-flags left right))
  :hints (("Goal" :in-theory (e/d (p6-compare-flags)
                                  (unsigned-byte-p boymoo-model::a64-signed p6-signed64-in-range)))))

(defthm p6-condition-after-compare
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (let ((flags (p6-compare-flags left right)))
             (and (equal (boymoo-model::a64-condition 0 flags) (equal left right))
                  (equal (boymoo-model::a64-condition 1 flags) (not (equal left right)))
                  (equal (boymoo-model::a64-condition 2 flags) (<= right left))
                  (equal (boymoo-model::a64-condition 3 flags) (< left right))
                  (equal (boymoo-model::a64-condition 8 flags) (< right left))
                  (equal (boymoo-model::a64-condition 9 flags) (<= left right)))))
  :hints (("Goal" :in-theory (e/d (p6-compare-flags)
                                  (boymoo-model::a64-signed p6-signed64-in-range)))))

(local
 (defthm p6-subtraction-carry
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (and (equal (logbitp 64 (+ #x10000000000000000 (- right) left))
                        (<= right left))
                 (equal (logbitp 64 (+ #x10000000000000000 left (- right)))
                        (<= right left))))
   :hints (("Goal" :use ((:instance p6-top-bit (bit 64) (x (+ (expt 2 64) (- left right)))))))))

(local
 (in-theory (disable boymoo-model::a64-signed p6-signed64-in-range
                     p6-unsigned-add p6-unsigned-add-integer p6-unsigned-sub)))

(defthm p6-effect-cmp-immediate
  (implies (and (p6-register-file-p world) (natp source) (< source 31)
                (unsigned-byte-p 64 immediate))
           (equal (proof-instruction-effect (list :arithmetic-imm 3 64 31 source immediate) world)
                  (p6-set-flags (p6-compare-flags (proof-world-reg source world) immediate)
                                (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-pc p6-set-flags proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p p6-compare-flags))))

(defthm p6-effect-cmp-register
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect (list :arithmetic-reg 3 64 31 left right 0 0) world)
                  (p6-set-flags (p6-compare-flags (proof-world-reg left world)
                                                 (proof-world-reg right world))
                                (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-pc p6-set-flags proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p p6-compare-flags))))

(defthm p6-effect-add-immediate
  (implies (and (p6-register-file-p world) (natp source) (< source 31)
                (natp dest) (< dest 31) (integerp immediate))
           (equal (proof-instruction-effect (list :arithmetic-imm 0 64 dest source immediate) world)
                  (p6-set-register dest (+ (proof-world-reg source world) immediate) (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-register p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p))))

(defthm p6-effect-sub-immediate
  (implies (and (p6-register-file-p world) (natp source) (< source 31)
                (natp dest) (< dest 31) (unsigned-byte-p 64 immediate))
           (equal (proof-instruction-effect (list :arithmetic-imm 2 64 dest source immediate) world)
                  (p6-set-register dest (- (proof-world-reg source world) immediate) (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-register p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p))))

(defund p6-world-load (count address world)
  (boymoo-model::a64-load count address (proof-world-machine world)))

(defthm p6-world-load-under-update
  (and (equal (p6-world-load count address (p6-set-pc pc world))
              (p6-world-load count address world))
       (equal (p6-world-load count address (p6-set-register dest value world))
              (p6-world-load count address world))
       (equal (p6-world-load count address (p6-set-flags flags world))
              (p6-world-load count address world)))
  :hints (("Goal" :in-theory (e/d (p6-world-load boymoo-model::a64-load)
                                  (p6-load-one-byte p6-load-at-wrapped-address)))))

(defthm p6-world-load-widths
  (and (unsigned-byte-p 8 (p6-world-load 1 address world))
       (unsigned-byte-p 64 (p6-world-load 8 address world))
       (unsigned-byte-p 64 (p6-world-load 1 address world)))
  :hints (("Goal" :in-theory (enable p6-world-load))))

(defthm p6-world-load-wraps
  (equal (p6-world-load count (boymoo-model::a64-unsigned 64 address) world)
         (p6-world-load count address world))
  :hints (("Goal" :in-theory (enable p6-world-load))))

(defthm p6-world-load-add-wraps
  (implies (and (integerp address) (integerp delta))
           (and (equal (p6-world-load count (+ delta (boymoo-model::a64-unsigned 64 address)) world)
                       (p6-world-load count (+ delta address) world))
                (equal (p6-world-load count (+ (boymoo-model::a64-unsigned 64 address) delta) world)
                       (p6-world-load count (+ address delta) world))))
  :hints (("Goal"
           :in-theory (enable p6-world-load boymoo-model::a64-load p6-unsigned-add-integer)
           :use ((:instance p6-read-bytes-equal-at-congruent-addresses
                            (left (+ delta (boymoo-model::a64-unsigned 64 address)))
                            (right (+ delta address))
                            (memory (boymoo-model::a64-memory (proof-world-machine world))))))))

(defthm p6-world-load-natural
  (natp (p6-world-load count address world))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable p6-world-load boymoo-model::a64-load))))

(local
 (defthm p6-load-and-memory-after-pc-write
   (and (equal (boymoo-model::a64-load count address (update-nth 2 value machine))
               (boymoo-model::a64-load count address machine))
        (equal (boymoo-model::a64-memory (update-nth 2 value machine))
               (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load boymoo-model::a64-memory)))))

(defthm p6-effect-load-offset
  (implies (and (p6-register-file-p world) (natp source) (< source 31)
                (natp dest) (< dest 31) (integerp offset) (member-equal count '(1 8)))
           (equal (proof-instruction-effect (list :single 1 count source dest :offset offset) world)
                  (p6-set-register dest (p6-world-load count (+ (proof-world-reg source world) offset) world)
                                   (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-register p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p p6-world-load))))

(defthm p6-effect-load-register
  (implies (and (p6-register-file-p world) (natp source) (< source 31)
                (natp dest) (< dest 31) (member-equal count '(1 8)))
           (equal (proof-instruction-effect
                   (list :single 1 count source dest :register index 3 0) world)
                  (p6-set-register dest
                                   (p6-world-load count (+ (proof-world-reg source world)
                                                          (proof-world-reg index world)) world)
                                   (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-register p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p p6-world-load))))

(defthm p6-offset-load-access
  (implies (and (natp source) (< source 31))
           (equal (proof-instruction-access-p (list :single 1 count source dest :offset offset) world)
                  (proof-covered-p (boymoo-model::a64-unsigned 64
                                                               (+ (proof-world-reg source world) offset))
                                   count :read (proof-world-regions world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-access-p proof-world-reg proof-reg
                              boymoo-model::a64-read-reg))))

(defthm p6-register-load-access
  (implies (and (natp source) (< source 31))
           (equal (proof-instruction-access-p
                   (list :single 1 count source dest :register index 3 0) world)
                  (proof-covered-p
                   (boymoo-model::a64-unsigned 64 (+ (proof-world-reg source world)
                                                     (proof-world-reg index world)))
                   count :read (proof-world-regions world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-access-p proof-world-reg proof-reg
                              boymoo-model::a64-read-reg))))

(defthm p6-effect-add-register
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect (list :arithmetic-reg 0 64 dest left right 0 0) world)
                  (p6-set-register dest (+ (proof-world-reg left world) (proof-world-reg right world))
                                   (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-register p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              p6-register-file-p))))

(local
 (defthm p6-double-negation
   (implies (acl2-numberp x) (equal (- (- x)) x))))

(defthm p6-effect-mov-register
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect (list :logical-reg 1 64 dest 31 source 0 0 nil) world)
                  (p6-set-register dest (proof-world-reg source world) (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              p6-set-register p6-set-pc proof-world-machine proof-world-pc
                              proof-world-reg proof-reg boymoo-model::a64-read-reg
                              acl2::binary-logior acl2::binary-logand p6-register-file-p))))
