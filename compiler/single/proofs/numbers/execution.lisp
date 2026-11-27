(in-package "BOYMOO-PROOFS")

(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-load boymoo-model::a64-store
                     boymoo-model::a64-unsigned boymoo-model::a64-read-bytes
                     boymoo-model::a64-write-bytes
                     acl2::binary-logand acl2::binary-logior
                     mod floor ash)))

(defthm proof-number-pc-range
  (unsigned-byte-p 64 (boymoo-model::a64-pc machine))
  :rule-classes ((:rewrite) (:type-prescription
                             :corollary (natp (boymoo-model::a64-pc machine)))
                 (:linear :corollary (< (boymoo-model::a64-pc machine) (expt 2 64)))))

(defthm proof-number-sp-range
  (unsigned-byte-p 64 (boymoo-model::a64-sp machine))
  :rule-classes ((:rewrite) (:type-prescription
                             :corollary (natp (boymoo-model::a64-sp machine)))
                 (:linear :corollary (< (boymoo-model::a64-sp machine) (expt 2 64)))))

(defthm proof-number-reg-range
  (unsigned-byte-p 64 (proof-reg register machine))
  :rule-classes ((:rewrite) (:type-prescription
                             :corollary (natp (proof-reg register machine)))
                 (:linear :corollary (< (proof-reg register machine) (expt 2 64)))))

(defthm proof-number-reg-of-set-pc
  (equal (proof-reg register (boymoo-model::a64-set-pc pc machine))
         (proof-reg register machine)))

(defthm proof-number-pc-of-set-pc
  (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-unsigned 64 pc)))

(defthm proof-number-sp-of-set-pc
  (equal (boymoo-model::a64-sp (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-sp machine)))

(defthm proof-number-memory-of-set-pc
  (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-memory machine)))

(defthm proof-number-reg-of-set-flags
  (equal (proof-reg register (boymoo-model::a64-set-nzcv flags machine))
         (proof-reg register machine)))

(defthm proof-number-pc-of-set-flags
  (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-pc machine)))

(defthm proof-number-sp-of-set-flags
  (equal (boymoo-model::a64-sp (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-sp machine)))

(defthm proof-number-memory-of-set-flags
  (equal (boymoo-model::a64-memory (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-memory machine)))

(defthm proof-number-read-reg-with-sp
  (equal (boymoo-model::a64-read-reg register 64 t machine)
         (if (equal register 31) (boymoo-model::a64-sp machine)
           (proof-reg register machine))))

(defthm proof-number-reg-of-write
  (equal (proof-reg register (boymoo-model::a64-write-reg dest 64 use-sp word machine))
         (if (and (natp dest) (< dest 31) (equal register dest))
             (boymoo-model::a64-unsigned 64 word)
           (proof-reg register machine))))

(defthm proof-number-pc-of-write
  (equal (boymoo-model::a64-pc (boymoo-model::a64-write-reg dest 64 use-sp word machine))
         (boymoo-model::a64-pc machine)))

(defthm proof-number-sp-of-write
  (equal (boymoo-model::a64-sp (boymoo-model::a64-write-reg dest 64 use-sp word machine))
         (if (and (equal dest 31) use-sp)
             (boymoo-model::a64-unsigned 64 word)
           (boymoo-model::a64-sp machine))))

(defthm proof-number-memory-of-write
  (equal (boymoo-model::a64-memory (boymoo-model::a64-write-reg dest 64 use-sp word machine))
         (boymoo-model::a64-memory machine)))

(defthm proof-number-reg-of-store
  (equal (proof-reg register (boymoo-model::a64-store count address word machine))
         (proof-reg register machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm proof-number-pc-of-store
  (equal (boymoo-model::a64-pc (boymoo-model::a64-store count address word machine))
         (boymoo-model::a64-pc machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm proof-number-sp-of-store
  (equal (boymoo-model::a64-sp (boymoo-model::a64-store count address word machine))
         (boymoo-model::a64-sp machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(defthm proof-number-load-of-set-pc
  (equal (proof-load-word address (boymoo-model::a64-set-pc pc machine))
         (proof-load-word address machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load))))

(defthm proof-number-load-of-write
  (equal (proof-load-word address (boymoo-model::a64-write-reg dest 64 use-sp word machine))
         (proof-load-word address machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load))))

(defthm proof-number-load-of-set-flags
  (equal (proof-load-word address (boymoo-model::a64-set-nzcv flags machine))
         (proof-load-word address machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load))))

(local
 (in-theory (disable proof-reg boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     proof-instruction-at-p proof-instruction-access-p proof-step
                     proof-execute proof-instruction-effect)))

(defun proof-number-execute-block (instructions world)
  (if (endp instructions)
      world
    (proof-number-execute-block (cdr instructions)
                                (proof-instruction-effect (car instructions) world))))

; Each instruction is checked in its own state. Cuts are forbidden
; until the last instruction has executed.
(defun proof-number-checked-block-p (instructions cuts world)
  (and (not (proof-world-stop world))
       (let ((pc (proof-world-pc world)))
         (if (endp instructions)
             t
           (and (not (member-equal pc cuts))
                (proof-instruction-at-p (car instructions) pc world)
                (proof-instruction-access-p (car instructions) world)
                (proof-number-checked-block-p
                 (cdr instructions) cuts
                 (proof-instruction-effect (car instructions) world)))))))

(local
 (defthm proof-run-one-more
   (implies (and (natp fuel) (not (proof-world-stop world))
                 (not (member-equal (proof-world-pc world) cuts)))
            (equal (proof-run (1+ fuel) cuts world)
                   (proof-run fuel cuts (proof-step world))))
   :hints (("Goal" :expand ((proof-run (1+ fuel) cuts world))))))

(defthm proof-number-checked-block-segment
  (implies (and (proof-number-checked-block-p instructions cuts world)
                (member-equal (proof-world-pc (proof-number-execute-block instructions world))
                              cuts))
           (proof-segment-p (len instructions) cuts world :cut
                            (proof-number-execute-block instructions world)))
  :hints (("Goal"
           :induct (proof-number-checked-block-p instructions cuts world)
           :in-theory (disable proof-run proof-world-pc proof-world-stop))
          ("Subgoal *1/1" :in-theory (enable proof-run)))
  :rule-classes nil)

(defthm proof-number-result-flags-fit
  (unsigned-byte-p 4 (boymoo-model::a64-result-flags 64 result carry overflow))
  :hints (("Goal" :in-theory (disable logbitp))))

(defthm proof-number-condition-of-flags
  (implies (and (booleanp carry) (booleanp overflow))
           (let* ((flags (boymoo-model::a64-result-flags 64 result carry overflow))
                  (negative (logbitp 63 result))
                  (zero (equal result 0)))
             (and (equal (boymoo-model::a64-condition 0 flags) zero)
                  (equal (boymoo-model::a64-condition 1 flags) (not zero))
                  (equal (boymoo-model::a64-condition 2 flags) carry)
                  (equal (boymoo-model::a64-condition 3 flags) (not carry))
                  (equal (boymoo-model::a64-condition 6 flags) overflow)
                  (equal (boymoo-model::a64-condition 8 flags) (and carry (not zero)))
                  (equal (boymoo-model::a64-condition 9 flags) (or (not carry) zero))
                  (equal (boymoo-model::a64-condition 11 flags) (not (equal negative overflow)))
                  (equal (boymoo-model::a64-condition 12 flags)
                         (and (equal negative overflow) (not zero))))))
  :hints (("Goal" :in-theory (disable logbitp))))

(defund proof-number-subtraction-flags (left right)
  (let* ((sum (+ left (logxor right (boymoo-model::a64-ones 64)) 1))
         (bits (boymoo-model::a64-unsigned 64 sum))
         (difference (- (boymoo-model::a64-signed 64 left)
                        (boymoo-model::a64-signed 64 right))))
    (boymoo-model::a64-unsigned
     4 (boymoo-model::a64-result-flags 64 bits (logbitp 64 sum)
                                       (not (equal difference
                                                   (boymoo-model::a64-signed 64 bits)))))))

(local
 (defthm normalized-subtraction
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (let* ((full (+ left (logxor right (boymoo-model::a64-ones 64)) 1))
                   (difference (- left right))
                   (bits (if (< left right) (+ (expt 2 64) difference) difference)))
              (and (equal (boymoo-model::a64-unsigned 64 full) bits)
                   (equal (logbitp 64 full) (<= right left))
                   (unsigned-byte-p 64 bits))))
   :hints (("Goal"
            :use ((:instance proof-number-xor-of-word-and-mask (width 64) (a right))
                  (:instance proof-number-sign-bit (width 65)
                             (a (+ left (logxor right (boymoo-model::a64-ones 64)) 1)))
                  (:instance proof-number-a64-unsigned-is-modulo (width 64)
                             (a (+ left (logxor right (boymoo-model::a64-ones 64)) 1)))
                  (:instance proof-number-mod-with-remainder (b (expt 2 64))
                             (a (+ left (logxor right (boymoo-model::a64-ones 64)) 1))
                             (q 1) (r (- left right))))
            :in-theory (disable logbitp acl2::binary-logxor)
            :cases ((< left right))))
   :rule-classes nil))

(defthm proof-number-subtraction-conditions
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (let* ((flags (proof-number-subtraction-flags left right))
                  (signed-left (boymoo-model::a64-signed 64 left))
                  (signed-right (boymoo-model::a64-signed 64 right)))
             (and (equal (boymoo-model::a64-condition 0 flags) (equal left right))
                  (equal (boymoo-model::a64-condition 1 flags) (not (equal left right)))
                  (equal (boymoo-model::a64-condition 2 flags) (<= right left))
                  (equal (boymoo-model::a64-condition 3 flags) (< left right))
                  (equal (boymoo-model::a64-condition 8 flags) (< right left))
                  (equal (boymoo-model::a64-condition 9 flags) (<= left right))
                  (equal (boymoo-model::a64-condition 11 flags) (< signed-left signed-right))
                  (equal (boymoo-model::a64-condition 12 flags) (< signed-right signed-left)))))
  :hints (("Goal"
           :use (normalized-subtraction
                 (:instance proof-number-sign-bit (width 64)
                            (a (if (< left right)
                                   (+ (expt 2 64) (- left right))
                                 (- left right))))
                 (:instance proof-number-a64-signed-value (width 64) (a left))
                 (:instance proof-number-a64-signed-value (width 64) (a right))
                 (:instance proof-number-a64-signed-value (width 64)
                            (a (if (< left right)
                                   (+ (expt 2 64) (- left right))
                                 (- left right)))))
           :in-theory (e/d (proof-number-subtraction-flags)
                           (boymoo-model::a64-condition boymoo-model::a64-result-flags
                            boymoo-model::a64-signed logbitp acl2::binary-logxor)))))

(defthm proof-number-execute-compare-immediate
  (implies (and (natp source) (< source 31))
           (equal (proof-execute (list :arithmetic-imm 3 64 31 source immediate) machine)
                  (boymoo-model::a64-set-nzcv
                   (proof-number-subtraction-flags (proof-reg source machine) immediate)
                   (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
  :hints (("Goal"
           :in-theory (e/d (proof-execute proof-number-subtraction-flags
                                          boymoo-model::a64-write-reg)
                           (boymoo-model::a64-signed boymoo-model::a64-result-flags
                            boymoo-model::a64-set-nzcv boymoo-model::a64-set-pc
                            acl2::binary-logxor logbitp)))))

(defthm proof-number-nzcv-of-set-flags
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-unsigned 4 flags)))

(defthm proof-number-nzcv-of-set-pc
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-nzcv machine)))

(defthm proof-number-registers-of-set-pc
  (equal (boymoo-model::a64-registers (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-registers machine)))

(defthm proof-number-registers-of-set-flags
  (equal (boymoo-model::a64-registers (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-registers machine)))

(defthm proof-number-subtraction-flags-fit
  (unsigned-byte-p 4 (proof-number-subtraction-flags left right))
  :hints (("Goal" :in-theory (enable proof-number-subtraction-flags))))

(defthm proof-number-update-same-slot-twice
  (equal (update-nth index new (update-nth index old state))
         (update-nth index new state))
  :hints (("Goal" :induct (update-nth index old state))))

(local
 (defun update-slots-induction (i j record)
   (declare (xargs :measure (nfix i)))
   (if (or (zp i) (zp j))
       record
     (update-slots-induction (1- i) (1- j) (cdr record)))))

(defthm proof-number-distinct-slot-updates
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i new (update-nth j old record))
                  (update-nth j old (update-nth i new record))))
  :hints (("Goal" :induct (update-slots-induction i j record)))
  :rule-classes nil)

(defthm proof-number-set-pc-again
  (equal (boymoo-model::a64-set-pc new (boymoo-model::a64-set-pc old machine))
         (boymoo-model::a64-set-pc new machine)))

(local
 (defthm set-pc-of-link-write
   (equal (boymoo-model::a64-set-pc
           pc (boymoo-model::a64-write-reg 30 64 nil value machine))
          (boymoo-model::a64-write-reg
           30 64 nil value (boymoo-model::a64-set-pc pc machine)))
   :hints (("Goal"
            :use ((:instance proof-number-distinct-slot-updates
                             (i 2) (j 0) (record machine)
                             (new (boymoo-model::a64-unsigned 64 pc))
                             (old (put-assoc-equal
                                   30 (boymoo-model::a64-unsigned 64 value)
                                   (boymoo-model::a64-registers machine)))))
            :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (defthm plain-read-register
   (equal (boymoo-model::a64-read-reg register 64 nil machine)
          (proof-reg register machine))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(defthm proof-number-zero-register
  (equal (proof-reg 31 machine) 0)
  :hints (("Goal"
           :in-theory (e/d (proof-reg boymoo-model::a64-read-reg) (plain-read-register)))))

(local
 (defthm no-shift
   (implies (unsigned-byte-p 64 word)
            (equal (boymoo-model::a64-shift 0 64 word 0) word))))

(defthm proof-number-execute-compare-registers
  (equal (proof-execute (list :arithmetic-reg 3 64 31 left right 0 0) machine)
         (boymoo-model::a64-set-nzcv
          (proof-number-subtraction-flags (proof-reg left machine) (proof-reg right machine))
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute proof-number-subtraction-flags
                                          boymoo-model::a64-write-reg)
                           (boymoo-model::a64-signed boymoo-model::a64-result-flags
                            boymoo-model::a64-set-nzcv boymoo-model::a64-set-pc
                            acl2::binary-logxor logbitp)))))

(defthm proof-number-execute-conditional-branch
  (equal (proof-execute (list :branch-cond delta condition) machine)
         (boymoo-model::a64-set-pc
          (+ (boymoo-model::a64-pc machine)
             (if (boymoo-model::a64-condition condition (boymoo-model::a64-nzcv machine))
                 delta
               4))
          machine))
  :hints (("Goal"
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-condition
                            boymoo-model::a64-nzcv)))))

(defthm proof-number-execute-branch
  (equal (proof-execute (list :branch delta link) machine)
         (let ((target (boymoo-model::a64-set-pc
                        (+ (boymoo-model::a64-pc machine) delta) machine)))
           (if link
               (boymoo-model::a64-write-reg 30 64 nil
                                           (boymoo-model::a64-unsigned
                                            64 (+ 4 (boymoo-model::a64-pc machine)))
                                           target)
             target)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-pc)))))

(defthm proof-number-execute-return
  (equal (proof-execute '(:branch-reg 30 nil) machine)
         (boymoo-model::a64-set-pc (proof-reg 30 machine) machine))
  :hints (("Goal"
           :in-theory (e/d (proof-execute) (boymoo-model::a64-set-pc)))))

(defthm proof-number-execute-move
  (equal (proof-execute (list :logical-reg 1 64 dest 31 source 0 0 nil) machine)
         (boymoo-model::a64-write-reg
          dest 64 nil (proof-reg source machine)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-shift)))))

(defthm proof-number-execute-add-immediate
  (equal (proof-execute (list :arithmetic-imm 0 64 dest source immediate) machine)
         (boymoo-model::a64-write-reg
          dest 64 t (boymoo-model::a64-unsigned
                     64 (+ (boymoo-model::a64-read-reg source 64 t machine) immediate))
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-pc)))))

(defthm proof-number-execute-move-constant
  (equal (proof-execute (list :move-wide 2 64 dest immediate 0) machine)
         (boymoo-model::a64-write-reg
          dest 64 nil (ifix immediate)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal" :in-theory (enable proof-execute ash))))

(defthm proof-number-proof-world-machine-update
  (equal (proof-world-machine (update-nth 0 machine world)) machine))

(defthm proof-number-proof-world-reg-update
  (equal (proof-world-reg register (update-nth 0 machine world))
         (proof-reg register machine)))

(defthm proof-number-proof-world-pc-update
  (equal (proof-world-pc (update-nth 0 machine world))
         (boymoo-model::a64-pc machine)))

(defthm proof-number-proof-world-stop-update
  (equal (proof-world-stop (update-nth 0 machine world))
         (proof-world-stop world)))

(defthm proof-number-instruction-effect-normal
  (implies (and (not (eq (proof-execute instruction (proof-world-machine world)) :undefined))
                (not (eq (car (proof-execute instruction (proof-world-machine world))) :svc)))
           (equal (proof-instruction-effect instruction world)
                  (update-nth 0 (proof-execute instruction (proof-world-machine world)) world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect))))

(defthm proof-number-execute-load-word
  (equal (proof-execute (list :single 1 8 base dest :offset offset) machine)
         (boymoo-model::a64-write-reg
          dest 64 nil
          (proof-load-word (+ (boymoo-model::a64-read-reg base 64 t machine) offset) machine)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute proof-load-word boymoo-model::a64-load)
                           (boymoo-model::a64-set-pc boymoo-model::a64-memory)))))

(defthm proof-number-execute-store-word
  (equal (proof-execute (list :single 0 8 base source :offset offset) machine)
         (boymoo-model::a64-store
          8 (+ (boymoo-model::a64-read-reg base 64 t machine) offset)
          (proof-reg source machine)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal" :in-theory (e/d (proof-execute) (boymoo-model::a64-set-pc)))))

(defthm proof-number-execute-store-pair
  (equal (proof-execute (list :pair nil base first second mode offset) machine)
         (let* ((address (boymoo-model::a64-read-reg base 64 t machine))
                (updated (+ address offset))
                (start (if (eq mode :post) address updated))
                (next (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                (written (boymoo-model::a64-store
                          8 (+ 8 start) (proof-reg second machine)
                          (boymoo-model::a64-store 8 start (proof-reg first machine) next))))
           (if (or (eq mode :pre) (eq mode :post))
               (boymoo-model::a64-write-reg base 64 t updated written)
             written)))
  :hints (("Goal" :in-theory (e/d (proof-execute) (boymoo-model::a64-set-pc)))))

(defthm proof-number-execute-load-pair
  (equal (proof-execute (list :pair t base first second mode offset) machine)
         (let* ((address (boymoo-model::a64-read-reg base 64 t machine))
                (updated (+ address offset))
                (start (if (eq mode :post) address updated))
                (next (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))
                (loaded (boymoo-model::a64-write-reg
                         second 64 nil (proof-load-word (+ 8 start) machine)
                         (boymoo-model::a64-write-reg
                          first 64 nil (proof-load-word start machine) next))))
           (if (or (eq mode :pre) (eq mode :post))
               (boymoo-model::a64-write-reg base 64 t updated loaded)
             loaded)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute proof-load-word boymoo-model::a64-load)
                           (boymoo-model::a64-set-pc boymoo-model::a64-memory))
           :do-not-induct t)))

(defthm proof-number-execute-subtract-registers-in-range
  (implies (<= (proof-reg right machine) (proof-reg left machine))
           (equal (proof-execute (list :arithmetic-reg 2 64 dest left right 0 0) machine)
                  (boymoo-model::a64-write-reg
                   dest 64 nil (- (proof-reg left machine) (proof-reg right machine))
                   (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
  :hints (("Goal"
           :use ((:instance normalized-subtraction
                            (left (proof-reg left machine)) (right (proof-reg right machine))))
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-shift
                            acl2::binary-logxor)))))

(defthm proof-number-unsigned-difference
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-unsigned 64 (- left right))
                  (if (< left right)
                      (+ (expt 2 64) (- left right))
                    (- left right))))
  :hints (("Goal"
           :use ((:instance proof-number-a64-unsigned-is-modulo (width 64) (a (- left right)))
                 (:instance proof-number-mod-with-remainder (a (- left right))
                            (b (expt 2 64)) (q -1) (r (+ (expt 2 64) (- left right)))))
           :cases ((< left right))))
  :rule-classes nil)

(defthm proof-number-execute-subtract-immediate
  (implies (unsigned-byte-p 64 immediate)
           (equal (proof-execute (list :arithmetic-imm 2 64 dest source immediate) machine)
                  (boymoo-model::a64-write-reg
                   dest 64 t
                   (boymoo-model::a64-unsigned
                    64 (- (boymoo-model::a64-read-reg source 64 t machine) immediate))
                   (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
  :hints (("Goal"
           :use ((:instance normalized-subtraction
                            (left (boymoo-model::a64-read-reg source 64 t machine))
                            (right immediate))
                 (:instance proof-number-unsigned-difference
                            (left (boymoo-model::a64-read-reg source 64 t machine))
                            (right immediate)))
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc acl2::binary-logxor logbitp)))))

(defthm proof-number-execute-add-registers
  (equal (proof-execute (list :arithmetic-reg 0 64 dest left right 0 0) machine)
         (boymoo-model::a64-write-reg
          dest 64 nil (boymoo-model::a64-unsigned
                       64 (+ (proof-reg left machine) (proof-reg right machine)))
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-shift)))))

(defthm proof-number-execute-branch-on-zero
  (equal (proof-execute (list :branch-zero delta 64 source nonzero) machine)
         (boymoo-model::a64-set-pc
          (+ (boymoo-model::a64-pc machine)
             (if (if nonzero
                     (not (equal (proof-reg source machine) 0))
                   (equal (proof-reg source machine) 0))
                 delta
               4))
          machine))
  :hints (("Goal" :in-theory (e/d (proof-execute) (boymoo-model::a64-set-pc)))))

(defthm proof-number-execute-select
  (equal (proof-execute (list :select 64 dest left right condition nil) machine)
         (boymoo-model::a64-write-reg
          dest 64 nil
          (if (boymoo-model::a64-condition condition (boymoo-model::a64-nzcv machine))
              (proof-reg left machine)
            (proof-reg right machine))
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute)
                           (boymoo-model::a64-set-pc boymoo-model::a64-condition
                            boymoo-model::a64-nzcv)))))

(local
 (defthm read-one-byte
   (equal (boymoo-model::a64-read-bytes 1 address memory)
          (boymoo-model::a64-byte address memory))
   :hints (("Goal"
            :expand ((boymoo-model::a64-read-bytes 1 address memory)
                     (:free (next) (boymoo-model::a64-read-bytes 0 next memory)))
            :in-theory (disable boymoo-model::a64-byte)))))

(defthm proof-number-load-byte-range
  (unsigned-byte-p 8 (boymoo-model::a64-load 1 address machine))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-load) (boymoo-model::a64-byte))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                  (natp (boymoo-model::a64-load 1 address machine)))
                 (:linear :corollary (< (boymoo-model::a64-load 1 address machine) 256))))

(local
 (defthm storing-a-byte-in-a-register
   (implies (unsigned-byte-p 8 value)
            (equal (boymoo-model::a64-write-reg register 8 nil value machine)
                   (boymoo-model::a64-write-reg register 64 nil value machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(defthm proof-number-execute-load-byte
  (equal (proof-execute (list :single 1 1 base dest :offset offset) machine)
         (boymoo-model::a64-write-reg
          dest 64 nil
          (boymoo-model::a64-load 1 (+ (boymoo-model::a64-read-reg base 64 t machine) offset) machine)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute boymoo-model::a64-load)
                           (boymoo-model::a64-set-pc boymoo-model::a64-memory))
           :use ((:instance storing-a-byte-in-a-register
                            (register dest)
                            (value (boymoo-model::a64-load
                                    1 (+ (boymoo-model::a64-read-reg base 64 t machine) offset)
                                    machine))
                            (machine (boymoo-model::a64-set-pc
                                      (+ 4 (boymoo-model::a64-pc machine)) machine)))))))

(local
 (defthm and-with-one-is-low-bit
   (implies (integerp value)
            (equal (logand value 1) (if (oddp value) 1 0)))
   :hints (("Goal"
            :use ((:instance proof-number-low-bit (a value)))
            :in-theory (e/d (boymoo-model::a64-unsigned)
                           (proof-number-low-bit oddp proof-number-integer-parity))))))

(defthm proof-number-execute-test-low-bit
  (equal (proof-execute (list :logical-imm 3 64 31 source 1) machine)
         (boymoo-model::a64-set-nzcv
          (if (oddp (proof-reg source machine)) 0 4)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute boymoo-model::a64-write-reg)
                           (boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                            logbitp oddp proof-number-integer-parity)))))

(local
 (defthm and-with-seven-is-tag
   (implies (integerp value)
            (equal (logand value 7) (proof-word-tag value)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned)))))

(defthm proof-number-word-tag-range
  (unsigned-byte-p 3 (proof-word-tag value)))

(defthm proof-number-execute-load-tag
  (equal (proof-execute (list :logical-imm 0 64 dest source 7) machine)
         (boymoo-model::a64-write-reg
          dest 64 t (proof-word-tag (proof-reg source machine))
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal"
           :in-theory (e/d (proof-execute) (boymoo-model::a64-set-pc proof-word-tag)))))
