(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                    boymoo-model::a64-load boymoo-model::a64-store
                    boymoo-model::a64-byte boymoo-model::a64-read-bytes
                    boymoo-model::a64-write-bytes
                    boymoo-model::a64-registers boymoo-model::a64-sp
                    boymoo-model::a64-pc boymoo-model::a64-nzcv
                    boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                    boymoo-model::a64-memory))

(defthm sequence-assoc-of-put
  (equal (assoc-equal key (put-assoc-equal target value pairs))
         (if (equal key target) (cons key value) (assoc-equal key pairs)))
  :hints (("Goal" :induct (put-assoc-equal target value pairs))))

(defthm sequence-first-of-update-later
  (implies (posp index)
           (equal (car (update-nth index value items)) (car items)))
  :hints (("Goal" :expand ((update-nth index value items)))))

(defthm sequence-replace-update-at-same-index
  (equal (update-nth index new (update-nth index old items))
         (update-nth index new items))
  :hints (("Goal" :induct (update-nth index old items)
                  :in-theory (enable update-nth))))

(defthm sequence-register-bits
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-read-reg register width use-sp machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg))))

(defthm sequence-register-value-is-natural
  (natp (boymoo-model::a64-read-reg register width use-sp machine))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg))))

(defthm sequence-register-value-bound
  (< (boymoo-model::a64-read-reg register width use-sp machine) (expt 2 (nfix width)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg))))

(defthm sequence-read-width-after-write
  (implies (and (natp register) (< register 31))
           (equal (boymoo-model::a64-read-reg
                   register read-width use-sp
                   (boymoo-model::a64-write-reg target width target-sp value machine))
                  (if (equal register target)
                      (boymoo-model::a64-unsigned
                       read-width (boymoo-model::a64-unsigned width value))
                    (boymoo-model::a64-read-reg register read-width use-sp machine))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg
                                    boymoo-model::a64-write-reg
                                    boymoo-model::a64-registers))))

(defthm sequence-reg-after-write
  (implies (and (natp register) (< register 31)
                (natp width) (<= width 64))
           (equal (boymoo-model::a64-read-reg
                   register 64 use-sp
                   (boymoo-model::a64-write-reg target width target-sp value machine))
                  (if (equal register target)
                      (boymoo-model::a64-unsigned width value)
                    (boymoo-model::a64-read-reg register 64 use-sp machine))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg
                                    boymoo-model::a64-write-reg
                                    boymoo-model::a64-registers))))

(defthm sequence-read-zero-register
  (equal (boymoo-model::a64-read-reg 31 width nil machine) 0)
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg))))

(defthm sequence-read-stack-register
  (equal (boymoo-model::a64-read-reg 31 64 t machine)
         (boymoo-model::a64-sp machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg
                                    boymoo-model::a64-sp))))

(defthm sequence-register-read-with-sp-selected
  (implies (not (equal register 31))
           (equal (boymoo-model::a64-read-reg register width t machine)
                  (boymoo-model::a64-read-reg register width nil machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg))))

(defthm sequence-ignore-zero-register-write
  (equal (boymoo-model::a64-write-reg 31 width nil value machine) machine)
  :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg))))

(defthm sequence-components-of-register-write
  (and (equal (boymoo-model::a64-pc
               (boymoo-model::a64-write-reg target width use-sp value machine))
              (boymoo-model::a64-pc machine))
       (equal (boymoo-model::a64-nzcv
               (boymoo-model::a64-write-reg target width use-sp value machine))
              (boymoo-model::a64-nzcv machine))
       (equal (boymoo-model::a64-memory
               (boymoo-model::a64-write-reg target width use-sp value machine))
              (boymoo-model::a64-memory machine))
       (equal (boymoo-model::a64-sp
               (boymoo-model::a64-write-reg target width use-sp value machine))
              (if (and (equal target 31) use-sp)
                  (boymoo-model::a64-unsigned
                   64 (boymoo-model::a64-unsigned width value))
                (boymoo-model::a64-sp machine))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg
                                    boymoo-model::a64-pc boymoo-model::a64-nzcv
                                    boymoo-model::a64-sp boymoo-model::a64-memory))))

(defthm sequence-components-of-pc-write
  (and (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
              (boymoo-model::a64-unsigned 64 pc))
       (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
              (boymoo-model::a64-nzcv machine))
       (equal (boymoo-model::a64-sp (boymoo-model::a64-set-pc pc machine))
              (boymoo-model::a64-sp machine))
       (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc pc machine))
              (boymoo-model::a64-memory machine))
       (equal (boymoo-model::a64-registers (boymoo-model::a64-set-pc pc machine))
              (boymoo-model::a64-registers machine))
       (equal (boymoo-model::a64-read-reg register width use-sp
                                         (boymoo-model::a64-set-pc pc machine))
              (boymoo-model::a64-read-reg register width use-sp machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc
                                    boymoo-model::a64-read-reg
                                    boymoo-model::a64-registers
                                    boymoo-model::a64-pc boymoo-model::a64-nzcv
                                    boymoo-model::a64-sp boymoo-model::a64-memory))))

(defthm sequence-components-of-flags-write
  (and (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-nzcv flags machine))
              (boymoo-model::a64-unsigned 4 flags))
       (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv flags machine))
              (boymoo-model::a64-pc machine))
       (equal (boymoo-model::a64-sp (boymoo-model::a64-set-nzcv flags machine))
              (boymoo-model::a64-sp machine))
       (equal (boymoo-model::a64-memory (boymoo-model::a64-set-nzcv flags machine))
              (boymoo-model::a64-memory machine))
       (equal (boymoo-model::a64-registers (boymoo-model::a64-set-nzcv flags machine))
              (boymoo-model::a64-registers machine))
       (equal (boymoo-model::a64-read-reg register width use-sp
                                         (boymoo-model::a64-set-nzcv flags machine))
              (boymoo-model::a64-read-reg register width use-sp machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-set-nzcv
                                    boymoo-model::a64-read-reg
                                    boymoo-model::a64-registers
                                    boymoo-model::a64-pc boymoo-model::a64-nzcv
                                    boymoo-model::a64-sp boymoo-model::a64-memory))))

(defthm sequence-components-of-store
  (and (equal (boymoo-model::a64-memory (boymoo-model::a64-store size address value machine))
              (boymoo-model::a64-write-bytes size address value
                                            (boymoo-model::a64-memory machine)))
       (equal (boymoo-model::a64-pc (boymoo-model::a64-store size address value machine))
              (boymoo-model::a64-pc machine))
       (equal (boymoo-model::a64-sp (boymoo-model::a64-store size address value machine))
              (boymoo-model::a64-sp machine))
       (equal (boymoo-model::a64-nzcv (boymoo-model::a64-store size address value machine))
              (boymoo-model::a64-nzcv machine))
       (equal (boymoo-model::a64-registers (boymoo-model::a64-store size address value machine))
              (boymoo-model::a64-registers machine))
       (equal (boymoo-model::a64-read-reg register width use-sp
                                         (boymoo-model::a64-store size address value machine))
              (boymoo-model::a64-read-reg register width use-sp machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store
                                    boymoo-model::a64-read-reg
                                    boymoo-model::a64-registers
                                    boymoo-model::a64-pc boymoo-model::a64-nzcv
                                    boymoo-model::a64-sp boymoo-model::a64-memory))))

(defthm sequence-register-list-of-write
  (equal (boymoo-model::a64-registers
          (boymoo-model::a64-write-reg target width use-sp value machine))
         (if (and (natp target) (< target 31))
             (put-assoc-equal target (boymoo-model::a64-unsigned width value)
                              (boymoo-model::a64-registers machine))
           (boymoo-model::a64-registers machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg
                                    boymoo-model::a64-registers))))

(defthm sequence-load-uses-memory
  (equal (boymoo-model::a64-load count address machine)
         (boymoo-model::a64-read-bytes count address (boymoo-model::a64-memory machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load))))

(defthm sequence-pc-bits
  (unsigned-byte-p 64 (boymoo-model::a64-pc machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-pc))))

(defthm sequence-pc-natural
  (natp (boymoo-model::a64-pc machine))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-pc))))

(defthm sequence-pc-bound
  (< (boymoo-model::a64-pc machine) (expt 2 64))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable boymoo-model::a64-pc))))

(defthm sequence-sp-bits
  (unsigned-byte-p 64 (boymoo-model::a64-sp machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-sp))))

(defthm sequence-sp-natural
  (natp (boymoo-model::a64-sp machine))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-sp))))

(defthm sequence-sp-bound
  (< (boymoo-model::a64-sp machine) (expt 2 64))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable boymoo-model::a64-sp))))

(defthm sequence-effect-of-machine-instruction
  (implies (consp (boymoo-model::a64-registers
                   (proof-execute instruction (proof-world-machine world))))
           (equal (proof-instruction-effect instruction world)
                  (update-nth 0 (proof-execute instruction (proof-world-machine world))
                              world)))
  :hints (("Goal" :in-theory (e/d (proof-instruction-effect boymoo-model::a64-registers)
                                   (proof-execute)))))
