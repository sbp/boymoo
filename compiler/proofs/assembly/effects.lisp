(in-package "BOYMOO-PROOFS")

(include-book "execution")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash floor mod proof-reg
                           boymoo-model::a64-pc boymoo-model::a64-nzcv
                           boymoo-model::a64-read-reg boymoo-model::a64-set-pc
                           boymoo-model::a64-signed boymoo-model::a64-shift
                           boymoo-model::a64-unsigned assembly-low assembly-high
                           assembly-power-of-two)))

(defthm assembly-page-of-aligned-base-plus-offset
  (implies (and (integerp base) (integerp offset) (equal (mod base 4096) 0))
           (equal (floor (+ base offset) 4096)
                  (+ (floor base 4096) (floor offset 4096))))
  :hints (("Goal"
           :use ((:instance assembly-floor-unique
                            (x (+ base offset)) (d 4096)
                            (q (+ (floor base 4096) (floor offset 4096))))
                 (:instance assembly-floor-bounds (x offset) (d 4096)))
           :in-theory (enable mod))))

(defthm assembly-adr-far-address
  (implies (and (integerp base) (integerp pc) (integerp target)
                (equal (mod base 4096) 0))
           (equal (+ (* 4096 (floor (+ base pc) 4096))
                     (* 4096 (- (floor target 4096) (floor pc 4096)))
                     (mod target 4096))
                  (+ base target)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm assembly-discarded-and-effect
  (equal (proof-execute (list :logical-reg 0 64 31 rn 31 0 0 nil) machine)
         (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))

(defthm assembly-cset-al-effect
  (equal (proof-execute (list :move-wide 2 64 rd 1 0) machine)
         (boymoo-model::a64-write-reg
          rd 64 nil 1
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-write-reg))))

(defthm assembly-svc-event
  (equal (proof-execute (list :svc immediate) machine)
         (list :svc immediate (proof-reg 16 machine) (proof-reg 8 machine)))
  :hints (("Goal" :in-theory (enable proof-reg))))

(defthm assembly-clz-effect
  (equal (proof-execute (list :clz rd rn) machine)
         (boymoo-model::a64-write-reg
          rd 64 nil (- 64 (integer-length (proof-reg rn machine)))
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-write-reg))))

(local
 (defthm assembly-put-assoc-keeps-register-file
   (implies (alistp registers)
            (alistp (put-assoc-equal register value registers)))))

(local
 (defthm assembly-update-nth-consp
   (consp (update-nth n value xs))
   :hints (("Goal" :expand ((update-nth n value xs))))))

(local
 (defthm assembly-a64-write-reg-preserves-fields
   (and (equal (boymoo-model::a64-pc
                 (boymoo-model::a64-write-reg register width use-sp value machine))
                (boymoo-model::a64-pc machine))
        (equal (boymoo-model::a64-memory
                 (boymoo-model::a64-write-reg register width use-sp value machine))
                (boymoo-model::a64-memory machine))
        (implies (alistp (boymoo-model::a64-registers machine))
                 (alistp (boymoo-model::a64-registers
                           (boymoo-model::a64-write-reg register width use-sp value machine))))
        (implies (not (equal (car machine) :svc))
                 (not (equal (car (boymoo-model::a64-write-reg
                                   register width use-sp value machine))
                             :svc)))
        (implies (consp machine)
                 (consp (boymoo-model::a64-write-reg register width use-sp value machine))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc)))))

(local
 (defthm assembly-a64-set-nzcv-preserves-fields
   (and (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv flags machine))
               (boymoo-model::a64-pc machine))
        (equal (boymoo-model::a64-memory (boymoo-model::a64-set-nzcv flags machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-registers (boymoo-model::a64-set-nzcv flags machine))
               (boymoo-model::a64-registers machine))
        (equal (car (boymoo-model::a64-set-nzcv flags machine)) (car machine))
        (consp (boymoo-model::a64-set-nzcv flags machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc)))))

(local
 (defthm assembly-a64-set-pc-fields
   (and (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc address machine))
               (boymoo-model::a64-unsigned 64 address))
        (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc address machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-registers (boymoo-model::a64-set-pc address machine))
               (boymoo-model::a64-registers machine))
        (equal (car (boymoo-model::a64-set-pc address machine)) (car machine))
        (consp (boymoo-model::a64-set-pc address machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc boymoo-model::a64-set-pc)))))

(defun assembly-register-instruction-p (instruction)
  (member-eq (car instruction)
             '(:address :move-wide :arithmetic-imm :arithmetic-reg :logical-imm
               :logical-reg :bitfield :shift-variable :multiply :signed-multiply-high
               :multiply-subtract :divide :select :clz :ccmp)))

(defthm assembly-register-instruction-machine-effect
  (implies (assembly-register-instruction-p instruction)
           (let ((after (proof-execute instruction machine)))
             (and (consp after)
                  (implies (alistp (boymoo-model::a64-registers machine))
                           (alistp (boymoo-model::a64-registers after)))
                  (implies (not (equal (car machine) :svc))
                           (not (equal (car after) :svc)))
                  (equal (boymoo-model::a64-memory after)
                         (boymoo-model::a64-memory machine))
                  (equal (boymoo-model::a64-pc after)
                         (boymoo-model::a64-unsigned
                          64 (+ 4 (boymoo-model::a64-pc machine)))))))
  :hints (("Goal"
           :in-theory (disable boymoo-model::a64-write-reg boymoo-model::a64-set-nzcv
                               boymoo-model::a64-memory boymoo-model::a64-registers
                               boymoo-model::a64-condition
                               acl2::binary-logand acl2::binary-logior acl2::binary-logxor
                               logbitp integer-length truncate))))

(defthm assembly-register-instruction-no-data-access
  (implies (assembly-register-instruction-p instruction)
           (proof-instruction-access-p instruction world)))

(defthm assembly-register-instruction-world-effect
  (implies (and (assembly-register-instruction-p instruction)
                (not (equal (car (proof-world-machine world)) :svc)))
           (equal (proof-instruction-effect instruction world)
                  (update-nth 0 (proof-execute instruction (proof-world-machine world)) world)))
  :hints (("Goal"
           :use ((:instance assembly-register-instruction-machine-effect
                            (machine (proof-world-machine world))))
           :in-theory (disable assembly-register-instruction-p
                               assembly-register-instruction-machine-effect
                               proof-execute proof-linux-svc))))

(defthm assembly-register-instruction-world-fields
  (implies (and (assembly-register-instruction-p instruction)
                (not (equal (car (proof-world-machine world)) :svc)))
           (let ((after (proof-instruction-effect instruction world)))
             (and (implies (assembly-machine-registers-p world)
                           (assembly-machine-registers-p after))
                  (not (equal (car (proof-world-machine after)) :svc))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-pc after)
                         (boymoo-model::a64-unsigned 64 (+ 4 (proof-world-pc world)))))))
  :hints (("Goal"
           :use ((:instance assembly-register-instruction-machine-effect
                            (machine (proof-world-machine world))))
           :in-theory (disable assembly-register-instruction-p
                               assembly-register-instruction-machine-effect
                               proof-instruction-effect proof-execute))))

(defthm assembly-instruction-at-same-memory
  (implies (and (equal (proof-world-regions after) (proof-world-regions before))
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (boymoo-model::a64-memory (proof-world-machine before)))
                (proof-instruction-at-p instruction address before))
           (proof-instruction-at-p instruction address after))
  :hints (("Goal" :in-theory (disable proof-decode proof-fetchable-p
                                      boymoo-model::a64-read-bytes)
                  :expand ((proof-fetchable-p address before)
                           (proof-fetchable-p address after)))))

(defthm assembly-register-effect-keeps-instructions-placed
  (implies (and (assembly-register-instruction-p instruction)
                (not (equal (car (proof-world-machine world)) :svc))
                (proof-instruction-at-p placed address world))
           (proof-instruction-at-p placed address (proof-instruction-effect instruction world)))
  :hints (("Goal"
           :use (assembly-register-instruction-world-fields
                 (:instance assembly-instruction-at-same-memory
                            (before world) (instruction placed)
                            (after (proof-instruction-effect instruction world))))
           :in-theory (disable assembly-instruction-at-same-memory
                               assembly-register-instruction-world-fields
                               assembly-register-instruction-world-effect proof-execute
                               assembly-register-instruction-p
                               proof-instruction-at-p proof-instruction-effect
                               proof-world-machine proof-world-regions
                               boymoo-model::a64-memory))))

(defthm assembly-two-register-instructions-run
  (implies (and (assembly-register-instruction-p first)
                (assembly-register-instruction-p second)
                (not (equal (car (proof-world-machine before)) :svc))
                (proof-instructions-at-p (list first second) address before)
                (not (proof-world-stop before))
                (equal (proof-world-pc before) address)
                (natp address) (< (+ address 4) (expt 2 64))
                (not (member-equal address cuts))
                (not (member-equal (+ address 4) cuts))
                (member-equal (boymoo-model::a64-unsigned 64 (+ address 8)) cuts))
           (proof-segment-p 2 cuts before :cut
                            (assembly-straight-line-effect (list first second) before)))
  :hints (("Goal"
           :use ((:instance assembly-two-steps-to-cutpoint
                            (between (proof-instruction-effect first before))
                            (after (proof-instruction-effect
                                    second (proof-instruction-effect first before))))
                 (:instance assembly-register-instruction-world-fields
                            (instruction first) (world before))
                 (:instance assembly-register-instruction-world-fields
                            (instruction second) (world (proof-instruction-effect first before)))
                 (:instance assembly-register-effect-keeps-instructions-placed
                            (instruction first) (placed second) (world before)
                            (address (+ address 4))))
           :in-theory (disable assembly-two-steps-to-cutpoint assembly-straight-line-run
                               assembly-register-instruction-p proof-segment-p
                               assembly-register-instruction-world-fields
                               assembly-register-effect-keeps-instructions-placed
                               assembly-machine-registers-p proof-instruction-at-p
                               assembly-register-instruction-world-effect proof-execute
                               proof-instruction-effect proof-world-pc proof-world-stop
                               proof-world-machine member-equal))))
