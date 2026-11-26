(in-package "BOYMOO-PROOFS")

(include-book "memory-footprints")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-unmasked-access-address (rn mode delta machine)
  (let ((base (boymoo-model::a64-read-reg rn 64 t machine)))
    (if (eq mode :post) base (+ base delta))))

(defun assembly-instruction-write-span (instruction machine)
  (let ((args (cdr instruction)))
    (case (car instruction)
      (:single
       (let* ((mode (nth 4 args))
              (offset (nth 5 args))
              (delta (if (eq mode :register)
                         (boymoo-model::a64-register-offset offset (nth 6 args) (nth 7 args) machine)
                       offset)))
         (and (not (equal (car args) 1))
              (cons (boymoo-model::a64-unsigned
                     64 (assembly-unmasked-access-address (nth 2 args) mode delta machine))
                    (nth 1 args)))))
      (:pair
       (and (not (car args))
            (cons (boymoo-model::a64-unsigned
                   64 (assembly-unmasked-access-address
                       (nth 1 args) (nth 4 args) (nth 5 args) machine))
                  16)))
      (otherwise nil))))

(local (in-theory (disable proof-covered-p proof-span-p proof-subspan-p
                           boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                           boymoo-model::a64-register-offset assembly-a64-unsigned-is-low
                           assembly-low ash mod floor logand logior logbitp)))

(defthm assembly-checked-access-covers-instruction-writes
  (let ((span (assembly-instruction-write-span instruction (proof-world-machine world))))
    (implies (and (proof-instruction-access-p instruction world) span)
             (proof-covered-p (car span) (cdr span) :write (proof-world-regions world)))))

(local
 (defthm assembly-memory-access-reads-registers-before-pc-change
   (equal (boymoo-model::a64-read-reg register width use-sp (boymoo-model::a64-set-pc value machine))
          (boymoo-model::a64-read-reg register width use-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))))

(local
 (defthm assembly-memory-offset-ignores-pc
   (equal (boymoo-model::a64-register-offset reg option shift (boymoo-model::a64-set-pc value machine))
          (boymoo-model::a64-register-offset reg option shift machine))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-register-offset)
                                   (boymoo-model::a64-signed boymoo-model::a64-shift
                                    boymoo-model::a64-set-pc))))))

(local (in-theory (disable boymoo-model::a64-set-pc boymoo-model::a64-write-reg
                           boymoo-model::a64-set-nzcv boymoo-model::a64-store
                           boymoo-model::a64-shift boymoo-model::a64-signed
                           boymoo-model::a64-condition boymoo-model::a64-byte
                           boymoo-model::a64-memory boymoo-model::a64-load
                           proof-instruction-access-p proof-execute boymoo-model::a64-execute)))

(local
 (defthm assembly-byte-of-store-register-effect
   (equal (boymoo-model::a64-load 1 address
               (boymoo-model::a64-write-reg register width use-sp value machine))
          (boymoo-model::a64-load 1 address machine))))

(local
 (defthm assembly-byte-of-store-pc-effect
   (equal (boymoo-model::a64-load 1 address (boymoo-model::a64-set-pc value machine))
          (boymoo-model::a64-load 1 address machine))))

(local
 (defthm assembly-byte-of-flag-update
   (equal (boymoo-model::a64-load 1 address (boymoo-model::a64-set-nzcv flags machine))
          (boymoo-model::a64-load 1 address machine))))

(local
 (defthm assembly-byte-of-data-processing-updates
   (and (equal (boymoo-model::a64-load
                1 address (boymoo-model::a64-exec-move-wide opc width rd imm position machine))
               (boymoo-model::a64-load 1 address machine))
        (equal (boymoo-model::a64-load
                1 address (boymoo-model::a64-exec-arithmetic opc width rd rn right immediate machine))
               (boymoo-model::a64-load 1 address machine))
        (equal (boymoo-model::a64-load
                1 address (boymoo-model::a64-exec-logical opc width rd rn right immediate machine))
               (boymoo-model::a64-load 1 address machine))
        (equal (boymoo-model::a64-load
                1 address (boymoo-model::a64-exec-bitfield opc width rd rn immr imms wmask tmask machine))
               (boymoo-model::a64-load 1 address machine)))
   :hints (("Goal" :in-theory (disable assembly-byte-load-is-memory-lookup
                                       boymoo-model::a64-result-flags)))))

(local
 (defthm assembly-signed-value-is-integer
   (integerp (boymoo-model::a64-signed width value))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-signed assembly-a64-unsigned-is-low)
                                   (expt))))
   :rule-classes :type-prescription))

(local
 (defthm assembly-effective-address-is-bounded
   (unsigned-byte-p 64 (boymoo-model::a64-unsigned 64 value))
   :hints (("Goal"
            :use ((:instance assembly-low-bounds (width 64)))
            :in-theory (enable assembly-a64-unsigned-is-low)))))

(local
 (defthm assembly-effective-address-is-natural
   (natp (boymoo-model::a64-unsigned 64 value))
   :hints (("Goal" :use (assembly-effective-address-is-bounded)))
   :rule-classes :type-prescription))

(local
 (defthm assembly-pair-store-keeps-disjoint-byte
   (let ((start (boymoo-model::a64-unsigned 64 pointer)))
     (implies (and (integerp pointer) (unsigned-byte-p 64 address)
                   (<= (+ start 16) (expt 2 64))
                   (or (< address start) (<= (+ start 16) address)))
              (equal (boymoo-model::a64-load
                      1 address (boymoo-model::a64-store
                                 8 (+ pointer 8) second
                                 (boymoo-model::a64-store 8 pointer first machine)))
                     (boymoo-model::a64-load 1 address machine))))
   :hints (("Goal" :use ((:instance assembly-effective-address-plus (base pointer) (offset 8))
                         (:instance assembly-model-store-writes-only-its-span
                                    (count 8) (value first))
                         (:instance assembly-model-store-writes-only-its-span
                                    (count 8) (pointer (+ pointer 8)) (value second)
                                    (machine (boymoo-model::a64-store 8 pointer first machine))))
                   :in-theory (disable assembly-model-store-writes-only-its-span
                                       assembly-byte-load-is-memory-lookup
                                       assembly-effective-address-plus)))))

(local
 (defthm assembly-read-register-bits-integer
   (integerp (boymoo-model::a64-read-reg register 64 use-sp machine))
   :hints (("Goal"
            :use ((:instance assembly-effective-address-is-bounded
                             (value (if (and (natp register) (< register 31))
                                        (cdr (assoc-equal register (boymoo-model::a64-registers machine)))
                                      (if (and (equal register 31) use-sp) (boymoo-model::a64-sp machine) 0)))))
            :in-theory (enable boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(defthm assembly-executing-instruction-keeps-bytes-outside-write-span
  (let* ((span (assembly-instruction-write-span instruction machine))
         (after (proof-execute instruction machine)))
    (implies (and (unsigned-byte-p 64 address)
                  (not (eq (car instruction) :svc))
                  (not (eq after :undefined))
                  (implies (eq (car instruction) :pair) (integerp (nth 6 instruction)))
                  (implies span
                           (and (proof-span-p (car span) (cdr span))
                                (or (< address (car span))
                                    (<= (+ (car span) (cdr span)) address)))))
             (equal (boymoo-model::a64-load 1 address after)
                    (boymoo-model::a64-load 1 address machine))))
  :hints (("Goal"
           :use ((:instance assembly-pair-store-keeps-disjoint-byte
                            (pointer (assembly-unmasked-access-address
                                      (nth 2 instruction) (nth 5 instruction) (nth 6 instruction) machine))
                            (first (boymoo-model::a64-read-reg (nth 3 instruction) 64 nil machine))
                            (second (boymoo-model::a64-read-reg (nth 4 instruction) 64 nil machine))
                            (machine (boymoo-model::a64-set-pc
                                      (+ 4 (boymoo-model::a64-pc machine)) machine))))
           :in-theory (e/d (proof-execute boymoo-model::a64-execute proof-span-p)
                           (assembly-register-instruction-machine-effect
                            assembly-pair-store-keeps-disjoint-byte
                            assembly-byte-load-is-memory-lookup
                            boymoo-model::a64-exec-move-wide boymoo-model::a64-exec-arithmetic
                            boymoo-model::a64-exec-logical boymoo-model::a64-exec-bitfield)))
          ("Goal'" :do-not-induct t))
  :rule-classes nil)

(local
 (defthm assembly-covered-write-has-span
   (implies (proof-covered-p address count :write regions)
            (proof-span-p address count))
   :hints (("Goal"
            :induct (proof-covered-p address count :write regions)
            :in-theory (enable proof-covered-p proof-subspan-p)))))

(defthm assembly-checked-instruction-preserves-protected-byte
  (let* ((machine (proof-world-machine world))
         (regions (proof-world-regions world))
         (after (proof-step world))
         (span (assembly-instruction-write-span instruction machine)))
    (implies (and (assembly-register-file-p machine)
                  (assembly-code-protected-p base size regions)
                  (proof-subspan-p address 1 base (+ base size))
                  (not (proof-world-stop world))
                  (not (eq (car instruction) :svc))
                  (implies (eq (car instruction) :pair) (integerp (nth 6 instruction)))
                  (proof-instruction-at-p instruction (proof-world-pc world) world)
                  (proof-instruction-access-p instruction world))
             (and (implies span (proof-span-p (car span) (cdr span)))
                  (equal (boymoo-model::a64-load 1 address (proof-world-machine after))
                         (boymoo-model::a64-load 1 address machine)))))
  :hints (("Goal"
           :use (proof-step-from-instruction
                 (:instance assembly-checked-access-covers-instruction-writes)
                 (:instance assembly-writable-span-disjoint-from-code
                            (code-base base) (code-end (+ base size))
                            (base (car (assembly-instruction-write-span
                                        instruction (proof-world-machine world))))
                            (size (cdr (assembly-instruction-write-span
                                        instruction (proof-world-machine world))))
                            (regions (proof-world-regions world)))
                 (:instance assembly-executing-instruction-keeps-bytes-outside-write-span
                            (machine (proof-world-machine world))))
           :in-theory (e/d (proof-subspan-p proof-span-p)
                           (assembly-instruction-write-span
                            assembly-checked-access-covers-instruction-writes
                            assembly-byte-load-is-memory-lookup
                            proof-instruction-at-p proof-step-from-instruction proof-step))))
  :rule-classes nil)
