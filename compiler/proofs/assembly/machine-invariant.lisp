(in-package "BOYMOO-PROOFS")

(include-book "image-execution")
(include-book "macho-link")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                           boymoo-model::a64-load boymoo-model::a64-ones
                           boymoo-model::a64-signed boymoo-model::a64-shift
                           boymoo-model::a64-result-flags boymoo-model::a64-condition
                           boymoo-model::a64-write-bytes boymoo-model::a64-register-offset
                           proof-decode-at proof-span-p proof-subspan-p proof-covered-p
                           proof-clear-memory proof-overlay-bytes proof-string-bytes
                           proof-instruction-access-p proof-remove-region-span
                           proof-region-disjoint-p proof-regions-p proof-page-size-p
                           proof-align-up mod ash logbitp logand logxor
                           acl2::binary-logand acl2::binary-logior acl2::binary-logxor)))

(defun assembly-register-file-p (machine)
  (alistp (boymoo-model::a64-registers machine)))

(local
 (defthm assembly-put-assoc-preserves-register-file
   (implies (alistp registers)
            (alistp (put-assoc-equal reg value registers)))))

(local
 (defthm assembly-register-file-of-register-write
   (implies (assembly-register-file-p machine)
            (assembly-register-file-p (boymoo-model::a64-write-reg reg width use-sp value machine)))))

(local
 (defthm assembly-register-file-of-other-state-field
   (implies (and (posp field) (assembly-register-file-p machine))
            (assembly-register-file-p (update-nth field value machine)))
   :hints (("Goal" :expand ((update-nth field value machine))))))

(local
 (defthm assembly-register-file-of-pc-write
   (implies (assembly-register-file-p machine)
            (assembly-register-file-p (boymoo-model::a64-set-pc pc machine)))))

(local
 (defthm assembly-register-file-of-flag-write
   (implies (assembly-register-file-p machine)
            (assembly-register-file-p (boymoo-model::a64-set-nzcv flags machine)))))

(local
 (defthm assembly-register-file-of-store
   (implies (assembly-register-file-p machine)
            (assembly-register-file-p (boymoo-model::a64-store width address value machine)))))

(local (in-theory (disable assembly-register-file-p boymoo-model::a64-set-pc
                           boymoo-model::a64-set-nzcv boymoo-model::a64-write-reg boymoo-model::a64-store)))

(defthm assembly-instruction-preserves-register-file
  (let ((next (proof-execute instruction machine)))
    (implies (and (assembly-register-file-p machine)
                  (not (eq (car instruction) :svc))
                  (not (eq next :undefined)))
             (assembly-register-file-p next)))
  :hints (("Goal" :do-not-induct t)))

(defthm assembly-register-file-cannot-mimic-svc
  (implies (assembly-register-file-p machine)
           (not (eq (car machine) :svc)))
  :hints (("Goal" :in-theory (enable assembly-register-file-p))))

(local
 (defthm assembly-executed-svc-is-an-event
   (implies (eq (car instruction) :svc)
            (eq (car (proof-execute instruction machine)) :svc))))

(local (in-theory (disable proof-execute boymoo-model::a64-execute)))

(defthm assembly-svc-event-identifies-instruction
  (implies (assembly-register-file-p machine)
           (equal (equal (car (proof-execute instruction machine)) :svc)
                  (equal (car instruction) :svc)))
  :hints (("Goal"
           :cases ((eq (car instruction) :svc) (eq (proof-execute instruction machine) :undefined))
           :use (assembly-executed-svc-is-an-event
                 assembly-instruction-preserves-register-file
                 (:instance assembly-register-file-cannot-mimic-svc
                            (machine (proof-execute instruction machine))))
           :in-theory (disable assembly-executed-svc-is-an-event
                               assembly-instruction-preserves-register-file
                               assembly-register-file-cannot-mimic-svc))))

(local
 (defthm assembly-register-file-of-svc-return
   (implies (assembly-register-file-p (proof-world-machine world))
            (assembly-register-file-p (proof-world-machine (proof-svc-return reply world))))))

(local (in-theory (disable proof-svc-return)))

(local
 (defthm assembly-world-machine-field-update
   (equal (proof-world-machine (update-nth field value world))
          (if (zp field) value (proof-world-machine world)))
   :hints (("Goal" :expand ((update-nth field value world))))))

(local (in-theory (disable proof-world-machine update-nth)))

(local
 (defthm assembly-register-file-of-linux-svc
   (implies (assembly-register-file-p (proof-world-machine world))
            (assembly-register-file-p (proof-world-machine (proof-linux-svc event world))))))

(local (in-theory (disable proof-linux-svc)))

(defthm assembly-checked-step-preserves-register-file
  (implies (assembly-register-file-p (proof-world-machine world))
           (assembly-register-file-p (proof-world-machine (proof-step world)))))

(local (in-theory (disable proof-step)))

(defthm assembly-checked-advance-preserves-register-file
  (implies (assembly-register-file-p (proof-world-machine world))
           (assembly-register-file-p (proof-world-machine (proof-advance count world)))))

(defthm assembly-checked-run-preserves-register-file
  (implies (assembly-register-file-p (proof-world-machine world))
           (assembly-register-file-p (proof-world-machine (mv-nth 1 (proof-run fuel cuts world))))))

(defthm assembly-loader-preserves-register-file
  (implies (assembly-register-file-p machine)
           (and (assembly-register-file-p
                 (proof-world-machine (proof-load-linux file machine regions page input replies)))
                (assembly-register-file-p
                 (proof-world-machine (assembly-load-macho-text file base machine regions input)))))
  :hints (("Goal"
           :in-theory (e/d (proof-world-machine)
                           (proof-elf-p assembly-macho-file-p assembly-macho-loader-input-p
                            assembly-macho-file-text)))))

(defthm assembly-valid-register-file-supplies-item-access
  (implies (assembly-register-file-p (proof-world-machine world))
           (iff (assembly-item-access-p instructions world)
                (proof-instruction-access-p (car instructions) world)))
  :hints (("Goal" :in-theory (disable proof-world-machine proof-instruction-access-p))))
