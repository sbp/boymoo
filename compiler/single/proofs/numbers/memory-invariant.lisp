(in-package "BOYMOO-PROOFS")

(include-book "fresh-views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-load boymoo-model::a64-write-bytes
                     boymoo-model::a64-read-reg boymoo-model::a64-pc
                     boymoo-model::a64-nzcv boymoo-model::a64-sp
                     boymoo-model::a64-condition boymoo-model::a64-shift
                     boymoo-model::a64-result-flags boymoo-model::a64-ones
                     boymoo-model::a64-memory proof-number-memory-byte-keys-p
                     proof-reg proof-world-reg proof-world-pc proof-world-stop
                     proof-decode-at proof-elf-p proof-covered-p
                     proof-instruction-access-p proof-fetchable-p
                     floor mod ash acl2::binary-logand acl2::binary-logior)))

(defund proof-number-world-byte-keys-p (world)
  (proof-number-memory-byte-keys-p
   (boymoo-model::a64-memory (proof-world-machine world))))

(local
 (defthm memory-of-update
   (equal (boymoo-model::a64-memory (update-nth slot value machine))
          (if (equal (nfix slot) 4) value (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-memory)))))

(local
 (defthm world-machine-of-update
   (equal (proof-world-machine (update-nth slot value world))
          (if (zp slot) value (proof-world-machine world)))
   :hints (("Goal" :in-theory (enable proof-world-machine)))))

(local
 (in-theory (disable (:definition nth) (:definition update-nth))))

(local
 (defthm memory-of-any-width-register-write
   (equal (boymoo-model::a64-memory (boymoo-model::a64-write-reg dest width use-sp value machine))
          (boymoo-model::a64-memory machine))))

(local
 (in-theory (disable boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-set-nzcv)))

(local
 (defthm byte-keys-after-machine-store
   (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
            (proof-number-memory-byte-keys-p
             (boymoo-model::a64-memory (boymoo-model::a64-store width address value machine))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store)))))

(local
 (defthm memory-of-branch
   (equal (boymoo-model::a64-memory (boymoo-model::a64-exec-branch target link machine))
          (boymoo-model::a64-memory machine))))

(local
 (defthm memory-of-arithmetic
   (equal (boymoo-model::a64-memory
           (boymoo-model::a64-exec-arithmetic opc width dest source value immediate machine))
          (boymoo-model::a64-memory machine))))

(local
 (defthm memory-of-logical
   (equal (boymoo-model::a64-memory
           (boymoo-model::a64-exec-logical opc width dest source value immediate machine))
          (boymoo-model::a64-memory machine))))

(local
 (defthm memory-of-bitfield
   (equal (boymoo-model::a64-memory
           (boymoo-model::a64-exec-bitfield opc width dest source immr imms wmask tmask machine))
          (boymoo-model::a64-memory machine))))

(local
 (defthm memory-of-move-wide
   (equal (boymoo-model::a64-memory
           (boymoo-model::a64-exec-move-wide opc width dest imm position machine))
          (boymoo-model::a64-memory machine))))

(local
 (defthm byte-keys-after-single-access
   (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
            (proof-number-memory-byte-keys-p
             (boymoo-model::a64-memory
              (boymoo-model::a64-exec-single opc width base dest mode offset option shift machine))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-store boymoo-model::a64-write-reg)))))

(local
 (defthm byte-keys-after-pair-access
   (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
            (proof-number-memory-byte-keys-p
             (boymoo-model::a64-memory
              (boymoo-model::a64-exec-pair load base first second mode delta machine))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-store boymoo-model::a64-write-reg)))))

(local
 (in-theory (disable boymoo-model::a64-exec-branch boymoo-model::a64-exec-arithmetic
                     boymoo-model::a64-exec-logical boymoo-model::a64-exec-bitfield
                     boymoo-model::a64-exec-move-wide boymoo-model::a64-exec-single
                     boymoo-model::a64-exec-pair boymoo-model::a64-store
                     boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-set-nzcv)))

(local
 (defthm byte-keys-after-model-execute
   (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
            (proof-number-memory-byte-keys-p
             (boymoo-model::a64-memory (boymoo-model::a64-execute instruction machine))))
   :hints (("Goal" :in-theory (disable (:definition nth)))
           (and stable-under-simplificationp
                '(:in-theory (enable boymoo-model::a64-memory proof-number-memory-byte-keys-p))))))

(local
 (defthm byte-keys-after-cpu-execute
   (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
            (proof-number-memory-byte-keys-p
             (boymoo-model::a64-memory (proof-execute instruction machine))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-execute)))))

(local
 (defthm byte-keys-after-clear
   (implies (proof-number-memory-byte-keys-p memory)
            (proof-number-memory-byte-keys-p (proof-clear-memory start end memory)))
   :hints (("Goal" :induct (proof-clear-memory start end memory)
                   :in-theory (enable proof-number-memory-byte-keys-p)))))

(local
 (defthm byte-keys-after-overlay
   (implies (proof-number-memory-byte-keys-p memory)
            (proof-number-memory-byte-keys-p
             (proof-overlay-bytes bytes address memory omit-zero)))
   :hints (("Goal" :induct (proof-overlay-bytes bytes address memory omit-zero)
                   :in-theory (enable proof-number-memory-byte-keys-p)))))

(local
 (defthm byte-keys-after-svc
   (implies (proof-number-world-byte-keys-p world)
            (proof-number-world-byte-keys-p (proof-linux-svc instruction world)))
   :hints (("Goal" :in-theory (e/d (proof-number-world-byte-keys-p)
                                  (proof-clear-memory proof-overlay-bytes proof-byte-list
                                   proof-align-up proof-regions-p proof-region-disjoint-p
                                   proof-remove-region-span (:definition nth)))
            :do-not-induct t))))

(defthm proof-number-step-preserves-byte-keys
  (implies (proof-number-world-byte-keys-p world)
           (proof-number-world-byte-keys-p (proof-step world)))
  :hints (("Goal"
           :use ((:instance byte-keys-after-svc
                            (instruction (proof-execute
                                          (proof-decode-at (proof-world-pc world)
                                                           (proof-world-machine world))
                                          (proof-world-machine world)))))
           :in-theory (e/d (proof-number-world-byte-keys-p)
                           (proof-execute proof-linux-svc (:definition nth))))))

(defthm proof-number-advance-preserves-byte-keys
  (implies (proof-number-world-byte-keys-p world)
           (proof-number-world-byte-keys-p (proof-advance count world)))
  :hints (("Goal" :induct (proof-advance count world) :in-theory (disable proof-step))))

(defthm proof-number-load-linux-preserves-byte-keys
  (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
           (proof-number-world-byte-keys-p (proof-load-linux file machine regions page input replies)))
  :hints (("Goal" :in-theory (e/d (proof-number-world-byte-keys-p)
                                 (proof-clear-memory proof-overlay-bytes proof-align-up
                                  proof-regions-p proof-region-disjoint-p
                                  proof-string-bytes)))
          (and stable-under-simplificationp
               '(:in-theory (enable boymoo-model::a64-memory proof-number-memory-byte-keys-p))))
  :rule-classes nil)
