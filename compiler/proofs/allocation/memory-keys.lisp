(in-package "BOYMOO-PROOFS")

(include-book "frame-composition")
(include-book "../foundations/loading")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-word-keys-after-assoc-write
   (implies (and (allocation-memory-addresses-are-words-p memory) (unsigned-byte-p 64 address))
            (allocation-memory-addresses-are-words-p (put-assoc-equal address value memory)))
   :hints (("Goal" :induct (put-assoc-equal address value memory)))))

(defthmd allocation-word-keys-after-byte-writes
  (implies (allocation-memory-addresses-are-words-p memory)
           (allocation-memory-addresses-are-words-p (boymoo-model::a64-write-bytes count address value memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
           :in-theory (e/d (boymoo-model::a64-write-bytes)
                           (put-assoc-equal boymoo-model::a64-unsigned)))))

(local
 (defthm allocation-machine-memory-of-slot-update
   (implies (natp slot)
            (equal (boymoo-model::a64-memory (update-nth slot value machine))
                   (if (equal slot 4) value (boymoo-model::a64-memory machine))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-memory)))))

(local
 (defthm allocation-world-memory-of-slot-update
   (implies (natp slot)
            (equal (allocation-memory (update-nth slot value world))
                   (if (equal slot 0) (boymoo-model::a64-memory value) (allocation-memory world))))
   :hints (("Goal" :in-theory (enable proof-world-machine allocation-memory)))))

(local (in-theory (disable update-nth boymoo-model::a64-memory allocation-memory-addresses-are-words-p)))

(local
 (defthm allocation-machine-control-updates-keep-memory
   (and (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc pc machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-memory (boymoo-model::a64-set-nzcv flags machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-memory (boymoo-model::a64-write-reg register width use-sp value machine))
               (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv boymoo-model::a64-write-reg)
                                  (boymoo-model::a64-unsigned put-assoc-equal))))))

(local
 (in-theory (disable boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv boymoo-model::a64-write-reg
                     boymoo-model::a64-read-reg boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-load boymoo-model::a64-condition boymoo-model::a64-result-flags)))

(local
 (defthm allocation-ordinary-register-instructions-keep-memory
   (and (equal (boymoo-model::a64-memory
                (boymoo-model::a64-exec-move-wide opc width rd imm position machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-memory
                (boymoo-model::a64-exec-arithmetic opc width rd rn right immediate machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-memory
                (boymoo-model::a64-exec-logical opc width rd rn right immediate machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-memory
                (boymoo-model::a64-exec-bitfield opc width rd rn immr imms wmask tmask machine))
               (boymoo-model::a64-memory machine))
        (equal (boymoo-model::a64-memory (boymoo-model::a64-exec-branch address link machine))
               (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-exec-move-wide boymoo-model::a64-exec-arithmetic
                                   boymoo-model::a64-exec-logical boymoo-model::a64-exec-bitfield
                                   boymoo-model::a64-exec-branch)
                                  (boymoo-model::a64-ones boymoo-model::a64-ror logand logxor logior logbitp))))))

(local
 (defthm allocation-a64-store-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
            (allocation-memory-addresses-are-words-p
             (boymoo-model::a64-memory (boymoo-model::a64-store count address value machine))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-store allocation-word-keys-after-byte-writes)
                                  (boymoo-model::a64-write-bytes))))))

(local
 (defthm allocation-load-store-instructions-keep-word-addresses
   (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
            (and (allocation-memory-addresses-are-words-p
                  (boymoo-model::a64-memory
                   (boymoo-model::a64-exec-single opc count rn rt mode offset option shift machine)))
                 (allocation-memory-addresses-are-words-p
                  (boymoo-model::a64-memory
                   (boymoo-model::a64-exec-pair load rn rt rt2 mode offset machine)))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-exec-single boymoo-model::a64-exec-pair)
                                  (boymoo-model::a64-store boymoo-model::a64-register-offset))))))

(local
 (in-theory (disable boymoo-model::a64-exec-move-wide boymoo-model::a64-exec-arithmetic
                     boymoo-model::a64-exec-logical boymoo-model::a64-exec-bitfield
                     boymoo-model::a64-exec-branch boymoo-model::a64-exec-single boymoo-model::a64-exec-pair
                     boymoo-model::a64-store)))

(local
 (defthm allocation-processor-events-have-empty-memory
   (and (equal (boymoo-model::a64-memory :undefined) nil)
        (equal (boymoo-model::a64-memory (list :svc immediate register16 register8)) nil))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-memory)))))

(local
 (defthm allocation-a64-instructions-keep-word-addresses
   (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
            (allocation-memory-addresses-are-words-p
             (boymoo-model::a64-memory (boymoo-model::a64-execute instruction machine))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-execute allocation-memory-addresses-are-words-p)
                                  (boymoo-model::a64-shift boymoo-model::a64-ones
                                   boymoo-model::a64-pc boymoo-model::a64-nzcv
                                   logxor logior logand mod))))))

(local
 (defthm allocation-model-instructions-keep-word-addresses
   (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
            (allocation-memory-addresses-are-words-p
             (boymoo-model::a64-memory (proof-execute instruction machine))))
   :hints (("Goal" :in-theory (e/d (proof-execute)
                                  (boymoo-model::a64-execute boymoo-model::a64-pc
                                   boymoo-model::a64-nzcv proof-reg))))))

(local
 (defthm allocation-clearing-memory-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p memory)
            (allocation-memory-addresses-are-words-p (proof-clear-memory start end memory)))
   :hints (("Goal" :induct (proof-clear-memory start end memory)
            :in-theory (enable allocation-memory-addresses-are-words-p)))))

(local
 (defthm allocation-byte-overlay-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p memory)
            (allocation-memory-addresses-are-words-p (proof-overlay-bytes bytes address memory omit-zero)))
   :hints (("Goal" :induct (proof-overlay-bytes bytes address memory omit-zero)
            :in-theory (e/d (proof-overlay-bytes allocation-memory-addresses-are-words-p)
                            (boymoo-model::a64-unsigned))))))

(local
 (defthm allocation-clear-span-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p (allocation-memory world))
            (allocation-memory-addresses-are-words-p (allocation-memory (proof-clear-span start end world))))
   :hints (("Goal" :in-theory (disable proof-clear-memory proof-world-machine)))))

(local
 (defthm allocation-svc-return-keeps-memory
   (equal (allocation-memory (proof-svc-return reply world)) (allocation-memory world))
   :hints (("Goal" :in-theory (disable proof-world-machine proof-world-pc)))))

(local
 (defthm allocation-store-input-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
            (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory (proof-store-bytes bytes address machine))))
   :hints (("Goal" :in-theory (e/d (proof-store-bytes) (proof-overlay-bytes))))))

(local
 (defthm allocation-linux-services-keep-word-addresses
   (implies (allocation-memory-addresses-are-words-p (allocation-memory world))
            (and (allocation-memory-addresses-are-words-p (allocation-memory (proof-linux-map reply world)))
                 (allocation-memory-addresses-are-words-p (allocation-memory (proof-linux-release unmap reply world)))
                 (allocation-memory-addresses-are-words-p (allocation-memory (proof-linux-read reply world)))
                 (allocation-memory-addresses-are-words-p (allocation-memory (proof-linux-write reply world)))))
   :hints (("Goal" :in-theory (disable proof-svc-return proof-clear-span proof-remove-region-span proof-region-disjoint-p
                                      proof-store-bytes proof-world-reg proof-world-input proof-world-machine
                                      proof-page-size-p proof-align-up proof-covered-p proof-linux-errno-p
                                      proof-byte-list mod)))))

(local
 (defthm allocation-linux-svc-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p (allocation-memory world))
            (allocation-memory-addresses-are-words-p (allocation-memory (proof-linux-svc event world))))
   :hints (("Goal" :in-theory (disable proof-linux-map proof-linux-release proof-linux-read proof-linux-write
                                      proof-world-reg proof-world-replies)))))

(defthm allocation-step-preserves-word-address-keys
  (implies (allocation-memory-addresses-are-words-p (allocation-memory world))
           (allocation-memory-addresses-are-words-p (allocation-memory (proof-step world))))
  :hints (("Goal"
           :in-theory (e/d (proof-step proof-instruction-effect)
                           (proof-execute proof-fetchable-p proof-instruction-access-p proof-decode-at proof-linux-svc
                            proof-world-pc proof-world-stop proof-world-machine)))))

(defthm allocation-executed-prefix-preserves-word-address-keys
  (implies (and (allocation-memory-addresses-are-words-p (allocation-memory before))
                (allocation-prefix-p steps cuts before after))
           (allocation-memory-addresses-are-words-p (allocation-memory after)))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-prefix-p steps cuts before after)
           :in-theory (disable proof-step))))

(defthm allocation-checked-path-preserves-word-address-keys
  (implies (and (allocation-memory-addresses-are-words-p (allocation-memory before))
                (allocation-path-ready-p path cuts before))
           (allocation-memory-addresses-are-words-p (allocation-memory (allocation-path-end path before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-prefix-from-path)
                 (:instance allocation-executed-prefix-preserves-word-address-keys
                   (steps (len path)) (after (allocation-path-end path before))))
           :in-theory (disable allocation-path-ready-p allocation-path-end allocation-prefix-p))))

(local
 (defthm allocation-loaded-image-keeps-word-addresses
   (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
            (allocation-memory-addresses-are-words-p
             (boymoo-model::a64-memory (proof-load-cleared-string file address machine))))
   :hints (("Goal" :in-theory (disable proof-overlay-bytes proof-string-bytes)))))

(local
 (defthm allocation-world-memory-from-construction
   (equal (allocation-memory (proof-world machine regions page input stdout stderr replies stop))
          (boymoo-model::a64-memory machine))
   :hints (("Goal" :in-theory (enable proof-world proof-world-machine allocation-memory)))))

(local
 (defthm allocation-empty-world-has-word-address-keys
   (allocation-memory-addresses-are-words-p (allocation-memory nil))
   :hints (("Goal" :in-theory (enable allocation-memory proof-world-machine boymoo-model::a64-memory
                                      allocation-memory-addresses-are-words-p)))))

(defthm allocation-linux-loader-keeps-word-address-keys
  (implies (allocation-memory-addresses-are-words-p (boymoo-model::a64-memory machine))
           (allocation-memory-addresses-are-words-p
            (allocation-memory (proof-load-linux file machine regions page input replies))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-load-linux)
                           (proof-elf-p proof-elf-entry proof-covered-p proof-region-disjoint-p
                            proof-regions-p proof-page-size-p proof-align-up proof-clear-memory
                            proof-load-cleared-string proof-world proof-string-bytes boymoo-model::a64-sp mod)))))
