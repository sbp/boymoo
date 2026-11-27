(in-package "BOYMOO-PROOFS")

(include-book "leaf-routines")

(logic)
(set-verify-guards-eagerness 0)

; Published values depend on the bytes of the machine and their witnesses.
(defund p6-memory-equiv (first second)
  (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory second)))

(defequiv p6-memory-equiv
  :hints (("Goal" :in-theory (enable p6-memory-equiv))))

(defcong p6-memory-equiv equal (boymoo-model::a64-memory machine) 1
  :hints (("Goal" :in-theory (enable p6-memory-equiv))))

(defcong p6-memory-equiv equal (boymoo-model::a64-load count address machine) 3
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load))))

(defcong p6-memory-equiv equal (proof-load-word address machine) 2
  :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load))))

(defcong p6-memory-equiv equal (proof-byte-list count address machine) 3
  :hints (("Goal" :induct (proof-byte-list count address machine)
                  :in-theory (enable (:induction proof-byte-list)))))

(defcong p6-memory-equiv equal (proof-load-string count address machine) 3)

(defcong p6-memory-equiv equal (proof-limb-magnitude count address machine) 3
  :hints (("Goal" :induct (proof-limb-magnitude count address machine))))

(defcong p6-memory-equiv equal (proof-limbs-p count address machine) 3
  :hints (("Goal" :induct (proof-limbs-p count address machine))))

(defcong p6-memory-equiv equal (proof-integer-view address machine) 2)

(defcong p6-memory-equiv equal (proof-view-step kind input count depth base objects packages machine) 8
  :hints (("Goal"
           :induct (proof-view-step kind input count depth base objects packages machine)
           :in-theory (disable proof-limb-magnitude proof-limbs-p proof-integer-view
                               proof-load-string proof-load-word proof-pointer-address
                               proof-symbol-value proof-rational-value proof-complex-value
                               proof-cons-value proof-header-size proof-header-type
                               p6-even-as-mod p6-unsigned-one-as-parity))))

(defcong p6-memory-equiv equal (proof-view word base objects packages machine) 5)

(defcong p6-memory-equiv equal (proof-value-p word value base objects packages machine) 6)

(defcong p6-memory-equiv equal (proof-object-size object machine) 2)

(defcong p6-memory-equiv equal (proof-object-disjoint-p address end objects machine) 4
  :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine)
                  :in-theory (disable proof-object-size))))

(defcong p6-memory-equiv equal (proof-object-view object base objects packages machine) 5
  :hints (("Goal" :in-theory (disable proof-view))))

(defcong p6-memory-equiv equal (proof-symbol-object-p object machine) 2)

(defcong p6-memory-equiv equal (proof-object-map-p pending objects symbols base packages machine) 6
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                  :in-theory (disable proof-object-size proof-object-view proof-symbol-object-p
                                      proof-object-disjoint-p))))

(defcong p6-memory-equiv equal (proof-static-spans-p objects base size machine) 4
  :hints (("Goal" :induct (proof-static-spans-p objects base size machine)
                  :in-theory (disable proof-object-size))))

(defcong p6-memory-equiv equal (proof-static-size base machine) 2)

(defcong p6-memory-equiv equal (proof-home-bindings-p pending base objects packages machine buckets) 5
  :hints (("Goal" :induct (proof-home-bindings-p pending base objects packages machine buckets)
                  :in-theory (disable proof-static-binding proof-object-view proof-symbol-object-p
                                      proof-view proof-load-word))))

(defcong p6-memory-equiv equal (proof-static-p base objects packages machine) 4
  :hints (("Goal" :in-theory (disable proof-view proof-value-p proof-load-word proof-static-size
                                      proof-object-map-p proof-home-bindings-p proof-static-spans-p
                                      proof-static-objects proof-packages-p proof-static-buckets-p
                                      proof-package-bindings-p proof-package-row-views))))

(defcong p6-memory-equiv equal (proof-dynamic-symbol-objects-p pending objects entries base packages machine) 6
  :hints (("Goal" :induct (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
                  :in-theory (disable proof-symbol-object-p proof-object-view proof-view))))

(defcong p6-memory-equiv equal (proof-dynamic-root base machine) 2)

(defcong p6-memory-equiv equal (proof-external-bytes headers machine) 2
  :hints (("Goal" :induct (proof-external-bytes headers machine)
                  :in-theory (disable proof-load-word))))

(defcong p6-memory-equiv equal (proof-stack-views count address base objects packages machine) 6
  :hints (("Goal" :induct (proof-stack-views count address base objects packages machine)
                  :in-theory (disable proof-view proof-load-word))))

; The heap invariants use the memory, kernel environment, machine stack
; pointer and six registers that describe the live runtime storage.
(defund p6-heap-world-equiv (before after)
  (and (p6-memory-equiv (proof-world-machine before) (proof-world-machine after))
       (equal (cdr before) (cdr after))
       (equal (boymoo-model::a64-sp (proof-world-machine before))
              (boymoo-model::a64-sp (proof-world-machine after)))
       (equal (proof-world-reg 23 before) (proof-world-reg 23 after))
       (equal (proof-world-reg 24 before) (proof-world-reg 24 after))
       (equal (proof-world-reg 25 before) (proof-world-reg 25 after))
       (equal (proof-world-reg 26 before) (proof-world-reg 26 after))
       (equal (proof-world-reg 27 before) (proof-world-reg 27 after))
       (equal (proof-world-reg 28 before) (proof-world-reg 28 after))))

(defequiv p6-heap-world-equiv
  :hints (("Goal" :in-theory (enable p6-heap-world-equiv p6-memory-equiv))))

(defcong p6-heap-world-equiv p6-memory-equiv (proof-world-machine world) 1
  :hints (("Goal" :in-theory (enable p6-heap-world-equiv))))

(defthm p6-heap-world-equiv-selectors
  (implies (p6-heap-world-equiv before after)
           (and (p6-memory-equiv (proof-world-machine before) (proof-world-machine after))
                (equal (proof-world-reg 23 before) (proof-world-reg 23 after))
                (equal (proof-world-reg 24 before) (proof-world-reg 24 after))
                (equal (proof-world-reg 25 before) (proof-world-reg 25 after))
                (equal (proof-world-reg 26 before) (proof-world-reg 26 after))
                (equal (proof-world-reg 27 before) (proof-world-reg 27 after))
                (equal (proof-world-reg 28 before) (proof-world-reg 28 after))
                (equal (boymoo-model::a64-sp (proof-world-machine before))
                       (boymoo-model::a64-sp (proof-world-machine after)))
                (equal (proof-world-regions before) (proof-world-regions after))
                (equal (proof-world-input before) (proof-world-input after))
                (equal (proof-world-stdout before) (proof-world-stdout after))
                (equal (proof-world-stderr before) (proof-world-stderr after))
                (equal (proof-world-replies before) (proof-world-replies after))
                (equal (proof-world-page-size before) (proof-world-page-size after))
                (equal (proof-world-stop before) (proof-world-stop after))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable p6-heap-world-equiv proof-world-stop proof-world-regions))))

(in-theory (disable proof-world-input proof-world-stdout proof-world-stderr
                    proof-world-replies proof-world-page-size))

(defcong p6-heap-world-equiv equal (proof-runtime-word offset world) 2)

(defcong p6-heap-world-equiv equal (proof-heap-layout-p world) 1
  :hints (("Goal" :in-theory (disable proof-runtime-word proof-static-size
                                      proof-page-size-p proof-regions-p
                                      proof-align-up proof-disjoint-p))))

(defcong p6-heap-world-equiv equal (proof-external-objects head fuel world objects) 3
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                  :in-theory (disable (:definition proof-external-objects)
                                      proof-load-word proof-runtime-word proof-header-type
                                      proof-header-size proof-align-up proof-disjoint-p)
                  :expand ((:free (address state) (proof-external-objects address fuel state objects))))))

(defcong p6-heap-world-equiv equal (proof-heap-object-spans-p objects external world) 3
  :hints (("Goal" :induct (proof-heap-object-spans-p objects external world)
                  :in-theory (disable proof-runtime-word proof-object-size proof-subspan-p))))

(defcong p6-heap-world-equiv equal (proof-string-accounting-p headers world) 2
  :hints (("Goal" :in-theory (disable proof-runtime-word proof-external-bytes))))

(defcong p6-heap-world-equiv equal (proof-stack-prefix top world objects packages) 2
  :hints (("Goal" :in-theory (disable proof-runtime-word proof-stack-views))))

(defcong p6-heap-world-equiv equal (proof-dynamic-view world objects packages) 1
  :hints (("Goal" :in-theory (disable proof-view proof-dynamic-root))))

(defcong p6-heap-world-equiv equal (proof-heap-p world objects packages) 1
  :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p
                                      proof-external-objects proof-heap-object-spans-p
                                      proof-string-accounting-p proof-dynamic-entries proof-dynamic-view
                                      proof-dynamic-symbol-objects-p proof-stack-prefix
                                      proof-runtime-word))))

(defthm p6-frame-preserves-unlisted-register
  (implies (and (proof-register-frame-p max clobbers before after)
                (natp register) (natp max) (<= register max)
                (not (member-equal register clobbers)))
           (equal (proof-world-reg register before) (proof-world-reg register after)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-register-frame-p max clobbers before after))))

(defthm p6-read-only-frame-preserves-heap-state
  (implies (and (proof-frame-return-p clobbers flags before after)
                (p6-same-mapped-memory-p before after)
                (equal (cdr before) (cdr after))
                (not (intersectp-equal '(23 24 25 26 27 28) clobbers)))
           (p6-heap-world-equiv before after))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-heap-world-equiv p6-memory-equiv p6-same-mapped-memory-p)
           :use ((:instance p6-frame-preserves-unlisted-register (max 30) (register 23))
                 (:instance p6-frame-preserves-unlisted-register (max 30) (register 24))
                 (:instance p6-frame-preserves-unlisted-register (max 30) (register 25))
                 (:instance p6-frame-preserves-unlisted-register (max 30) (register 26))
                 (:instance p6-frame-preserves-unlisted-register (max 30) (register 27))
                 (:instance p6-frame-preserves-unlisted-register (max 30) (register 28))))))

(local
 (defthm p6-byte-entries-agree-reflexive
   (proof-byte-entries-agree-p entries start end memory memory)))

(defthm p6-memory-span-agrees-from-memory-equiv
  (implies (p6-memory-equiv (proof-world-machine before) (proof-world-machine after))
           (proof-memory-span-agrees-p start end before after))
  :hints (("Goal" :in-theory (enable p6-memory-equiv))))

(defthm p6-heap-frame-from-world-equiv
  (implies (p6-heap-world-equiv before after)
           (proof-heap-frame-p before after))
  :hints (("Goal" :in-theory (disable proof-memory-span-agrees-p proof-runtime-word
                                      proof-load-word proof-static-size))))

(local
 (defthm p6-external-spans-agree-from-memory-equiv
   (implies (p6-memory-equiv (proof-world-machine before) (proof-world-machine after))
            (proof-fixed-external-p mappings before after))
   :hints (("Goal" :induct (proof-fixed-external-p mappings before after)
                   :in-theory (disable proof-memory-span-agrees-p proof-load-word)))))

(defthm p6-fixed-heap-from-world-equiv
  (implies (and (p6-heap-world-equiv before after) (proof-heap-p before objects packages))
           (proof-fixed-heap-p before after objects))
  :hints (("Goal"
           :in-theory (disable proof-external-objects proof-memory-span-agrees-p proof-runtime-word
                               proof-heap-layout-p proof-static-p proof-object-map-p
                               proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                               proof-string-accounting-p proof-dynamic-view proof-dynamic-entries
                               proof-stack-prefix))))

(local
 (defthm p6-heap-has-stack-prefix
   (implies (proof-heap-p world objects packages)
            (proof-stack-prefix (proof-world-reg 25 world) world objects packages))
   :hints (("Goal"
            :in-theory (disable proof-external-objects proof-runtime-word
                                proof-heap-layout-p proof-static-p proof-object-map-p
                                proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                                proof-string-accounting-p proof-dynamic-view proof-dynamic-entries
                                proof-stack-prefix)))))

(defthm p6-preserved-heap-from-world-equiv
  (implies (and (p6-heap-world-equiv before after) (proof-heap-p before objects packages))
           (proof-preserved-heap-p nil before after objects objects packages))
  :hints (("Goal"
           :in-theory (disable proof-heap-p proof-heap-frame-p proof-external-objects proof-runtime-word
                               proof-heap-layout-p proof-static-p proof-object-map-p
                               proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                               proof-string-accounting-p proof-dynamic-view proof-dynamic-entries
                               proof-stack-prefix))))

(defthm p6-read-only-datum-return
  (let ((after (p6-path-end sites before)))
    (implies (and (p6-read-only-return-p word clobbers flags sites before)
                  (not (intersectp-equal '(23 24 25 26 27 28) clobbers))
                  (proof-heap-p before objects packages)
                  (proof-value-p word value (proof-heap-base before) objects packages
                                 (proof-world-machine before)))
             (proof-datum-return-p value clobbers flags nil nil before after objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance p6-read-only-frame-preserves-heap-state (after (p6-path-end sites before))))
           :in-theory (e/d (p6-read-only-return-p)
                           (p6-path-end proof-heap-p proof-frame-return-p proof-segment-p
                            proof-preserved-heap-p proof-fixed-heap-p proof-value-p)))))
