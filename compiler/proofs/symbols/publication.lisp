(in-package "BOYMOO-PROOFS")

(include-book "loops")
(include-book "memory")
(include-book "intern-call")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-view proof-view-step proof-load-word
                     proof-pointer-address proof-word-tag proof-header-size proof-header-type
                     boymoo-model::a64-unsigned boymoo-model::a64-signed
                     symbols-path-ready-p symbols-runtime-offset symbols-no-memory-or-kernel-change-p
                     symbols-intern-initialized-world symbols-intern-initialize-frame-p)))

(local
 (defthm symbols-publication-register-is-natural
   (natp (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-publication-register-fits
   (equal (boymoo-model::a64-unsigned 64 (proof-world-reg register world)) (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-publication-load-is-word
   (equal (symbols-load-register-word address world) (proof-load-word address (proof-world-machine world)))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word symbols-word-load-fits proof-load-word)
                                   (boymoo-model::a64-load))))))

(local
 (defthm symbols-publication-loaded-word-fits
   (equal (boymoo-model::a64-unsigned 64 (proof-load-word address machine))
          (proof-load-word address machine))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits proof-load-word) (boymoo-model::a64-load))))))

(defun symbols-intern-initial-fields-p (before after)
  (let* ((symbol (proof-world-reg 0 before))
         (entry (+ 24 symbol))
         (machine (proof-world-machine after))
         (stack (symbols-intern-popped-stack-top before)))
    (and (equal (proof-load-word symbol machine) 4098)
         (equal (proof-load-word (+ symbol 8) machine) (symbols-load-register-word stack before))
         (equal (proof-load-word (+ symbol 16) machine) (proof-world-reg 20 before))
         (equal (proof-load-word entry machine) 6150)
         (equal (proof-load-word (+ entry 8) machine) (symbols-box-word symbol (proof-heap-base before)))
         (equal (proof-load-word (+ entry 16) machine) (proof-world-reg 22 before)))))

(local
 (defthm symbols-publication-machine-of-replacement
   (equal (car (update-nth 0 machine world)) machine)
   :hints (("Goal" :expand ((update-nth 0 machine world))))))

(local
 (defthm symbols-intern-initialization-stores-establish-fields
   (implies (<= (+ 56 (proof-world-reg 0 before)) (expt 2 64))
            (symbols-intern-initial-fields-p before (symbols-intern-initialized-world before)))
   :hints (("Goal"
            :in-theory (e/d (symbols-intern-initialized-world proof-world-machine)
                            (symbols-intern-popped-stack-top
                             boymoo-model::a64-store update-nth))))
   :rule-classes nil))

(local
 (defthm symbols-intern-initialized-fields-of-same-memory
   (implies (equal (symbols-machine-memory first) (symbols-machine-memory last))
            (equal (symbols-intern-initial-fields-p before first) (symbols-intern-initial-fields-p before last)))
   :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load)))
   :rule-classes nil))

(defthm symbols-run-intern-initializes-fields
  (let ((after (proof-advance (len *symbols-intern-initialize-path*) before)))
    (implies (and (symbols-intern-initialize-pre-p code-base before)
                  (symbols-path-ready-p *symbols-intern-initialize-path* code-base
                                        (symbols-runtime-address "rt:intern-bucket-address" code-base) before)
                  (proof-reserved-span-p :header (proof-world-reg 0 before) 56 before objects))
             (symbols-intern-initial-fields-p before after)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-initialize)
                 (:instance symbols-intern-initialization-stores-establish-fields)
                 (:instance symbols-intern-initialized-fields-of-same-memory
                            (first (symbols-intern-initialized-world before))
                            (last (proof-advance (len *symbols-intern-initialize-path*) before))))
           :in-theory (e/d (symbols-intern-initialize-frame-p symbols-no-memory-or-kernel-change-p)
                           (symbols-intern-initial-fields-p proof-object-disjoint-p symbols-box-address
                            symbols-intern-popped-stack-top symbols-box-word))))
  :rule-classes nil)

(defun symbols-word-below-rank-p (word depth base objects)
  (< (nfix (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))) depth))

(local
 (defthm symbols-publication-read-at-rank
   (implies (and (natp depth) (symbols-word-below-rank-p word depth base objects))
            (equal (proof-view-step :word word 0 depth base objects packages machine)
                   (proof-view word base objects packages machine)))
   :hints (("Goal"
            :expand ((proof-view word base objects packages machine)
                     (:free (rank) (proof-view-step :word word 0 rank base objects packages machine)))
            :in-theory (disable proof-symbol-value proof-integer-view proof-cons-value
                                proof-rational-value proof-complex-value proof-load-string proof-span-p
                                proof-object-rank proof-object-kind assoc-equal ash floor mod)))
   :rule-classes nil))

; A symbol record ranks above its two fields. The fields give the
; source name and the package index independently of the word address.
(defun symbols-ranked-symbol-fields-p (word name number base objects packages machine)
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object))
         (name-word (proof-load-word (+ address 8) machine))
         (package-word (proof-load-word (+ address 16) machine)))
    (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2)
         object (eq (proof-object-kind object) :header) (natp rank)
         (proof-span-p address 24)
         (equal (proof-load-word address machine) 4098)
         (symbols-word-below-rank-p name-word rank base objects)
         (symbols-word-below-rank-p package-word rank base objects)
         (proof-value-p name-word name base objects packages machine)
         (proof-value-p package-word number base objects packages machine))))

(local
 (defthm symbols-publication-boxed-word-is-even
   (implies (and (integerp word) (equal (proof-word-tag word) 2)) (evenp word))
   :hints (("Goal"
            :use ((:instance symbols-mod-of-nested-mod (x word) (factor 4) (divisor 2))
                  (:instance symbols-unsigned-as-mod (width 3) (x word)))
            :cases ((equal (* 1/2 word) (floor word 2)))
            :in-theory (e/d (proof-word-tag) (symbols-mod-of-nested-mod floor))))))

(defthm symbols-ranked-symbol-fields-give-view
  (implies (symbols-ranked-symbol-fields-p word name number base objects packages machine)
           (equal (proof-view word base objects packages machine)
                  (proof-symbol-value (proof-value-view name) (proof-value-view number) packages)))
  :hints (("Goal"
           :use ((:instance symbols-publication-boxed-word-is-even)
                 (:instance symbols-publication-read-at-rank
                            (word (proof-load-word (+ 8 (proof-pointer-address word base)) machine))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance symbols-publication-read-at-rank
                            (word (proof-load-word (+ 16 (proof-pointer-address word base)) machine))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))
           :expand ((proof-view word base objects packages machine)
                    (:free (rank) (proof-view-step :word word 0 rank base objects packages machine)))
           :in-theory (e/d ((:executable-counterpart proof-header-type) (:executable-counterpart proof-header-size))
                           (symbols-word-below-rank-p symbols-publication-boxed-word-is-even
                            proof-symbol-value proof-integer-view proof-cons-value proof-rational-value
                            proof-complex-value proof-load-string proof-span-p proof-object-rank proof-object-kind
                            assoc-equal ash mod floor))))
  :rule-classes nil)

(local
 (defthm symbols-publication-associated-package-has-key-name
   (implies (assoc-equal name packages)
            (equal (proof-package-name (assoc-equal name packages)) name))
   :hints (("Goal" :induct (assoc-equal name packages)))))

(defthm symbols-ranked-home-symbol-implements-core-interning
  (let* ((package (acl2::symbol-package-name designator))
         (number (proof-package-number package packages 0))
         (result (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol (list name designator) program)))
    (implies (and (stringp name) (symbolp designator) (natp number)
                  (proof-immediate-integer-p number)
                  (proof-packages-p packages) (proof-package-bindings-p packages 0 buckets)
                  (not (proof-static-binding number name buckets))
                  (symbols-ranked-symbol-fields-p word name number base objects packages machine))
             (and (boymoo-model::core-value-p result)
                  (proof-value-p word (boymoo-model::core-datum result) base objects packages machine))))
  :hints (("Goal"
           :use ((:instance symbols-ranked-symbol-fields-give-view
                            (number (proof-package-number (acl2::symbol-package-name designator) packages 0)))
                 (:instance symbols-intern-on-static-miss-is-home)
                 (:instance symbols-package-number-range
                            (name (acl2::symbol-package-name designator)) (first 0))
                 (:instance symbols-package-number-selects-row
                            (name (acl2::symbol-package-name designator)) (first 0))
                 (:instance symbols-row-witness-fields (name (acl2::symbol-package-name designator)))
                 (:instance symbols-publication-associated-package-has-key-name
                            (name (acl2::symbol-package-name designator)))
                 (:instance symbols-package-number-present (name (acl2::symbol-package-name designator)) (first 0))
                 (:instance symbols-intern-in-same-package (x designator)
                            (y (proof-package-witness (assoc-equal (acl2::symbol-package-name designator) packages)))))
           :in-theory (e/d (boymoo-model::core-primitive)
                           (symbols-ranked-symbol-fields-p proof-package-number proof-package-bindings-p
                            proof-static-binding proof-packages-p symbols-package-number-selects-row
                            symbols-package-number-present symbols-row-witness-fields assoc-equal
                            symbols-publication-associated-package-has-key-name))))
  :rule-classes nil)

(defun symbols-intern-initialized-symbol-ranks-p (before after objects)
  (let* ((address (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (word (symbols-box-word address base))
         (record (assoc-equal address objects))
         (rank (proof-object-rank record)))
    (and (equal (proof-word-tag word) 2)
         (equal (proof-pointer-address word base) address)
         record (eq (proof-object-kind record) :header) (natp rank)
         (symbols-word-below-rank-p
          (symbols-load-register-word (symbols-intern-popped-stack-top before) before) rank base objects)
         (symbols-word-below-rank-p (proof-world-reg 20 before) rank base objects)
         (equal (proof-heap-base after) base))))

(local
 (defthm symbols-intern-boxed-word-fits-register
   (< (symbols-box-word address base) (expt 2 64))
   :hints (("Goal" :in-theory (enable symbols-box-word)))
   :rule-classes :linear))

(local
 (defthm symbols-intern-fields-from-reserved-symbol
   (let ((name-word (symbols-load-register-word (symbols-intern-popped-stack-top before) before))
         (base (proof-heap-base before))
         (machine (proof-world-machine after)))
     (implies (and (symbols-intern-initial-fields-p before after)
                   (symbols-intern-initialized-symbol-ranks-p before after new-objects)
                   (proof-span-p (proof-world-reg 0 before) 56)
                   (proof-value-p name-word name base new-objects packages machine)
                   (proof-value-p (proof-world-reg 20 before) number base new-objects packages machine))
              (symbols-ranked-symbol-fields-p (symbols-box-word (proof-world-reg 0 before) base)
                                               name number base new-objects packages machine)))
   :hints (("Goal"
            :in-theory (disable symbols-word-below-rank-p symbols-box-word symbols-intern-popped-stack-top
                                proof-value-p proof-object-rank proof-object-kind assoc-equal)))
   :rule-classes nil))

(defthm symbols-intern-prepared-symbol-represents-core-result
  (let* ((after (proof-advance (len *symbols-intern-initialize-path*) before))
         (number (proof-package-number (acl2::symbol-package-name designator) packages 0))
         (result (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol (list name designator) program))
         (base (proof-heap-base before))
         (machine (proof-world-machine after))
         (name-word (symbols-load-register-word (symbols-intern-popped-stack-top before) before)))
    (implies (and (symbols-intern-initialize-pre-p code-base before)
                  (symbols-path-ready-p *symbols-intern-initialize-path* code-base
                                        (symbols-runtime-address "rt:intern-bucket-address" code-base) before)
                  (proof-reserved-span-p :header (proof-world-reg 0 before) 56 before old-objects)
                  (symbols-intern-initialized-symbol-ranks-p before after new-objects)
                  (proof-value-p name-word name base new-objects packages machine)
                  (proof-value-p (proof-world-reg 20 before) number base new-objects packages machine)
                  (stringp name) (symbolp designator) (natp number) (proof-immediate-integer-p number)
                  (proof-packages-p packages) (proof-package-bindings-p packages 0 buckets)
                  (not (proof-static-binding number name buckets)))
             (proof-reg-value-p 5 (boymoo-model::core-datum result) after new-objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-initializes-fields (objects old-objects))
                 (:instance symbols-run-intern-initialize)
                 (:instance symbols-intern-fields-from-reserved-symbol
                            (after (proof-advance (len *symbols-intern-initialize-path*) before))
                            (number (proof-package-number (acl2::symbol-package-name designator) packages 0)))
                 (:instance symbols-ranked-home-symbol-implements-core-interning
                            (word (symbols-box-word (proof-world-reg 0 before) (proof-heap-base before)))
                            (base (proof-heap-base before)) (objects new-objects)
                            (machine (proof-world-machine (proof-advance (len *symbols-intern-initialize-path*) before)))))
           :in-theory (e/d (symbols-intern-initialize-frame-p)
                           (symbols-intern-initial-fields-p symbols-ranked-symbol-fields-p
                            symbols-intern-initialized-world symbols-box-word symbols-box-address
                            symbols-intern-popped-stack-top proof-value-p
                            proof-static-binding proof-packages-p proof-package-bindings-p proof-package-number
                            proof-object-disjoint-p boymoo-model::core-primitive))))
  :rule-classes nil)

(defun symbols-intern-initialized-state (before)
  (proof-advance (len *symbols-intern-initialize-path*) before))

(defun symbols-intern-publication-entry (before)
  (proof-advance (len *symbols-bucket-address-path*) (symbols-intern-initialized-state before)))

(defun symbols-intern-publication-finish (before)
  (proof-advance (len *symbols-intern-publish-path*) (symbols-intern-publication-entry before)))

(defun symbols-intern-publication-ready-p (base before)
  (let ((initialized (symbols-intern-initialized-state before))
        (entry (symbols-intern-publication-entry before)))
    (and (symbols-path-ready-p *symbols-intern-initialize-path* base
                               (symbols-runtime-address "rt:intern-bucket-address" base) before)
         (symbols-path-ready-p *symbols-bucket-address-path* base (proof-world-reg 30 initialized) initialized)
         (symbols-path-ready-p *symbols-intern-publish-path* base (symbols-runtime-address "rt:intern-return" base) entry))))

(defconst *symbols-intern-publication-clobbers* '(0 1 2 3 4 5 9 25 30))

(defun symbols-intern-publication-frame-p (base before entry after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-return" base))
       (equal (proof-world-reg 0 after) (symbols-box-word (proof-world-reg 0 before) (proof-heap-base before)))
       (equal (proof-world-reg 25 after) (symbols-intern-popped-stack-top before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 *symbols-intern-publication-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p (symbols-intern-linked-world entry) after)))

(local
 (defthm symbols-intern-publication-frames-compose
   (implies (and (symbols-intern-initialize-frame-p base before initialized)
                 (proof-frame-return-p '(3 4) nil initialized entry)
                 (symbols-intern-publish-frame-p base entry after))
            (symbols-intern-publication-frame-p base before entry after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 5)
                             (clobbers '(3 4)) (before initialized) (after entry))
                  (:instance symbols-frame-gives-register (highest 30) (register 25)
                             (clobbers '(3 4)) (before initialized) (after entry))
                  (:instance symbols-frame-gives-register (highest 30) (register 25)
                             (clobbers '(0 3)) (before entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(0 1 2 5 9 25 30))
                             (allowed *symbols-intern-publication-clobbers*) (after initialized))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(3 4))
                             (allowed *symbols-intern-publication-clobbers*) (before initialized) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(0 3))
                             (allowed *symbols-intern-publication-clobbers*) (before entry))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-publication-clobbers*)
                             (first before) (middle initialized) (last entry))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-publication-clobbers*)
                             (first before) (middle entry) (last after)))
            :in-theory (e/d (symbols-intern-initialize-frame-p)
                            (symbols-intern-linked-world symbols-intern-entry-location
                             symbols-box-address symbols-box-word symbols-intern-popped-stack-top))))
   :rule-classes nil))

(defthm symbols-run-intern-publication-from-reserved-span
  (implies (and (symbols-intern-initialize-pre-p code-base before)
                (symbols-intern-publication-ready-p code-base before))
           (symbols-intern-publication-frame-p code-base before (symbols-intern-publication-entry before)
                                                (symbols-intern-publication-finish before)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-initialize)
                 (:instance symbols-run-bucket-address (before (symbols-intern-initialized-state before)))
                 (:instance symbols-run-intern-publish (before (symbols-intern-publication-entry before)))
                 (:instance symbols-intern-publication-frames-compose (base code-base)
                            (initialized (symbols-intern-initialized-state before))
                            (entry (symbols-intern-publication-entry before))
                            (after (symbols-intern-publication-finish before))))
           :in-theory (e/d (symbols-intern-initialize-frame-p)
                           (symbols-intern-publication-frame-p symbols-intern-publish-frame-p proof-segment-p
                            symbols-dynamic-bucket-address symbols-intern-initialized-world symbols-box-address
                            symbols-run-bucket-address symbols-intern-popped-stack-top))))
  :rule-classes nil)

(defconst *symbols-intern-unpopped-clobbers*
  (append *symbols-intern-temporary-clobbers* '(25)))

(defun symbols-intern-fresh-finish (reserved)
  (proof-advance (len *symbols-intern-return-path*) (symbols-intern-publication-finish reserved)))

(defun symbols-intern-fresh-return-ready-p (code-base caller reserved)
  (let* ((published (symbols-intern-publication-finish reserved))
         (sp (boymoo-model::a64-sp (proof-world-machine caller))))
    (and (not (proof-world-stop caller))
         (<= 48 sp)
         (equal (boymoo-model::a64-sp (proof-world-machine reserved)) (- sp 48))
         (equal (proof-stack-top reserved) (+ 8 (proof-stack-top caller)))
         (< (+ 8 (proof-stack-top caller)) (expt 2 64))
         (proof-register-frame-p 30 *symbols-intern-unpopped-clobbers* caller reserved)
         (symbols-intern-publication-ready-p code-base reserved)
         (proof-memory-span-agrees-p (- sp 48) sp (symbols-intern-saved-world caller) published)
         (symbols-path-ready-p *symbols-intern-return-path* code-base (proof-world-reg 30 caller) published))))

(defun symbols-intern-fresh-tail-ready-p (code-base caller reserved)
  (and (symbols-intern-initialize-pre-p code-base reserved)
       (symbols-intern-fresh-return-ready-p code-base caller reserved)))

(local
 (defthm symbols-intern-publication-reestablishes-stack-frame
   (implies (and (proof-register-frame-p 30 *symbols-intern-unpopped-clobbers* caller reserved)
                 (equal (proof-stack-top reserved) (+ 8 (proof-stack-top caller)))
                 (< (+ 8 (proof-stack-top caller)) (expt 2 64))
                 (symbols-intern-publication-frame-p code-base reserved entry published))
            (proof-register-frame-p 30 *symbols-intern-temporary-clobbers* caller published))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers *symbols-intern-publication-clobbers*) (allowed *symbols-intern-unpopped-clobbers*)
                             (before reserved) (after published))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-unpopped-clobbers*)
                             (first caller) (middle reserved) (last published))
                  (:instance symbols-frame-keeps-restored-register (highest 30) (register 25)
                             (clobbers *symbols-intern-unpopped-clobbers*) (before caller) (after published)))
            :in-theory (e/d (proof-stack-top symbols-intern-popped-stack-top)
                            (symbols-box-word symbols-intern-linked-world))))
   :rule-classes nil))

(local
 (defthm symbols-intern-epilogue-is-read-only
   (implies (symbols-intern-restore-frame-p result before after)
            (symbols-no-memory-or-kernel-change-p before after))
   :hints (("Goal" :in-theory (disable symbols-stack-word)))
   :rule-classes nil))

(local
 (defthm symbols-intern-publication-keeps-machine-frame
   (implies (symbols-intern-publication-frame-p code-base reserved entry published)
            (and (equal (boymoo-model::a64-sp (proof-world-machine published))
                        (boymoo-model::a64-sp (proof-world-machine reserved)))
                 (equal (proof-world-reg 0 published)
                        (symbols-box-word (proof-world-reg 0 reserved) (proof-heap-base reserved)))
                 (symbols-no-memory-or-kernel-change-p (symbols-intern-linked-world entry) published)))
   :hints (("Goal" :in-theory (disable symbols-box-word symbols-intern-linked-world)))
   :rule-classes nil))

(local
 (defthm symbols-intern-epilogue-has-caller-link
   (implies (symbols-intern-caller-save-slots-p caller published)
            (equal (symbols-stack-word 8 published) (proof-world-reg 30 caller)))
   :hints (("Goal" :in-theory (disable symbols-stack-word)))
   :rule-classes nil))

(local
 (defthm symbols-intern-publication-enters-epilogue
   (implies (and (symbols-runtime-base-p code-base)
                 (symbols-intern-publication-frame-p code-base reserved entry published)
                 (equal (boymoo-model::a64-sp (proof-world-machine reserved))
                        (- (boymoo-model::a64-sp (proof-world-machine caller)) 48)))
            (symbols-intern-return-pre-p code-base published))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-sp) (symbols-intern-linked-world))))
   :rule-classes nil))

(defthm symbols-run-intern-fresh-tail
  (let* ((entry (symbols-intern-publication-entry reserved))
         (after (symbols-intern-fresh-finish reserved))
         (word (symbols-box-word (proof-world-reg 0 reserved) (proof-heap-base reserved))))
    (implies (symbols-intern-fresh-tail-ready-p code-base caller reserved)
             (and (proof-frame-return-p *symbols-intern-call-clobbers* t caller after)
                  (equal (proof-world-reg 0 after) word)
                  (symbols-no-memory-or-kernel-change-p (symbols-intern-linked-world entry) after))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-publication-from-reserved-span (before reserved))
                 (:instance symbols-intern-publication-keeps-machine-frame
                            (entry (symbols-intern-publication-entry reserved))
                            (published (symbols-intern-publication-finish reserved)))
                 (:instance symbols-intern-publication-reestablishes-stack-frame
                            (entry (symbols-intern-publication-entry reserved))
                            (published (symbols-intern-publication-finish reserved)))
                 (:instance symbols-intern-publication-enters-epilogue
                            (entry (symbols-intern-publication-entry reserved))
                            (published (symbols-intern-publication-finish reserved)))
                 (:instance symbols-intern-caller-save-slots-survive-writes
                            (before caller) (middle (symbols-intern-publication-finish reserved)))
                 (:instance symbols-intern-epilogue-has-caller-link
                            (published (symbols-intern-publication-finish reserved)))
                 (:instance symbols-run-intern-return (before (symbols-intern-publication-finish reserved)))
                 (:instance symbols-intern-epilogue-is-read-only
                            (before (symbols-intern-publication-finish reserved))
                            (result (proof-world-reg 0 (symbols-intern-publication-finish reserved)))
                            (after (symbols-intern-fresh-finish reserved)))
                 (:instance symbols-intern-restore-caller-registers
                            (before caller) (middle (symbols-intern-publication-finish reserved))
                            (result (symbols-box-word (proof-world-reg 0 reserved) (proof-heap-base reserved)))
                            (after (symbols-intern-fresh-finish reserved)))
                 (:instance symbols-memory-and-kernel-frame-is-transitive
                            (first (symbols-intern-linked-world (symbols-intern-publication-entry reserved)))
                            (middle (symbols-intern-publication-finish reserved))
                            (last (symbols-intern-fresh-finish reserved))))
           :in-theory (disable proof-advance-after-stop symbols-intern-publication-finish
                               symbols-intern-publication-entry symbols-intern-publication-ready-p
                               symbols-intern-publication-frame-p symbols-intern-caller-save-slots-p
                               symbols-intern-return-pre-p symbols-stack-word
                               symbols-intern-restore-frame-p symbols-intern-saved-world symbols-intern-linked-world
                               proof-frame-return-p proof-register-frame-p proof-memory-span-agrees-p
                               symbols-intern-popped-stack-top symbols-box-word symbols-load-register-word)))
  :rule-classes nil)

(defun symbols-intern-link-writes-disjoint-p (start end entry)
  (let ((link (+ 24 (proof-world-reg 0 entry)))
        (bucket (proof-world-reg 4 entry))
        (count (+ 8 (proof-world-reg 1 entry))))
    (and (proof-span-p link 8) (proof-span-p bucket 8) (proof-span-p count 8)
         (proof-disjoint-p start end link (+ link 8))
         (proof-disjoint-p start end bucket (+ bucket 8))
         (proof-disjoint-p start end count (+ count 8)))))

(local
 (defthm symbols-intern-initial-fields-survive-link-writes
   (let ((address (proof-world-reg 0 reserved)))
     (implies (and (proof-span-p address 48)
                   (symbols-intern-link-writes-disjoint-p address (+ address 48) entry))
              (equal (symbols-intern-initial-fields-p reserved (symbols-intern-linked-world entry))
                     (symbols-intern-initial-fields-p reserved entry))))
   :hints (("Goal"
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes boymoo-model::a64-store
                             symbols-load-register-word symbols-intern-popped-stack-top symbols-box-word))))
   :rule-classes nil))

(local
 (defthm symbols-intern-bucket-helper-keeps-initialized-fields
   (let* ((initialized (symbols-intern-initialized-state reserved))
          (entry (symbols-intern-publication-entry reserved)))
     (implies (and (symbols-intern-initialize-pre-p code-base reserved)
                   (symbols-intern-publication-ready-p code-base reserved)
                   (symbols-intern-initial-fields-p reserved initialized))
              (symbols-intern-initial-fields-p reserved entry)))
   :hints (("Goal"
            :use ((:instance symbols-run-intern-initialize (before reserved))
                  (:instance symbols-run-bucket-address (before (symbols-intern-initialized-state reserved)))
                  (:instance symbols-intern-initialized-fields-of-same-memory (before reserved)
                             (first (symbols-intern-initialized-state reserved))
                             (last (symbols-intern-publication-entry reserved))))
            :in-theory (e/d (symbols-intern-initialize-frame-p symbols-no-memory-or-kernel-change-p)
                            (symbols-run-bucket-address proof-segment-p
                             symbols-intern-initial-fields-p
                             symbols-intern-popped-stack-top symbols-box-address symbols-box-word))))
   :rule-classes nil))

(defthm symbols-intern-fresh-tail-preserves-initialized-fields
  (let ((entry (symbols-intern-publication-entry reserved))
        (after (symbols-intern-fresh-finish reserved))
        (address (proof-world-reg 0 reserved)))
    (implies (and (symbols-intern-fresh-tail-ready-p code-base caller reserved)
                  (proof-reserved-span-p :header address 56 reserved objects)
                  (symbols-intern-link-writes-disjoint-p address (+ address 48) entry))
             (symbols-intern-initial-fields-p reserved after)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-fresh-tail)
                 (:instance symbols-run-intern-initializes-fields (before reserved))
                 (:instance symbols-intern-bucket-helper-keeps-initialized-fields)
                 (:instance symbols-intern-initial-fields-survive-link-writes
                            (entry (symbols-intern-publication-entry reserved)))
                 (:instance symbols-intern-initialized-fields-of-same-memory (before reserved)
                            (first (symbols-intern-linked-world (symbols-intern-publication-entry reserved)))
                            (last (symbols-intern-fresh-finish reserved))))
           :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                           (symbols-intern-fresh-finish symbols-intern-publication-entry
                            symbols-intern-initial-fields-p
                            symbols-intern-link-writes-disjoint-p symbols-intern-linked-world
                            symbols-intern-initialize-pre-p
                            symbols-intern-publication-finish symbols-intern-saved-world
                            proof-frame-return-p proof-object-disjoint-p proof-memory-span-agrees-p))))
  :rule-classes nil)

(defun symbols-intern-publication-slots-p (before)
  (let ((link (+ 24 (proof-world-reg 0 before)))
        (bucket (proof-world-reg 4 before))
        (count (+ 8 (proof-world-reg 1 before))))
    (and (proof-span-p link 8) (proof-span-p bucket 8) (proof-span-p count 8)
         (proof-disjoint-p link (+ link 8) bucket (+ bucket 8))
         (proof-disjoint-p link (+ link 8) count (+ count 8))
         (proof-disjoint-p bucket (+ bucket 8) count (+ count 8)))))

(defun symbols-intern-published-entry-fields-p (before after)
  (let* ((entry (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (bucket (proof-world-reg 4 before))
         (count (+ 8 (proof-world-reg 1 before)))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (and (equal (proof-load-word (+ 24 entry) last) (proof-load-word bucket first))
         (equal (proof-load-word bucket last) (symbols-box-word entry base))
         (equal (proof-load-word count last)
                (boymoo-model::a64-unsigned 64 (+ 2 (proof-load-word count first)))))))

(local
 (defthm symbols-link-writes-establish-entry-and-count
   (implies (symbols-intern-publication-slots-p before)
            (symbols-intern-published-entry-fields-p before (symbols-intern-linked-world before)))
   :hints (("Goal"
            :use ((:instance symbols-publication-loaded-word-fits
                             (address (proof-world-reg 4 before)) (machine (proof-world-machine before))))
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes boymoo-model::a64-store symbols-box-word
                             symbols-load-register-word symbols-publication-loaded-word-fits))))
   :rule-classes nil))

(local
 (defthm symbols-linked-entry-fields-depend-on-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (equal (symbols-intern-published-entry-fields-p before first)
                   (symbols-intern-published-entry-fields-p before last)))
   :hints (("Goal"
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p proof-load-word boymoo-model::a64-load)
                            (symbols-box-word boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm symbols-run-intern-publication-updates-bucket-and-count
  (let ((after (proof-advance (len *symbols-intern-publish-path*) before)))
    (implies (and (symbols-intern-publish-pre-p code-base before)
                  (symbols-path-ready-p *symbols-intern-publish-path* code-base
                                        (symbols-runtime-address "rt:intern-return" code-base) before)
                  (symbols-intern-publication-slots-p before))
             (symbols-intern-published-entry-fields-p before after)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-publish)
                 (:instance symbols-link-writes-establish-entry-and-count)
                 (:instance symbols-linked-entry-fields-depend-on-memory
                            (first (symbols-intern-linked-world before))
                            (last (proof-advance (len *symbols-intern-publish-path*) before))))
           :in-theory (disable symbols-intern-linked-world symbols-intern-publication-slots-p
                               symbols-intern-published-entry-fields-p symbols-box-word)))
  :rule-classes nil)

(local
 (defthm symbols-ranked-initialization-keeps-heap-base
   (implies (symbols-intern-initialized-symbol-ranks-p reserved after new-objects)
            (equal (proof-heap-base after) (proof-heap-base reserved)))
   :hints (("Goal" :in-theory (disable symbols-box-word symbols-intern-popped-stack-top
                                      symbols-load-register-word symbols-word-below-rank-p)))
   :rule-classes nil))

(defun symbols-intern-fresh-representation-p (name designator buckets packages reserved after new-objects)
  (let* ((base (proof-heap-base reserved))
         (machine (proof-world-machine after))
         (name-word (symbols-load-register-word (symbols-intern-popped-stack-top reserved) reserved))
         (number (proof-package-number (acl2::symbol-package-name designator) packages 0)))
    (and (symbols-intern-initialized-symbol-ranks-p reserved after new-objects)
         (proof-value-p name-word name base new-objects packages machine)
         (proof-value-p (proof-world-reg 20 reserved) number base new-objects packages machine)
         (stringp name) (symbolp designator)
         (natp number) (proof-immediate-integer-p number)
         (proof-packages-p packages) (proof-package-bindings-p packages 0 buckets)
         (not (proof-static-binding number name buckets)))))

(defthm symbols-intern-reserved-fresh-runtime-contract
  (let* ((primitive 'acl2::intern-in-package-of-symbol)
         (args (list name designator))
         (after (symbols-intern-fresh-finish reserved))
         (entry (symbols-intern-publication-entry reserved))
         (address (proof-world-reg 0 reserved)))
    (implies (and (proof-runtime-pre-p primitive args program *symbols-runtime-labels*
                                       code-base caller caller-objects packages)
                  (symbols-intern-fresh-tail-ready-p code-base caller reserved)
                  (proof-reserved-span-p :header address 56 reserved reserved-objects)
                  (symbols-intern-link-writes-disjoint-p address (+ address 48) entry)
                  (symbols-intern-fresh-representation-p name designator buckets packages reserved after new-objects)
                  (proof-preserved-heap-p t caller after caller-objects new-objects packages))
             (proof-runtime-return-p primitive args program caller after caller-objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-fresh-tail)
                 (:instance symbols-intern-fresh-tail-preserves-initialized-fields (objects reserved-objects))
                 (:instance symbols-ranked-initialization-keeps-heap-base (after (symbols-intern-fresh-finish reserved)))
                 (:instance symbols-intern-fields-from-reserved-symbol
                            (before reserved) (after (symbols-intern-fresh-finish reserved))
                            (number (proof-package-number (acl2::symbol-package-name designator) packages 0)))
                 (:instance symbols-ranked-home-symbol-implements-core-interning
                            (word (symbols-box-word (proof-world-reg 0 reserved) (proof-heap-base reserved)))
                            (base (proof-heap-base reserved)) (objects new-objects)
                            (machine (proof-world-machine (symbols-intern-fresh-finish reserved)))))
           :in-theory (disable symbols-intern-fresh-finish symbols-intern-publication-entry
                               symbols-intern-fresh-tail-ready-p symbols-intern-initial-fields-p
                               symbols-ranked-symbol-fields-p symbols-intern-linked-world symbols-box-word
                               symbols-intern-link-writes-disjoint-p symbols-intern-popped-stack-top
                               symbols-intern-initialized-symbol-ranks-p proof-frame-return-p
                               proof-runtime-pre-p proof-preserved-heap-p proof-value-p proof-packages-p
                               proof-package-number proof-static-binding proof-package-bindings-p
                               proof-object-disjoint-p boymoo-model::core-primitive)))
  :rule-classes nil)

(defun symbols-ranked-slot-views-p (views address depth base objects packages machine)
  (if (atom views)
      (null views)
    (let ((word (proof-load-word address machine)))
      (and (car views)
           (symbols-word-below-rank-p word depth base objects)
           (equal (proof-view word base objects packages machine) (car views))
           (symbols-ranked-slot-views-p (cdr views) (+ 8 address) depth base objects packages machine)))))

(defthm symbols-ranked-slots-decode-to-expected-views
  (implies (and (natp depth)
                (symbols-ranked-slot-views-p views address depth base objects packages machine))
           (equal (proof-view-step :slots address (len views) depth base objects packages machine)
                  (cons :slots views)))
  :hints (("Goal"
           :induct (symbols-ranked-slot-views-p views address depth base objects packages machine)
           :in-theory (disable proof-view-step))
          ("Subgoal *1/2"
           :expand ((proof-view-step :slots address (+ 1 (len (cdr views))) depth base objects packages machine))
           :use ((:instance symbols-publication-read-at-rank (word (proof-load-word address machine))))
           :in-theory (disable proof-view-step symbols-word-below-rank-p))
          ("Subgoal *1/1"
           :expand ((proof-view-step :slots address 0 depth base objects packages machine))
           :in-theory (disable proof-view-step)))
  :rule-classes nil)

(defun symbols-ranked-vector-fields-p (word views base objects packages machine)
  (let* ((address (proof-pointer-address word base))
         (record (assoc-equal address objects))
         (depth (proof-object-rank record))
         (bytes (* 8 (len views))))
    (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2)
         record (eq (proof-object-kind record) :header) (natp depth)
         (proof-span-p address (+ 8 bytes))
         (equal (proof-load-word address machine) (+ 6 (* 256 bytes)))
         (symbols-ranked-slot-views-p views (+ address 8) depth base objects packages machine))))

(local
 (defthm symbols-vector-header-scales-slot-count
   (and (equal (* 256 (* 8 count)) (* 2048 count))
        (equal (* 1/256 (* 2048 count)) (* 8 count))
        (equal (* 1/8 (* 8 count)) (fix count)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm symbols-vector-header-shift-agrees-with-count
   (implies (natp count)
            (and (equal (proof-header-type (+ 6 (* 2048 count))) 6)
                 (equal (proof-header-size (+ 6 (* 2048 count))) (* 8 count))
                 (equal (mod (* 8 count) 8) 0)
                 (equal (ash (* 8 count) -3) count)))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-keeps-low-field (width 8) (low 6) (high (* 8 count)))
                  (:instance symbols-floor-of-decomposition (q (* 8 count)) (r 3/128) (divisor 1))
                  (:instance symbols-floor-of-decomposition (q count) (r 0) (divisor 1))
                  (:instance symbols-mod-of-decomposition (q count) (r 0) (divisor 8)))
            :in-theory (e/d (proof-header-type proof-header-size ash)
                            (floor mod symbols-unsigned-keeps-low-field
                             symbols-floor-of-decomposition symbols-mod-of-decomposition))))
   :rule-classes nil))

(defthm symbols-ranked-vector-fields-give-view
  (implies (symbols-ranked-vector-fields-p word views base objects packages machine)
           (equal (proof-view word base objects packages machine)
                  (cons :vector views)))
  :hints (("Goal"
           :use ((:instance symbols-publication-boxed-word-is-even)
                 (:instance symbols-vector-header-shift-agrees-with-count (count (len views)))
                 (:instance symbols-ranked-slots-decode-to-expected-views
                            (address (+ 8 (proof-pointer-address word base)))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))
           :expand ((proof-view word base objects packages machine)
                    (:free (rank) (proof-view-step :word word 0 rank base objects packages machine)))
           :in-theory (disable symbols-publication-boxed-word-is-even symbols-ranked-slot-views-p
                               proof-symbol-value proof-integer-view proof-cons-value proof-rational-value
                               proof-complex-value proof-load-string proof-span-p proof-object-rank
                               proof-object-kind assoc-equal ash mod floor)))
  :rule-classes nil)

(defthm symbols-intern-fresh-tail-publishes-entry-fields
  (let ((entry (symbols-intern-publication-entry reserved))
        (after (symbols-intern-fresh-finish reserved)))
    (implies (and (symbols-intern-fresh-tail-ready-p code-base caller reserved)
                  (symbols-intern-publication-slots-p entry))
             (symbols-intern-published-entry-fields-p entry after)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-fresh-tail)
                 (:instance symbols-link-writes-establish-entry-and-count
                            (before (symbols-intern-publication-entry reserved)))
                 (:instance symbols-linked-entry-fields-depend-on-memory
                            (before (symbols-intern-publication-entry reserved))
                            (first (symbols-intern-linked-world (symbols-intern-publication-entry reserved)))
                            (last (symbols-intern-fresh-finish reserved))))
           :in-theory (disable symbols-intern-fresh-tail-ready-p symbols-intern-linked-world
                               symbols-intern-fresh-finish symbols-intern-publication-entry
                               symbols-intern-publication-slots-p symbols-intern-published-entry-fields-p
                               proof-frame-return-p)))
  :rule-classes nil)

(defun symbols-intern-published-entry-ranks-p (reserved entry after objects)
  (let* ((address (proof-world-reg 0 entry))
         (base (proof-heap-base reserved))
         (word (symbols-box-word address base))
         (record (assoc-equal address objects))
         (depth (proof-object-rank record))
         (old-head (proof-load-word (proof-world-reg 4 entry) (proof-world-machine entry))))
    (and (equal address (+ 24 (proof-world-reg 0 reserved)))
         (equal (proof-heap-base entry) base)
         (equal (proof-heap-base after) base)
         (equal (proof-pointer-address word base) address)
         (equal (proof-word-tag word) 2)
         record (eq (proof-object-kind record) :header) (natp depth)
         (proof-span-p address 32)
         (symbols-word-below-rank-p (symbols-box-word (proof-world-reg 0 reserved) base) depth base objects)
         (symbols-word-below-rank-p (proof-world-reg 22 reserved) depth base objects)
         (symbols-word-below-rank-p old-head depth base objects))))

(local
 (defthm symbols-intern-entry-word-gives-prepended-fields
   (let* ((base (proof-heap-base reserved))
          (symbol-word (symbols-box-word (proof-world-reg 0 reserved) base))
          (entry-word (symbols-box-word (proof-world-reg 0 entry) base))
          (machine (proof-world-machine after))
          (old-head (proof-load-word (proof-world-reg 4 entry) (proof-world-machine entry)))
          (fields (cdr (symbols-prepend-entry symbol old-bucket packages))))
     (implies (and (symbols-intern-initial-fields-p reserved after)
                   (symbols-intern-published-entry-fields-p entry after)
                   (symbols-intern-published-entry-ranks-p reserved entry after objects)
                   (proof-value-p symbol-word symbol base objects packages machine)
                   (proof-value-p (proof-world-reg 22 reserved) (symbols-cached-hash symbol packages)
                                  base objects packages machine)
                   old-bucket (equal (proof-view old-head base objects packages machine) old-bucket))
              (and (equal (proof-load-word (proof-world-reg 4 entry) machine) entry-word)
                   (symbols-ranked-vector-fields-p entry-word fields base objects packages machine))))
   :hints (("Goal"
            :in-theory (disable symbols-cached-hash symbols-box-word proof-object-kind proof-object-rank
                                assoc-equal proof-span-p symbols-word-below-rank-p)))
   :rule-classes nil))

(local
 (defthm symbols-valid-dynamic-bucket-has-view
   (implies (proof-dynamic-bucket bucket index size packages) bucket)
   :hints (("Goal" :expand ((proof-dynamic-bucket bucket index size packages))))
   :rule-classes nil))

(defthm symbols-intern-fresh-tail-publishes-prepended-bucket
  (let* ((entry (symbols-intern-publication-entry reserved))
         (after (symbols-intern-fresh-finish reserved))
         (address (proof-world-reg 0 reserved))
         (base (proof-heap-base reserved))
         (symbol-word (symbols-box-word address base))
         (entry-word (symbols-box-word (proof-world-reg 0 entry) base))
         (machine (proof-world-machine after))
         (old-head (proof-load-word (proof-world-reg 4 entry) (proof-world-machine entry))))
    (implies (and (symbols-intern-fresh-tail-ready-p code-base caller reserved)
                  (proof-reserved-span-p :header address 56 reserved old-objects)
                  (symbols-intern-link-writes-disjoint-p address (+ address 48) entry)
                  (symbols-intern-publication-slots-p entry)
                  (symbols-intern-published-entry-ranks-p reserved entry after objects)
                  (proof-value-p symbol-word symbol base objects packages machine)
                  (proof-value-p (proof-world-reg 22 reserved) (symbols-cached-hash symbol packages)
                                 base objects packages machine)
                  (equal (proof-view old-head base objects packages machine) old-bucket)
                  (proof-dynamic-bucket old-bucket index size packages)
                  (symbols-home-symbol-p symbol packages)
                  (equal index (symbols-bucket-index symbol size packages)))
             (and (equal (proof-load-word (proof-world-reg 4 entry) machine) entry-word)
                  (equal (proof-view entry-word base objects packages machine)
                         (symbols-prepend-entry symbol old-bucket packages))
                  (equal (proof-dynamic-bucket (proof-view entry-word base objects packages machine)
                                               index size packages)
                         (list* :entries symbol (cdr (proof-dynamic-bucket old-bucket index size packages)))))))
  :hints (("Goal"
           :use ((:instance symbols-intern-fresh-tail-preserves-initialized-fields (objects old-objects))
                 (:instance symbols-intern-fresh-tail-publishes-entry-fields)
                 (:instance symbols-intern-entry-word-gives-prepended-fields
                            (entry (symbols-intern-publication-entry reserved))
                            (after (symbols-intern-fresh-finish reserved)))
                 (:instance symbols-ranked-vector-fields-give-view
                            (word (symbols-box-word (proof-world-reg 0 (symbols-intern-publication-entry reserved))
                                                     (proof-heap-base reserved)))
                            (views (cdr (symbols-prepend-entry symbol old-bucket packages)))
                            (base (proof-heap-base reserved))
                            (machine (proof-world-machine (symbols-intern-fresh-finish reserved))))
                 (:instance symbols-prepend-entry-yields-binding (bucket old-bucket))
                 (:instance symbols-valid-dynamic-bucket-has-view (bucket old-bucket)))
           :in-theory (disable proof-reserved-span-p proof-value-p proof-dynamic-bucket
                               symbols-prepend-entry-yields-binding symbols-ranked-vector-fields-p
                               symbols-intern-fresh-tail-ready-p symbols-intern-link-writes-disjoint-p
                               symbols-intern-publication-slots-p symbols-intern-published-entry-ranks-p
                               symbols-intern-initial-fields-p symbols-intern-publication-entry
                               symbols-intern-fresh-finish symbols-box-word symbols-home-symbol-p
                               symbols-bucket-index symbols-cached-hash)))
  :rule-classes nil)

(local
 (defun symbols-first-missing-dynamic-binding (old new)
   (cond ((atom old) nil)
         ((member-equal (car old) new) (symbols-first-missing-dynamic-binding (cdr old) new))
         (t (car old)))))

(local
 (defthm symbols-first-missing-binding-is-in-old-table
   (let ((missing (symbols-first-missing-dynamic-binding old new)))
     (implies (not (subsetp-eq old new))
              (and (member-equal missing old) (not (member-equal missing new)))))
   :hints (("Goal" :induct (symbols-first-missing-dynamic-binding old new)))
   :rule-classes nil))

(local
 (defthm symbols-inserted-and-grown-root-are-vectors
   (and (equal (cons :vector (cdr (symbols-insert-binding symbol root packages)))
               (symbols-insert-binding symbol root packages))
        (equal (cons :vector (cdr (symbols-grow-view root packages)))
               (symbols-grow-view root packages)))
   :hints (("Goal"
            :in-theory (disable symbols-empty-buckets symbols-rehash-bindings symbols-push-bucket
                                proof-dynamic-entries symbols-grown-size)))))

(defthm symbols-ranked-inserted-root-preserves-dynamic-bindings
  (let* ((root (proof-dynamic-view before old-objects packages))
         (old (proof-dynamic-entries root packages))
         (updated (symbols-insert-binding symbol root packages))
         (base (proof-heap-base after))
         (machine (proof-world-machine after))
         (word (proof-dynamic-root base machine)))
    (implies (and old (not (equal root (proof-value-view nil)))
                  (symbols-home-symbol-p symbol packages)
                  (< (proof-view-value (cadr root)) (len (cddr root)))
                  (not (member-equal symbol (cdr old)))
                  (symbols-ranked-vector-fields-p word (cdr updated) base new-objects packages machine))
             (and (equal (proof-dynamic-view after new-objects packages) updated)
                  (proof-dynamic-table-preserved-p t before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-ranked-vector-fields-give-view (objects new-objects)
                            (word (proof-dynamic-root (proof-heap-base after) (proof-world-machine after)))
                            (views (cdr (symbols-insert-binding symbol (proof-dynamic-view before old-objects packages)
                                                                 packages)))
                            (base (proof-heap-base after)) (machine (proof-world-machine after)))
                 (:instance symbols-first-missing-binding-is-in-old-table
                            (old (cdr (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages)))
                            (new (cdr (proof-dynamic-entries (symbols-insert-binding
                                                             symbol (proof-dynamic-view before old-objects packages) packages)
                                                            packages))))
                 (:instance symbols-fresh-binding-preserves-dynamic-table
                            (root (proof-dynamic-view before old-objects packages))
                            (value (symbols-first-missing-dynamic-binding
                                    (cdr (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages))
                                    (cdr (proof-dynamic-entries (symbols-insert-binding
                                                                 symbol (proof-dynamic-view before old-objects packages)
                                                                 packages) packages))))))
           :in-theory (disable symbols-insert-binding symbols-ranked-vector-fields-p proof-dynamic-entries
                               proof-dynamic-root symbols-home-symbol-p
                               symbols-first-missing-dynamic-binding symbols-fresh-binding-preserves-dynamic-table)))
  :rule-classes nil)

(defthm symbols-ranked-grown-root-preserves-dynamic-bindings
  (let* ((root (proof-dynamic-view before old-objects packages))
         (old (proof-dynamic-entries root packages))
         (updated (symbols-grow-view root packages))
         (base (proof-heap-base after))
         (machine (proof-world-machine after))
         (word (proof-dynamic-root base machine)))
    (implies (and old (symbols-ranked-vector-fields-p word (cdr updated) base new-objects packages machine))
             (and (equal (proof-dynamic-view after new-objects packages) updated)
                  (proof-dynamic-table-preserved-p t before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-ranked-vector-fields-give-view (objects new-objects)
                            (word (proof-dynamic-root (proof-heap-base after) (proof-world-machine after)))
                            (views (cdr (symbols-grow-view (proof-dynamic-view before old-objects packages) packages)))
                            (base (proof-heap-base after)) (machine (proof-world-machine after)))
                 (:instance symbols-first-missing-binding-is-in-old-table
                            (old (cdr (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages)))
                            (new (cdr (proof-dynamic-entries (symbols-grow-view
                                                             (proof-dynamic-view before old-objects packages) packages)
                                                            packages))))
                 (:instance symbols-doubling-preserves-dynamic-table
                            (root (proof-dynamic-view before old-objects packages))
                            (value (symbols-first-missing-dynamic-binding
                                    (cdr (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages))
                                    (cdr (proof-dynamic-entries (symbols-grow-view
                                                                 (proof-dynamic-view before old-objects packages) packages)
                                                                packages))))))
           :in-theory (disable symbols-grow-view symbols-ranked-vector-fields-p proof-dynamic-entries
                               proof-dynamic-root symbols-first-missing-dynamic-binding
                               symbols-doubling-preserves-dynamic-table)))
  :rule-classes nil)
