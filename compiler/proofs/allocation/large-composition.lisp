(in-package "BOYMOO-PROOFS")

(include-book "large-map-heap")
(include-book "large-caller")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-large-map-same-memory-keeps-load
   (implies (equal (allocation-memory before) (allocation-memory after))
            (equal (allocation-load-word address after) (allocation-load-word address before)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-load-word proof-load-word)
                                   (boymoo-model::a64-read-bytes))))))

(defthm allocation-large-map-keeps-constructor-saves
  (implies (and (allocation-large-caller-saves-p caller before)
                (allocation-large-map-call-result-p before after)
                (equal (allocation-memory after) (allocation-memory before)))
           (allocation-large-caller-saves-p caller after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-keeps-heap-registers
                 (:instance allocation-large-map-same-memory-keeps-load (address (allocation-sp before)))
                 (:instance allocation-large-map-same-memory-keeps-load (address (+ (allocation-sp before) 8)))
                 (:instance allocation-large-map-same-memory-keeps-load (address (+ (allocation-sp before) 16)))
                 (:instance allocation-large-map-same-memory-keeps-load (address (+ (allocation-sp before) 24)))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small *allocation-large-map-clobbers*)
                  (large (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)))
                 (:instance allocation-register-frame-transitive
                  (register 30) (before caller) (middle before)
                  (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))))
           :in-theory (e/d (allocation-large-map-call-result-p allocation-large-caller-saves-p)
                           (proof-register-frame-p proof-streams-preserved-p proof-clear-memory proof-linux-errno-p)))))

(defthm allocation-large-map-extends-executed-prefix
  (let ((cuts (list (proof-world-reg 30 caller))))
    (implies (and (natp steps)
                  (allocation-prefix-p steps cuts caller before)
                  (allocation-path-ready-p *allocation-large-map-call* cuts before)
                  (equal after (allocation-path-end *allocation-large-map-call* before)))
             (allocation-prefix-p (+ steps (len *allocation-large-map-call*)) cuts caller after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-prefix-from-path (path *allocation-large-map-call*)
                            (cuts (list (proof-world-reg 30 caller))))
                 (:instance allocation-prefix-after-prefix
                  (first-steps steps) (last-steps (len *allocation-large-map-call*))
                  (cuts (list (proof-world-reg 30 caller))) (before caller) (middle before)))
           :in-theory (disable allocation-prefix-p allocation-path-end allocation-path-ready-p allocation-prefix-from-path))))

(local
 (defthm allocation-stack-four-words-keep-alignment
   (implies (and (integerp sp) (equal (mod sp 16) 0))
            (equal (mod (+ 32 sp) 16) 0))))

(local
 (defthm allocation-constructor-layout-page-and-alignment
   (implies (proof-heap-layout-p world)
            (and (not (proof-world-stop world))
                 (proof-page-size-p (proof-world-page-size world))
                 (equal (mod (proof-heap-base world) 8) 0)
                 (equal (mod (+ 32 (allocation-sp world)) 16) 0)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :use ((:instance allocation-word-register-range (register 0))
                  (:instance allocation-stack-four-words-keep-alignment (sp (allocation-sp world))))
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                            (allocation-word-register-range allocation-stack-four-words-keep-alignment
                             proof-page-size-p proof-align-up proof-regions-p proof-covered-p
                             proof-runtime-word proof-disjoint-p mod))))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm allocation-linux-mapping-word-alignment
    (implies (and (allocation-map-admissible-success-p reply size world)
                  (proof-page-size-p (proof-world-page-size world)))
             (equal (mod reply 8) 0))
    :rule-classes nil
    :hints (("Goal" :use ((:instance allocation-align-up-of-multiple
                           (size reply) (alignment (proof-world-page-size world))))
             :in-theory (disable allocation-align-up-of-multiple proof-region-disjoint-p)))))

(local
 (defthm allocation-heap-has-string-accounting
   (implies (proof-heap-p world objects packages)
            (proof-string-accounting-p
             (cdr (proof-external-objects (proof-external-head world) (len objects) world objects))
             world))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-static-p proof-object-map-p proof-heap-layout-p
                                      proof-external-objects proof-string-accounting-p proof-heap-object-spans-p
                                      proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                                      proof-stack-prefix)))))

(defthm allocation-large-success-at-mapping-initializer
  (let* ((base (proof-heap-base before))
         (save (allocation-sp before))
         (size (proof-world-reg 20 before))
         (length (proof-world-reg 19 before))
         (reply (car (proof-world-replies before)))
         (machine-start (- (proof-machine-limit before) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (and (allocation-code-origin-p origin)
                  (equal (proof-world-pc after) (allocation-large-string-address origin 21))
                  (proof-heap-p before objects packages)
                  (allocation-large-map-call-result-p before after)
                  (allocation-map-admissible-success-p reply size before)
                  (allocation-memory-in-readable-regions-p (allocation-memory before) (proof-world-regions before))
                  (< length *proof-space-size*)
                  (equal size (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 before) (- base 128))
                  (proof-subspan-p save 32 machine-start machine-end)
                  (< (+ save 32) *allocation-word-modulus*))
             (and (allocation-large-mapped-entry-p origin after)
                  (allocation-large-mapping-outside-reservations-p after)
                  (allocation-objects-outside-write-p reply (+ reply size) objects (proof-world-machine after))
                  (proof-preserved-heap-p nil before after objects objects packages)
                  (equal (allocation-memory after) (allocation-memory before)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-keeps-heap-registers allocation-large-map-success-keeps-old-data
                 allocation-large-successful-map-keeps-old-heap allocation-large-mapped-outside-old-objects
                 allocation-successful-map-outside-runtime-reservations allocation-mapping-success-geometry
                 allocation-map-keeps-save-span-and-account
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-mapped-entry-with-safe-stack (world after))
                 (:instance allocation-large-rounded-size-is-mappable (length (proof-world-reg 19 before)))
                 (:instance allocation-heap-has-string-accounting (world before))
                 (:instance allocation-large-budget-sum-fits
                  (world before) (length (proof-world-reg 19 before))
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))))
           :in-theory (disable allocation-mapping-preserves-heap-data-p allocation-map-admissible-success-p
                               allocation-large-mapping-size allocation-memory-in-readable-regions-p
                               allocation-large-map-call-result-p allocation-large-mapped-entry-p
                               allocation-large-mapping-outside-reservations-p
                               proof-heap-p proof-heap-layout-p proof-preserved-heap-p allocation-code-origin-p
                               allocation-large-string-address proof-string-accounting-p proof-external-objects
                               proof-register-frame-p proof-streams-preserved-p proof-regions-p proof-region-disjoint-p
                               proof-clear-memory proof-load-word proof-span-p proof-subspan-p proof-disjoint-p
                               allocation-objects-outside-write-p mod))))

(local
 (defthm allocation-large-call-success-fields
   (let* ((reply (car (proof-world-replies before)))
          (size (proof-world-reg 20 before)))
     (implies (and (allocation-map-admissible-success-p reply size before)
                   (allocation-large-map-call-result-p before after))
              (and (equal (proof-world-reg 0 after) reply)
                   (equal (allocation-sp after) (allocation-sp before))
                   (equal (allocation-memory after) (proof-clear-memory reply (+ reply size) (allocation-memory before)))
                   (equal (proof-world-regions after) (cons (proof-region reply (+ reply size) :rw)
                                                           (proof-world-regions before))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-large-map-call-result-p)
                                   (proof-register-frame-p proof-region-disjoint-p proof-clear-memory
                                    proof-streams-preserved-p mod))))))

(local
 (defthm allocation-large-caller-save-end-is-word
   (implies (allocation-large-caller-saves-p caller before)
            (< (+ 32 (allocation-sp before)) *allocation-word-modulus*))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-word-register-range (world caller) (register 0)))
            :in-theory (e/d (allocation-large-caller-saves-p unsigned-byte-p acl2::integer-range-p)
                            (allocation-word-register-range proof-register-frame-p))))))

(local
 (defthm allocation-subspan-end-within-upper
   (implies (proof-subspan-p start size lower upper)
            (<= (+ start size) upper))
   :rule-classes :forward-chaining))

(local
 (defthm allocation-preserved-heap-includes-heap
   (implies (proof-preserved-heap-p may-intern before after old-objects objects packages)
            (proof-heap-p after objects packages))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-heap-p proof-heap-frame-p proof-prefix-preserved-p
                                      proof-dynamic-table-preserved-p)))))

(local
 (defthm allocation-large-map-entry-has-code-origin
   (implies (allocation-large-map-entry-p origin world)
            (allocation-code-origin-p origin))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (allocation-large-map-entry-p) (allocation-code-origin-p))))))

(local
 (defthm allocation-success-is-an-admissible-map-reply
   (implies (allocation-map-admissible-success-p reply (proof-world-reg 20 world) world)
            (allocation-large-map-reply-p reply world))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (allocation-large-map-reply-p)
                                   (allocation-map-admissible-success-p proof-linux-errno-p))))))

(defthm allocation-large-successful-map-prefix-keeps-caller
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (length (proof-world-reg 19 before))
         (base (proof-heap-base before))
         (save (allocation-sp before))
         (machine-start (- (proof-machine-limit before) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*))
         (regions (proof-world-regions before))
         (memory (allocation-memory before)))
    (implies (and (allocation-large-map-entry-p origin before)
                  (allocation-large-caller-saves-p caller before)
                  (proof-preserved-heap-p nil caller before old-objects objects packages)
                  (allocation-memory-in-readable-regions-p memory regions)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (proof-span-p (proof-heap-base caller) 8)
                  (consp (proof-world-replies before))
                  (allocation-map-admissible-success-p reply size before)
                  (< length *proof-space-size*)
                  (equal size (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 before) (- base 128))
                  (proof-subspan-p save 32 machine-start machine-end)
                  (equal mapped (allocation-path-end *allocation-large-map-call* before)))
             (and (allocation-large-mapped-entry-p origin mapped)
                  (allocation-large-caller-saves-p caller mapped)
                  (proof-preserved-heap-p nil caller mapped old-objects objects packages)
                  (allocation-large-mapping-outside-reservations-p mapped)
                  (allocation-objects-outside-write-p reply (+ reply size) objects (proof-world-machine mapped))
                  (equal (proof-world-reg 0 mapped) reply)
                  (equal (proof-world-reg 20 mapped) size)
                  (equal (proof-world-reg 19 mapped) length)
                  (equal (allocation-sp mapped) save)
                  (equal (proof-machine-limit mapped) (proof-machine-limit before))
                  (equal (mod reply 8) 0)
                  (equal (mod (proof-heap-base mapped) 8) 0)
                  (equal (mod (+ save 32) 16) 0)
                  (<= (+ save 32) machine-end)
                  (equal (allocation-memory mapped) (proof-clear-memory reply (+ reply size) memory))
                  (equal (proof-world-regions mapped) (cons (proof-region reply (+ reply size) :rw) regions)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-map-path-effects (after mapped))
                 (:instance allocation-large-success-at-mapping-initializer (after mapped))
                 (:instance allocation-large-map-keeps-constructor-saves (after mapped))
                 (:instance allocation-large-map-keeps-heap-registers (after mapped))
                 (:instance allocation-large-call-success-fields (after mapped))
                 allocation-large-caller-save-end-is-word
                 (:instance allocation-linux-mapping-word-alignment
                  (reply (car (proof-world-replies before))) (size (proof-world-reg 20 before)) (world before))
                 (:instance allocation-large-rounded-size-is-mappable (length (proof-world-reg 19 before)))
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-memory-in-readable-regions-has-word-keys
                  (memory (allocation-memory before)) (regions (proof-world-regions before)))
                 (:instance allocation-large-call-heap-after-suffix (after mapped) (new-objects objects)))
           :in-theory (disable allocation-path-end allocation-large-mapped-entry-p allocation-large-mapping-size
                            allocation-large-map-call-result-p allocation-large-caller-saves-p
                            allocation-large-map-entry-p allocation-large-map-reply-p allocation-code-origin-p
                            allocation-large-string-address
                            allocation-map-admissible-success-p allocation-memory-in-readable-regions-p
                            allocation-large-mapping-outside-reservations-p allocation-objects-outside-write-p
                            allocation-memory-addresses-are-words-p proof-clear-memory proof-heap-frame-p proof-prefix-preserved-p
                            proof-dynamic-table-preserved-p proof-heap-p proof-heap-layout-p proof-heap-base
                            proof-page-size-p proof-register-frame-p
                            proof-stack-top proof-streams-preserved-p proof-span-p proof-subspan-p proof-preserved-heap-p
                            proof-linux-errno-p mod))))

(defthm allocation-large-constructor-checked-return-through-map
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (length (proof-world-reg 19 before))
         (base (proof-heap-base before))
         (save (allocation-sp before))
         (machine-start (- (proof-machine-limit before) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*))
         (regions (proof-world-regions before))
         (memory (allocation-memory before))
         (external (proof-external-objects (proof-external-head mapped) (len objects) mapped objects))
         (mapped-total (proof-external-bytes (cdr external) (proof-world-machine mapped)))
         (published (cons (proof-object (+ reply 24) :external :header 0) objects))
         (cuts (list (proof-world-reg 30 caller))))
    (implies (and (allocation-large-map-entry-p origin before)
                  (allocation-large-caller-saves-p caller before)
                  (proof-preserved-heap-p nil caller before old-objects objects packages)
                  (allocation-memory-in-readable-regions-p memory regions)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (allocation-memory-addresses-are-words-p (allocation-memory after))
                  (proof-span-p (proof-heap-base caller) 8)
                  (consp (proof-world-replies before))
                  (allocation-map-admissible-success-p reply size before)
                  (< length *proof-space-size*)
                  (equal size (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 before) (- base 128))
                  (proof-subspan-p save 32 machine-start machine-end)
                  (natp prefix-steps)
                  (allocation-prefix-p prefix-steps cuts caller before)
                  (allocation-path-ready-p *allocation-large-map-call* cuts before)
                  (equal mapped (allocation-path-end *allocation-large-map-call* before))
                  (< (+ mapped-total size) (expt 2 63))
                  (allocation-path-ready-p (allocation-large-postmap-path) cuts mapped)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* mapped))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
             (and (proof-segment-p (+ prefix-steps (len *allocation-large-map-call*) (len (allocation-large-postmap-path)))
                                   cuts caller :cut after)
                  (proof-string-constructor-return-p (proof-world-reg 0 caller) caller after old-objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-successful-map-prefix-keeps-caller
                 (:instance allocation-large-map-extends-executed-prefix (steps prefix-steps) (after mapped))
                 (:instance allocation-large-constructor-checked-return-from-mapped-state
                  (before mapped) (prefix-steps (+ prefix-steps (len *allocation-large-map-call*)))
                  (old-regions (proof-world-regions before)) (memory (allocation-memory before))))
           :in-theory (disable allocation-large-map-entry-p allocation-large-caller-saves-p allocation-large-mapped-entry-p
                               allocation-large-mapping-outside-reservations-p allocation-large-mapping-size
                               allocation-prefix-p allocation-path-end allocation-path-ready-p proof-segment-p
                               allocation-large-postmap-path proof-string-constructor-return-p proof-preserved-heap-p
                               allocation-memory-in-readable-regions-p allocation-memory-addresses-are-words-p
                               allocation-map-admissible-success-p allocation-objects-outside-write-p proof-clear-memory
                               proof-heap-base proof-machine-limit proof-span-p proof-subspan-p
                               proof-external-objects proof-external-head proof-external-bytes mod))))
