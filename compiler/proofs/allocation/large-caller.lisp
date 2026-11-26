(in-package "BOYMOO-PROOFS")

(include-book "large-layout")
(include-book "frame-composition")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-large-suffix-register-frame
  (implies (and (allocation-large-mapped-entry-p origin before)
                (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
           (proof-register-frame-p 30 '(0 1 2 19 20 21 30) before after))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-code-origin-p allocation-large-string-address
                                     allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defconst *allocation-large-saved-registers* '(19 20 21 30))

(defconst *allocation-large-constructor-clobbers*
  (append *proof-volatile-registers* '(26 27)))

(defund allocation-large-caller-saves-p (caller before)
  (let ((sp (allocation-sp before)))
    (and (not (proof-world-stop caller))
         (equal (allocation-sp caller) (+ sp 32))
         (equal (proof-world-reg 19 before) (proof-world-reg 0 caller))
         (equal (proof-stack-top before) (proof-stack-top caller))
         (equal (proof-machine-limit before) (proof-machine-limit caller))
         (equal (allocation-load-word sp before) (proof-world-reg 21 caller))
         (equal (allocation-load-word (+ sp 8) before) (proof-world-reg 30 caller))
         (equal (allocation-load-word (+ sp 16) before) (proof-world-reg 19 caller))
         (equal (allocation-load-word (+ sp 24) before) (proof-world-reg 20 caller))
         (proof-register-frame-p 30 (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)
                                 caller before))))

(defthm allocation-large-return-restores-caller-frame
  (implies (and (allocation-large-caller-saves-p caller before)
                (allocation-large-postmap-result-p before after)
                (proof-register-frame-p 30 '(0 1 2 19 20 21 30) before after))
           (proof-frame-return-p *allocation-large-constructor-clobbers* t caller after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-under-more-clobbers
                  (small '(0 1 2 19 20 21 30))
                  (large (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))
                  (register 30))
                 (:instance allocation-register-frame-transitive
                  (register 30) (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))
                  (before caller) (middle before))
                 (:instance allocation-register-frame-after-restoration
                  (upper 30) (restored *allocation-large-saved-registers*) (clobbers *allocation-large-constructor-clobbers*)
                  (before caller)))
           :in-theory (e/d (allocation-large-caller-saves-p)
                           (proof-register-frame-p proof-object-word allocation-string-header proof-streams-preserved-p)))))

(defthm allocation-large-call-heap-after-suffix
  (implies (and (allocation-large-caller-saves-p caller before)
                (proof-preserved-heap-p nil caller before old-objects objects packages)
                (proof-preserved-heap-p nil before after objects new-objects packages)
                (proof-span-p (proof-heap-base caller) 8)
                (allocation-memory-addresses-are-words-p (allocation-memory caller))
                (allocation-memory-addresses-are-words-p (allocation-memory after)))
           (proof-preserved-heap-p nil caller after old-objects new-objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-heap-preservation-compose-at-same-stack-top
                  (before caller) (middle before) (middle-objects objects)))
           :in-theory (e/d (allocation-large-caller-saves-p)
                           (proof-preserved-heap-p proof-register-frame-p
                            proof-stack-top proof-machine-limit proof-heap-base
                            allocation-memory-addresses-are-words-p proof-span-p)))))

(defthm allocation-large-constructor-return-after-publication
  (implies (and (allocation-large-caller-saves-p caller before)
                (allocation-large-postmap-result-p before after)
                (proof-register-frame-p 30 '(0 1 2 19 20 21 30) before after)
                (proof-preserved-heap-p nil caller before old-objects objects packages)
                (proof-preserved-heap-p nil before after objects new-objects packages)
                (proof-span-p (proof-heap-base caller) 8)
                (allocation-memory-addresses-are-words-p (allocation-memory caller))
                (allocation-memory-addresses-are-words-p (allocation-memory after))
                (proof-string-result-p length after new-objects packages))
           (proof-string-constructor-return-p length caller after old-objects new-objects packages))
  :rule-classes nil
  :hints (("Goal" :use (allocation-large-return-restores-caller-frame allocation-large-call-heap-after-suffix)
           :in-theory (disable allocation-large-postmap-result-p proof-frame-return-p proof-preserved-heap-p
                               proof-register-frame-p proof-string-result-p proof-span-p proof-heap-base))))

(defthm allocation-large-constructor-checked-return-from-mapped-state
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before))
         (machine (proof-world-machine before))
         (external (proof-external-objects (proof-external-head before) (len objects) before objects))
         (old-total (proof-external-bytes (cdr external) machine))
         (published (cons (proof-object (+ mapping 24) :external :header 0) objects))
         (path (allocation-large-postmap-path))
         (cuts (list (proof-world-reg 30 caller))))
    (implies (and (allocation-large-caller-saves-p caller before)
                  (allocation-large-mapped-entry-p origin before)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized))
                  (natp prefix-steps) (allocation-prefix-p prefix-steps cuts caller before)
                  (allocation-path-ready-p path cuts before)
                  (proof-preserved-heap-p nil caller before old-objects objects packages)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (allocation-memory-addresses-are-words-p (allocation-memory after))
                  (equal size (allocation-large-mapping-size length))
                  (equal (mod mapping 8) 0) (equal (mod base 8) 0)
                  (allocation-large-mapping-outside-reservations-p before)
                  (equal (proof-world-regions before) (cons (proof-region mapping (+ mapping size) :rw) old-regions))
                  (equal (allocation-memory before) (proof-clear-memory mapping (+ mapping size) memory))
                  (allocation-objects-outside-write-p mapping (+ mapping size) objects machine)
                  (< (+ old-total size) (expt 2 63))
                  (<= (+ (allocation-sp before) 32)
                      (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
                  (equal (mod (+ (allocation-sp before) 32) 16) 0))
             (and (proof-segment-p (+ prefix-steps (len path)) cuts caller :cut after)
                  (proof-string-constructor-return-p (proof-world-reg 0 caller) caller after old-objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-checked-heap-return-from-mapping allocation-large-suffix-register-frame
                 allocation-large-checked-suffix-effects
                 (:instance allocation-large-constructor-return-after-publication
                  (length (proof-world-reg 19 before)) (new-objects
                   (cons (proof-object (+ (proof-world-reg 0 before) 24) :external :header 0) objects)))
                 (:instance allocation-segment-after-prefix
                  (count prefix-steps) (remaining (len (allocation-large-postmap-path)))
                  (middle before) (before caller) (cuts (list (proof-world-reg 30 caller))) (reason :cut)))
           :in-theory (e/d (allocation-large-caller-saves-p)
                           (allocation-large-mapped-entry-p allocation-large-postmap-result-p allocation-large-layout-frame-p
                            allocation-large-insertion-p allocation-large-header-p allocation-large-mapping-size
                            allocation-large-initialization-writes allocation-write-words
                            allocation-prefix-p allocation-path-end allocation-path-ready-p proof-segment-p
                            proof-string-constructor-return-p proof-string-result-p proof-heap-p proof-frame-return-p
                            proof-heap-frame-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                            proof-clear-memory proof-external-objects proof-external-head proof-external-bytes
                            proof-span-p proof-register-frame-p allocation-objects-outside-write-p
                            allocation-memory-addresses-are-words-p mod)))))

(defthm allocation-large-size-prefix-saves-caller
  (let ((save (- (allocation-sp caller) 32)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (not (proof-world-stop caller))
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (<= 32 (allocation-sp caller))
                  (equal before (allocation-path-end *allocation-large-size-path* caller)))
             (and (equal (allocation-sp before) save)
                  (equal (proof-world-reg 19 before) (proof-world-reg 0 caller))
                  (equal (allocation-load-word save before) (proof-world-reg 21 caller))
                  (equal (allocation-load-word (+ 8 save) before) (proof-world-reg 30 caller))
                  (equal (allocation-load-word (+ 16 save) before) (proof-world-reg 19 caller))
                  (equal (allocation-load-word (+ 24 save) before) (proof-world-reg 20 caller))
                  (proof-register-frame-p 30 '(1 19) caller before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-register-range (register 0) (world caller)))
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (allocation-word-register-range allocation-unsigned-64-of-sum
                            allocation-unsigned-64-of-difference)))))
