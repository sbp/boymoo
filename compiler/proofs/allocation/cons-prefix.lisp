(in-package "BOYMOO-PROOFS")

(include-book "cons-caller")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-cons-save-writes (caller)
  (let ((save (- (allocation-sp caller) 16)))
    (list (cons save (proof-world-reg 29 caller))
          (cons (+ 8 save) (proof-world-reg 30 caller)))))

(defun allocation-cons-root-writes (caller)
  (let ((slot (proof-stack-top caller)))
    (list (cons slot (proof-world-reg 0 caller))
          (cons (+ 8 slot) (proof-world-reg 1 caller)))))

(defun allocation-cons-prologue-writes (caller)
  (append (allocation-cons-save-writes caller) (allocation-cons-root-writes caller)))

(defconst *allocation-cons-prologue-clobbers* '(0 2 8 9 10 11 12 24 25 30))

(defthm allocation-cons-growth-cut-effects
  (implies (and (allocation-cons-machine-entry-p origin caller)
                (not (proof-allocation-fits-p :cons 16 caller))
                (<= 16 (allocation-sp caller))
                (< (+ 16 (proof-stack-top caller)) *allocation-word-modulus*)
                (equal cut (allocation-path-end *allocation-cons-growth-path* caller)))
           (and (allocation-cons-growth-edge-p origin caller cut)
                (proof-register-frame-p 30 '(2 8 30) caller cut)
                (equal (allocation-memory cut)
                       (allocation-memory (allocation-write-words (allocation-cons-save-writes caller) caller)))
                (equal (proof-world-replies cut) (proof-world-replies caller))
                (proof-streams-preserved-p caller cut)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-cons-machine-to-growth (before caller)))
           :in-theory (disable allocation-cons-growth-edge-p
                               allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-cons-root-cut-effects
  (implies (and (allocation-code-origin-p origin)
                (allocation-machine-state-p before)
                (not (proof-world-stop before))
                (equal (proof-world-pc before) (allocation-cons-address origin 14))
                (< (+ 16 (proof-stack-top before)) *allocation-word-modulus*)
                (equal cut (allocation-path-end *allocation-cons-root-path* before)))
           (and (allocation-cons-root-edge-p origin before cut)
                (proof-register-frame-p 30 '(0 25 30) before cut)
                (equal (allocation-memory cut)
                       (allocation-memory (allocation-write-words (allocation-cons-root-writes before) before)))
                (equal (proof-world-regions cut) (proof-world-regions before))
                (equal (proof-world-replies cut) (proof-world-replies before))
                (proof-streams-preserved-p before cut)))
  :rule-classes nil
  :hints (("Goal" :use (allocation-cons-machine-to-allocator)
           :in-theory (disable allocation-cons-root-edge-p
                               allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-cons-growth-keeps-operands-and-stack
  (implies (proof-frame-return-p (allocation-growth-clobbers "rt:ensure-stack") t before after)
           (and (equal (proof-world-pc after) (proof-world-reg 30 before))
                (not (proof-world-stop after))
                (equal (allocation-sp after) (allocation-sp before))
                (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                (equal (proof-stack-top after) (proof-stack-top before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-member
                  (register 0) (upper 30) (clobbers (allocation-growth-clobbers "rt:ensure-stack")))
                 (:instance allocation-register-frame-member
                  (register 1) (upper 30) (clobbers (allocation-growth-clobbers "rt:ensure-stack")))
                 (:instance allocation-register-frame-member
                  (register 25) (upper 30) (clobbers (allocation-growth-clobbers "rt:ensure-stack"))))
           :in-theory (disable proof-register-frame-p))))

(defthm allocation-cons-after-growth-is-machine-state
  (implies (and (allocation-machine-state-p before)
                (equal after (allocation-path-end (allocation-growth-path "rt:ensure-stack" required before) before))
                (allocation-growth-machine-pre-p "rt:ensure-stack" required origin before)
                (<= required (proof-stack-end before)))
           (allocation-machine-state-p after))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable allocation-growth-path))))

(local
 (defthm allocation-cons-load-from-memory
   (equal (allocation-load-word address world)
          (boymoo-model::a64-read-bytes 8 address (allocation-memory world)))
   :hints (("Goal" :in-theory (enable allocation-load-word proof-load-word)))))

(local
 (defthm allocation-cons-sp-is-natural
   (natp (allocation-sp world))
   :rule-classes :type-prescription
   :hints (("Goal" :use ((:instance allocation-word-register-range (register 0)))
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p) (allocation-word-register-range))))))

(defthm allocation-cons-rooting-keeps-saved-word
  (let ((slot (proof-stack-top before))
        (save (allocation-sp before)))
    (implies (and (allocation-cons-root-edge-p origin before rooted)
                  (proof-span-p slot 16) (proof-span-p save 16)
                  (proof-disjoint-p slot (+ slot 16) save (+ save 16))
                  (member-equal offset '(0 8)))
             (equal (allocation-load-word (+ save offset) rooted)
                    (allocation-load-word (+ save offset) before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-after-disjoint-store
                  (world before) (word (proof-world-reg 0 before))
                  (address (proof-stack-top before)) (probe (+ (allocation-sp before) offset)))
                 (:instance allocation-word-after-disjoint-store
                  (world (allocation-store-word (proof-stack-top before) (proof-world-reg 0 before) before))
                  (word (proof-world-reg 1 before)) (address (+ 8 (proof-stack-top before)))
                  (probe (+ (allocation-sp before) offset))))
           :in-theory (disable allocation-word-after-disjoint-store allocation-cons-fields-p
                               allocation-code-address allocation-cons-address boymoo-model::a64-write-bytes))))

(local
 (defthm allocation-cons-frame-register-23
   (implies (proof-register-frame-p 30 *allocation-cons-clobbers-through-saves* before after)
            (equal (proof-machine-limit after) (proof-machine-limit before)))
   :hints (("Goal"
            :use ((:instance allocation-register-frame-member
                   (register 23) (upper 30) (clobbers *allocation-cons-clobbers-through-saves*)))))))

(defthm allocation-cons-rooted-caller-control-and-saves
  (let* ((save (- (allocation-sp caller) 16))
         (top (proof-stack-top caller)))
    (implies (and (allocation-cons-growth-edge-p origin caller cut)
                  (proof-register-frame-p 30 '(2 8 30) caller cut)
                  (proof-frame-return-p (allocation-growth-clobbers "rt:ensure-stack") t cut grown)
                  (equal (allocation-memory grown) (allocation-memory cut))
                  (allocation-cons-root-edge-p origin grown rooted)
                  (proof-register-frame-p 30 '(0 25 30) grown rooted)
                  (proof-span-p save 16)
                  (proof-span-p top 16)
                  (proof-disjoint-p top (+ top 16) save (+ save 16))
                  (not (proof-world-stop caller)))
             (and (allocation-cons-rooted-caller-frame-p caller rooted)
                  (allocation-cons-fields-p top (proof-world-reg 0 caller) (proof-world-reg 1 caller) rooted)
                  (proof-register-frame-p 30 *allocation-cons-prologue-clobbers* caller rooted))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-cons-growth-keeps-operands-and-stack (before cut) (after grown))
                 (:instance allocation-cons-rooting-keeps-saved-word (before grown) (offset 0))
                 (:instance allocation-cons-rooting-keeps-saved-word (before grown) (offset 8))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(2 8 30)) (large *allocation-cons-prologue-clobbers*)
                  (before caller) (after cut))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small (allocation-growth-clobbers "rt:ensure-stack"))
                  (large *allocation-cons-prologue-clobbers*) (before cut) (after grown))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(0 25 30)) (large *allocation-cons-prologue-clobbers*)
                  (before grown) (after rooted))
                 (:instance allocation-register-frame-transitive
                  (register 30) (clobbers *allocation-cons-prologue-clobbers*)
                  (before caller) (middle cut) (after grown))
                 (:instance allocation-register-frame-transitive
                  (register 30) (clobbers *allocation-cons-prologue-clobbers*)
                  (before caller) (middle grown) (after rooted))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small *allocation-cons-prologue-clobbers*) (large *allocation-cons-clobbers-through-saves*)
                  (before caller) (after rooted)))
           :in-theory (e/d (allocation-cons-rooted-caller-frame-p)
                           (proof-register-frame-p proof-span-p proof-disjoint-p
                            allocation-code-address allocation-cons-address boymoo-model::a64-write-bytes)))))

(defun allocation-cons-prologue-path (caller cut)
  (let ((required (+ 16 (proof-stack-top caller))))
    (append *allocation-cons-growth-path*
            (allocation-growth-path "rt:ensure-stack" required cut)
            *allocation-cons-root-path*)))

(local
 (defthm allocation-cons-prologue-spans
   (implies (and (proof-span-p (- (allocation-sp caller) 16) 16)
                 (< (+ (proof-stack-top caller) 16) *allocation-word-modulus*))
            (and (<= 16 (allocation-sp caller))
                 (proof-span-p (proof-stack-top caller) 16)))
   :rule-classes nil))

(defthm allocation-cons-ensure-stack-return-effects
  (let ((entry "rt:ensure-stack"))
    (implies (and (allocation-growth-machine-pre-p entry required origin cut)
                  (allocation-machine-state-p cut)
                  (<= required (proof-stack-end cut))
                  (or (<= required (proof-stack-limit cut)) (allocation-growth-doubling-fits-p cut))
                  (equal grown (allocation-path-end (allocation-growth-path entry required cut) cut)))
             (and (proof-frame-return-p (allocation-growth-clobbers entry) t cut grown)
                  (equal (allocation-memory grown) (allocation-memory cut))
                  (equal (proof-world-regions grown) (proof-world-regions cut))
                  (equal (proof-world-replies grown) (proof-world-replies cut))
                  (proof-streams-preserved-p cut grown)
                  (allocation-machine-state-p grown)
                  (not (proof-world-stop grown))
                  (equal (proof-world-pc grown) (proof-world-reg 30 cut))
                  (equal (proof-world-reg 0 grown) (proof-world-reg 0 cut))
                  (equal (proof-world-reg 1 grown) (proof-world-reg 1 cut))
                  (equal (proof-stack-limit grown) (proof-grow-limit required cut))
                  (equal (proof-stack-top grown) (proof-stack-top cut)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-growth-machine-return (entry "rt:ensure-stack") (before cut) (after grown))
                 (:instance allocation-cons-after-growth-is-machine-state (before cut) (after grown))
                 (:instance allocation-cons-growth-keeps-operands-and-stack (before cut) (after grown)))
           :in-theory (disable allocation-growth-path allocation-path-end allocation-growth-machine-pre-p
                               proof-frame-return-p allocation-growth-doubling-fits-p proof-grow-limit
                               proof-stack-limit proof-stack-end))))

(defthm allocation-cons-prologue-effects
  (let* ((top (proof-stack-top caller))
         (required (+ top 16))
         (save (- (allocation-sp caller) 16))
         (grow-path (allocation-growth-path "rt:ensure-stack" required cut))
         (target (allocation-code-address "rt:alloc-cells" origin)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (proof-span-p save 16)
                  (< required *allocation-word-modulus*)
                  (proof-disjoint-p top required save (+ save 16))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (allocation-growth-machine-pre-p "rt:ensure-stack" required origin cut)
                  (<= required (proof-stack-end cut))
                  (or (<= required (proof-stack-limit cut)) (allocation-growth-doubling-fits-p cut))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown)))
             (and (allocation-cons-rooted-caller-frame-p caller rooted)
                  (allocation-cons-fields-p top (proof-world-reg 0 caller) (proof-world-reg 1 caller) rooted)
                  (proof-register-frame-p 30 *allocation-cons-prologue-clobbers* caller rooted)
                  (equal (proof-world-pc rooted) target)
                  (equal (proof-world-reg 0 rooted) 16)
                  (not (proof-world-stop rooted)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-spans allocation-cons-growth-cut-effects
                 (:instance allocation-cons-ensure-stack-return-effects (required (+ 16 (proof-stack-top caller))))
                 (:instance allocation-cons-root-cut-effects (before grown) (cut rooted))
                 allocation-cons-rooted-caller-control-and-saves)
           :in-theory (disable allocation-growth-path allocation-path-end
                               allocation-growth-machine-pre-p allocation-growth-doubling-fits-p proof-allocation-fits-p
                               proof-frame-return-p proof-register-frame-p proof-span-p proof-grow-limit
                               proof-stack-end proof-stack-limit allocation-cons-rooted-caller-frame-p allocation-cons-fields-p
                               allocation-code-address allocation-cons-address mod))))

(defthm allocation-cons-prologue-memory-footprint
  (let* ((top (proof-stack-top caller))
         (required (+ top 16))
         (grow-path (allocation-growth-path "rt:ensure-stack" required cut)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (<= 16 (allocation-sp caller))
                  (< required *allocation-word-modulus*)
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (allocation-growth-machine-pre-p "rt:ensure-stack" required origin cut)
                  (<= required (proof-stack-end cut))
                  (or (<= required (proof-stack-limit cut)) (allocation-growth-doubling-fits-p cut))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown)))
             (and (equal (allocation-memory rooted)
                         (allocation-memory (allocation-write-words (allocation-cons-prologue-writes caller) caller)))
                  (equal (proof-world-regions rooted) (proof-world-regions caller))
                  (equal (proof-world-replies rooted) (proof-world-replies caller))
                  (proof-streams-preserved-p caller rooted))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-growth-cut-effects
                 (:instance allocation-cons-ensure-stack-return-effects (required (+ 16 (proof-stack-top caller))))
                 (:instance allocation-cons-root-cut-effects (before grown) (cut rooted)))
           :in-theory (disable allocation-growth-path allocation-path-end allocation-growth-machine-pre-p
                               allocation-growth-doubling-fits-p proof-allocation-fits-p proof-frame-return-p
                               proof-register-frame-p proof-span-p proof-stack-end proof-stack-limit
                               allocation-cons-fields-p allocation-code-address allocation-cons-address
                               boymoo-model::a64-write-bytes mod))))

(defthm allocation-cons-checked-prologue-to-roots
  (let* ((top (proof-stack-top caller))
         (required (+ top 16))
         (save (- (allocation-sp caller) 16))
         (grow-path (allocation-growth-path "rt:ensure-stack" required cut))
         (path (allocation-cons-prologue-path caller cut))
         (target (allocation-code-address "rt:alloc-cells" origin))
         (cuts (list target)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (proof-span-p save 16)
                  (< required *allocation-word-modulus*)
                  (proof-disjoint-p top required save (+ save 16))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller))
                  (allocation-growth-machine-pre-p "rt:ensure-stack" required origin cut)
                  (<= required (proof-stack-end cut))
                  (or (<= required (proof-stack-limit cut)) (allocation-growth-doubling-fits-p cut))
                  (equal grown (allocation-path-end grow-path cut))
                  (equal rooted (allocation-path-end *allocation-cons-root-path* grown))
                  (allocation-path-ready-p path cuts caller))
             (and (proof-segment-p (len path) cuts caller :cut rooted)
                  (allocation-cons-rooted-caller-frame-p caller rooted)
                  (allocation-cons-fields-p top (proof-world-reg 0 caller) (proof-world-reg 1 caller) rooted)
                  (equal (proof-world-reg 0 rooted) 16))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-effects
                 (:instance allocation-path-end-of-append
                  (first *allocation-cons-growth-path*)
                  (last (append (allocation-growth-path "rt:ensure-stack" (+ 16 (proof-stack-top caller)) cut)
                                *allocation-cons-root-path*))
                  (world caller))
                 (:instance allocation-path-end-of-append
                  (first (allocation-growth-path "rt:ensure-stack" (+ 16 (proof-stack-top caller)) cut))
                  (last *allocation-cons-root-path*) (world cut))
                 (:instance allocation-checked-cut
                  (instructions (allocation-cons-prologue-path caller cut)) (world caller) (after rooted)
                  (cuts (list (allocation-code-address "rt:alloc-cells" origin)))))
           :in-theory (disable allocation-growth-path allocation-path-end allocation-path-end-of-append
                               allocation-path-ready-p allocation-checked-cut proof-segment-p
                               allocation-growth-machine-pre-p allocation-growth-doubling-fits-p
                               allocation-cons-machine-entry-p proof-allocation-fits-p proof-span-p proof-stack-end proof-stack-limit
                               allocation-cons-rooted-caller-frame-p allocation-cons-fields-p
                               allocation-code-address allocation-cons-address mod))))
