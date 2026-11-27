(in-package "BOYMOO-PROOFS")

(include-book "cons-prefix")
(include-book "placement")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defund allocation-cons-prologue-room-p (caller)
  (let* ((save (- (allocation-sp caller) 16))
         (top (proof-stack-top caller))
         (machine-start (- (proof-machine-limit caller) *proof-machine-margin*)))
    (and (posp save) (posp top)
         (proof-subspan-p save 16 machine-start (+ machine-start *proof-machine-reservation*))
         (<= (+ 16 top) (proof-stack-end caller))
         (< (+ 16 top) *allocation-word-modulus*))))

(local
 (defthm allocation-cons-caller-layout-stack-ranges
   (let* ((machine-start (- (proof-machine-limit caller) *proof-machine-margin*))
          (machine-end (+ machine-start *proof-machine-reservation*)))
     (implies (proof-heap-layout-p caller)
              (and (<= (proof-stack-base caller) (proof-stack-top caller))
                   (<= (allocation-sp caller) machine-end)
                   (proof-disjoint-p (proof-stack-base caller) (proof-stack-end caller) machine-start machine-end))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                                      proof-runtime-word mod)))))

(local
 (defthm allocation-pair-writes-avoid-range
   (implies (and (posp start) (proof-span-p start 16)
                 (proof-disjoint-p start (+ 16 start) lower upper))
            (allocation-word-writes-avoid-span-p
             (list (cons start first) (cons (+ 8 start) second)) lower upper))))

(local
 (defthm allocation-avoid-span-of-appended-writes
   (equal (allocation-word-writes-avoid-span-p (append first last) lower upper)
          (and (allocation-word-writes-avoid-span-p first lower upper)
               (allocation-word-writes-avoid-span-p last lower upper)))
   :hints (("Goal" :induct (append first last)
            :in-theory (disable proof-span-p proof-disjoint-p)))))

(local
 (defthm allocation-cons-prologue-intervals
   (let* ((base (proof-heap-base caller))
          (heap-start (- base *proof-heap-prefix*))
          (heap-end (proof-spaces-end caller))
          (stack (proof-stack-base caller))
          (top (proof-stack-top caller))
          (sp (allocation-sp caller))
          (save (- sp 16))
          (machine-end (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*)))
     (implies (and (proof-heap-layout-p caller)
                   (allocation-cons-prologue-room-p caller))
              (and (posp save) (posp top)
                   (proof-span-p save 16) (proof-span-p top 16)
                   (proof-span-p stack (- top stack))
                   (proof-disjoint-p top (+ 16 top) save sp)
                   (proof-disjoint-p save sp heap-start heap-end)
                   (proof-disjoint-p top (+ 16 top) heap-start heap-end)
                   (proof-disjoint-p save sp stack top)
                   (proof-disjoint-p top (+ 16 top) stack top)
                   (proof-disjoint-p save sp sp machine-end)
                   (proof-disjoint-p top (+ 16 top) sp machine-end))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance allocation-layout-storage-spans (world caller))
                         allocation-cons-caller-layout-stack-ranges)
            :in-theory (e/d (allocation-cons-prologue-room-p)
                            (proof-heap-layout-p proof-spaces-end proof-heap-base proof-stack-base proof-stack-end
                             proof-machine-limit proof-stack-top proof-static-size proof-runtime-word
                             allocation-runtime-word-as-load))))))

(local
 (defthm allocation-cons-prologue-both-pairs-avoid-range
   (let* ((save (- (allocation-sp caller) 16))
          (top (proof-stack-top caller)))
     (implies (and (posp save) (posp top)
                   (proof-span-p save 16) (proof-span-p top 16)
                   (proof-disjoint-p save (+ save 16) lower upper)
                   (proof-disjoint-p top (+ top 16) lower upper))
              (allocation-word-writes-avoid-span-p (allocation-cons-prologue-writes caller) lower upper)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-pair-writes-avoid-range
                   (start (- (allocation-sp caller) 16))
                   (first (proof-world-reg 29 caller)) (second (proof-world-reg 30 caller)))
                  (:instance allocation-pair-writes-avoid-range
                   (start (proof-stack-top caller))
                   (first (proof-world-reg 0 caller)) (second (proof-world-reg 1 caller)))
                  (:instance allocation-avoid-span-of-appended-writes
                   (first (allocation-cons-save-writes caller)) (last (allocation-cons-root-writes caller))))
            :in-theory (disable proof-span-p proof-disjoint-p allocation-word-writes-avoid-span-p)))))

(defthm allocation-cons-prologue-writes-in-unused-stack
  (let* ((base (proof-heap-base caller))
         (heap-start (- base *proof-heap-prefix*))
         (heap-end (proof-spaces-end caller))
         (stack (proof-stack-base caller))
         (top (proof-stack-top caller))
         (sp (allocation-sp caller))
         (save (- sp 16))
         (machine-end (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*))
         (writes (allocation-cons-prologue-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller))
             (and (proof-span-p save 16)
                  (proof-span-p top 16)
                  (proof-disjoint-p top (+ 16 top) save sp)
                  (proof-disjoint-p save sp heap-start heap-end)
                  (proof-disjoint-p top (+ 16 top) heap-start heap-end)
                  (allocation-word-writes-avoid-span-p writes heap-start heap-end)
                  (allocation-word-writes-avoid-span-p writes stack top)
                  (allocation-word-writes-avoid-span-p writes sp machine-end)
                  (proof-span-p stack (- top stack)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-intervals
                 (:instance allocation-cons-prologue-both-pairs-avoid-range
                  (lower (- (proof-heap-base caller) *proof-heap-prefix*)) (upper (proof-spaces-end caller)))
                 (:instance allocation-cons-prologue-both-pairs-avoid-range
                  (lower (proof-stack-base caller)) (upper (proof-stack-top caller)))
                 (:instance allocation-cons-prologue-both-pairs-avoid-range
                  (lower (allocation-sp caller))
                  (upper (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (disable proof-heap-layout-p proof-span-p proof-disjoint-p proof-subspan-p
                               allocation-word-writes-avoid-span-p proof-spaces-end proof-heap-base proof-stack-base
                               proof-stack-top proof-machine-limit proof-runtime-word allocation-runtime-word-as-load))))

(local
 (defthm allocation-two-word-subspans-avoid-objects
   (implies (allocation-objects-outside-write-p start (+ 16 start) objects machine)
            (and (allocation-objects-outside-write-p start (+ 8 start) objects machine)
                 (allocation-objects-outside-write-p (+ 8 start) (+ 16 start) objects machine)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-objects-outside-subspan (end (+ 16 start)) (lower start) (upper (+ 8 start)))
                  (:instance allocation-objects-outside-subspan (end (+ 16 start)) (lower (+ 8 start)) (upper (+ 16 start))))
            :in-theory (disable allocation-objects-outside-write-p)))))

(defthm allocation-cons-prologue-avoids-published-objects
  (implies (and (proof-heap-p caller objects packages)
                (allocation-cons-prologue-room-p caller))
           (allocation-word-writes-outside-objects-p
            (allocation-cons-prologue-writes caller) objects (proof-world-machine caller)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 allocation-cons-prologue-writes-in-unused-stack
                 allocation-cons-caller-layout-stack-ranges
                 (:instance allocation-published-objects-avoid-fresh-or-stack-span
                  (world caller) (start (- (allocation-sp caller) 16)) (end (allocation-sp caller)))
                 (:instance allocation-published-objects-avoid-fresh-or-stack-span
                  (world caller) (start (proof-stack-top caller)) (end (+ 16 (proof-stack-top caller))))
                 (:instance allocation-two-word-subspans-avoid-objects
                  (start (- (allocation-sp caller) 16)) (machine (proof-world-machine caller)))
                 (:instance allocation-two-word-subspans-avoid-objects
                  (start (proof-stack-top caller)) (machine (proof-world-machine caller))))
           :in-theory (e/d (allocation-cons-prologue-room-p)
                           (proof-heap-p proof-heap-layout-p allocation-objects-outside-write-p
                            allocation-word-writes-avoid-span-p proof-disjoint-p proof-heap-base
                            proof-stack-base proof-stack-end proof-runtime-word allocation-runtime-word-as-load)))))

(local
 (defthm allocation-cons-prologue-keeps-heap-base
   (implies (allocation-cons-rooted-caller-frame-p caller rooted)
            (equal (proof-heap-base rooted) (proof-heap-base caller)))
   :hints (("Goal"
            :use ((:instance allocation-register-frame-member
                   (register 28) (upper 30) (clobbers *allocation-cons-clobbers-through-saves*)
                   (before caller) (after rooted)))
            :in-theory (e/d (allocation-cons-rooted-caller-frame-p) (proof-register-frame-p))))))

(defthm allocation-cons-prologue-roots-represent-arguments
  (let* ((slot (proof-stack-top caller))
         (left-word (proof-world-reg 0 caller))
         (right-word (proof-world-reg 1 caller))
         (writes (allocation-cons-prologue-writes caller)))
    (implies (and (allocation-cons-rooted-caller-frame-p caller rooted)
                  (allocation-cons-fields-p slot left-word right-word rooted)
                  (equal (allocation-memory rooted) (allocation-memory (allocation-write-words writes caller)))
                  (proof-heap-p caller objects packages)
                  (allocation-cons-prologue-room-p caller)
                  (proof-reg-value-p 0 left caller objects packages)
                  (proof-reg-value-p 1 right caller objects packages))
             (and (proof-machine-value-p (allocation-load-word slot rooted) left rooted objects packages)
                  (proof-machine-value-p (allocation-load-word (+ 8 slot) rooted) right rooted objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-avoids-published-objects
                 (:instance allocation-word-writes-keep-views
                  (base (proof-heap-base caller)) (world caller)
                  (writes (allocation-cons-prologue-writes caller)) (word (proof-world-reg 0 caller)))
                 (:instance allocation-word-writes-keep-views
                  (base (proof-heap-base caller)) (world caller)
                  (writes (allocation-cons-prologue-writes caller)) (word (proof-world-reg 1 caller)))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first rooted) (last (allocation-write-words (allocation-cons-prologue-writes caller) caller))))
           :in-theory (disable proof-heap-p proof-view proof-heap-base allocation-write-words
                               allocation-cons-prologue-writes allocation-word-writes-outside-objects-p
                               allocation-equal-memory-is-model-equivalence))))

(defthm allocation-cons-prologue-protects-heap-and-machine-frames
  (let* ((heap-start (- (proof-heap-base caller) *proof-heap-prefix*))
         (heap-end (proof-spaces-end caller))
         (sp (allocation-sp caller))
         (machine-end (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*))
         (writes (allocation-cons-prologue-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (equal (allocation-memory rooted) (allocation-memory (allocation-write-words writes caller))))
             (and (proof-memory-span-agrees-p heap-start heap-end caller rooted)
                  (proof-memory-span-agrees-p sp machine-end caller rooted))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-writes-in-unused-stack allocation-cons-caller-layout-stack-ranges
                 (:instance allocation-layout-storage-spans (world caller))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-cons-prologue-writes caller)) (world caller) (after rooted)
                  (lower (- (proof-heap-base caller) *proof-heap-prefix*)) (upper (proof-spaces-end caller)))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-cons-prologue-writes caller)) (world caller) (after rooted)
                  (lower (allocation-sp caller))
                  (upper (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (disable proof-heap-layout-p allocation-write-words allocation-cons-prologue-writes
                               proof-memory-span-agrees-p allocation-word-writes-avoid-span-p
                               proof-stack-base proof-spaces-end proof-machine-limit proof-heap-base
                               proof-runtime-word allocation-runtime-word-as-load))))

(defthm allocation-cons-prologue-keeps-runtime-word
  (let* ((base (proof-heap-base caller))
         (start (- base *proof-heap-prefix*))
         (end (proof-spaces-end caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-rooted-caller-frame-p caller rooted)
                  (proof-memory-span-agrees-p start end caller rooted)
                  (natp offset) (<= offset 80))
             (equal (proof-runtime-word offset rooted) (proof-runtime-word offset caller))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-storage-spans (world caller))
                 (:instance allocation-word-in-agreeing-span
                  (before caller) (after rooted) (lower (- (proof-heap-base caller) *proof-heap-prefix*))
                  (upper (proof-spaces-end caller)) (address (+ (- (proof-heap-base caller) 128) offset))))
           :in-theory (e/d (allocation-runtime-word-as-load)
                           (proof-heap-layout-p proof-heap-base proof-static-size proof-stack-base proof-stack-end
                            proof-spaces-end proof-runtime-word proof-memory-span-agrees-p)))))

(defthm allocation-cons-prologue-preserves-shared-heap-frame
  (let ((writes (allocation-cons-prologue-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-rooted-caller-frame-p caller rooted)
                  (allocation-cons-prologue-room-p caller)
                  (equal (allocation-memory rooted) (allocation-memory (allocation-write-words writes caller)))
                  (proof-streams-preserved-p caller rooted))
             (proof-heap-frame-p caller rooted)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-protects-heap-and-machine-frames
                 (:instance allocation-layout-storage-spans (world caller))
                 (:instance allocation-cons-prologue-keeps-runtime-word (offset 40))
                 (:instance allocation-cons-prologue-keeps-runtime-word (offset 48))
                 (:instance allocation-cons-prologue-keeps-runtime-word (offset 64))
                 (:instance allocation-memory-span-agreement-in-contained-span
                  (before caller) (after rooted) (lower (- (proof-heap-base caller) *proof-heap-prefix*))
                  (upper (proof-spaces-end caller)) (start (proof-heap-base caller)) (end (+ 24 (proof-heap-base caller))))
                 (:instance allocation-memory-span-agreement-in-contained-span
                  (before caller) (after rooted) (lower (- (proof-heap-base caller) *proof-heap-prefix*))
                  (upper (proof-spaces-end caller)) (start (+ 32 (proof-heap-base caller)))
                  (end (+ (proof-heap-base caller) (proof-static-size (proof-heap-base caller) (proof-world-machine caller))))))
           :in-theory (disable proof-heap-layout-p proof-memory-span-agrees-p proof-static-size
                               proof-heap-base proof-machine-limit allocation-cons-prologue-writes allocation-write-words
                               proof-streams-preserved-p proof-runtime-word allocation-runtime-word-as-load))))

(local
 (defthm allocation-cons-stack-index-from-top
   (implies (and (natp index) (integerp stack) (equal top (+ stack (* 8 index))))
            (and (equal (ash (- top stack) -3) index)
                 (equal (mod (- top stack) 8) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable mod ash)))))

(defthm allocation-cons-prologue-preserves-live-stack
  (let* ((stack (proof-stack-base caller))
         (top (proof-stack-top caller))
         (writes (allocation-cons-prologue-writes caller)))
    (implies (and (proof-heap-p caller objects packages)
                  (allocation-cons-prologue-room-p caller)
                  (allocation-cons-rooted-caller-frame-p caller rooted)
                  (equal (allocation-memory rooted) (allocation-memory (allocation-write-words writes caller)))
                  (natp index) (equal top (+ stack (* 8 index))))
             (proof-prefix-preserved-p top caller rooted objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 (:instance allocation-heap-stack-prefix-exists (world caller))
                 allocation-cons-prologue-writes-in-unused-stack allocation-cons-prologue-avoids-published-objects
                 allocation-cons-prologue-protects-heap-and-machine-frames
                 allocation-cons-prologue-keeps-heap-base
                 (:instance allocation-cons-stack-index-from-top
                  (top (proof-stack-top caller)) (stack (proof-stack-base caller)))
                 (:instance allocation-cons-prologue-keeps-runtime-word (offset 40))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first rooted) (last (allocation-write-words (allocation-cons-prologue-writes caller) caller)))
                 (:instance allocation-word-writes-keep-stack-views
                  (address (proof-stack-base caller)) (count index) (base (proof-heap-base caller))
                  (world caller) (writes (allocation-cons-prologue-writes caller))))
           :in-theory (e/d (allocation-cons-rooted-caller-frame-p)
                           (proof-heap-p proof-heap-layout-p proof-heap-base proof-load-word
                            proof-register-frame-p proof-stack-views proof-runtime-word proof-span-p
                            proof-memory-span-agrees-p allocation-equal-memory-is-model-equivalence
                            allocation-cons-prologue-writes allocation-write-words allocation-runtime-word-as-load
                            allocation-word-writes-outside-objects-p allocation-word-writes-avoid-span-p mod ash)))))

(defthm allocation-cons-prologue-preserves-dynamic-table
  (let ((writes (allocation-cons-prologue-writes caller)))
    (implies (and (proof-heap-p caller objects packages)
                  (allocation-cons-prologue-room-p caller)
                  (allocation-cons-rooted-caller-frame-p caller rooted)
                  (equal (allocation-memory rooted) (allocation-memory (allocation-write-words writes caller))))
             (proof-dynamic-table-preserved-p nil caller rooted objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 (:instance allocation-layout-storage-spans (world caller))
                 allocation-cons-prologue-avoids-published-objects allocation-cons-prologue-protects-heap-and-machine-frames
                 (:instance allocation-word-in-agreeing-span
                  (before caller) (after rooted) (lower (- (proof-heap-base caller) *proof-heap-prefix*))
                  (upper (proof-spaces-end caller)) (address (+ (proof-heap-base caller) 24)))
                 (:instance allocation-word-writes-keep-views
                  (base (proof-heap-base caller)) (world caller) (writes (allocation-cons-prologue-writes caller))
                  (word (proof-dynamic-root (proof-heap-base caller) (proof-world-machine caller))))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first rooted) (last (allocation-write-words (allocation-cons-prologue-writes caller) caller))))
           :in-theory (e/d (allocation-load-word)
                           (proof-heap-p proof-heap-layout-p proof-view proof-heap-base proof-load-word
                            proof-runtime-word allocation-runtime-word-as-load proof-memory-span-agrees-p
                            proof-spaces-end proof-static-size
                            allocation-equal-memory-is-model-equivalence allocation-cons-prologue-writes
                            allocation-write-words allocation-word-writes-outside-objects-p)))))

(defthm allocation-cons-save-writes-avoid-heap
  (let* ((base (proof-heap-base caller))
         (lower (- base *proof-heap-prefix*))
         (upper (proof-spaces-end caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller))
             (allocation-word-writes-avoid-span-p (allocation-cons-save-writes caller) lower upper)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-prologue-intervals
                 (:instance allocation-pair-writes-avoid-range
                  (start (- (allocation-sp caller) 16))
                  (first (proof-world-reg 29 caller)) (second (proof-world-reg 30 caller))
                  (lower (- (proof-heap-base caller) *proof-heap-prefix*)) (upper (proof-spaces-end caller))))
           :in-theory (disable proof-heap-layout-p proof-disjoint-p proof-span-p
                               allocation-word-writes-avoid-span-p proof-heap-base proof-spaces-end))))

(local
 (defun allocation-stack-pair-prefix-induct (count address)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       address
     (allocation-stack-pair-prefix-induct (1- count) (+ 8 address)))))

(defthm allocation-stack-views-append-argument-pair
  (let* ((old (proof-stack-views count address base objects packages machine))
         (first (+ address (* 8 count)))
         (left (proof-view (proof-load-word first machine) base objects packages machine))
         (right (proof-view (proof-load-word (+ first 8) machine) base objects packages machine)))
    (implies (and (natp count) (natp address) old left right)
             (equal (proof-stack-views (+ count 2) address base objects packages machine)
                    (cons :slots (append (cdr old) (list left right))))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-stack-pair-prefix-induct count address)
           :expand ((:free (number) (proof-stack-views number address base objects packages machine)))
           :in-theory (disable (:definition proof-stack-views) proof-view proof-load-word))
          ("Subgoal *1/1"
           :expand ((:free (spot) (proof-stack-views 0 spot base objects packages machine))
                    (proof-stack-views 2 address base objects packages machine)
                    (proof-stack-views 1 (+ 8 address) base objects packages machine)))))

(defthm allocation-stack-prefix-extended-with-argument-pair
  (let* ((base (proof-stack-base world))
         (top (proof-stack-top world))
         (slot (+ base (* 8 index)))
         (old (proof-stack-prefix slot world objects packages)))
    (implies (and (natp index) (equal top (+ slot 16)) old
                  (proof-machine-value-p (allocation-load-word slot world) left world objects packages)
                  (proof-machine-value-p (allocation-load-word (+ slot 8) world) right world objects packages))
             (equal (proof-stack-prefix top world objects packages)
                    (cons :slots (append (cdr old) (list (proof-value-view left) (proof-value-view right)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-stack-views-append-argument-pair
                  (count index) (address (proof-stack-base world)) (base (proof-heap-base world))
                  (machine (proof-world-machine world)))
                 (:instance allocation-cons-stack-index-from-top
                  (stack (proof-stack-base world))
                  (top (+ (proof-stack-base world) (* 8 index))))
                 (:instance allocation-cons-stack-index-from-top
                  (stack (proof-stack-base world)) (top (proof-stack-top world)) (index (+ 2 index))))
           :in-theory (e/d (allocation-load-word)
                           (proof-stack-views proof-view proof-load-word proof-stack-base
                            proof-stack-top proof-heap-base mod ash)))))
