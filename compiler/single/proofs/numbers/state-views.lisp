(in-package "BOYMOO-PROOFS")

(include-book "execution")
(include-book "frames")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-read-bytes
                     boymoo-model::a64-write-bytes
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

(local
 (defund memory-image (machine)
   (boymoo-model::a64-state nil 0 0 0 (boymoo-model::a64-memory machine))))

(local
 (defthm load-from-memory-image
   (and (equal (boymoo-model::a64-load width address (memory-image machine))
               (boymoo-model::a64-load width address machine))
        (equal (proof-load-word address (memory-image machine))
               (proof-load-word address machine)))
   :hints (("Goal" :in-theory (enable memory-image)))))

(local
 (in-theory (disable boymoo-model::a64-load proof-load-word)))

(local
 (defthm limbs-in-memory-image
   (equal (proof-limbs-p count address (memory-image machine))
          (proof-limbs-p count address machine))
   :hints (("Goal" :induct (proof-limbs-p count address machine)))))

(local
 (defthm magnitude-in-memory-image
   (equal (proof-limb-magnitude count address (memory-image machine))
          (proof-limb-magnitude count address machine))
   :hints (("Goal" :induct (proof-limb-magnitude count address machine)))))

(local
 (defthm integer-view-in-memory-image
   (equal (proof-integer-view address (memory-image machine))
          (proof-integer-view address machine))))

(local
 (defthm bytes-in-memory-image
   (equal (proof-byte-list count address (memory-image machine))
          (proof-byte-list count address machine))
   :hints (("Goal" :induct (proof-byte-list count address machine)))))

(local
 (defthm string-in-memory-image
   (equal (proof-load-string count address (memory-image machine))
          (proof-load-string count address machine))))

(local
 (defthm view-step-in-memory-image
   (equal (proof-view-step kind input count depth base objects packages (memory-image machine))
          (proof-view-step kind input count depth base objects packages machine))
   :hints (("Goal"
            :induct (proof-view-step kind input count depth base objects packages machine)
            :in-theory (disable proof-integer-view proof-load-string proof-rational-value
                                proof-complex-value proof-symbol-value proof-cons-value
                                proof-span-p proof-word-tag proof-pointer-address
                                proof-header-type proof-header-size
                                proof-number-integer-parity)))))

(defthm proof-number-view-step-kept-with-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-view-step kind input count depth base objects packages last)
                  (proof-view-step kind input count depth base objects packages first)))
  :hints (("Goal"
           :use ((:instance view-step-in-memory-image (machine first))
                 (:instance view-step-in-memory-image (machine last)))
           :in-theory (e/d (memory-image)
                           (view-step-in-memory-image proof-view-step))))
  :rule-classes nil)

(defthm proof-number-view-kept-with-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-view word base objects packages last)
                  (proof-view word base objects packages first)))
  :hints (("Goal"
           :use ((:instance proof-number-view-step-kept-with-memory
                            (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base)
                                                           objects)))))))
           :in-theory (disable proof-view-step proof-word-tag proof-pointer-address)))
  :rule-classes nil)

(local
 (defthm byte-agreement-from-present-entry
   (implies (and (proof-byte-entries-agree-p entries start end before after)
                 (assoc-equal address entries)
                 (<= start address) (< address end))
            (equal (boymoo-model::a64-byte address after)
                   (boymoo-model::a64-byte address before)))
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries start end before after)
                   :in-theory (disable boymoo-model::a64-byte)))
   :rule-classes nil))

(local
 (defthm byte-agreement-from-both-memories
   (implies (and (unsigned-byte-p 64 address)
                 (<= start address) (< address end)
                 (proof-byte-entries-agree-p before start end before after)
                 (proof-byte-entries-agree-p after start end before after))
            (equal (boymoo-model::a64-byte address after)
                   (boymoo-model::a64-byte address before)))
   :hints (("Goal"
            :use ((:instance byte-agreement-from-present-entry (entries before))
                  (:instance byte-agreement-from-present-entry (entries after)))
            :in-theory (disable proof-byte-entries-agree-p)
            :cases ((assoc-equal address before) (assoc-equal address after))))
   :rule-classes nil))

(local
 (defthm read-bytes-agrees-inside-span
   (implies (and (natp count) (natp address)
                 (<= start address) (<= (+ address count) end)
                 (<= end (expt 2 64))
                 (proof-byte-entries-agree-p before start end before after)
                 (proof-byte-entries-agree-p after start end before after))
            (equal (boymoo-model::a64-read-bytes count address after)
                   (boymoo-model::a64-read-bytes count address before)))
   :hints (("Goal"
            :induct (boymoo-model::a64-read-bytes count address before)
            :in-theory (e/d ((:induction boymoo-model::a64-read-bytes))
                           (boymoo-model::a64-byte proof-byte-entries-agree-p
                            (:definition boymoo-model::a64-read-bytes)))
            :expand ((boymoo-model::a64-read-bytes count address before)
                     (boymoo-model::a64-read-bytes count address after)))
           ("Subgoal *1/2" :use byte-agreement-from-both-memories)
           ("Subgoal *1/1" :in-theory (enable boymoo-model::a64-read-bytes)))
   :rule-classes nil))

(defthm proof-number-load-agrees-inside-saved-span
  (implies (and (natp address) (<= start address) (<= (+ address 8) end)
                (<= end (expt 2 64))
                (proof-memory-span-agrees-p start end before after))
           (equal (proof-load-word address (proof-world-machine after))
                  (proof-load-word address (proof-world-machine before))))
  :hints (("Goal"
           :use ((:instance read-bytes-agrees-inside-span (count 8)
                            (before (boymoo-model::a64-memory (proof-world-machine before)))
                            (after (boymoo-model::a64-memory (proof-world-machine after)))))
           :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                           (proof-byte-entries-agree-p proof-world-machine))))
  :rule-classes nil)

(defthm proof-number-slot-ash-is-floor
  (implies (integerp bytes) (equal (ash bytes -3) (floor bytes 8)))
  :hints (("Goal" :in-theory (e/d (ash floor) (acl2::nonnegative-integer-quotient)))))

(local
 (defthm aligned-slot-count
   (implies (and (natp bytes) (equal (mod bytes 8) 0))
            (let ((count (ash bytes -3)))
              (and (natp count)
                   (equal (* 8 count) bytes)
                   (equal (ash (+ 8 bytes) -3) (1+ count))
                   (equal (mod (+ 8 bytes) 8) 0))))
   :hints (("Goal"
            :use ((:instance proof-number-quotient-and-remainder (a bytes) (b 8))
                  (:instance proof-number-floor-with-remainder
                             (a (+ 8 bytes)) (b 8) (q (1+ (floor bytes 8))))
                  (:instance proof-number-mod-with-remainder
                             (a (+ 8 bytes)) (b 8) (q (1+ (floor bytes 8))) (r 0)))))
   :rule-classes nil))

(local
 (defthm stack-views-with-one-more-slot
   (implies (and (natp count) (integerp address))
            (let ((prefix (proof-stack-views count address base objects packages machine))
                  (last (proof-view (proof-load-word (+ address (* 8 count)) machine)
                                    base objects packages machine)))
              (equal (proof-stack-views (1+ count) address base objects packages machine)
                     (and prefix last (append prefix (list last))))))
   :hints (("Goal"
            :induct (proof-stack-views count address base objects packages machine)
            :expand ((proof-stack-views (1+ count) address base objects packages machine))
            :in-theory (disable proof-view proof-value-view proof-number-integer-parity))
           ("Subgoal *1/1"
            :expand ((proof-stack-views 1 address base objects packages machine))))
   :rule-classes nil))

(local
 (defthm prefix-with-one-more-slot
   (implies (and (proof-stack-prefix top world objects packages)
                 (<= (+ 8 top) (proof-stack-top world))
                 (integerp (proof-stack-base world)))
            (let ((one (proof-view (proof-load-word top (proof-world-machine world))
                                   (proof-heap-base world) objects packages
                                   (proof-world-machine world))))
              (equal (proof-stack-prefix (+ 8 top) world objects packages)
                     (and one (append (proof-stack-prefix top world objects packages)
                                      (list one))))))
   :hints (("Goal"
            :use ((:instance aligned-slot-count (bytes (- top (proof-stack-base world))))
                  (:instance stack-views-with-one-more-slot
                             (count (ash (- top (proof-stack-base world)) -3))
                             (address (proof-stack-base world))
                             (base (proof-heap-base world))
                             (machine (proof-world-machine world))))
            :in-theory (disable proof-stack-views proof-view proof-heap-base
                                proof-stack-base proof-stack-top proof-world-machine
                                proof-number-slot-ash-is-floor)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm argument-views-of-append
   (equal (proof-argument-views (append slots more))
          (append (proof-argument-views slots) (proof-argument-views more)))))

(local
 (defthm argument-views-of-singleton
   (equal (proof-argument-views (list value))
          (list (proof-value-view value)))))

(local
 (defthm tail-of-list-with-appended-slot
   (implies (and (natp start) (<= start (len prefix)))
            (equal (nthcdr start (append prefix (list slot)))
                   (append (nthcdr start prefix) (list slot))))
   :hints (("Goal" :induct (nthcdr start prefix)))))

(local
 (defthm appended-slot-length
   (equal (len (append prefix (list slot))) (1+ (len prefix)))))

(defthm proof-number-frame-after-appending-slot
  (let ((top (proof-stack-top before)))
    (implies (and (proof-number-frame-p start slots before old-objects packages)
                  (proof-prefix-preserved-p top before after old-objects objects packages)
                  (equal (proof-stack-top after) (+ 8 top))
                  (integerp (proof-stack-base after))
                  (proof-machine-value-p (proof-load-word top (proof-world-machine after))
                                         value after objects packages))
             (proof-number-frame-p start (append slots (list value)) after objects packages)))
  :hints (("Goal"
           :use ((:instance prefix-with-one-more-slot
                            (world after) (top (proof-stack-top before)))
                 (:instance tail-of-list-with-appended-slot
                            (prefix (cdr (proof-stack-prefix (proof-stack-top before)
                                                           after objects packages)))
                            (slot (proof-value-view value))))
           :in-theory (e/d (proof-number-frame-p)
                           (proof-stack-prefix proof-view proof-argument-views
                            proof-stack-top proof-stack-base proof-heap-base
                            proof-world-machine nth len true-listp
                            tail-of-list-with-appended-slot))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm tail-after-whole-prefix
   (equal (nthcdr (len prefix) (append prefix suffix)) suffix)
   :hints (("Goal" :induct (len prefix)))))

(local
 (defthm append-association
   (equal (append (append left middle) right)
          (append left (append middle right)))
   :hints (("Goal" :induct (len left)))))

(local
 (defthm append-length
   (equal (len (append left right)) (+ (len left) (len right)))
   :hints (("Goal" :induct (len left)))))

(local
 (defthm prefix-with-two-more-slots
   (let* ((machine (proof-world-machine world))
          (base (proof-heap-base world))
          (first (proof-view (proof-load-word top machine) base objects packages machine))
          (second (proof-view (proof-load-word (+ 8 top) machine) base objects packages machine))
          (prefix (proof-stack-prefix top world objects packages)))
     (implies (and prefix first second (integerp (proof-stack-base world))
                   (<= (+ 16 top) (proof-stack-top world)))
              (equal (proof-stack-prefix (+ 16 top) world objects packages)
                     (append prefix (list first second)))))
   :hints (("Goal"
            :use (prefix-with-one-more-slot
                  (:instance prefix-with-one-more-slot (top (+ 8 top))))
            :in-theory (disable proof-stack-prefix proof-view proof-load-word
                                proof-heap-base proof-world-machine proof-stack-base proof-stack-top)
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-argument-list-p (args)
  (and (consp args)
       (or (null (cdr args))
           (and (consp (cdr args)) (null (cddr args))))))

(defthm proof-number-frame-initialized-with-arguments
  (let* ((top (proof-stack-top before))
         (prefix (proof-stack-prefix top before old-objects packages))
         (start (len (cdr prefix)))
         (arity (len args))
         (machine (proof-world-machine after)))
    (implies (and (proof-number-argument-list-p args)
                  (proof-prefix-preserved-p top before after old-objects objects packages)
                  (equal (proof-stack-top after) (+ top (* 8 arity)))
                  (integerp (proof-stack-base after))
                  (proof-machine-value-p (proof-load-word top machine)
                                         (car args) after objects packages)
                  (implies (equal arity 2)
                           (proof-machine-value-p (proof-load-word (+ 8 top) machine)
                                                  (cadr args) after objects packages)))
             (proof-number-frame-p start args after objects packages)))
  :hints (("Goal"
           :use ((:instance prefix-with-one-more-slot
                            (world after) (top (proof-stack-top before)))
                 (:instance prefix-with-two-more-slots
                            (world after) (top (proof-stack-top before))))
           :in-theory (e/d (proof-number-frame-p proof-value-p proof-number-argument-list-p)
                           (proof-stack-prefix proof-view proof-stack-base proof-stack-top
                            proof-heap-base proof-world-machine proof-load-word))
           :expand ((len (cdr args)) (proof-argument-views (cdr args)))
           :cases ((null (cdr args)))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-prefix-end-is-frame-address
  (let* ((prefix (proof-stack-prefix top world objects packages))
         (start (len (cdr prefix))))
    (implies (and prefix (integerp (proof-stack-base world)))
             (equal (proof-number-frame-address start world) top)))
  :hints (("Goal"
           :use (proof-number-stack-prefix-length
                 (:instance aligned-slot-count (bytes (- top (proof-stack-base world)))))
           :in-theory (disable proof-stack-views proof-stack-base proof-stack-top
                               proof-number-slot-ash-is-floor
                               proof-heap-base proof-world-machine)))
  :rule-classes nil)

(local
 (defthm view-in-memory-image
   (equal (proof-view word base objects packages (memory-image machine))
          (proof-view word base objects packages machine))
   :hints (("Goal" :in-theory (disable proof-view-step proof-word-tag proof-pointer-address)))))

(local
 (defthm stack-views-in-memory-image
   (equal (proof-stack-views count address base objects packages (memory-image machine))
          (proof-stack-views count address base objects packages machine))
   :hints (("Goal"
            :induct (proof-stack-views count address base objects packages machine)
            :in-theory (disable proof-view proof-view-step)))))

(local
 (defthm stack-views-with-same-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-stack-views count address base objects packages last)
                   (proof-stack-views count address base objects packages first)))
   :hints (("Goal"
            :use ((:instance stack-views-in-memory-image (machine first))
                  (:instance stack-views-in-memory-image (machine last)))
            :in-theory (e/d (memory-image)
                            (stack-views-in-memory-image proof-stack-views))))
   :rule-classes nil))

(defthm proof-number-frame-kept-with-memory
  (implies (and (proof-number-frame-p start slots before objects packages)
                (equal (proof-stack-top after) (proof-stack-top before))
                (equal (proof-heap-base after) (proof-heap-base before))
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (boymoo-model::a64-memory (proof-world-machine before))))
           (proof-number-frame-p start slots after objects packages))
  :hints (("Goal"
           :use ((:instance stack-views-with-same-memory
                            (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (e/d (proof-number-frame-p proof-load-word boymoo-model::a64-load)
                           (proof-stack-views proof-stack-top proof-heap-base
                            proof-world-machine proof-argument-views))
           :do-not-induct t))
  :rule-classes nil)
