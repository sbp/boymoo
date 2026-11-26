(in-package "BOYMOO-PROOFS")

(include-book "heap-layout")
(include-book "memory-invariant")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p
                     proof-world-machine proof-world-reg proof-world-stop
                     proof-number-memory-byte-keys-p proof-stack-base proof-stack-top
                     proof-heap-base proof-load-word proof-view proof-stack-views
                     proof-number-machine-span-agrees-p proof-memory-span-agrees-p
                     proof-number-slot-ash-is-floor boymoo-model::a64-sp
                     boymoo-model::a64-byte boymoo-model::a64-memory
                     floor mod ash)))

(local
 (defthm byte-entries-agreement-composes
   (implies (and (proof-number-memory-byte-keys-p entries)
                 (proof-number-machine-span-agrees-p start end first middle)
                 (proof-number-machine-span-agrees-p start end middle last))
            (proof-byte-entries-agree-p
             entries start end (boymoo-model::a64-memory first) (boymoo-model::a64-memory last)))
   :hints (("Goal"
            :induct (proof-byte-entries-agree-p
                     entries start end (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            :in-theory (enable proof-number-memory-byte-keys-p))
           (and stable-under-simplificationp
                '(:use ((:instance proof-number-byte-agrees-in-machine-span
                                   (address (caar entries)) (last middle))
                        (:instance proof-number-byte-agrees-in-machine-span
                                   (address (caar entries)) (first middle))))))
   :rule-classes nil))

(defthm proof-number-span-agreement-composes
  (implies (and (proof-number-world-byte-keys-p before)
                (proof-number-world-byte-keys-p after)
                (proof-memory-span-agrees-p start end before middle)
                (proof-memory-span-agrees-p start end middle after))
           (proof-memory-span-agrees-p start end before after))
  :hints (("Goal"
           :use ((:instance byte-entries-agreement-composes
                            (entries (boymoo-model::a64-memory (proof-world-machine before)))
                            (first (proof-world-machine before))
                            (middle (proof-world-machine middle))
                            (last (proof-world-machine after)))
                 (:instance byte-entries-agreement-composes
                            (entries (boymoo-model::a64-memory (proof-world-machine after)))
                            (first (proof-world-machine before))
                            (middle (proof-world-machine middle))
                            (last (proof-world-machine after))))
           :in-theory (e/d (proof-number-world-byte-keys-p proof-number-machine-span-agrees-p
                            proof-memory-span-agrees-p proof-world-machine)
                           (proof-byte-entries-agree-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-span-agreement-narrows
  (implies (and (proof-memory-span-agrees-p start end before after)
                (<= start low) (<= high end))
           (proof-memory-span-agrees-p low high before after))
  :hints (("Goal"
           :use ((:instance proof-number-subspan-agrees
                            (lower start) (upper end) (start low) (end high)
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (e/d (proof-memory-span-agrees-p proof-number-machine-span-agrees-p proof-world-machine)
                           (proof-byte-entries-agree-p))))
  :rule-classes nil)

(defthm proof-number-run-preserves-byte-keys
  (implies (proof-number-world-byte-keys-p world)
           (proof-number-world-byte-keys-p (mv-nth 1 (proof-run count cuts world))))
  :hints (("Goal" :induct (proof-run count cuts world)
                  :in-theory (enable proof-run))))

(local
 (defun count-both-prefixes (short long address)
   (declare (xargs :measure (nfix short)))
   (if (zp short)
       (list long address)
     (count-both-prefixes (1- short) (1- long) (+ 8 address)))))

(local
 (defthm tag-of-valid-stack-views
   (implies (proof-stack-views count address base objects packages machine)
            (equal (car (proof-stack-views count address base objects packages machine)) :slots))
   :hints (("Goal" :expand ((proof-stack-views count address base objects packages machine))))
   :rule-classes nil))

(local
 (defthm cdr-of-take
   (implies (natp count)
            (equal (cdr (take (1+ count) entries)) (take count (cdr entries))))
   :hints (("Goal" :expand ((take (1+ count) entries))))))

(local
 (defthmd take-of-tagged-slots
   (implies (posp short)
            (equal (take (1+ short) (list* :slots first (cdr rest)))
                   (list* :slots first (cdr (take short rest)))))
   :hints (("Goal"
            :use ((:instance cdr-of-take (count (1- short)) (entries rest)))
            :expand ((take (1+ short) (list* :slots first (cdr rest)))
                     (take short (cons first (cdr rest))))
            :in-theory (disable take cdr-of-take)))))

(local
 (defthm take-positive-is-cons
   (implies (posp count) (consp (take count items)))
   :hints (("Goal" :expand ((take count items))))))

(defthm proof-number-stack-views-prefix
  (let ((full (proof-stack-views long address base objects packages machine)))
    (implies (and full (natp short) (natp long) (<= short long))
             (equal (proof-stack-views short address base objects packages machine)
                    (take (1+ short) full))))
  :hints (("Goal"
           :induct (count-both-prefixes short long address)
           :expand ((proof-stack-views short address base objects packages machine)
                    (proof-stack-views long address base objects packages machine))
           :in-theory (disable (:definition take)))
          ("Subgoal *1/2"
           :use ((:instance take-of-tagged-slots
                            (first (proof-view (proof-load-word address machine) base objects packages machine))
                            (rest (proof-stack-views (1- long) (+ 8 address) base objects packages machine)))
                 (:instance take-positive-is-cons
                            (count short)
                            (items (proof-stack-views (1- long) (+ 8 address) base objects packages machine)))))
          ("Subgoal *1/1"
           :use ((:instance tag-of-valid-stack-views (count long)))
           :in-theory (enable take proof-stack-views)))
  :rule-classes nil)

(local
 (defthm aligned-slot-count-is-exact
   (implies (and (natp bytes) (equal (mod bytes 8) 0))
            (and (natp (ash bytes -3)) (equal (* 8 (ash bytes -3)) bytes)))
   :hints (("Goal"
            :use ((:instance proof-number-quotient-and-remainder (a bytes) (b 8))
                  (:instance proof-number-positive-divisor-floor-bounds (a bytes) (b 8)))
            :in-theory (enable proof-number-slot-ash-is-floor)))
   :rule-classes nil))

(defthm proof-number-shorter-prefix-is-retained
  (let ((base (proof-stack-base before)))
    (implies (and (proof-prefix-preserved-p top before after old-objects new-objects packages)
                  (equal (proof-stack-base after) base)
                  (natp short) (<= base short) (<= short top)
                  (equal (mod (- short base) 8) 0))
             (proof-prefix-preserved-p short before after old-objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance aligned-slot-count-is-exact (bytes (- short (proof-stack-base before))))
                 (:instance aligned-slot-count-is-exact (bytes (- top (proof-stack-base before))))
                 (:instance proof-number-stack-views-prefix
                            (long (ash (- top (proof-stack-base before)) -3))
                            (short (ash (- short (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (objects old-objects) (machine (proof-world-machine before)))
                 (:instance proof-number-stack-views-prefix
                            (long (ash (- top (proof-stack-base after)) -3))
                            (short (ash (- short (proof-stack-base after)) -3))
                            (address (proof-stack-base after)) (base (proof-heap-base after))
                            (objects new-objects) (machine (proof-world-machine after)))
                 (:instance take-positive-is-cons
                            (count (1+ (ash (- short (proof-stack-base after)) -3)))
                            (items (proof-stack-views (ash (- top (proof-stack-base after)) -3)
                                                     (proof-stack-base after) (proof-heap-base after)
                                                     new-objects packages (proof-world-machine after)))))
           :in-theory (disable take)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm heap-static-header-end-fits
   (implies (proof-heap-layout-p world)
            (and (natp (proof-heap-base world))
                 (<= (+ 24 (proof-heap-base world)) (expt 2 64))))
   :hints (("Goal"
            :use (proof-number-heap-layout-range-bounds
                  (:instance proof-number-reg-range (register 28) (machine (proof-world-machine world))))
            :in-theory (e/d (proof-heap-layout-p proof-heap-base)
                            (proof-covered-p proof-align-up proof-runtime-word proof-disjoint-p
                             proof-inactive-floor proof-inactive-end proof-active-floor
                             proof-active-end proof-cons-floor proof-spaces-end proof-regions-p
                             proof-box-top proof-heap-limit proof-reg))))
   :rule-classes nil))

(defthm proof-number-heap-frames-compose
  (implies (and (proof-heap-layout-p before)
                (proof-heap-frame-p before middle)
                (proof-heap-frame-p middle after)
                (equal (proof-machine-limit before) (proof-machine-limit middle))
                (<= (boymoo-model::a64-sp (proof-world-machine middle))
                    (boymoo-model::a64-sp (proof-world-machine before)))
                (proof-number-world-byte-keys-p before)
                (proof-number-world-byte-keys-p after))
           (proof-heap-frame-p before after))
  :hints (("Goal"
           :use ((:instance heap-static-header-end-fits (world before))
                 (:instance proof-number-load-agrees-inside-saved-span
                            (address (proof-heap-base before)) (start (proof-heap-base before))
                            (end (+ 24 (proof-heap-base before))) (after middle))
                 (:instance proof-number-span-agreement-narrows
                            (start (boymoo-model::a64-sp (proof-world-machine middle)))
                            (end (+ (- (proof-machine-limit middle) *proof-machine-margin*)
                                    *proof-machine-reservation*))
                            (low (boymoo-model::a64-sp (proof-world-machine before)))
                            (high (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                     *proof-machine-reservation*))
                            (before middle))
                 (:instance proof-number-span-agreement-composes
                            (start (proof-heap-base before)) (end (+ 24 (proof-heap-base before))))
                 (:instance proof-number-span-agreement-composes
                            (start (+ 32 (proof-heap-base before)))
                            (end (+ (proof-heap-base before)
                                    (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance proof-number-span-agreement-composes
                            (start (boymoo-model::a64-sp (proof-world-machine before)))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*))))
           :in-theory (e/d (proof-heap-frame-p)
                           (proof-machine-limit proof-heap-layout-p proof-runtime-word))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-preserved-heaps-compose
  (implies (and (proof-heap-p before old-objects packages)
                (proof-preserved-heap-p nil before middle old-objects middle-objects packages)
                (proof-preserved-heap-p nil middle after middle-objects objects packages)
                (equal (proof-machine-limit before) (proof-machine-limit middle))
                (<= (boymoo-model::a64-sp (proof-world-machine middle))
                    (boymoo-model::a64-sp (proof-world-machine before)))
                (proof-number-world-byte-keys-p before)
                (proof-number-world-byte-keys-p after))
           (proof-preserved-heap-p nil before after old-objects objects packages))
  :hints (("Goal"
           :use (proof-number-heap-frames-compose
                 (:instance proof-number-shorter-prefix-is-retained
                            (short (proof-stack-top before)) (top (proof-stack-top middle))
                            (before middle) (old-objects middle-objects) (new-objects objects)))
           :in-theory (e/d (proof-heap-frame-p proof-prefix-preserved-p proof-stack-prefix proof-heap-p)
                           (proof-machine-limit proof-heap-layout-p proof-runtime-word
                            proof-external-objects proof-object-map-p proof-stack-views
                            proof-heap-object-spans-p proof-static-p proof-dynamic-view
                            proof-dynamic-entries proof-dynamic-symbol-objects-p proof-string-accounting-p))
           :do-not-induct t))
  :rule-classes nil)
