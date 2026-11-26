(in-package "BOYMOO-PROOFS")

(include-book "growth")
(include-book "allocators")
(include-book "heap-frames")
(include-book "alignment")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-growth-layout-facts
  (implies (proof-heap-layout-p before)
           (and (<= 128 (proof-heap-base before))
                (<= (proof-stack-base before) (proof-stack-limit before))
                (<= (proof-stack-limit before) (proof-stack-end before))
                (<= (- (proof-stack-limit before) (proof-stack-base before))
                    *proof-value-reservation*)
                (equal (mod (proof-stack-base before) 8) 0)
                (equal (mod (proof-stack-limit before) 8) 0)
                (equal (proof-stack-end before)
                       (+ (proof-stack-base before) *proof-value-reservation*))
                (<= (proof-active-floor before) (proof-box-top before))
                (<= (proof-box-top before) (proof-heap-limit before))
                (<= (proof-heap-limit before) (proof-cons-floor before))
                (<= (proof-cons-floor before) (proof-active-end before))
                (equal (mod (proof-box-top before) 8) 0)
                (equal (mod (proof-heap-limit before) 8) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-stack-base proof-stack-end proof-stack-top
                                     proof-heap-base proof-align-up proof-covered-p
                                     proof-disjoint-p proof-regions-p mod))))

(defthm allocation-growth-aligned-limit
  (implies (and (integerp required) (integerp (proof-stack-base before))
                (<= required (proof-stack-end before))
                (<= (proof-stack-limit before) (proof-stack-end before))
                (equal (mod required 8) 0)
                (equal (mod (proof-stack-base before) 8) 0)
                (equal (mod (proof-stack-limit before) 8) 0)
                (equal (proof-stack-end before)
                       (+ (proof-stack-base before) *proof-value-reservation*)))
           (equal (mod (proof-grow-limit required before) 8) 0))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-doubled-stack-size-alignment
                  (base (proof-stack-base before)) (old-limit (proof-stack-limit before)))
                 (:instance allocation-stack-reservation-alignment (base (proof-stack-base before))))
           :in-theory (disable proof-stack-base proof-stack-end mod))))

(defthm allocation-growth-context-and-frontiers
  (implies (and (member-equal entry '("rt:grow" "rt:ensure-stack"))
                (proof-frame-return-p (allocation-growth-clobbers entry) t before after)
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (proof-streams-preserved-p before after))
           (and (allocation-same-heap-context-p before after)
                (equal (proof-box-top after) (proof-box-top before))
                (equal (proof-heap-limit after) (proof-heap-limit before))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal entry "rt:grow"))
           :use ((:instance allocation-context-from-register-frame
                            (clobbers (allocation-growth-clobbers entry)))
                 (:instance allocation-register-frame-member
                            (clobbers (allocation-growth-clobbers entry)) (register 26) (upper 30))
                 (:instance allocation-register-frame-member
                            (clobbers (allocation-growth-clobbers entry)) (register 27) (upper 30))))))

(local
 (defthm allocation-growth-stack-base-natural
   (natp (proof-stack-base world))
   :rule-classes :type-prescription))

(defthm allocation-growth-new-limit-facts
  (let ((limit (proof-grow-limit required before)))
    (implies (and (proof-heap-layout-p before)
                  (integerp required) (equal (mod required 8) 0)
                  (<= required (proof-stack-end before)))
             (and (<= (proof-stack-limit before) limit)
                  (<= limit (proof-stack-end before))
                  (equal (mod limit 8) 0))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-growth-layout-facts allocation-growth-aligned-limit
                 (:instance allocation-growth-limit-in-reservation (world before)))
           :in-theory (disable proof-grow-limit proof-heap-layout-p proof-stack-base
                               proof-stack-limit proof-stack-end mod
                               allocation-growth-limit-in-reservation))))

(defthm allocation-growth-new-layout
  (implies (and (allocation-same-heap-context-p before after)
                (proof-heap-layout-p before)
                (integerp required) (equal (mod required 8) 0)
                (<= required (proof-stack-end before))
                (equal (proof-stack-limit after) (proof-grow-limit required before))
                (equal (proof-box-top after) (proof-box-top before))
                (equal (proof-heap-limit after) (proof-heap-limit before)))
           (proof-heap-layout-p after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-growth-new-limit-facts allocation-growth-layout-facts
                 allocation-extend-layout-tops)
           :in-theory (disable proof-heap-layout-p proof-grow-limit proof-stack-limit
                               proof-stack-end proof-box-top proof-heap-limit mod))))

(defthm allocation-growth-heap-preservation
  (implies (and (allocation-same-heap-context-p before after)
                (proof-heap-p before objects packages)
                (proof-heap-layout-p after)
                (equal (proof-box-top after) (proof-box-top before))
                (equal (proof-heap-limit after) (proof-heap-limit before)))
           (and (proof-preserved-heap-p nil before after objects objects packages)
                (proof-fixed-heap-p before after objects)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-heap-with-raised-box-top allocation-preserved-heap-under-same-context
                 allocation-fixed-heap-under-same-context)
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-box-top proof-heap-limit
                               proof-preserved-heap-p proof-fixed-heap-p))))

(defthm allocation-growth-heap-return
  (implies (and (member-equal entry '("rt:grow" "rt:ensure-stack"))
                (integerp required) (equal (mod required 8) 0)
                (<= required (proof-stack-end before))
                (proof-heap-p before objects packages)
                (proof-frame-return-p (allocation-growth-clobbers entry) t before after)
                (equal (proof-stack-limit after) (proof-grow-limit required before))
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (proof-streams-preserved-p before after))
           (proof-grow-return-p entry required before after objects objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-growth-context-and-frontiers allocation-growth-new-layout
                 allocation-growth-heap-preservation (:instance allocation-layout-of-heap (world before)))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-stack-end proof-grow-limit
                               proof-stack-limit proof-box-top proof-heap-limit proof-frame-return-p
                               proof-preserved-heap-p proof-fixed-heap-p mod))))

(defthm allocation-growth-entry-facts
  (implies (allocation-growth-machine-pre-p entry required origin before)
           (and (member-equal entry '("rt:grow" "rt:ensure-stack"))
                (integerp required)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-code-origin-p allocation-code-address
                                     proof-stack-base proof-stack-limit proof-stack-end))))

(defthm allocation-linux-layout-allows-doubling
  (implies (and (proof-heap-layout-p before)
                (<= (proof-stack-end before) (expt 2 63)))
           (allocation-growth-doubling-fits-p before))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-growth-layout-facts
                 (:instance allocation-growth-doubling-in-linux-range
                   (base (proof-stack-base before)) (old-limit (proof-stack-limit before))))
           :in-theory (disable proof-heap-layout-p proof-stack-base proof-stack-limit proof-stack-end mod))))

(defthm allocation-growth-return-contract
  (let* ((path (allocation-growth-path entry required before))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-growth-machine-pre-p entry required origin before)
                  (proof-heap-p before objects packages)
                  (equal (mod required 8) 0)
                  (<= required (proof-stack-end before))
                  (<= (proof-stack-end before) (expt 2 63))
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-grow-return-p entry required before after objects objects packages)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-growth-checked-return
                        allocation-growth-heap-return
                        allocation-linux-layout-allows-doubling allocation-growth-entry-facts
                        (:instance allocation-layout-of-heap (world before)))
           :in-theory (disable allocation-growth-path allocation-growth-machine-pre-p
                               allocation-growth-doubling-fits-p allocation-path-ready-p allocation-path-end
                               proof-heap-p proof-heap-layout-p proof-stack-base proof-stack-end proof-stack-limit
                               proof-grow-return-p proof-frame-return-p proof-grow-limit
                               proof-segment-p proof-streams-preserved-p mod))))

(defthm allocation-tail-collector-frame
  (implies (and (not (proof-world-stop before)) (not (proof-world-stop cut))
                (allocation-collector-prefix-p before cut)
                (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t cut after))
           (and (allocation-same-heap-context-p before cut)
                (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-context-from-register-frame
                  (after cut) (clobbers *proof-volatile-registers*))
                 (:instance allocation-register-frame-member
                  (register 30) (upper 30) (clobbers *proof-volatile-registers*) (after cut))
                 (:instance allocation-register-frame-under-more-clobbers
                  (small *proof-volatile-registers*) (large (append *proof-volatile-registers* '(26 27)))
                  (register 30) (after cut))
                 (:instance allocation-register-frame-transitive
                  (middle cut) (register 30) (clobbers (append *proof-volatile-registers* '(26 27))))))))

(defthm allocation-tail-collector-reservation
  (implies (and (not (proof-world-stop before)) (not (proof-world-stop cut))
                (allocation-collector-prefix-p before cut)
                (proof-collector-return-p kind bytes cut after old-objects new-objects packages))
           (proof-allocator-return-p kind bytes before after old-objects new-objects packages))
  :rule-classes nil
  :hints (("Goal" :use allocation-tail-collector-frame
           :in-theory (disable proof-preserved-heap-p proof-reserved-span-p
                               proof-frame-return-p proof-active-floor proof-inactive-floor))))

(defthm allocation-slow-checked-return
  (let* ((path (allocation-slow-path kind))
         (entry-cuts (list (allocation-code-address "rt:collect" origin)))
         (return-cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-request-machine-pre-p kind bytes origin before)
                  (not (proof-allocation-fits-p kind bytes before))
                  (not (allocation-word-overflow-p kind bytes before))
                  (allocation-path-ready-p path entry-cuts before)
                  (allocation-path-ready-p path return-cuts before)
                  (equal cut (allocation-path-end path before))
                  (natp collector-steps)
                  (proof-segment-p collector-steps return-cuts cut :cut after)
                  (proof-collector-return-p kind bytes cut after old-objects new-objects packages))
             (and (proof-allocator-return-p kind bytes before after old-objects new-objects packages)
                  (proof-segment-p (+ (len path) collector-steps) return-cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-slow-to-collector allocation-tail-collector-reservation
                        (:instance allocation-prefix-from-path (path (allocation-slow-path kind))
                         (cuts (list (proof-world-reg 30 before))))
                        (:instance allocation-segment-after-prefix
                         (count (len (allocation-slow-path kind))) (remaining collector-steps)
                         (middle cut) (reason :cut) (cuts (list (proof-world-reg 30 before)))))
           :in-theory (disable allocation-slow-path allocation-path-ready-p allocation-path-end
                               allocation-collector-prefix-p allocation-prefix-p proof-segment-p
                               proof-collector-return-p proof-allocator-return-p proof-allocation-fits-p))))
