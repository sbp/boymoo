(in-package "BOYMOO-PROOFS")

(include-book "machine-arithmetic")
(include-book "ranges")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

; The lower limbs are still pending when this prefix has been processed.
(defun division-one-limb-prefix-ready-p (digits pending world)
  (if (atom digits)
      (null digits)
    (let* ((before (proof-advance (* 7 (len (cdr digits))) world))
           (offset (* 8 pending))
           (address (+ (proof-world-reg 0 before) offset)))
      (and (division-one-limb-prefix-ready-p (cdr digits) (1+ pending) world)
           (division-one-limb-iteration-ready-p before)
           (equal (proof-world-reg 4 before) (+ 8 offset))
           (equal (proof-load-word address (proof-world-machine before)) (car digits))))))

(defun division-write-quotient-limbs (digits pending base memory)
  (if (atom digits)
      memory
    (boymoo-model::a64-write-bytes
     8 (+ base (* 8 pending)) (car digits)
     (division-write-quotient-limbs (cdr digits) (1+ pending) base memory))))

(local
 (defthm division-advance-zero-steps
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :expand ((proof-advance 0 world))))))

(defthm division-one-limb-prefix-correct
  (implies (and (division-digits-p digits) (natp pending)
                (equal (proof-world-reg 4 world) (* 8 (+ pending (len digits))))
                (equal (proof-world-reg 5 world) 0)
                (division-one-limb-prefix-ready-p digits pending world))
           (let* ((after (proof-advance (* 7 (len digits)) world))
                  (divisor (proof-world-reg 3 world)))
             (mv-let (quotient remainder)
               (division-one-limb-loop digits divisor)
               (and (equal (proof-world-reg 4 after) (* 8 pending))
                    (equal (proof-world-reg 5 after) remainder)
                    (equal (proof-world-reg 3 after) divisor)
                    (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                    (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
                    (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                    (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                    (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                    (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                    (equal (proof-world-regions after) (proof-world-regions world))
                    (equal (boymoo-model::a64-sp (proof-world-machine after))
                           (boymoo-model::a64-sp (proof-world-machine world)))
                    (equal (proof-world-pc after)
                           (if (and (equal pending 0) (consp digits))
                               (+ (proof-world-pc world) 28)
                             (proof-world-pc world)))
                    (equal (boymoo-model::a64-memory (proof-world-machine after))
                           (division-write-quotient-limbs
                            quotient pending (proof-world-reg 21 world)
                            (boymoo-model::a64-memory (proof-world-machine world))))
                    (equal (proof-world-stop after) (proof-world-stop world))))))
  :hints (("Goal"
           :induct (division-one-limb-prefix-ready-p digits pending world)
           :in-theory (disable proof-step proof-world-pc proof-world-stop proof-world-reg proof-load-word
                               division-one-limb-iteration-ready-p division-one-limb-step
                               boymoo-model::a64-memory boymoo-model::a64-write-bytes boymoo-model::a64-sp
                               (:definition proof-advance)))
          ("Subgoal *1/2"
           :use ((:instance division-one-limb-iteration-advances
                            (world (proof-advance (* 7 (len (cdr digits))) world)))
                 (:instance proof-advance-append (prefix (* 7 (len (cdr digits)))) (suffix 7)))))
  :rule-classes nil)

(defthm division-read-after-disjoint-quotient-writes
  (implies (and (natp pending) (natp base)
                (proof-span-p (+ base (* 8 pending)) (* 8 (len digits)))
                (proof-span-p query size)
                (proof-disjoint-p (+ base (* 8 pending)) (+ base (* 8 (+ pending (len digits))))
                                  query (+ query size)))
           (equal (boymoo-model::a64-read-bytes
                   size query (division-write-quotient-limbs digits pending base memory))
                  (boymoo-model::a64-read-bytes size query memory)))
  :hints (("Goal" :induct (division-write-quotient-limbs digits pending base memory)
                  :in-theory (disable boymoo-model::a64-write-bytes boymoo-model::a64-read-bytes))
          ("Subgoal *1/2" :cases ((consp (cdr digits))))))

(defthm division-load-word-after-quotient-writes
  (implies (and (natp pending) (natp base)
                (proof-span-p (+ base (* 8 pending)) (* 8 (len digits)))
                (proof-span-p query 8)
                (proof-disjoint-p (+ base (* 8 pending)) (+ base (* 8 (+ pending (len digits))))
                                  query (+ query 8))
                (equal (boymoo-model::a64-memory after)
                       (division-write-quotient-limbs
                        digits pending base (boymoo-model::a64-memory before))))
           (equal (proof-load-word query after) (proof-load-word query before)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-memory
                                      division-write-quotient-limbs)))
  :rule-classes nil)

(local
 (defthm division-instruction-after-quotient-writes
   (implies (and (natp pending) (natp base)
                 (proof-span-p (+ base (* 8 pending)) (* 8 (len digits)))
                 (proof-disjoint-p (+ base (* 8 pending)) (+ base (* 8 (+ pending (len digits))))
                                   pc (+ pc 4))
                 (equal (proof-world-regions after) (proof-world-regions before))
                 (equal (boymoo-model::a64-memory (proof-world-machine after))
                        (division-write-quotient-limbs
                         digits pending base (boymoo-model::a64-memory (proof-world-machine before)))))
            (equal (proof-instruction-at-p instruction pc after)
                   (proof-instruction-at-p instruction pc before)))
   :hints (("Goal"
            :use (:instance division-covered-span
                            (address pc) (size 4) (access :execute) (regions (proof-world-regions before)))
            :in-theory (e/d (division-instruction-at-depends-on-bytes)
                            (mod proof-instruction-at-p proof-covered-p proof-decode
                             boymoo-model::a64-read-bytes boymoo-model::a64-memory
                             division-write-quotient-limbs proof-world-machine proof-world-regions))))
   :rule-classes nil))

(defthm division-code-after-quotient-writes
  (implies (and (natp pending) (natp base)
                (proof-span-p (+ base (* 8 pending)) (* 8 (len digits)))
                (proof-disjoint-p (+ base (* 8 pending)) (+ base (* 8 (+ pending (len digits))))
                                  pc (+ pc (* 4 (len instructions))))
                (equal (proof-world-regions after) (proof-world-regions before))
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (division-write-quotient-limbs
                        digits pending base (boymoo-model::a64-memory (proof-world-machine before)))))
           (equal (proof-instructions-at-p instructions pc after)
                  (proof-instructions-at-p instructions pc before)))
  :hints (("Goal" :induct (proof-instructions-at-p instructions pc before)
                  :in-theory (disable proof-instruction-at-p proof-covered-p proof-decode
                                      boymoo-model::a64-read-bytes boymoo-model::a64-memory
                                      division-write-quotient-limbs proof-world-machine proof-world-regions))
          ("Subgoal *1/2"
           :use (:instance division-instruction-after-quotient-writes (instruction (car instructions)))
           :expand ((proof-instructions-at-p instructions pc after)))
          ("Subgoal *1/3"
           :use (:instance division-instruction-after-quotient-writes (instruction (car instructions)))
           :expand ((proof-instructions-at-p instructions pc after))))
  :rule-classes nil)

(local
 (in-theory (disable proof-step proof-world-pc proof-world-reg proof-world-stop
                     proof-world-regions proof-world-machine proof-instructions-at-p
                     proof-load-word proof-covered-p boymoo-model::a64-memory boymoo-model::a64-sp
                     boymoo-model::a64-write-bytes division-one-limb-loop
                     division-one-limb-step (:definition proof-advance))))

(local
 (defthm division-prefix-unsigned-natural
   (natp (boymoo-model::a64-unsigned 64 value))
   :hints (("Goal" :use (:instance division-a64-unsigned-bounded (width 64) (x value))
                   :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-bounded)))
   :rule-classes :type-prescription))

(local
 (defthm division-prefix-register-natural
   (natp (proof-world-reg register world))
   :hints (("Goal" :in-theory (e/d (proof-world-reg) (boymoo-model::a64-unsigned))))
   :rule-classes :type-prescription))

(local
 (defthm division-prefix-length-positive
   (implies (consp digits) (< 0 (len digits)))
   :hints (("Goal" :expand ((len digits))))
   :rule-classes :linear))

(defun division-one-limb-prefix-layout-p (digits pending world)
  (let* ((count (len digits))
         (bytes (* 8 count))
         (source (+ (proof-world-reg 0 world) (* 8 pending)))
         (target (+ (proof-world-reg 21 world) (* 8 pending)))
         (pc (proof-world-pc world))
         (regions (proof-world-regions world)))
    (and (natp pending)
         (division-digits-p digits)
         (division-digit-p (proof-world-reg 3 world))
         (posp (proof-world-reg 3 world))
         (equal (proof-world-reg 4 world) (* 8 (+ pending count)))
         (equal (proof-world-reg 5 world) 0)
         (not (proof-world-stop world))
         (unsigned-byte-p 64 (+ pc 28))
         (proof-instructions-at-p *division-one-limb-instructions* pc world)
         (equal (division-read-limbs count source (proof-world-machine world)) digits)
         (or (atom digits)
             (and (proof-span-p source bytes)
                  (proof-span-p target bytes)
                  (proof-covered-p source bytes :read regions)
                  (proof-covered-p target bytes :write regions)
                  (proof-disjoint-p target (+ target bytes) source (+ source bytes))
                  (proof-disjoint-p target (+ target bytes) pc (+ pc 28)))))))

(local
 (defthm division-prefix-read-limbs-unfold
   (implies (posp count)
            (equal (division-read-limbs count address machine)
                   (cons (proof-load-word address machine)
                         (division-read-limbs (1- count) (+ address 8) machine))))
   :hints (("Goal" :expand ((division-read-limbs count address machine))))
   :rule-classes nil))

(local
 (defthm division-prefix-layout-of-upper-limbs
   (implies (and (consp digits)
                 (division-one-limb-prefix-layout-p digits pending world))
            (division-one-limb-prefix-layout-p (cdr digits) (1+ pending) world))
   :hints (("Goal"
            :cases ((consp (cdr digits)))
            :use ((:instance division-covered-slice
                             (base (+ (proof-world-reg 0 world) (* 8 pending)))
                             (bytes (* 8 (len digits))) (offset 8)
                             (size (* 8 (len (cdr digits)))) (access :read)
                             (regions (proof-world-regions world)))
                  (:instance division-covered-slice
                             (base (+ (proof-world-reg 21 world) (* 8 pending)))
                             (bytes (* 8 (len digits))) (offset 8)
                             (size (* 8 (len (cdr digits)))) (access :write)
                             (regions (proof-world-regions world)))
                  (:instance division-prefix-read-limbs-unfold
                             (count (len digits)) (address (+ (proof-world-reg 0 world) (* 8 pending)))
                             (machine (proof-world-machine world))))
            :in-theory (disable division-read-limbs)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-current-limb-ready
   (let* ((pc (proof-world-pc world))
          (source (+ (proof-world-reg 0 world) (* 8 pending)))
          (target (+ (proof-world-reg 21 world) (* 8 pending)))
          (regions (proof-world-regions world)))
     (implies (and (natp pending)
                   (equal (proof-world-reg 4 world) (+ 8 (* 8 pending)))
                   (division-digit-p (proof-world-reg 3 world))
                   (posp (proof-world-reg 3 world))
                   (< (proof-world-reg 5 world) (proof-world-reg 3 world))
                   (division-digit-p (proof-load-word source (proof-world-machine world)))
                   (not (proof-world-stop world))
                   (unsigned-byte-p 64 (+ pc 28))
                   (proof-instructions-at-p *division-one-limb-instructions* pc world)
                   (proof-span-p source 8) (proof-span-p target 8)
                   (proof-covered-p source 8 :read regions)
                   (proof-covered-p target 8 :write regions)
                   (proof-disjoint-p target (+ target 8) pc (+ pc 28)))
              (division-one-limb-iteration-ready-p world)))
   :hints (("Goal" :use (:instance division-one-limb-iteration-ready-from-spans)
                   :in-theory (disable division-one-limb-iteration-ready-p division-digit-p
                                       proof-span-p proof-disjoint-p)
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-prefix-layout-at-lowest-limb
   (let* ((pc (proof-world-pc world))
          (bytes (* 8 (len digits)))
          (source (+ (proof-world-reg 0 world) (* 8 pending)))
          (target (+ (proof-world-reg 21 world) (* 8 pending)))
          (regions (proof-world-regions world)))
     (implies (and (consp digits) (division-one-limb-prefix-layout-p digits pending world))
              (and (equal (proof-load-word source (proof-world-machine world)) (car digits))
                   (proof-covered-p source 8 :read regions)
                   (proof-covered-p target 8 :write regions)
                   (proof-disjoint-p target (+ target 8) pc (+ pc 28))
                   (proof-span-p source 8) (proof-span-p target 8)
                   (or (atom (cdr digits))
                       (and (proof-span-p (+ target 8) (- bytes 8))
                            (proof-disjoint-p (+ target 8) (+ target bytes) source (+ source 8))
                            (proof-disjoint-p (+ target 8) (+ target bytes) pc (+ pc 28)))))))
   :hints (("Goal"
            :cases ((consp (cdr digits)))
            :use ((:instance division-covered-slice
                             (base (+ (proof-world-reg 0 world) (* 8 pending)))
                             (bytes (* 8 (len digits))) (offset 0) (size 8)
                             (access :read) (regions (proof-world-regions world)))
                  (:instance division-covered-slice
                             (base (+ (proof-world-reg 21 world) (* 8 pending)))
                             (bytes (* 8 (len digits))) (offset 0) (size 8)
                             (access :write) (regions (proof-world-regions world)))
                  (:instance division-prefix-read-limbs-unfold
                             (count (len digits)) (address (+ (proof-world-reg 0 world) (* 8 pending)))
                             (machine (proof-world-machine world))))
            :in-theory (disable division-read-limbs)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-prefix-empty-advance
   (implies (atom digits)
            (equal (proof-advance (* 7 (len digits)) world) world))))

(local
 (defthm division-prefix-layout-after-upper-frame
   (let* ((before (proof-advance (* 7 (len (cdr digits))) world))
          (pc (proof-world-pc world))
          (regions (proof-world-regions world))
          (divisor (proof-world-reg 3 world))
          (quotient (mv-nth 0 (division-one-limb-loop (cdr digits) divisor))))
     (implies (and (consp (cdr digits))
                   (division-one-limb-prefix-layout-p digits pending world)
                   (division-one-limb-prefix-ready-p (cdr digits) (1+ pending) world))
              (and (equal (proof-world-pc before) pc)
                   (equal (proof-world-reg 0 before) (proof-world-reg 0 world))
                   (equal (proof-world-reg 21 before) (proof-world-reg 21 world))
                   (equal (proof-world-reg 3 before) divisor)
                   (equal (proof-world-reg 4 before) (+ 8 (* 8 pending)))
                   (< (proof-world-reg 5 before) divisor)
                   (not (proof-world-stop before))
                   (equal (proof-world-regions before) regions)
                   (equal (len quotient) (len (cdr digits)))
                   (equal (boymoo-model::a64-memory (proof-world-machine before))
                          (division-write-quotient-limbs
                           quotient (1+ pending) (proof-world-reg 21 world)
                           (boymoo-model::a64-memory (proof-world-machine world)))))))
   :hints (("Goal"
            :use ((:instance division-one-limb-prefix-correct
                             (digits (cdr digits)) (pending (1+ pending)))
                  (:instance division-one-limb-loop-correct
                             (digits (cdr digits)) (divisor (proof-world-reg 3 world))))
            :in-theory (disable division-read-limbs division-one-limb-prefix-ready-p
                                division-write-quotient-limbs)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-prefix-layout-after-upper-limbs
   (let* ((before (proof-advance (* 7 (len (cdr digits))) world))
          (source (+ (proof-world-reg 0 before) (* 8 pending))))
     (implies (and (consp digits)
                   (division-one-limb-prefix-layout-p digits pending world)
                   (division-one-limb-prefix-ready-p (cdr digits) (1+ pending) world))
              (and (division-one-limb-iteration-ready-p before)
                   (equal (proof-world-reg 4 before) (+ 8 (* 8 pending)))
                   (equal (proof-load-word source (proof-world-machine before)) (car digits)))))
   :hints (("Goal" :cases ((consp (cdr digits)))
            :in-theory (disable division-read-limbs division-one-limb-iteration-ready-p
                                division-one-limb-prefix-ready-p division-digit-p
                                proof-span-p proof-disjoint-p division-write-quotient-limbs)
            :do-not '(generalize fertilize eliminate-destructors)
            :do-not-induct t)
           ("Subgoal 2"
            :use ((:instance division-prefix-layout-at-lowest-limb)
                  (:instance division-current-limb-ready)))
           ("Subgoal 1"
            :use ((:instance division-prefix-layout-at-lowest-limb)
                  (:instance division-prefix-layout-after-upper-frame)
                  (:instance division-code-after-quotient-writes
                             (before world) (after (proof-advance (* 7 (len (cdr digits))) world))
                             (pc (proof-world-pc world)) (instructions *division-one-limb-instructions*)
                             (digits (mv-nth 0 (division-one-limb-loop (cdr digits) (proof-world-reg 3 world))))
                             (base (proof-world-reg 21 world)) (pending (1+ pending)))
                  (:instance division-load-word-after-quotient-writes
                             (before (proof-world-machine world))
                             (after (proof-world-machine (proof-advance (* 7 (len (cdr digits))) world)))
                             (query (+ (proof-world-reg 0 world) (* 8 pending)))
                             (base (proof-world-reg 21 world)) (pending (1+ pending))
                             (digits (mv-nth 0 (division-one-limb-loop (cdr digits) (proof-world-reg 3 world)))))
                  (:instance division-current-limb-ready
                             (world (proof-advance (* 7 (len (cdr digits))) world))))))
   :rule-classes nil))

(defthm division-one-limb-prefix-ready-from-layout
  (implies (division-one-limb-prefix-layout-p digits pending world)
           (division-one-limb-prefix-ready-p digits pending world))
  :hints (("Goal" :induct (division-one-limb-prefix-ready-p digits pending world)
                  :in-theory (disable division-one-limb-prefix-layout-p
                                      division-one-limb-iteration-ready-p))
          ("Subgoal *1/2"
           :use ((:instance division-prefix-layout-of-upper-limbs)
                 (:instance division-prefix-layout-after-upper-limbs)))
          ("Subgoal *1/1" :in-theory (enable division-one-limb-prefix-layout-p)))
  :rule-classes nil)

(defthm division-one-limb-checked-loop-result
  (implies (and (consp digits) (division-digits-p digits)
                (division-digit-p (proof-world-reg 3 world))
                (posp (proof-world-reg 3 world))
                (equal (proof-world-reg 4 world) (* 8 (len digits)))
                (equal (proof-world-reg 5 world) 0)
                (division-one-limb-prefix-ready-p digits 0 world))
           (let* ((after (proof-advance (* 7 (len digits)) world))
                  (divisor (proof-world-reg 3 world))
                  (quotient (mv-nth 0 (division-one-limb-loop digits divisor)))
                  (remainder (proof-world-reg 5 after)))
             (and (equal (proof-world-pc after) (+ 28 (proof-world-pc world)))
                  (natp remainder) (< remainder divisor)
                  (equal (+ (* divisor (division-magnitude quotient)) remainder)
                         (division-magnitude digits))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (division-write-quotient-limbs
                          quotient 0 (proof-world-reg 21 world)
                          (boymoo-model::a64-memory (proof-world-machine world)))))))
  :hints (("Goal"
           :use ((:instance division-one-limb-prefix-correct (pending 0))
                 (:instance division-one-limb-loop-correct (divisor (proof-world-reg 3 world))))
           :in-theory (disable proof-step proof-advance proof-world-pc proof-world-reg
                               division-one-limb-prefix-ready-p division-one-limb-loop
                               division-write-quotient-limbs boymoo-model::a64-memory)))
  :rule-classes nil)

(defthm division-read-limbs-from-same-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory second))
           (equal (division-read-limbs count address first)
                  (division-read-limbs count address second)))
  :hints (("Goal" :induct (division-read-limbs count address first)
                  :in-theory (e/d (proof-load-word)
                                  (boymoo-model::a64-read-bytes)))
          ("Subgoal *1/2" :expand ((division-read-limbs count address second))))
  :rule-classes nil)

(defthm division-read-limbs-after-disjoint-store
  (implies (and (natp count)
                (proof-span-p address (* 8 count))
                (proof-span-p target bytes)
                (proof-disjoint-p address (+ address (* 8 count)) target (+ target bytes)))
           (equal (division-read-limbs count address (boymoo-model::a64-store bytes target value machine))
                  (division-read-limbs count address machine)))
  :hints (("Goal" :induct (division-read-limbs count address machine)
                  :in-theory (e/d (proof-load-word)
                                  (boymoo-model::a64-load boymoo-model::a64-store
                                   proof-memory-span-agrees-p)))
          ("Subgoal *1/2"
           :use (:instance division-load-after-disjoint-store
                           (count bytes) (address target) (query address) (size 8))
           :expand ((division-read-limbs count address
                       (boymoo-model::a64-store bytes target value machine)))
           :cases ((equal count 1)))))

(local
 (defthm division-replace-memory-twice
   (equal (update-nth index value (update-nth index previous machine))
          (update-nth index value machine))
   :hints (("Goal" :induct (update-nth index previous machine)))))

(local
 (defthm division-quotient-memory-head-is-a-store
   (implies (consp digits)
            (equal (update-nth 4 (division-write-quotient-limbs
                                  digits pending base (boymoo-model::a64-memory machine))
                               machine)
                   (boymoo-model::a64-store
                    8 (+ base (* 8 pending)) (car digits)
                    (update-nth 4 (division-write-quotient-limbs
                                   (cdr digits) (1+ pending) base (boymoo-model::a64-memory machine))
                                machine))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-memory)))))

(local
 (defthm division-zero-limb-read
   (equal (division-read-limbs 0 address machine) nil)
   :hints (("Goal" :expand ((division-read-limbs 0 address machine))))))

(defun division-word-list-p (words)
  (if (atom words)
      (null words)
    (and (unsigned-byte-p 64 (car words)) (division-word-list-p (cdr words)))))

(defthm division-limbs-fit-in-word-list
  (implies (division-digits-p digits) (division-word-list-p digits))
  :hints (("Goal" :induct (division-digits-p digits))))

(local
 (defthm division-read-quotient-from-updated-memory
   (implies (and (natp pending) (natp base)
                 (division-word-list-p digits)
                 (proof-span-p (+ base (* 8 pending)) (* 8 (len digits))))
            (equal (division-read-limbs
                    (len digits) (+ base (* 8 pending))
                    (update-nth 4 (division-write-quotient-limbs
                                   digits pending base (boymoo-model::a64-memory machine))
                                machine))
                   digits))
   :hints (("Goal"
            :induct (division-write-quotient-limbs digits pending base memory)
            :in-theory (e/d (proof-load-word)
                            (boymoo-model::a64-load boymoo-model::a64-store
                             (:definition division-write-quotient-limbs) division-read-limbs)))
           ("Subgoal *1/2"
            :use ((:instance division-prefix-read-limbs-unfold
                             (count (len digits)) (address (+ base (* 8 pending)))
                             (machine (update-nth 4 (division-write-quotient-limbs
                                                     digits pending base (boymoo-model::a64-memory machine))
                                                  machine)))
                  (:instance division-load-after-fitting-store
                             (count 8) (address (+ base (* 8 pending))) (value (car digits))
                             (machine (update-nth 4 (division-write-quotient-limbs
                                                     (cdr digits) (1+ pending) base
                                                     (boymoo-model::a64-memory machine))
                                                  machine))))
            :cases ((consp (cdr digits)))))
   :rule-classes nil))

(defthm division-read-back-word-writes
  (implies (and (natp pending) (natp base)
                (division-word-list-p digits)
                (proof-span-p (+ base (* 8 pending)) (* 8 (len digits)))
                (equal (boymoo-model::a64-memory after)
                       (division-write-quotient-limbs
                        digits pending base (boymoo-model::a64-memory before))))
           (equal (division-read-limbs (len digits) (+ base (* 8 pending)) after) digits))
  :hints (("Goal"
           :use ((:instance division-read-quotient-from-updated-memory (machine before))
                 (:instance division-read-limbs-from-same-memory
                            (first after) (count (len digits)) (address (+ base (* 8 pending)))
                            (second (update-nth 4 (division-write-quotient-limbs
                                                   digits pending base (boymoo-model::a64-memory before))
                                                before))))
           :in-theory (e/d (boymoo-model::a64-memory)
                           (division-read-limbs division-write-quotient-limbs))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-read-quotient-limb-writes
  (implies (and (natp pending) (natp base)
                (division-digits-p digits)
                (proof-span-p (+ base (* 8 pending)) (* 8 (len digits)))
                (equal (boymoo-model::a64-memory after)
                       (division-write-quotient-limbs
                        digits pending base (boymoo-model::a64-memory before))))
           (equal (division-read-limbs (len digits) (+ base (* 8 pending)) after) digits))
  :hints (("Goal"
           :use (:instance division-read-back-word-writes)
           :in-theory (disable division-write-quotient-limbs division-read-limbs
                               division-digits-p division-word-list-p)))
  :rule-classes nil)

(local
 (defthm division-one-limb-loop-readback
   (implies (and (consp digits) (division-one-limb-prefix-layout-p digits 0 world))
            (let* ((after (proof-advance (* 7 (len digits)) world))
                   (divisor (proof-world-reg 3 world))
                   (quotient (mv-nth 0 (division-one-limb-loop digits divisor))))
              (and (equal (division-read-limbs
                           (len digits) (proof-world-reg 21 world) (proof-world-machine after))
                          quotient)
                   (equal (proof-world-reg 5 after)
                          (mv-nth 1 (division-one-limb-loop digits divisor)))
                   (equal (proof-world-pc after) (+ 28 (proof-world-pc world)))
                   (equal (proof-world-reg 4 after) 0)
                   (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                   (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                   (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                   (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (division-write-quotient-limbs
                           quotient 0 (proof-world-reg 21 world)
                           (boymoo-model::a64-memory (proof-world-machine world))))
                   (not (proof-world-stop after)))))
   :hints (("Goal"
            :use ((:instance division-one-limb-prefix-ready-from-layout (pending 0))
                  (:instance division-one-limb-prefix-correct (pending 0))
                  (:instance division-one-limb-loop-correct (divisor (proof-world-reg 3 world)))
                  (:instance division-read-quotient-limb-writes
                             (pending 0) (base (proof-world-reg 21 world))
                             (digits (mv-nth 0 (division-one-limb-loop digits (proof-world-reg 3 world))))
                             (before (proof-world-machine world))
                             (after (proof-world-machine (proof-advance (* 7 (len digits)) world)))))
            :in-theory (disable division-one-limb-prefix-ready-p division-write-quotient-limbs
                                division-read-limbs)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-one-limb-loop-from-layout
  (implies (and (consp digits) (division-one-limb-prefix-layout-p digits 0 world))
           (let* ((after (proof-advance (* 7 (len digits)) world))
                  (input (division-magnitude digits))
                  (divisor (proof-world-reg 3 world))
                  (quotient (division-read-limbs
                             (len digits) (proof-world-reg 21 world) (proof-world-machine after))))
             (and (equal (division-magnitude quotient) (floor input divisor))
                  (division-digits-p quotient)
                  (equal (proof-world-reg 5 after) (mod input divisor))
                  (equal (proof-world-pc after) (+ 28 (proof-world-pc world)))
                  (equal (proof-world-reg 4 after) 0)
                  (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (division-write-quotient-limbs
                          quotient 0 (proof-world-reg 21 world)
                          (boymoo-model::a64-memory (proof-world-machine world))))
                  (not (proof-world-stop after)))))
  :hints (("Goal"
           :use ((:instance division-one-limb-loop-readback)
                 (:instance division-one-limb-loop-correct (divisor (proof-world-reg 3 world)))
                 (:instance division-quotient-unique
                            (a (division-magnitude digits)) (b (proof-world-reg 3 world))
                            (q (division-magnitude
                                (mv-nth 0 (division-one-limb-loop digits (proof-world-reg 3 world)))))
                            (r (mv-nth 1 (division-one-limb-loop digits (proof-world-reg 3 world)))))
                 (:instance division-remainder-unique
                            (a (division-magnitude digits)) (b (proof-world-reg 3 world))
                            (q (division-magnitude
                                (mv-nth 0 (division-one-limb-loop digits (proof-world-reg 3 world)))))
                            (r (mv-nth 1 (division-one-limb-loop digits (proof-world-reg 3 world))))))
           :in-theory (disable floor mod division-read-limbs division-magnitude division-write-quotient-limbs)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
