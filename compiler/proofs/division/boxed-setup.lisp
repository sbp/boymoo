(in-package "BOYMOO-PROOFS")

(include-book "boxed-entry")
(include-book "divide-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-segment-p division-before-cuts-p division-instruction-sequence-ready-p
                     proof-register-frame-p proof-memory-span-agrees-p proof-integer-view-p
                     proof-preserved-heap-p proof-reg-value-p proof-reserved-span-p
                     boymoo-model::a64-sp boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defun division-boxed-view-call-return-p (value count before after objects packages)
  (and (proof-reg-value-p 0 value before objects packages)
       (proof-covered-p (proof-world-reg 1 before) 32 :write (proof-world-regions before))
       (proof-frame-return-p '(0 2 3 4 5) t before after)
       (equal (proof-world-reg 2 after) count)
       (proof-integer-view-p value (proof-world-reg 0 after) count after)))

(local
 (defthm division-boxed-retains-register
   (implies (and (proof-register-frame-p last clobbers before after)
                 (natp last) (natp register) (<= register last) (not (member-equal register clobbers)))
            (equal (proof-world-reg register after) (proof-world-reg register before)))
   :hints (("Goal"
            :induct (proof-register-frame-p last clobbers before after)
            :in-theory (enable proof-register-frame-p))
           ("Subgoal *1/1" :cases ((equal register last))))))

(defun division-boxed-call-frame-p (before after)
  (and (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 before))
       (equal (division-boxed-stack-address 0 after) (division-boxed-stack-address 0 before))
       (equal (proof-world-pc after) (proof-world-reg 30 before))
       (not (proof-world-stop after))))

(local
 (defthm division-boxed-view-return-keeps-frame
   (implies (division-boxed-view-call-return-p value count before after objects packages)
            (division-boxed-call-frame-p before after))
   :hints (("Goal"
            :use ((:instance division-boxed-retains-register (last 30) (register 6) (clobbers '(0 2 3 4 5)))
                  (:instance division-boxed-retains-register (last 30) (register 19) (clobbers '(0 2 3 4 5)))
                  (:instance division-boxed-retains-register (last 30) (register 20) (clobbers '(0 2 3 4 5)))
                  (:instance division-boxed-retains-register (last 30) (register 21) (clobbers '(0 2 3 4 5)))
                  (:instance division-boxed-retains-register (last 30) (register 22) (clobbers '(0 2 3 4 5))))
            :in-theory (disable division-boxed-retains-register proof-covered-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-boxed-reservation-return-keeps-frame
   (implies (proof-integer-reserve-return-p a b bytes before after old-objects new-objects packages)
            (and (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                 (equal (division-boxed-stack-address 0 after) (division-boxed-stack-address 0 before))
                 (equal (proof-world-pc after) (proof-world-reg 30 before))
                 (not (proof-world-stop after))))
   :hints (("Goal"
            :use (:instance division-boxed-retains-register
                            (last 30) (register 20) (clobbers (append *proof-volatile-registers* '(24 26 27))))
            :in-theory (disable division-boxed-retains-register)
            :do-not-induct t))
   :rule-classes nil))

(defun division-boxed-setup-counts (views allocation)
  (list 9 (nth 0 views) 4 (nth 1 views) 8 allocation 4 (nth 2 views) 4 (nth 3 views) 5))

(defun division-boxed-setup-steps (views allocation)
  (division-step-sum (division-boxed-setup-counts views allocation)))

(defun division-boxed-setup-state (phase views allocation world)
  (division-advance-chain (take phase (division-boxed-setup-counts views allocation)) world))

(defun division-boxed-view-setup-ready-p (phase world)
  (and (division-boxed-view-call-inputs-p phase world)
       (division-instruction-sequence-ready-p (division-boxed-view-call-code phase)
                                              (list (division-boxed-view-call-target phase world)) world)))

(defun division-boxed-setup-ready-p (a b a-count b-count views allocation world old-objects new-objects packages)
  (let* ((first (division-boxed-setup-state 1 views allocation world))
         (first-return (division-boxed-setup-state 2 views allocation world))
         (second (division-boxed-setup-state 3 views allocation world))
         (second-return (division-boxed-setup-state 4 views allocation world))
         (reserve (division-boxed-setup-state 5 views allocation world))
         (reserve-return (division-boxed-setup-state 6 views allocation world))
         (left (division-boxed-setup-state 7 views allocation world))
         (left-return (division-boxed-setup-state 8 views allocation world))
         (right (division-boxed-setup-state 9 views allocation world))
         (right-return (division-boxed-setup-state 10 views allocation world))
         (left-address (proof-world-reg 0 left-return))
         (right-address (proof-world-reg 0 right-return))
         (mode (division-boxed-stack-address 64 first))
         (slot (division-boxed-stack-address 80 right-return))
         (left-end (+ left-address (division-view-bytes a-count)))
         (right-end (+ right-address (division-view-bytes b-count))))
    (and (integerp a) (posp b) (or (equal (proof-world-reg 2 world) 0) (equal (proof-world-reg 2 world) 1))
         (division-boxed-entry-inputs-p world)
         (division-instruction-sequence-ready-p *division-boxed-first-view-instructions*
                                                (list (+ *division-boxed-entry-to-view* (proof-world-pc world))) world)
         (division-boxed-view-call-return-p a a-count first first-return old-objects packages)
         (division-boxed-view-setup-ready-p :second first-return)
         (division-boxed-view-call-return-p b b-count second second-return old-objects packages)
         (division-boxed-reservation-inputs-p a-count b-count second-return)
         (division-instruction-sequence-ready-p
          *division-boxed-reserve-instructions* (list (+ (- *division-boxed-entry-to-reserve* 52)
                                                          (proof-world-pc second-return))) second-return)
         (proof-reg-value-p 0 a reserve old-objects packages)
         (proof-reg-value-p 1 b reserve old-objects packages)
         (proof-integer-reserve-return-p a b (division-reservation-bytes a-count b-count)
                                         reserve reserve-return old-objects new-objects packages)
         (division-boxed-view-setup-ready-p :refresh-left reserve-return)
         (division-boxed-view-call-return-p a a-count left left-return new-objects packages)
         (division-boxed-view-setup-ready-p :refresh-right left-return)
         (division-boxed-view-call-return-p b b-count right right-return new-objects packages)
         (proof-span-p left-address (division-view-bytes a-count))
         (proof-span-p right-address (division-view-bytes b-count))
         (proof-span-p mode 8)
         (proof-memory-span-agrees-p left-address left-end left-return right-return)
         (proof-memory-span-agrees-p mode (+ mode 8) first right-return)
         (proof-disjoint-p left-address left-end slot (+ slot 8))
         (proof-disjoint-p right-address right-end slot (+ slot 8))
         (division-boxed-choose-path-inputs-p right-return)
         (division-instruction-sequence-ready-p *division-boxed-choose-path-instructions*
                                                (list (division-boxed-choose-path-target right-return)) right-return))))

(local
 (defthm division-boxed-setup-state-is-execution
   (equal (division-boxed-setup-state 11 views allocation world)
          (proof-advance (division-boxed-setup-steps views allocation) world))
   :hints (("Goal"
            :use (:instance division-advance-chain-sum (counts (division-boxed-setup-counts views allocation)))
            :in-theory (disable division-advance-chain division-step-sum)))
   :rule-classes nil))

(local
 (defthm division-boxed-setup-checked-blocks-advance
   (and (equal (division-boxed-setup-state 1 views allocation world) (proof-advance 9 world))
        (equal (division-boxed-setup-state 3 views allocation world)
               (proof-advance 4 (division-boxed-setup-state 2 views allocation world)))
        (equal (division-boxed-setup-state 5 views allocation world)
               (proof-advance 8 (division-boxed-setup-state 4 views allocation world)))
        (equal (division-boxed-setup-state 7 views allocation world)
               (proof-advance 4 (division-boxed-setup-state 6 views allocation world)))
        (equal (division-boxed-setup-state 9 views allocation world)
               (proof-advance 4 (division-boxed-setup-state 8 views allocation world))))
   :rule-classes nil))

(local
 (defthm division-boxed-view-return-has-view
   (implies (division-boxed-view-call-return-p value count before after objects packages)
            (proof-integer-view-p value (proof-world-reg 0 after) count after))
   :hints (("Goal" :in-theory (disable proof-frame-return-p proof-covered-p)))
   :rule-classes nil))

(local
 (defthm division-boxed-span-covers-itself
   (implies (proof-span-p address size)
            (and (proof-subspan-p address size address (+ address size))
                 (proof-subspan-p address size address (+ size address))))
   :rule-classes nil))

(local
 (defthm division-boxed-prologue-and-reservation-frames
   (let* ((first (division-boxed-setup-state 1 views allocation world))
          (reserve-return (division-boxed-setup-state 6 views allocation world)))
     (implies (division-boxed-setup-ready-p a b a-count b-count views allocation world
                                           old-objects new-objects packages)
              (and (equal (proof-world-pc reserve-return) (+ 84 (proof-world-pc world)))
                   (equal (proof-world-reg 20 reserve-return) (division-buffer-bytes a-count b-count))
                   (equal (division-boxed-stack-address 0 reserve-return) (division-boxed-stack-address 0 first))
                   (equal (division-boxed-mode first) (proof-world-reg 2 world)))))
   :hints (("Goal"
            :use ((:instance division-boxed-setup-checked-blocks-advance)
                  (:instance division-boxed-enters-first-view)
                  (:instance division-boxed-view-return-keeps-frame (value a) (count a-count)
                             (before (division-boxed-setup-state 1 views allocation world))
                             (after (division-boxed-setup-state 2 views allocation world)) (objects old-objects))
                  (:instance division-boxed-passes-view-arguments (phase :second)
                             (world (division-boxed-setup-state 2 views allocation world)))
                  (:instance division-boxed-view-return-keeps-frame (value b) (count b-count)
                             (before (division-boxed-setup-state 3 views allocation world))
                             (after (division-boxed-setup-state 4 views allocation world)) (objects old-objects))
                  (:instance division-boxed-reserves-five-buffers (world (division-boxed-setup-state 4 views allocation world)))
                  (:instance division-boxed-reservation-return-keeps-frame (bytes (division-reservation-bytes a-count b-count))
                             (before (division-boxed-setup-state 5 views allocation world))
                             (after (division-boxed-setup-state 6 views allocation world))))
            :in-theory (disable division-boxed-setup-state division-boxed-saved-registers-p
                                proof-span-p proof-disjoint-p
                                proof-integer-reserve-return-p division-boxed-view-call-return-p
                                division-boxed-entry-inputs-p division-boxed-reservation-inputs-p
                                division-boxed-view-call-inputs-p division-boxed-choose-path-inputs-p
                                division-view-bytes proof-frame-return-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-boxed-setup-has-refreshed-views
   (let* ((reserved (division-boxed-setup-state 6 views allocation world))
          (left-return (division-boxed-setup-state 8 views allocation world))
          (right-return (division-boxed-setup-state 10 views allocation world))
          (left-address (proof-world-reg 0 left-return))
          (right-address (proof-world-reg 0 right-return)))
     (implies (division-boxed-setup-ready-p a b a-count b-count views allocation world
                                           old-objects new-objects packages)
              (and (equal (proof-world-reg 19 right-return) (proof-world-reg 2 reserved))
                   (equal (proof-world-reg 20 right-return) (proof-world-reg 20 reserved))
                   (equal (proof-world-reg 21 right-return) left-address)
                   (equal (proof-world-pc right-return) (+ 32 (proof-world-pc reserved)))
                   (equal (division-boxed-stack-address 0 right-return) (division-boxed-stack-address 0 reserved))
                   (proof-integer-view-p a left-address a-count right-return)
                   (proof-integer-view-p b right-address b-count right-return)
                   (not (proof-world-stop right-return)))))
   :hints (("Goal"
            :use ((:instance division-boxed-setup-checked-blocks-advance)
                  (:instance division-boxed-passes-view-arguments (phase :refresh-left)
                             (world (division-boxed-setup-state 6 views allocation world)))
                  (:instance division-boxed-view-return-keeps-frame (value a) (count a-count)
                             (before (division-boxed-setup-state 7 views allocation world))
                             (after (division-boxed-setup-state 8 views allocation world)) (objects new-objects))
                  (:instance division-boxed-passes-view-arguments (phase :refresh-right)
                             (world (division-boxed-setup-state 8 views allocation world)))
                  (:instance division-boxed-view-return-keeps-frame (value b) (count b-count)
                             (before (division-boxed-setup-state 9 views allocation world))
                             (after (division-boxed-setup-state 10 views allocation world)) (objects new-objects))
                  (:instance division-boxed-view-return-has-view (value a) (count a-count)
                             (before (division-boxed-setup-state 7 views allocation world))
                             (after (division-boxed-setup-state 8 views allocation world)) (objects new-objects))
                  (:instance division-boxed-view-return-has-view (value b) (count b-count)
                             (before (division-boxed-setup-state 9 views allocation world))
                             (after (division-boxed-setup-state 10 views allocation world)) (objects new-objects))
                  (:instance division-boxed-span-covers-itself
                             (address (proof-world-reg 0 (division-boxed-setup-state 8 views allocation world)))
                             (size (division-view-bytes a-count)))
                  (:instance division-integer-view-after-span-agreement
                             (value a) (count a-count)
                             (address (proof-world-reg 0 (division-boxed-setup-state 8 views allocation world)))
                             (start (proof-world-reg 0 (division-boxed-setup-state 8 views allocation world)))
                             (end (+ (proof-world-reg 0 (division-boxed-setup-state 8 views allocation world))
                                     (division-view-bytes a-count)))
                             (before (division-boxed-setup-state 8 views allocation world))
                             (after (division-boxed-setup-state 10 views allocation world))))
            :in-theory (disable division-boxed-setup-state proof-subspan-p proof-disjoint-p proof-span-p
                                proof-integer-reserve-return-p proof-frame-return-p division-boxed-view-call-return-p
                                division-boxed-entry-inputs-p division-boxed-reservation-inputs-p
                                division-boxed-view-call-inputs-p division-boxed-choose-path-inputs-p
                                division-view-bytes proof-covered-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))
(local
 (defthm division-boxed-setup-final-stage
   (equal (division-boxed-setup-state 11 views allocation world)
          (proof-advance 5 (division-boxed-setup-state 10 views allocation world)))))

(local
 (defthm division-boxed-choose-slot-fits
   (implies (division-boxed-choose-path-inputs-p world)
            (proof-span-p (division-boxed-stack-address 80 world) 8))
   :rule-classes nil))

(local
 (defthm division-boxed-setup-keeps-mode
   (implies (division-boxed-setup-ready-p a b a-count b-count views allocation world
                                         old-objects new-objects packages)
            (equal (division-boxed-mode (division-boxed-setup-state 10 views allocation world))
                   (proof-world-reg 2 world)))
   :hints (("Goal"
            :use ((:instance division-boxed-prologue-and-reservation-frames)
                  (:instance division-boxed-setup-has-refreshed-views)
                  (:instance division-boxed-span-covers-itself
                             (address (division-boxed-stack-address 64 (division-boxed-setup-state 1 views allocation world)))
                             (size 8))
                  (:instance division-read-after-span-agreement
                             (address (division-boxed-stack-address 64 (division-boxed-setup-state 1 views allocation world)))
                             (count 8)
                             (start (division-boxed-stack-address 64 (division-boxed-setup-state 1 views allocation world)))
                             (end (+ 8 (division-boxed-stack-address 64 (division-boxed-setup-state 1 views allocation world))))
                             (before (division-boxed-setup-state 1 views allocation world))
                             (after (division-boxed-setup-state 10 views allocation world))))
            :in-theory (e/d (proof-load-word)
                            (boymoo-model::a64-load division-boxed-setup-state proof-integer-reserve-return-p
                             proof-subspan-p proof-span-p
                             division-boxed-view-call-return-p division-view-bytes division-boxed-entry-inputs-p
                             division-boxed-reservation-inputs-p division-boxed-view-call-inputs-p
                             division-boxed-choose-path-inputs-p))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-setup-prepares-views-and-workspace
  (let* ((after (proof-advance (division-boxed-setup-steps views allocation) world))
         (reserved (division-boxed-setup-state 6 views allocation world))
         (base (proof-world-reg 2 reserved))
         (stride (division-buffer-bytes a-count b-count))
         (mode (proof-world-reg 2 world))
         (slot (division-boxed-stack-address 80 after)))
    (implies (division-boxed-setup-ready-p a b a-count b-count views allocation world
                                          old-objects new-objects packages)
             (and (equal (proof-world-pc after)
                         (+ (proof-world-pc world) (if (equal mode 0) 136 *division-boxed-entry-to-copy*)))
                  (equal (proof-world-reg 19 after) base)
                  (equal (proof-world-reg 20 after) stride)
                  (equal (proof-world-reg 1 after) mode)
                  (equal (proof-load-word slot (proof-world-machine after)) (+ base stride))
                  (proof-reserved-span-p :header base (division-reservation-bytes a-count b-count) reserved new-objects)
                  (proof-integer-view-p a (proof-world-reg 21 after) a-count after)
                  (proof-integer-view-p b (proof-world-reg 22 after) b-count after))))
  :hints (("Goal"
           :use ((:instance division-boxed-setup-state-is-execution)
                 (:instance division-boxed-prologue-and-reservation-frames)
                 (:instance division-boxed-setup-has-refreshed-views)
                 (:instance division-boxed-setup-keeps-mode)
                 (:instance division-boxed-choose-slot-fits (world (division-boxed-setup-state 10 views allocation world)))
                 (:instance division-boxed-initializes-remainder-slot
                            (world (division-boxed-setup-state 10 views allocation world)))
                 (:instance division-view-after-disjoint-word-write
                            (value a) (count a-count)
                            (address (proof-world-reg 0 (division-boxed-setup-state 8 views allocation world)))
                            (target (division-boxed-stack-address 80 (division-boxed-setup-state 10 views allocation world)))
                            (word (division-boxed-initial-remainder (division-boxed-setup-state 10 views allocation world)))
                            (before (division-boxed-setup-state 10 views allocation world))
                            (after (division-boxed-setup-state 11 views allocation world)))
                 (:instance division-view-after-disjoint-word-write
                            (value b) (count b-count)
                            (address (proof-world-reg 0 (division-boxed-setup-state 10 views allocation world)))
                            (target (division-boxed-stack-address 80 (division-boxed-setup-state 10 views allocation world)))
                            (word (division-boxed-initial-remainder (division-boxed-setup-state 10 views allocation world)))
                            (before (division-boxed-setup-state 10 views allocation world))
                            (after (division-boxed-setup-state 11 views allocation world))))
           :in-theory (disable division-boxed-setup-state division-boxed-setup-steps
                               proof-span-p proof-disjoint-p
                               division-boxed-entry-inputs-p division-boxed-reservation-inputs-p
                               division-boxed-view-call-return-p division-boxed-view-call-inputs-p
                               division-boxed-choose-path-inputs-p division-view-bytes proof-frame-return-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

