(in-package "BOYMOO-PROOFS")

(include-book "dispatch")
(include-book "sign-view")
(include-book "ranges")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-boxed-gcd-select-instructions* (division-runtime-block "rt:z-gcd-loop" 0 9))
(defconst *division-boxed-gcd-rotate-instructions* (division-runtime-block "rt:z-gcd-divide" 1 5))
(defconst *division-gcd-to-done-offset*
  (- (division-runtime-offset "rt:z-gcd-done") (division-runtime-offset "rt:z-gcd-loop")))
(defconst *division-gcd-to-one-offset*
  (- (division-runtime-offset "rt:z-gcd-one") (division-runtime-offset "rt:z-gcd-loop")))
(defconst *division-gcd-to-divide-offset*
  (- (division-runtime-offset "rt:z-gcd-divide") (division-runtime-offset "rt:z-gcd-loop")))
(defconst *division-gcd-rotate-to-loop-offset*
  (- (division-runtime-offset "rt:z-gcd-loop") (+ 4 (division-runtime-offset "rt:z-gcd-divide"))))

(local
 (in-theory (disable ash floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes boymoo-model::a64-sp
                     boymoo-model::a64-nzcv boymoo-model::a64-condition boymoo-model::a64-shift
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defthm division-normalized-magnitude-positive
   (implies (and (division-normalized-limbs-p digits) (consp digits))
            (posp (division-magnitude digits)))
   :hints (("Goal" :induct (division-normalized-limbs-p digits)))))

(local
 (defthm division-read-one-view-limb
   (equal (division-read-limbs 1 address machine)
          (list (proof-load-word address machine)))
   :hints (("Goal" :expand ((division-read-limbs 1 address machine)
                            (division-read-limbs 0 (+ 8 address) machine))))))

(local
 (defthm division-boxed-load-word-is-bounded
   (unsigned-byte-p 64 (proof-load-word address machine))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8) (memory (boymoo-model::a64-memory machine)))
            :in-theory (e/d (proof-load-word)
                            (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm division-view-zero-and-one-tests
  (implies (and (proof-integer-view-p value address count world) (natp value))
           (and (equal (equal count 0) (equal value 0))
                (equal (and (equal count 1)
                            (equal (proof-load-word (+ 16 address) (proof-world-machine world)) 1))
                       (equal value 1))))
  :hints (("Goal"
           :cases ((equal count 0) (equal count 1))
           :use ((:instance division-view-magnitude-and-count)
                 (:instance division-shorten-dividend
                            (left '(1)) (right (division-read-limbs count (+ 16 address)
                                                                    (proof-world-machine world))))
                 (:instance division-normalized-magnitude-positive
                            (digits (division-read-limbs count (+ 16 address) (proof-world-machine world)))))
           :in-theory (disable proof-integer-view division-read-limbs division-normalized-magnitude-positive)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-boxed-gcd-select-instructions (count)
  (take (cond ((equal count 0) 4) ((equal count 1) 9) (t 6))
        *division-boxed-gcd-select-instructions*))

(defun division-boxed-gcd-select-offset (value)
  (cond ((equal value 0) *division-gcd-to-done-offset*)
        ((equal value 1) *division-gcd-to-one-offset*)
        (t *division-gcd-to-divide-offset*)))

(defun division-boxed-gcd-select-inputs-p (value count world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ *division-gcd-to-one-offset* (proof-world-pc world)))
       (natp value)
       (natp count) (< count (expt 2 29))
       (proof-integer-view-p value (proof-world-reg 22 world) count world)))

(defun division-boxed-gcd-select-output-p (value world after)
  (and (equal (proof-world-pc after) (+ (division-boxed-gcd-select-offset value) (proof-world-pc world)))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(defthm division-boxed-gcd-select-effects
  (implies (division-boxed-gcd-select-inputs-p value count world)
           (division-boxed-gcd-select-output-p
            value world (division-instruction-sequence (division-boxed-gcd-select-instructions count) world)))
  :hints (("Goal"
           :cases ((equal count 0) (equal count 1))
           :use ((:instance division-view-zero-and-one-tests (address (proof-world-reg 22 world)))
                 (:instance division-boxed-load-word-is-bounded
                            (address (+ 16 (proof-world-reg 22 world))) (machine (proof-world-machine world)))
                 (:instance division-quotient-unique
                            (a (+ 3 (* 2048 (1+ count)))) (b 2048) (q (1+ count)) (r 3)))
           :in-theory (disable proof-integer-view)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-boxed-gcd-select-runs
  (let* ((instructions (division-boxed-gcd-select-instructions count))
         (steps (len instructions))
         (cuts (list (+ (division-boxed-gcd-select-offset value) (proof-world-pc world))))
         (after (proof-advance steps world)))
    (implies (and (division-boxed-gcd-select-inputs-p value count world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-boxed-gcd-select-output-p value world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-gcd-select-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-boxed-gcd-select-instructions count))
                            (cuts (list (+ (division-boxed-gcd-select-offset value) (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-boxed-gcd-select-instructions count))
                            (cuts (list (+ (division-boxed-gcd-select-offset value) (proof-world-pc world))))))
           :in-theory (disable division-boxed-gcd-select-inputs-p division-boxed-gcd-select-output-p
                               division-boxed-gcd-select-offset division-boxed-gcd-select-instructions
                               division-instruction-sequence)))
  :rule-classes nil)

(defun division-boxed-remainder-slot (world)
  (+ 80 (boymoo-model::a64-sp (proof-world-machine world))))

(defun division-boxed-gcd-rotate-inputs-p (world)
  (let ((slot (division-boxed-remainder-slot world)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
         (unsigned-byte-p 64 (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc world)))
         (proof-span-p slot 8)
         (unsigned-byte-p 64 (proof-load-word slot (proof-world-machine world))))))

(defun division-boxed-gcd-rotate-output-p (world after)
  (let* ((slot (division-boxed-remainder-slot world))
         (remainder (proof-load-word slot (proof-world-machine world))))
    (and (equal (proof-world-pc after) (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc world)))
         (equal (proof-world-reg 21 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 22 after) remainder)
         (equal (proof-load-word slot (proof-world-machine after)) (proof-world-reg 21 world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes 8 slot (proof-world-reg 21 world)
                                              (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-boxed-gcd-rotate-effects
  (implies (division-boxed-gcd-rotate-inputs-p world)
           (division-boxed-gcd-rotate-output-p
            world (division-instruction-sequence *division-boxed-gcd-rotate-instructions* world)))
  :hints (("Goal"
           :use (:instance division-world-register-in-word (register 21))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-boxed-gcd-rotates-views
  (let* ((cuts (list (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc world))))
         (after (proof-advance 5 world)))
    (implies (and (division-boxed-gcd-rotate-inputs-p world)
                  (division-instruction-sequence-ready-p *division-boxed-gcd-rotate-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (division-boxed-gcd-rotate-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-gcd-rotate-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-gcd-rotate-instructions*)
                            (cuts (list (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-gcd-rotate-instructions*)
                            (cuts (list (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc world))))))
           :in-theory (disable division-boxed-gcd-rotate-inputs-p division-boxed-gcd-rotate-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defthm division-boxed-gcd-euclidean-step
  (let* ((slot (division-boxed-remainder-slot world))
         (remainder (proof-load-word slot (proof-world-machine world)))
         (b-address (proof-world-reg 22 world))
         (r (mod (abs a) b))
         (b-bytes (division-view-bytes b-count))
         (r-bytes (division-view-bytes r-count))
         (after (proof-advance 5 world))
         (cuts (list (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc world)))))
    (implies (and (integerp a) (posp b)
                  (proof-integer-view-p b b-address b-count world)
                  (proof-integer-view-p r remainder r-count world)
                  (proof-span-p b-address b-bytes) (proof-span-p remainder r-bytes)
                  (proof-disjoint-p b-address (+ b-address b-bytes) slot (+ slot 8))
                  (proof-disjoint-p remainder (+ remainder r-bytes) slot (+ slot 8))
                  (division-boxed-gcd-rotate-inputs-p world)
                  (division-instruction-sequence-ready-p *division-boxed-gcd-rotate-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (proof-integer-view-p b (proof-world-reg 21 after) b-count after)
                  (proof-integer-view-p r (proof-world-reg 22 after) r-count after)
                  (equal (proof-load-word slot (proof-world-machine after)) (proof-world-reg 21 world))
                  (natp r)
                  (< r b))))
  :hints (("Goal"
           :use ((:instance division-boxed-gcd-rotates-views)
                 (:instance division-mod-bounds (a (abs a)))
                 (:instance division-view-after-disjoint-word-write
                            (value b) (count b-count) (address (proof-world-reg 22 world))
                            (target (division-boxed-remainder-slot world)) (word (proof-world-reg 21 world))
                            (before world) (after (proof-advance 5 world)))
                 (:instance division-view-after-disjoint-word-write
                            (value (mod (abs a) b)) (count r-count)
                            (address (proof-load-word (division-boxed-remainder-slot world) (proof-world-machine world)))
                            (target (division-boxed-remainder-slot world)) (word (proof-world-reg 21 world))
                            (before world) (after (proof-advance 5 world))))
           :in-theory (disable proof-integer-view-p division-view-bytes proof-span-p proof-disjoint-p
                               division-boxed-remainder-slot)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defconst *division-boxed-gcd-done-instructions* (division-runtime-block "rt:z-gcd-done" 0 3))
(defconst *division-boxed-gcd-one-instructions* (division-runtime-block "rt:z-gcd-one" 0 2))
(defconst *division-gcd-done-to-pack-setup*
  (- (division-runtime-offset "rt:z-division-return") (division-runtime-offset "rt:z-gcd-done")))

(defun division-boxed-gcd-finish-instructions (one)
  (if one *division-boxed-gcd-one-instructions* *division-boxed-gcd-done-instructions*))

(defun division-boxed-gcd-finish-target (one world)
  (+ (proof-world-pc world) (if one 8 *division-gcd-done-to-pack-setup*)))

(defun division-boxed-gcd-finish-address (one world)
  (proof-world-reg (if one 22 21) world))

(defun division-boxed-gcd-finish-output-p (one world after)
  (let ((address (division-boxed-gcd-finish-address one world)))
    (and (equal (proof-world-reg 0 after) address)
         (equal (proof-world-pc after) (division-boxed-gcd-finish-target one world))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 (+ address 8) 0 (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-boxed-gcd-finish-effects
  (implies (and (division-ordinary-world-p world)
                (unsigned-byte-p 64 (division-boxed-gcd-finish-target one world)))
           (division-boxed-gcd-finish-output-p
            one world (division-instruction-sequence (division-boxed-gcd-finish-instructions one) world)))
  :hints (("Goal" :cases (one) :do-not-induct t))
  :rule-classes nil)

(defthm division-boxed-gcd-finishes-with-natural-view
  (let* ((address (division-boxed-gcd-finish-address one world))
         (target (division-boxed-gcd-finish-target one world))
         (instructions (division-boxed-gcd-finish-instructions one))
         (steps (len instructions))
         (after (proof-advance steps world))
         (value (if one 1 a)))
    (implies (and (integerp a) (equal b (if one 1 0))
                  (division-ordinary-world-p world) (unsigned-byte-p 64 target)
                  (proof-integer-view-p value address count world)
                  (proof-span-p address (division-view-bytes count))
                  (division-instruction-sequence-ready-p instructions (list target) world))
             (and (proof-segment-p steps (list target) world :cut after)
                  (equal (proof-world-reg 0 after) address)
                  (proof-integer-view-p (abs value) address count after)
                  (proof-gcd-p a b (abs value)))))
  :hints (("Goal"
           :cases (one)
           :use ((:instance division-boxed-gcd-finish-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-boxed-gcd-finish-instructions one))
                            (cuts (list (division-boxed-gcd-finish-target one world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-boxed-gcd-finish-instructions one))
                            (cuts (list (division-boxed-gcd-finish-target one world))))
                 (:instance division-view-after-writing-sign
                            (value (if one 1 a)) (sign 0)
                            (address (division-boxed-gcd-finish-address one world))
                            (before world)
                            (after (proof-advance (len (division-boxed-gcd-finish-instructions one)) world)))
                 (:instance division-gcd-witness-gives-contract (b 1) (g 1) (left 0) (right 1)))
           :in-theory (disable proof-integer-view-p division-view-bytes division-instruction-sequence)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
