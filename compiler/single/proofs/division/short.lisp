(in-package "BOYMOO-PROOFS")

(include-book "copy")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-short-instructions* (division-runtime-block "rt:z-divide-short" 0 4))
(defconst *division-short-to-copy-offset*
  (- (division-runtime-offset "rt:z-copy") (division-runtime-offset "rt:z-divide-short")))

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     division-before-cuts-p division-instruction-prefix-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-short-copy-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 16 (proof-world-pc world)))
       (unsigned-byte-p 64 (+ *division-short-to-copy-offset* (proof-world-pc world)))))

(defun division-short-copy-output-p (world after)
  (and (equal (proof-world-pc after) (+ (proof-world-pc world) *division-short-to-copy-offset*))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 3 world))
       (equal (proof-world-reg 9 after) 0)
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 30 after) (+ 16 (proof-world-pc world)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(local
 (defthm division-short-calls-copy-effects
   (implies (division-short-copy-inputs-p world)
            (division-short-copy-output-p
             world (division-instruction-sequence *division-short-instructions* world)))
   :hints (("Goal" :do-not-induct t))
   :rule-classes nil))

(defthm division-short-calls-copy
  (let* ((cuts (list (+ *division-short-to-copy-offset* (proof-world-pc world))))
         (after (proof-advance 4 world)))
    (implies (and (division-short-copy-inputs-p world)
                  (division-instruction-sequence-ready-p *division-short-instructions* cuts world))
             (and (proof-segment-p 4 cuts world :cut after)
                  (division-short-copy-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-short-calls-copy-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-short-instructions*)
                            (cuts (list (+ *division-short-to-copy-offset* (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-short-instructions*)
                            (cuts (list (+ *division-short-to-copy-offset* (proof-world-pc world))))))
           :in-theory (disable division-short-copy-inputs-p division-short-copy-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(local
 (defthm division-short-count-establishes-magnitude
   (implies (and (proof-integer-view-p a a-address a-count world)
                 (proof-integer-view-p b b-address b-count world)
                 (< a-count b-count))
            (< (abs a) (abs b)))
   :hints (("Goal"
            :use ((:instance division-view-magnitude-and-count
                             (value a) (address a-address) (count a-count))
                  (:instance division-view-magnitude-and-count
                             (value b) (address b-address) (count b-count))
                  (:instance division-shorten-dividend
                             (left (division-read-limbs a-count (+ 16 a-address) (proof-world-machine world)))
                             (right (division-read-limbs b-count (+ 16 b-address) (proof-world-machine world)))))
            :in-theory (disable proof-integer-view division-read-limbs division-magnitude)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-short-count-establishes-results
   (implies (and (proof-integer-view-p a a-address a-count world)
                 (proof-integer-view-p b b-address b-count world)
                 (< a-count b-count))
            (and (equal (floor (abs a) (abs b)) 0)
                 (equal (mod (abs a) (abs b)) (abs a))))
   :hints (("Goal"
            :use (:instance division-short-count-establishes-magnitude)
            :in-theory (disable proof-integer-view)
            :do-not-induct t))
   :rule-classes nil))

(defun division-short-before-normalization (count world)
  (proof-advance (+ 4 (division-step-sum (division-copy-call-counts count))) world))

(local
 (defthm division-short-before-normalization-composed
   (equal (division-short-before-normalization count world)
          (proof-advance (division-step-sum (division-copy-call-counts count)) (proof-advance 4 world)))
   :hints (("Goal"
            :use (:instance proof-advance-append (prefix 4)
                            (suffix (division-step-sum (division-copy-call-counts count))))
            :in-theory (disable division-step-sum division-copy-call-counts proof-advance-append)))
   :rule-classes nil))

(defthm division-short-prepares-unsigned-results
  (let* ((before-copy (proof-advance 4 world))
         (after (division-short-before-normalization a-count world))
         (r-address (proof-world-reg 3 world))
         (r-digits (division-read-limbs a-count (+ 16 r-address) (proof-world-machine after))))
    (implies (and (proof-integer-view-p a (proof-world-reg 0 world) a-count world)
                  (proof-integer-view-p b (proof-world-reg 1 world) b-count world)
                  (< a-count b-count)
                  (division-short-copy-inputs-p world)
                  (equal (proof-world-reg 9 world) (* 8 a-count))
                  (division-instruction-sequence-ready-p
                   *division-short-instructions* (list (+ *division-short-to-copy-offset* (proof-world-pc world))) world)
                  (division-copy-call-ready-p a a-count before-copy))
             (and (equal (proof-world-pc after) (+ 16 (proof-world-pc world)))
                  (equal (proof-world-reg 9 after) 0)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (* 8 a-count))
                  (equal (floor (abs a) (abs b)) 0)
                  (equal (division-magnitude r-digits) (mod (abs a) (abs b)))
                  (division-digits-p r-digits))))
  :hints (("Goal"
           :use ((:instance division-short-calls-copy)
                 (:instance division-short-count-establishes-results
                            (a-address (proof-world-reg 0 world)) (b-address (proof-world-reg 1 world)))
                 (:instance division-copy-call-returns-view (value a) (count a-count) (world (proof-advance 4 world)))
                 (:instance division-short-before-normalization-composed (count a-count))
                 (:instance division-view-magnitude-and-count
                            (value a) (count a-count) (address (proof-world-reg 3 world))
                            (world (division-short-before-normalization a-count world))))
           :in-theory (disable division-short-before-normalization division-copy-call-ready-p
                               division-step-sum division-copy-call-counts proof-integer-view-p
                               division-read-limbs division-magnitude)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
(defun division-short-call-prefix-counts (count)
  (list 15 (+ 4 (division-step-sum (division-copy-call-counts count)))))

(defun division-short-call-raw (count world)
  (division-short-before-normalization count (proof-advance 15 world)))

(defun division-short-call-remainder (count world)
  (division-read-limbs count (proof-world-reg 19 world) (proof-world-machine world)))

(defun division-short-call-ready-p (a b a-count b-count q-steps r-steps world)
  (let* ((cuts (list (proof-world-reg 30 world)))
         (branch (proof-advance 15 world))
         (copy-entry (proof-advance 4 branch))
         (raw (division-short-call-raw a-count world))
         (a-address (proof-world-reg 0 world))
         (b-address (proof-world-reg 1 world))
         (r-digits (division-short-call-remainder a-count raw)))
    (and (< a-count b-count)
         (proof-integer-view-p a a-address a-count world)
         (proof-integer-view-p b b-address b-count world)
         (division-divide-entry-inputs-p a-count b-count world)
         (division-instruction-prefix-ready-p (division-divide-dispatch-instructions a-count b-count) cuts world)
         (proof-span-p a-address (division-view-bytes a-count))
         (proof-span-p b-address (division-view-bytes b-count))
         (proof-memory-span-agrees-p a-address (+ a-address (division-view-bytes a-count)) world branch)
         (proof-memory-span-agrees-p b-address (+ b-address (division-view-bytes b-count)) world branch)
         (division-short-copy-inputs-p branch)
         (division-instruction-sequence-ready-p
          *division-short-instructions* (list (+ *division-short-to-copy-offset* (proof-world-pc branch))) branch)
         (division-copy-call-ready-p a a-count copy-entry)
         (division-before-cuts-p (+ 4 (division-step-sum (division-copy-call-counts a-count))) cuts branch)
         (division-normalization-return-ready-p world nil r-digits q-steps r-steps raw))))

(local
 (defthm division-short-call-dispatch-advances
   (implies (and (< a-count b-count)
                 (division-divide-entry-inputs-p a-count b-count world)
                 (division-instruction-prefix-ready-p (division-divide-dispatch-instructions a-count b-count) cuts world))
            (and (division-divide-dispatch-output-p a-count b-count world (proof-advance 15 world))
                 (division-before-cuts-p 15 cuts world)))
   :hints (("Goal"
            :use ((:instance division-divide-dispatch-effects)
                  (:instance division-instruction-prefix-advances
                             (instructions (division-divide-dispatch-instructions a-count b-count))))
            :in-theory (disable division-divide-entry-inputs-p division-divide-dispatch-output-p
                                division-instruction-sequence)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-short-call-raw-values
   (let* ((raw (division-short-call-raw a-count world))
          (r-digits (division-short-call-remainder a-count raw))
          (counts (division-short-call-prefix-counts a-count))
          (cuts (list (proof-world-reg 30 world))))
     (implies (division-short-call-ready-p a b a-count b-count q-steps r-steps world)
              (and (division-chain-before-cuts-p counts cuts world)
                   (equal (division-advance-chain counts world) raw)
                   (equal (division-normalization-address nil raw) (proof-world-reg 2 world))
                   (equal (division-normalization-address t raw) (proof-world-reg 3 world))
                   (equal (floor (abs a) (abs b)) 0)
                   (equal (division-magnitude r-digits) (mod (abs a) (abs b))))))
   :hints (("Goal"
            :use ((:instance division-short-call-dispatch-advances (cuts (list (proof-world-reg 30 world))))
                  (:instance division-integer-view-after-span-agreement
                             (value a) (count a-count) (address (proof-world-reg 0 world))
                             (start (proof-world-reg 0 world)) (end (+ (proof-world-reg 0 world) (division-view-bytes a-count)))
                             (before world) (after (proof-advance 15 world)))
                  (:instance division-integer-view-after-span-agreement
                             (value b) (count b-count) (address (proof-world-reg 1 world))
                             (start (proof-world-reg 1 world)) (end (+ (proof-world-reg 1 world) (division-view-bytes b-count)))
                             (before world) (after (proof-advance 15 world)))
                  (:instance division-short-prepares-unsigned-results (world (proof-advance 15 world))))
            :in-theory (disable proof-integer-view-p proof-memory-span-agrees-p division-view-bytes
                                division-short-copy-inputs-p division-copy-call-ready-p
                                division-divide-entry-inputs-p division-normalization-return-ready-p division-step-sum
                                division-copy-call-counts division-divide-saved-registers-p division-magnitude
                                division-instruction-prefix-ready-p division-read-limbs division-before-cuts-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-short-call-steps (count q-steps r-steps)
  (+ (division-step-sum (division-short-call-prefix-counts count))
     (division-step-sum (division-normalization-return-steps q-steps r-steps))))

(local
 (defthm division-short-call-first-return
   (let* ((raw (division-short-call-raw a-count world))
          (counts (division-short-call-prefix-counts a-count))
          (prefix (division-step-sum counts))
          (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))
          (cuts (list (proof-world-reg 30 world)))
          (after (proof-advance suffix raw)))
     (implies (and (division-short-call-ready-p a b a-count b-count q-steps r-steps world)
                   (proof-segment-p suffix cuts raw :cut after))
              (and (proof-segment-p (+ prefix suffix) cuts world :cut after)
                   (equal (proof-advance (+ prefix suffix) world) after))))
   :hints (("Goal"
            :use ((:instance division-short-call-raw-values)
                  (:instance division-advance-chain-sum (counts (division-short-call-prefix-counts a-count)))
                  (:instance division-chain-keeps-before-cuts (counts (division-short-call-prefix-counts a-count))
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance division-run-after-cut-free-prefix
                             (prefix (division-step-sum (division-short-call-prefix-counts a-count)))
                             (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-advance-append
                             (prefix (division-step-sum (division-short-call-prefix-counts a-count)))
                             (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))))
            :in-theory (e/d (proof-segment-p)
                            (division-short-call-ready-p division-short-call-raw division-short-call-prefix-counts
                             division-step-sum division-normalization-return-steps proof-run
                             division-short-call-remainder division-chain-before-cuts-p
                             division-advance-chain proof-advance-append division-run-after-cut-free-prefix))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-short-entry-to-return
  (let* ((raw (division-short-call-raw a-count world))
         (r-digits (division-short-call-remainder a-count raw))
         (steps (division-short-call-steps a-count q-steps r-steps))
         (after (proof-advance steps world)))
    (implies (division-short-call-ready-p a b a-count b-count q-steps r-steps world)
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (equal (floor (abs a) (abs b)) 0)
                  (proof-integer-view-p 0 (proof-world-reg 2 world) 0 after)
                  (proof-integer-view-p (mod (abs a) (abs b)) (proof-world-reg 3 world)
                                        (len (division-trim-limbs r-digits)) after)
                  (equal (proof-world-reg 0 after) (proof-world-reg 3 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance division-short-call-raw-values)
                 (:instance division-short-call-first-return)
                 (:instance division-divide-normalize-and-return
                            (entry world) (world (division-short-call-raw a-count world))
                            (q-digits nil)
                            (r-digits (division-short-call-remainder a-count (division-short-call-raw a-count world)))))
           :in-theory (disable division-short-call-raw division-short-call-prefix-counts division-short-call-remainder
                               division-step-sum division-normalization-return-steps division-normalization-address
                               division-divide-entry-inputs-p division-short-copy-inputs-p division-copy-call-ready-p
                               division-view-bytes proof-memory-span-agrees-p division-before-cuts-p
                               division-instruction-prefix-ready-p division-read-limbs
                               division-normalization-return-ready-p proof-integer-view-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

