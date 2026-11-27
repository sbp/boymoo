(in-package "BOYMOO-PROOFS")

(include-book "boxed-divide")
(include-book "boxed-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable abs ash floor mod proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-instruction-sequence-ready-p
                     division-boxed-inner-call-inputs-p division-boxed-save-sign-inputs-p
                     division-unsigned-ready-p division-unsigned-steps division-result-view-count
                     division-boxed-finish-ready-p division-boxed-sign-inputs-p proof-integer-view-p
                     proof-exact-quotient-p proof-reg-value-p boymoo-model::a64-sp boymoo-model::a64-memory)))

(defun division-boxed-quotient-entered (world)
  (proof-advance 7 (proof-advance 4 world)))

(defun division-boxed-quotient-divide-steps (a-count b-count q-steps r-steps world)
  (division-unsigned-steps a-count b-count q-steps r-steps (division-boxed-quotient-entered world)))

(defun division-boxed-quotient-divided (a-count b-count q-steps r-steps world)
  (proof-advance (division-boxed-quotient-divide-steps a-count b-count q-steps r-steps world)
                 (division-boxed-quotient-entered world)))

(defun division-boxed-quotient-view-steps (a-count b-count q-steps r-steps world)
  (+ 19 (division-boxed-quotient-divide-steps a-count b-count q-steps r-steps world)))

(defun division-boxed-quotient-view-ready-p (a b quotient a-count b-count q-steps r-steps world)
  (let* ((call (proof-advance 4 world))
         (entered (division-boxed-quotient-entered world))
         (divided (division-boxed-quotient-divided a-count b-count q-steps r-steps world))
         (quotient-address (proof-world-reg 19 divided))
         (count (division-result-view-count quotient-address divided)))
    (and (posp b) (proof-exact-quotient-p a b quotient)
         (division-boxed-save-sign-inputs-p a b a-count b-count world)
         (division-instruction-sequence-ready-p *division-boxed-quotient-save-sign-instructions*
                                                (list (+ 16 (proof-world-pc world))) world)
         (division-boxed-inner-call-inputs-p nil call)
         (division-instruction-sequence-ready-p (division-boxed-inner-call-instructions nil)
                                                (list (division-boxed-inner-target nil call)) call)
         (division-unsigned-ready-p a b a-count b-count q-steps r-steps entered)
         (equal (division-boxed-sign divided) (division-boxed-sign call))
         (division-boxed-sign-inputs-p count divided)
         (proof-span-p quotient-address (division-view-bytes count))
         (division-instruction-sequence-ready-p *division-boxed-quotient-sign-instructions*
                                                (list (+ *division-boxed-sign-to-restore-offset*
                                                         (proof-world-pc divided))) divided))))

(local
 (defthm division-boxed-quotient-sign-is-saved
   (implies (division-boxed-save-sign-output-p a world after)
            (equal (division-boxed-sign after) (if (< a 0) 1 0)))))

(local
 (defthm division-boxed-quotient-divides-magnitudes
   (let ((divided (division-boxed-quotient-divided a-count b-count q-steps r-steps world)))
     (implies (division-boxed-quotient-view-ready-p a b quotient a-count b-count q-steps r-steps world)
              (and (equal (division-boxed-sign divided) (if (< a 0) 1 0))
                   (proof-integer-view-p (abs quotient) (proof-world-reg 19 divided)
                                         (division-result-view-count (proof-world-reg 19 divided) divided) divided))))
   :hints (("Goal"
            :use ((:instance division-boxed-saves-quotient-sign)
                  (:instance division-boxed-quotient-sign-is-saved (after (proof-advance 4 world)))
                  (:instance division-boxed-call-enters-divider (gcd nil) (world (proof-advance 4 world)))
                  (:instance division-unsigned-entry-to-return (world (division-boxed-quotient-entered world)))
                  (:instance division-exact-divisor-remainder-zero (q quotient)))
            :in-theory (disable division-boxed-sign division-boxed-save-sign-output-p
                                division-boxed-inner-target division-boxed-inner-call-instructions
                                division-view-bytes)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-boxed-quotient-advance-to-view
   (equal (proof-advance (division-boxed-quotient-view-steps a-count b-count q-steps r-steps world) world)
          (proof-advance 8 (division-boxed-quotient-divided a-count b-count q-steps r-steps world)))
   :hints (("Goal"
            :use (:instance division-advance-chain-sum
                            (counts (list 4 7 (division-boxed-quotient-divide-steps a-count b-count q-steps r-steps world) 8)))
            :in-theory (disable proof-advance-append)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-exact-quotient-produces-view
  (let* ((divided (division-boxed-quotient-divided a-count b-count q-steps r-steps world))
         (after (proof-advance (division-boxed-quotient-view-steps a-count b-count q-steps r-steps world) world))
         (address (proof-world-reg 19 divided))
         (count (division-result-view-count address divided)))
    (implies (division-boxed-quotient-view-ready-p a b quotient a-count b-count q-steps r-steps world)
             (proof-integer-view-p quotient (proof-world-reg 0 after) count after)))
  :hints (("Goal"
           :use ((:instance division-boxed-quotient-divides-magnitudes)
                 (:instance division-boxed-quotient-advance-to-view)
                 (:instance division-boxed-exact-quotient-writes-signed-view
                            (q quotient)
                            (count (division-result-view-count
                                    (proof-world-reg 19 (division-boxed-quotient-divided a-count b-count q-steps r-steps world))
                                    (division-boxed-quotient-divided a-count b-count q-steps r-steps world)))
                            (world (division-boxed-quotient-divided a-count b-count q-steps r-steps world))))
           :in-theory (disable division-boxed-quotient-divided division-boxed-quotient-view-steps
                               division-boxed-inner-target division-boxed-inner-call-instructions division-boxed-sign
                               division-view-bytes)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-boxed-signed-result-start (a-count b-count q-steps r-steps world)
  (proof-advance (division-boxed-quotient-view-steps a-count b-count q-steps r-steps world) world))

(defun division-boxed-quotient-count (a-count b-count q-steps r-steps world)
  (let ((divided (division-boxed-quotient-divided a-count b-count q-steps r-steps world)))
    (division-result-view-count (proof-world-reg 19 divided) divided)))

(defun division-boxed-exact-from-views-ready-p (a b quotient a-count b-count q-steps r-steps
                                                pack-steps entry world objects packages)
  (let ((signed (division-boxed-signed-result-start a-count b-count q-steps r-steps world))
        (count (division-boxed-quotient-count a-count b-count q-steps r-steps world))
        (cuts (list (proof-world-reg 30 entry))))
    (and (division-boxed-quotient-view-ready-p a b quotient a-count b-count q-steps r-steps world)
         (division-before-cuts-p (division-boxed-quotient-view-steps a-count b-count q-steps r-steps world) cuts world)
         (division-boxed-finish-ready-p entry quotient count pack-steps signed objects packages))))

(defun division-boxed-exact-from-views-steps (a-count b-count q-steps r-steps pack-steps world)
  (+ (division-boxed-quotient-view-steps a-count b-count q-steps r-steps world)
     (division-boxed-finish-steps pack-steps)))

(defthm division-boxed-exact-quotient-returns-from-views
  (let* ((steps (division-boxed-exact-from-views-steps a-count b-count q-steps r-steps pack-steps world))
         (cuts (list (proof-world-reg 30 entry)))
         (after (proof-advance steps world)))
    (implies (division-boxed-exact-from-views-ready-p a b quotient a-count b-count q-steps r-steps
                                                      pack-steps entry world objects packages)
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-reg-value-p 0 quotient after objects packages)
                  (implies (proof-immediate-integer-p quotient)
                           (equal (proof-world-reg 0 after) (proof-integer-word quotient))))))
  :hints (("Goal"
           :use ((:instance division-boxed-exact-quotient-produces-view)
                 (:instance division-boxed-finishes-through-pack
                            (value quotient) (count (division-boxed-quotient-count a-count b-count q-steps r-steps world))
                            (world (division-boxed-signed-result-start a-count b-count q-steps r-steps world)))
                 (:instance division-return-after-checked-prefix
                            (prefix (division-boxed-quotient-view-steps a-count b-count q-steps r-steps world))
                            (suffix (division-boxed-finish-steps pack-steps)) (cuts (list (proof-world-reg 30 entry)))))
           :in-theory (disable division-boxed-quotient-view-ready-p division-boxed-quotient-view-steps
                               division-boxed-quotient-divided division-boxed-finish-steps proof-immediate-integer-p
                               proof-integer-word)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
