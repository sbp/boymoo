(in-package "BOYMOO-PROOFS")

(include-book "boxed-setup")
(include-book "boxed-exact")
(include-book "boxed-copies")
(include-book "boxed-euclid")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable abs floor mod proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-public-prefix-ready-p division-public-route
                     division-boxed-setup-ready-p division-boxed-setup-steps division-gcd-copy-steps
                     division-boxed-gcd-loop-ready-p division-boxed-gcd-loop-steps division-gcd-magnitude
                     division-boxed-exact-from-views-ready-p division-boxed-exact-from-views-steps
                     division-boxed-finish-ready-p proof-integer-view-p proof-immediate-integer-p
                     proof-reg-value-p proof-integer-word proof-gcd-p)))

(defun division-public-boxed-start (gcd views allocation world)
  (proof-advance (division-boxed-setup-steps views allocation) (division-public-body gcd world)))

(defun division-public-boxed-prefix-steps (gcd views allocation world)
  (+ (division-public-prefix-count gcd world) (division-boxed-setup-steps views allocation)))

(defun division-public-boxed-prefix-ready-p (gcd a b a-count b-count views allocation world
                                                old-objects new-objects packages)
  (let ((body (division-public-body gcd world))
        (cuts (list (proof-world-reg 30 world))))
    (and (integerp a) (posp b)
         (proof-reg-value-p 0 a world old-objects packages)
         (proof-reg-value-p 1 b world old-objects packages)
         (eq (division-public-route gcd (proof-world-reg 0 world) (proof-world-reg 1 world)) :boxed)
         (division-public-prefix-ready-p gcd world)
         (division-boxed-setup-ready-p a b a-count b-count views allocation body old-objects new-objects packages)
         (division-before-cuts-p (division-boxed-setup-steps views allocation) cuts body))))

(local
 (defthm division-boxed-setup-steps-natural
   (natp (division-boxed-setup-steps views allocation))
   :hints (("Goal" :in-theory (enable division-boxed-setup-steps)))
   :rule-classes :type-prescription))

(defthm division-public-boxed-prefix-advances
  (let* ((steps (division-public-boxed-prefix-steps gcd views allocation world))
         (cuts (list (proof-world-reg 30 world)))
         (after (proof-advance steps world)))
    (implies (division-public-boxed-prefix-ready-p gcd a b a-count b-count views allocation world
                                                    old-objects new-objects packages)
             (and (equal after (division-public-boxed-start gcd views allocation world))
                  (division-before-cuts-p steps cuts world)
                  (equal (proof-world-reg 1 after) (if gcd 1 0))
                  (proof-integer-view-p a (proof-world-reg 21 after) a-count after)
                  (proof-integer-view-p b (proof-world-reg 22 after) b-count after))))
  :hints (("Goal"
           :use ((:instance division-public-prefix-passes-arguments)
                 (:instance division-boxed-setup-prepares-views-and-workspace
                            (world (division-public-body gcd world)))
                 (:instance proof-advance-append (prefix (division-public-prefix-count gcd world))
                            (suffix (division-boxed-setup-steps views allocation)))
                 (:instance division-before-cuts-append (prefix (division-public-prefix-count gcd world))
                            (suffix (division-boxed-setup-steps views allocation))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-public-prefix-count division-public-target division-boxed-setup-state
                               division-buffer-bytes division-reservation-bytes proof-reserved-span-p
                               proof-advance-append division-before-cuts-append)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-public-boxed-exact-quotient-returns
  (let* ((prefix (division-public-boxed-prefix-steps nil views allocation world))
         (body (division-public-boxed-start nil views allocation world))
         (suffix (division-boxed-exact-from-views-steps a-count b-count q-steps r-steps pack-steps body))
         (steps (+ prefix suffix))
         (after (proof-advance steps world))
         (cuts (list (proof-world-reg 30 world))))
    (implies (and (division-public-boxed-prefix-ready-p nil a b a-count b-count views allocation world
                                                         old-objects new-objects packages)
                  (division-boxed-exact-from-views-ready-p a b quotient a-count b-count q-steps r-steps
                                                           pack-steps world body new-objects packages))
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-reg-value-p 0 quotient after new-objects packages)
                  (implies (proof-immediate-integer-p quotient)
                           (equal (proof-world-reg 0 after) (proof-integer-word quotient))))))
  :hints (("Goal"
           :use ((:instance division-public-boxed-prefix-advances (gcd nil))
                 (:instance division-boxed-exact-quotient-returns-from-views
                            (entry world) (world (division-public-boxed-start nil views allocation world))
                            (objects new-objects))
                 (:instance division-return-after-checked-prefix
                            (prefix (division-public-boxed-prefix-steps nil views allocation world))
                            (suffix (division-boxed-exact-from-views-steps
                                     a-count b-count q-steps r-steps pack-steps
                                     (division-public-boxed-start nil views allocation world)))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-public-boxed-prefix-steps division-public-boxed-prefix-ready-p
                               division-public-boxed-start)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-boxed-gcd-packing-start (plans a b world)
  (proof-advance (division-boxed-gcd-loop-steps plans a b world) world))

(defun division-boxed-gcd-call-ready-p (plans a b pack-steps entry world objects packages)
  (let* ((after (division-boxed-gcd-packing-start plans a b world))
         (value (division-gcd-magnitude a b))
         (count (division-result-view-count (proof-world-reg 0 after) after))
         (cuts (list (proof-world-reg 30 entry))))
    (and (integerp a) (natp b)
         (division-boxed-gcd-loop-ready-p plans a b world)
         (division-before-cuts-p (division-boxed-gcd-loop-steps plans a b world) cuts world)
         (division-boxed-finish-ready-p entry value count pack-steps after objects packages))))

(defun division-boxed-gcd-call-steps (plans a b pack-steps world)
  (+ (division-boxed-gcd-loop-steps plans a b world) (division-boxed-finish-steps pack-steps)))

(defthm division-boxed-gcd-returns-from-loop
  (let* ((steps (division-boxed-gcd-call-steps plans a b pack-steps world))
         (after (proof-advance steps world))
         (value (division-gcd-magnitude a b))
         (cuts (list (proof-world-reg 30 entry))))
    (implies (division-boxed-gcd-call-ready-p plans a b pack-steps entry world objects packages)
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-gcd-p a b value)
                  (proof-reg-value-p 0 value after objects packages)
                  (implies (proof-immediate-integer-p value)
                           (equal (proof-world-reg 0 after) (proof-integer-word value))))))
  :hints (("Goal"
           :use ((:instance division-boxed-gcd-loop-computes-natural-view)
                 (:instance division-gcd-magnitude-satisfies-contract)
                 (:instance division-boxed-finishes-through-pack
                            (value (division-gcd-magnitude a b))
                            (count (division-result-view-count
                                    (proof-world-reg 0 (division-boxed-gcd-packing-start plans a b world))
                                    (division-boxed-gcd-packing-start plans a b world)))
                            (world (division-boxed-gcd-packing-start plans a b world)))
                 (:instance division-return-after-checked-prefix
                            (prefix (division-boxed-gcd-loop-steps plans a b world))
                            (suffix (division-boxed-finish-steps pack-steps))
                            (cuts (list (proof-world-reg 30 entry)))))
           :in-theory (disable division-result-view-count division-boxed-finish-steps)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-public-boxed-gcd-loop-start (a-count b-count views allocation world)
  (proof-advance (division-gcd-copy-steps a-count b-count)
                 (division-public-boxed-start t views allocation world)))

(defun division-public-boxed-gcd-prefix-steps (a-count b-count views allocation world)
  (+ (division-public-boxed-prefix-steps t views allocation world) (division-gcd-copy-steps a-count b-count)))

(local
 (defthm division-gcd-copy-steps-natural
   (natp (division-gcd-copy-steps a-count b-count))
   :hints (("Goal" :in-theory (enable division-gcd-copy-steps)))
   :rule-classes :type-prescription))

(local
 (defthm division-public-boxed-gcd-prefix-reaches-loop
   (let* ((body (division-public-boxed-start t views allocation world))
          (steps (division-public-boxed-gcd-prefix-steps a-count b-count views allocation world))
          (cuts (list (proof-world-reg 30 world))))
     (implies (and (division-public-boxed-prefix-ready-p t a b a-count b-count views allocation world
                                                          old-objects new-objects packages)
                   (division-before-cuts-p (division-gcd-copy-steps a-count b-count) cuts body))
              (and (equal (proof-advance steps world)
                          (division-public-boxed-gcd-loop-start a-count b-count views allocation world))
                   (division-before-cuts-p steps cuts world))))
   :hints (("Goal"
            :use ((:instance division-public-boxed-prefix-advances (gcd t))
                  (:instance proof-advance-append
                             (prefix (division-public-boxed-prefix-steps t views allocation world))
                             (suffix (division-gcd-copy-steps a-count b-count)))
                  (:instance division-before-cuts-append
                             (prefix (division-public-boxed-prefix-steps t views allocation world))
                             (suffix (division-gcd-copy-steps a-count b-count))
                             (cuts (list (proof-world-reg 30 world)))))
            :in-theory (disable division-public-boxed-prefix-ready-p division-public-boxed-start
                                division-public-boxed-prefix-steps proof-advance-append division-before-cuts-append)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-public-boxed-prefix-has-positive-divisor
   (implies (division-public-boxed-prefix-ready-p gcd a b a-count b-count views allocation world
                                                old-objects new-objects packages)
            (posp b))
   :hints (("Goal"
            :in-theory (enable division-public-boxed-prefix-ready-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-public-boxed-gcd-returns
  (let* ((body (division-public-boxed-start t views allocation world))
         (loop (division-public-boxed-gcd-loop-start a-count b-count views allocation world))
         (prefix (division-public-boxed-gcd-prefix-steps a-count b-count views allocation world))
         (suffix (division-boxed-gcd-call-steps plans a b pack-steps loop))
         (steps (+ prefix suffix))
         (after (proof-advance steps world))
         (value (division-gcd-magnitude a b))
         (cuts (list (proof-world-reg 30 world))))
    (implies (and (division-public-boxed-prefix-ready-p t a b a-count b-count views allocation world
                                                         old-objects new-objects packages)
                  (division-gcd-copies-ready-p a b a-count b-count body)
                  (division-before-cuts-p (division-gcd-copy-steps a-count b-count) cuts body)
                  (division-boxed-gcd-call-ready-p plans a b pack-steps world loop new-objects packages))
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-gcd-p a b value)
                  (proof-reg-value-p 0 value after new-objects packages)
                  (implies (equal a 0) (proof-reg-value-p 0 b after new-objects packages))
                  (implies (proof-immediate-integer-p value)
                           (equal (proof-world-reg 0 after) (proof-integer-word value))))))
  :hints (("Goal"
           :use ((:instance division-public-boxed-gcd-prefix-reaches-loop)
                 (:instance division-public-boxed-prefix-has-positive-divisor (gcd t))
                 (:instance division-gcd-contract-at-zero-first (gcd (division-gcd-magnitude a b)))
                 (:instance division-boxed-gcd-returns-from-loop
                            (entry world) (objects new-objects)
                            (world (division-public-boxed-gcd-loop-start a-count b-count views allocation world)))
                 (:instance division-return-after-checked-prefix
                            (prefix (division-public-boxed-gcd-prefix-steps a-count b-count views allocation world))
                            (suffix (division-boxed-gcd-call-steps
                                     plans a b pack-steps (division-public-boxed-gcd-loop-start
                                                           a-count b-count views allocation world)))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-boxed-gcd-call-ready-p division-boxed-gcd-call-steps division-gcd-copies-ready-p
                               division-public-boxed-prefix-ready-p division-public-boxed-start
                               division-public-boxed-gcd-prefix-steps division-public-boxed-gcd-loop-start)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
