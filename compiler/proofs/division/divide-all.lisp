(in-package "BOYMOO-PROOFS")

(include-book "short")
(include-book "divide-correctness")
(include-book "divide-long")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable abs floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-short-call-steps division-one-call-steps division-long-call-steps
                     division-short-call-ready-p division-one-call-ready-p division-long-call-ready-p
                     proof-integer-view-p division-trim-limbs boymoo-model::a64-sp)))

(defun division-result-view-count (address world)
  (1- (floor (proof-load-word address (proof-world-machine world)) 2048)))

(defthm division-view-count-after-header
  (implies (proof-integer-view-p value address count world)
           (equal (division-result-view-count address world) count))
  :hints (("Goal"
           :use (:instance division-quotient-unique
                           (a (+ 3 (* 2048 (1+ count)))) (b 2048) (q (1+ count)) (r 3))
           :in-theory (e/d (proof-integer-view-p) (proof-integer-view))
           :do-not-induct t))
  :rule-classes nil)

(defun division-unsigned-ready-p (a b a-count b-count q-steps r-steps world)
  (and (integerp a) (integerp b) (not (equal b 0))
       (cond ((< a-count b-count)
              (division-short-call-ready-p a b a-count b-count q-steps r-steps world))
             ((equal b-count 1)
              (division-one-call-ready-p a b a-count q-steps r-steps world))
             (t (division-long-call-ready-p a b a-count b-count q-steps r-steps world)))))

(defun division-unsigned-steps (a-count b-count q-steps r-steps world)
  (cond ((< a-count b-count) (division-short-call-steps a-count q-steps r-steps))
        ((equal b-count 1) (division-one-call-steps a-count q-steps r-steps))
        (t (division-long-call-steps a-count b-count q-steps r-steps world))))

(defun division-unsigned-result-p (a b before after)
  (let ((quotient (proof-world-reg 2 before))
        (remainder (proof-world-reg 3 before)))
    (and (proof-integer-view-p (floor (abs a) (abs b)) quotient (division-result-view-count quotient after) after)
         (proof-integer-view-p (mod (abs a) (abs b)) remainder (division-result-view-count remainder after) after)
         (equal (proof-world-reg 0 after) remainder)
         (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 before))
         (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
         (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp (proof-world-machine before))))))

(local
 (defthm division-result-view-at-read-count
   (implies (proof-integer-view-p value address count world)
            (proof-integer-view-p value address (division-result-view-count address world) world))
   :hints (("Goal"
            :use (:instance division-view-count-after-header)
            :in-theory (disable division-result-view-count)
            :do-not-induct t))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((proof-integer-view-p value address count world))))))

(defthm division-unsigned-entry-to-return
  (let* ((steps (division-unsigned-steps a-count b-count q-steps r-steps world))
         (after (proof-advance steps world)))
    (implies (division-unsigned-ready-p a b a-count b-count q-steps r-steps world)
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (division-unsigned-result-p a b world after))))
  :hints (("Goal"
           :use ((:instance division-one-limb-entry-to-return (count a-count))
                 (:instance division-short-entry-to-return)
                 (:instance division-multi-limb-entry-to-return))
           :in-theory (disable division-result-view-count division-one-call-raw division-one-call-quotient
                               division-one-call-remainder division-short-call-remainder division-short-call-raw
                               division-long-finish-raw division-long-call-first-position
                               division-long-call-scaled-divisor division-long-quotient division-long-remainder)
           :cases ((< a-count b-count) (equal b-count 1))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
