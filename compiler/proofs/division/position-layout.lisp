(in-package "BOYMOO-PROOFS")

(include-book "long-iteration")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word
                     division-position-estimate-ready-p division-position-write-ready-p
                     division-position-subtraction-start division-position-iteration-counts
                     division-step-sum)))

(local
 (defun division-digit-split-induct (count digits)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       digits
     (division-digit-split-induct (1- count) (cdr digits)))))

(defthm division-magnitude-split
  (implies (and (natp count) (<= count (len digits)))
           (equal (division-magnitude digits)
                  (+ (division-magnitude (take count digits))
                     (* (division-place-value count)
                        (division-magnitude (nthcdr count digits))))))
  :hints (("Goal" :induct (division-digit-split-induct count digits))
          ("Subgoal *1/2" :cases ((consp digits))))
  :rule-classes nil)

(local
 (defthm division-take-keeps-words
   (implies (and (division-digits-p digits) (natp count) (<= count (len digits)))
            (and (equal (len (take count digits)) count)
                 (division-digits-p (take count digits))))
   :hints (("Goal" :induct (division-digit-split-induct count digits)))))

(local
 (defthm division-limb-at-index-fits
   (implies (and (division-digits-p digits) (natp index) (< index (len digits)))
            (division-digit-p (nth index digits)))
   :hints (("Goal" :induct (division-digit-split-induct index digits)))))

(local
 (defthm division-digits-are-a-true-list
   (implies (division-digits-p digits) (true-listp digits))
   :hints (("Goal" :induct (division-digits-p digits)))))

(local
 (defthm division-last-two-limbs
   (implies (and (true-listp digits) (natp count) (equal (len digits) (+ 2 count)))
            (equal (nthcdr count digits)
                   (list (nth count digits) (nth (1+ count) digits))))
   :hints (("Goal" :induct (division-digit-split-induct count digits))
           ("Subgoal *1/1" :cases ((consp digits) (consp (cdr digits)) (consp (cddr digits)))))
   :rule-classes nil))

(local
 (defthm division-leading-is-last-index
   (implies (and (division-digits-p digits) (consp digits))
            (equal (division-leading-limb digits) (nth (1- (len digits)) digits)))
   :hints (("Goal" :induct (division-leading-limb digits))
           ("Subgoal *1/2" :expand ((nth (1- (len digits)) digits))))))

(defthm division-position-place-positive
  (posp (division-place-value count))
  :rule-classes :type-prescription)

(defthm division-radix-magnitude-is-natural
  (natp (division-magnitude digits))
  :rule-classes :type-prescription)

(local
 (defthm division-place-value-for-window
   (implies (natp count)
            (equal (division-place-value (+ 2 count))
                   (* *division-radix* *division-radix* (division-place-value count))))
   :hints (("Goal" :expand ((division-place-value (+ 2 count))
                            (division-place-value (+ 1 count)))))))

(local
 (defthm division-two-limb-list-value
   (implies (and (division-digit-p low) (division-digit-p high))
            (equal (division-magnitude (list low high)) (+ low (* *division-radix* high))))))

(local
 (defthm division-window-has-prefix-value
   (implies (and (division-digits-p digits) (natp count) (equal (len digits) (+ 2 count)))
            (equal (division-window-magnitude digits high)
                   (division-prefix-value
                    (+ (nth count digits)
                       (* *division-radix* (nth (1+ count) digits))
                       (* *division-radix* *division-radix* high))
                    (division-magnitude (take count digits)) (division-place-value count))))
   :hints (("Goal"
            :use ((:instance division-magnitude-split)
                  (:instance division-last-two-limbs)
                  (:instance division-limb-at-index-fits (index count))
                  (:instance division-limb-at-index-fits (index (1+ count)))
                  (:instance division-two-limb-list-value
                             (low (nth count digits)) (high (nth (1+ count) digits))))
            :in-theory (disable division-magnitude division-place-value nthcdr take
                                (:definition nth) division-two-limb-list-value)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defun division-read-index-induct (index count address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count address)
     (division-read-index-induct (1- index) (1- count) (+ 8 address)))))

(defthm division-limb-read-at-index
  (implies (and (natp index) (natp count) (< index count) (acl2-numberp address))
           (equal (nth index (division-read-limbs count address machine))
                  (proof-load-word (+ address (* 8 index)) machine)))
  :hints (("Goal" :induct (division-read-index-induct index count address)
                  :do-not '(generalize fertilize)
                  :in-theory (disable division-read-limbs))
          ("Subgoal *1/1" :expand ((division-read-limbs count address machine)))
          ("Subgoal *1/2"
           :expand ((division-read-limbs count address machine) (nth index (division-read-limbs count address machine)))))
  :rule-classes nil)

(defun division-position-digits (divisor world)
  (division-read-limbs (len divisor) (division-position-window world) (proof-world-machine world)))

(defun division-position-value (divisor world)
  (division-window-magnitude (division-position-digits divisor world) (division-position-word 0 world)))

(defthm division-position-value-is-integer
  (integerp (division-position-value divisor world))
  :rule-classes :type-prescription)

(defun division-position-layout-p (divisor world)
  (let* ((count (len divisor))
         (digits (division-position-digits divisor world)))
    (and (<= 2 count)
         (division-digits-p divisor)
         (division-leading-digit-p (division-leading-limb divisor))
         (equal (proof-world-reg 22 world) (* 8 count))
         (equal (proof-world-reg 11 world) (division-leading-limb divisor))
         (equal (proof-world-reg 12 world) (nth (- count 2) divisor))
         (division-digits-p digits)
         (division-digit-p (division-position-word 0 world)))))

(defun division-position-geometry-p (divisor world)
  (and (division-position-layout-p divisor world)
       (< (division-position-value divisor world) (* *division-radix* (division-magnitude divisor)))))

(local
 (defthm division-position-reads-leading-pair
   (let* ((count (len divisor))
          (digits (division-position-digits divisor world)))
     (implies (division-position-geometry-p divisor world)
              (and (equal (division-position-word 8 world) (nth (1- count) digits))
                   (equal (division-position-word 16 world) (nth (- count 2) digits)))))
   :hints (("Goal"
            :use ((:instance division-limb-read-at-index
                             (index (1- (len divisor))) (count (len divisor))
                             (address (division-position-window world)) (machine (proof-world-machine world)))
                  (:instance division-limb-read-at-index
                             (index (- (len divisor) 2)) (count (len divisor))
                             (address (division-position-window world)) (machine (proof-world-machine world))))
            :in-theory (disable division-position-window division-position-value division-read-limbs
                                division-digits-p division-leading-digit-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-position-has-normalized-prefixes
   (let* ((count (- (len divisor) 2))
          (digits (division-position-digits divisor world))
          (head (division-position-head world))
          (digit (division-position-word 16 world))
          (lead (proof-world-reg 11 world))
          (next (proof-world-reg 12 world))
          (a-tail (division-magnitude (take count digits)))
          (b-tail (division-magnitude (take count divisor)))
          (scale (division-place-value count)))
     (implies (division-position-geometry-p divisor world)
              (and (division-window-p head lead next digit a-tail b-tail scale)
                   (equal (division-position-value divisor world)
                          (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale))
                   (equal (division-magnitude divisor)
                          (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))))
   :hints (("Goal"
            :use ((:instance division-position-reads-leading-pair)
                  (:instance division-leading-is-last-index (digits divisor))
                  (:instance division-limb-at-index-fits (index (- (len divisor) 2)) (digits divisor))
                  (:instance division-limb-at-index-fits (index (- (len divisor) 2))
                             (digits (division-position-digits divisor world)))
                  (:instance division-limb-at-index-fits (index (1- (len divisor)))
                             (digits (division-position-digits divisor world)))
                  (:instance division-window-has-prefix-value
                             (count (- (len divisor) 2)) (high 0) (digits divisor))
                  (:instance division-window-has-prefix-value
                             (count (- (len divisor) 2)) (high (division-position-word 0 world))
                             (digits (division-position-digits divisor world)))
                  (:instance division-two-limb-word-fits
                             (low (division-position-word 8 world)) (high (division-position-word 0 world)))
                  (:instance division-magnitude-bound (digits (take (- (len divisor) 2) divisor)))
                  (:instance division-magnitude-bound
                             (digits (take (- (len divisor) 2) (division-position-digits divisor world)))))
            :in-theory (disable division-position-word division-read-limbs
                                division-digits-p division-place-value division-magnitude
                                division-leading-limb division-leading-digit-p division-limb-at-index-fits
                                division-leading-is-last-index
                                (:definition take) (:definition nth))
            :cases ((consp divisor))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-position-steps (divisor world)
  (division-step-sum
   (division-position-iteration-counts (division-position-digits divisor world) divisor world)))

(defun division-position-after (divisor world)
  (proof-advance (division-position-steps divisor world) world))

(defun division-position-machine-ready-p (divisor world)
  (and (division-position-estimate-ready-p world)
       (division-position-write-ready-p
        (division-position-digits divisor world) divisor (division-position-subtraction-start world))))

(defthm division-position-from-memory
  (let* ((after (division-position-after divisor world))
         (base (division-position-window world))
         (offset (proof-world-reg 13 world))
         (machine (proof-world-machine after))
         (q (proof-load-word (+ (proof-world-reg 21 world) offset) machine))
         (r-digits (division-read-limbs (len divisor) base machine))
         (b (division-magnitude divisor))
         (r (division-magnitude r-digits)))
    (implies (and (division-position-geometry-p divisor world)
                  (division-position-machine-ready-p divisor world))
             (and (division-digit-p q)
                  (division-digits-p r-digits)
                  (< r b)
                  (equal (+ (* b q) r) (division-position-value divisor world))
                  (equal (proof-load-word (+ base (* 8 (len divisor))) machine) 0)
                  (equal (proof-world-reg 13 after) (boymoo-model::a64-unsigned 64 (- offset 8)))
                  (equal (proof-world-pc after)
                         (if (<= 8 offset) (proof-world-pc world) (+ 252 (proof-world-pc world)))))))
  :hints (("Goal"
           :use ((:instance division-position-has-normalized-prefixes)
                 (:instance division-one-normalized-position-executes
                            (digits (division-position-digits divisor world))
                            (a-tail (division-magnitude (take (- (len divisor) 2)
                                                             (division-position-digits divisor world))))
                            (b-tail (division-magnitude (take (- (len divisor) 2) divisor)))
                            (scale (division-place-value (- (len divisor) 2)))))
           :in-theory (disable division-position-geometry-p division-position-word division-position-head
                               division-digits-p division-magnitude division-prefix-value division-window-p
                               division-window-magnitude division-read-limbs division-place-value
                               (:definition take))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
