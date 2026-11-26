(in-package "BOYMOO-PROOFS")

(include-book "equality-views")
(include-book "byte-views")

(logic)
(set-verify-guards-eagerness 0)

(defconst *p6-limb-radix* (expt 2 32))

(local
 (defthm p6-word-natural-for-limbs
   (natp (proof-load-word address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-load-word boymoo-model::a64-load)))))

(defthm p6-limb-magnitude-natural
  (natp (proof-limb-magnitude count address machine))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (proof-limb-magnitude count address machine))))

(defthm p6-limb-magnitude-low-and-high
  (implies (and (posp count) (proof-limbs-p count address machine))
           (and (equal (mod (proof-limb-magnitude count address machine) *p6-limb-radix*)
                       (proof-load-word address machine))
                (equal (floor (proof-limb-magnitude count address machine) *p6-limb-radix*)
                       (proof-limb-magnitude (1- count) (+ 8 address) machine))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-limbs-p)
                  :expand ((proof-limb-magnitude count address machine))
                  :use ((:instance p6-floor-mod-of-scaled-sum
                                   (d *p6-limb-radix*) (lo (proof-load-word address machine))
                                   (n (proof-limb-magnitude (1- count) (+ 8 address) machine)))))))

(local
 (defthm p6-limb-magnitude-at-zero
   (implies (zp count) (equal (proof-limb-magnitude count address machine) 0))
   :hints (("Goal" :expand ((proof-limb-magnitude count address machine))))))

(local
 (defthm p6-first-eight-bytes-are-a-fixed-prefix
   (equal (equal (append (proof-byte-list 8 left first) tail-a)
                 (append (proof-byte-list 8 right second) tail-b))
          (and (equal (proof-byte-list 8 left first) (proof-byte-list 8 right second))
               (equal tail-a tail-b)))
   :hints (("Goal" :in-theory (enable proof-byte-list)))))

(local
 (defun p6-limb-spans-induction (count left right)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons left right)
     (p6-limb-spans-induction (1- count) (+ 8 left) (+ 8 right)))))

(defthm p6-normalized-limbs-equal-by-declared-bytes
  (implies (and (natp count) (integerp left) (integerp right)
                (proof-limbs-p count left first) (proof-limbs-p count right second))
           (equal (equal (proof-limb-magnitude count left first) (proof-limb-magnitude count right second))
                  (equal (proof-byte-list (* 8 count) left first) (proof-byte-list (* 8 count) right second))))
  :rule-classes nil
  :hints (("Goal" :induct (p6-limb-spans-induction count left right)
                  :in-theory (e/d (proof-limbs-p proof-load-word)
                                  (proof-limb-magnitude p6-byte-list-step
                                   p6-load-equality-is-byte-list-equality)))
          ("Subgoal *1/2"
           :expand ((proof-limb-magnitude count left first)
                    (proof-limb-magnitude count right second))
           :use ((:instance p6-limb-magnitude-low-and-high (address left) (machine first))
                 (:instance p6-limb-magnitude-low-and-high (address right) (machine second))
                 (:instance p6-load-equality-is-byte-list-equality (count 8))
                 (:instance p6-byte-list-split (prefix 8) (suffix (* 8 (1- count)))
                            (address left) (machine first))
                 (:instance p6-byte-list-split (prefix 8) (suffix (* 8 (1- count)))
                            (address right) (machine second))))))

(local
 (defthm p6-limb-power-is-positive
   (implies (natp count) (posp (expt *p6-limb-radix* count)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (expt *p6-limb-radix* count) :in-theory (enable expt)))))

(local
 (defthm p6-strict-integer-bound
   (implies (and (integerp a) (integerp b) (< a b))
            (<= a (1- b)))))

(defthm p6-limb-magnitude-bounds
  (implies (and (natp count) (proof-limbs-p count address machine))
           (and (< (proof-limb-magnitude count address machine) (expt *p6-limb-radix* count))
                (implies (posp count)
                         (<= (expt *p6-limb-radix* (1- count))
                             (proof-limb-magnitude count address machine)))))
  :rule-classes nil
  :hints (("Goal"
           :induct (proof-limb-magnitude count address machine)
           :in-theory (enable proof-limbs-p (:induction proof-limb-magnitude))
           :expand ((proof-limb-magnitude count address machine) (expt *p6-limb-radix* count)))
          ("Subgoal *1/2" :cases ((<= count 1))
           :use ((:instance p6-strict-integer-bound
                            (a (proof-limb-magnitude (1- count) (+ 8 address) machine))
                            (b (expt *p6-limb-radix* (1- count))))
                 (:instance p6-limb-power-is-positive (count (- count 2))))
           :expand ((expt *p6-limb-radix* count) (expt *p6-limb-radix* (1- count))))))

(local
 (defthm p6-limb-power-step
   (implies (posp count)
            (equal (expt *p6-limb-radix* count)
                   (* *p6-limb-radix* (expt *p6-limb-radix* (1- count)))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt *p6-limb-radix* count))))))

(local
 (defthm p6-limb-power-nondecreasing
   (implies (and (natp a) (natp b) (<= a b))
            (<= (expt *p6-limb-radix* a) (expt *p6-limb-radix* b)))
   :rule-classes nil
   :hints (("Goal" :induct (expt *p6-limb-radix* b)
                   :in-theory (enable (:induction expt)))
           ("Subgoal *1/3" :cases ((<= a (1- b)))
            :use ((:instance p6-limb-power-step (count b)))))))

(defthm p6-normalized-limb-count-is-unique
  (implies (and (natp count-a) (natp count-b)
                (proof-limbs-p count-a left first) (proof-limbs-p count-b right second)
                (equal (proof-limb-magnitude count-a left first) (proof-limb-magnitude count-b right second)))
           (equal count-a count-b))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-limb-magnitude)
           :cases ((< count-a count-b) (< count-b count-a))
           :use ((:instance p6-limb-magnitude-bounds (count count-a) (address left) (machine first))
                 (:instance p6-limb-magnitude-bounds (count count-b) (address right) (machine second))
                 (:instance p6-limb-power-nondecreasing (a count-a) (b (1- count-b)))
                 (:instance p6-limb-power-nondecreasing (a count-b) (b (1- count-a)))))))

(defund p6-integer-limb-count (address machine)
  (1- (ash (proof-header-size (proof-load-word address machine)) -3)))

(defund p6-integer-sign (address machine)
  (proof-load-word (+ 8 address) machine))

(defthm p6-normalized-integer-fields
  (let* ((view (proof-integer-view address machine))
         (header (proof-load-word address machine))
         (count (p6-integer-limb-count address machine))
         (sign (p6-integer-sign address machine))
         (magnitude (proof-limb-magnitude count (+ address 16) machine)))
    (implies view
             (and (natp address) (natp count)
                  (equal (proof-header-size header) (* 8 (1+ count)))
                  (equal header (+ 3 (* 2048 (1+ count))))
                  (proof-limbs-p count (+ address 16) machine)
                  (or (equal sign 0) (and (equal sign 1) (posp count)))
                  (equal view (proof-value-view (if (equal sign 0) magnitude (- magnitude)))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-integer-view p6-integer-limb-count p6-integer-sign
                                               proof-span-p proof-header-type proof-header-size p6-unsigned-as-mod)
                           (proof-limb-magnitude proof-limbs-p p6-loaded-header-fields))
           :use ((:instance p6-mod-decomposition (x (proof-load-word address machine)) (d 256))
                 (:instance p6-mod-decomposition (x (ash (proof-load-word address machine) -8)) (d 8))
                 (:instance p6-floor-bounds (x (ash (proof-load-word address machine) -8)) (d 8))))))

(local
 (defthm p6-positive-length-magnitude-is-positive
   (implies (and (posp count) (proof-limbs-p count address machine))
            (< 0 (proof-limb-magnitude count address machine)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-limb-magnitude)
                   :use p6-limb-magnitude-bounds))))

(defthm p6-normalized-integers-equal-by-sign-and-limbs
  (let* ((view-a (proof-integer-view left first)) (view-b (proof-integer-view right second))
         (count-a (p6-integer-limb-count left first)) (count-b (p6-integer-limb-count right second))
         (sign-a (p6-integer-sign left first)) (sign-b (p6-integer-sign right second)))
    (implies (and view-a view-b)
             (equal (equal view-a view-b)
                    (and (equal sign-a sign-b) (equal count-a count-b)
                         (equal (proof-byte-list (* 8 count-a) (+ 16 left) first)
                                (proof-byte-list (* 8 count-b) (+ 16 right) second))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-integer-view proof-limb-magnitude proof-view-value)
           :use ((:instance p6-normalized-integer-fields (address left) (machine first))
                 (:instance p6-normalized-integer-fields (address right) (machine second))
                 (:instance p6-positive-length-magnitude-is-positive
                            (count (p6-integer-limb-count left first)) (address (+ 16 left)) (machine first))
                 (:instance p6-positive-length-magnitude-is-positive
                            (count (p6-integer-limb-count right second)) (address (+ 16 right)) (machine second))
                 (:instance p6-normalized-limb-count-is-unique
                            (count-a (p6-integer-limb-count left first)) (count-b (p6-integer-limb-count right second))
                            (left (+ 16 left)) (right (+ 16 right)))
                 (:instance p6-normalized-limbs-equal-by-declared-bytes
                            (count (p6-integer-limb-count left first)) (left (+ 16 left)) (right (+ 16 right)))))))

(defthm p6-boxed-integer-equality-by-header-and-payload
  (let* ((header-a (proof-load-word left first)) (header-b (proof-load-word right second))
         (view-a (proof-integer-view left first)) (view-b (proof-integer-view right second)))
    (implies (and view-a view-b)
             (equal (equal view-a view-b)
                    (and (equal header-a header-b)
                         (equal (proof-byte-list (proof-header-size header-a) (+ 8 left) first)
                                (proof-byte-list (proof-header-size header-b) (+ 8 right) second))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-integer-sign proof-load-word)
                           (proof-integer-view proof-limb-magnitude p6-loaded-header-fields p6-byte-list-step
                            p6-load-equality-is-byte-list-equality))
           :use (p6-normalized-integers-equal-by-sign-and-limbs
                 (:instance p6-normalized-integer-fields (address left) (machine first))
                 (:instance p6-normalized-integer-fields (address right) (machine second))
                 (:instance p6-byte-list-split (prefix 8) (suffix (* 8 (p6-integer-limb-count left first)))
                            (address (+ 8 left)) (machine first))
                 (:instance p6-byte-list-split (prefix 8) (suffix (* 8 (p6-integer-limb-count right second)))
                            (address (+ 8 right)) (machine second))
                 (:instance p6-load-equality-is-byte-list-equality (count 8) (left (+ 8 left)) (right (+ 8 right)))))))
