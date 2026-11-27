(in-package "BOYMOO-PROOFS")

(include-book "correction-loops")
(include-book "one-limb-loop")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defthm division-window-len-positive
   (implies (consp digits) (< 0 (len digits)))
   :hints (("Goal" :expand ((len digits))))
   :rule-classes :linear))

(defthm division-read-after-disjoint-window-writes
  (implies (and (proof-span-p address (* 8 (len digits)))
                (proof-span-p query size)
                (proof-disjoint-p address (+ address (* 8 (len digits))) query (+ query size)))
           (equal (boymoo-model::a64-read-bytes
                   size query (division-write-window-limbs digits address memory))
                  (boymoo-model::a64-read-bytes size query memory)))
  :hints (("Goal" :induct (division-write-window-limbs digits address memory))
          ("Subgoal *1/2" :cases ((consp (cdr digits))))))

(defthm division-load-word-after-window-writes
  (implies (and (proof-span-p address (* 8 (len digits)))
                (proof-span-p query 8)
                (proof-disjoint-p address (+ address (* 8 (len digits))) query (+ query 8))
                (equal (boymoo-model::a64-memory after)
                       (division-write-window-limbs digits address (boymoo-model::a64-memory before))))
           (equal (proof-load-word query after) (proof-load-word query before)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-memory division-write-window-limbs)))
  :rule-classes nil)

(local
 (defthm division-empty-window-writes
   (implies (atom digits) (equal (division-write-window-limbs digits address memory) memory))
   :hints (("Goal" :expand ((division-write-window-limbs digits address memory))))))

(local
 (defthm division-window-load-first-written-limb
   (implies (and (consp digits)
                 (proof-span-p address (* 8 (len digits)))
                 (division-digit-p (car digits)))
            (equal (boymoo-model::a64-read-bytes
                    8 address (division-write-window-limbs digits address memory))
                   (car digits)))
   :hints (("Goal" :cases ((consp (cdr digits)))
                   :expand ((division-write-window-limbs digits address memory))))))

(local
 (defthm division-window-read-zero-limbs
   (equal (division-read-limbs 0 address machine) nil)
   :hints (("Goal" :expand ((division-read-limbs 0 address machine))))))

(local
 (defthm division-window-read-positive-count
   (implies (posp count)
            (equal (division-read-limbs count address machine)
                   (cons (proof-load-word address machine)
                         (division-read-limbs (1- count) (+ 8 address) machine))))
   :hints (("Goal" :expand ((division-read-limbs count address machine))))
   :rule-classes nil))

(local
 (defthm division-window-read-just-written-limbs
   (implies (and (division-digits-p digits) (proof-span-p address (* 8 (len digits))))
            (equal (division-read-limbs
                    (len digits) address
                    (list nil nil nil nil (division-write-window-limbs digits address memory)))
                   digits))
   :hints (("Goal"
            :induct (division-write-window-limbs digits address memory)
            :in-theory (disable division-read-limbs (:definition division-write-window-limbs)))
           ("Subgoal *1/2"
            :cases ((consp (cdr digits)))
            :use ((:instance division-window-read-positive-count
                             (count (len digits))
                             (machine (list nil nil nil nil (division-write-window-limbs digits address memory))))
                  (:instance division-window-load-first-written-limb))
            :expand ((division-write-window-limbs digits address memory))))
   :rule-classes nil))

(defthm division-read-window-limb-writes
  (implies (and (division-digits-p digits) (proof-span-p address (* 8 (len digits)))
                (equal (boymoo-model::a64-memory after)
                       (division-write-window-limbs digits address (boymoo-model::a64-memory before))))
           (equal (division-read-limbs (len digits) address after) digits))
  :hints (("Goal"
           :use ((:instance division-window-read-just-written-limbs (memory (boymoo-model::a64-memory before)))
                 (:instance division-read-limbs-from-same-memory
                            (first after)
                            (second (list nil nil nil nil
                                          (division-write-window-limbs digits address
                                                                       (boymoo-model::a64-memory before))))
                            (count (len digits))))
           :in-theory (disable division-read-limbs division-write-window-limbs)))
  :rule-classes nil)

(defthm division-limbs-after-disjoint-word-write
  (implies (and (natp count) (proof-span-p address (* 8 count))
                (proof-span-p target 8)
                (proof-disjoint-p address (+ address (* 8 count)) target (+ target 8))
                (equal (boymoo-model::a64-memory after)
                       (boymoo-model::a64-write-bytes 8 target value (boymoo-model::a64-memory before))))
           (equal (division-read-limbs count address after)
                  (division-read-limbs count address before)))
  :hints (("Goal"
           :use ((:instance division-read-limbs-after-disjoint-store
                            (bytes 8) (machine before))
                 (:instance division-read-limbs-from-same-memory
                            (first after) (second (boymoo-model::a64-store 8 target value before))))
           :in-theory (disable division-read-limbs)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-limbs-after-disjoint-window-writes
  (implies (and (natp count) (proof-span-p address (* 8 count))
                (proof-span-p target (* 8 (len written)))
                (proof-disjoint-p address (+ address (* 8 count)) target (+ target (* 8 (len written))))
                (equal (boymoo-model::a64-memory after)
                       (division-write-window-limbs written target (boymoo-model::a64-memory before))))
           (equal (division-read-limbs count address after)
                  (division-read-limbs count address before)))
  :hints (("Goal"
           :induct (division-read-limbs count address before)
           :in-theory (disable division-write-window-limbs boymoo-model::a64-memory proof-load-word))
          ("Subgoal *1/2"
           :use (:instance division-load-word-after-window-writes
                           (address target) (query address) (digits written))
           :cases ((equal count 1))
           :expand ((division-read-limbs count address after))))
  :rule-classes nil)
