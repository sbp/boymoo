(in-package "BOYMOO-PROOFS")

(include-book "view-frame")
(include-book "window-memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash proof-world-machine proof-load-word
                     boymoo-model::a64-memory boymoo-model::a64-read-bytes
                     boymoo-model::a64-write-bytes)))

(defthm division-load-word-after-disjoint-written-word
  (implies (and (proof-span-p address 8) (proof-span-p target 8)
                (proof-disjoint-p address (+ 8 address) target (+ 8 target))
                (equal (boymoo-model::a64-memory after)
                       (boymoo-model::a64-write-bytes 8 target word (boymoo-model::a64-memory before))))
           (equal (proof-load-word address after) (proof-load-word address before)))
  :hints (("Goal" :in-theory (enable proof-load-word)))
  :rule-classes nil)

(local
 (defthm division-view-read-none
   (equal (division-read-limbs 0 address machine) nil)
   :hints (("Goal" :expand ((division-read-limbs 0 address machine))))))

(defthm division-view-after-disjoint-word-write
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after))
        (bytes (division-view-bytes count)))
    (implies (and (proof-integer-view-p value address count before)
                  (proof-span-p address bytes) (proof-span-p target 8)
                  (proof-disjoint-p address (+ address bytes) target (+ target 8))
                  (equal (boymoo-model::a64-memory last)
                         (boymoo-model::a64-write-bytes 8 target word (boymoo-model::a64-memory first))))
             (proof-integer-view-p value address count after)))
  :hints (("Goal"
           :cases ((equal count 0))
           :use ((:instance division-view-value-determined-by-words)
                 (:instance division-load-word-after-disjoint-written-word
                            (before (proof-world-machine before)) (after (proof-world-machine after)))
                 (:instance division-load-word-after-disjoint-written-word
                            (address (+ 8 address))
                            (before (proof-world-machine before)) (after (proof-world-machine after)))
                 (:instance division-limbs-after-disjoint-word-write
                            (value word) (address (+ 16 address))
                            (before (proof-world-machine before)) (after (proof-world-machine after))))
           :in-theory (disable proof-integer-view division-read-limbs)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-view-load-at-written-word
   (implies (and (proof-span-p target 8) (unsigned-byte-p 64 word)
                 (equal (boymoo-model::a64-memory after)
                        (boymoo-model::a64-write-bytes 8 target word (boymoo-model::a64-memory before))))
            (equal (proof-load-word target after) word))
   :hints (("Goal" :in-theory (enable proof-load-word)))
   :rule-classes nil))

(local
 (defthm division-view-header-type-from-count
   (implies (natp count)
            (equal (proof-header-type (+ 3 (* 2048 (1+ count)))) 3))
   :hints (("Goal"
            :use ((:instance division-a64-unsigned-is-remainder (width 8) (x (+ 3 (* 2048 (1+ count)))))
                  (:instance division-remainder-unique
                             (a (+ 3 (* 2048 (1+ count)))) (b 256) (q (* 8 (1+ count))) (r 3)))
            :in-theory (disable boymoo-model::a64-unsigned)))))

(defthm division-view-from-normalized-words
  (let* ((machine (proof-world-machine world))
         (digits (division-read-limbs count (+ 16 address) machine))
         (sign (proof-load-word (+ 8 address) machine))
         (magnitude (division-magnitude digits)))
    (implies (and (natp count)
                  (equal (proof-load-word address machine) (+ 3 (* 2048 (1+ count))))
                  (proof-span-p address (division-view-bytes count))
                  (division-normalized-limbs-p digits)
                  (or (equal sign 0) (and (equal sign 1) (posp count))))
             (proof-integer-view-p (if (equal sign 0) magnitude (- magnitude)) address count world)))
  :hints (("Goal"
           :use ((:instance division-view-header-byte-count)
                 (:instance division-view-header-type-from-count)
                 (:instance division-read-limbs-view-magnitude
                            (address (+ 16 address)) (machine (proof-world-machine world)))
                 (:instance division-read-limbs-normalized
                            (address (+ 16 address)) (machine (proof-world-machine world)))
                 (:instance division-remainder-unique
                            (a (* 8 (1+ count))) (b 8) (q (1+ count)) (r 0)))
           :in-theory (disable proof-header-size proof-header-type division-read-limbs proof-limbs-p proof-limb-magnitude
                               division-read-limbs-normalized division-view-header-type-from-count)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-view-after-writing-sign
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (target (+ 8 address)))
    (implies (and (proof-integer-view-p value address count before)
                  (or (equal sign 0) (and (equal sign 1) (posp count)))
                  (proof-span-p address (division-view-bytes count))
                  (equal (boymoo-model::a64-memory last)
                         (boymoo-model::a64-write-bytes 8 target sign (boymoo-model::a64-memory first))))
             (proof-integer-view-p (if (equal sign 0) (abs value) (- (abs value))) address count after)))
  :hints (("Goal"
           :cases ((equal count 0))
           :use ((:instance division-view-magnitude-and-count (world before))
                 (:instance division-view-from-normalized-words (world after))
                 (:instance division-load-word-after-disjoint-written-word
                            (before (proof-world-machine before)) (after (proof-world-machine after))
                            (word sign) (target (+ 8 address)))
                 (:instance division-view-load-at-written-word
                            (before (proof-world-machine before)) (after (proof-world-machine after))
                            (word sign) (target (+ 8 address)))
                 (:instance division-limbs-after-disjoint-word-write
                            (value sign) (address (+ 16 address)) (target (+ 8 address))
                            (before (proof-world-machine before)) (after (proof-world-machine after))))
           :in-theory (disable proof-integer-view division-read-limbs division-read-limbs-normalized
                               division-normalized-limbs-p division-magnitude division-read-limbs-view-magnitude)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-view-sign-and-limbs
  (let* ((machine (proof-world-machine world))
         (digits (division-read-limbs count (+ 16 address) machine))
         (sign (proof-load-word (+ 8 address) machine))
         (magnitude (division-magnitude digits)))
    (implies (proof-integer-view-p value address count world)
             (and (natp count)
                  (equal (proof-load-word address machine) (+ 3 (* 2048 (1+ count))))
                  (division-normalized-limbs-p digits)
                  (or (equal sign 0) (and (equal sign 1) (posp count)))
                  (equal value (if (equal sign 0) magnitude (- magnitude))))))
  :hints (("Goal"
           :use ((:instance division-view-header-byte-count)
                 (:instance division-read-limbs-view-magnitude
                            (address (+ 16 address)) (machine (proof-world-machine world))))
           :in-theory (disable proof-header-size proof-header-type division-read-limbs proof-limbs-p
                               proof-limb-magnitude)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
