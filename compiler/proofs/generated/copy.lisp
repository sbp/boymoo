(in-package "BOYMOO-PROOFS")

(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-reg generated-load-word generated-store-word
                    proof-world-machine boymoo-model::a64-load boymoo-model::a64-store
                    boymoo-model::a64-unsigned expt))

(defun generated-word-block-span-p (start count)
  (and (natp start) (natp count) (<= (+ start (* 8 count)) (expt 2 64))))

(defund generated-read-words (count address world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (generated-load-word address world)
          (generated-read-words (1- count) (+ address 8) world))))

(defund generated-copy-words (count source destination world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      world
    (generated-copy-words
     (1- count) (+ 8 source) (+ 8 destination)
     (generated-store-word destination (generated-load-word source world) world))))

(defthm generated-word-block-unchanged-by-disjoint-store
  (implies (and (generated-word-block-span-p start count) (proof-span-p address 8)
                (proof-disjoint-p start (+ start (* 8 count)) address (+ 8 address)))
           (equal (generated-read-words count start (generated-store-word address value world))
                  (generated-read-words count start world)))
  :hints (("Goal" :induct (generated-read-words count start world)
                  :in-theory (enable generated-read-words))))

(defthm generated-word-outside-copied-destination
  (implies (and (generated-word-block-span-p destination count) (proof-span-p address 8)
                (proof-disjoint-p destination (+ destination (* 8 count)) address (+ 8 address)))
           (equal (generated-load-word address (generated-copy-words count source destination world))
                  (generated-load-word address world)))
  :hints (("Goal" :induct (generated-copy-words count source destination world)
                  :in-theory (enable generated-copy-words))))

(defthm generated-forward-copy-with-overlap
  (implies (and (generated-word-block-span-p source count)
                (generated-word-block-span-p destination count)
                (<= destination source))
           (equal (generated-read-words count destination
                                        (generated-copy-words count source destination world))
                  (generated-read-words count source world)))
  :hints (("Goal" :induct (generated-copy-words count source destination world)
                  :in-theory (enable generated-copy-words generated-read-words))))

(defthm generated-copy-preserves-control
  (let ((after (generated-copy-words count source destination world)))
    (and (equal (proof-world-pc after) (proof-world-pc world))
         (equal (proof-world-reg register after) (proof-world-reg register world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (generated-sp after) (generated-sp world))
         (equal (generated-flags after) (generated-flags world))
         (equal (proof-world-regions after) (proof-world-regions world))))
  :hints (("Goal" :induct (generated-copy-words count source destination world)
                  :in-theory (e/d (generated-copy-words)
                                  (proof-world-pc proof-world-stop proof-world-regions
                                   generated-sp generated-flags)))))
