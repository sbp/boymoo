(in-package "BOYMOO-PROOFS")

(include-book "stack-write")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-world-pc proof-world-reg proof-world-machine
                    proof-world-regions proof-world-page-size proof-world-stop proof-heap-base proof-box-top
                    proof-heap-limit proof-stack-base proof-stack-top proof-stack-limit proof-machine-limit
                    proof-stack-prefix proof-prefix-preserved-p proof-reg-value-p proof-machine-value-p
                    proof-span-p proof-subspan-p proof-disjoint-p proof-segment-p proof-instruction-effect
                    generated-path-p generated-path-after generated-sp generated-load-word
                    boymoo-model::a64-unsigned expt mod))

(local
 (defthm generated-identical-memory-entries-agree-outside-span
   (generated-outside-entries-p entries start end memory memory)
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm generated-return-stack-pointer-update-keeps-page-size
   (equal (proof-world-page-size (generated-set-sp sp before)) (proof-world-page-size before))
   :hints (("Goal" :in-theory (enable generated-set-sp)))))

(defthm generated-return-path-observations
  (let* ((sp (generated-sp before)) (link (generated-load-word (+ sp 8) before))
         (after (generated-path-after *generated-return-path* before)))
    (implies (and (generated-ordinary-machine-p before) (< (+ sp 16) (expt 2 64)))
             (and (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 30 after) link)
                  (equal (generated-sp after) (+ sp 16))
                  (equal (proof-stack-top after) (proof-world-reg 19 before))
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-heap-base after) (proof-heap-base before))
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (generated-ordinary-machine-p after)
                  (generated-memory-equiv (proof-world-machine after) (proof-world-machine before))
                  (implies (not (member-equal register '(19 25 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register before))))))
  :hints (("Goal" :in-theory (enable generated-path-after proof-stack-top proof-heap-base proof-stack-base proof-runtime-word)))
  :rule-classes nil)

(local
 (defthm generated-return-is-stack-update-without-writes
   (let* ((sp (generated-sp before)) (frame (proof-world-reg 19 before))
          (after (generated-path-after *generated-return-path* before)))
     (implies (and (proof-heap-layout-p before) (natp keep)
                   (equal frame (+ (proof-stack-base before) (* 8 keep))) (<= frame (proof-stack-top before))
                   (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                   (generated-ordinary-machine-p before) (< (+ sp 16) (expt 2 64)))
              (generated-stack-update-p sp sp before after)))
   :hints (("Goal"
            :use ((:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-heap-layout-machine-stack-bounds (world before))
                  (:instance generated-add-slots-keeps-stack-alignment (base (proof-stack-base before)) (count keep))
                  (:instance generated-floor-add-multiple (x (generated-sp before)) (divisor 16) (q 1)))
            :in-theory (enable generated-stack-update-p generated-runtime-stack-span-p generated-memory-outside-p
                               proof-subspan-p proof-span-p generated-path-after proof-stack-top proof-stack-limit
                               proof-machine-limit proof-heap-base proof-box-top proof-heap-limit mod)))
   :rule-classes nil))

(local
 (defthm generated-return-machine-frame-is-outside-value-stack
   (let ((sp (generated-sp before)) (frame (proof-world-reg 19 before)))
     (implies (and (proof-heap-layout-p before) (<= frame (proof-stack-top before))
                   (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before)))
              (proof-disjoint-p (proof-stack-base before) frame sp sp)))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p proof-subspan-p proof-disjoint-p
                                     generated-machine-stack-base generated-machine-stack-end)))
   :rule-classes nil))

(defthm generated-return-preserves-heap-and-retained-prefix
  (let* ((sp (generated-sp before)) (frame (proof-world-reg 19 before))
         (link (generated-load-word (+ sp 8) before)) (after (generated-path-after *generated-return-path* before)))
    (implies (and (proof-heap-p before objects packages) (natp keep)
                  (equal frame (+ (proof-stack-base before) (* 8 keep))) (<= frame (proof-stack-top before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                  (generated-ordinary-machine-p before) (< (+ sp 16) (expt 2 64))
                  (generated-path-p *generated-return-path* (list link) before)
                  (proof-reg-value-p 0 datum before objects packages))
             (and (proof-segment-p 3 (list link) before :cut after)
                  (proof-heap-p after objects packages)
                  (proof-prefix-preserved-p frame before after objects objects packages)
                  (equal (proof-stack-top after) frame)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 30 after) link)
                  (equal (generated-sp after) (+ sp 16))
                  (proof-reg-value-p 0 datum after objects packages))))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-layout-value-stack-bounds (world before))
                 (:instance generated-return-path-observations (register 0))
                 generated-return-is-stack-update-without-writes
                 generated-return-machine-frame-is-outside-value-stack
                 (:instance generated-stack-update-is-disjoint-from-published-objects
                            (start (generated-sp before)) (end (generated-sp before))
                            (after (generated-path-after *generated-return-path* before)))
                 (:instance generated-stack-update-preserves-untouched-prefix
                            (start (generated-sp before)) (end (generated-sp before))
                            (after (generated-path-after *generated-return-path* before)))
                 (:instance generated-stack-update-preserves-heap-with-valid-roots
                            (start (generated-sp before)) (end (generated-sp before))
                            (after (generated-path-after *generated-return-path* before)))
                 (:instance generated-placed-path-to-cut (instructions *generated-return-path*)
                            (cuts (list (generated-load-word (+ 8 (generated-sp before)) before)))))
           :in-theory (enable proof-subspan-p proof-span-p proof-disjoint-p proof-prefix-preserved-p proof-reg-value-p
                              proof-machine-value-p proof-value-p)))
  :rule-classes nil)
