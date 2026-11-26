(in-package "BOYMOO-PROOFS")

(include-book "prologue-state")
(include-book "segments")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-label-address proof-heap-p proof-world-pc proof-world-reg proof-world-stop
                    proof-stack-top proof-stack-limit proof-machine-limit proof-heap-layout-p proof-resource-bound-p
                    proof-resource-observation-p proof-segment-p generated-sp generated-path-after
                    generated-path-p generated-growing-prologue-path expt))

(local
 (defthm generated-fitting-heap-layout-is-running
   (implies (proof-heap-layout-p before) (not (proof-world-stop before)))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p)))))

(defthm generated-growth-edge-composes-with-value-stack-stop
  (let* ((target (proof-label-address "rt:grow" base labels))
         (entry-path (generated-growing-prologue-path bytes target before))
         (entered (generated-path-after entry-path before))
         (required (+ (proof-stack-top before) bytes))
         (link (+ (proof-world-pc before) 4 (* 4 (len entry-path)))))
    (implies (and (proof-heap-p before objects packages) (generated-ordinary-machine-p before)
                  (posp bytes) (unsigned-byte-p 64 bytes) (unsigned-byte-p 64 target)
                  (<= (proof-machine-limit before) (- (generated-sp before) 16))
                  (< (proof-stack-limit before) required) (< required (expt 2 64)) (< link (expt 2 64))
                  (generated-path-p entry-path (list target) before)
                  (proof-resource-bound-p :value-stack required entered)
                  (proof-segment-p stop-steps nil entered '(:exit . 3) after)
                  (proof-resource-observation-p after))
             (and (equal (proof-world-pc entered) target)
                  (equal (proof-world-reg 0 entered) required)
                  (proof-segment-p (+ (len entry-path) (nfix stop-steps)) nil before '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 generated-incoming-machine-bound-prevents-subtraction-wrap
                 generated-prologue-reaches-growth-entry
                 (:instance generated-segment-composes-with-final-segment
                            (prefix-steps (len (generated-growing-prologue-path bytes (proof-label-address "rt:grow" base labels) before)))
                            (prefix-cuts (list (proof-label-address "rt:grow" base labels)))
                            (middle (generated-path-after
                                     (generated-growing-prologue-path bytes (proof-label-address "rt:grow" base labels) before) before))
                            (cuts nil) (suffix-steps stop-steps) (reason '(:exit . 3))))))
  :rule-classes nil)

(local
 (defthm generated-valid-layout-shares-end-when-stack-base-is-equal
   (implies (and (proof-heap-layout-p before) (proof-heap-layout-p entered)
                 (equal (proof-stack-base entered) (proof-stack-base before)))
            (equal (proof-stack-end entered) (proof-stack-end before)))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p)))
   :rule-classes nil))

(defthm generated-over-reservation-demand-reaches-value-stack-resource-stop
  (let* ((target (proof-label-address "rt:grow" base labels))
         (path (generated-growing-prologue-path bytes target before))
         (entered (generated-path-after path before)) (required (+ (proof-stack-top before) bytes))
         (link (+ (proof-world-pc before) 4 (* 4 (len path)))))
    (implies (and (proof-heap-p before objects packages) (generated-ordinary-machine-p before)
                  (posp bytes) (unsigned-byte-p 64 bytes) (unsigned-byte-p 64 target)
                  (<= (proof-machine-limit before) (- (generated-sp before) 16))
                  (proof-resource-bound-p :value-stack required before)
                  (< required (expt 2 64)) (< link (expt 2 64))
                  (generated-path-p path (list target) before)
                  (proof-segment-p stop-steps nil entered '(:exit . 3) after)
                  (proof-resource-observation-p after))
             (and (proof-resource-bound-p :value-stack required entered)
                  (equal (proof-world-reg 0 entered) required)
                  (proof-segment-p (+ (len path) (nfix stop-steps)) nil before '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :hints (("Goal"
           :use (generated-growth-edge-composes-with-value-stack-stop
                 (:instance generated-growing-prologue-establishes-heap-at-runtime-entry
                            (target (proof-label-address "rt:grow" base labels)))
                 (:instance generated-valid-layout-shares-end-when-stack-base-is-equal
                            (entered (generated-path-after
                                      (generated-growing-prologue-path bytes (proof-label-address "rt:grow" base labels) before) before)))
                 (:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-has-layout-and-roots
                            (world (generated-path-after
                                    (generated-growing-prologue-path bytes (proof-label-address "rt:grow" base labels) before) before)))
                 (:instance generated-heap-layout-value-stack-bounds (world before)))
           :in-theory (enable proof-resource-bound-p)))
  :rule-classes nil)
