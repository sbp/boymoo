(in-package "BOYMOO-PROOFS")

(include-book "prologue-paths")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-run proof-advance proof-segment-p proof-world-pc
                    proof-world-reg proof-world-stop proof-instruction-effect proof-label-address
                    proof-grow-return-p generated-ordinary-machine-p generated-before-cuts-p
                    generated-path-p generated-path-after generated-address-path
                    generated-growing-prologue-path generated-prologue-depth-stop-path
                    generated-load-word generated-sp expt))

(defthm generated-growing-prologue-enters-body
  (let* ((sp (- (generated-sp before) 16))
         (top (proof-stack-top before))
         (required (+ top bytes))
         (machine-end (+ (- (proof-machine-limit entered) *proof-machine-margin*)
                         *proof-machine-reservation*))
         (after (generated-path-after frame-path returned)))
    (implies (and (natp arity) (natp high) (< arity high) (equal bytes (* 8 (- high arity)))
                  (equal target (proof-label-address "rt:grow" base labels))
                  (equal entry-path (generated-growing-prologue-path bytes target before))
                  (equal entered (generated-path-after entry-path before))
                  (equal frame-path (generated-address-path 19 25 (* 8 arity) t))
                  (equal body (+ (proof-world-pc before) 4 (* 4 (len entry-path)) (* 4 (len frame-path))))
                  (unsigned-byte-p 64 bytes) (unsigned-byte-p 64 (* 8 arity)) (<= (* 8 arity) top)
                  (<= 16 (generated-sp before)) (<= (proof-machine-limit before) sp)
                  (< (proof-stack-limit before) required) (< required (expt 2 64))
                  (unsigned-byte-p 64 target) (< body (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p entry-path (list target body) before)
                  (<= required (proof-stack-end entered)) (<= (+ sp 16) machine-end)
                  (generated-before-cuts-p grow-steps (list body) entered)
                  (equal returned (proof-advance grow-steps entered))
                  (proof-grow-return-p "rt:grow" required entered returned old-objects new-objects packages)
                  (not (proof-world-stop returned)) (generated-path-p frame-path (list body) returned))
             (and (proof-segment-p (+ (len entry-path) (nfix grow-steps) (len frame-path))
                                   (list body) before :cut after)
                  (equal (proof-world-pc after) body)
                  (equal (proof-world-reg 19 after) (- top (* 8 arity)))
                  (equal (proof-stack-top after) top)
                  (<= required (proof-stack-limit after))
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ sp 8) after) (proof-world-reg 30 before)))))
  :hints (("Goal"
           :use ((:instance generated-placed-path-allows-fewer-cuts (path entry-path)
                            (all-cuts (list target body)) (cuts (list target)))
                 (:instance generated-placed-path-allows-fewer-cuts (path entry-path)
                            (all-cuts (list target body)) (cuts (list body)))
                 (:instance generated-advance-of-placed-path
                            (world before) (instructions entry-path) (cuts (list body)))
                 generated-prologue-reaches-growth-entry
                 (:instance generated-prologue-after-successful-growth
                            (required (+ (proof-stack-top before) bytes)))
                 (:instance generated-prefix-then-segment (prefix grow-steps) (suffix (len frame-path))
                            (before entered) (middle returned) (cuts (list body)) (reason :cut)
                            (after (generated-path-after frame-path returned)))
                 (:instance generated-prefix-then-segment (prefix (len entry-path))
                            (suffix (+ (nfix grow-steps) (len frame-path)))
                            (middle entered) (cuts (list body)) (reason :cut)
                            (after (generated-path-after frame-path returned))))
           :in-theory (disable generated-advance-of-placed-path proof-stack-end proof-machine-limit
                              proof-resource-bound-p)))
  :rule-classes nil)

(defthm generated-depth-stop-composes-with-runtime
  (let* ((target (proof-label-address (proof-resource-label :machine-stack) base labels))
         (path (generated-prologue-depth-stop-path target before))
         (entered (generated-path-after path before))
         (next-sp (- (generated-sp before) 16)))
    (implies (and (unsigned-byte-p 64 target) (< (+ 16 (proof-world-pc before)) (expt 2 64))
                  (<= 16 (generated-sp before)) (< next-sp (proof-machine-limit before))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p path (list target) before)
                  (proof-segment-p stop-steps nil entered '(:exit . 3) after)
                  (proof-resource-observation-p after))
             (and (proof-resource-bound-p :machine-stack next-sp entered)
                  (proof-segment-p (+ 4 (nfix stop-steps)) nil before '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :hints (("Goal"
           :use (generated-prologue-reaches-failed-depth-check
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-prologue-depth-stop-path
                                   (proof-label-address (proof-resource-label :machine-stack) base labels) before))
                            (all-cuts (list (proof-label-address
                                             (proof-resource-label :machine-stack) base labels)))
                            (cuts nil))
                 (:instance generated-advance-of-placed-path
                            (world before)
                            (instructions (generated-prologue-depth-stop-path
                                           (proof-label-address (proof-resource-label :machine-stack) base labels)
                                           before))
                            (cuts nil))
                 (:instance generated-prefix-then-segment (prefix 4) (suffix stop-steps)
                            (middle (generated-path-after
                                     (generated-prologue-depth-stop-path
                                      (proof-label-address (proof-resource-label :machine-stack) base labels) before)
                                     before))
                            (cuts nil) (reason '(:exit . 3))))
           :in-theory (e/d (generated-prologue-depth-stop-path)
                           (proof-resource-observation-p proof-resource-bound-p
                            generated-path-after-append))))
  :rule-classes nil)
