(in-package "BOYMOO-PROOFS")

(include-book "stack")
(include-book "stack-write")
(include-book "prefix-suffix")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-term generated-push-schedule
                    proof-world-pc proof-world-reg proof-stack-base proof-stack-top proof-stack-limit
                    proof-stack-end proof-heap-p proof-heap-layout-p proof-stack-prefix proof-reg-value-p
                    proof-segment-p generated-path-after generated-path-p expt))

(defthm generated-scheduled-push-fits-reserved-frame
  (let ((high-water (mv-nth 1 (boymoo-compiler::gen-term term scope depth tail context code high serial))))
    (implies (and (natp depth) (natp high) (integerp frame)
                  (member-equal pushed (car (generated-push-schedule :term term nil depth context)))
                  (equal (proof-stack-top before) (+ frame (* 8 (1- pushed))))
                  (<= (+ frame (* 8 high-water)) (proof-stack-limit before)))
             (<= (+ (proof-stack-top before) 8) (proof-stack-limit before))))
  :hints (("Goal" :use generated-term-high-bounds-pushes))
  :rule-classes nil)

(defthm generated-scheduled-push-preserves-heap-and-appends-source-value
  (let* ((high-water (mv-nth 1 (boymoo-compiler::gen-term term scope depth tail context code high serial)))
         (frame (proof-world-reg 19 before)) (top (proof-stack-top before))
         (path *generated-push-path*) (end (+ (proof-world-pc before) 8))
         (after (generated-path-after path before)))
    (implies (and (natp depth) (natp high)
                  (member-equal pushed (car (generated-push-schedule :term term nil depth context)))
                  (equal top (+ frame (* 8 (1- pushed))))
                  (<= (+ frame (* 8 high-water)) (proof-stack-limit before))
                  (proof-heap-p before objects packages) (proof-reg-value-p 0 datum before objects packages)
                  (< end (expt 2 64)) (generated-ordinary-machine-p before) (generated-path-p path (list end) before))
             (and (proof-segment-p 2 (list end) before :cut after)
                  (proof-heap-p after objects packages)
                  (equal (proof-world-reg 19 after) frame)
                  (equal (proof-stack-top after) (+ frame (* 8 pushed)))
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (equal (proof-stack-views 1 top (proof-heap-base after) objects packages (proof-world-machine after))
                         (list :slots (proof-value-view datum))))))
  :hints (("Goal"
           :use ((:instance generated-scheduled-push-fits-reserved-frame (frame (proof-world-reg 19 before)))
                 (:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-stack-prefix-has-aligned-slot-count (world before) (top (proof-stack-top before)))
                 (:instance generated-push-preserves-heap-and-appends-value
                            (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))))))
  :rule-classes nil)

(defthm generated-successful-growth-limit-covers-its-prior-limit
  (implies (and (<= (proof-stack-limit before) (proof-stack-end before))
                (<= required (proof-stack-end before)))
           (and (<= (proof-stack-limit before) (proof-grow-limit required before))
                (<= required (proof-grow-limit required before))))
  :hints (("Goal" :in-theory (enable proof-grow-limit)))
  :rule-classes nil)
