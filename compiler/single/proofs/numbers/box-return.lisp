(in-package "BOYMOO-PROOFS")

(include-book "fresh-views")
(include-book "completion-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-number-execute-block proof-segment-p
                     proof-number-checked-block-p proof-number-cut-free-prefix-p
                     proof-integer-reserve-return-p proof-frame-return-p proof-preserved-heap-p
                     proof-reserved-span-p proof-heap-p proof-world-machine proof-world-reg
                     proof-world-pc proof-world-stop proof-load-word proof-machine-limit
                     proof-reg-value-p proof-number-next-object-rank
                     boymoo-model::a64-sp boymoo-model::a64-memory)))

(local
 (defthm reserve-return-state
   (implies (proof-integer-reserve-return-p a b 24 before after old-objects objects packages)
            (and (equal (proof-world-pc after) (proof-world-reg 30 before))
                 (equal (boymoo-model::a64-sp (proof-world-machine after))
                        (boymoo-model::a64-sp (proof-world-machine before)))
                 (proof-reg-value-p 0 a after objects packages)
                 (proof-reg-value-p 1 b after objects packages)
                 (proof-heap-p after objects packages)
                 (proof-reserved-span-p :header (proof-world-reg 2 after) 24 after objects)))
   :hints (("Goal"
            :in-theory (e/d (proof-integer-reserve-return-p proof-frame-return-p
                             proof-preserved-heap-p)
                            (proof-register-frame-p proof-heap-frame-p
                             proof-prefix-preserved-p proof-dynamic-table-preserved-p))))
   :rule-classes nil))

(defund proof-number-box-reserve-ready (reserve world)
  (proof-number-execute-block
   (proof-number-box-reserve-instructions (proof-world-pc world) reserve) world))

(defund proof-number-box-publish-after (returned)
  (proof-number-execute-block *proof-number-box-publish-instructions* returned))

(defund proof-number-box-object-map (returned reserved-objects)
  (cons (proof-object (proof-world-reg 2 returned) :active :header
                      (proof-number-next-object-rank reserved-objects))
        reserved-objects))

(defund proof-number-box-fields-trace-p (reserve world returned reserve-steps)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (entry (proof-world-pc world))
         (continuation (+ 12 entry))
         (link (proof-world-reg 30 world))
         (code (proof-number-box-reserve-instructions entry reserve))
         (ready (proof-number-box-reserve-ready reserve world))
         (machine-end (+ (- (proof-machine-limit ready) *proof-machine-margin*)
                         *proof-machine-reservation*))
         (return-machine (proof-world-machine returned)))
    (and (not (eq (car machine) :svc))
         (proof-span-p (- sp 16) 16)
         (unsigned-byte-p 64 sp)
         (unsigned-byte-p 64 continuation)
         (unsigned-byte-p 64 reserve)
         (<= sp machine-end) (<= machine-end (expt 2 64))
         (proof-number-checked-block-p code (list reserve) world)
         (proof-number-cut-free-prefix-p 3 (list reserve link) world)
         (natp reserve-steps)
         (proof-segment-p reserve-steps (list continuation) ready :cut returned)
         (proof-number-cut-free-prefix-p reserve-steps (list continuation link) ready)
         (not (eq (car return-machine) :svc))
         (proof-number-checked-block-p *proof-number-box-publish-instructions*
                                      (list link) returned))))

(defthm proof-number-box-fields-return
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (link (proof-world-reg 30 world))
         (ready (proof-number-box-reserve-ready reserve world))
         (after (proof-number-box-publish-after returned))
         (objects (proof-number-box-object-map returned reserved-objects))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (equal (proof-world-reg 2 world) (+ 4096 kind))
                  (proof-number-box-fields-trace-p reserve world returned reserve-steps)
                  (proof-integer-reserve-return-p a b 24 ready returned
                                                  old-objects reserved-objects packages))
             (and (proof-segment-p (+ 3 reserve-steps 6) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use (proof-number-box-calls-reserve
                 (:instance reserve-return-state
                            (before (proof-number-box-reserve-ready reserve world))
                            (after returned) (objects reserved-objects))
                 (:instance proof-number-reserve-preserves-machine-saves
                            (before (proof-number-box-reserve-ready reserve world))
                            (after returned) (new-objects reserved-objects) (offset 0) (bytes 24))
                 (:instance proof-number-reserve-preserves-machine-saves
                            (before (proof-number-box-reserve-ready reserve world))
                            (after returned) (new-objects reserved-objects) (offset 8) (bytes 24))
                 (:instance proof-number-box-publishes-reserved-value
                            (world returned) (old-objects reserved-objects))
                 (:instance proof-number-compose-segments
                            (prefix reserve-steps) (suffix 6)
                            (first-cuts (list (+ 12 (proof-world-pc world))))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before (proof-number-box-reserve-ready reserve world))
                            (middle returned) (reason :cut)
                            (after (proof-number-box-publish-after returned)))
                 (:instance proof-number-compose-segments
                            (prefix 3) (suffix (+ reserve-steps 6))
                            (first-cuts (list reserve))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-box-reserve-ready reserve world))
                            (after (proof-number-box-publish-after returned))))
           :in-theory (e/d (proof-number-box-fields-trace-p proof-number-box-reserve-ready
                            proof-number-box-publish-after proof-number-box-object-map)
                           (proof-number-box-reserve-instructions
                            proof-number-reduced-p proof-object))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-allocated-return
  (let* ((middle (proof-number-box-select-after kind unchanged fields world))
         (ready (proof-number-box-reserve-ready reserve middle))
         (after (proof-number-box-publish-after returned))
         (objects (proof-number-box-object-map returned reserved-objects))
         (link (proof-world-reg 30 world))
         (count (if (equal kind 4) 3 4))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (proof-number-box-select-pre-p kind unchanged fields world)
                  (proof-reg-value-p 0 a world old-objects packages)
                  (proof-reg-value-p 1 b world old-objects packages)
                  (proof-number-cut-free-prefix-p count (list fields link) world)
                  (proof-number-box-fields-trace-p reserve middle returned reserve-steps)
                  (proof-integer-reserve-return-p a b 24 ready returned
                                                  old-objects reserved-objects packages)
                  (natp reserve-steps))
             (and (proof-segment-p (+ count 9 reserve-steps) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (proof-reg-value-p 0 a middle old-objects packages)
                  (proof-reg-value-p 1 b middle old-objects packages)
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use (proof-number-box-select
                 (:instance proof-number-box-select-by-value (objects old-objects))
                 (:instance proof-number-box-fields-return
                            (world (proof-number-box-select-after kind unchanged fields world)))
                 (:instance proof-number-compose-segments
                            (prefix (if (equal kind 4) 3 4)) (suffix (+ 9 reserve-steps))
                            (first-cuts (list fields)) (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-box-select-after kind unchanged fields world))
                            (after (proof-number-box-publish-after returned)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value a) (word (proof-world-reg 0 world))
                            (before world) (objects old-objects)
                            (after (proof-number-box-select-after kind unchanged fields world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 1) (value b) (word (proof-world-reg 1 world))
                            (before world) (objects old-objects)
                            (after (proof-number-box-select-after kind unchanged fields world))))
           :in-theory (e/d (proof-number-box-select-count proof-number-box-select-target
                            proof-reg-value-p)
                           (proof-number-box-select-pre-p proof-machine-value-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-complex-collapsed-return
  (let* ((link (proof-world-reg 30 world))
         (middle (proof-number-types-completion-after t classifier world))
         (leaf (proof-number-box-select-after 5 unchanged fields middle))
         (code '((:branch-reg 30 nil)))
         (after (proof-number-execute-block code leaf))
         (count (+ 3 (proof-number-types-completion-steps t classifier world))))
    (implies (and (equal (rfix b) 0)
                  (proof-number-types-completion-trace-p t classifier (list link) a b world objects packages)
                  (proof-number-box-select-pre-p 5 unchanged fields middle)
                  (proof-number-cut-free-prefix-p 2 (list unchanged link) middle)
                  (proof-number-checked-block-p code (list link) leaf)
                  (not (eq (car (proof-world-machine leaf)) :svc))
                  (unsigned-byte-p 64 (+ 4 unchanged)))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 (complex (rfix a) (rfix b)) after objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-types-return-or-fallthrough
                            (rational-only t) (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-box-collapse-return
                            (kind 5) (a (rfix a)) (b (rfix b))
                            (world (proof-number-types-completion-after t classifier world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (proof-number-types-completion-steps t classifier world))
                            (suffix 3) (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-types-completion-after t classifier world))
                            (after (proof-number-execute-block
                                    '((:branch-reg 30 nil))
                                    (proof-number-box-select-after
                                     5 unchanged fields
                                     (proof-number-types-completion-after t classifier world))))
                            (reason :cut)))
           :in-theory (disable proof-number-types-completion-trace-p proof-number-box-select-pre-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-complex-allocated-return
  (let* ((link (proof-world-reg 30 world))
         (middle (proof-number-types-completion-after t classifier world))
         (selected (proof-number-box-select-after 5 unchanged fields middle))
         (ready (proof-number-box-reserve-ready reserve selected))
         (after (proof-number-box-publish-after returned))
         (objects (proof-number-box-object-map returned reserved-objects))
         (count (+ 13 reserve-steps (proof-number-types-completion-steps t classifier world))))
    (implies (and (not (equal (rfix b) 0))
                  (proof-number-types-completion-trace-p t classifier (list link) a b world old-objects packages)
                  (proof-number-box-select-pre-p 5 unchanged fields middle)
                  (proof-number-cut-free-prefix-p 4 (list fields link) middle)
                  (proof-number-box-fields-trace-p reserve selected returned reserve-steps)
                  (proof-integer-reserve-return-p (rfix a) (rfix b) 24 ready returned
                                                  old-objects reserved-objects packages)
                  (natp reserve-steps))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (proof-reg-value-p 0 (complex (rfix a) (rfix b)) after objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-types-return-or-fallthrough
                            (rational-only t) (objects old-objects) (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-box-allocated-return
                            (kind 5) (a (rfix a)) (b (rfix b))
                            (world (proof-number-types-completion-after t classifier world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (proof-number-types-completion-steps t classifier world))
                            (suffix (+ 13 reserve-steps)) (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-types-completion-after t classifier world))
                            (after (proof-number-box-publish-after returned)) (reason :cut)))
           :in-theory (disable proof-number-types-completion-trace-p proof-number-box-select-pre-p)
           :do-not-induct t))
  :rule-classes nil)
