(in-package "BOYMOO-PROOFS")

(include-book "store-traces")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-instruction-effect
                     proof-execute proof-number-checked-block-p
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                     proof-reg-value-p proof-machine-value-p proof-heap-base proof-load-word
                     proof-datum-return-p proof-preserved-heap-p proof-frame-return-p
                     proof-number-binary-types-p proof-number-order
                     (:definition update-nth) (:definition nth)
                     boymoo-model::a64-sp boymoo-model::a64-memory)))

(defund proof-number-less-leaf (order)
  (if (equal order -1) "rt:true" "rt:nil"))

(defund proof-number-less-selected (order yes no world)
  (proof-number-execute-block
   (proof-number-less-return-path order (proof-world-pc world) yes no) world))

(defund proof-number-less-tail-after (order yes no world)
  (proof-number-execute-block
   (cdr (assoc-equal (proof-number-less-leaf order) *proof-number-leaf-returns*))
   (proof-number-less-selected order yes no world)))

(defund proof-number-less-tail-code-p (order link yes no world)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (target (if (equal order -1) yes no))
         (path (proof-number-less-return-path order (proof-world-pc world) yes no))
         (selected (proof-number-less-selected order yes no world))
         (leaf (cdr (assoc-equal (proof-number-less-leaf order) *proof-number-leaf-returns*))))
    (and (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 sp))
         (unsigned-byte-p 64 (+ 12 (proof-world-pc world)))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p path (list target) world)
         (proof-number-checked-block-p path (list link) world)
         (not (eq (car (proof-world-machine selected)) :svc))
         (unsigned-byte-p 64 (+ 4 target))
         (proof-number-checked-block-p leaf (list link) selected))))

(defund proof-number-less-tail-trace-p (order link yes no world)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine)))
    (and (member-equal order '(-1 0 1))
         (equal (proof-world-reg 0 world) (proof-integer-word order))
         (equal link (proof-load-word (+ 8 sp) machine))
         (proof-number-less-tail-code-p order link yes no world))))

(local
 (defthm comparison-result-tag
   (implies (and (member-equal order '(-1 0 1))
                 (proof-reg-value-p 0 order world objects packages))
            (equal (proof-world-reg 0 world) (proof-integer-word order)))
   :hints (("Goal"
            :use ((:instance proof-number-value-has-immediate-word
                             (value order) (word (proof-world-reg 0 world))
                             (base (proof-heap-base world))
                             (machine (proof-world-machine world))))
            :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                            (proof-view-step proof-view proof-world-machine proof-world-reg))))
   :rule-classes nil))

(defthm proof-number-less-tail-returns-boolean
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (count (if (equal order -1) 5 6))
         (after (proof-number-less-tail-after order yes no world)))
    (implies (proof-number-less-tail-trace-p order link yes no world)
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 29 after) (proof-load-word sp machine))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine))
                  (equal (proof-world-reg 0 after) (if (equal order -1) *proof-t* *proof-nil*)))))
  :hints (("Goal"
           :use (proof-number-less-finishes-comparison
                 (:instance proof-number-leaf-returns-word
                            (name (proof-number-less-leaf order)) (register 29)
                            (world (proof-number-less-selected order yes no world)))
                 (:instance proof-number-leaf-returns-word
                            (name (proof-number-less-leaf order)) (register 30)
                            (world (proof-number-less-selected order yes no world)))
                 (:instance proof-number-checked-block-exact-prefix
                            (cuts (list link))
                            (instructions (proof-number-less-return-path
                                           order (proof-world-pc world) yes no)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (if (equal order -1) 3 4)) (suffix 2)
                            (before world) (cuts (list link)) (reason :cut)
                            (middle (proof-number-less-selected order yes no world))
                            (after (proof-number-less-tail-after order yes no world))))
           :in-theory (e/d (proof-number-less-tail-trace-p proof-number-less-tail-code-p
                            proof-number-less-tail-after
                            proof-number-less-selected proof-number-less-leaf
                            proof-number-less-return-code proof-number-leaf-result-word)
                           (proof-number-execute-block))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-less-compare-ready (rational complex world)
  (proof-number-execute-block
   (proof-number-less-compare-path (proof-world-pc world) rational complex
                                  (equal (proof-world-reg 3 world) 5))
   world))

(defund proof-number-less-resume-code (complex-case)
  (if complex-case nil '((:branch 8 nil))))

(defund proof-number-less-resumed (complex-case world)
  (proof-number-execute-block (proof-number-less-resume-code complex-case) world))

(defthm proof-number-less-resume
  (let* ((machine (proof-world-machine world))
         (code (proof-number-less-resume-code complex-case))
         (after (proof-number-less-resumed complex-case world)))
    (implies (and (not (eq (car machine) :svc))
                  (implies (not complex-case) (unsigned-byte-p 64 (+ 8 (proof-world-pc world))))
                  (proof-number-checked-block-p code (list link) world))
             (and (proof-number-exact-prefix-p (if complex-case 0 1) (list link) world after)
                  (equal (proof-world-pc after) (+ (if complex-case 0 8) (proof-world-pc world)))
                  (equal (proof-world-reg register after) (proof-world-reg register world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine))
                  (equal (cdr after) (cdr world)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-less-resume-code complex-case))
                            (cuts (list link))))
           :in-theory (e/d (proof-number-less-resumed proof-number-less-resume-code
                            proof-world-pc proof-world-reg proof-heap-base)
                           (proof-reg boymoo-model::a64-pc
                            boymoo-model::a64-set-pc proof-advance
                            proof-number-cut-free-prefix-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-numeric-clobbers ()
  (append *proof-volatile-registers* '(24 26 27)))

(defthm proof-number-comparison-return-keeps-saves
  (let* ((first (proof-world-machine ready))
         (last (proof-world-machine returned))
         (sp (boymoo-model::a64-sp first))
         (end (+ (- (proof-machine-limit ready) *proof-machine-margin*)
                 *proof-machine-reservation*)))
    (implies (and (member-equal order '(-1 0 1))
                  (proof-datum-return-p order (proof-number-numeric-clobbers)
                                        t t nil ready returned objects new-objects packages)
                  (<= (+ 16 sp) end)
                  (<= end (expt 2 64)))
             (and (equal (proof-world-pc returned) (proof-world-reg 30 ready))
                  (equal (boymoo-model::a64-sp last) sp)
                  (equal (proof-load-word sp last) (proof-load-word sp first))
                  (equal (proof-load-word (+ 8 sp) last) (proof-load-word (+ 8 sp) first))
                  (equal (proof-world-reg 0 returned) (proof-integer-word order)))))
  :hints (("Goal"
           :use ((:instance comparison-result-tag (world returned) (objects new-objects))
                 (:instance proof-number-load-agrees-inside-saved-span
                            (address (boymoo-model::a64-sp (proof-world-machine ready)))
                            (start (boymoo-model::a64-sp (proof-world-machine ready)))
                            (end (+ (- (proof-machine-limit ready) *proof-machine-margin*)
                                    *proof-machine-reservation*))
                            (before ready) (after returned))
                 (:instance proof-number-load-agrees-inside-saved-span
                            (address (+ 8 (boymoo-model::a64-sp (proof-world-machine ready))))
                            (start (boymoo-model::a64-sp (proof-world-machine ready)))
                            (end (+ (- (proof-machine-limit ready) *proof-machine-margin*)
                                    *proof-machine-reservation*))
                            (before ready) (after returned)))
           :in-theory (e/d (proof-datum-return-p proof-preserved-heap-p proof-frame-return-p
                            proof-heap-frame-p)
                           (proof-heap-p proof-memory-span-agrees-p proof-register-frame-p
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm word-with-same-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-load-word address last) (proof-load-word address first)))
   :hints (("Goal" :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm proof-number-less-continues-comparator-return
  (let* ((resumed (proof-number-less-resumed complex-case returned))
         (sp (boymoo-model::a64-sp (proof-world-machine ready)))
         (end (+ (- (proof-machine-limit ready) *proof-machine-margin*)
                 *proof-machine-reservation*))
         (after (proof-number-less-tail-after order yes no resumed))
         (steps (+ (if complex-case 0 1) (if (equal order -1) 5 6))))
    (implies (and (member-equal order '(-1 0 1))
                  (proof-datum-return-p order (proof-number-numeric-clobbers)
                                        t t nil ready returned objects new-objects packages)
                  (<= (+ 16 sp) end) (<= end (expt 2 64))
                  (equal link (proof-load-word (+ 8 sp) (proof-world-machine ready)))
                  (not (eq (car (proof-world-machine returned)) :svc))
                  (implies (not complex-case)
                           (unsigned-byte-p 64 (+ 8 (proof-world-pc returned))))
                  (proof-number-checked-block-p (proof-number-less-resume-code complex-case)
                                               (list link) returned)
                  (proof-number-less-tail-code-p order link yes no resumed))
             (and (proof-segment-p steps (list link) returned :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 29 after) (proof-load-word sp (proof-world-machine ready)))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                  (equal (proof-world-reg 0 after) (if (equal order -1) *proof-t* *proof-nil*)))))
  :hints (("Goal"
           :use (proof-number-comparison-return-keeps-saves
                 (:instance proof-number-less-resume (world returned) (register 0))
                 (:instance word-with-same-memory
                            (first (proof-world-machine returned))
                            (last (proof-world-machine (proof-number-less-resumed complex-case returned)))
                            (address (boymoo-model::a64-sp (proof-world-machine ready))))
                 (:instance word-with-same-memory
                            (first (proof-world-machine returned))
                            (last (proof-world-machine (proof-number-less-resumed complex-case returned)))
                            (address (+ 8 (boymoo-model::a64-sp (proof-world-machine ready)))))
                 (:instance proof-number-less-tail-returns-boolean
                            (world (proof-number-less-resumed complex-case returned)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (if complex-case 0 1)) (suffix (if (equal order -1) 5 6))
                            (before returned) (cuts (list link)) (reason :cut)
                            (middle (proof-number-less-resumed complex-case returned))
                            (after (proof-number-less-tail-after
                                    order yes no (proof-number-less-resumed complex-case returned)))))
           :in-theory (enable proof-number-less-tail-trace-p)
           :do-not-induct t))
  :rule-classes nil)
