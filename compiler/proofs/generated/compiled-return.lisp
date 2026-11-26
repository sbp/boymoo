(in-package "BOYMOO-PROOFS")

(include-book "return-heap")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-compiled-return-p proof-frame-return-p proof-register-frame-p proof-heap-frame-p
                    proof-memory-span-agrees-p proof-byte-entries-agree-p proof-streams-preserved-p
                    proof-heap-p proof-dynamic-table-preserved-p proof-prefix-preserved-p proof-dynamic-view
                    proof-heap-base proof-world-pc proof-world-reg proof-world-machine proof-world-stop
                    proof-stack-top proof-stack-base proof-stack-end proof-spaces-end proof-runtime-word
                    proof-segment-p proof-reg-value-p proof-subspan-p generated-sp generated-load-word
                    generated-path-after generated-path-p generated-memory-equiv expt))

(defconst *generated-compiled-return-clobbers*
  (append *proof-volatile-registers* '(24 25 26 27)))

(defund generated-at-saved-compiled-frame-p (arity entry before)
  (let ((sp (generated-sp before)))
    (and (not (proof-world-stop entry))
         (equal (generated-load-word sp before) (proof-world-reg 19 entry))
         (equal (generated-load-word (+ sp 8) before) (proof-world-reg 30 entry))
         (equal (+ sp 16) (generated-sp entry))
         (equal (proof-world-reg 19 before) (- (proof-stack-top entry) (* 8 arity)))
         (proof-register-frame-p 30 (list* 19 30 *generated-compiled-return-clobbers*) entry before)
         (proof-heap-frame-p entry before))))

(defthm generated-finish-emits-frame-restore-and-ret
  (equal (boymoo-compiler::gen-finish tail code)
         (if tail (boymoo-compiler::reverse-onto '((:mov 25 19) (:ldp-post 19 30 31 16) (:ret)) code) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-finish boymoo-compiler::gen-emit))))

(local
 (defun generated-register-frame-induction (register)
   (declare (xargs :measure (nfix register)))
   (if (zp register)
       register
     (generated-register-frame-induction (1- register)))))

(local
 (defthm generated-return-path-keeps-register-frame
   (let ((sp (generated-sp before)) (after (generated-path-after *generated-return-path* before)))
     (implies (and (generated-ordinary-machine-p before) (< (+ sp 16) (expt 2 64))
                   (equal (generated-load-word sp before) (proof-world-reg 19 entry))
                   (equal (generated-load-word (+ sp 8) before) (proof-world-reg 30 entry))
                   (proof-register-frame-p register (list* 19 30 *generated-compiled-return-clobbers*) entry before))
              (proof-register-frame-p register *generated-compiled-return-clobbers* entry after)))
   :hints (("Goal" :induct (generated-register-frame-induction register)
                   :in-theory (enable proof-register-frame-p))
           ("Subgoal *1/2" :use generated-return-path-observations)
           ("Subgoal *1/1" :use generated-return-path-observations))
   :rule-classes nil))

(local
 (defthm generated-return-control-updates-keep-resource-streams
   (and (equal (proof-streams-preserved-p entry (generated-set-pc pc before)) (proof-streams-preserved-p entry before))
        (equal (proof-streams-preserved-p entry (generated-set-sp sp before)) (proof-streams-preserved-p entry before))
        (equal (proof-streams-preserved-p entry (generated-set-reg register value before))
               (proof-streams-preserved-p entry before)))
   :hints (("Goal" :in-theory (enable proof-streams-preserved-p generated-set-machine
                                      generated-set-reg generated-set-pc generated-set-sp
                                      proof-world-input proof-world-stdout proof-world-stderr proof-world-page-size)))))

(local
 (defthm generated-return-path-keeps-resource-streams
   (let ((after (generated-path-after *generated-return-path* before)))
     (implies (generated-ordinary-machine-p before)
              (proof-streams-preserved-p before after)))
   :hints (("Goal" :in-theory (enable generated-path-after proof-streams-preserved-p)))
   :rule-classes nil))

(local
 (defthm generated-return-path-keeps-observed-heap-frame
   (let ((after (generated-path-after *generated-return-path* before)))
     (implies (and (proof-heap-frame-p entry before) (generated-ordinary-machine-p before)
                   (< (+ (generated-sp before) 16) (expt 2 64)))
              (proof-heap-frame-p entry after)))
   :hints (("Goal"
            :use ((:instance generated-return-path-observations (register 28)) generated-return-path-keeps-resource-streams)
            :in-theory (enable proof-heap-frame-p proof-streams-preserved-p proof-memory-span-agrees-p
                               generated-memory-equiv proof-spaces-end proof-stack-end proof-runtime-word
                               proof-load-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm generated-return-path-keeps-previous-dynamic-views
   (let ((after (generated-path-after *generated-return-path* before)))
     (implies (and (proof-dynamic-table-preserved-p t entry before old-objects objects packages)
                   (generated-ordinary-machine-p before) (< (+ (generated-sp before) 16) (expt 2 64)))
              (proof-dynamic-table-preserved-p t entry after old-objects objects packages)))
   :hints (("Goal"
            :use (:instance generated-return-path-observations (register 28))
            :in-theory (enable proof-dynamic-table-preserved-p proof-dynamic-view proof-dynamic-root)))
   :rule-classes nil))

(defthm generated-finish-establishes-compiled-return-contract
  (let* ((sp (generated-sp before)) (frame (proof-world-reg 19 before))
         (link (generated-load-word (+ sp 8) before)) (after (generated-path-after *generated-return-path* before)))
    (implies (and (natp arity) (boymoo-model::core-value-p result)
                  (generated-at-saved-compiled-frame-p arity entry before)
                  (proof-heap-p before objects packages) (natp keep)
                  (equal frame (+ (proof-stack-base before) (* 8 keep))) (<= frame (proof-stack-top before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                  (generated-ordinary-machine-p before) (< (+ sp 16) (expt 2 64))
                  (generated-path-p *generated-return-path* (list link) before)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) before objects packages)
                  (proof-prefix-preserved-p frame entry before old-objects objects packages)
                  (proof-dynamic-table-preserved-p t entry before old-objects objects packages))
             (and (proof-segment-p 3 (list (proof-world-reg 30 entry)) before :cut after)
                  (proof-compiled-return-p arity result entry after old-objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-return-preserves-heap-and-retained-prefix (datum (boymoo-model::core-datum result)))
                 (:instance generated-return-path-keeps-register-frame (register 30))
                 generated-return-path-keeps-observed-heap-frame generated-return-path-keeps-previous-dynamic-views
                 (:instance generated-prefix-preserved-transitive
                            (top (proof-world-reg 19 before)) (first entry) (middle before)
                            (last (generated-path-after *generated-return-path* before))
                            (first-objects old-objects) (middle-objects objects) (last-objects objects))
                 (:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-has-layout-and-roots (world (generated-path-after *generated-return-path* before)))
                 (:instance generated-heap-layout-value-stack-bounds (world before))
                 (:instance generated-heap-layout-value-stack-bounds (world (generated-path-after *generated-return-path* before))))
           :in-theory (enable generated-at-saved-compiled-frame-p proof-compiled-return-p proof-frame-return-p
                              generated-heap-machine-sp)))
  :rule-classes nil)
