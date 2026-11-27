(in-package "BOYMOO-PROOFS")

(include-book "frames")
(include-book "heap-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-segment-p proof-instruction-effect proof-step proof-label-address
                    proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-stack-top proof-heap-p proof-compiled-entry-p proof-compiled-return-p
                    proof-heap-frame-p proof-frame-return-p proof-register-frame-p
                    proof-prefix-preserved-p proof-reg-value-p proof-dynamic-table-preserved-p
                    generated-load-word
                    generated-sp boymoo-model::a64-unsigned expt))

(defthm generated-link-preserves-heap-observations
  (generated-heap-world-equiv (generated-link-to target before) before)
  :hints (("Goal" :in-theory (enable generated-link-to))))

(defthm generated-defined-call-establishes-entry
  (let* ((pc (proof-world-pc before))
         (arity (len args))
         (target (proof-label-address (list :fn name) base labels))
         (item (car (boymoo-compiler::gen-defined-call name arity nil nil)))
         (after (generated-link-to target before)))
    (implies (and (unsigned-byte-p 64 target) (< (+ 4 pc) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (not (equal pc target))
                  (proof-compiled-entry-p pc args before objects packages)
                  (generated-linked-item-p item (list :branch (- target pc) t) pc base labels before))
             (and (proof-segment-p 1 (list target) before :cut after)
                  (proof-compiled-entry-p target args after objects packages)
                  (equal (proof-world-reg 30 after) (+ 4 pc)))))
  :hints (("Goal"
           :use ((:instance generated-defined-call-link (arity (len args)))
                 (:instance generated-compiled-entry-ignores-other-registers
                            (before (generated-link-to (proof-label-address (list :fn name) base labels)
                                                       before))
                            (after before)))))
  :rule-classes nil)

(defthm generated-defined-call-returns-to-continuation
  (let* ((pc (proof-world-pc before))
         (entry (generated-link-to target before))
         (top (- (proof-stack-top before) (* 8 arity))))
    (implies (and (< (+ 4 pc) (expt 2 64))
                  (proof-compiled-return-p arity result entry after old-objects new-objects packages))
             (and (equal (proof-world-pc after) (+ 4 pc))
                  (equal (proof-stack-top after) top)
                  (equal (generated-sp after) (generated-sp before))
                  (proof-prefix-preserved-p top before after old-objects new-objects packages)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages))))
  :hints (("Goal" :in-theory (enable generated-link-to generated-heap-machine-sp proof-stack-top
                                    proof-prefix-preserved-p proof-compiled-return-p
                                    proof-frame-return-p)))
  :rule-classes nil)

(defun generated-tail-epilogue-path (arity target before)
  (list (list :arithmetic-imm 0 64 25 19 (* 8 arity))
        '(:pair t 31 19 30 :post 16)
        (list :branch (- target (+ (proof-world-pc before) 8)) nil)))

(defthm generated-tail-epilogue-installs-callee-frame
  (let* ((pc (proof-world-pc before))
         (sp (generated-sp before))
         (new-top (+ (proof-world-reg 19 before) (* 8 arity)))
         (path (generated-tail-epilogue-path arity target before))
         (after (generated-path-after path before)))
    (implies (and (natp arity) (< (* 8 arity) 4096) (unsigned-byte-p 64 target)
                  (< (+ pc 8) (expt 2 64)) (< (+ sp 16) (expt 2 64))
                  (< new-top (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (generated-path-p path (list target) before))
             (and (proof-segment-p 3 (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (generated-sp after) (+ sp 16))
                  (equal (proof-world-reg 25 after) new-top)
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                  (equal (generated-load-word address after)
                         (generated-load-word address before)))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-tail-epilogue-path arity target before))
                           (cuts (list target)))
           :in-theory (disable generated-path-p)))
  :rule-classes nil)
