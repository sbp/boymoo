(in-package "BOYMOO-PROOFS")

(include-book "return-heap")
(include-book "growth")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-stack-top
                    proof-stack-limit proof-stack-base proof-stack-end proof-machine-limit proof-instruction-effect
                    proof-heap-layout-p proof-span-p proof-subspan-p proof-disjoint-p proof-heap-frame-p
                    proof-frame-return-p proof-runtime-return-p proof-compiled-return-p proof-register-frame-p
                    proof-memory-span-agrees-p proof-preserved-heap-p proof-datum-return-p proof-runtime-value
                    generated-path-after generated-sp generated-load-word generated-store-word expt))

(defund generated-saved-machine-frame-preserved-p (before after)
  (let ((sp (generated-sp before)))
    (and (equal (generated-sp after) sp)
         (equal (generated-load-word sp after) (generated-load-word sp before))
         (equal (generated-load-word (+ sp 8) after) (generated-load-word (+ sp 8) before)))))

(defthm generated-saved-machine-frame-preservation-composes
  (implies (and (generated-saved-machine-frame-preserved-p first middle)
                (generated-saved-machine-frame-preserved-p middle last))
           (generated-saved-machine-frame-preserved-p first last))
  :hints (("Goal" :in-theory (enable generated-saved-machine-frame-preserved-p)))
  :rule-classes nil)

(defthm generated-pure-heap-observations-preserve-saved-machine-frame
  (implies (generated-heap-world-equiv after before)
           (generated-saved-machine-frame-preserved-p before after))
  :hints (("Goal" :in-theory (enable generated-saved-machine-frame-preserved-p generated-load-word)))
  :rule-classes nil)

(local
 (defthm generated-shared-heap-frame-keeps-saved-machine-words
   (let ((sp (generated-sp before)) (end (generated-machine-stack-end before)))
     (implies (and (proof-heap-frame-p before after) (equal (generated-sp after) sp)
                   (<= (+ sp 16) end) (<= (+ sp 16) (expt 2 64)))
              (generated-saved-machine-frame-preserved-p before after)))
   :hints (("Goal"
            :use ((:instance generated-read-in-agreeing-span (count 8) (start (generated-sp before))
                             (end (generated-machine-stack-end before)) (address (generated-sp before)))
                  (:instance generated-read-in-agreeing-span (count 8) (start (generated-sp before))
                             (end (generated-machine-stack-end before)) (address (+ (generated-sp before) 8))))
            :in-theory (enable generated-saved-machine-frame-preserved-p generated-machine-stack-end
                               generated-machine-stack-base generated-load-word proof-load-word boymoo-model::a64-load
                               proof-heap-frame-p generated-heap-machine-sp)))
   :rule-classes nil))

(defthm generated-runtime-and-compiled-returns-preserve-saved-machine-frame
  (let ((sp (generated-sp before)))
    (implies (and (<= (+ sp 16) (generated-machine-stack-end before)) (<= (+ sp 16) (expt 2 64))
                  (or (proof-runtime-return-p name args program before after old-objects new-objects packages)
                      (proof-compiled-return-p arity result before after old-objects new-objects packages)))
             (generated-saved-machine-frame-preserved-p before after)))
  :hints (("Goal" :use generated-shared-heap-frame-keeps-saved-machine-words
                  :in-theory (enable proof-runtime-return-p proof-compiled-return-p proof-datum-return-p
                                     proof-preserved-heap-p proof-frame-return-p generated-heap-machine-sp)))
  :rule-classes nil)

(local
 (defthm generated-value-push-does-not-overlap-saved-machine-words
   (let ((sp (generated-sp before)) (top (proof-stack-top before)))
     (implies (and (proof-heap-layout-p before) (<= (+ top 8) (proof-stack-limit before))
                   (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before)))
              (and (proof-span-p top 8) (proof-span-p sp 8) (proof-span-p (+ sp 8) 8)
                   (proof-disjoint-p sp (+ sp 8) top (+ top 8))
                   (proof-disjoint-p (+ sp 8) (+ sp 16) top (+ top 8)))))
   :hints (("Goal" :use (:instance generated-heap-layout-value-stack-bounds (world before))
                   :in-theory (enable proof-heap-layout-p proof-span-p proof-subspan-p proof-disjoint-p proof-stack-top
                                      generated-machine-stack-base generated-machine-stack-end)))
   :rule-classes nil))

(defthm generated-operand-push-preserves-saved-machine-frame
  (let* ((sp (generated-sp before)) (top (proof-stack-top before))
         (after (generated-path-after *generated-push-path* before)))
    (implies (and (proof-heap-layout-p before) (<= (+ top 8) (proof-stack-limit before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                  (generated-ordinary-machine-p before))
             (generated-saved-machine-frame-preserved-p before after)))
  :hints (("Goal"
           :use (generated-value-push-does-not-overlap-saved-machine-words
                 (:instance generated-load-after-word-store-disjoint (query (generated-sp before))
                            (address (proof-stack-top before)) (value (proof-world-reg 0 before)) (world before))
                 (:instance generated-load-after-word-store-disjoint (query (+ (generated-sp before) 8))
                            (address (proof-stack-top before)) (value (proof-world-reg 0 before)) (world before)))
           :in-theory (enable generated-saved-machine-frame-preserved-p generated-path-after proof-stack-top)))
  :rule-classes nil)
