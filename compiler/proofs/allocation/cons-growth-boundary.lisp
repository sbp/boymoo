(in-package "BOYMOO-PROOFS")

(include-book "cons-root-heap")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-cons-growth-save-leaves-heap-bytes
  (let* ((base (proof-heap-base caller))
         (lower (- base *proof-heap-prefix*))
         (upper (proof-spaces-end caller))
         (writes (allocation-cons-save-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (equal (allocation-memory cut) (allocation-memory (allocation-write-words writes caller))))
             (proof-memory-span-agrees-p lower upper caller cut)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-save-writes-avoid-heap
                 (:instance allocation-layout-storage-spans (world caller))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-cons-save-writes caller)) (world caller) (after cut)
                  (lower (- (proof-heap-base caller) *proof-heap-prefix*)) (upper (proof-spaces-end caller))))
           :in-theory (disable proof-heap-layout-p proof-disjoint-p proof-memory-span-agrees-p
                               allocation-write-words allocation-cons-save-writes
                               allocation-word-writes-avoid-span-p proof-heap-base proof-spaces-end
                               proof-runtime-word allocation-runtime-word-as-load))))

(defthm allocation-protected-heap-preserves-runtime-word
  (let* ((base (proof-heap-base caller))
         (lower (- base *proof-heap-prefix*))
         (upper (proof-spaces-end caller)))
    (implies (and (proof-heap-layout-p caller)
                  (equal (proof-heap-base after) base)
                  (proof-memory-span-agrees-p lower upper caller after)
                  (natp offset) (<= offset 80))
             (equal (proof-runtime-word offset after) (proof-runtime-word offset caller))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-storage-spans (world caller))
                 (:instance allocation-word-in-agreeing-span
                  (before caller) (lower (- (proof-heap-base caller) *proof-heap-prefix*))
                  (upper (proof-spaces-end caller)) (address (+ (- (proof-heap-base caller) 128) offset))))
           :in-theory (e/d (allocation-runtime-word-as-load)
                           (proof-heap-layout-p proof-heap-base proof-static-size proof-stack-base proof-stack-end
                            proof-spaces-end proof-runtime-word proof-memory-span-agrees-p)))))

(defthm allocation-cons-growth-cut-keeps-limits
  (let* ((top (proof-stack-top caller))
         (required (+ top 16)))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller)))
             (and (allocation-cons-growth-edge-p origin caller cut)
                  (equal (proof-heap-base cut) (proof-heap-base caller))
                  (equal (proof-stack-base cut) (proof-stack-base caller))
                  (equal (proof-stack-limit cut) (proof-stack-limit caller))
                  (equal (proof-stack-end cut) (proof-stack-end caller))
                  (<= required (proof-stack-end cut)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-growth-cut-effects allocation-cons-growth-save-leaves-heap-bytes
                 (:instance allocation-protected-heap-preserves-runtime-word (after cut) (offset 40))
                 (:instance allocation-protected-heap-preserves-runtime-word (after cut) (offset 48))
                 (:instance allocation-register-frame-member
                  (before caller) (after cut) (register 28) (upper 30) (clobbers '(2 8 30)))
                 (:instance allocation-register-frame-member
                  (before caller) (after cut) (register 24) (upper 30) (clobbers '(2 8 30))))
           :in-theory (e/d (allocation-cons-prologue-room-p)
                           (allocation-cons-machine-entry-p allocation-cons-growth-edge-p
                            allocation-path-end proof-allocation-fits-p proof-heap-layout-p
                            proof-register-frame-p proof-subspan-p proof-memory-span-agrees-p proof-streams-preserved-p
                            proof-stack-top proof-runtime-word allocation-runtime-word-as-load
                            allocation-cons-save-writes allocation-write-words mod)))))

(defthm allocation-cons-growth-premises-from-linux-layout
  (let ((required (+ 16 (proof-stack-top caller))))
    (implies (and (allocation-cons-machine-entry-p origin caller)
                  (proof-heap-layout-p caller)
                  (allocation-cons-prologue-room-p caller)
                  (not (proof-allocation-fits-p :cons 16 caller))
                  (<= (proof-stack-end caller) (expt 2 63))
                  (equal cut (allocation-path-end *allocation-cons-growth-path* caller)))
             (and (allocation-growth-machine-pre-p "rt:ensure-stack" required origin cut)
                  (<= required (proof-stack-end cut))
                  (allocation-growth-doubling-fits-p cut))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-growth-cut-keeps-limits
                 (:instance allocation-linux-layout-allows-doubling (before caller))
                 (:instance allocation-growth-layout-facts (before caller)))
           :in-theory (e/d (allocation-growth-machine-pre-p allocation-growth-doubling-fits-p)
                           (allocation-path-end proof-heap-layout-p proof-allocation-fits-p
                            proof-stack-base proof-stack-end proof-stack-limit proof-heap-base mod)))))
