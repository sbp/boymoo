(in-package "BOYMOO-PROOFS")

(include-book "frames")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-instruction-at-p
                    proof-instruction-access-p proof-world-pc proof-world-reg proof-world-stop
                    proof-label-address generated-load-word generated-sp proof-machine-limit
                    proof-stack-top proof-stack-limit boymoo-model::a64-unsigned expt))

(defthm generated-machine-limit-is-x23
  (equal (proof-machine-limit world) (proof-world-reg 23 world))
  :hints (("Goal" :in-theory (enable proof-machine-limit))))

(defthm generated-value-limit-is-x24
  (equal (proof-stack-limit world) (proof-world-reg 24 world))
  :hints (("Goal" :in-theory (enable proof-stack-limit))))

(defthm generated-value-top-is-x25
  (equal (proof-stack-top world) (proof-world-reg 25 world))
  :hints (("Goal" :in-theory (enable proof-stack-top))))

(defthm generated-prologue-deep-call
  (let* ((pc (proof-world-pc before))
         (label (proof-resource-label :machine-stack))
         (target (proof-label-address label base labels))
         (proposed (- (generated-sp before) 16))
         (after (generated-link-to target before)))
    (implies (and (unsigned-byte-p 64 target) (not (equal pc target))
                  (< (+ 4 pc) (expt 2 64)) (<= 16 (generated-sp before))
                  (< proposed (proof-machine-limit before))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-linked-item-p (list :bl label) (list :branch (- target pc) t)
                                           pc base labels before))
             (and (proof-resource-bound-p :machine-stack proposed before)
                  (proof-segment-p 1 (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ 4 pc)))))
  :hints (("Goal" :use (:instance generated-branch-with-link-transfer
                                  (target (proof-label-address "rt:deep" base labels))
                                  (cuts (list (proof-label-address "rt:deep" base labels)))
                                  (address 0))))
  :rule-classes nil)

(defun generated-value-stack-test-path (bytes)
  (list (list :arithmetic-imm 0 64 0 25 bytes)
        '(:arithmetic-reg 3 64 31 0 24 0 0)
        '(:branch-cond 8 9)))

(defthm generated-prologue-value-stack-check
  (let* ((pc (proof-world-pc before))
         (required (+ (proof-stack-top before) bytes))
         (cuts (list (+ pc 12) (+ pc 16)))
         (path (generated-value-stack-test-path bytes))
         (after (generated-path-after path before)))
    (implies (and (posp bytes) (< bytes 4096) (< required (expt 2 64))
                  (< (+ pc 16) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (proof-instructions-at-p path pc before))
             (and (proof-segment-p 3 cuts before :cut after)
                  (equal (proof-world-pc after)
                         (if (<= required (proof-stack-limit before)) (+ pc 16) (+ pc 12)))
                  (equal (proof-world-reg 0 after) required)
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (equal (generated-sp after) (generated-sp before)))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions (generated-value-stack-test-path bytes))
                                  (cuts (list (+ (proof-world-pc before) 12)
                                              (+ (proof-world-pc before) 16))))))
  :rule-classes nil)

(defthm generated-prologue-grow-link
  (let* ((pc (proof-world-pc before))
         (target (proof-label-address "rt:grow" base labels))
         (after (generated-link-to target before)))
    (implies (and (unsigned-byte-p 64 target) (not (equal pc target))
                  (< (+ 4 pc) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-linked-item-p '(:bl "rt:grow") (list :branch (- target pc) t)
                                           pc base labels before))
             (and (proof-segment-p 1 (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ 4 pc))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (proof-stack-top after) (proof-stack-top before)))))
  :hints (("Goal" :use (:instance generated-branch-with-link-transfer
                                  (target (proof-label-address "rt:grow" base labels))
                                  (cuts (list (proof-label-address "rt:grow" base labels)))
                                  (address 0))
                  :in-theory (enable generated-link-to)))
  :rule-classes nil)

(defthm generated-prologue-sets-immediate-frame-base
  (let* ((pc (proof-world-pc before))
         (bytes (* 8 arity))
         (instruction (list :arithmetic-imm 2 64 19 25 bytes))
         (after (proof-instruction-effect instruction before)))
    (implies (and (natp arity) (< bytes 4096) (<= bytes (proof-stack-top before))
                  (< (+ 4 pc) (expt 2 64))
                  (generated-instruction-p instruction before))
             (and (proof-segment-p 1 (list (+ 4 pc)) before :cut after)
                  (equal (proof-world-reg 19 after) (- (proof-stack-top before) bytes))
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before)))))
  :hints (("Goal" :use (:instance generated-one-instruction-segment
                                  (instruction (list :arithmetic-imm 2 64 19 25 (* 8 arity)))
                                  (cuts (list (+ 4 (proof-world-pc before)))))))
  :rule-classes nil)

(defun generated-prologue-fits-path (arity high)
  (append *generated-prologue-depth-path*
          '((:pair nil 31 19 30 :pre -16))
          (if (< arity high) (generated-value-stack-test-path (* 8 (- high arity))) nil)
          (list (list :arithmetic-imm 2 64 19 25 (* 8 arity)))))

(defthm generated-immediate-prologue-when-frame-fits
  (let* ((pc (proof-world-pc before))
         (top (proof-world-reg 25 before))
         (sp (- (generated-sp before) 16))
         (has-extra (< arity high))
         (extra (* 8 (- high arity)))
         (end (+ pc 24 (if has-extra 16 0)))
         (path (generated-prologue-fits-path arity high))
         (after (generated-path-after path before)))
    (implies (and (natp arity) (natp high) (<= arity high)
                  (< (* 8 arity) 4096) (< extra 4096) (<= (* 8 arity) top)
                  (<= (+ top extra) (proof-world-reg 24 before))
                  (<= 16 (generated-sp before)) (<= (proof-world-reg 23 before) sp)
                  (< end (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (if has-extra 8 5) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ 8 sp) after) (proof-world-reg 30 before))
                  (equal (proof-world-reg 19 after) (- top (* 8 arity)))
                  (equal (proof-world-reg 25 after) top))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions (generated-prologue-fits-path arity high))
                                  (cuts (list (+ (proof-world-pc before) 24 (if (< arity high) 16 0)))))
                  :in-theory (e/d (proof-span-p proof-disjoint-p) (generated-path-p))))
  :rule-classes nil)
