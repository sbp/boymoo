(in-package "BOYMOO-PROOFS")

(include-book "comparisons")
(include-book "placement")
(include-book "copy")
(include-book "emission")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-at-p proof-instruction-access-p
                    proof-instruction-effect proof-world-machine proof-world-reg proof-world-pc
                    proof-world-stop proof-world-regions boymoo-model::a64-unsigned
                    generated-load-word generated-store-word generated-flags generated-sp
                    boymoo-compiler::a64-word boymoo-compiler::gen-defined-call proof-decode
                    proof-label-address expt mod))

(defund generated-link-to (target before)
  (generated-set-reg 30 (+ 4 (proof-world-pc before)) (generated-set-pc target before)))

(defthm generated-branch-with-link-transfer
  (let* ((pc (proof-world-pc before))
         (instruction (list :branch (- target pc) t))
         (after (generated-link-to target before)))
    (implies (and (unsigned-byte-p 64 target) (< (+ 4 pc) (expt 2 64))
                  (generated-ordinary-machine-p before)
                  (generated-instruction-p instruction before)
                  (not (member-equal pc cuts)) (member-equal target cuts))
             (and (proof-segment-p 1 cuts before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ 4 pc))
                  (equal (generated-sp after) (generated-sp before))
                  (equal (generated-flags after) (generated-flags before))
                  (equal (proof-world-reg 25 after) (proof-world-reg 25 before))
                  (equal (generated-load-word address after)
                         (generated-load-word address before)))))
  :hints (("Goal"
           :use (:instance generated-one-instruction-segment
                           (instruction (list :branch (- target (proof-world-pc before)) t)))
           :in-theory (enable generated-link-to)))
  :rule-classes nil)

(defthm generated-defined-call-link
  (let* ((pc (proof-world-pc before))
         (target (proof-label-address (list :fn name) base labels))
         (call (car (boymoo-compiler::gen-defined-call name arity nil nil)))
         (after (generated-link-to target before)))
    (implies (and (unsigned-byte-p 64 target) (< (+ pc 4) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (not (equal pc target))
                  (generated-linked-item-p call (list :branch (- target pc) t) pc base labels
                                           before))
             (and (proof-segment-p 1 (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ pc 4))
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-world-reg 25 after) (proof-world-reg 25 before)))))
  :hints (("Goal" :use (:instance generated-branch-with-link-transfer
                                  (target (proof-label-address (list :fn name) base labels))
                                  (cuts (list (proof-label-address (list :fn name) base labels)))
                                  (address 0))))
  :rule-classes nil)

(defconst *generated-prologue-depth-path*
  '((:arithmetic-imm 2 64 9 31 16)
    (:arithmetic-reg 3 64 31 9 23 0 0)
    (:branch-cond 8 2)))

(defthm generated-prologue-machine-stack-check
  (let* ((pc (proof-world-pc before))
         (proposed (- (generated-sp before) 16))
         (cuts (list (+ pc 12) (+ pc 16)))
         (after (generated-path-after *generated-prologue-depth-path* before)))
    (implies (and (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (<= 16 (generated-sp before)) (< (+ pc 16) (expt 2 64))
                  (proof-instructions-at-p *generated-prologue-depth-path* pc before))
             (and (proof-segment-p 3 cuts before :cut after)
                  (equal (proof-world-pc after)
                         (if (< proposed (proof-machine-limit before)) (+ pc 12) (+ pc 16)))
                  (equal (proof-world-reg 9 after) proposed)
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
                  (equal (proof-world-reg 25 after) (proof-world-reg 25 before)))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions *generated-prologue-depth-path*)
                                  (cuts (list (+ (proof-world-pc before) 12)
                                              (+ (proof-world-pc before) 16))))))
  :rule-classes nil)

(defthm generated-prologue-save-slot-words
  (let* ((instruction '(:pair nil 31 19 30 :pre -16))
         (pc (proof-world-pc before))
         (sp (- (generated-sp before) 16))
         (after (proof-instruction-effect instruction before)))
    (implies (and (generated-ordinary-machine-p before) (<= 16 (generated-sp before))
                  (< (+ pc 4) (expt 2 64)) (generated-instruction-p instruction before))
             (and (proof-segment-p 1 (list (+ pc 4)) before :cut after)
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ sp 8) after) (proof-world-reg 30 before))
                  (equal (proof-world-reg 25 after) (proof-world-reg 25 before)))))
  :hints (("Goal" :use (:instance generated-one-instruction-segment
                                  (instruction '(:pair nil 31 19 30 :pre -16))
                                  (cuts (list (+ 4 (proof-world-pc before)))))))
  :rule-classes nil)

(defconst *generated-return-path*
  '((:logical-reg 1 64 25 31 19 0 0 nil)
    (:pair t 31 19 30 :post 16)
    (:branch-reg 30 nil)))

(defthm generated-return-restores-frame
  (let* ((pc (proof-world-pc before))
         (sp (generated-sp before))
         (link (generated-load-word (+ sp 8) before))
         (after (generated-path-after *generated-return-path* before)))
    (implies (and (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (< (+ pc 8) (expt 2 64)) (< (+ sp 16) (expt 2 64))
                  (not (member-equal link (list pc (+ pc 4) (+ pc 8))))
                  (proof-instructions-at-p *generated-return-path* pc before)
                  (proof-instruction-access-p '(:pair t 31 19 30 :post 16)
                                            (generated-set-reg 25 (proof-world-reg 19 before)
                                                               (generated-set-pc (+ pc 4) before))))
             (and (proof-segment-p 3 (list link) before :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 25 after) (proof-world-reg 19 before))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (generated-sp after) (+ sp 16))
                  (equal (generated-load-word address after)
                         (generated-load-word address before)))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions *generated-return-path*)
                                  (cuts (list (generated-load-word (+ (generated-sp before) 8)
                                                                  before))))))
  :rule-classes nil)
