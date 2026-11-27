(in-package "BOYMOO-PROOFS")

(include-book "frames")
(include-book "heap-views")
(include-book "source")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-world-reg
                    proof-world-pc proof-world-machine proof-world-stop proof-stack-top
                    proof-stack-prefix proof-reg-value-p proof-machine-value-p proof-heap-p
                    proof-instruction-at-p proof-instruction-access-p proof-constant-map-p
                    proof-constant-word generated-load-word generated-store-word
                    boymoo-model::a64-unsigned boymoo-compiler::gen-term
                    boymoo-compiler::gen-slot boymoo-compiler::gen-datum
                    boymoo-compiler::gen-load-high boymoo-compiler::gen-load-word
                    boymoo-compiler::gen-load-datum boymoo-compiler::gen-frame-word
                    boymoo-compiler::index-get boymoo-model::core-eval-step ash mod floor expt))

(defthm generated-variable-immediate-slot-emission
  (let ((slot (boymoo-compiler::gen-slot compiler-name scope)))
    (implies (and (stringp compiler-name) (natp slot) (< slot 4096))
             (equal (mv-nth 0 (boymoo-compiler::gen-term
                               compiler-name scope depth nil context code high serial))
                    (cons (list :ldr 0 19 (* 8 slot)) code))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term compiler-name scope depth nil context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple
                              boymoo-compiler::gen-frame-word boymoo-compiler::gen-finish))))

(local
 (defthm generated-heap-has-current-prefix
   (implies (proof-heap-p world objects packages)
            (proof-stack-prefix (proof-stack-top world) world objects packages))
   :hints (("Goal" :in-theory (enable proof-heap-p)))))

(defthm generated-variable-immediate-slot-execution
  (let* ((slot (boymoo-compiler::gen-slot compiler-name scope))
         (offset (* 8 slot))
         (frame (proof-world-reg 19 before))
         (pc (proof-world-pc before))
         (instruction (list :single 1 8 19 0 :offset offset))
         (after (proof-instruction-effect instruction before))
         (result (boymoo-model::core-eval-step :term variable env program fuel)))
    (implies (and (stringp compiler-name) (symbolp variable) (posp fuel)
                  (natp slot) (< slot 4096) (< (+ pc 4) (expt 2 64))
                  (proof-heap-p before objects packages)
                  (proof-environment-p bindings env frame before objects packages)
                  (member-equal (cons variable slot) bindings)
                  (not (proof-world-stop before))
                  (generated-linked-item-p (list :ldr 0 19 offset) instruction pc base labels before)
                  (proof-instruction-access-p instruction before))
             (and (proof-segment-p 1 (list (+ pc 4)) before :cut after)
                  (boymoo-model::core-value-p result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                  (proof-environment-p bindings env frame after objects packages)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-environment-binding (world before) (frame (proof-world-reg 19 before))
                            (slot (boymoo-compiler::gen-slot compiler-name scope)))
                 (:instance generated-one-instruction-segment
                            (instruction (list :single 1 8 19 0 :offset
                                               (* 8 (boymoo-compiler::gen-slot compiler-name scope))))
                            (cuts (list (+ 4 (proof-world-pc before))))))
           :in-theory (enable proof-reg-value-p)))
  :rule-classes nil)

(local
 (defthm generated-ash-right-sixteen
   (implies (integerp word) (equal (ash word -16) (floor word 65536)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(defthm generated-small-word-load-emission
  (implies (unsigned-byte-p 16 word)
           (equal (boymoo-compiler::gen-load-word rd word code) (cons (list :movz rd word 0) code)))
  :hints (("Goal" :use (:instance generated-floor-unique (x word) (y 65536) (q 0))
                  :in-theory (enable boymoo-compiler::gen-load-word boymoo-compiler::gen-load-high
                                    boymoo-compiler::low-bits))))

(defthm generated-small-quote-emission
  (let ((word (boymoo-compiler::index-get text (caddr context))))
    (implies (and (stringp text) (unsigned-byte-p 16 word))
             (equal (mv-nth 0 (boymoo-compiler::gen-term
                               (list boymoo-compiler::*quote-name* text)
                               scope depth nil context code high serial))
                    (cons (list :movz 0 word 0) code))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term (list boymoo-compiler::*quote-name* text)
                                             scope depth nil context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple
                              boymoo-compiler::gen-datum boymoo-compiler::gen-load-datum
                              boymoo-compiler::gen-finish))))

(defthm generated-small-quote-execution
  (let* ((word (boymoo-compiler::index-get text (caddr context)))
         (pc (proof-world-pc before))
         (instruction (list :move-wide 2 64 0 word 0))
         (after (proof-instruction-effect instruction before))
         (result (boymoo-model::core-eval-step :term (list 'quote datum) env program fuel)))
    (implies (and (stringp text) (unsigned-byte-p 16 word) (posp fuel)
                  (< (+ pc 4) (expt 2 64)) (not (proof-world-stop before))
                  (proof-heap-p before objects packages)
                  (proof-constant-map-p (list (cons text datum)) (caddr context)
                                        (proof-heap-base before) objects packages
                                        (proof-world-machine before))
                  (generated-linked-item-p (list :movz 0 word 0) instruction pc base labels before))
             (and (proof-segment-p 1 (list (+ pc 4)) before :cut after)
                  (boymoo-model::core-value-p result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after objects objects packages))))
  :hints (("Goal"
           :use (:instance generated-one-instruction-segment
                           (instruction (list :move-wide 2 64 0
                                              (boymoo-compiler::index-get text (caddr context)) 0))
                           (cuts (list (+ 4 (proof-world-pc before)))))
           :in-theory (enable proof-constant-map-p proof-constant-word
                              proof-reg-value-p proof-machine-value-p)))
  :rule-classes nil)

(defun generated-if-path (yes no before)
  (let* ((pc (proof-world-pc before))
         (compare '(:arithmetic-imm 3 64 31 0 34))
         (branch (list :branch-cond (- yes (+ pc 4)) 1)))
    (if (equal (proof-world-reg 0 before) *proof-nil*)
        (list compare branch (list :branch (- no (+ pc 8)) nil))
      (list compare branch))))

(defthm generated-if-dispatch-selects-source-arm
  (let* ((pc (proof-world-pc before))
         (path (generated-if-path yes no before))
         (after (generated-path-after path before))
         (truth (boymoo-model::core-datum test-result)))
    (implies (and (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                  (< (+ pc 8) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (boymoo-model::core-value-p test-result)
                  (equal (equal (proof-world-reg 0 before) *proof-nil*) (not truth))
                  (generated-path-p path (list yes no) before))
             (and (proof-segment-p (len path) (list yes no) before :cut after)
                  (equal (proof-world-pc after) (if truth yes no))
                  (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before)))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-if-path yes no before)) (cuts (list yes no)))
           :in-theory (disable generated-path-p)))
  :rule-classes nil)
