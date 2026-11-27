(in-package "BOYMOO-PROOFS")

(include-book "wide-words")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-instruction-effect proof-segment-p proof-world-reg proof-world-pc
                    proof-world-machine proof-world-stop proof-heap-p proof-stack-prefix proof-stack-top
                    proof-reg-value-p proof-machine-value-p proof-constant-map-p proof-constant-word
                    generated-wide-word-items generated-move-instructions boymoo-model::a64-unsigned
                    boymoo-compiler::gen-term boymoo-compiler::gen-slot boymoo-compiler::gen-frame-word
                    boymoo-compiler::gen-load-datum boymoo-compiler::gen-load-word
                    boymoo-compiler::index-get expt))

(defthm generated-variable-indexed-slot-emission
  (let ((slot (boymoo-compiler::gen-slot compiler-name scope)))
    (implies (and (stringp compiler-name) (natp slot) (<= 4096 slot))
             (equal (mv-nth 0 (boymoo-compiler::gen-term
                               compiler-name scope depth nil context code high serial))
                    (boymoo-compiler::reverse-onto
                     (append (generated-wide-word-items 17 (* 8 slot)) '((:ldr-reg 0 19 17)))
                     code))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term compiler-name scope depth nil context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple
                              boymoo-compiler::gen-frame-word boymoo-compiler::gen-finish))))

(defthm generated-quoted-raw-word-emission
  (let ((word (boymoo-compiler::index-get text (caddr context))))
    (implies (and (stringp text) (unsigned-byte-p 64 word))
             (equal (mv-nth 0 (boymoo-compiler::gen-term
                               (list boymoo-compiler::*quote-name* text)
                               scope depth nil context code high serial))
                    (boymoo-compiler::reverse-onto (generated-wide-word-items 0 word) code))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term (list boymoo-compiler::*quote-name* text)
                                             scope depth nil context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple
                              boymoo-compiler::gen-datum boymoo-compiler::gen-load-datum
                              boymoo-compiler::gen-finish))))

(local
 (defthm generated-wide-terms-heap-prefix
   (implies (proof-heap-p world objects packages)
            (proof-stack-prefix (proof-stack-top world) world objects packages))
   :hints (("Goal" :in-theory (enable proof-heap-p)))))

(local
 (defthm generated-wide-terms-len-of-append
   (equal (len (append first second)) (+ (len first) (len second)))))

(defun generated-variable-indexed-path (slot)
  (append (generated-move-instructions (generated-wide-word-items 17 (* 8 slot)))
          '((:single 1 8 19 0 :register 17 3 0))))

(defthm generated-variable-indexed-slot-execution
  (let* ((slot (boymoo-compiler::gen-slot compiler-name scope))
         (frame (proof-world-reg 19 before))
         (path (generated-variable-indexed-path slot))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path))))
         (result (boymoo-model::core-eval-step :term variable env program fuel)))
    (implies (and (stringp compiler-name) (symbolp variable) (posp fuel)
                  (natp slot) (<= 4096 slot) (unsigned-byte-p 64 (* 8 slot))
                  (< end (expt 2 64)) (not (proof-world-stop before))
                  (proof-heap-p before objects packages)
                  (proof-environment-p bindings env frame before objects packages)
                  (member-equal (cons variable slot) bindings)
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (boymoo-model::core-value-p result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                  (proof-environment-p bindings env frame after objects packages)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-wide-word-loads-value
                            (rd 17) (word (* 8 (boymoo-compiler::gen-slot compiler-name scope))))
                 (:instance generated-environment-binding (world before) (frame (proof-world-reg 19 before))
                            (slot (boymoo-compiler::gen-slot compiler-name scope)))
                 (:instance generated-word-load-bounds (world before)
                            (address (+ (proof-world-reg 19 before)
                                        (* 8 (boymoo-compiler::gen-slot compiler-name scope)))))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-variable-indexed-path
                                           (boymoo-compiler::gen-slot compiler-name scope)))
                            (cuts (list (+ (proof-world-pc before) (* 4 (len
                                          (generated-variable-indexed-path
                                           (boymoo-compiler::gen-slot compiler-name scope)))))))))
           :in-theory (e/d (proof-reg-value-p proof-machine-value-p generated-load-word)
                           (generated-path-p generated-word-load-bounds))))
  :rule-classes nil)

(defthm generated-quoted-raw-word-execution
  (let* ((word (boymoo-compiler::index-get text (caddr context)))
         (path (generated-move-instructions (generated-wide-word-items 0 word)))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path))))
         (result (boymoo-model::core-eval-step :term (list 'quote datum) env program fuel)))
    (implies (and (stringp text) (unsigned-byte-p 64 word) (posp fuel)
                  (< end (expt 2 64)) (not (proof-world-stop before))
                  (proof-heap-p before objects packages)
                  (proof-constant-map-p (list (cons text datum)) (caddr context)
                                        (proof-heap-base before) objects packages
                                        (proof-world-machine before))
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (boymoo-model::core-value-p result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after objects objects packages))))
  :hints (("Goal"
           :use (:instance generated-wide-word-load-continuation
                           (rd 0) (word (boymoo-compiler::index-get text (caddr context))))
           :in-theory (e/d (proof-constant-map-p proof-constant-word
                           proof-reg-value-p proof-machine-value-p)
                          (generated-path-p generated-path-after))))
  :rule-classes nil)
