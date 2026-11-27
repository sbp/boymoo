(in-package "BOYMOO-PROOFS")

(include-book "calls")
(include-book "copy-path")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-world-reg
                    proof-world-pc proof-world-stop generated-sp generated-load-word
                    generated-copy-words generated-read-words boymoo-model::a64-unsigned
                    boymoo-compiler::gen-defined-call boymoo-compiler::gen-copy-arguments
                    boymoo-compiler::gen-address expt))

(defun generated-tail-immediate-items (name arity)
  (append (if (zp arity) nil
            (cons (list :sub 10 25 (* 8 arity)) (generated-copy-immediate-items arity 0)))
          (list (list :add 25 19 (* 8 arity)) '(:ldp-post 19 30 31 16) (list :b (list :fn name)))))

(defthm generated-tail-immediate-emission
  (implies (and (natp arity) (< (* 8 arity) 4096))
           (equal (boymoo-compiler::gen-defined-call name arity t code)
                  (boymoo-compiler::reverse-onto (generated-tail-immediate-items name arity) code)))
  :hints (("Goal" :use ((:instance generated-defined-call-emission (tail t))
                        (:instance generated-copy-immediate-emission (count arity) (offset 0) (code nil))
                        (:instance generated-reverse-onto-of-appended-accumulator
                                   (items (generated-copy-immediate-items arity 0)) (code nil)
                                   (suffix (cons (list :sub 10 25 (* 8 arity)) code))))
                  :in-theory (e/d (boymoo-compiler::gen-address)
                                  (generated-reverse-onto-of-appended-accumulator))))
  :rule-classes nil)

(defun generated-tail-prefix (arity)
  (if (zp arity) nil
    (cons (list :arithmetic-imm 2 64 10 25 (* 8 arity)) (generated-copy-immediate-path arity 0))))

(defund generated-tail-path (arity target before)
  (let* ((prefix (generated-tail-prefix arity))
         (middle (generated-path-after prefix before)))
    (append prefix (generated-tail-epilogue-path arity target middle))))

(local
 (defthm generated-len-of-append
   (equal (len (append first second)) (+ (len first) (len second)))))

(defthm generated-tail-prefix-length
  (equal (len (generated-tail-prefix arity))
         (if (zp arity) 0 (1+ (* 2 (nfix arity))))))

(defthm generated-tail-immediate-path-length
  (implies (natp arity)
           (equal (len (generated-tail-path arity target before))
                  (+ (if (zp arity) 0 1) (* 2 arity) 3)))
  :hints (("Goal" :in-theory (enable generated-tail-path))))

(defthm generated-tail-prefix-transfers-words
  (let* ((frame (proof-world-reg 19 before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (pc (+ (proof-world-pc before) (if (zp arity) 0 4) bytes))
         (middle (generated-path-after (generated-tail-prefix arity) before)))
    (implies (and (natp arity) (< bytes 4096) (<= frame source)
                  (< pc (expt 2 64)) (generated-ordinary-machine-p before))
             (and (equal (proof-world-pc middle) pc)
                  (equal (proof-world-reg 19 middle) frame)
                  (equal (generated-sp middle) (generated-sp before))
                  (equal (proof-world-stop middle) (proof-world-stop before))
                  (generated-ordinary-machine-p middle)
                  (equal (generated-read-words arity frame middle)
                         (generated-read-words arity source before))
                  (implies (and (proof-span-p address 8)
                                (proof-disjoint-p frame (+ frame bytes) address (+ address 8)))
                           (equal (generated-load-word address middle)
                                  (generated-load-word address before))))))
  :hints (("Goal"
           :in-theory (enable generated-word-block-span-p))
          ("Subgoal 2" :in-theory (enable generated-read-words))))

(defthm generated-tail-immediate-call-transfer
  (let* ((frame (proof-world-reg 19 before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (sp (generated-sp before))
         (path (generated-tail-path arity target before))
         (after (generated-path-after path before)))
    (implies (and (natp arity) (< bytes 4096) (<= frame source)
                  (< (+ (proof-world-pc before) (if (zp arity) 0 4) bytes 8) (expt 2 64))
                  (< (+ sp 16) (expt 2 64))
                  (proof-disjoint-p frame (+ frame bytes) sp (+ sp 16))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (generated-path-p path (list target) before))
             (and (proof-segment-p (+ (if (zp arity) 0 1) (* 2 arity) 3)
                                   (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 25 after) (+ frame bytes))
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                  (equal (generated-sp after) (+ sp 16))
                  (equal (generated-read-words arity frame after)
                         (generated-read-words arity source before)))))
  :hints (("Goal" :use ((:instance generated-placed-path-to-cut
                                   (instructions (generated-tail-path arity target before))
                                   (cuts (list target)))
                        (:instance generated-tail-prefix-transfers-words (address (generated-sp before)))
                        (:instance generated-tail-prefix-transfers-words (address (+ 8 (generated-sp before)))))
                  :in-theory (e/d (generated-tail-path proof-span-p proof-disjoint-p)
                                  (generated-tail-prefix generated-tail-prefix-transfers-words
                                   generated-path-p))))
  :rule-classes nil)

(defthm generated-tail-callee-return-observations
  (implies (and (natp arity) (natp frame)
                (equal (proof-stack-top entry) (+ frame (* 8 arity)))
                (equal (proof-world-reg 30 entry) saved-link)
                (equal (generated-sp entry) saved-sp)
                (proof-compiled-return-p arity result entry after old-objects new-objects packages))
           (and (equal (proof-world-pc after) saved-link)
                (equal (generated-sp after) saved-sp)
                (equal (proof-stack-top after) frame)
                (proof-prefix-preserved-p frame entry after old-objects new-objects packages)
                (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages)))
  :hints (("Goal" :in-theory (enable proof-compiled-return-p proof-frame-return-p
                                    generated-heap-machine-sp))))
