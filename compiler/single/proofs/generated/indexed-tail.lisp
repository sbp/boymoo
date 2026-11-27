(in-package "BOYMOO-PROOFS")

(include-book "addresses")
(include-book "indexed-copy")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-world-reg proof-world-pc proof-world-stop
                    proof-world-machine proof-instruction-effect generated-load-word
                    generated-read-words generated-copy-words generated-sp
                    generated-address-path generated-indexed-copy-path
                    boymoo-compiler::gen-defined-call boymoo-compiler::gen-copy-arguments
                    boymoo-compiler::gen-address boymoo-model::a64-unsigned expt))

(defun generated-indexed-tail-items (name arity)
  (append (if (zp arity) nil
            (generated-address-items 10 25 (* 8 arity) t))
          (generated-indexed-copy-items arity 0)
          (generated-address-items 25 19 (* 8 arity) nil)
          (list '(:ldp-post 19 30 31 16) (list :b (list :fn name)))))

(defthm generated-indexed-tail-emission
  (equal (boymoo-compiler::gen-defined-call name arity t code)
         (boymoo-compiler::reverse-onto (generated-indexed-tail-items name arity) code))
  :hints (("Goal" :use (:instance generated-defined-call-emission (tail t)))))

(defun generated-indexed-tail-prefix (arity)
  (append (if (zp arity) nil
            (generated-address-path 10 25 (* 8 arity) t))
          (generated-indexed-copy-path arity 0)
          (generated-address-path 25 19 (* 8 arity) nil)))

(defund generated-indexed-tail-path (arity target before)
  (let* ((prefix (generated-indexed-tail-prefix arity))
         (middle (generated-path-after prefix before)))
    (append prefix (list '(:pair t 31 19 30 :post 16)
                         (list :branch (- target (+ 4 (proof-world-pc middle))) nil)))))

(local
 (defthm generated-indexed-tail-length-append
   (equal (len (append first second)) (+ (len first) (len second)))))

(local
 (defthm generated-copy-zero-path
   (equal (generated-indexed-copy-path 0 offset) nil)
   :hints (("Goal" :in-theory (enable generated-indexed-copy-path)))))

(local
 (defthm generated-empty-tail-word-block
   (equal (generated-read-words 0 address world) nil)
   :hints (("Goal" :expand (generated-read-words 0 address world)))))

(defthm generated-indexed-tail-prefix-effect
  (let* ((frame (proof-world-reg 19 before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (prefix (generated-indexed-tail-prefix arity))
         (middle (generated-path-after prefix before))
         (pc (+ (proof-world-pc before) (* 4 (len prefix)))))
    (implies (and (natp arity) (unsigned-byte-p 64 bytes) (<= frame source)
                  (< pc (expt 2 64)) (generated-ordinary-machine-p before))
             (and (equal (proof-world-pc middle) pc)
                  (equal (proof-world-reg 19 middle) frame)
                  (equal (proof-world-reg 25 middle) (+ frame bytes))
                  (equal (generated-sp middle) (generated-sp before))
                  (equal (proof-world-stop middle) (proof-world-stop before))
                  (generated-ordinary-machine-p middle)
                  (equal (generated-read-words arity frame middle)
                         (generated-read-words arity source before))
                  (implies (and (proof-span-p address 8)
                                (proof-disjoint-p frame (+ frame bytes) address (+ address 8)))
                           (equal (generated-load-word address middle)
                                  (generated-load-word address before))))))
  :hints (("Goal" :in-theory (enable generated-word-block-span-p))))

(defthm generated-indexed-tail-call-transfer
  (let* ((frame (proof-world-reg 19 before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (sp (generated-sp before))
         (path (generated-indexed-tail-path arity target before))
         (after (generated-path-after path before)))
    (implies (and (natp arity) (unsigned-byte-p 64 bytes) (<= frame source)
                  (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                  (< (+ sp 16) (expt 2 64))
                  (proof-disjoint-p frame (+ frame bytes) sp (+ sp 16))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (generated-path-p path (list target) before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 25 after) (+ frame bytes))
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                  (equal (generated-sp after) (+ sp 16))
                  (equal (generated-read-words arity frame after)
                         (generated-read-words arity source before)))))
  :hints (("Goal" :use ((:instance generated-placed-path-to-cut
                                   (instructions (generated-indexed-tail-path arity target before))
                                   (cuts (list target)))
                        (:instance generated-indexed-tail-prefix-effect (address (generated-sp before)))
                        (:instance generated-indexed-tail-prefix-effect (address (+ 8 (generated-sp before)))))
                  :in-theory (e/d (generated-indexed-tail-path proof-span-p proof-disjoint-p)
                                  (generated-indexed-tail-prefix generated-indexed-tail-prefix-effect
                                   generated-path-p))))
  :rule-classes nil)
