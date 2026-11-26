(in-package "BOYMOO-PROOFS")

(include-book "type-completion")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-load boymoo-model::a64-store
                     boymoo-model::a64-pc boymoo-model::a64-nzcv
                     boymoo-model::a64-sp boymoo-model::a64-set-pc
                     boymoo-model::a64-set-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory proof-execute proof-instruction-effect
                     proof-reg proof-load-word proof-world-machine proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-run proof-segment-p proof-view proof-value-p
                     proof-number-checked-block-p
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

(defconst *proof-number-first-order-code*
  '((:arithmetic-imm 3 64 31 0 1)
    (:select 64 0 0 1 1 nil)
    (:branch-reg 30 nil)))

(defthm proof-number-first-order-decoding
  (equal (proof-number-decode-items
          (cdr (take 4 (proof-number-code-at-label "rt:num-first-order"
                                                   (boymoo-compiler::runtime-rational-code))))
          0 nil)
         *proof-number-first-order-code*)
  :rule-classes nil)

(defthm proof-number-first-order-returns-word
  (let* ((machine (proof-world-machine world))
         (code *proof-number-first-order-code*)
         (link (proof-world-reg 30 world))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-checked-block-p code (list link) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 8 (proof-world-pc world))))
             (and (proof-segment-p 3 (list link) world :cut after)
                  (equal (proof-world-reg 0 after)
                         (proof-world-reg (if (equal (proof-world-reg 0 world) 1) 1 0) world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions *proof-number-first-order-code*)
                            (cuts (list (proof-world-reg 30 world)))))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-first-order-returns-value
  (let* ((machine (proof-world-machine world))
         (code *proof-number-first-order-code*)
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-checked-block-p code (list (proof-world-reg 30 world)) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
                  (proof-reg-value-p 0 first world objects packages)
                  (proof-reg-value-p 1 second world objects packages))
             (proof-reg-value-p 0 (proof-number-first-order first second)
                                after objects packages)))
  :hints (("Goal"
           :use (proof-number-first-order-returns-word
                 (:instance proof-number-tagged-zero-and-one (value first)
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value (proof-number-first-order first second))
                            (before world)
                            (after (proof-number-execute-block *proof-number-first-order-code* world))
                            (word (proof-world-reg (if (equal first 0) 1 0) world))))
           :in-theory (e/d (proof-number-first-order)
                           (proof-number-execute-block proof-world-reg proof-heap-base))))
  :rule-classes nil)

(defund proof-number-less-compare-path (pc rational complex complex-case)
  (list '(:arithmetic-imm 3 64 31 3 5)
        '(:branch-cond 12 0)
        (list :branch (if complex-case (- complex (+ pc 16)) (- rational (+ pc 8))) t)))

(defund proof-number-less-return-code (pc yes no)
  (list '(:pair t 31 29 30 :post 16)
        '(:arithmetic-imm 3 64 31 0 1)
        (list :branch-cond (- yes (+ pc 8)) 11)
        (list :branch (- no (+ pc 12)) nil)))

(defthm proof-number-less-continuations-decode
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((runtime (boymoo-compiler::runtime-primitive-code))
           (pc (+ 8 (boymoo-compiler::a64-offset "rt:n-less" labels)))
           (rational (boymoo-compiler::a64-offset "rt:q-compare" labels))
           (complex (boymoo-compiler::a64-offset "rt:c-compare" labels))
           (yes (boymoo-compiler::a64-offset "rt:true" labels))
           (no (boymoo-compiler::a64-offset "rt:nil" labels))
           (prefix (nthcdr 3 (proof-number-code-at-label "rt:n-less" runtime)))
           (both (proof-number-decode-items (take 4 prefix) pc labels))
           (complex-call (cadr (proof-number-code-at-label "rt:n-less-complex" runtime)))
           (result (boymoo-compiler::a64-offset "rt:n-less-result" labels)))
      (and (equal (take 3 both) (proof-number-less-compare-path pc rational complex nil))
           (equal (nth 3 both) (list :branch (- result (+ pc 12)) nil))
           (equal (append (take 2 both)
                          (proof-number-decode-items (list complex-call) (+ pc 16) labels))
                  (proof-number-less-compare-path pc rational complex t))
           (equal result (+ pc 20))
           (equal (proof-number-decode-items
                   (cdr (take 5 (proof-number-code-at-label "rt:n-less-result" runtime)))
                   result labels)
                  (proof-number-less-return-code result yes no)))))
  :rule-classes nil)

(defthm proof-number-less-calls-comparator
  (let* ((pc (proof-world-pc world))
         (complex-case (equal (proof-world-reg 3 world) 5))
         (target (if complex-case complex rational))
         (code (proof-number-less-compare-path pc rational complex complex-case))
         (after (proof-number-execute-block code world))
         (machine (proof-world-machine world)))
    (implies (and (proof-number-checked-block-p code (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 target)
                  (unsigned-byte-p 64 (+ pc 20)))
             (and (proof-segment-p 3 (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ pc (if complex-case 20 12)))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-less-compare-path
                                           (proof-world-pc world) rational complex
                                           (equal (proof-world-reg 3 world) 5)))
                            (cuts (list (if (equal (proof-world-reg 3 world) 5)
                                           complex rational)))))
           :in-theory (enable proof-number-less-compare-path)
           :do-not-induct t))
  :rule-classes nil)

(defun proof-number-less-return-path (order pc yes no)
  (take (if (equal order -1) 3 4) (proof-number-less-return-code pc yes no)))

(defthm proof-number-less-finishes-comparison
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (path (proof-number-less-return-path order (proof-world-pc world) yes no))
         (target (if (equal order -1) yes no))
         (after (proof-number-execute-block path world)))
    (implies (and (member-equal order '(-1 0 1))
                  (equal (proof-world-reg 0 world) (proof-integer-word order))
                  (proof-number-checked-block-p path (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 target)
                  (unsigned-byte-p 64 (+ 12 (proof-world-pc world)))
                  (unsigned-byte-p 64 (+ 16 stack)))
             (and (proof-segment-p (len path) (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (proof-load-word (+ 8 stack) machine))
                  (equal (proof-world-reg 29 after) (proof-load-word stack machine))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 stack))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-less-return-path
                                           order (proof-world-pc world) yes no))
                            (cuts (list (if (equal order -1) yes no)))))
           :in-theory (enable proof-number-less-return-code)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-less-uses-order-sign
  (equal (equal (proof-number-order a b) -1) (< a b))
  :hints (("Goal" :in-theory (enable proof-number-order))))
