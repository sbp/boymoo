(in-package "BOYMOO-PROOFS")

(include-book "returns")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-execute proof-instruction-effect
                     proof-segment-p proof-number-checked-block-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-stop proof-reg proof-load-word
                     proof-instruction-at-p proof-instruction-access-p proof-world-reg
                     proof-world-pc proof-heap-base proof-reg-value-p
                     boymoo-model::a64-unsigned boymoo-model::a64-signed boymoo-model::a64-memory
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-pc boymoo-model::a64-sp boymoo-model::a64-set-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-nzcv
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand mod floor ash oddp)))

(local
 (defthm truncated-word-parity
   (implies (integerp word)
            (equal (oddp (boymoo-model::a64-unsigned 64 word)) (oddp word)))
   :hints (("Goal"
            :use ((:instance proof-number-logand-parity
                             (a word) (b (boymoo-model::a64-ones 64))))
            :in-theory (e/d (boymoo-model::a64-unsigned boymoo-model::a64-ones)
                            (proof-number-a64-unsigned-in-range proof-number-integer-parity))))))

(local
 (defthm register-and-parity
   (equal (oddp (logand (proof-reg left machine) (proof-reg right machine)))
          (and (oddp (proof-reg left machine)) (oddp (proof-reg right machine))))
   :hints (("Goal"
            :use ((:instance proof-number-logand-parity
                             (a (proof-reg left machine)) (b (proof-reg right machine))))
            :in-theory (disable proof-number-integer-parity)))))

(local
 (defthm read-value-register
   (equal (boymoo-model::a64-read-reg register 64 nil machine) (proof-reg register machine))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(local
 (defthm execute-and-registers
   (equal (proof-execute (list :logical-reg 0 64 dest left right 0 0 nil) machine)
          (boymoo-model::a64-write-reg
           dest 64 nil (logand (proof-reg left machine) (proof-reg right machine))
           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
   :hints (("Goal"
            :in-theory (e/d (proof-execute) (boymoo-model::a64-pc))
            :do-not-induct t))))

; Each row gives a public primitive, its general entry and its arity.
(defconst *proof-number-tag-gates*
  '(("prim:ACL2::BINARY-+" "rt:n-add" 2)
    ("prim:ACL2::BINARY-*" "rt:n-multiply" 2)
    ("prim:ACL2::UNARY--" "rt:n-negate" 1)
    ("prim:ACL2::UNARY-/" "rt:n-reciprocal" 1)
    ("prim:COMMON-LISP::<" "rt:n-less" 2)))

(defund proof-number-tag-gate-instructions (arity entry general)
  (if (equal arity 2)
      (list '(:logical-reg 0 64 2 0 1 0 0 nil)
            '(:logical-imm 3 64 31 2 1)
            (list :branch-cond (- general (+ entry 8)) 0))
    (list '(:logical-imm 3 64 31 0 1)
          (list :branch-cond (- general (+ entry 4)) 0))))

(defun proof-number-tag-gates-decode-p (rows labels)
  (if (endp rows)
      t
    (let* ((row (car rows))
           (name (car row))
           (general (boymoo-compiler::a64-offset (cadr row) labels))
           (arity (caddr row))
           (entry (boymoo-compiler::a64-offset name labels))
           (items (cdr (take (+ 2 arity) (proof-number-code-at-label
                                        name (boymoo-compiler::runtime-primitive-code))))))
      (and (equal (proof-number-decode-items items entry labels)
                  (proof-number-tag-gate-instructions arity entry general))
           (proof-number-tag-gates-decode-p (cdr rows) labels)))))

(defthm proof-number-public-tag-gates-decode
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (proof-number-tag-gates-decode-p *proof-number-tag-gates* labels))
  :rule-classes nil)

(defund proof-number-immediate-less-instructions (entry yes no)
  (list '(:arithmetic-reg 3 64 31 0 1 0 0)
        (list :branch-cond (- yes (+ 4 entry)) 11)
        (list :branch (- no (+ 8 entry)) nil)))

(defthm proof-number-immediate-less-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((name "prim:COMMON-LISP::<")
           (entry (+ 12 (boymoo-compiler::a64-offset name labels)))
           (yes (boymoo-compiler::a64-offset "rt:true" labels))
           (no (boymoo-compiler::a64-offset "rt:nil" labels))
           (items (take 3 (nthcdr 4 (proof-number-code-at-label
                                    name (boymoo-compiler::runtime-primitive-code))))))
      (equal (proof-number-decode-items items entry labels)
             (proof-number-immediate-less-instructions entry yes no))))
  :rule-classes nil)

(local
 (defthm immediate-order-condition
   (let ((left (proof-integer-word a)) (right (proof-integer-word b)))
     (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b))
              (equal (boymoo-model::a64-condition 11 (proof-number-subtraction-flags left right))
                     (< a b))))
   :hints (("Goal"
            :use ((:instance proof-number-subtraction-conditions
                             (left (proof-integer-word a)) (right (proof-integer-word b))))
            :in-theory (disable proof-integer-word proof-number-immediate-word-bits)
            :cases ((< a b))))
   :rule-classes nil))

(defthm proof-number-immediate-less-selects-boolean
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (count (if (< a b) 2 3))
         (target (if (< a b) yes no))
         (path (take count (proof-number-immediate-less-instructions entry yes no)))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (equal (proof-world-reg 1 world) (proof-integer-word b))
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 8 entry))
                  (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                  (proof-number-checked-block-p path (list target) world))
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use (immediate-order-condition
                 (:instance proof-number-checked-block-segment
                            (instructions (take (if (< a b) 2 3)
                                                (proof-number-immediate-less-instructions
                                                 (proof-world-pc world) yes no)))
                            (cuts (list (if (< a b) yes no)))))
           :in-theory (e/d (proof-number-immediate-less-instructions proof-world-reg
                            proof-world-pc proof-heap-base)
                           (proof-integer-word proof-number-immediate-word-bits))
           :cases ((< a b))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-tag-gate
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (code (proof-number-tag-gate-instructions arity entry general))
         (count (1+ arity))
         (body (+ entry (* 4 count)))
         (immediate (and (oddp (proof-world-reg 0 world))
                         (or (equal arity 1) (oddp (proof-world-reg 1 world)))))
         (target (if immediate body general))
         (after (proof-number-execute-block code world)))
    (implies (and (member-equal arity '(1 2))
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 body) (unsigned-byte-p 64 general)
                  (proof-number-checked-block-p code (list target) world))
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-tag-gate-instructions
                                           arity (proof-world-pc world) general))
                            (cuts (list (if (and (oddp (proof-world-reg 0 world))
                                                (or (equal arity 1) (oddp (proof-world-reg 1 world))))
                                           (+ (proof-world-pc world) (* 4 (1+ arity)))
                                         general)))))
           :in-theory (e/d (proof-number-tag-gate-instructions proof-world-reg
                            proof-world-pc proof-heap-base)
                           (proof-number-integer-parity))
           :cases ((equal arity 1))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-immediate-less-selection (a b yes no world)
  (proof-number-execute-block
   (take (if (< a b) 2 3) (proof-number-immediate-less-instructions (proof-world-pc world) yes no))
   world))

(local
 (defthm world-pc-is-natural
   (natp (proof-world-pc world))
   :hints (("Goal" :in-theory (enable proof-world-pc)))
   :rule-classes :type-prescription))

(defund proof-number-immediate-less-body-pre-p (a b yes no world)
  (let* ((entry (proof-world-pc world))
         (target (if (< a b) yes no))
         (count (if (< a b) 2 3))
         (path (take count (proof-number-immediate-less-instructions entry yes no)))
         (selected (proof-number-immediate-less-selection a b yes no world))
         (leaf (if (< a b) "rt:true" "rt:nil"))
         (leaf-code (cdr (assoc-equal leaf *proof-number-leaf-returns*)))
         (link (proof-world-reg 30 world)))
    (and (unsigned-byte-p 64 (+ 8 entry))
         (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
         (unsigned-byte-p 64 (+ 4 target))
         (not (eq (car (proof-world-machine world)) :svc))
         (not (eq (car (proof-world-machine selected)) :svc))
         (proof-number-checked-block-p path (list target) world)
         (proof-number-checked-block-p leaf-code (list link) selected)
         (proof-number-cut-free-prefix-p count (list target link) world))))

(defund proof-number-immediate-less-after (a b yes no world)
  (let ((leaf (if (< a b) "rt:true" "rt:nil")))
    (proof-number-execute-block
     (cdr (assoc-equal leaf *proof-number-leaf-returns*))
     (proof-number-immediate-less-selection a b yes no world))))

(defthm proof-number-immediate-less-body-returns-word
  (let* ((link (proof-world-reg 30 world))
         (after (proof-number-immediate-less-after a b yes no world)))
    (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (equal (proof-world-reg 1 world) (proof-integer-word b))
                  (proof-number-immediate-less-body-pre-p a b yes no world))
             (and (proof-segment-p (if (< a b) 4 5) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 0 after) (if (< a b) *proof-t* *proof-nil*))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world))))))
  :hints (("Goal"
           :use (proof-number-immediate-less-selects-boolean
                 (:instance proof-number-leaf-returns-word
                            (name (if (< a b) "rt:true" "rt:nil")) (register 30)
                            (world (proof-number-immediate-less-selection a b yes no world)))
                 (:instance proof-number-compose-segments
                            (prefix (if (< a b) 2 3)) (suffix 2)
                            (first-cuts (list (if (< a b) yes no)))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-immediate-less-selection a b yes no world))
                            (after (proof-number-immediate-less-after a b yes no world))))
           :in-theory (e/d (proof-number-immediate-less-body-pre-p proof-number-immediate-less-after
                            proof-number-leaf-result-word proof-number-immediate-less-selection)
                           (proof-number-execute-block proof-integer-word
                            proof-number-immediate-word-bits proof-number-integer-parity))
           :cases ((< a b))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-immediate-less-returns-word
  (let* ((entry (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (target (+ 12 entry))
         (code (proof-number-tag-gate-instructions 2 entry general))
         (body (proof-number-execute-block code world))
         (after (proof-number-immediate-less-after a b yes no body)))
    (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (equal (proof-world-reg 1 world) (proof-integer-word b))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 general)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (proof-number-checked-block-p code (list target) world)
                  (proof-number-cut-free-prefix-p 3 (list target link) world)
                  (proof-number-immediate-less-body-pre-p a b yes no body))
             (and (proof-segment-p (if (< a b) 7 8) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 0 after) (if (< a b) *proof-t* *proof-nil*))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance proof-number-public-tag-gate (arity 2))
                 (:instance proof-number-immediate-less-body-returns-word
                            (world (proof-number-execute-block
                                    (proof-number-tag-gate-instructions
                                     2 (proof-world-pc world) general) world)))
                 (:instance proof-number-compose-segments
                            (prefix 3) (suffix (if (< a b) 4 5))
                            (first-cuts (list (+ 12 (proof-world-pc world))))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-execute-block
                                     (proof-number-tag-gate-instructions
                                      2 (proof-world-pc world) general) world))
                            (after (proof-number-immediate-less-after
                                    a b yes no (proof-number-execute-block
                                                (proof-number-tag-gate-instructions
                                                 2 (proof-world-pc world) general) world)))))
           :in-theory (disable proof-number-execute-block proof-integer-word
                               proof-number-immediate-word-bits proof-number-integer-parity)
           :cases ((< a b))
           :do-not-induct t))
  :rule-classes nil)
