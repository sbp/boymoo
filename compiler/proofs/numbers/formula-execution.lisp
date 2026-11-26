(in-package "BOYMOO-PROOFS")

(include-book "publication")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                     boymoo-model::a64-write-reg boymoo-model::a64-load
                     boymoo-model::a64-store boymoo-model::a64-read-bytes
                     boymoo-model::a64-pc boymoo-model::a64-nzcv boymoo-model::a64-sp
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory
                     proof-execute proof-instruction-effect proof-reg proof-load-word
                     proof-world-machine proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-run proof-segment-p proof-view proof-value-p
                     proof-number-checked-block-p
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

(defund proof-number-formula-grow-instructions (entry grow bytes)
  (list '(:pair nil 31 19 30 :pre -16)
        '(:logical-reg 1 64 19 31 25 0 0 nil)
        (list :arithmetic-imm 0 64 8 25 bytes)
        (list :branch (- grow (+ entry 12)) t)))

(defund proof-number-formula-argument-store-instructions (arity)
  (if (equal arity 1)
      '((:single 0 8 25 0 :offset 0) (:arithmetic-imm 0 64 25 25 8))
    '((:pair nil 25 0 1 :offset 0) (:arithmetic-imm 0 64 25 25 16))))

(defconst *proof-number-formula-spill-instructions*
  '((:single 0 8 25 0 :offset 0)
    (:arithmetic-imm 0 64 25 25 8)))

(defconst *proof-number-formula-return-instructions*
  '((:logical-reg 1 64 25 31 19 0 0 nil)
    (:pair t 31 19 30 :post 16)
    (:branch-reg 30 nil)))

(defun proof-number-formula-load-instructions (indices register)
  (if (endp indices)
      nil
    (cons (list :single 1 8 19 register :offset (* 8 (car indices)))
          (proof-number-formula-load-instructions (cdr indices) (1+ register)))))

(defun proof-number-formula-call-instructions (indices entry target)
  (append (proof-number-formula-load-instructions indices 0)
          (list (list :branch (- target (+ entry (* 4 (len indices)))) t))))

(defun proof-number-formula-body-instructions (calls entry labels)
  (if (endp calls)
      *proof-number-formula-return-instructions*
    (let* ((target (boymoo-compiler::a64-offset (caar calls) labels))
           (call (proof-number-formula-call-instructions (cdar calls) entry target))
           (spill (if (consp (cdr calls)) *proof-number-formula-spill-instructions* nil))
           (next (+ entry (* 4 (+ (len call) (len spill))))))
      (append call spill (proof-number-formula-body-instructions (cdr calls) next labels)))))

(defun proof-number-formula-decoding-list-p (formulas labels)
  (if (endp formulas)
      t
    (let* ((name (caar formulas))
           (arity (cadar formulas))
           (calls (caddar formulas))
           (entry (boymoo-compiler::a64-offset name labels))
           (grow (boymoo-compiler::a64-offset "rt:ensure-stack" labels))
           (bytes (* 8 (+ arity (1- (len calls)))))
           (items (cdr (boymoo-compiler::runtime-number-formula name arity calls))))
      (and (equal (proof-number-decode-items items entry labels)
                  (append (proof-number-formula-grow-instructions entry grow bytes)
                          (proof-number-formula-argument-store-instructions arity)
                          (proof-number-formula-body-instructions calls (+ entry 24) labels)))
           (proof-number-formula-decoding-list-p (cdr formulas) labels)))))

(defthm proof-number-generated-formula-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (proof-number-formula-decoding-list-p *proof-number-formulas* labels))
  :rule-classes nil)

(defthm proof-number-formula-calls-growth
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (code (proof-number-formula-grow-instructions entry grow bytes))
         (ready (proof-number-execute-block code world))
         (ready-machine (proof-world-machine ready))
         (needed (+ (proof-stack-top world) bytes)))
    (implies (and (proof-number-checked-block-p code (list grow) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p saved 16)
                  (unsigned-byte-p 64 (+ 16 entry))
                  (unsigned-byte-p 64 grow)
                  (unsigned-byte-p 64 needed))
             (and (proof-segment-p 4 (list grow) world :cut ready)
                  (equal (proof-world-pc ready) grow)
                  (equal (proof-world-reg 30 ready) (+ 16 entry))
                  (equal (boymoo-model::a64-sp ready-machine) saved)
                  (equal (proof-world-reg 0 ready) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 ready) (proof-world-reg 1 world))
                  (equal (proof-world-reg 8 ready) needed)
                  (equal (proof-world-reg 19 ready) (proof-stack-top world))
                  (equal (proof-stack-top ready) (proof-stack-top world))
                  (equal (proof-load-word saved ready-machine) (proof-world-reg 19 world))
                  (equal (proof-load-word (+ 8 saved) ready-machine) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-formula-grow-instructions
                                           (proof-world-pc world) grow bytes))
                            (cuts (list grow))))
           :in-theory (enable proof-number-formula-grow-instructions)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-loads-call-arguments
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (frame (proof-world-reg 19 world))
         (arity (len indices))
         (count (1+ arity))
         (code (proof-number-formula-call-instructions indices entry target))
         (ready (proof-number-execute-block code world))
         (ready-machine (proof-world-machine ready)))
    (implies (and (consp indices)
                  (or (null (cdr indices))
                      (and (consp (cdr indices)) (null (cddr indices))))
                  (proof-number-checked-block-p code (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ entry (* 4 count)))
                  (unsigned-byte-p 64 target))
             (and (proof-segment-p count (list target) world :cut ready)
                  (equal (proof-world-pc ready) target)
                  (equal (proof-world-reg 30 ready) (+ entry (* 4 count)))
                  (equal (proof-world-reg 0 ready)
                         (proof-load-word (+ frame (* 8 (car indices))) machine))
                  (implies (equal arity 2)
                           (equal (proof-world-reg 1 ready)
                                  (proof-load-word (+ frame (* 8 (cadr indices))) machine)))
                  (equal (proof-world-reg 19 ready) frame)
                  (equal (proof-stack-top ready) (proof-stack-top world))
                  (equal (proof-heap-base ready) (proof-heap-base world))
                  (equal (boymoo-model::a64-memory ready-machine)
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-formula-call-instructions
                                           indices (proof-world-pc world) target))
                            (cuts (list target))))
           :cases ((consp (cdr indices)))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm loaded-slot-represents-argument
   (implies (and (proof-number-frame-p start slots world objects packages)
                 (integerp (proof-stack-base world))
                 (natp index) (< index (len slots))
                 (equal (proof-world-reg register ready)
                        (proof-load-word
                         (+ (proof-number-frame-address start world) (* 8 index))
                         (proof-world-machine world)))
                 (equal (proof-heap-base ready) (proof-heap-base world))
                 (equal (boymoo-model::a64-memory (proof-world-machine ready))
                        (boymoo-model::a64-memory (proof-world-machine world))))
            (proof-reg-value-p register (nth index slots) ready objects packages))
   :hints (("Goal"
            :use (proof-number-frame-slot-value
                  (:instance proof-number-view-kept-with-memory
                             (word (proof-world-reg register ready))
                             (base (proof-heap-base world))
                             (first (proof-world-machine world))
                             (last (proof-world-machine ready))))
            :in-theory (e/d (proof-value-p) (proof-number-frame-address proof-heap-base nth))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-formula-passes-slot-values
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (count (1+ (len indices)))
         (code (proof-number-formula-call-instructions indices entry target))
         (ready (proof-number-execute-block code world)))
    (implies (and (consp indices)
                  (or (null (cdr indices))
                      (and (consp (cdr indices)) (null (cddr indices))))
                  (proof-number-slot-indices-p indices (len slots))
                  (proof-number-frame-p start slots world objects packages)
                  (equal (proof-world-reg 19 world) (proof-number-frame-address start world))
                  (proof-number-checked-block-p code (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ entry (* 4 count)))
                  (unsigned-byte-p 64 target))
             (and (proof-segment-p count (list target) world :cut ready)
                  (proof-number-frame-p start slots ready objects packages)
                  (proof-register-arguments-p (proof-number-slot-arguments indices slots)
                                              0 ready objects packages))))
  :hints (("Goal"
           :use (proof-number-formula-loads-call-arguments
                 (:instance proof-number-frame-kept-with-memory
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-formula-call-instructions
                                     indices (proof-world-pc world) target) world)))
                 (:instance loaded-slot-represents-argument
                            (index (car indices)) (register 0)
                            (ready (proof-number-execute-block
                                    (proof-number-formula-call-instructions
                                     indices (proof-world-pc world) target) world)))
                 (:instance loaded-slot-represents-argument
                            (index (cadr indices)) (register 1)
                            (ready (proof-number-execute-block
                                    (proof-number-formula-call-instructions
                                     indices (proof-world-pc world) target) world))))
           :in-theory (disable proof-number-execute-block proof-number-formula-call-instructions
                               proof-reg-value-p proof-number-frame-address proof-heap-base nth)
           :cases ((consp (cdr indices)))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-writes-arguments
  (let* ((machine (proof-world-machine world))
         (top (proof-stack-top world))
         (end (+ top (* 8 arity)))
         (code (proof-number-formula-argument-store-instructions arity))
         (after (proof-number-execute-block code world))
         (after-machine (proof-world-machine after)))
    (implies (and (member-equal arity '(1 2))
                  (not (eq (car machine) :svc))
                  (proof-span-p top (* 8 arity))
                  (unsigned-byte-p 64 end)
                  (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
                  (proof-number-checked-block-p code (list (+ 8 (proof-world-pc world))) world))
             (and (proof-segment-p 2 (list (+ 8 (proof-world-pc world))) world :cut after)
                  (equal (proof-stack-top after) end)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (proof-load-word top after-machine) (proof-world-reg 0 world))
                  (implies (equal arity 2)
                           (equal (proof-load-word (+ 8 top) after-machine)
                                  (proof-world-reg 1 world)))
                  (implies (and (proof-span-p address 8)
                                (proof-disjoint-p address (+ 8 address) top end))
                           (equal (proof-load-word address after-machine)
                                  (proof-load-word address machine))))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-formula-argument-store-instructions arity))
                            (cuts (list (+ 8 (proof-world-pc world))))))
           :in-theory (enable proof-number-formula-argument-store-instructions)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-spills-result
  (let* ((machine (proof-world-machine world))
         (top (proof-stack-top world))
         (pc (+ 8 (proof-world-pc world)))
         (after (proof-number-execute-block *proof-number-formula-spill-instructions* world)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-span-p top 8)
                  (unsigned-byte-p 64 (+ top 8))
                  (unsigned-byte-p 64 pc)
                  (proof-number-checked-block-p *proof-number-formula-spill-instructions*
                                               (list pc) world))
             (and (proof-segment-p 2 (list pc) world :cut after)
                  (equal (proof-stack-top after) (+ 8 top))
                  (equal (proof-load-word top (proof-world-machine after))
                         (proof-world-reg 0 world))
                  (implies (and (proof-span-p address 8)
                                (proof-disjoint-p address (+ 8 address) top (+ 8 top)))
                           (equal (proof-load-word address (proof-world-machine after))
                                  (proof-load-word address machine))))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-writes-arguments (arity 1)))
           :in-theory (enable proof-number-formula-argument-store-instructions)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-spill-extends-frame
  (let* ((machine (proof-world-machine world))
         (top (proof-stack-top world))
         (pc (+ 8 (proof-world-pc world)))
         (after (proof-number-execute-block *proof-number-formula-spill-instructions* world)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-span-p top 8)
                  (unsigned-byte-p 64 (+ top 8))
                  (unsigned-byte-p 64 pc)
                  (proof-number-checked-block-p *proof-number-formula-spill-instructions*
                                               (list pc) world)
                  (proof-number-frame-p start slots world objects packages)
                  (proof-prefix-preserved-p top world after objects objects packages)
                  (proof-machine-value-p (proof-world-reg 0 world) value after objects packages))
             (proof-number-frame-p start (append slots (list value)) after objects packages)))
  :hints (("Goal"
           :use (proof-number-formula-spills-result
                 (:instance proof-number-frame-after-appending-slot
                            (before world) (old-objects objects)
                            (after (proof-number-execute-block
                                    *proof-number-formula-spill-instructions* world))))
           :in-theory (disable proof-number-execute-block proof-prefix-preserved-p
                               proof-stack-top proof-machine-value-p)))
  :rule-classes nil)

(defthm proof-number-formula-restores-frame
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (link (proof-load-word (+ 8 stack) machine))
         (after (proof-number-execute-block *proof-number-formula-return-instructions* world))
         (after-machine (proof-world-machine after)))
    (implies (and (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 stack))
                  (proof-number-checked-block-p *proof-number-formula-return-instructions*
                                               (list link) world))
             (and (proof-segment-p 3 (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 19 after) (proof-load-word stack machine))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (proof-stack-top after) (proof-world-reg 19 world))
                  (equal (boymoo-model::a64-sp after-machine) (+ 16 stack))
                  (equal (boymoo-model::a64-memory after-machine)
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions *proof-number-formula-return-instructions*)
                            (cuts (list (proof-load-word
                                         (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))
                                         (proof-world-machine world))))))
           :do-not-induct t))
  :rule-classes nil)
