(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; Offsets are relative to the first instruction of the runtime. The
; assembler supplies the words and the model supplies their decoding.
(defconst *symbols-runtime-labels*
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reversed))
    labels))

(defun symbols-runtime-offset (label)
  (boymoo-compiler::a64-offset label *symbols-runtime-labels*))

(defun symbols-runtime-address (label base)
  (+ base (symbols-runtime-offset label)))

(defun symbols-code-instructions (items offset)
  (if (atom items)
      nil
    (let* ((item (car items))
           (size (boymoo-compiler::a64-image-item-size item))
           (tail (symbols-code-instructions (cdr items) (+ offset size))))
      (if (and (equal size 4) (not (member-eq (car item) '(:bytes :image))))
          (acons offset
                 (proof-decode (boymoo-compiler::a64-word
                                item offset *symbols-runtime-labels*))
                 tail)
        tail))))

(defconst *symbols-runtime-instructions*
  (append (symbols-code-instructions (boymoo-compiler::runtime-primitive-code)
                                     (symbols-runtime-offset "rt:true"))
          (symbols-code-instructions (boymoo-compiler::runtime-sequence-code)
                                     (symbols-runtime-offset "rt:string-view"))
          (symbols-code-instructions (boymoo-compiler::runtime-symbol-code)
                                     (symbols-runtime-offset "rt:symbol-view"))))

(defun symbols-code-path (label displacements)
  (if (atom displacements)
      nil
    (cons (assoc-equal (+ (symbols-runtime-offset label) (car displacements))
                       *symbols-runtime-instructions*)
          (symbols-code-path label (cdr displacements)))))

(defun symbols-replay (path world)
  (if (atom path)
      world
    (symbols-replay (cdr path) (proof-instruction-effect (cdar path) world))))

; This predicate supplies instruction placement and the memory premises
; of the checked machine. The step effects determine the next state.
(defun symbols-path-ready-p (path base cut world)
  (if (atom path)
      (null path)
    (and (consp (car path))
         (not (proof-world-stop world))
         (not (equal (proof-world-pc world) cut))
         (proof-instruction-at-p (cdar path) (+ base (caar path)) world)
         (proof-instruction-access-p (cdar path) world)
         (symbols-path-ready-p (cdr path) base cut
                               (proof-instruction-effect (cdar path) world)))))

(defun symbols-path-control-p (path base world)
  (if (atom path)
      t
    (and (equal (proof-world-pc world) (+ base (caar path)))
         (symbols-path-control-p (cdr path) base
                                 (proof-instruction-effect (cdar path) world)))))

(defthm symbols-replay-is-segment
  (implies (and (symbols-path-ready-p path base cut world)
                (symbols-path-control-p path base world)
                (not (proof-world-stop (symbols-replay path world)))
                (equal (proof-world-pc (symbols-replay path world)) cut))
           (proof-segment-p (len path) (list cut) world :cut
                            (symbols-replay path world)))
  :hints (("Goal" :induct (symbols-path-control-p path base world)
                  :in-theory (disable proof-step proof-instruction-effect
                                      proof-instruction-at-p proof-instruction-access-p
                                      proof-world-stop proof-world-pc))))

(defthm symbols-replay-is-advance
  (implies (and (symbols-path-ready-p path base cut world)
                (symbols-path-control-p path base world))
           (equal (proof-advance (len path) world) (symbols-replay path world)))
  :hints (("Goal" :induct (symbols-path-control-p path base world)
                  :in-theory (disable proof-step proof-instruction-effect
                                      proof-instruction-at-p proof-instruction-access-p
                                      proof-world-stop proof-world-pc)))
  :rule-classes nil)

; These projections let the execution proofs use the model's state
; operations without expanding the register and memory association lists.
(defthm symbols-world-machine-of-update
  (equal (proof-world-machine (update-nth 0 machine world)) machine))

(defthm symbols-world-stop-of-update
  (equal (proof-world-stop (update-nth 0 machine world)) (proof-world-stop world)))

(defthm symbols-world-update-of-update
  (equal (update-nth 0 machine (update-nth 0 earlier world))
         (update-nth 0 machine world)))

(local
 (defthm symbols-assoc-of-put-assoc
   (implies (and (natp register) (natp target))
            (equal (assoc-equal register (put-assoc-equal target value registers))
                   (if (equal register target)
                       (cons register value)
                     (assoc-equal register registers))))))

(defthm symbols-read-register-of-write
  (implies (and (natp target) (< target 31))
           (equal (boymoo-model::a64-read-reg
                   register width use-sp
                   (boymoo-model::a64-write-reg target bits sp value machine))
                  (if (equal register target)
                      (boymoo-model::a64-unsigned width
                                                 (boymoo-model::a64-unsigned bits value))
                    (boymoo-model::a64-read-reg register width use-sp machine))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                      put-assoc-equal assoc-equal))))

(defthm symbols-read-register-of-zero-write
  (equal (boymoo-model::a64-write-reg 31 width nil value machine) machine))

(defthm symbols-car-of-update-nth
  (implies (posp position)
           (equal (car (update-nth position value fields)) (car fields)))
  :hints (("Goal" :expand ((update-nth position value fields)))))

(defthm symbols-car-of-pc
  (equal (car (boymoo-model::a64-set-pc pc machine)) (car machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm symbols-car-of-flags
  (equal (car (boymoo-model::a64-set-nzcv flags machine)) (car machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm symbols-car-of-register-write
  (implies (and (natp register) (< register 31))
           (consp (car (boymoo-model::a64-write-reg register width sp value machine))))
  :hints (("Goal" :in-theory (disable put-assoc-equal))))

(defthm symbols-register-write-is-not-a-syscall
  (implies (and (natp register) (< register 31))
           (not (equal (car (boymoo-model::a64-write-reg register width sp value machine))
                       :svc)))
  :hints (("Goal" :use symbols-car-of-register-write
                  :in-theory (disable boymoo-model::a64-write-reg
                                      symbols-car-of-register-write))))

(defthm symbols-machine-after-pc-is-cons
  (consp (boymoo-model::a64-set-pc pc machine))
  :rule-classes :type-prescription)

(defthm symbols-machine-after-flags-is-cons
  (consp (boymoo-model::a64-set-nzcv flags machine))
  :rule-classes :type-prescription)

(defthm symbols-machine-after-register-write-is-cons
  (implies (and (natp register) (< register 31))
           (consp (boymoo-model::a64-write-reg register width sp value machine)))
  :rule-classes :type-prescription)

(defthm symbols-machine-after-sp-write-is-cons
  (consp (boymoo-model::a64-write-reg 31 width t value machine))
  :rule-classes :type-prescription)

(defthm symbols-car-of-sp-write
  (equal (car (boymoo-model::a64-write-reg 31 width t value machine))
         (car machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm symbols-read-register-of-sp-write
  (implies (not (and (equal register 31) use-sp))
           (equal (boymoo-model::a64-read-reg
                   register width use-sp
                   (boymoo-model::a64-write-reg 31 bits t value machine))
                  (boymoo-model::a64-read-reg register width use-sp machine)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm symbols-sp-of-sp-write
  (equal (boymoo-model::a64-sp (boymoo-model::a64-write-reg 31 bits t value machine))
         (boymoo-model::a64-unsigned
          64 (boymoo-model::a64-unsigned 64 (boymoo-model::a64-unsigned bits value))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm symbols-read-register-of-pc
  (equal (boymoo-model::a64-read-reg register width use-sp
                                   (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-read-reg register width use-sp machine)))

(defthm symbols-read-register-of-flags
  (equal (boymoo-model::a64-read-reg register width use-sp
                                   (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-read-reg register width use-sp machine)))

(defthm symbols-pc-of-pc
  (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-unsigned 64 (boymoo-model::a64-unsigned 64 pc)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(defthm symbols-pc-of-flags
  (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-pc machine)))

(defthm symbols-pc-of-write
  (equal (boymoo-model::a64-pc
          (boymoo-model::a64-write-reg target width sp value machine))
         (boymoo-model::a64-pc machine)))

(defthm symbols-sp-of-pc
  (equal (boymoo-model::a64-sp (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-sp machine)))

(defthm symbols-sp-of-flags
  (equal (boymoo-model::a64-sp (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-sp machine)))

(defthm symbols-sp-of-register-write
  (implies (not (equal target 31))
           (equal (boymoo-model::a64-sp
                   (boymoo-model::a64-write-reg target width sp value machine))
                  (boymoo-model::a64-sp machine))))

(defthm symbols-flags-of-pc
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-nzcv machine)))

(defthm symbols-flags-of-flags
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-unsigned 4 (boymoo-model::a64-unsigned 4 flags))))

(defthm symbols-flags-of-write
  (equal (boymoo-model::a64-nzcv
          (boymoo-model::a64-write-reg target width sp value machine))
         (boymoo-model::a64-nzcv machine)))

(defthm symbols-memory-of-pc
  (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-memory machine)))

(defthm symbols-memory-of-flags
  (equal (boymoo-model::a64-memory (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-memory machine)))

(defthm symbols-memory-of-write
  (equal (boymoo-model::a64-memory
          (boymoo-model::a64-write-reg target width sp value machine))
         (boymoo-model::a64-memory machine)))

(defthm symbols-load-of-pc
  (equal (boymoo-model::a64-load size address (boymoo-model::a64-set-pc pc machine))
         (boymoo-model::a64-load size address machine)))

(defthm symbols-load-of-flags
  (equal (boymoo-model::a64-load
          size address (boymoo-model::a64-set-nzcv flags machine))
         (boymoo-model::a64-load size address machine)))

(defthm symbols-load-of-write
  (equal (boymoo-model::a64-load
          size address (boymoo-model::a64-write-reg target width sp value machine))
         (boymoo-model::a64-load size address machine)))

(defthm symbols-machine-after-store-is-cons
  (consp (boymoo-model::a64-store size address value machine))
  :rule-classes :type-prescription)

(defthm symbols-car-of-store
  (equal (car (boymoo-model::a64-store size address value machine))
         (car machine)))

(defthm symbols-pc-of-store
  (equal (boymoo-model::a64-pc (boymoo-model::a64-store size address value machine))
         (boymoo-model::a64-pc machine)))

(defthm symbols-sp-of-store
  (equal (boymoo-model::a64-sp (boymoo-model::a64-store size address value machine))
         (boymoo-model::a64-sp machine)))

(defthm symbols-read-register-of-store
  (equal (boymoo-model::a64-read-reg
          register width sp (boymoo-model::a64-store size address value machine))
         (boymoo-model::a64-read-reg register width sp machine)))

(defthm symbols-flags-of-store
  (equal (boymoo-model::a64-nzcv (boymoo-model::a64-store size address value machine))
         (boymoo-model::a64-nzcv machine)))

(defthm symbols-memory-of-store
  (equal (boymoo-model::a64-memory (boymoo-model::a64-store size address value machine))
         (boymoo-model::a64-write-bytes size address value (boymoo-model::a64-memory machine))))

(local
 (defun symbols-register-index-induction (register)
   (declare (xargs :measure (nfix register)))
   (if (zp register)
       nil
     (symbols-register-index-induction (1- register)))))

(defthm symbols-register-frame-of-pc
  (equal (proof-register-frame-p
          register clobbers before
          (update-nth 0 (boymoo-model::a64-set-pc pc machine) after))
         (proof-register-frame-p register clobbers before (update-nth 0 machine after)))
  :hints (("Goal" :induct (symbols-register-index-induction register)
                  :in-theory (disable boymoo-model::a64-set-pc
                                      boymoo-model::a64-read-reg update-nth))))

(defthm symbols-register-frame-of-flags
  (equal (proof-register-frame-p
          register clobbers before
          (update-nth 0 (boymoo-model::a64-set-nzcv flags machine) after))
         (proof-register-frame-p register clobbers before (update-nth 0 machine after)))
  :hints (("Goal" :induct (symbols-register-index-induction register)
                  :in-theory (disable boymoo-model::a64-set-nzcv
                                      boymoo-model::a64-read-reg update-nth))))

(defthm symbols-register-frame-of-clobber
  (implies (and (natp target) (< target 31) (member-equal target clobbers))
           (equal (proof-register-frame-p
                   register clobbers before
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  target width sp value machine)
                               after))
                  (proof-register-frame-p register clobbers before
                                          (update-nth 0 machine after))))
  :hints (("Goal" :induct (symbols-register-index-induction register)
                  :in-theory (disable boymoo-model::a64-write-reg
                                      boymoo-model::a64-read-reg update-nth))))

(defthm symbols-register-frame-of-self
  (proof-register-frame-p register clobbers world world))

(defthm symbols-register-frame-of-sp-write
  (equal (proof-register-frame-p
          register clobbers before
          (update-nth 0 (boymoo-model::a64-write-reg 31 width t value machine) after))
         (proof-register-frame-p register clobbers before (update-nth 0 machine after)))
  :hints (("Goal" :induct (symbols-register-index-induction register)
                  :in-theory (disable boymoo-model::a64-write-reg
                                      boymoo-model::a64-read-reg update-nth))))

(defthm symbols-register-frame-of-store
  (equal (proof-register-frame-p
          register clobbers before
          (update-nth 0 (boymoo-model::a64-store size address value machine) after))
         (proof-register-frame-p register clobbers before (update-nth 0 machine after)))
  :hints (("Goal" :induct (symbols-register-index-induction register)
                  :in-theory (disable boymoo-model::a64-store
                                      boymoo-model::a64-read-reg update-nth))))

(defthm symbols-register-frame-of-current-machine
  (equal (proof-register-frame-p register clobbers before
                                 (update-nth 0 (proof-world-machine after) after))
         (proof-register-frame-p register clobbers before after))
  :hints (("Goal" :induct (symbols-register-index-induction register)
                  :in-theory (disable update-nth))))

(deftheory symbols-state-operations
  '(proof-instruction-at-p proof-instruction-access-p proof-step proof-decode
    boymoo-model::a64-load boymoo-model::a64-store boymoo-model::a64-read-reg
    boymoo-model::a64-write-reg boymoo-model::a64-write-bytes
    boymoo-model::a64-pc boymoo-model::a64-set-pc boymoo-model::a64-sp
    boymoo-model::a64-nzcv boymoo-model::a64-set-nzcv boymoo-model::a64-memory
    proof-register-frame-p proof-world-machine update-nth))
