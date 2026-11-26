(in-package "BOYMOO-PROOFS")

(include-book "normalization")

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
                     proof-step proof-run proof-view proof-value-p
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

(defthm proof-number-store-keeps-machine-result
  (implies (not (eq (car machine) :svc))
           (and (not (eq (boymoo-model::a64-store bytes address word machine) :undefined))
                (not (eq (car (boymoo-model::a64-store bytes address word machine)) :svc))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-store))))

(local
 (defthm put-assoc-is-cons
   (consp (put-assoc-equal key value entries))))

(defthm proof-number-register-write-keeps-machine-result
  (implies (and (not (eq machine :undefined)) (not (eq (car machine) :svc)))
           (and (not (eq (boymoo-model::a64-write-reg dest 64 use-sp word machine) :undefined))
                (not (eq (car (boymoo-model::a64-write-reg dest 64 use-sp word machine)) :svc))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg
                                     boymoo-model::a64-registers))))

(defund proof-number-box-select-instructions (kind entry unchanged fields)
  (append
   (list (list :arithmetic-imm 3 64 31 1 (if (equal kind 4) 3 1))
         (list :branch-cond (- unchanged (+ entry 4)) 0)
         (list :move-wide 2 64 2 (+ 4096 kind) 0))
   (if (equal kind 4)
       nil
     (list (list :branch (- fields (+ entry 12)) nil)))))

(defund proof-number-box-without-allocation-p (kind world)
  (equal (proof-world-reg 1 world) (if (equal kind 4) 3 1)))

(defund proof-number-box-select-count (kind world)
  (cond ((proof-number-box-without-allocation-p kind world) 2)
        ((equal kind 4) 3)
        (t 4)))

(defund proof-number-box-select-target (kind unchanged fields world)
  (if (proof-number-box-without-allocation-p kind world) unchanged fields))

(defund proof-number-box-select-pre-p (kind unchanged fields world)
  (let* ((entry (proof-world-pc world))
         (target (proof-number-box-select-target kind unchanged fields world)))
    (and (member-equal kind '(4 5))
         (not (proof-world-stop world))
         (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ 12 entry))
         (unsigned-byte-p 64 unchanged)
         (unsigned-byte-p 64 fields)
         (if (equal kind 4) (equal fields (+ 12 entry)) t)
         (not (member-equal target
                            (if (equal kind 4)
                                (list entry (+ 4 entry) (+ 8 entry))
                              (list entry (+ 4 entry) (+ 8 entry) (+ 12 entry)))))
         (proof-instructions-at-p
          (proof-number-box-select-instructions kind entry unchanged fields) entry world))))

(defund proof-number-box-select-after (kind unchanged fields world)
  (let ((path (take (proof-number-box-select-count kind world)
                    (proof-number-box-select-instructions
                     kind (proof-world-pc world) unchanged fields))))
    (proof-number-execute-block path world)))

(local
 (defthm box-select-checked
   (let* ((entry (proof-world-pc world))
          (count (proof-number-box-select-count kind world))
          (instructions (proof-number-box-select-instructions kind entry unchanged fields))
          (target (proof-number-box-select-target kind unchanged fields world))
          (path (take count instructions)))
     (implies (proof-number-box-select-pre-p kind unchanged fields world)
              (and (proof-number-checked-block-p path (list target) world)
                   (equal (len path) count))))
   :hints (("Goal"
            :in-theory (enable proof-number-box-select-pre-p
                               proof-number-box-select-target proof-number-box-select-count
                               proof-number-box-without-allocation-p
                               proof-number-box-select-instructions)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-box-select
  (let* ((target (proof-number-box-select-target kind unchanged fields world))
         (count (proof-number-box-select-count kind world))
         (after (proof-number-box-select-after kind unchanged fields world)))
    (implies (proof-number-box-select-pre-p kind unchanged fields world)
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (proof-number-box-without-allocation-p kind world))
                           (equal (proof-world-reg 2 after) (+ 4096 kind))))))
  :hints (("Goal"
           :use (box-select-checked
                 (:instance proof-number-checked-block-segment
                            (instructions
                             (take (proof-number-box-select-count kind world)
                                   (proof-number-box-select-instructions
                                    kind (proof-world-pc world) unchanged fields)))
                            (cuts
                             (list (proof-number-box-select-target
                                    kind unchanged fields world)))))
           :in-theory (e/d (proof-number-box-select-pre-p proof-number-box-select-after
                            proof-number-box-select-count proof-number-box-select-target
                            proof-number-box-without-allocation-p
                            proof-number-box-select-instructions)
                           (proof-number-checked-block-p proof-segment-p
                            proof-instructions-at-p))
           :do-not-induct t))
  :rule-classes nil)

(defun proof-number-box-select-decoding-p (kind)
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((name (if (equal kind 4) "rt:q-box" "rt:c-box"))
           (entry (boymoo-compiler::a64-offset name labels))
           (unchanged (boymoo-compiler::a64-offset "rt:num-type-return" labels))
           (fields (boymoo-compiler::a64-offset "rt:num-box-fields" labels))
           (count (if (equal kind 4) 4 5))
           (items (cdr (take count (proof-number-code-at-label
                                    name (boymoo-compiler::runtime-primitive-code))))))
      (and (implies (equal kind 4) (equal fields (+ 12 entry)))
           (equal (proof-number-decode-items items entry labels)
                  (proof-number-box-select-instructions kind entry unchanged fields))))))

(defthm proof-number-box-select-decoding
  (and (proof-number-box-select-decoding-p 4)
       (proof-number-box-select-decoding-p 5))
  :rule-classes nil)

(defund proof-number-box-reserve-instructions (entry reserve)
  (list '(:pair nil 31 2 30 :pre -16)
        '(:move-wide 2 64 2 24 0)
        (list :branch (- reserve (+ entry 8)) t)))

(defconst *proof-number-box-publish-instructions*
  '((:pair t 31 3 30 :post 16)
    (:single 0 8 2 3 :offset 0)
    (:pair nil 2 0 1 :offset 8)
    (:arithmetic-reg 2 64 0 2 28 0 0)
    (:arithmetic-imm 0 64 0 0 2)
    (:branch-reg 30 nil)))

(defthm proof-number-box-fields-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((entry (boymoo-compiler::a64-offset "rt:num-box-fields" labels))
           (reserve (boymoo-compiler::a64-offset "rt:z-reserve" labels))
           (items (cdr (take 10 (proof-number-code-at-label
                                 "rt:num-box-fields" (boymoo-compiler::runtime-primitive-code))))))
      (equal (proof-number-decode-items items entry labels)
             (append (proof-number-box-reserve-instructions entry reserve)
                     *proof-number-box-publish-instructions*))))
  :rule-classes nil)

(defthm proof-number-box-calls-reserve
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (code (proof-number-box-reserve-instructions entry reserve))
         (ready (proof-number-execute-block code world))
         (ready-machine (proof-world-machine ready)))
    (implies (and (proof-number-checked-block-p code (list reserve) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p saved 16)
                  (unsigned-byte-p 64 (+ 12 entry))
                  (unsigned-byte-p 64 reserve))
             (and (proof-segment-p 3 (list reserve) world :cut ready)
                  (equal (proof-world-pc ready) reserve)
                  (equal (proof-world-reg 30 ready) (+ 12 entry))
                  (equal (boymoo-model::a64-sp ready-machine) saved)
                  (equal (proof-world-reg 0 ready) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 ready) (proof-world-reg 1 world))
                  (equal (proof-world-reg 2 ready) 24)
                  (equal (proof-load-word saved ready-machine) (proof-world-reg 2 world))
                  (equal (proof-load-word (+ 8 saved) ready-machine) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-box-reserve-instructions
                                           (proof-world-pc world) reserve))
                            (cuts (list reserve))))
           :in-theory (e/d (proof-number-box-reserve-instructions)
                           (proof-number-checked-block-p proof-segment-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-publishes-fields
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 2 world))
         (base (proof-heap-base world))
         (link (proof-load-word (+ stack 8) machine))
         (header (proof-load-word stack machine))
         (word (+ 2 (- address base)))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world))
         (after-machine (proof-world-machine after)))
    (implies (and (proof-number-checked-block-p *proof-number-box-publish-instructions*
                                               (list link) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p address 24)
                  (unsigned-byte-p 64 (+ 16 stack))
                  (<= base address))
             (and (proof-segment-p 6 (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (boymoo-model::a64-sp after-machine) (+ 16 stack))
                  (equal (proof-world-reg 0 after) word)
                  (equal (proof-heap-base after) base)
                  (equal (proof-load-word address after-machine) header)
                  (equal (proof-load-word (+ address 8) after-machine) (proof-world-reg 0 world))
                  (equal (proof-load-word (+ address 16) after-machine) (proof-world-reg 1 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions *proof-number-box-publish-instructions*)
                            (cuts (list (proof-load-word
                                         (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))
                                         (proof-world-machine world))))))
           :in-theory (disable proof-number-checked-block-p proof-segment-p)
           :do-not-induct t))
  :rule-classes nil)
