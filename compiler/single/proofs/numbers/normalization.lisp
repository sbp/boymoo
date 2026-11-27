(in-package "BOYMOO-PROOFS")

(include-book "execution")
(include-book "representation")
(include-book "formulas")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                     boymoo-model::a64-write-reg boymoo-model::a64-load
                     boymoo-model::a64-pc boymoo-model::a64-nzcv boymoo-model::a64-sp
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-condition
                     proof-execute proof-instruction-effect proof-reg
                     proof-world-reg proof-world-machine proof-world-pc proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-run proof-view proof-value-p
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

(defthm proof-number-instruction-kept-with-memory
  (implies (equal (boymoo-model::a64-memory machine)
                  (boymoo-model::a64-memory (proof-world-machine world)))
           (equal (proof-instruction-at-p instruction address (update-nth 0 machine world))
                  (proof-instruction-at-p instruction address world)))
  :hints (("Goal"
           :in-theory (e/d (proof-instruction-at-p proof-decode-at proof-fetchable-p
                                                  boymoo-model::a64-load)
                           (proof-decode proof-covered-p boymoo-model::a64-read-bytes)))))

(defthm proof-number-car-of-update
  (equal (car (update-nth index value record))
         (if (zp index) value (car record)))
  :hints (("Goal" :expand ((update-nth index value record)))))

(defthm proof-number-update-is-cons
  (consp (update-nth index value record))
  :hints (("Goal" :expand ((update-nth index value record)))))

(defthm proof-number-setting-pc-keeps-machine-result
  (implies (not (eq (car machine) :svc))
           (and (not (eq (boymoo-model::a64-set-pc address machine) :undefined))
                (not (eq (car (boymoo-model::a64-set-pc address machine)) :svc))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc update-nth))))

(defthm proof-number-setting-flags-keeps-machine-result
  (implies (not (eq (car machine) :svc))
           (and (not (eq (boymoo-model::a64-set-nzcv flags machine) :undefined))
                (not (eq (car (boymoo-model::a64-set-nzcv flags machine)) :svc))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-set-nzcv update-nth))))

(defthm proof-number-q-normalize-items
  (equal (take 6 (proof-number-code-at-label "rt:q-normalize"
                                           (boymoo-compiler::runtime-rational-code)))
         '((:label "rt:q-normalize")
           (:cmp 0 1) (:b-cond :eq "rt:zero")
           (:cmp 1 3) (:b-cond :eq "rt:num-type-return")
           (:b "rt:q-reduce")))
  :rule-classes nil)

(defund proof-number-q-normalize-instructions (entry zero unchanged reduce)
  (list '(:arithmetic-imm 3 64 31 0 1)
        (list :branch-cond (- zero (+ entry 4)) 0)
        '(:arithmetic-imm 3 64 31 1 3)
        (list :branch-cond (- unchanged (+ entry 12)) 0)
        (list :branch (- reduce (+ entry 16)) nil)))

(defund proof-number-q-normalize-target (a b zero unchanged reduce)
  (cond ((equal a 1) zero)
        ((equal b 3) unchanged)
        (t reduce)))

(defund proof-number-q-normalize-count (a b)
  (cond ((equal a 1) 2)
        ((equal b 3) 4)
        (t 5)))

(defund proof-number-q-normalize-pre-p (zero unchanged reduce world)
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (a (proof-world-reg 0 world))
         (b (proof-world-reg 1 world))
         (target (proof-number-q-normalize-target a b zero unchanged reduce)))
    (and (not (proof-world-stop world))
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 entry))
         (unsigned-byte-p 64 zero)
         (unsigned-byte-p 64 unchanged)
         (unsigned-byte-p 64 reduce)
         (not (member-equal target (list entry (+ 4 entry) (+ 8 entry)
                                         (+ 12 entry) (+ 16 entry))))
         (proof-instructions-at-p
          (proof-number-q-normalize-instructions entry zero unchanged reduce)
          entry world))))

(defund proof-number-q-normalize-after (zero unchanged reduce world)
  (let* ((machine (proof-world-machine world))
         (a (proof-world-reg 0 world))
         (b (proof-world-reg 1 world))
         (target (proof-number-q-normalize-target a b zero unchanged reduce))
         (flags (if (equal a 1)
                    (proof-number-subtraction-flags a 1)
                  (proof-number-subtraction-flags b 3))))
    (update-nth 0 (boymoo-model::a64-set-pc
                   target (boymoo-model::a64-set-nzcv flags machine))
                world)))

(local
 (defthm set-pc-without-changing-flags
   (equal (boymoo-model::a64-set-nzcv flags (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-set-pc pc (boymoo-model::a64-set-nzcv flags machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc
                                      boymoo-model::a64-set-nzcv)
                   :use ((:instance proof-number-distinct-slot-updates (i 3) (j 2)
                                    (new (boymoo-model::a64-unsigned 4 flags))
                                    (old (boymoo-model::a64-unsigned 64 pc))
                                    (record machine)))))))

(local
 (defthm set-flags-again
   (equal (boymoo-model::a64-set-nzcv new (boymoo-model::a64-set-nzcv old machine))
          (boymoo-model::a64-set-nzcv new machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-nzcv)))))

(local
 (defthm pc-and-word-registers-fit
   (and (unsigned-byte-p 64 (proof-world-pc world))
        (unsigned-byte-p 64 (proof-world-reg register world)))
   :hints (("Goal" :in-theory (enable proof-world-pc proof-world-reg)))))

(local
 (defthm checked-q-normalize-path
   (let* ((entry (proof-world-pc world))
          (a (proof-world-reg 0 world))
          (b (proof-world-reg 1 world))
          (target (proof-number-q-normalize-target a b zero unchanged reduce))
          (count (proof-number-q-normalize-count a b))
          (path (take count (proof-number-q-normalize-instructions entry zero unchanged reduce))))
     (implies (proof-number-q-normalize-pre-p zero unchanged reduce world)
              (and (proof-number-checked-block-p path (list target) world)
                   (equal (proof-number-execute-block path world)
                          (proof-number-q-normalize-after zero unchanged reduce world)))))
   :hints (("Goal"
            :in-theory (enable proof-number-q-normalize-instructions
                               proof-number-q-normalize-target proof-number-q-normalize-count
                               proof-number-q-normalize-pre-p proof-number-q-normalize-after
                               proof-world-reg proof-world-pc)
            :cases ((equal (proof-world-reg 0 world) 1)
                    (equal (proof-world-reg 1 world) 3))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-q-normalize-dispatch
  (let* ((a (proof-world-reg 0 world))
         (b (proof-world-reg 1 world))
         (target (proof-number-q-normalize-target a b zero unchanged reduce))
         (count (proof-number-q-normalize-count a b))
         (after (proof-number-q-normalize-after zero unchanged reduce world)))
    (implies (proof-number-q-normalize-pre-p zero unchanged reduce world)
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg register after) (proof-world-reg register world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world))))))
  :hints (("Goal"
           :use (checked-q-normalize-path
                 (:instance proof-number-checked-block-segment
                            (instructions
                             (take (proof-number-q-normalize-count (proof-world-reg 0 world)
                                                                    (proof-world-reg 1 world))
                                   (proof-number-q-normalize-instructions
                                    (proof-world-pc world) zero unchanged reduce)))
                            (cuts
                             (list (proof-number-q-normalize-target
                                    (proof-world-reg 0 world) (proof-world-reg 1 world)
                                    zero unchanged reduce)))))
           :in-theory (e/d (proof-number-q-normalize-count proof-number-q-normalize-pre-p
                            proof-number-q-normalize-after proof-number-q-normalize-target
                            proof-number-q-normalize-instructions proof-world-reg proof-world-pc)
                           (proof-number-execute-block proof-number-checked-block-p
                            proof-instructions-at-p proof-segment-p boymoo-model::a64-memory))))
  :rule-classes nil)

(defun proof-number-decode-items (items pc labels)
  (if (endp items)
      nil
    (cons (proof-decode (boymoo-compiler::a64-word (car items) pc labels))
          (proof-number-decode-items (cdr items) (+ 4 pc) labels))))

(defthm proof-number-q-normalize-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((entry (boymoo-compiler::a64-offset "rt:q-normalize" labels))
           (zero (boymoo-compiler::a64-offset "rt:zero" labels))
           (unchanged (boymoo-compiler::a64-offset "rt:num-type-return" labels))
           (reduce (boymoo-compiler::a64-offset "rt:q-reduce" labels))
           (items (cdr (take 6 (proof-number-code-at-label
                               "rt:q-normalize" (boymoo-compiler::runtime-rational-code))))))
      (equal (proof-number-decode-items items entry labels)
             (proof-number-q-normalize-instructions entry zero unchanged reduce))))
  :rule-classes nil)

(defthm proof-number-q-normalize-dispatch-by-value
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (target (cond ((equal a 0) zero)
                       ((equal b 1) unchanged)
                       (t reduce)))
         (count (cond ((equal a 0) 2)
                      ((equal b 1) 4)
                      (t 5))))
    (implies (and (integerp a) (posp b)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-q-normalize-pre-p zero unchanged reduce world))
             (let ((after (proof-number-q-normalize-after zero unchanged reduce world)))
               (and (proof-segment-p count (list target) world :cut after)
                    (equal (proof-world-pc after) target)
                    (equal (proof-world-reg register after) (proof-world-reg register world))
                    (equal (boymoo-model::a64-memory (proof-world-machine after))
                           (boymoo-model::a64-memory machine))
                    (equal (proof-heap-base after) base)))))
  :hints (("Goal"
           :use (proof-number-q-normalize-dispatch
                 (:instance proof-number-q-normalize-dispatch (register 28))
                 (:instance proof-number-tagged-zero-and-one
                            (word (proof-world-reg 0 world)) (value a)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance proof-number-tagged-zero-and-one
                            (word (proof-world-reg 1 world)) (value b)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-number-q-normalize-target proof-number-q-normalize-count)
                           (proof-segment-p proof-load-word boymoo-model::a64-memory))))
  :rule-classes nil)
