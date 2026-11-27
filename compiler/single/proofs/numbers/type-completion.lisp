(in-package "BOYMOO-PROOFS")

(include-book "dispatch")
(include-book "state-views")

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

(defund proof-number-types-first-code (pc classifier)
  (list '(:pair nil 31 29 30 :pre -16)
        (list :branch (- classifier (+ pc 4)) t)))

(defconst *proof-number-types-rational-filter*
  '((:arithmetic-imm 3 64 31 3 5)
    (:select 64 3 31 3 0 nil)))

(defund proof-number-types-second-code (rational-only pc classifier)
  (append (if rational-only *proof-number-types-rational-filter* nil)
          '((:arithmetic-imm 3 64 31 3 0)
            (:move-wide 2 64 6 1 0)
            (:select 64 6 0 6 1 nil))
          (if rational-only nil '((:logical-reg 1 64 7 31 3 0 0 nil)))
          '((:logical-reg 1 64 0 31 1 0 0 nil))
          (list (list :branch (- classifier (+ pc (if rational-only 24 20))) t))))

(defund proof-number-types-finish-code (rational-only)
  (append (if rational-only *proof-number-types-rational-filter* nil)
          '((:arithmetic-imm 3 64 31 3 0)
            (:move-wide 2 64 1 1 0)
            (:select 64 1 0 1 1 nil)
            (:logical-reg 1 64 0 31 6 0 0 nil))
          (if rational-only
              '((:pair t 31 29 30 :post 16))
            '((:arithmetic-reg 3 64 31 3 7 0 0)
              (:select 64 3 3 7 2 nil)
              (:pair t 31 29 30 :post 16)
              (:branch-reg 30 nil)))))

(defun proof-number-type-completion-decoding-p (rational-only labels)
  (let* ((name (if rational-only "prim:COMMON-LISP::COMPLEX" "rt:n-types"))
         (entry (boymoo-compiler::a64-offset name labels))
         (classifier (boymoo-compiler::a64-offset "rt:num-type" labels))
         (code (append (proof-number-types-first-code entry classifier)
                       (proof-number-types-second-code rational-only (+ 8 entry) classifier)
                       (proof-number-types-finish-code rational-only)))
         (items (take (len code)
                      (cdr (proof-number-code-at-label
                            name (boymoo-compiler::runtime-primitive-code))))))
    (and (equal (proof-number-decode-items items entry labels) code)
         (or (not rational-only)
             (equal (+ entry (* 4 (len code)))
                    (boymoo-compiler::a64-offset "rt:c-box" labels))))))

(defthm proof-number-types-and-complex-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (and (proof-number-type-completion-decoding-p nil labels)
         (proof-number-type-completion-decoding-p t labels)))
  :rule-classes nil)

(defthm proof-number-types-call-first-classifier
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (code (proof-number-types-first-code pc classifier))
         (after (proof-number-execute-block code world))
         (after-machine (proof-world-machine after)))
    (implies (and (proof-number-checked-block-p code (list classifier) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p saved 16)
                  (unsigned-byte-p 64 (+ pc 8))
                  (unsigned-byte-p 64 classifier))
             (and (proof-segment-p 2 (list classifier) world :cut after)
                  (equal (proof-world-pc after) classifier)
                  (equal (proof-world-reg 30 after) (+ pc 8))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (boymoo-model::a64-sp after-machine) saved)
                  (equal (proof-load-word saved after-machine) (proof-world-reg 29 world))
                  (equal (proof-load-word (+ 8 saved) after-machine)
                         (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-types-first-code
                                           (proof-world-pc world) classifier))
                            (cuts (list classifier))))
           :in-theory (enable proof-number-types-first-code)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-completed-word (rational-only class word)
  (if (or (equal class 0) (and rational-only (equal class 5))) 1 word))

(defthm proof-number-register-write-keeps-flags
  (equal (boymoo-model::a64-nzcv
          (boymoo-model::a64-write-reg dest width use-sp value machine))
         (boymoo-model::a64-nzcv machine))
  :hints (("Goal"
           :in-theory (enable boymoo-model::a64-nzcv boymoo-model::a64-write-reg))))

(defthm proof-number-types-call-second-classifier
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (class (proof-world-reg 3 world))
         (code (proof-number-types-second-code rational-only pc classifier))
         (after (proof-number-execute-block code world))
         (after-machine (proof-world-machine after))
         (link (+ pc (if rational-only 28 24))))
    (implies (and (proof-number-checked-block-p code (list classifier) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 link)
                  (unsigned-byte-p 64 classifier))
             (and (proof-segment-p (len code) (list classifier) world :cut after)
                  (equal (proof-world-pc after) classifier)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 0 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 6 after)
                         (proof-number-completed-word rational-only class (proof-world-reg 0 world)))
                  (implies (not rational-only) (equal (proof-world-reg 7 after) class))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp after-machine) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory after-machine)
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-types-second-code
                                           rational-only (proof-world-pc world) classifier))
                            (cuts (list classifier))))
           :in-theory (enable proof-number-types-second-code proof-number-completed-word)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-types-finish-target (rational-only world)
  (if rational-only
      (+ 28 (proof-world-pc world))
    (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))
                     (proof-world-machine world))))

(defthm proof-number-types-finish
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (code (proof-number-types-finish-code rational-only))
         (target (proof-number-types-finish-target rational-only world))
         (class (proof-world-reg 3 world))
         (after (proof-number-execute-block code world))
         (after-machine (proof-world-machine after)))
    (implies (and (proof-number-checked-block-p code (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 stack))
                  (unsigned-byte-p 64 (+ (* 4 (len code)) (proof-world-pc world))))
             (and (proof-segment-p (len code) (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (proof-load-word (+ 8 stack) machine))
                  (equal (proof-world-reg 29 after) (proof-load-word stack machine))
                  (equal (proof-world-reg 0 after) (proof-world-reg 6 world))
                  (equal (proof-world-reg 1 after)
                         (proof-number-completed-word rational-only class (proof-world-reg 0 world)))
                  (implies (not rational-only)
                           (equal (proof-world-reg 3 after) (max (proof-world-reg 7 world) class)))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp after-machine) (+ 16 stack))
                  (equal (boymoo-model::a64-memory after-machine)
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-types-finish-code rational-only))
                            (cuts (list (proof-number-types-finish-target rational-only world)))))
           :in-theory (enable proof-number-types-finish-code proof-number-types-finish-target
                              proof-number-completed-word)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-completed-word-view
  (implies (proof-value-p word value base objects packages machine)
           (proof-value-p (proof-number-completed-word
                           rational-only (proof-number-datum-class value) word)
                          (if rational-only (rfix value) (fix value))
                          base objects packages machine))
  :hints (("Goal"
           :use ((:instance proof-number-immediate-word-view (value 0)))
           :in-theory (e/d (proof-number-datum-class proof-number-completed-word)
                           (proof-number-immediate-word-view))))
  :rule-classes nil)

(defthm proof-number-reg-value-with-same-memory
  (implies (and (equal (proof-world-reg register after) word)
                (equal (proof-heap-base after) (proof-heap-base before))
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (boymoo-model::a64-memory (proof-world-machine before))))
           (equal (proof-reg-value-p register value after objects packages)
                  (proof-machine-value-p word value before objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-view-kept-with-memory
                            (base (proof-heap-base before))
                            (first (proof-world-machine before))
                            (last (proof-world-machine after))))
           :in-theory (e/d (proof-value-p) (proof-heap-base proof-world-reg))))
  :rule-classes nil)

(defthm proof-number-types-save-first-value
  (let* ((code (proof-number-types-second-code rational-only (proof-world-pc world) classifier))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-checked-block-p code (list classifier) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ (proof-world-pc world) (if rational-only 28 24)))
                  (unsigned-byte-p 64 classifier)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (equal (proof-world-reg 3 world) (proof-number-datum-class a)))
             (and (proof-reg-value-p 6 (if rational-only (rfix a) (fix a)) after objects packages)
                  (proof-reg-value-p 0 b after objects packages))))
  :hints (("Goal"
           :use (proof-number-types-call-second-classifier
                 (:instance proof-number-completed-word-view
                            (word (proof-world-reg 0 world)) (value a)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 6) (value (if rational-only (rfix a) (fix a)))
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-types-second-code
                                     rational-only (proof-world-pc world) classifier) world))
                            (word (proof-number-completed-word
                                   rational-only (proof-world-reg 3 world) (proof-world-reg 0 world))))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value b) (before world)
                            (after (proof-number-execute-block
                                    (proof-number-types-second-code
                                     rational-only (proof-world-pc world) classifier) world))
                            (word (proof-world-reg 1 world))))
           :in-theory (disable proof-number-execute-block proof-world-reg proof-heap-base)))
  :rule-classes nil)

(defthm proof-number-types-return-completed-values
  (let* ((machine (proof-world-machine world))
         (code (proof-number-types-finish-code rational-only))
         (target (proof-number-types-finish-target rational-only world))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-checked-block-p code (list target) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp machine)))
                  (unsigned-byte-p 64 (+ (if rational-only 28 32) (proof-world-pc world)))
                  (proof-reg-value-p 6 (if rational-only (rfix a) (fix a)) world objects packages)
                  (proof-reg-value-p 0 b world objects packages)
                  (equal (proof-world-reg 3 world) (proof-number-datum-class b))
                  (or rational-only (equal (proof-world-reg 7 world) (proof-number-datum-class a))))
             (if rational-only
                 (proof-register-arguments-p (list (rfix a) (rfix b)) 0 after objects packages)
               (proof-number-binary-types-p a b after objects packages))))
  :hints (("Goal"
           :use (proof-number-types-finish
                 (:instance proof-number-completed-word-view
                            (word (proof-world-reg 0 world)) (value b)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value (if rational-only (rfix a) (fix a)))
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-types-finish-code rational-only) world))
                            (word (proof-world-reg 6 world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 1) (value (if rational-only (rfix b) (fix b)))
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-types-finish-code rational-only) world))
                            (word (proof-number-completed-word
                                   rational-only (proof-world-reg 3 world) (proof-world-reg 0 world)))))
           :in-theory (e/d (proof-number-types-finish-code
                            proof-number-binary-types-p proof-number-max-class)
                           (proof-number-execute-block proof-world-reg proof-heap-base))))
  :rule-classes nil)
