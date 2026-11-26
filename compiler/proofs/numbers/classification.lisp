(in-package "BOYMOO-PROOFS")

(include-book "boxing")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                     boymoo-model::a64-write-reg boymoo-model::a64-load
                     boymoo-model::a64-pc boymoo-model::a64-nzcv boymoo-model::a64-sp
                     boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory
                     proof-execute proof-instruction-effect proof-reg proof-load-word
                     proof-world-machine proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-run proof-segment-p proof-view proof-value-p
                     proof-number-checked-block-p proof-word-tag proof-header-type
                     proof-header-size proof-pointer-address proof-number-integer-parity
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior oddp evenp mod floor ash)))

(defun proof-number-instruction-items (items)
  (if (endp items)
      nil
    (if (eq (caar items) :label)
        (proof-number-instruction-items (cdr items))
      (cons (car items) (proof-number-instruction-items (cdr items))))))

(defund proof-number-classifier-instructions (entry)
  (list '(:move-wide 2 64 3 3 0)
        '(:logical-imm 3 64 31 0 1)
        (list :branch-cond (- (+ entry 52) (+ entry 8)) 1)
        '(:logical-imm 0 64 3 0 7)
        '(:arithmetic-imm 3 64 31 3 2)
        (list :branch-cond (- (+ entry 48) (+ entry 20)) 1)
        '(:arithmetic-imm 2 64 4 0 2)
        '(:arithmetic-reg 0 64 4 28 4 0 0)
        '(:single 1 1 4 3 :offset 0)
        '(:arithmetic-imm 2 64 5 3 3)
        '(:arithmetic-imm 3 64 31 5 2)
        (list :branch-cond (- (+ entry 52) (+ entry 44)) 9)
        '(:move-wide 2 64 3 0 0)
        '(:branch-reg 30 nil)))

(defthm proof-number-classifier-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let ((entry (boymoo-compiler::a64-offset "rt:num-type" labels)))
      (equal
       (proof-number-decode-items
        (proof-number-instruction-items
         (take 17 (proof-number-code-at-label "rt:num-type"
                                             (boymoo-compiler::runtime-primitive-code))))
        entry labels)
       (proof-number-classifier-instructions entry))))
  :rule-classes nil)

(defund proof-number-classifier-path (world)
  (let* ((word (proof-world-reg 0 world))
         (base (proof-heap-base world))
         (machine (proof-world-machine world))
         (address (proof-pointer-address word base))
         (kind (proof-header-type (proof-load-word address machine)))
         (code (proof-number-classifier-instructions (proof-world-pc world)))
         (return '(:branch-reg 30 nil))
         (other '(:move-wide 2 64 3 0 0)))
    (cond ((oddp word) (append (take 3 code) (list return)))
          ((not (equal (proof-word-tag word) 2))
           (append (take 6 code) (list other return)))
          ((member-equal kind '(3 4 5)) (append (take 12 code) (list return)))
          (t code))))

(local
 (defthm header-tag-is-at-least-two
   (implies (and (natp word) (equal (proof-word-tag word) 2))
            (<= 2 word))
   :hints (("Goal" :in-theory (enable proof-word-tag)))
   :rule-classes nil))

(local
 (defthm header-address-range
   (unsigned-byte-p 64 (proof-pointer-address word base))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary (natp (proof-pointer-address word base)))
                  (:linear :corollary (< (proof-pointer-address word base) (expt 2 64))))))

(defthm proof-number-address-from-header-tag
  (implies (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2))
           (equal (boymoo-model::a64-unsigned
                   64 (+ base (boymoo-model::a64-unsigned 64 (- word 2))))
                  (proof-pointer-address word base)))
  :hints (("Goal" :use header-tag-is-at-least-two
                  :in-theory (enable proof-pointer-address))))

(local
 (defthm header-type-is-low-byte
   (equal (boymoo-model::a64-load 1 address machine)
          (proof-header-type (proof-load-word address machine)))
   :hints (("Goal" :use proof-number-loaded-low-byte))))

(local
 (defthm header-type-range
   (unsigned-byte-p 8 (proof-header-type header))
   :hints (("Goal" :in-theory (enable proof-header-type)))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary (natp (proof-header-type header)))
                  (:linear :corollary (< (proof-header-type header) 256)))))

(local
 (defthm header-type-class-test
   (implies (unsigned-byte-p 8 kind)
            (equal (<= (boymoo-model::a64-unsigned 64 (- kind 3)) 2)
                   (if (member-equal kind '(3 4 5)) t nil)))
   :hints (("Goal"
            :use ((:instance proof-number-unsigned-difference (left kind) (right 3)))))))

(local
 (defthm header-class-condition
   (implies (unsigned-byte-p 8 kind)
            (equal (boymoo-model::a64-condition
                    9 (proof-number-subtraction-flags
                       (boymoo-model::a64-unsigned 64 (- kind 3)) 2))
                   (if (member-equal kind '(3 4 5)) t nil)))))

(local
 (defthm test-low-bit-condition
   (equal (boymoo-model::a64-condition 1 (if test 0 4)) (if test t nil))))

(defthm proof-number-classifier-returns
  (let* ((machine (proof-world-machine world))
         (link (proof-world-reg 30 world))
         (word (proof-world-reg 0 world))
         (base (proof-heap-base world))
         (path (proof-number-classifier-path world))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-number-checked-block-p path (list link) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 52 (proof-world-pc world))))
             (and (proof-segment-p (len path) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 3 after) (proof-number-word-class word base machine))
                  (implies (and (not (oddp word)) (equal (proof-word-tag word) 2))
                           (equal (proof-world-reg 4 after) (proof-pointer-address word base)))
                  (implies (not (member-equal register '(3 4 5)))
                           (equal (proof-world-reg register after) (proof-world-reg register world)))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (proof-number-classifier-path world))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (enable proof-number-classifier-path
                              proof-number-classifier-instructions proof-number-word-class)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-classifier-returns-datum-class
  (let* ((path (proof-number-classifier-path world))
         (link (proof-world-reg 30 world))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-reg-value-p 0 value world objects packages)
                  (proof-number-checked-block-p path (list link) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 52 (proof-world-pc world))))
             (and (proof-segment-p (len path) (list link) world :cut after)
                  (equal (proof-world-reg 3 after) (proof-number-datum-class value)))))
  :hints (("Goal"
           :use ((:instance proof-number-classifier-returns (register 0))
                 (:instance proof-number-view-class
                            (word (proof-world-reg 0 world))
                            (base (proof-heap-base world))
                            (machine (proof-world-machine world))))
           :in-theory (disable proof-number-execute-block proof-world-reg proof-heap-base)))
  :rule-classes nil)
