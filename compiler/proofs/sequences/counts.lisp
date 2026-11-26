(in-package "BOYMOO-PROOFS")

(include-book "helpers")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-count-immediate*
  ("rt:sequence-count" 0 2)
  ("rt:sequence-count-immediate" 0 4))

(sequence-defpath *sequence-count-nonheader*
  ("rt:sequence-count" 0 5)
  ("rt:sequence-count-zero" 0 2))

(sequence-defpath *sequence-count-other-header*
  ("rt:sequence-count" 0 10)
  ("rt:sequence-count-zero" 0 2))

(sequence-defpath *sequence-count-negative-integer*
  ("rt:sequence-count" 0 12)
  ("rt:sequence-count-zero" 0 2))

(sequence-defpath *sequence-count-positive-integer*
  ("rt:sequence-count" 0 14))

(defun sequence-index-path (word base machine)
  (let ((address (proof-pointer-address word base)))
    (cond ((oddp word) *sequence-count-immediate*)
          ((not (equal (proof-word-tag word) 2)) *sequence-count-nonheader*)
          ((not (equal (proof-header-type (proof-load-word address machine)) 3))
           *sequence-count-other-header*)
          ((not (equal (proof-load-word (+ address 8) machine) 0))
           *sequence-count-negative-integer*)
          (t *sequence-count-positive-integer*))))

(defun sequence-index-value (word base machine)
  (let ((address (proof-pointer-address word base)))
    (cond ((oddp word)
           (sequence-count (floor (boymoo-model::a64-signed 64 word) 2)))
          ((and (equal (proof-word-tag word) 2)
                (equal (proof-header-type (proof-load-word address machine)) 3)
                (equal (proof-load-word (+ address 8) machine) 0))
           *proof-space-size*)
          (t 0))))

(local
 (defthm sequence-immediate-decoding-fits
   (implies (unsigned-byte-p 64 word)
            (proof-immediate-integer-p (floor (boymoo-model::a64-signed 64 word) 2)))
   :hints (("Goal"
            :use ((:instance sequence-floor-bounds
                             (value (boymoo-model::a64-signed 64 word)) (divisor 2)))))
   :rule-classes nil))

(local
 (defthm sequence-compare-with-zero
   (equal (boymoo-model::a64-exec-arithmetic 3 64 31 source 0 t machine)
          (boymoo-model::a64-set-nzcv
           (boymoo-model::a64-result-flags 64
                                          (boymoo-model::a64-read-reg source 64 t machine)
                                          t nil)
           machine))))

(defthm sequence-positive-count-from-signed-word
  (implies (signed-byte-p 64 value)
           (let ((bits (boymoo-model::a64-unsigned 64 value)))
             (equal (if (boymoo-model::a64-condition
                         12 (boymoo-model::a64-result-flags 64 bits carry nil))
                        bits 0)
                    (sequence-count value))))
  :hints (("Goal" :cases ((< value 0)))
          ("Subgoal 1"
           :in-theory (disable sequence-truncate-word-plus-modulus)
           :use (sequence-truncate-word-plus-modulus)))
  :rule-classes nil)

(defthm sequence-index-count-effects
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (address (proof-pointer-address word base))
         (path (sequence-index-path word base machine))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (implies (and (equal (proof-word-tag word) 2)
                        (equal (proof-header-type (proof-load-word address machine)) 3))
                   (unsigned-byte-p 64 (+ address 8))))
     (and (equal (proof-world-reg 0 after) (sequence-index-value word base machine))
          (equal (proof-world-pc after) (proof-world-reg 30 before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 '(0 3 4) before after))))
  :hints (("Goal"
           :in-theory (e/d (sequence-execute)
                           (sequence-count sequence-signed-word
                            sequence-conditions-on-result-flags))
           :use ((:instance sequence-immediate-decoding-fits (word (proof-world-reg 0 before)))
                 (:instance sequence-positive-count-from-signed-word
                            (carry t)
                            (value (floor (boymoo-model::a64-signed 64 (proof-world-reg 0 before))
                                          2))))
           :expand ((:free (register clobbers first last)
                           (proof-register-frame-p register clobbers first last)))))
  :rule-classes nil)

(local
 (defthm sequence-limb-magnitude-natp
   (natp (proof-limb-magnitude count address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (proof-limb-magnitude count address machine)))))

(local
 (defthm sequence-large-integer-sign
   (implies
    (and (equal (proof-integer-view address machine) (proof-value-view datum))
         (not (proof-immediate-integer-p datum)))
    (and (integerp datum)
         (equal (posp datum) (equal (proof-load-word (+ address 8) machine) 0))))
   :hints (("Goal" :in-theory (disable proof-limb-magnitude)))
   :rule-classes nil))

(defthm sequence-index-value-of-represented-datum
  (implies
   (equal (proof-view-step :word word 0 depth base objects packages machine)
          (proof-value-view datum))
   (equal (sequence-index-value word base machine) (sequence-runtime-count datum)))
  :hints
  (("Goal"
    :expand ((proof-view-step :word word 0 depth base objects packages machine))
    :in-theory (disable sequence-signed-word proof-integer-view proof-symbol-value
                        proof-rational-value proof-complex-value proof-load-string)
    :use (sequence-immediate-decoding-fits
          (:instance sequence-large-integer-sign
                     (address (proof-pointer-address word base))))))
  :rule-classes nil)

(defthm sequence-index-count-contract
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (address (proof-pointer-address word base))
         (path (sequence-index-path word base machine))
         (cuts (list (proof-world-reg 30 before)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (proof-value-p word datum base objects packages machine)
          (implies (and (equal (proof-word-tag word) 2)
                        (equal (proof-header-type (proof-load-word address machine)) 3))
                   (unsigned-byte-p 64 (+ address 8)))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-frame-return-p '(0 3 4) t before after)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (proof-world-reg 0 after) (sequence-runtime-count datum)))))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-register-frame-p proof-world-machine
                        proof-world-reg proof-heap-base proof-pointer-address proof-load-word
                        proof-segment-p sequence-index-path sequence-index-value
                        sequence-runtime-count)
    :use (sequence-index-count-effects
          (:instance sequence-index-value-of-represented-datum
                     (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                     (machine (proof-world-machine before))
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address
                                                     (proof-world-reg 0 before)
                                                     (proof-heap-base before)) objects))))))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-index-path (proof-world-reg 0 before)
                                                        (proof-heap-base before)
                                                        (proof-world-machine before)))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute
                             (sequence-index-path (proof-world-reg 0 before)
                                                  (proof-heap-base before)
                                                  (proof-world-machine before))
                             before))))))
  :rule-classes nil)

(local
 (defthm sequence-count-resource-bounds
   (implies (<= *proof-space-size* (sequence-runtime-count value))
            (and (proof-resource-bound-p :string-size (sequence-count value) world)
                 (proof-resource-bound-p :allocation-size (* 16 (sequence-count value)) world)))
   :hints (("Goal" :use sequence-runtime-count-for-size
                   :in-theory (disable sequence-runtime-count)))
   :rule-classes nil))

(defthm sequence-subseq-result-size-limit
  (implies (<= *proof-space-size*
               (sequence-runtime-count (- (sequence-end end datum) start)))
           (and (proof-resource-bound-p :string-size (sequence-result-size datum start end) world)
                (proof-resource-bound-p :allocation-size
                                        (* 16 (sequence-result-size datum start end)) world)))
  :hints (("Goal" :use ((:instance sequence-count-resource-bounds
                                   (value (- (sequence-end end datum) start))))
                  :in-theory (disable sequence-end sequence-count sequence-runtime-count)))
  :rule-classes nil)
