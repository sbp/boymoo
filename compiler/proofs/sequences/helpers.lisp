(in-package "BOYMOO-PROOFS")

(include-book "shifts")
(include-book "memory")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-list-length-entry*
  ("rt:list-length" 0 2))

(sequence-defpath *sequence-list-length-cell*
  ("rt:list-length-loop" 0 6))

(sequence-defpath *sequence-list-length-return*
  ("rt:list-length-loop" 0 2)
  ("rt:list-length-done" 0 1))

(defthm sequence-list-length-entry-effects
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-list-length-entry* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 64 (+ 8 (proof-world-pc before))))
     (and (equal (proof-world-reg 2 after) 0)
          (equal (proof-world-reg 3 after) (proof-world-reg 0 before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-pc after) (+ 8 (proof-world-pc before)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 '(2 3) before after))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (register clobbers first last)
                                  (proof-register-frame-p register clobbers first last)))))
  :rule-classes nil)

(defthm sequence-list-length-cell-effects
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (word (proof-world-reg 3 before))
         (count (proof-world-reg 2 before))
         (after (sequence-execute *sequence-list-length-cell* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-word-tag word) 0)
          (unsigned-byte-p 64 (+ 15 base word))
          (unsigned-byte-p 64 (+ 24 (proof-world-pc before)))
          (unsigned-byte-p 64 (1+ count)))
     (and (equal (proof-world-reg 2 after) (1+ count))
          (equal (proof-world-reg 3 after) (proof-load-word (+ base word 8) machine))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-pc after) (proof-world-pc before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 '(2 3) before after))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (register clobbers first last)
                                  (proof-register-frame-p register clobbers first last)))))
  :rule-classes nil)

(defthm sequence-list-length-return-effects
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-list-length-return* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (not (equal (proof-word-tag (proof-world-reg 3 before)) 0)))
     (and (equal (proof-world-pc after) (proof-world-reg 30 before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 nil before after))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (register clobbers first last)
                                  (proof-register-frame-p register clobbers first last)))))
  :rule-classes nil)

(sequence-defpath *sequence-string-view-string*
  ("rt:string-view" 0 12))

(sequence-defpath *sequence-string-view-other-header*
  ("rt:string-view" 0 9)
  ("rt:no-string" 0 3))

(sequence-defpath *sequence-string-view-nonheader*
  ("rt:string-view" 0 3)
  ("rt:no-string" 0 3))

(defun sequence-string-view-path (word base machine)
  (if (equal (proof-word-tag word) 2)
      (if (equal (proof-header-type
                  (proof-load-word (proof-pointer-address word base) machine)) 1)
          *sequence-string-view-string*
        *sequence-string-view-other-header*)
    *sequence-string-view-nonheader*))

(local
 (defthm sequence-header-size-is-word
   (implies (unsigned-byte-p 64 header)
            (equal (boymoo-model::a64-unsigned 64 (floor header 256))
                   (floor header 256)))
   :hints (("Goal" :use ((:instance sequence-floor-of-unsigned
                                    (dropped 8) (kept 56) (value header)))))))

(local
 (defthm sequence-add-eight-after-address-reduction
   (implies (and (integerp address)
                 (unsigned-byte-p 64 (+ 8 (boymoo-model::a64-unsigned 64 address))))
            (equal (boymoo-model::a64-unsigned 64 (+ 8 address))
                   (+ 8 (boymoo-model::a64-unsigned 64 address))))
   :hints (("Goal" :in-theory (disable sequence-wrap-sum-with-reduced-addend)
                   :use ((:instance sequence-wrap-sum-with-reduced-addend
                                    (left 8) (right address)))))
   :rule-classes nil))

(defthm sequence-string-view-effects
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (address (proof-pointer-address word base))
         (header (proof-load-word address machine))
         (string (and (equal (proof-word-tag word) 2) (equal (proof-header-type header) 1)))
         (path (sequence-string-view-path word base machine))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (implies string (unsigned-byte-p 64 (+ 8 address))))
     (and (equal (proof-world-reg 1 after) (if string (+ 8 address) 0))
          (equal (proof-world-reg 2 after) (if string (proof-header-size header) 0))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-pc after) (proof-world-reg 30 before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 '(1 2 3) before after))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :use ((:instance sequence-add-eight-after-address-reduction
                                   (address (+ (proof-heap-base before)
                                               (- (proof-world-reg 0 before) 2)))))
                  :expand ((:free (register clobbers first last)
                                  (proof-register-frame-p register clobbers first last)))))
  :rule-classes nil)

(defthm sequence-even-tags-mark-even-words
  (implies (and (integerp word) (member-equal (proof-word-tag word) '(0 2 4)))
           (not (oddp word)))
  :hints (("Goal" :in-theory (disable oddp evenp sequence-word-parity-of-tag)
                  :use sequence-word-parity-of-tag)))

(local
 (defthm sequence-string-header-floor-is-natural
   (natp (floor (proof-load-word address machine) 256))
   :hints (("Goal" :use ((:instance sequence-floor-of-unsigned
                                    (dropped 8) (kept 56)
                                    (value (proof-load-word address machine))))))
   :rule-classes :type-prescription))

(defthm sequence-string-view-field-contract
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (address (proof-pointer-address word base))
         (path (sequence-string-view-path word base machine))
         (cuts (list (proof-world-reg 30 before)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (proof-value-p word datum base objects packages machine)
          (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-frame-return-p '(1 2 3) t before after)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (proof-world-reg 1 after) (if (stringp datum) (+ address 8) 0))
          (equal (proof-world-reg 2 after) (if (stringp datum)
                                             (len (coerce datum 'list))
                                           0)))))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-world-machine proof-world-reg
                        proof-heap-base proof-pointer-address proof-load-word
                        proof-segment-p sequence-string-view-path
                        proof-register-frame-p proof-load-string)
    :use (sequence-string-view-effects
          (:instance sequence-even-tags-mark-even-words (word (proof-world-reg 0 before)))
          (:instance sequence-string-view-of-represented-value
                     (word (proof-world-reg 0 before))
                     (base (proof-heap-base before))
                     (machine (proof-world-machine before))
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address
                                                     (proof-world-reg 0 before)
                                                     (proof-heap-base before))
                                                    objects))))))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-string-view-path (proof-world-reg 0 before)
                                                               (proof-heap-base before)
                                                               (proof-world-machine before)))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute
                             (sequence-string-view-path (proof-world-reg 0 before)
                                                        (proof-heap-base before)
                                                        (proof-world-machine before))
                             before))))))
  :rule-classes nil)
