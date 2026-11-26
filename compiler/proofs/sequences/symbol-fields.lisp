(in-package "BOYMOO-PROOFS")

(include-book "coerce-dispatch")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-integer-word-from-odd-bits
   (implies (and (unsigned-byte-p 64 word) (oddp word))
            (equal (proof-integer-word (floor (boymoo-model::a64-signed 64 word) 2))
                   word))
   :hints
   (("Goal"
     :in-theory (disable oddp evenp sequence-truncate-word-plus-modulus)
     :cases ((< word (expt 2 63)))
     :use ((:instance sequence-floor-half-decomposition (value word))
           (:instance sequence-floor-add-multiple
                      (value word) (divisor 2) (multiple (- (expt 2 63))))
           (:instance sequence-truncate-word-plus-modulus (value (- word (expt 2 64)))))))
   :rule-classes nil))

(defthm sequence-immediate-value-has-canonical-word
  (implies (and (proof-immediate-integer-p datum)
                (equal (proof-view-step :word word 0 depth base objects packages machine)
                       (proof-value-view datum)))
           (equal word (proof-integer-word datum)))
  :hints
  (("Goal"
    :in-theory (disable oddp evenp proof-view-step proof-integer-view proof-load-string
                        proof-rational-value proof-complex-value proof-symbol-value
                        proof-cons-value proof-pointer-address proof-header-size
                        proof-word-tag proof-integer-word sequence-signed-word)
    :expand ((proof-view-step :word word 0 depth base objects packages machine))
    :use sequence-integer-word-from-odd-bits))
  :rule-classes nil)

(local
 (defthm sequence-symbol-value-identifies-fields
   (let ((index (proof-view-value number)))
     (implies (equal (proof-symbol-value name number packages) (proof-value-view datum))
              (and (symbolp datum)
                   (equal name (proof-value-view (symbol-name datum)))
                   (equal number (proof-value-view index))
                   (natp index) (< index (len packages))
                   (proof-immediate-integer-p index)
                   (equal (proof-package-name (nth index packages))
                          (acl2::symbol-package-name datum)))))
   :hints (("Goal" :in-theory (enable proof-symbol-value)))
   :rule-classes :forward-chaining))

(defun sequence-symbol-field-view (offset address rank base objects packages machine)
  (proof-view-step :word (proof-load-word (+ address offset) machine)
                   0 rank base objects packages machine))

(defthm sequence-symbol-view-identifies-fields
  (let* ((address (proof-pointer-address word base))
         (header (proof-load-word address machine))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object))
         (name (sequence-symbol-field-view 8 address rank base objects packages machine))
         (number (sequence-symbol-field-view 16 address rank base objects packages machine))
         (index (proof-view-value number)))
    (implies
     (equal (proof-view-step :word word 0 depth base objects packages machine)
            (proof-value-view datum))
     (and (equal (symbolp datum)
                 (and (not (oddp word)) (equal (proof-word-tag word) 2)
                      (equal (proof-header-type header) 2)))
          (implies (symbolp datum)
                   (and object (natp rank) (< rank depth)
                        (eq (proof-object-kind object) :header)
                        (equal (proof-header-size header) 16)
                        (proof-span-p address 24)
                        (equal name (proof-value-view (symbol-name datum)))
                        (equal number (proof-value-view index))
                        (natp index) (< index (len packages))
                        (proof-immediate-integer-p index)
                        (equal (proof-package-name (nth index packages))
                               (acl2::symbol-package-name datum)))))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-integer-view)
                    (proof-view-step proof-rational-value proof-complex-value proof-symbol-value
                     proof-pointer-address proof-word-tag proof-header-type proof-load-word
                     proof-header-size proof-load-string proof-limb-magnitude proof-limbs-p))
    :expand ((proof-view-step :word word 0 depth base objects packages machine))
    :use ((:instance sequence-symbol-value-identifies-fields
                     (name (sequence-symbol-field-view
                            8 (proof-pointer-address word base)
                            (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))
                            base objects packages machine))
                     (number (sequence-symbol-field-view
                              16 (proof-pointer-address word base)
                              (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))
                              base objects packages machine))))))
  :rule-classes nil)

(defthm sequence-equal-symbol-names-and-packages
  (implies (and (symbolp left) (symbolp right))
           (equal (equal left right)
                  (and (equal (symbol-name left) (symbol-name right))
                       (equal (acl2::symbol-package-name left)
                              (acl2::symbol-package-name right)))))
  :hints
  (("Goal"
    :in-theory (disable acl2::intern-in-package-of-symbol-symbol-name)
    :use ((:instance acl2::intern-in-package-of-symbol-symbol-name
                     (acl2::x left) (acl2::y right))
          (:instance acl2::intern-in-package-of-symbol-symbol-name
                     (acl2::x right) (acl2::y right)))))
  :rule-classes nil)

(local
 (defthm sequence-package-in-list-is-bound
   (implies (and (proof-packages-p packages) (natp index) (< index (len packages)))
            (assoc-equal (proof-package-name (nth index packages)) packages))
   :hints (("Goal" :induct (nth index packages)
                   :in-theory (disable proof-package-imports proof-package-witness
                                       proof-package-visible)))))

(local
 (defun sequence-package-number-induction (index packages start)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (cons start packages)
     (sequence-package-number-induction (1- index) (cdr packages) (1+ start)))))

(defthm sequence-package-number-of-indexed-name
  (implies (and (proof-packages-p packages) (natp index)
                (< index (len packages)) (natp start))
           (equal (proof-package-number (proof-package-name (nth index packages)) packages start)
                  (+ start index)))
  :hints
  (("Goal" :induct (sequence-package-number-induction index packages start)
           :in-theory (disable proof-package-imports proof-package-witness proof-package-visible))
   ("Subgoal *1/2"
    :use ((:instance sequence-package-in-list-is-bound
                     (packages (cdr packages)) (index (1- index))))))
  :rule-classes nil)

(defthm sequence-package-numbers-agree-exactly-for-equal-names
  (implies (and (proof-packages-p packages)
                (natp left) (< left (len packages))
                (natp right) (< right (len packages)))
           (equal (equal (proof-package-name (nth left packages))
                         (proof-package-name (nth right packages)))
                  (equal left right)))
  :hints
  (("Goal"
    :in-theory (disable proof-packages-p proof-package-name proof-package-number)
    :use ((:instance sequence-package-number-of-indexed-name (index left) (start 0))
          (:instance sequence-package-number-of-indexed-name (index right) (start 0)))))
  :rule-classes nil)
