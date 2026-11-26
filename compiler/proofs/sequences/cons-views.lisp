(in-package "BOYMOO-PROOFS")

(include-book "coerce-list")
(include-book "returns")
(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-datum-view-at-sufficient-rank
  (let* ((tag (proof-word-tag word))
         (object (assoc-equal (proof-pointer-address word base) objects)))
    (implies
     (and (proof-value-p word datum base objects packages machine)
          (natp depth)
          (or (oddp word) (equal tag 4) (< (proof-object-rank object) depth)))
     (equal (proof-view-step :word word 0 depth base objects packages machine)
            (proof-value-view datum))))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-pointer-address proof-load-word proof-word-tag
                        proof-load-string proof-integer-view proof-symbol-value
                        proof-rational-value proof-complex-value oddp evenp)
    :expand ((:free (rank)
                    (proof-view-step :word word 0 rank base objects packages machine)))))
  :rule-classes nil)

(defthm sequence-cons-value-from-ranked-fields
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object)))
    (implies
     (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 0)
          object (eq (proof-object-kind object) :cons)
          (natp rank) (proof-span-p address 16)
          (equal (proof-view-step :word (proof-load-word address machine)
                                  0 rank base objects packages machine)
                 (proof-value-view first))
          (equal (proof-view-step :word (proof-load-word (+ 8 address) machine)
                                  0 rank base objects packages machine)
                 (proof-value-view rest)))
     (proof-value-p word (cons first rest) base objects packages machine)))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-pointer-address proof-load-word proof-word-tag
                        sequence-even-tags-mark-even-words oddp evenp)
    :expand ((:free (rank)
                    (proof-view-step :word word 0 rank base objects packages machine)))
    :use sequence-even-tags-mark-even-words))
  :rule-classes nil)

(defthm sequence-character-view-at-any-rank
  (implies (and (unsigned-byte-p 8 byte) (natp depth))
           (equal (proof-view-step :word (+ 4 (* 8 byte)) 0 depth base objects packages machine)
                  (proof-value-view (code-char byte))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-a64-unsigned-as-mod)
                    (proof-view-step proof-value-p sequence-tagged-character-view
                     sequence-mod-add-multiple))
    :use (sequence-tagged-character-view
          (:instance sequence-mod-add-multiple (value 4) (divisor 8) (multiple byte))
          (:instance sequence-datum-view-at-sufficient-rank
                     (word (+ 4 (* 8 byte))) (datum (code-char byte))))))
  :rule-classes nil)

(defthm sequence-cell-word-is-relative-pointer
  (let ((word (sequence-cell-word cell base)))
    (implies (and (unsigned-byte-p 64 cell) (natp base) (<= base cell)
                  (equal (mod (- cell base) 8) 0))
             (and (unsigned-byte-p 64 word)
                  (equal (proof-word-tag word) 0)
                  (equal (proof-pointer-address word base) cell))))
  :hints (("Goal" :in-theory (enable sequence-a64-unsigned-as-mod)))
  :rule-classes nil)
