(in-package "BOYMOO-PROOFS")

(include-book "data-views")
(include-book "byte-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-value-p proof-object-view proof-object-size proof-object-record-p
                    proof-symbol-object-p proof-object-disjoint-p proof-view proof-view-step))

(defthm p6-view-of-equal-words
  (implies (and (equal left right)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal first second))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-value-p))))

(defthm p6-cons-equality-by-fields
  (implies (and (consp first) (consp second)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal
            (equal first second)
            (and (equal (proof-view (p6-field-word 0 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 0 right base machine) base objects packages machine))
                 (equal (proof-view (p6-field-word 8 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 8 right base machine) base objects packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-value-p)
           :use ((:instance p6-cons-field-views (word left) (value first))
                 (:instance p6-cons-field-views (word right) (value second))))))

(defthm p6-rational-equality-by-parts
  (implies (and (rationalp first) (rationalp second))
           (equal (equal first second)
                  (and (equal (numerator first) (numerator second))
                       (equal (denominator first) (denominator second)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable acl2::rational-implies2)
           :use ((:instance acl2::rational-implies2 (acl2::x first))
                 (:instance acl2::rational-implies2 (acl2::x second))))))

(defthm p6-fraction-equality-by-fields
  (implies (and (rationalp first) (not (integerp first))
                (rationalp second) (not (integerp second))
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal
            (equal first second)
            (and (equal (proof-view (p6-field-word 8 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 8 right base machine) base objects packages machine))
                 (equal (proof-view (p6-field-word 16 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 16 right base machine) base objects packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-value-p)
           :use (p6-rational-equality-by-parts
                 (:instance p6-rational-field-views (word left) (value first))
                 (:instance p6-rational-field-views (word right) (value second))))))

(defthm p6-complex-equality-by-parts
  (implies (and (complex-rationalp first) (complex-rationalp second))
           (equal (equal first second)
                  (and (equal (realpart first) (realpart second))
                       (equal (imagpart first) (imagpart second)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable acl2::realpart-imagpart-elim)
           :use ((:instance acl2::realpart-imagpart-elim (acl2::x first))
                 (:instance acl2::realpart-imagpart-elim (acl2::x second))))))

(defthm p6-complex-equality-by-fields
  (implies (and (complex-rationalp first) (complex-rationalp second)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal
            (equal first second)
            (and (equal (proof-view (p6-field-word 8 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 8 right base machine) base objects packages machine))
                 (equal (proof-view (p6-field-word 16 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 16 right base machine) base objects packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-value-p)
           :use (p6-complex-equality-by-parts
                 (:instance p6-complex-field-views (word left) (value first))
                 (:instance p6-complex-field-views (word right) (value second))))))

(defthm p6-symbol-object-avoids-preceding-identities
  (implies (and (proof-object-map-p pending objects seen base packages machine)
                (member-equal object pending)
                (proof-symbol-object-p object machine))
           (not (member-equal (proof-view-value (proof-object-view object base objects packages machine))
                              seen)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine))))

(defthm p6-symbol-objects-with-same-identity-are-equal
  (implies (and (proof-object-map-p pending objects seen base packages machine)
                (member-equal left pending) (member-equal right pending)
                (proof-symbol-object-p left machine) (proof-symbol-object-p right machine)
                (equal (proof-view-value (proof-object-view left base objects packages machine))
                       (proof-view-value (proof-object-view right base objects packages machine))))
           (equal left right))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine))
          ("Subgoal *1/2"
           :use ((:instance p6-symbol-object-avoids-preceding-identities
                            (pending (cdr pending)) (object left)
                            (seen (cons (proof-view-value (proof-object-view (car pending) base objects packages machine))
                                        seen)))
                 (:instance p6-symbol-object-avoids-preceding-identities
                            (pending (cdr pending)) (object right)
                            (seen (cons (proof-view-value (proof-object-view (car pending) base objects packages machine))
                                        seen)))))))

; The last pair written occupies the sixteen bytes immediately below the
; current top. Both words are interpreted with the same published map.
(defun p6-deferred-conjunction (count top base objects packages machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (equal (proof-view (proof-load-word (- top 16) machine) base objects packages machine)
                (proof-view (proof-load-word (- top 8) machine) base objects packages machine))
         (p6-deferred-conjunction (1- count) (- top 16) base objects packages machine))))

(defthm p6-deferred-conjunction-pop
  (implies (posp count)
           (equal
            (p6-deferred-conjunction count top base objects packages machine)
            (and (equal (proof-view (proof-load-word (- top 16) machine) base objects packages machine)
                        (proof-view (proof-load-word (- top 8) machine) base objects packages machine))
                 (p6-deferred-conjunction (1- count) (- top 16) base objects packages machine))))
  :rule-classes nil
  :hints (("Goal" :expand ((p6-deferred-conjunction count top base objects packages machine)))))

(defthm p6-defer-cons-second-field
  (implies (and (consp first) (consp second)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal
            (and (equal first second)
                 (p6-deferred-conjunction count top base objects packages machine))
            (and (equal (proof-view (p6-field-word 0 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 0 right base machine) base objects packages machine))
                 (equal (proof-view (p6-field-word 8 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 8 right base machine) base objects packages machine))
                 (p6-deferred-conjunction count top base objects packages machine))))
  :rule-classes nil
  :hints (("Goal" :use p6-cons-equality-by-fields :in-theory (disable p6-deferred-conjunction))))

(local
 (defthm p6-lookup-record-key
   (implies (assoc-equal key objects)
            (and (equal (car (assoc-equal key objects)) key)
                 (member-equal (assoc-equal key objects) objects)))
   :hints (("Goal" :induct (assoc-equal key objects)))))

(local
 (defthm p6-header-pointer-round-trip
   (implies (and (integerp base) (unsigned-byte-p 64 word)
                 (equal (proof-word-tag word) 2))
            (equal (boymoo-model::a64-unsigned 64 (+ 2 (- (proof-pointer-address word base) base)))
                   word))
   :hints (("Goal"
            :in-theory (e/d (proof-pointer-address) (p6-unsigned-add p6-unsigned-add-integer))
            :use ((:instance p6-unsigned-add (width 64) (x (+ base (- word 2))) (y (- 2 base))))))))

(local
 (defthm p6-header-lookup-recovers-word
   (let ((record (assoc-equal (proof-pointer-address word base) objects)))
     (implies (and (integerp base) (unsigned-byte-p 64 word)
                   (equal (proof-word-tag word) 2) record
                   (eq (proof-object-kind record) :header))
              (equal (proof-object-word record base) word)))
   :hints (("Goal" :in-theory (e/d (proof-object-word)
                                   (proof-object-kind proof-header-type proof-pointer-address))
                   :use p6-header-pointer-round-trip))))

(defthm p6-symbol-view-identifies-published-record
  (let ((record (assoc-equal (proof-pointer-address word base) objects)))
    (implies (and (proof-value-p word value base objects packages machine)
                  (symbolp value) (integerp base))
             (and (member-equal record objects)
                  (proof-symbol-object-p record machine)
                  (equal (proof-view-value (proof-object-view record base objects packages machine)) value)
                  (equal (proof-object-word record base) word))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-value-p proof-object-view proof-view p6-word-class p6-datum-class
                                          proof-symbol-object-p)
                           (p6-loaded-header-fields proof-header-type proof-load-word
                            proof-object-kind proof-object-rank proof-object-word
                            proof-symbol-value proof-integer-view proof-cons-value
                            proof-rational-value proof-complex-value p6-even-as-mod))
           :use p6-word-class-of-value
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine))))))

(defthm p6-published-symbols-equal-exactly-by-word
  (implies (and (integerp base)
                (proof-object-map-p objects objects nil base packages machine)
                (symbolp first) (symbolp second)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal (equal left right) (equal first second)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-object-map-p proof-view-value proof-object-word)
           :use (p6-view-of-equal-words
                 (:instance p6-symbol-view-identifies-published-record (word left) (value first))
                 (:instance p6-symbol-view-identifies-published-record (word right) (value second))
                 (:instance p6-symbol-objects-with-same-identity-are-equal
                            (pending objects) (seen nil)
                            (left (assoc-equal (proof-pointer-address left base) objects))
                            (right (assoc-equal (proof-pointer-address right base) objects)))))))

(defthm p6-string-view-reads-declared-span
  (let* ((address (proof-pointer-address word base))
         (header (proof-load-word address machine)))
    (implies (and (proof-value-p word value base objects packages machine)
                  (stringp value))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type header) 1)
                  (equal value (proof-load-string (proof-header-size header) (+ 8 address) machine)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-value-p proof-view p6-word-class p6-datum-class)
                           (p6-loaded-header-fields proof-header-type proof-header-size
                            proof-load-word proof-load-string proof-symbol-value proof-integer-view
                            proof-cons-value proof-rational-value proof-complex-value))
           :use p6-word-class-of-value
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine))))))

(defthm p6-string-equality-by-payload-bytes
  (implies (and (stringp first) (stringp second)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (let* ((a (proof-pointer-address left base))
                  (b (proof-pointer-address right base)))
             (equal (equal first second)
                    (equal (proof-byte-list (proof-header-size (proof-load-word a machine)) (+ 8 a) machine)
                           (proof-byte-list (proof-header-size (proof-load-word b machine)) (+ 8 b) machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance p6-string-view-reads-declared-span (word left) (value first))
                 (:instance p6-string-view-reads-declared-span (word right) (value second)))
           :in-theory (disable proof-load-string proof-load-word proof-header-size))))

(defthm p6-defer-numeric-second-field
  (implies (and (or (and (rationalp first) (not (integerp first))
                         (rationalp second) (not (integerp second)))
                    (and (complex-rationalp first) (complex-rationalp second)))
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine))
           (equal
            (and (equal first second)
                 (p6-deferred-conjunction count top base objects packages machine))
            (and (equal (proof-view (p6-field-word 8 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 8 right base machine) base objects packages machine))
                 (equal (proof-view (p6-field-word 16 left base machine) base objects packages machine)
                        (proof-view (p6-field-word 16 right base machine) base objects packages machine))
                 (p6-deferred-conjunction count top base objects packages machine))))
  :rule-classes nil
  :hints (("Goal" :use (p6-fraction-equality-by-fields p6-complex-equality-by-fields)
                  :in-theory (disable p6-deferred-conjunction))))

(defthm p6-cons-comparison-descent
  (implies (and (consp first) (consp second))
           (< (+ (acl2-count (car first)) (acl2-count (cdr first))
                 (acl2-count (car second)) (acl2-count (cdr second)))
              (+ (acl2-count first) (acl2-count second))))
  :rule-classes nil
  :hints (("Goal" :expand ((acl2-count first) (acl2-count second)))))
