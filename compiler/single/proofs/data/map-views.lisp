(in-package "BOYMOO-PROOFS")

(include-book "scan-completeness")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-word-tag proof-pointer-address proof-object-rank proof-object-size
                     proof-object-kind proof-load-word proof-header-type proof-header-size proof-span-p
                     proof-load-string proof-integer-view proof-cons-value proof-symbol-value
                     proof-rational-value proof-complex-value boymoo-model::a64-signed evenp ash mod)))

(local
 (defthm lookup-finds-its-key
   (implies (assoc-equal address objects)
            (equal (car (assoc-equal address objects)) address))))

(local
 (defthm all-records-present-implies-lookup-children-present
   (implies (and (data-static-records-children-present-p pending base objects machine)
                 (assoc-equal address pending))
            (data-static-record-children-present-p (assoc-equal address pending) base objects machine))
   :hints (("Goal" :induct (assoc-equal address pending)
                   :in-theory (disable data-static-record-children-present-p)))))

(local
 (defthm two-present-fields-give-two-present-words
   (implies (data-static-field-words-present-p address 2 base objects machine)
            (and (data-static-word-present-p (proof-load-word address machine) base objects)
                 (data-static-word-present-p (proof-load-word (+ 8 address) machine) base objects)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable data-static-word-present-p)
                   :expand ((data-static-field-words-present-p address 2 base objects machine)
                            (data-static-field-words-present-p (+ 8 address) 1 base objects machine))))))

(local
 (defthm view-of-cons-has-present-fields
   (let ((record (assoc-equal address objects)))
     (implies (and record (eq (proof-object-kind record) :cons)
                   (data-static-records-children-present-p objects base objects machine))
              (and (data-static-word-present-p (proof-load-word address machine) base objects)
                   (data-static-word-present-p (proof-load-word (+ 8 address) machine) base objects))))
   :hints (("Goal" :use ((:instance all-records-present-implies-lookup-children-present (pending objects))
                         two-present-fields-give-two-present-words)
                   :in-theory (disable data-static-word-present-p data-static-records-children-present-p
                                       all-records-present-implies-lookup-children-present)))))

(local
 (defthm view-of-two-field-header-has-present-fields
   (let* ((record (assoc-equal address objects)) (header (proof-load-word address machine)))
     (implies (and record (eq (proof-object-kind record) :header)
                   (member-equal (proof-header-type header) '(2 4 5)) (equal (proof-header-size header) 16)
                   (data-static-records-children-present-p objects base objects machine))
              (and (data-static-word-present-p (proof-load-word (+ 8 address) machine) base objects)
                   (data-static-word-present-p (proof-load-word (+ 16 address) machine) base objects))))
   :hints (("Goal" :use ((:instance all-records-present-implies-lookup-children-present (pending objects))
                         (:instance two-present-fields-give-two-present-words (address (+ 8 address))))
                   :in-theory (disable data-static-word-present-p data-static-records-children-present-p
                                       all-records-present-implies-lookup-children-present)))))

(local
 (defthm view-of-vector-has-present-slots
   (let* ((record (assoc-equal address objects))
          (header (proof-load-word address machine))
          (size (proof-header-size header)))
     (implies (and record (eq (proof-object-kind record) :header)
                   (equal (proof-header-type header) 6) (equal (mod size 8) 0)
                   (data-static-records-children-present-p objects base objects machine))
              (data-static-field-words-present-p (+ 8 address) (ash size -3) base objects machine)))
   :hints (("Goal" :use ((:instance all-records-present-implies-lookup-children-present (pending objects)))
                   :in-theory (disable data-static-field-words-present-p data-static-records-children-present-p
                                       all-records-present-implies-lookup-children-present)))))

(local
 (defthm present-reference-has-same-record
   (let ((tag (proof-word-tag word)) (address (proof-pointer-address word base)))
     (implies (and (not (oddp word)) (member-equal tag '(0 2))
                   (data-static-word-present-p word base objects)
                   (data-static-known-records-p objects witness))
              (equal (assoc-equal address witness) (assoc-equal address objects))))
   :hints (("Goal" :use ((:instance data-static-known-lookup-agrees
                                    (records objects) (address (proof-pointer-address word base))))
                   :in-theory (disable data-static-known-records-p)))))

(defthmd data-symbol-record-has-present-fields
  (let ((address (proof-object-address record)))
    (implies (and (proof-symbol-object-p record machine)
                  (data-static-record-children-present-p record base objects machine))
             (and (data-static-word-present-p (proof-load-word (+ 8 address) machine) base objects)
                  (data-static-word-present-p (proof-load-word (+ 16 address) machine) base objects))))
  :hints (("Goal" :use ((:instance two-present-fields-give-two-present-words
                                   (address (+ 8 (proof-object-address record)))))
                  :in-theory (disable data-static-word-present-p))))

(local
 (in-theory (disable data-static-record-children-present-p data-static-records-children-present-p
                     data-static-known-records-p data-static-word-present-p data-static-header-work)))

(defthmd data-view-step-agrees-with-witness-map
  (implies (and (data-static-known-records-p objects witness)
                (data-static-records-children-present-p objects base objects machine)
                (if (eq kind :slots)
                    (data-static-field-words-present-p input count base objects machine)
                  (data-static-word-present-p input base objects)))
           (equal (proof-view-step kind input count depth base objects packages machine)
                  (proof-view-step kind input count depth base witness packages machine)))
  :hints (("Goal" :induct (proof-view-step kind input count depth base objects packages machine)
                  :in-theory (e/d ((:induction proof-view-step))
                                 ((:definition proof-view-step) (:executable-counterpart proof-view-step) assoc-equal))
                  :expand ((:free (mode) (proof-view-step mode input count depth base objects packages machine))
                           (:free (mode) (proof-view-step mode input count depth base witness packages machine))))))

(defthmd data-view-agrees-with-witness-map
  (implies (and (data-static-known-records-p objects witness)
                (data-static-records-children-present-p objects base objects machine)
                (data-static-word-present-p word base objects))
           (equal (proof-view word base objects packages machine)
                  (proof-view word base witness packages machine)))
  :hints (("Goal" :use ((:instance data-view-step-agrees-with-witness-map
                                   (kind :word) (input word) (count 0)
                                   (depth (1+ (nfix (proof-object-rank
                                                     (assoc-equal (proof-pointer-address word base) objects))))))
                        (:instance data-view-at-greater-rank (objects witness)
                                   (depth (1+ (nfix (proof-object-rank
                                                     (assoc-equal (proof-pointer-address word base) objects)))))))
                  :in-theory (e/d (data-static-word-present-p)
                                 (proof-view-step assoc-equal)))))
