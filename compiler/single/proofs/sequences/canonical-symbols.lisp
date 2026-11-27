(in-package "BOYMOO-PROOFS")

(include-book "symbol-fields")
(include-book "static-roots")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-header-offset-after-wrapped-addition
   (implies (and (integerp base) (integerp word))
            (equal (+ 2 (- base) (mod (+ -2 base word) (expt 2 64)))
                   (+ word (* (expt 2 64) (- (floor (+ -2 base word) (expt 2 64)))))))
   :hints
   (("Goal"
     :in-theory (enable mod)
     :use ((:instance distributivity
                      (acl2::x (expt 2 64))
                      (acl2::y (floor (+ -2 base word) (expt 2 64)))
                      (acl2::z (- (floor (+ -2 base word) (expt 2 64))))))))))

(local
 (defthm sequence-mod-of-word-plus-quotient
   (implies (and (unsigned-byte-p 64 word) (integerp quotient)
                 (equal adjusted (+ word (* (expt 2 64) quotient))))
            (equal (mod adjusted (expt 2 64)) word))
   :hints (("Goal" :in-theory (disable sequence-mod-add-multiple)
            :use ((:instance sequence-mod-add-multiple
                             (value word) (divisor (expt 2 64)) (multiple quotient)))))
   :rule-classes nil))

(defthm sequence-header-word-from-its-address
  (let ((address (proof-pointer-address word base)))
    (implies (and (unsigned-byte-p 64 word) (integerp base) (equal (proof-word-tag word) 2))
             (equal (proof-object-word (proof-object address :static :header rank) base) word)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-pointer-address sequence-a64-unsigned-as-mod)
                    (proof-word-tag sequence-header-offset-after-wrapped-addition))
    :use (sequence-header-offset-after-wrapped-addition
          (:instance sequence-mod-of-word-plus-quotient
                     (adjusted (+ 2 (- base) (mod (+ -2 base word) (expt 2 64))))
                     (quotient (- (floor (+ -2 base word) (expt 2 64))))))))
  :rule-classes nil)

(local
 (defthm sequence-object-lookup-returns-key-and-member
   (implies (assoc-equal address records)
            (and (equal (proof-object-address (assoc-equal address records)) address)
                 (member-equal (assoc-equal address records) records)))
   :hints (("Goal" :induct (assoc-equal address records)))))

(defthm sequence-symbol-record-for-value
  (let* ((address (proof-pointer-address word base))
         (record (assoc-equal address objects)))
    (implies (and (symbolp datum) (integerp base) (proof-value-p word datum base objects packages machine))
             (and (member-equal record objects)
                  (proof-symbol-object-p record machine)
                  (equal (proof-object-word record base) word)
                  (equal (proof-object-view record base objects packages machine)
                         (proof-value-view datum)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-value-p proof-view proof-symbol-object-p proof-object-view proof-object-word)
                    (proof-view-step proof-pointer-address proof-object-rank proof-word-tag
                     proof-load-word proof-header-type oddp evenp))
    :use ((:instance sequence-object-lookup-returns-key-and-member
                     (address (proof-pointer-address word base)) (records objects))
          (:instance sequence-symbol-view-identifies-fields
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address word base) objects))))))
          (:instance sequence-unsigned-word-of-value
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address word base) objects))))))
          (:instance sequence-header-word-from-its-address (rank (proof-object-rank
                                                                  (assoc-equal (proof-pointer-address word base)
                                                                               objects)))))
    :expand ((proof-object-word (assoc-equal (proof-pointer-address word base) objects) base)
             (:free (rank) (proof-object-word (proof-object (proof-pointer-address word base)
                                                           :static :header rank) base)))))
  :rule-classes nil)

(local
 (defun sequence-symbol-map-induction (records objects seen base packages machine)
   (if (atom records)
       seen
     (sequence-symbol-map-induction
      (cdr records) objects
      (if (proof-symbol-object-p (car records) machine)
          (cons (proof-view-value (proof-object-view (car records) base objects packages machine)) seen)
        seen)
      base packages machine))))

(local
 (defthm sequence-listed-symbol-is-not-in-seen-names
   (implies (and (proof-object-map-p records objects seen base packages machine)
                 (member-equal symbol-record records)
                 (proof-symbol-object-p symbol-record machine))
            (not (member-eq (proof-view-value
                             (proof-object-view symbol-record base objects packages machine))
                            seen)))
   :hints
   (("Goal"
     :in-theory (disable proof-symbol-object-p proof-object-view proof-object-record-p
                         proof-object-size proof-object-disjoint-p proof-span-p proof-view-value)
     :induct (sequence-symbol-map-induction records objects seen base packages machine)
     :expand ((proof-object-map-p records objects seen base packages machine))))
   :rule-classes nil))

(defthm sequence-symbol-record-unique-in-map
  (implies (and (proof-object-map-p records objects seen base packages machine)
                (member-equal left records) (member-equal right records)
                (proof-symbol-object-p left machine)
                (proof-symbol-object-p right machine)
                (equal (proof-object-view left base objects packages machine)
                       (proof-object-view right base objects packages machine)))
           (equal left right))
  :hints
  (("Goal"
    :in-theory (disable proof-symbol-object-p proof-object-view proof-object-record-p
                        proof-object-size proof-object-disjoint-p proof-span-p proof-view-value)
    :induct (sequence-symbol-map-induction records objects seen base packages machine)
    :expand ((proof-object-map-p records objects seen base packages machine)))
   ("Subgoal *1/2"
    :use ((:instance sequence-listed-symbol-is-not-in-seen-names
                     (symbol-record left) (records (cdr records))
                     (seen (cons (proof-view-value (proof-object-view (car records) base objects packages machine))
                                 seen)))
          (:instance sequence-listed-symbol-is-not-in-seen-names
                     (symbol-record right) (records (cdr records))
                     (seen (cons (proof-view-value (proof-object-view (car records) base objects packages machine))
                                 seen))))))
  :rule-classes nil)

(local
 (defthm sequence-map-is-valid-in-heap
   (implies (proof-heap-p world objects packages)
            (proof-object-map-p objects objects nil (proof-heap-base world) packages (proof-world-machine world)))
   :hints
   (("Goal"
     :in-theory (disable proof-static-p proof-heap-layout-p proof-object-map-p proof-stack-prefix
                         proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                         proof-dynamic-entries proof-dynamic-view proof-dynamic-symbol-objects-p)
     :expand ((proof-heap-p world objects packages))))
   :rule-classes nil))

(defthm sequence-nil-word-is-canonical
  (implies (and (proof-heap-p world objects packages)
                (proof-machine-value-p word datum world objects packages))
           (equal (equal word *proof-nil*) (null datum)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-machine-value-p proof-value-p)
                    (proof-heap-p proof-view proof-object-map-p proof-symbol-object-p
                     proof-object-view proof-object-word proof-pointer-address proof-world-machine))
    :use (sequence-map-is-valid-in-heap sequence-static-truth-values-in-heap
          (:instance sequence-symbol-record-for-value (datum nil)
                     (base (proof-heap-base world)) (machine (proof-world-machine world)))
          (:instance sequence-symbol-record-for-value (word *proof-nil*) (datum nil)
                     (base (proof-heap-base world)) (machine (proof-world-machine world)))
          (:instance sequence-symbol-record-unique-in-map (records objects) (seen nil)
                     (base (proof-heap-base world)) (machine (proof-world-machine world))
                     (left (assoc-equal (proof-pointer-address word (proof-heap-base world)) objects))
                     (right (assoc-equal (proof-pointer-address *proof-nil* (proof-heap-base world)) objects))))))
  :rule-classes nil)
