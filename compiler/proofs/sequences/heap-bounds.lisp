(in-package "BOYMOO-PROOFS")

(include-book "helpers")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-loaded-header-size-is-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal" :use ((:instance sequence-floor-of-unsigned
                                    (dropped 8) (kept 56)
                                    (value (proof-load-word address machine))))))
   :rule-classes :type-prescription))

(local
 (defthm sequence-header-smaller-than-object
   (implies (eq (proof-object-kind object) :header)
            (< (proof-header-size (proof-load-word (proof-object-address object) machine))
               (proof-object-size object machine)))
   :hints (("Goal" :in-theory (disable proof-align-up sequence-loaded-header-size-is-natural)
                   :use ((:instance sequence-align-up-covers-address
                                    (address (proof-header-size
                                              (proof-load-word (proof-object-address object)
                                                               machine)))
                                    (alignment 8))
                         (:instance sequence-loaded-header-size-is-natural
                                    (address (proof-object-address object))))))
   :rule-classes nil))

(defthm sequence-static-object-membership
  (implies (and (member-equal object objects) (eq (proof-object-zone object) :static))
           (member-equal object (proof-static-objects objects)))
  :hints (("Goal" :induct (proof-static-objects objects))))

(defthm sequence-static-span-of-member
  (implies (and (member-equal object statics)
                (proof-static-spans-p statics base size machine))
           (proof-subspan-p (proof-object-address object) (proof-object-size object machine)
                            (+ base 32) (+ base size)))
  :hints (("Goal" :induct (proof-static-spans-p statics base size machine)
                  :in-theory (disable proof-object-size proof-subspan-p)))
  :rule-classes nil)

(local
 (defthm sequence-header-object-span-of-member
   (implies
    (and (eq (proof-object-kind object) :header)
         (member-equal object objects)
         (proof-heap-object-spans-p objects external world))
    (case (proof-object-zone object)
      (:static t)
      (:active (proof-subspan-p (proof-object-address object)
                                (proof-object-size object (proof-world-machine world))
                                (proof-active-floor world) (proof-box-top world)))
      (:external (member-equal (proof-object-address object) external))
      (otherwise nil)))
   :hints (("Goal" :induct (proof-heap-object-spans-p objects external world)
                   :in-theory (disable proof-object-size proof-subspan-p
                                       proof-load-word proof-active-floor proof-box-top)))
   :rule-classes nil))

(local
 (defthm sequence-external-header-length
   (implies
    (member-equal address (cdr (proof-external-objects head fuel world objects)))
    (< (proof-header-size (proof-load-word address (proof-world-machine world)))
       *proof-space-size*))
   :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                   :in-theory (disable proof-header-size proof-load-word proof-align-up
                                       proof-spaces-end proof-stack-base proof-stack-end
                                       proof-disjoint-p proof-machine-limit proof-heap-base)))
   :rule-classes nil))

(local
 (defthm sequence-active-box-area-bound
   (implies (proof-heap-layout-p world)
            (<= (- (proof-box-top world) (proof-active-floor world)) *proof-space-size*))
   :hints (("Goal" :in-theory (disable proof-covered-p proof-align-up
                                      proof-regions-p proof-load-word)))
   :rule-classes nil))

(defthm sequence-published-header-length-bounded
  (implies (and (proof-heap-p world objects packages)
                (member-equal object objects) (eq (proof-object-kind object) :header))
           (< (proof-header-size
               (proof-load-word (proof-object-address object) (proof-world-machine world)))
              *proof-space-size*))
  :hints
  (("Goal"
    :in-theory (disable proof-external-objects proof-heap-object-spans-p
                        proof-heap-layout-p proof-static-spans-p proof-object-size
                        proof-object-map-p proof-align-up proof-load-word proof-header-size
                        proof-limbs-p proof-string-accounting-p proof-stack-prefix
                        proof-static-buckets-p proof-dynamic-view proof-dynamic-entries
                        proof-dynamic-symbol-objects-p proof-package-bindings-p
                        proof-home-bindings-p proof-value-p proof-view
                        proof-active-floor proof-box-top proof-heap-base proof-world-machine)
    :use
    (sequence-active-box-area-bound
     (:instance sequence-header-smaller-than-object (machine (proof-world-machine world)))
     (:instance sequence-static-span-of-member
                (statics (proof-static-objects objects)) (base (proof-heap-base world))
                (size (proof-static-size (proof-heap-base world) (proof-world-machine world)))
                (machine (proof-world-machine world)))
     (:instance sequence-header-object-span-of-member
                (external (cdr (proof-external-objects (proof-external-head world)
                                                      (len objects) world objects))))
     (:instance sequence-external-header-length
                (head (proof-external-head world)) (fuel (len objects))
                (address (proof-object-address object))))))
  :rule-classes nil)

(local
 (defthm sequence-string-view-selects-header
   (let ((object (assoc-equal (proof-pointer-address word base) objects)))
     (implies (and (stringp datum)
                   (equal (proof-view-step :word word 0 depth base objects packages machine)
                          (proof-value-view datum)))
              (and (consp object) (eq (proof-object-kind object) :header))))
   :hints (("Goal"
            :expand ((proof-view-step :word word 0 depth base objects packages machine))
            :in-theory (disable proof-view-step proof-symbol-value proof-rational-value
                                proof-complex-value proof-integer-view proof-load-string
                                proof-pointer-address)))
   :rule-classes nil))

(local
 (defthm sequence-selected-object-is-member
   (implies (consp (assoc-equal address objects))
            (and (member-equal (assoc-equal address objects) objects)
                 (equal (proof-object-address (assoc-equal address objects)) address)))
   :hints (("Goal" :induct (assoc-equal address objects)))
   :rule-classes nil))

(defthm sequence-represented-string-length-bounded
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world)))
    (implies (and (proof-heap-p world objects packages) (stringp datum)
                  (proof-value-p word datum base objects packages machine))
             (< (len (coerce datum 'list)) *proof-space-size*)))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-heap-p proof-world-machine
                        proof-heap-base proof-pointer-address proof-header-size
                        proof-load-word proof-load-string)
    :use
    ((:instance sequence-string-view-selects-header
                (base (proof-heap-base world)) (machine (proof-world-machine world))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                               objects))))))
     (:instance sequence-selected-object-is-member
                (address (proof-pointer-address word (proof-heap-base world))))
     (:instance sequence-published-header-length-bounded
                (object (assoc-equal (proof-pointer-address word (proof-heap-base world)) objects)))
     (:instance sequence-string-view-of-represented-value
                (base (proof-heap-base world)) (machine (proof-world-machine world))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                               objects)))))))))
  :rule-classes nil)
