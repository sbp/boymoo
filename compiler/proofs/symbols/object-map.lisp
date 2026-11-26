(in-package "BOYMOO-PROOFS")

(include-book "layout")

(logic)
(set-verify-guards-eagerness 0)

; An extension keeps the record at each address in the smaller map.
(defun symbols-object-map-extension-p (partial full)
  (if (atom partial)
      t
    (and (equal (assoc-equal (caar partial) full) (car partial))
         (symbols-object-map-extension-p (cdr partial) full))))

(defthmd symbols-map-extension-keeps-association
  (implies (and (symbols-object-map-extension-p partial full)
                (assoc-equal address partial))
           (equal (assoc-equal address full) (assoc-equal address partial)))
  :hints (("Goal" :induct (assoc-equal address partial)))
  :rule-classes ((:rewrite :match-free :all)))

(local
 (defthm symbols-absent-component-has-no-view
   (and (not (proof-cons-value nil second)) (not (proof-cons-value first nil))
        (not (proof-rational-value nil second)) (not (proof-rational-value first nil))
        (not (proof-complex-value nil second)) (not (proof-complex-value first nil))
        (not (proof-symbol-value nil second packages)) (not (proof-symbol-value first nil packages)))))

(local
 (defthm symbols-map-extension-keeps-view-step
   (implies (and (symbols-object-map-extension-p partial full)
                 (proof-view-step kind input count depth base partial packages machine))
            (equal (proof-view-step kind input count depth base full packages machine)
                   (proof-view-step kind input count depth base partial packages machine)))
   :hints (("Goal"
            :induct (proof-view-step kind input count depth base partial packages machine)
            :expand ((:free (kind) (proof-view-step kind input count depth base full packages machine))
                     (:free (kind) (proof-view-step kind input count depth base partial packages machine)))
            :in-theory (e/d (symbols-map-extension-keeps-association)
                            ((:definition proof-view-step) symbols-object-map-extension-p
                             proof-load-word proof-word-tag proof-pointer-address proof-object-rank
                             proof-object-kind proof-header-type proof-header-size proof-span-p
                             proof-cons-value proof-symbol-value proof-rational-value proof-complex-value
                             proof-load-string proof-integer-view assoc-equal
                             boymoo-model::a64-signed boymoo-model::a64-unsigned ash floor mod))))
   :rule-classes nil))

(local
 (defthm symbols-view-without-association-is-independent-of-rank
   (implies (not (assoc-equal (proof-pointer-address word base) objects))
            (equal (proof-view-step :word word 0 first base objects packages machine)
                   (proof-view-step :word word 0 last base objects packages machine)))
   :hints (("Goal"
            :expand ((:free (rank) (proof-view-step :word word 0 rank base objects packages machine)))
            :in-theory (disable proof-view-step proof-pointer-address assoc-equal proof-word-tag)))
   :rule-classes nil))

(defthm symbols-map-extension-keeps-view
  (implies (and (symbols-object-map-extension-p partial full)
                (proof-view word base partial packages machine))
           (equal (proof-view word base full packages machine)
                  (proof-view word base partial packages machine)))
  :hints (("Goal"
           :use ((:instance symbols-map-extension-keeps-view-step (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                             (assoc-equal (proof-pointer-address word base) partial))))))
                 (:instance symbols-map-extension-keeps-view-step (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                             (assoc-equal (proof-pointer-address word base) full))))))
                 (:instance symbols-view-without-association-is-independent-of-rank (objects partial)
                            (first (1+ (nfix (proof-object-rank
                                             (assoc-equal (proof-pointer-address word base) partial)))))
                            (last (1+ (nfix (proof-object-rank
                                            (assoc-equal (proof-pointer-address word base) full))))))
                 (:instance symbols-map-extension-keeps-association (address (proof-pointer-address word base))))
           :in-theory (disable proof-view-step symbols-object-map-extension-p proof-object-rank
                               proof-pointer-address assoc-equal)))
  :rule-classes nil)

(local
 (defthm symbols-object-size-is-positive
   (< 0 (proof-object-size object machine))
   :hints (("Goal" :in-theory (disable proof-object-address proof-object-kind
                                     proof-header-size proof-load-word)))
   :rule-classes :linear))

(local
 (defthm symbols-disjoint-objects-have-different-addresses
   (implies (and (rationalp address) (< address end)
                 (proof-object-disjoint-p address end objects machine))
            (not (member-equal address (strip-cars objects))))
   :hints (("Goal" :induct (strip-cars objects)
                   :in-theory (e/d (proof-object-address) (proof-object-size))))))

(defthm symbols-valid-object-map-has-unique-addresses
  (implies (proof-object-map-p pending objects seen base packages machine)
           (and (alistp pending) (no-duplicatesp-equal (strip-cars pending))))
  :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine)
                  :in-theory (disable proof-object-view proof-symbol-object-p proof-span-p proof-object-size mod))
          ("Subgoal *1/2"
           :use ((:instance symbols-disjoint-objects-have-different-addresses
                            (objects (cdr pending)) (address (proof-object-address (car pending)))
                            (end (+ (proof-object-address (car pending)) (proof-object-size (car pending) machine)))))
           :in-theory (disable proof-object-view proof-symbol-object-p proof-span-p proof-object-size
                               symbols-disjoint-objects-have-different-addresses mod)))
  :rule-classes nil)

(local
 (defthm symbols-static-objects-form-an-alist
   (implies (alistp objects) (alistp (proof-static-objects objects)))
   :hints (("Goal" :induct (proof-static-objects objects)))))

(local
 (defthm symbols-association-iff-member-key
   (implies (alistp objects)
            (iff (assoc-equal address objects) (member-equal address (strip-cars objects))))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm symbols-submap-records-make-extension
   (implies (and (symbols-object-map-extension-p partial full) (consp object)
                 (equal (assoc-equal (car object) full) object))
            (symbols-object-map-extension-p (cons object partial) full))))

(local
 (defthm symbols-static-submap-of-tail-is-extension
   (implies (and (alistp partial)
                 (symbols-object-map-extension-p partial full)
                 (not (assoc-equal (car object) full)))
            (symbols-object-map-extension-p partial (cons object full)))
   :hints (("Goal" :induct (symbols-object-map-extension-p partial full)))
   :rule-classes nil))

(defthm symbols-static-objects-extend-to-object-map
  (implies (and (alistp objects) (no-duplicatesp-equal (strip-cars objects)))
           (symbols-object-map-extension-p (proof-static-objects objects) objects))
  :hints (("Goal" :induct (proof-static-objects objects))
          ("Subgoal *1/3"
           :use ((:instance symbols-static-submap-of-tail-is-extension
                            (object (car objects)) (full (cdr objects))
                            (partial (proof-static-objects (cdr objects))))))
          ("Subgoal *1/2"
           :use ((:instance symbols-static-submap-of-tail-is-extension
                            (object (car objects)) (full (cdr objects))
                            (partial (proof-static-objects (cdr objects)))))))
  :rule-classes nil)

(defthm symbols-static-view-in-live-objects
  (implies (and (proof-object-map-p objects objects nil base packages machine)
                (proof-view word base (proof-static-objects objects) packages machine))
           (equal (proof-view word base objects packages machine)
                  (proof-view word base (proof-static-objects objects) packages machine)))
  :hints (("Goal"
           :use ((:instance symbols-static-objects-extend-to-object-map)
                 (:instance symbols-valid-object-map-has-unique-addresses (pending objects) (seen nil))
                 (:instance symbols-map-extension-keeps-view (partial (proof-static-objects objects)) (full objects)))
           :in-theory (disable proof-view proof-object-map-p proof-static-objects
                               symbols-object-map-extension-p)))
  :rule-classes nil)

(defthm symbols-static-nil-in-live-objects
  (implies (and (proof-static-p base objects packages machine)
                (proof-object-map-p objects objects nil base packages machine))
           (proof-value-p *proof-nil* nil base objects packages machine))
  :hints (("Goal"
           :use ((:instance symbols-static-view-in-live-objects (word *proof-nil*)))
           :in-theory (disable proof-view proof-object-map-p proof-static-objects proof-static-spans-p
                               proof-home-bindings-p proof-static-buckets-p proof-package-bindings-p
                               proof-packages-p proof-load-word)))
  :rule-classes nil)

(defthm symbols-static-package-row-fields-in-live-objects
  (let* ((address (proof-pointer-address (symbols-static-package-row-word number base machine) base))
         (row (nth number packages)))
    (implies (and (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (natp number) (< number (len packages)))
             (and (proof-value-p (proof-load-word (+ address 8) machine)
                                 (proof-package-name row) base objects packages machine)
                  (proof-value-p (proof-load-word (+ address 16) machine)
                                 (proof-package-imports row) base objects packages machine)
                  (proof-value-p (proof-load-word (+ address 24) machine)
                                 (if (proof-package-visible row) (proof-package-witness row) nil)
                                 base objects packages machine))))
  :hints (("Goal"
           :use ((:instance symbols-static-package-row-fields)
                 (:instance symbols-static-view-in-live-objects
                            (word (proof-load-word
                                   (+ 8 (proof-pointer-address (symbols-static-package-row-word number base machine) base))
                                   machine)))
                 (:instance symbols-static-view-in-live-objects
                            (word (proof-load-word
                                   (+ 16 (proof-pointer-address (symbols-static-package-row-word number base machine) base))
                                   machine)))
                 (:instance symbols-static-view-in-live-objects
                            (word (proof-load-word
                                   (+ 24 (proof-pointer-address (symbols-static-package-row-word number base machine) base))
                                   machine))))
           :in-theory (disable proof-view proof-object-map-p proof-static-objects proof-static-p proof-load-word
                               proof-pointer-address symbols-static-package-row-word)))
  :rule-classes nil)
