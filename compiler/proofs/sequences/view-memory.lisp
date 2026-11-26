(in-package "BOYMOO-PROOFS")

(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defun sequence-machine-with-memory (memory)
   (boymoo-model::a64-state nil 0 0 0 memory)))

(local
 (defthm sequence-machine-memory-projection
   (equal (boymoo-model::a64-memory (sequence-machine-with-memory memory)) memory)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-memory)))))

(local (in-theory (disable sequence-machine-with-memory)))

(local
 (defmacro sequence-def-memory-only-load (name operation)
   `(defthm ,name
      (implies (syntaxp (not (and (consp machine)
                                  (eq (car machine) 'sequence-machine-with-memory))))
               (equal (,operation count address machine)
                      (,operation count address
                                  (sequence-machine-with-memory
                                   (boymoo-model::a64-memory machine)))))
      :hints (("Goal" :induct (,operation count address machine))))))

(local (sequence-def-memory-only-load sequence-byte-list-uses-only-memory proof-byte-list))
(local (sequence-def-memory-only-load sequence-limbs-use-only-memory proof-limbs-p))
(local (sequence-def-memory-only-load sequence-magnitude-uses-only-memory proof-limb-magnitude))

(defthm sequence-load-string-of-equal-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-load-string count address first)
                  (proof-load-string count address last)))
  :hints (("Goal"
           :in-theory (disable proof-byte-list sequence-byte-list-uses-only-memory)
           :use ((:instance sequence-byte-list-uses-only-memory (machine first))
                 (:instance sequence-byte-list-uses-only-memory (machine last)))))
  :rule-classes nil)

(local
 (defthm sequence-view-step-uses-only-memory
   (equal (proof-view-step kind input count depth base objects packages machine)
          (proof-view-step kind input count depth base objects packages
                           (sequence-machine-with-memory (boymoo-model::a64-memory machine))))
   :hints (("Goal"
            :induct (proof-view-step kind input count depth base objects packages machine)
            :expand ((:free (state kind)
                            (proof-view-step kind input count depth base objects packages state)))
            :in-theory (e/d ((:induction proof-view-step))
                            ((:definition proof-view-step) proof-limbs-p proof-limb-magnitude
                             proof-byte-list proof-symbol-value proof-rational-value
                             proof-complex-value proof-pointer-address proof-header-size
                             proof-header-type))))
   :rule-classes nil))

(defthm sequence-view-step-of-equal-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-view-step kind input count depth base objects packages first)
                  (proof-view-step kind input count depth base objects packages last)))
  :hints (("Goal" :in-theory (disable proof-view-step)
                  :use ((:instance sequence-view-step-uses-only-memory (machine first))
                        (:instance sequence-view-step-uses-only-memory (machine last)))))
  :rule-classes nil)

(defthm sequence-view-of-equal-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-view word base objects packages first)
                  (proof-view word base objects packages last)))
  :hints (("Goal"
           :in-theory (disable proof-view-step proof-pointer-address proof-object-rank)
           :use ((:instance sequence-view-step-of-equal-memory
                            (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base)
                                                           objects)))))))))
  :rule-classes nil)

(defthm sequence-value-view-at-its-own-rank
  (implies (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view datum))
           (proof-value-p word datum base objects packages machine))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-pointer-address proof-word-tag proof-load-word
                        proof-integer-view proof-symbol-value proof-rational-value
                        proof-complex-value proof-load-string)
    :expand ((:free (rank)
                    (proof-view-step :word word 0 rank base objects packages machine)))))
  :rule-classes nil)

(defun sequence-object-lookups-agree-p (pending objects extended)
  (if (atom pending)
      t
    (let ((address (proof-object-address (car pending))))
      (and (or (null (car pending))
               (equal (assoc-equal address extended) (assoc-equal address objects)))
           (sequence-object-lookups-agree-p (cdr pending) objects extended)))))

(local
 (defthm sequence-object-lookup-in-agreeing-map
   (implies (and (sequence-object-lookups-agree-p pending objects extended)
                 (assoc-equal address pending))
            (equal (assoc-equal address extended) (assoc-equal address objects)))
   :hints (("Goal" :induct (assoc-equal address pending)))
   :rule-classes nil))

(local
 (defthm sequence-selected-object-unchanged-in-extension
   (implies (and (sequence-object-lookups-agree-p objects objects extended)
                 (assoc-equal address objects))
            (equal (assoc-equal address extended) (assoc-equal address objects)))
   :hints (("Goal" :use ((:instance sequence-object-lookup-in-agreeing-map
                                    (pending objects)))))
   :rule-classes ((:rewrite :match-free :once))))

(local
 (defthm sequence-new-address-keeps-lookups
   (implies (and (consp record) (natp (proof-object-address record))
                 (not (assoc-equal (proof-object-address record) pending)))
            (sequence-object-lookups-agree-p pending objects (cons record objects)))
   :hints (("Goal" :induct (assoc-equal (proof-object-address record) pending)))))

(defthm sequence-view-step-on-extended-map
  (let ((old (proof-view-step kind input count depth base objects packages machine)))
    (implies (and old (sequence-object-lookups-agree-p objects objects extended))
             (equal (proof-view-step kind input count depth base extended packages machine)
                    old)))
  :hints
  (("Goal"
    :induct (proof-view-step kind input count depth base objects packages machine)
    :expand ((:free (kind records)
                    (proof-view-step kind input count depth base records packages machine)))
    :in-theory (e/d ((:induction proof-view-step))
                    ((:definition proof-view-step) proof-pointer-address proof-word-tag
                     proof-load-word proof-load-string proof-integer-view
                     sequence-object-lookups-agree-p))
    :do-not '(generalize)))
  :rule-classes nil)

(defthm sequence-fresh-object-preserves-old-value-view
  (implies (and (proof-value-p word datum base objects packages machine)
                (consp record) (natp (proof-object-address record))
                (not (assoc-equal (proof-object-address record) objects)))
           (proof-value-p word datum base (cons record objects) packages machine))
  :hints
  (("Goal"
    :in-theory (disable proof-view-step proof-pointer-address proof-object-rank
                        sequence-object-lookups-agree-p)
    :use
    ((:instance sequence-view-step-on-extended-map
                (kind :word) (input word) (count 0) (extended (cons record objects))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word base) objects))))))
     (:instance sequence-value-view-at-its-own-rank
                (objects (cons record objects))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word base) objects)))))))))
  :rule-classes nil)
