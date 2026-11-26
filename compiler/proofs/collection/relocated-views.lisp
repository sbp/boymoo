(in-package "BOYMOO-PROOFS")

(include-book "root-views")

(logic)
(set-verify-guards-eagerness 0)

; The table binds an original tagged pointer word to its forwarded
; word. Immediate data retain their words without an association.
(defun collection-rewritten-word-p (source copy table)
  (if (member-equal (proof-word-tag source) '(0 2))
      (equal (assoc-equal source table) (cons source copy))
    (equal source copy)))

(defun collection-rewritten-fields-p (count source copy table before after)
  (declare (xargs :measure (nfix count)))
  (or (zp count)
      (and (collection-rewritten-word-p
            (proof-load-word source before) (proof-load-word copy after) table)
           (collection-rewritten-fields-p
            (1- count) (+ source 8) (+ copy 8) table before after))))

; The condition for one object inspects its own words and fields.
; Field words use the table even when they refer to another object.
(defun collection-local-copy-p (source copy table base old-objects new-objects before after)
  (let* ((tag (proof-word-tag source))
         (old-address (proof-pointer-address source base))
         (new-address (proof-pointer-address copy base))
         (old (assoc-equal old-address old-objects))
         (new (assoc-equal new-address new-objects))
         (rank (proof-object-rank old)))
    (and (unsigned-byte-p 64 source) (unsigned-byte-p 64 copy)
         (not (oddp source)) (not (oddp copy))
         (equal (proof-word-tag copy) tag)
         old new (natp rank) (equal (proof-object-rank new) rank)
         (if (equal tag 0)
             (and (eq (proof-object-kind old) :cons) (eq (proof-object-kind new) :cons)
                  (proof-span-p old-address 16) (proof-span-p new-address 16)
                  (collection-rewritten-fields-p
                   2 old-address new-address table before after))
           (let* ((header (proof-load-word old-address before))
                  (size (proof-header-size header))
                  (old-fields (+ old-address 8))
                  (new-fields (+ new-address 8)))
             (and (equal tag 2)
                  (eq (proof-object-kind old) :header) (eq (proof-object-kind new) :header)
                  (equal (proof-load-word new-address after) header)
                  (proof-span-p old-address (+ 8 size))
                  (proof-span-p new-address (+ 8 size))
                  (case (proof-header-type header)
                    (1 (equal (proof-byte-list size old-fields before)
                              (proof-byte-list size new-fields after)))
                    (3 (and (equal (proof-load-word old-fields before)
                                   (proof-load-word new-fields after))
                            (collection-same-limb-words-p
                             (1- (ash size -3)) (+ old-fields 8) (+ new-fields 8) before after)))
                    ((2 4 5)
                     (and (equal size 16)
                          (collection-rewritten-fields-p 2 old-fields new-fields table
                                                        before after)))
                    (6 (and (equal (mod size 8) 0)
                            (collection-rewritten-fields-p (ash size -3)
                                                            old-fields new-fields table
                                                            before after)))
                    (otherwise nil))))))))

(defun collection-copy-table-p (entries table base old-objects new-objects before after)
  (if (endp entries)
      t
    (and (collection-local-copy-p (caar entries) (cdar entries) table base
                                   old-objects new-objects before after)
         (collection-copy-table-p (cdr entries) table base old-objects new-objects
                                  before after))))

(local
 (in-theory (disable proof-load-word proof-word-tag proof-pointer-address
                     proof-header-type proof-header-size proof-span-p
                     proof-byte-list collection-same-limb-words-p
                     (:definition ash) (:definition oddp) mod)))

(local
 (defthm collection-copy-table-lookup-gives-object-fields
   (implies (and (collection-copy-table-p entries table base old-objects new-objects
                                           before after)
                 (equal (assoc-equal source entries) (cons source copy)))
            (collection-local-copy-p source copy table base old-objects new-objects
                                     before after))
   :rule-classes nil
   :hints (("Goal" :induct (assoc-equal source entries)
                   :in-theory (disable collection-local-copy-p)))))

(local
 (defthm collection-valid-cons-has-valid-fields
   (implies (proof-cons-value first second) (and first second))
   :rule-classes :forward-chaining))

(local
 (defthm collection-valid-boxed-pair-has-valid-fields
   (implies (or (proof-rational-value first second)
                 (proof-complex-value first second)
                 (proof-symbol-value first second packages))
            (and first second))
   :rule-classes
   ((:forward-chaining :corollary
                        (implies (proof-rational-value first second) (and first second)))
    (:forward-chaining :corollary
                        (implies (proof-complex-value first second) (and first second)))
    (:forward-chaining :corollary
                        (implies (proof-symbol-value first second packages) (and first second))))))

(local
 (in-theory (disable collection-copy-table-p collection-local-copy-p assoc-equal
                     proof-cons-value proof-symbol-value proof-rational-value proof-complex-value
                     proof-limb-magnitude proof-limbs-p proof-integer-view proof-load-string)))

(local
 (defthm collection-rewritten-pointer-has-local-copy
   (implies (and (member-equal (proof-word-tag source) '(0 2))
                 (collection-rewritten-word-p source copy table)
                 (collection-copy-table-p table table base old-objects new-objects before after))
            (collection-local-copy-p source copy table base old-objects new-objects before after))
   :hints (("Goal"
            :use ((:instance collection-copy-table-lookup-gives-object-fields
                             (entries table)))))))

(local
 (defthm collection-rewritten-two-fields
   (equal (collection-rewritten-fields-p 2 source copy table before after)
          (and (collection-rewritten-word-p
                (proof-load-word source before) (proof-load-word copy after) table)
               (collection-rewritten-word-p
                (proof-load-word (+ 8 source) before) (proof-load-word (+ 8 copy) after) table)))
   :hints (("Goal"
            :expand ((:free (source copy)
                            (collection-rewritten-fields-p 2 source copy table before after))
                     (:free (source copy)
                            (collection-rewritten-fields-p 1 source copy table before after))
                     (:free (source copy)
                            (collection-rewritten-fields-p 0 source copy table before after)))
            :in-theory (disable collection-rewritten-word-p collection-rewritten-fields-p)))))

(defthm collection-local-copies-imply-recursive-transport
  (implies (and (collection-copy-table-p table table base old-objects new-objects before after)
                (if (eq kind :slots)
                    (collection-rewritten-fields-p count source copy table before after)
                  (collection-rewritten-word-p source copy table))
                (proof-view-step kind source count depth base old-objects packages before))
           (collection-view-transport-p kind source copy count depth base
                                        old-objects new-objects before after))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-view-transport-p
                    kind source copy count depth base old-objects new-objects before after)
           :expand ((proof-view-step kind source count depth base old-objects packages before)
                    (collection-rewritten-fields-p count source copy table before after))
           :do-not '(generalize))
          (and stable-under-simplificationp
               '(:use ((:instance collection-rewritten-pointer-has-local-copy))
                 :in-theory (e/d (collection-local-copy-p)
                                 (collection-rewritten-pointer-has-local-copy))))))

(defthm collection-local-copies-preserve-valid-root
  (implies (and (collection-copy-table-p table table base old-objects new-objects before after)
                (collection-rewritten-word-p source copy table)
                (proof-view source base old-objects packages before))
           (collection-root-transport-p source copy base old-objects new-objects before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-local-copies-imply-recursive-transport
                            (kind :word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address source base)
                                                           old-objects))))))
                 (:instance collection-rewritten-pointer-has-local-copy))
           :in-theory (e/d (collection-local-copy-p)
                           (collection-rewritten-pointer-has-local-copy
                            proof-view-step collection-view-transport-p)))))

(defthm collection-local-copies-transport-all-stack-roots
  (implies (and (collection-copy-table-p table table base old-objects new-objects before after)
                (collection-rewritten-fields-p count address address table before after)
                (proof-stack-views count address base old-objects packages before))
           (collection-stack-roots-transported-p
            count address base old-objects new-objects before after))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-stack-roots-transported-p
                    count address base old-objects new-objects before after)
           :expand ((proof-stack-views count address base old-objects packages before)
                    (collection-rewritten-fields-p count address address table before after))
           :in-theory (disable collection-root-transport-p collection-rewritten-word-p
                               proof-view proof-view-step collection-view-transport-p))
          ("Subgoal *1/2"
           :use ((:instance collection-local-copies-preserve-valid-root
                            (source (proof-load-word address before))
                            (copy (proof-load-word address after)))))
          ("Subgoal *1/3"
           :use ((:instance collection-local-copies-preserve-valid-root
                            (source (proof-load-word address before))
                            (copy (proof-load-word address after)))))))

(defthm collection-local-copies-establish-stack-and-table-contracts
  (let* ((base (proof-heap-base before))
         (bottom (proof-stack-base before))
         (count (ash (- top bottom) -3))
         (original (proof-world-machine before))
         (copied (proof-world-machine after)))
    (implies (and (equal (proof-heap-base after) base)
                  (equal (proof-stack-base after) bottom)
                  (<= top (proof-stack-top after))
                  (proof-stack-prefix top before old-objects packages)
                  (proof-dynamic-view before old-objects packages)
                  (collection-copy-table-p table table base old-objects new-objects original copied)
                  (collection-rewritten-fields-p count bottom bottom table original copied)
                  (collection-rewritten-word-p (proof-dynamic-root base original)
                                               (proof-dynamic-root base copied) table))
             (and (proof-prefix-preserved-p top before after old-objects new-objects packages)
                  (proof-dynamic-table-preserved-p nil before after old-objects new-objects
                                                   packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-local-copies-transport-all-stack-roots
                            (base (proof-heap-base before))
                            (count (ash (- top (proof-stack-base before)) -3))
                            (address (proof-stack-base before))
                            (before (proof-world-machine before))
                            (after (proof-world-machine after)))
                 (:instance collection-transported-stack-satisfies-prefix-contract)
                 (:instance collection-local-copies-preserve-valid-root
                            (source (proof-dynamic-root (proof-heap-base before)
                                                        (proof-world-machine before)))
                            (copy (proof-dynamic-root (proof-heap-base before)
                                                      (proof-world-machine after)))
                            (base (proof-heap-base before))
                            (before (proof-world-machine before))
                            (after (proof-world-machine after)))
                 (:instance collection-transported-dynamic-root-preserves-table))
           :in-theory (disable collection-rewritten-fields-p collection-rewritten-word-p
                               collection-stack-roots-transported-p collection-root-transport-p
                               proof-dynamic-table-preserved-p proof-prefix-preserved-p
                               proof-heap-base proof-stack-base proof-stack-top
                               proof-dynamic-root proof-world-machine proof-stack-views
                               proof-view proof-view-step collection-view-transport-p))))
