(in-package "BOYMOO-PROOFS")

(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-root-transport-p (source copy base old-objects new-objects before after)
  (let* ((old (assoc-equal (proof-pointer-address source base) old-objects))
         (new (assoc-equal (proof-pointer-address copy base) new-objects))
         (depth (1+ (nfix (proof-object-rank old)))))
    (and (implies (member-equal (proof-word-tag source) '(0 2))
                  (equal (proof-object-rank old) (proof-object-rank new)))
         (collection-view-transport-p :word source copy 0 depth base
                                      old-objects new-objects before after))))

(local
 (in-theory (disable proof-load-word proof-pointer-address proof-word-tag proof-view
                     collection-view-transport-p assoc-equal)))

(local
 (defthm collection-transported-immediate-has-equal-view
   (implies (and (not (member-equal (proof-word-tag source) '(0 2)))
                 (collection-root-transport-p source copy base
                                              old-objects new-objects before after))
            (equal (proof-view source base old-objects packages before)
                   (proof-view copy base new-objects packages after)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-view collection-view-transport-p)
                            (proof-cons-value proof-symbol-value proof-rational-value
                             proof-complex-value proof-integer-view proof-load-string
                             (:definition ash) (:definition oddp)))))))

(defthm collection-transported-root-has-equal-view
  (implies (collection-root-transport-p source copy base
                                        old-objects new-objects before after)
           (equal (proof-view source base old-objects packages before)
                  (proof-view copy base new-objects packages after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-transport-preserves-view)
                 (:instance collection-transported-immediate-has-equal-view)))))

(defun collection-stack-roots-transported-p
    (count address base old-objects new-objects before after)
  (declare (xargs :measure (nfix count)))
  (or (zp count)
      (and (collection-root-transport-p
            (proof-load-word address before) (proof-load-word address after)
            base old-objects new-objects before after)
           (collection-stack-roots-transported-p
            (1- count) (+ address 8) base old-objects new-objects before after))))

(local (in-theory (disable collection-root-transport-p)))

(defthm collection-transported-stack-roots-have-equal-views
  (implies (collection-stack-roots-transported-p
            count address base old-objects new-objects before after)
           (equal (proof-stack-views count address base old-objects packages before)
                  (proof-stack-views count address base new-objects packages after)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-stack-roots-transported-p
                    count address base old-objects new-objects before after))
          ("Subgoal *1/2"
           :use ((:instance collection-transported-root-has-equal-view
                            (source (proof-load-word address before))
                            (copy (proof-load-word address after)))))))

(local
 (in-theory (disable proof-stack-top proof-stack-base proof-heap-base proof-dynamic-root
                     proof-stack-views collection-stack-roots-transported-p
                     proof-world-machine boymoo-model::a64-unsigned (:definition ash))))

(defthm collection-transported-stack-satisfies-prefix-contract
  (let* ((base (proof-heap-base before))
         (bottom (proof-stack-base before))
         (count (ash (- top bottom) -3)))
    (implies (and (equal (proof-heap-base after) base)
                  (equal (proof-stack-base after) bottom)
                  (<= top (proof-stack-top after))
                  (proof-stack-prefix top before old-objects packages)
                  (collection-stack-roots-transported-p
                   count bottom base old-objects new-objects
                   (proof-world-machine before) (proof-world-machine after)))
             (proof-prefix-preserved-p top before after old-objects new-objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-transported-stack-roots-have-equal-views
                            (count (ash (- top (proof-stack-base before)) -3))
                            (address (proof-stack-base before))
                            (base (proof-heap-base before))
                            (before (proof-world-machine before))
                            (after (proof-world-machine after)))))))

(defthm collection-transported-dynamic-root-preserves-table
  (let* ((base (proof-heap-base before))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and (equal (proof-heap-base after) base)
                  (collection-root-transport-p (proof-dynamic-root base first)
                                               (proof-dynamic-root base last)
                                               base old-objects new-objects first last))
             (proof-dynamic-table-preserved-p nil before after old-objects new-objects
                                              packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-transported-root-has-equal-view
                            (source (proof-dynamic-root (proof-heap-base before)
                                                        (proof-world-machine before)))
                            (copy (proof-dynamic-root (proof-heap-base before)
                                                      (proof-world-machine after)))
                            (base (proof-heap-base before))
                            (before (proof-world-machine before))
                            (after (proof-world-machine after)))))))
