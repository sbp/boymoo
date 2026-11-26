(in-package "BOYMOO-PROOFS")

(include-book "map-views")
(include-book "static-bounds")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm object-size-is-positive
   (posp (proof-object-size object machine))
   :rule-classes :type-prescription
   :hints (("Goal" :use ((:instance data-floor-bounds
                                    (x (* -1 (nfix (proof-header-size
                                                   (proof-load-word (proof-object-address object) machine)))))
                                    (d 8)))
                   :in-theory (e/d (ceiling) (floor proof-load-word proof-header-size ash))))))

(local
 (in-theory (disable proof-object-size proof-load-word proof-header-size proof-subspan-p
                     proof-pointer-address proof-word-tag proof-object-word ash floor mod evenp)))

(local
 (defthm disjoint-records-have-different-starts
   (implies (and (proof-object-disjoint-p address end objects machine)
                 (< address end) (integerp address))
            (not (assoc-equal address objects)))
   :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine)))))

(local
 (defthm positive-size-record-is-not-in-disjoint-tail
   (implies (and (proof-object-disjoint-p (car object) (+ (car object) (proof-object-size object machine))
                                          objects machine)
                 (proof-object-record-p object))
            (not (assoc-equal (car object) objects)))
   :hints (("Goal" :use ((:instance disjoint-records-have-different-starts
                                    (address (car object)) (end (+ (car object) (proof-object-size object machine)))))
                   :in-theory (disable disjoint-records-have-different-starts)))))

(local
 (defthm record-is-a-cons
   (implies (proof-object-record-p record)
            (and (consp record) (integerp (car record))))
   :rule-classes :forward-chaining))

(local
 (defthm member-record-has-its-address-in-the-map
   (implies (and (consp record) (car record) (member-equal record records))
            (assoc-equal (car record) records))
   :hints (("Goal" :induct (member-equal record records)))))

(defthmd data-static-head-is-absent-from-disjoint-tail
  (implies (and (consp objects) (data-static-object-spans-p objects base size machine))
           (not (member-equal (car objects) (cdr objects))))
  :hints (("Goal" :use ((:instance positive-size-record-is-not-in-disjoint-tail
                                   (object (car objects)) (objects (cdr objects)))
                        (:instance member-record-has-its-address-in-the-map
                                   (record (car objects)) (records (cdr objects))))
                  :in-theory (disable proof-object-disjoint-p proof-object-record-p))))

(local
 (defthm known-records-are-unaffected-by-a-different-key
   (implies (and (data-static-known-records-p records witness)
                 (not (assoc-equal (car object) records)) (consp object))
            (data-static-known-records-p records (cons object witness)))
   :hints (("Goal" :induct (data-static-known-records-p records witness)))))

(defthmd data-static-distinct-spans-give-self-lookup
  (implies (data-static-object-spans-p objects base size machine)
           (data-static-known-records-p objects objects))
  :hints (("Goal" :induct (data-static-object-spans-p objects base size machine)
                  :in-theory (disable proof-object-record-p proof-object-disjoint-p data-static-rank))
          ("Subgoal *1/2" :use ((:instance positive-size-record-is-not-in-disjoint-tail
                                           (object (car objects)) (objects (cdr objects)))
                                (:instance known-records-are-unaffected-by-a-different-key
                                           (records (cdr objects)) (witness (cdr objects)) (object (car objects))))
                          :in-theory (disable proof-object-record-p proof-object-disjoint-p
                                              data-static-rank known-records-are-unaffected-by-a-different-key
                                              positive-size-record-is-not-in-disjoint-tail))))

(local
 (defthm aligned-address-difference-is-in-whole-words
   (implies (and (integerp address) (integerp base) (equal (mod address 8) 0) (equal (mod base 8) 0))
            (equal (* 8 (- (floor address 8) (floor base 8))) (- address base)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable mod)))))

(local
 (defthm valid-static-object-word-points-to-its-record
   (let* ((address (proof-object-address record))
          (tag (if (eq (proof-object-kind record) :cons) 0 2))
          (word (proof-object-word record base)))
     (implies (and (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0)
                   (proof-object-record-p record)
                   (proof-subspan-p address (proof-object-size record machine) (+ base 32) (+ base size)))
              (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) tag)
                   (equal (proof-pointer-address word base) address))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance aligned-address-difference-is-in-whole-words
                                    (address (proof-object-address record)))
                         (:instance data-static-reference-fits-and-points-at-offset
                                    (slot (- (floor (proof-object-address record) 8) (floor base 8)))
                                    (tag (if (eq (proof-object-kind record) :cons) 0 2))))
                   :in-theory (e/d (proof-object-word proof-subspan-p data-machine-unsigned-is-low-bits)
                                  (boymoo-model::a64-unsigned boymoo-compiler::low-bits))))))

(defun data-static-record-words-present-p (records base objects)
  (if (atom records)
      (null records)
    (and (data-static-word-present-p (proof-object-word (car records) base) base objects)
         (data-static-record-words-present-p (cdr records) base objects))))

(local
 (defthm valid-static-record-word-is-present
   (let ((address (proof-object-address record)))
     (implies (and (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0)
                   (proof-object-record-p record)
                   (proof-subspan-p address (proof-object-size record machine) (+ base 32) (+ base size))
                   (equal (assoc-equal address objects) record))
              (data-static-word-present-p (proof-object-word record base) base objects)))
   :hints (("Goal" :use valid-static-object-word-points-to-its-record
                   :in-theory (disable proof-subspan-p proof-span-p)))))

(defthmd data-static-record-words-present-under-span-bounds
  (implies (and (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0)
                (data-static-object-spans-p records base size machine)
                (data-static-known-records-p records objects))
           (data-static-record-words-present-p records base objects))
  :hints (("Goal" :induct (data-static-object-spans-p records base size machine)
                  :in-theory (disable proof-span-p proof-object-record-p proof-object-disjoint-p
                                      data-static-word-present-p))
          ("Subgoal *1/2" :use ((:instance valid-static-record-word-is-present (record (car records))))
                          :in-theory (disable valid-static-record-word-is-present proof-span-p proof-object-record-p
                                              proof-object-disjoint-p data-static-word-present-p))))

(defthmd data-static-map-record-words-are-present
  (implies (and (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0)
                (data-static-object-spans-p objects base size machine))
           (data-static-record-words-present-p objects base objects))
  :hints (("Goal" :use (data-static-distinct-spans-give-self-lookup
                        (:instance data-static-record-words-present-under-span-bounds (records objects)))
                  :in-theory (disable proof-span-p data-static-object-spans-p
                                      data-static-record-words-present-p data-static-known-records-p))))
