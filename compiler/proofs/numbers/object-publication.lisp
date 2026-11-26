(in-package "BOYMOO-PROOFS")

(include-book "memory-footprint")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-view proof-pointer-address proof-word-tag
                     proof-header-type proof-header-size proof-object-size proof-object-address
                     proof-object-word proof-object-record-p proof-object-map-p
                     proof-object-view proof-symbol-object-p
                     proof-object-disjoint-p proof-number-object-memory-p
                     proof-number-objects-memory-p proof-align-up
                     boymoo-model::a64-unsigned acl2::binary-logand mod floor ash)))

(defthm proof-number-object-memory-keeps-symbol-test
  (implies (proof-number-object-memory-p object objects first last)
           (equal (proof-symbol-object-p object last)
                  (proof-symbol-object-p object first)))
  :hints (("Goal"
           :use proof-number-object-memory-keeps-header
           :in-theory (enable proof-symbol-object-p)))
  :rule-classes nil)

(defthm proof-number-object-view-kept
  (implies (and (proof-object-view object base old-objects packages first)
                (proof-number-objects-memory-p old-objects objects first last))
           (equal (proof-object-view object base objects packages last)
                  (proof-object-view object base old-objects packages first)))
  :hints (("Goal"
           :use ((:instance proof-number-view-kept-with-object-memory
                            (word (proof-object-word object base))))
           :in-theory (enable proof-object-view)))
  :rule-classes nil)

(defthm proof-number-object-memory-keeps-disjointness
  (implies (proof-number-objects-memory-p pending objects first last)
           (equal (proof-object-disjoint-p address end pending last)
                  (proof-object-disjoint-p address end pending first)))
  :hints (("Goal"
           :induct (proof-object-disjoint-p address end pending first)
           :in-theory (enable proof-number-objects-memory-p proof-object-disjoint-p))
          ("Subgoal *1/2"
           :use ((:instance proof-number-object-memory-keeps-size (object (car pending)))))
          ("Subgoal *1/3"
           :use ((:instance proof-number-object-memory-keeps-size (object (car pending))))))
  :rule-classes nil)

(defthm proof-number-object-map-kept
  (implies (and (proof-object-map-p pending old-objects symbols base packages first)
                (proof-number-objects-memory-p old-objects objects first last)
                (proof-number-objects-memory-p pending objects first last))
           (proof-object-map-p pending objects symbols base packages last))
  :hints (("Goal"
           :induct (proof-object-map-p pending old-objects symbols base packages first)
           :in-theory (e/d ((:induction proof-object-map-p) proof-number-objects-memory-p)
                           (proof-view proof-disjoint-p proof-span-p))
           :expand ((proof-object-map-p pending old-objects symbols base packages first)
                    (proof-object-map-p pending objects symbols base packages last)
                    (proof-object-map-p nil objects symbols base packages last)))
          (and (member-equal '(not (consp pending)) clause)
               '(:use ((:instance proof-number-object-view-kept (object (car pending)))
                       (:instance proof-number-object-memory-keeps-size (object (car pending)))
                       (:instance proof-number-object-memory-keeps-symbol-test (object (car pending)))
                       (:instance proof-number-object-memory-keeps-disjointness
                                  (address (proof-object-address (car pending)))
                                  (end (+ (proof-object-address (car pending))
                                          (proof-object-size (car pending) first)))
                                  (pending (cdr pending)))))))
  :rule-classes nil)

(local
 (defthm box-header-size-and-type
   (implies (member-equal header '(4100 4101))
            (and (equal (proof-header-size header) 16)
                 (not (equal (proof-header-type header) 2))))))

(defthm proof-number-published-record-extends-map
  (let* ((object (proof-object address :active :header rank))
         (objects (cons object old-objects)))
    (implies (and (proof-span-p address 24)
                  (equal (mod address 8) 0)
                  (natp rank)
                  (member-equal (proof-load-word address last) '(4100 4101))
                  (proof-object-view object base objects packages last)
                  (proof-object-map-p old-objects old-objects nil base packages first)
                  (proof-number-objects-memory-p old-objects objects first last)
                  (proof-object-disjoint-p address (+ address 24) old-objects first))
             (proof-object-map-p objects objects nil base packages last)))
  :hints (("Goal"
           :use ((:instance proof-number-object-map-kept
                            (pending old-objects) (symbols nil)
                            (objects (cons (proof-object address :active :header rank) old-objects)))
                 (:instance proof-number-object-memory-keeps-disjointness
                            (pending old-objects) (end (+ address 24))
                            (objects (cons (proof-object address :active :header rank) old-objects))))
           :expand ((proof-object-map-p
                     (cons (list address :active :header rank) old-objects)
                     (cons (list address :active :header rank) old-objects)
                     nil base packages last))
           :in-theory (enable proof-object-size proof-object-address
                              proof-object-record-p proof-symbol-object-p)
           :do-not-induct t))
  :rule-classes nil)
