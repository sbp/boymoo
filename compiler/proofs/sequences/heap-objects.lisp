(in-package "BOYMOO-PROOFS")

(include-book "object-memory")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-object-view proof-symbol-object-p proof-header-size
                    proof-view proof-value-p proof-object-disjoint-p
                    proof-object-map-p proof-static-spans-p
                    proof-dynamic-symbol-objects-p proof-stack-views))

(local
 (defthm sequence-subset-on-an-enlarged-list
   (implies (subsetp-equal subset whole)
            (subsetp-equal subset (cons object whole)))
   :hints (("Goal" :induct (subsetp-equal subset whole)))))

(defthm sequence-subset-of-itself
  (subsetp-equal objects objects)
  :hints (("Goal" :induct (len objects))))

(local
 (defthm sequence-object-holds-a-word
   (<= 8 (proof-object-size object machine))
   :hints
   (("Goal"
     :in-theory (e/d (proof-object-size proof-header-size proof-load-word) (proof-align-up))
     :use ((:instance sequence-floor-of-unsigned
                      (dropped 8) (kept 56)
                      (value (proof-load-word (proof-object-address object) machine)))
           (:instance sequence-align-up-covers-address
                      (address (proof-header-size
                                (proof-load-word (proof-object-address object) machine)))
                      (alignment 8)))))
   :rule-classes nil))

(defthm sequence-object-head-on-agreed-storage
  (let* ((object (car pending))
         (address (proof-object-address object))
         (size (proof-object-size object first)))
    (implies (and (consp pending)
                  (sequence-object-storage-agrees-p pending first last))
             (and (equal (proof-load-word address last) (proof-load-word address first))
                  (equal (proof-object-size object last) size)
                  (equal (proof-symbol-object-p object last)
                         (proof-symbol-object-p object first))
                  (sequence-object-storage-agrees-p (cdr pending) first last))))
  :hints
  (("Goal"
    :in-theory (enable proof-load-word proof-symbol-object-p proof-object-size)
    :expand ((sequence-object-storage-agrees-p pending first last))
    :use ((:instance sequence-object-holds-a-word (object (car pending)) (machine first))
          (:instance sequence-read-in-agreed-machine-span
                     (start (proof-object-address (car pending)))
                     (end (+ (proof-object-address (car pending))
                             (proof-object-size (car pending) first)))
                     (address (proof-object-address (car pending))) (count 8)))))
  :rule-classes nil)

(defthm sequence-static-storage-on-agreed-objects
  (implies (sequence-object-storage-agrees-p pending first last)
           (sequence-object-storage-agrees-p (proof-static-objects pending) first last))
  :hints
  (("Goal" :induct (proof-static-objects pending)
           :in-theory (e/d (sequence-object-storage-agrees-p) (proof-span-p))))
  :rule-classes nil)

(defthm sequence-object-view-on-agreed-storage
  (implies (sequence-object-storage-agrees-p objects first last)
           (equal (proof-object-view object base objects packages last)
                  (proof-object-view object base objects packages first)))
  :hints (("Goal" :in-theory (enable proof-object-view)
                  :use ((:instance sequence-view-on-agreed-objects
                                   (word (proof-object-word object base))))))
  :rule-classes nil)

(defthm sequence-disjoint-objects-on-agreed-storage
  (implies (sequence-object-storage-agrees-p pending first last)
           (equal (proof-object-disjoint-p start end pending last)
                  (proof-object-disjoint-p start end pending first)))
  :hints
  (("Goal"
    :in-theory (disable proof-disjoint-p)
    :induct (len pending)
    :expand ((:free (machine) (proof-object-disjoint-p start end pending machine))))
   ("Subgoal *1/1" :use sequence-object-head-on-agreed-storage))
  :rule-classes nil)

(defthm sequence-static-spans-on-agreed-objects
  (implies (sequence-object-storage-agrees-p pending first last)
           (equal (proof-static-spans-p pending base size last)
                  (proof-static-spans-p pending base size first)))
  :hints
  (("Goal"
    :in-theory (disable proof-subspan-p)
    :induct (len pending)
    :expand ((:free (machine) (proof-static-spans-p pending base size machine))))
   ("Subgoal *1/1" :use sequence-object-head-on-agreed-storage))
  :rule-classes nil)

(local
 (defun sequence-object-map-induction (pending objects symbols base packages machine)
   (if (atom pending)
       symbols
     (sequence-object-map-induction
      (cdr pending) objects
      (if (proof-symbol-object-p (car pending) machine)
          (cons (proof-view-value (proof-object-view (car pending) base objects packages machine))
                symbols)
        symbols)
      base packages machine))))

(defthm sequence-object-map-on-agreed-storage
  (implies (and (sequence-object-storage-agrees-p pending first last)
                (sequence-object-storage-agrees-p objects first last))
           (equal (proof-object-map-p pending objects symbols base packages last)
                  (proof-object-map-p pending objects symbols base packages first)))
  :hints
  (("Goal"
    :in-theory (disable proof-object-record-p proof-span-p proof-object-size
                        proof-view-value)
    :induct (sequence-object-map-induction pending objects symbols base packages first)
    :expand ((:free (machine) (proof-object-map-p pending objects symbols base packages machine))))
   ("Subgoal *1/2"
    :use (sequence-object-head-on-agreed-storage
          (:instance sequence-object-view-on-agreed-storage (object (car pending)))
          (:instance sequence-disjoint-objects-on-agreed-storage
                     (start (proof-object-address (car pending)))
                     (end (+ (proof-object-address (car pending))
                             (proof-object-size (car pending) first)))
                     (pending (cdr pending))))))
  :rule-classes nil)

(defthm sequence-dynamic-symbols-on-agreed-storage
  (implies (and (sequence-object-storage-agrees-p pending first last)
                (sequence-object-storage-agrees-p objects first last))
           (equal (proof-dynamic-symbol-objects-p pending objects entries base packages last)
                  (proof-dynamic-symbol-objects-p pending objects entries base packages first)))
  :hints
  (("Goal" :induct (len pending)
           :expand ((:free (machine)
                           (proof-dynamic-symbol-objects-p pending objects entries base
                                                           packages machine))))
   ("Subgoal *1/1"
    :use (sequence-object-head-on-agreed-storage
          (:instance sequence-object-view-on-agreed-storage (object (car pending))))))
  :rule-classes nil)

(local
 (defun sequence-stack-slots-induction (count address)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       address
     (sequence-stack-slots-induction (1- count) (+ 8 address)))))

(defthm sequence-stack-views-on-agreed-storage
  (implies (and (sequence-object-storage-agrees-p objects first last)
                (implies (posp count)
                         (and (sequence-machine-span-agrees-p lower upper first last)
                              (proof-subspan-p address (* 8 count) lower upper))))
           (equal (proof-stack-views count address base objects packages last)
                  (proof-stack-views count address base objects packages first)))
  :hints
  (("Goal"
    :induct (sequence-stack-slots-induction count address)
    :expand ((:free (machine) (proof-stack-views count address base objects packages machine))))
   ("Subgoal *1/2"
    :in-theory (enable proof-load-word)
    :expand ((:free (machine) (proof-stack-views count address base objects packages machine))
             (:free (machine) (proof-stack-views 1 address base objects packages machine)))
    :cases ((equal count 1))
    :use ((:instance sequence-read-in-agreed-machine-span
                     (start lower) (end upper) (count 8))
          (:instance sequence-view-on-agreed-objects (word (proof-load-word address first))))))
  :rule-classes nil)
