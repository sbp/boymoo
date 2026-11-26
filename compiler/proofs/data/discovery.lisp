(in-package "BOYMOO-PROOFS")

(include-book "objects")

(logic)
(set-verify-guards-eagerness 0)

(defun data-static-word-present-p (word base objects)
  (let ((tag (proof-word-tag word)))
    (and (unsigned-byte-p 64 word)
         (cond ((oddp word) t)
               ((equal tag 4) (unsigned-byte-p 8 (ash word -3)))
               ((member-equal tag '(0 2))
                (let ((object (assoc-equal (proof-pointer-address word base) objects)))
                  (and object (eq (proof-object-kind object) (if (equal tag 0) :cons :header)))))
               (t nil)))))

(defun data-static-field-words-present-p (address count base objects machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (data-static-word-present-p (proof-load-word address machine) base objects)
         (data-static-field-words-present-p (+ address 8) (1- count) base objects machine))))

(defun data-static-task-present-p (task base objects machine)
  (case (car task)
    (:word (data-static-word-present-p (cadr task) base objects))
    (:fields (data-static-field-words-present-p (cadr task) (caddr task) base objects machine))
    (otherwise nil)))

(defun data-static-tasks-present-p (pending base objects machine)
  (if (atom pending)
      (null pending)
    (and (data-static-task-present-p (car pending) base objects machine)
         (data-static-tasks-present-p (cdr pending) base objects machine))))

(local
 (in-theory (disable proof-word-tag proof-pointer-address proof-object-size proof-object-kind
                     proof-object-record-p proof-subspan-p proof-object-disjoint-p
                     proof-load-word data-static-rank data-static-header-work evenp ash)))

(local
 (defthm word-step-retains-object-record
   (implies (assoc-equal address objects)
            (equal (assoc-equal address
                                (mv-nth 2 (data-static-word-step word depth pending objects base size machine)))
                   (assoc-equal address objects)))))

(local
 (defthm scan-step-retains-object-record
   (implies (assoc-equal address objects)
            (equal (assoc-equal address
                                (mv-nth 2 (data-static-scan-step task pending objects base size machine)))
                   (assoc-equal address objects)))
   :hints (("Goal" :in-theory (disable data-static-word-step)))))

(defthmd data-static-scan-retains-object-record
  (implies (assoc-equal address objects)
           (equal (assoc-equal address
                               (mv-nth 1 (data-static-scan pending objects base size machine fuel)))
                  (assoc-equal address objects)))
  :hints (("Goal" :induct (data-static-scan pending objects base size machine fuel)
                  :in-theory (disable data-static-scan-step))))

(local
 (defthm successful-word-step-finds-its-reference
   (mv-let (ok next objects)
     (data-static-word-step word depth pending objects base size machine)
     (declare (ignore next))
     (implies ok (data-static-word-present-p word base objects)))
   :hints (("Goal" :in-theory (enable proof-object-kind)))))

(local
 (defthm word-step-preserves-pending-tasks
   (implies (data-static-tasks-present-p (mv-nth 1 (data-static-word-step
                                                   word depth pending objects base size machine))
                                         base final-objects machine)
            (data-static-tasks-present-p pending base final-objects machine))
   :hints (("Goal" :in-theory (enable data-static-header-work)))))

(local
 (defthm scan-step-accounts-for-task-and-tail
   (mv-let (ok next extended)
     (data-static-scan-step task pending objects base size machine)
     (declare (ignore extended))
     (implies (and ok (data-static-tasks-present-p next base final-objects machine)
                   (implies (eq (car task) :word) (data-static-word-present-p (cadr task) base final-objects)))
              (data-static-tasks-present-p (cons task pending) base final-objects machine)))
   :hints (("Goal" :in-theory (disable data-static-word-step data-static-word-present-p)))))

(local
 (defthm scan-retains-present-word
   (implies (data-static-word-present-p word base objects)
            (data-static-word-present-p word base (mv-nth 1 (data-static-scan
                                                             pending objects base size machine fuel))))
   :hints (("Goal" :use ((:instance data-static-scan-retains-object-record
                                    (address (proof-pointer-address word base))))
                   :in-theory (disable data-static-scan)))))

(defthmd data-static-scan-on-success-covers-tasks
  (mv-let (ok final-objects)
    (data-static-scan pending objects base size machine fuel)
    (implies ok (data-static-tasks-present-p pending base final-objects machine)))
  :hints (("Goal" :induct (data-static-scan pending objects base size machine fuel)
                  :in-theory (disable data-static-word-step data-static-word-present-p))))

(defun data-static-constant-words-present-p (bindings base objects)
  (if (atom bindings)
      (null bindings)
    (and (data-static-word-present-p (proof-constant-word (cdar bindings)) base objects)
         (data-static-constant-words-present-p (cdr bindings) base objects))))

(local
 (defthm constant-work-finds-each-word
   (implies (and (true-listp bindings)
                 (data-static-tasks-present-p (data-static-constant-work bindings depth) base objects machine))
            (data-static-constant-words-present-p bindings base objects))
   :hints (("Goal" :induct (data-static-constant-work bindings depth)
                   :in-theory (disable data-static-word-present-p proof-constant-word)))))

(defthmd data-static-map-on-success-covers-roots
  (mv-let (ok objects) (data-static-image-map base image constants machine)
    (implies ok
             (and (data-static-word-present-p *proof-nil* base objects)
                  (data-static-word-present-p *proof-t* base objects)
                  (data-static-field-words-present-p (+ base 8) 2 base objects machine)
                  (data-static-constant-words-present-p (data-table-bindings constants 12) base objects))))
  :hints (("Goal" :use ((:instance data-static-scan-on-success-covers-tasks
                                   (pending (data-static-image-work base (car image)
                                                                    (data-table-bindings constants 12)))
                                   (objects nil) (size (car image))
                                   (fuel (+ 16 (nfix (car image)) (len (data-table-bindings constants 12))))))
                  :in-theory (disable data-static-scan data-table-bindings data-static-word-present-p
                                      data-static-field-words-present-p data-static-constant-work nfix))))

(defun data-static-record-children-present-p (record base objects machine)
  (mv-let (ok tasks) (data-static-header-work record nil machine)
    (and ok (data-static-tasks-present-p tasks base objects machine))))

(defun data-static-records-children-present-p (records base objects machine)
  (if (atom records)
      (null records)
    (and (data-static-record-children-present-p (car records) base objects machine)
         (data-static-records-children-present-p (cdr records) base objects machine))))

(local
 (defthm header-work-check-does-not-depend-on-pending
   (equal (mv-nth 0 (data-static-header-work record pending machine))
          (mv-nth 0 (data-static-header-work record nil machine)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable data-static-header-work)))))

(local
 (defthm header-work-adds-tasks-before-pending
   (equal (mv-nth 1 (data-static-header-work record pending machine))
          (append (mv-nth 1 (data-static-header-work record nil machine)) pending))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable data-static-header-work)))))

(local
 (defthm header-work-started-empty-is-a-list
   (true-listp (mv-nth 1 (data-static-header-work record nil machine)))
   :hints (("Goal" :in-theory (enable data-static-header-work)))))

(local
 (defthm present-tasks-cover-appended-prefix
   (implies (and (true-listp new) (data-static-tasks-present-p (append new pending) base objects machine))
            (data-static-tasks-present-p new base objects machine))
   :hints (("Goal" :induct (append new pending)))))

(local
 (defthm word-step-accounts-for-new-object-children
   (mv-let (ok next extended)
     (data-static-word-step word depth pending objects base size machine)
     (implies (and ok
                   (data-static-tasks-present-p next base final-objects machine)
                   (data-static-records-children-present-p objects base final-objects machine))
              (data-static-records-children-present-p extended base final-objects machine)))
   :hints (("Goal" :use ((:instance header-work-check-does-not-depend-on-pending
                                    (record (proof-object
                                             (proof-pointer-address word base) :static
                                             (if (equal (proof-word-tag word) 0) :cons :header)
                                             (data-static-rank (- (proof-pointer-address word base) base)))))
                        (:instance header-work-adds-tasks-before-pending
                                    (record (proof-object
                                             (proof-pointer-address word base) :static
                                             (if (equal (proof-word-tag word) 0) :cons :header)
                                             (data-static-rank (- (proof-pointer-address word base) base))))))))))

(local
 (defthm scan-step-accounts-for-new-object-children
   (mv-let (ok next extended)
     (data-static-scan-step task pending objects base size machine)
     (implies (and ok
                   (data-static-tasks-present-p next base final-objects machine)
                   (data-static-records-children-present-p objects base final-objects machine))
              (data-static-records-children-present-p extended base final-objects machine)))
   :hints (("Goal" :in-theory (disable data-static-word-step data-static-records-children-present-p)))))

(defthmd data-static-scan-on-success-closes-object-children
  (mv-let (ok final-objects) (data-static-scan pending objects base size machine fuel)
    (implies (and ok (data-static-records-children-present-p objects base final-objects machine))
             (data-static-records-children-present-p final-objects base final-objects machine)))
  :hints (("Goal" :induct (data-static-scan pending objects base size machine fuel)
                  :in-theory (e/d (data-static-scan-on-success-covers-tasks)
                                 (data-static-scan-step data-static-records-children-present-p)))))

(defthmd data-static-image-map-on-success-closes-object-children
  (mv-let (ok objects) (data-static-image-map base image constants machine)
    (implies ok (data-static-records-children-present-p objects base objects machine)))
  :hints (("Goal" :use ((:instance data-static-scan-on-success-closes-object-children
                                   (pending (data-static-image-work base (car image)
                                                                    (data-table-bindings constants 12)))
                                   (objects nil) (size (car image))
                                   (fuel (+ 16 (nfix (car image)) (len (data-table-bindings constants 12))))))
                  :in-theory (disable data-static-scan data-static-image-work data-table-bindings nfix))))
