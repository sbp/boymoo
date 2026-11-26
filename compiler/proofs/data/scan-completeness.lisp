(in-package "BOYMOO-PROOFS")

(include-book "discovery")
(include-book "fuel")

(logic)
(set-verify-guards-eagerness 0)

(defun data-reference-record (word base)
  (let ((address (proof-pointer-address word base)))
    (proof-object address :static (if (equal (proof-word-tag word) 0) :cons :header)
                  (data-static-rank (- address base)))))

(defun data-ranked-word-p (word depth base witness)
  (let ((tag (proof-word-tag word)))
    (and (unsigned-byte-p 64 word)
         (cond ((oddp word) t)
               ((equal tag 4) (unsigned-byte-p 8 (ash word -3)))
               ((member-equal tag '(0 2))
                (let ((record (data-reference-record word base)))
                  (and (equal (assoc-equal (proof-object-address record) witness) record)
                       (< (proof-object-rank record) depth))))
               (t nil)))))

(defun data-ranked-field-words-p (address count depth base witness machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (data-ranked-word-p (proof-load-word address machine) depth base witness)
         (data-ranked-field-words-p (+ address 8) (1- count) depth base witness machine))))

(defun data-ranked-task-p (task base witness machine)
  (case (car task)
    (:word (data-ranked-word-p (cadr task) (caddr task) base witness))
    (:fields (data-ranked-field-words-p (cadr task) (caddr task) (cadddr task)
                                        base witness machine))
    (otherwise nil)))

(defun data-ranked-tasks-p (pending base witness machine)
  (if (atom pending)
      (null pending)
    (and (data-ranked-task-p (car pending) base witness machine)
         (data-ranked-tasks-p (cdr pending) base witness machine))))

(defun data-ranked-records-p (records base witness machine)
  (if (atom records)
      (null records)
    (mv-let (ok children) (data-static-header-work (car records) nil machine)
      (and ok (data-ranked-tasks-p children base witness machine)
           (data-ranked-records-p (cdr records) base witness machine)))))

(defun data-static-known-records-p (records witness)
  (if (atom records)
      (null records)
    (and (consp (car records))
         (equal (assoc-equal (caar records) witness) (car records))
         (data-static-known-records-p (cdr records) witness))))

(local
 (in-theory (disable proof-object-record-p proof-object-size proof-subspan-p
                     proof-load-word proof-pointer-address proof-word-tag data-static-rank
                     proof-header-size proof-header-type evenp ash)))

(defthmd data-static-known-lookup-agrees
  (implies (and (data-static-known-records-p records witness) (assoc-equal address records))
           (equal (assoc-equal address witness) (assoc-equal address records)))
  :hints (("Goal" :induct (assoc-equal address records))))

(local
 (defthm lookup-is-a-member-of-records
   (implies (assoc-equal address records)
            (member-equal (assoc-equal address records) records))
   :hints (("Goal" :induct (assoc-equal address records)))))

(local
 (defthm member-has-record-and-span
   (implies (and (data-static-object-spans-p witness base size machine)
                 (member-equal record witness))
            (and (proof-object-record-p record)
                 (proof-subspan-p (proof-object-address record) (proof-object-size record machine)
                                  (+ base 32) (+ base size))))
   :hints (("Goal" :induct (data-static-object-spans-p witness base size machine)
                   :in-theory (disable proof-object-disjoint-p)))))

(local
 (defthm member-obeys-object-disjointness
   (implies (and (proof-object-disjoint-p start end records machine)
                 (member-equal record records))
            (proof-disjoint-p start end (proof-object-address record)
                              (+ (proof-object-address record) (proof-object-size record machine))))
   :hints (("Goal" :induct (proof-object-disjoint-p start end records machine)
                   :in-theory (disable proof-disjoint-p)))))

(local
 (defthm disjointness-is-symmetric
   (implies (proof-disjoint-p start end other-start other-end)
            (proof-disjoint-p other-start other-end start end))
   :rule-classes nil))

(local
 (defthm distinct-members-are-disjoint
   (implies (and (data-static-object-spans-p witness base size machine)
                 (member-equal record witness) (member-equal other witness)
                 (not (equal record other)))
            (proof-disjoint-p (proof-object-address record)
                              (+ (proof-object-address record) (proof-object-size record machine))
                              (proof-object-address other)
                              (+ (proof-object-address other) (proof-object-size other machine))))
   :rule-classes nil
   :hints (("Goal" :induct (data-static-object-spans-p witness base size machine)
                   :in-theory (disable proof-object-disjoint-p proof-disjoint-p
                                       member-has-record-and-span member-obeys-object-disjointness))
           ("Subgoal *1/2" :use ((:instance disjointness-is-symmetric
                                            (start (proof-object-address other))
                                            (end (+ (proof-object-address other) (proof-object-size other machine)))
                                            (other-start (proof-object-address record))
                                            (other-end (+ (proof-object-address record)
                                                          (proof-object-size record machine))))
                                 (:instance member-obeys-object-disjointness
                                            (record other) (records (cdr witness))
                                            (start (proof-object-address (car witness)))
                                            (end (+ (proof-object-address (car witness))
                                                    (proof-object-size (car witness) machine))))
                                 (:instance member-obeys-object-disjointness
                                            (records (cdr witness))
                                            (start (proof-object-address (car witness)))
                                            (end (+ (proof-object-address (car witness))
                                                    (proof-object-size (car witness) machine)))))))))

(local
 (defthm witness-record-disjoint-from-known-records
   (implies (and (data-static-object-spans-p witness base size machine)
                 (member-equal record witness) (consp record)
                 (data-static-known-records-p records witness)
                 (not (assoc-equal (proof-object-address record) records)))
            (proof-object-disjoint-p (proof-object-address record)
                                     (+ (proof-object-address record) (proof-object-size record machine))
                                     records machine))
   :rule-classes nil
   :hints (("Goal" :induct (data-static-known-records-p records witness)
                   :in-theory (disable data-static-object-spans-p proof-disjoint-p))
           ("Subgoal *1/2" :use ((:instance distinct-members-are-disjoint (other (car records)))
                                 (:instance lookup-is-a-member-of-records
                                            (address (caar records)) (records witness)))))))

(local
 (defthm admitted-record-supplies-admitted-work
   (implies (and (data-ranked-records-p records base witness machine)
                 (member-equal record records)
                 (data-ranked-tasks-p pending base witness machine))
            (mv-let (ok children) (data-static-header-work record pending machine)
              (and ok (data-ranked-tasks-p children base witness machine))))
   :hints (("Goal" :induct (data-ranked-records-p records base witness machine)
                   :in-theory (disable data-static-header-work data-ranked-tasks-p))
           ("Subgoal *1/2" :in-theory (e/d (data-static-header-work data-ranked-tasks-p)
                                          (data-ranked-field-words-p data-ranked-word-p))))))

(local
 (defthm witness-reference-passes-allocation-checks
   (implies (and (data-static-object-spans-p witness base size machine)
                 (data-static-known-records-p objects witness)
                 (consp record)
                 (equal (assoc-equal (proof-object-address record) witness) record)
                 (not (assoc-equal (proof-object-address record) objects)))
            (and (proof-object-record-p record)
                 (proof-subspan-p (proof-object-address record) (proof-object-size record machine)
                                  (+ base 32) (+ base size))
                 (proof-object-disjoint-p (proof-object-address record)
                                          (+ (proof-object-address record) (proof-object-size record machine))
                                          objects machine)))
   :hints (("Goal" :use ((:instance witness-record-disjoint-from-known-records (records objects))
                        member-has-record-and-span
                        (:instance lookup-is-a-member-of-records
                                   (address (proof-object-address record)) (records witness)))
                   :in-theory (disable data-static-object-spans-p data-static-known-records-p
                                       member-has-record-and-span lookup-is-a-member-of-records
                                       proof-object-disjoint-p)))))

(local
 (in-theory (disable data-static-object-spans-p proof-object-disjoint-p data-static-header-work
                     data-ranked-records-p data-ranked-tasks-p)))

(local
 (defthm admitted-word-step-succeeds
   (implies (and (data-static-object-spans-p witness base size machine)
                 (data-ranked-records-p witness base witness machine)
                 (data-static-known-records-p objects witness)
                 (data-ranked-word-p word depth base witness)
                 (data-ranked-tasks-p pending base witness machine))
            (mv-let (ok next extended) (data-static-word-step word depth pending objects base size machine)
              (and ok (data-static-known-records-p extended witness)
                   (data-ranked-tasks-p next base witness machine))))
   :hints (("Goal" :use ((:instance data-static-known-lookup-agrees
                                    (address (proof-pointer-address word base)) (records objects))
                         (:instance admitted-record-supplies-admitted-work
                                    (records witness) (record (data-reference-record word base)))
                         (:instance lookup-is-a-member-of-records
                                    (address (proof-pointer-address word base)) (records witness))
                         (:instance witness-reference-passes-allocation-checks
                                    (record (data-reference-record word base))))
                   :in-theory (disable admitted-record-supplies-admitted-work
                                       witness-reference-passes-allocation-checks
                                       lookup-is-a-member-of-records)))))

(local
 (defthm admitted-scan-step-succeeds
   (implies (and (data-static-object-spans-p witness base size machine)
                 (data-ranked-records-p witness base witness machine)
                 (data-static-known-records-p objects witness)
                 (data-ranked-tasks-p (cons task pending) base witness machine))
            (mv-let (ok next extended) (data-static-scan-step task pending objects base size machine)
              (and ok (data-static-known-records-p extended witness)
                   (data-ranked-tasks-p next base witness machine))))
   :hints (("Goal" :use ((:instance admitted-word-step-succeeds
                                    (word (cadr task)) (depth (caddr task))))
                   :in-theory (e/d (data-ranked-tasks-p)
                                   (admitted-word-step-succeeds data-static-word-step
                                    data-static-known-records-p data-ranked-word-p))))))

(local
 (in-theory (disable data-static-scan-step data-static-word-step data-static-scan-budget
                     data-static-known-records-p admitted-scan-step-succeeds)))

(defthmd data-static-scan-complete-for-ranked-graph
  (implies (and (integerp base) (integerp size) (<= 32 size)
                (data-static-object-spans-p witness base size machine)
                (data-ranked-records-p witness base witness machine)
                (data-static-object-spans-p objects base size machine)
                (data-static-known-records-p objects witness)
                (data-ranked-tasks-p pending base witness machine)
                (natp fuel) (<= (data-static-scan-budget pending objects size machine) fuel))
           (mv-let (ok found) (data-static-scan pending objects base size machine fuel)
             (and ok (data-static-known-records-p found witness))))
  :hints (("Goal" :induct (data-static-scan pending objects base size machine fuel))
          ("Subgoal *1/1" :in-theory (enable data-ranked-tasks-p))
          ("Subgoal *1/2" :use data-static-nonempty-scan-has-positive-budget)
          ("Subgoal *1/3" :use ((:instance data-static-scan-step-preserves-budget
                                           (task (car pending)) (pending (cdr pending)))
                                (:instance admitted-scan-step-succeeds
                                           (task (car pending)) (pending (cdr pending))))
                          :expand ((data-ranked-tasks-p pending base witness machine)))
          ("Subgoal *1/4" :use ((:instance admitted-scan-step-succeeds
                                           (task (car pending)) (pending (cdr pending))))
                          :expand ((data-ranked-tasks-p pending base witness machine)))))

(defun data-static-image-witness-p (base image constants machine witness)
  (let ((size (car image)))
    (and (integerp base) (integerp size) (<= 32 size)
         (data-static-object-spans-p witness base size machine)
         (data-ranked-records-p witness base witness machine)
         (data-ranked-tasks-p (data-static-image-work base size (data-table-bindings constants 12))
                              base witness machine))))

(defthmd data-static-image-map-succeeds-for-ranked-graph
  (implies (data-static-image-witness-p base image constants machine witness)
           (mv-let (ok objects) (data-static-image-map base image constants machine)
             (and ok (data-static-known-records-p objects witness))))
  :hints (("Goal" :use ((:instance data-static-scan-complete-for-ranked-graph
                                   (size (car image)) (objects nil)
                                   (pending (data-static-image-work base (car image)
                                                                    (data-table-bindings constants 12)))
                                   (fuel (+ 16 (car image) (len (data-table-bindings constants 12))))))
                  :in-theory (e/d (data-static-image-work-cost data-static-known-records-p
                                   data-static-object-spans-p data-static-scan-budget)
                                  (data-static-scan data-static-image-work data-table-bindings
                                   data-static-work-cost data-static-object-bytes)))))
