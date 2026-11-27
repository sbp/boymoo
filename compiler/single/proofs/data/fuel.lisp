(in-package "BOYMOO-PROOFS")

(include-book "objects")

(logic)
(set-verify-guards-eagerness 0)

; Intervals use an inclusive start and exclusive end.
(local
 (defun interval-disjoint-from-list-p (start end intervals)
   (if (atom intervals)
       t
     (and (proof-disjoint-p start end (caar intervals) (cdar intervals))
          (interval-disjoint-from-list-p start end (cdr intervals))))))

(local
 (defun intervals-fit-p (intervals lower upper)
   (if (atom intervals)
       (and (null intervals) (integerp lower) (integerp upper) (<= lower upper))
     (let ((start (caar intervals)) (end (cdar intervals)))
       (and (integerp start) (integerp end) (<= lower start) (<= start end) (<= end upper)
            (interval-disjoint-from-list-p start end (cdr intervals))
            (intervals-fit-p (cdr intervals) lower upper))))))

(local
 (defun interval-list-size (intervals)
   (if (atom intervals)
       0
     (+ (- (cdar intervals) (caar intervals)) (interval-list-size (cdr intervals))))))

(local
 (defun intervals-on-side (intervals boundary left)
   (if (atom intervals)
       nil
     (let ((rest (intervals-on-side (cdr intervals) boundary left)))
       (if (equal (<= (cdar intervals) boundary) left)
           (cons (car intervals) rest)
         rest)))))

(local
 (defthm interval-sublist-limits
   (<= (len (intervals-on-side intervals boundary left)) (len intervals))
   :rule-classes :linear
   :hints (("Goal" :induct (intervals-on-side intervals boundary left)))))

(local
 (defthm interval-partition-preserves-size
   (equal (+ (interval-list-size (intervals-on-side intervals boundary t))
             (interval-list-size (intervals-on-side intervals boundary nil)))
          (interval-list-size intervals))
   :hints (("Goal" :induct (intervals-on-side intervals boundary left)))))

(local
 (defthm filtered-intervals-preserve-disjointness
   (implies (interval-disjoint-from-list-p start end intervals)
            (interval-disjoint-from-list-p start end (intervals-on-side intervals boundary left)))
   :hints (("Goal" :induct (intervals-on-side intervals boundary left)))))

(local
 (defthm left-intervals-fit-before-gap
   (implies (and (intervals-fit-p intervals lower upper) (integerp start) (<= lower start))
            (intervals-fit-p (intervals-on-side intervals start t) lower start))
   :hints (("Goal" :induct (intervals-on-side intervals start t)))))

(local
 (defthm right-intervals-fit-after-gap
   (implies (and (intervals-fit-p intervals lower upper) (integerp end) (<= end upper)
                 (interval-disjoint-from-list-p start end intervals))
            (intervals-fit-p (intervals-on-side intervals start nil) end upper))
   :hints (("Goal" :induct (intervals-on-side intervals start nil)))))

(local
 (defun interval-size-induction (intervals lower upper fuel)
   (declare (xargs :measure (nfix fuel)))
   (if (or (atom intervals) (zp fuel))
       (list lower upper)
     (let ((start (caar intervals)) (end (cdar intervals)))
       (list (interval-size-induction (intervals-on-side (cdr intervals) start t) lower start (1- fuel))
             (interval-size-induction (intervals-on-side (cdr intervals) start nil) end upper (1- fuel)))))))

(local
 (defthm disjoint-interval-size-is-bounded
   (implies (and (intervals-fit-p intervals lower upper) (natp fuel) (<= (len intervals) fuel))
            (<= (interval-list-size intervals) (- upper lower)))
   :rule-classes nil
   :hints (("Goal" :induct (interval-size-induction intervals lower upper fuel))
           ("Subgoal *1/2" :use ((:instance interval-partition-preserves-size
                                            (intervals (cdr intervals)) (boundary (caar intervals)))
                                 (:instance left-intervals-fit-before-gap
                                            (intervals (cdr intervals)) (start (caar intervals)))
                                 (:instance right-intervals-fit-after-gap
                                            (intervals (cdr intervals)) (start (caar intervals))
                                            (end (cdar intervals))))
                           :in-theory (disable interval-partition-preserves-size
                                               left-intervals-fit-before-gap right-intervals-fit-after-gap)))))

(defun data-static-object-bytes (objects machine)
  (if (atom objects)
      0
    (+ (proof-object-size (car objects) machine) (data-static-object-bytes (cdr objects) machine))))

(local
 (defun static-object-intervals (objects machine)
   (if (atom objects)
       nil
     (let ((address (proof-object-address (car objects))))
       (cons (cons address (+ address (proof-object-size (car objects) machine)))
             (static-object-intervals (cdr objects) machine))))))

(local
 (in-theory (disable proof-object-size proof-object-address proof-object-record-p
                     proof-object-rank proof-object-zone data-static-rank)))

(local
 (defthm object-intervals-have-body-byte-count
   (equal (interval-list-size (static-object-intervals objects machine))
          (data-static-object-bytes objects machine))
   :hints (("Goal" :induct (static-object-intervals objects machine)))))

(local
 (defthm object-intervals-preserve-disjointness
   (implies (proof-object-disjoint-p start end objects machine)
            (interval-disjoint-from-list-p start end (static-object-intervals objects machine)))
   :hints (("Goal" :induct (proof-object-disjoint-p start end objects machine)))))

(local
 (defthm static-object-intervals-fit-the-image
   (implies (and (integerp base) (integerp size) (<= 32 size)
                 (data-static-object-spans-p objects base size machine))
            (intervals-fit-p (static-object-intervals objects machine) (+ base 32) (+ base size)))
   :hints (("Goal" :induct (static-object-intervals objects machine)
                   :in-theory (disable proof-object-disjoint-p)))))

(defthmd data-static-objects-use-at-most-image-bytes
  (implies (and (integerp base) (integerp size) (<= 32 size)
                (data-static-object-spans-p objects base size machine))
           (<= (data-static-object-bytes objects machine) (- size 32)))
  :hints (("Goal" :use (static-object-intervals-fit-the-image
                       (:instance disjoint-interval-size-is-bounded
                                   (intervals (static-object-intervals objects machine))
                                   (lower (+ base 32)) (upper (+ base size))
                                   (fuel (len (static-object-intervals objects machine)))))
                  :in-theory (disable static-object-intervals data-static-object-spans-p
                                      data-static-object-bytes static-object-intervals-fit-the-image))))

; A field task costs one stop check and two steps for each word. A
; word task costs one step, with any new child tasks charged to its object.
(defun data-static-task-cost (task)
  (if (eq (car task) :fields) (+ 1 (* 2 (nfix (caddr task)))) 1))

(defun data-static-work-cost (pending)
  (if (atom pending)
      0
    (+ (data-static-task-cost (car pending)) (data-static-work-cost (cdr pending)))))

(defthm data-static-work-cost-is-natural
  (natp (data-static-work-cost pending))
  :rule-classes :type-prescription)

(local
 (in-theory (disable proof-subspan-p proof-object-disjoint-p proof-object-kind
                     proof-load-word proof-header-type proof-header-size proof-pointer-address
                     proof-word-tag ash floor mod evenp)))

(local
 (defthm align-eight-covers-natural-part
   (<= (nfix size) (proof-align-up size 8))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance data-floor-bounds (x (nfix size)) (d 8))
                        (:instance acl2::rational-implies2 (acl2::x (* 1/8 (nfix size)))))
                   :in-theory (e/d (ceiling floor) (acl2::rational-implies2))))))

(local
 (defthm vector-field-cost-fits-aligned-header
   (implies (integerp size)
            (<= (+ 1 (* 2 (nfix (ash size -3)))) (+ 8 (proof-align-up size 8))))
   :rule-classes :linear
   :hints (("Goal" :use (align-eight-covers-natural-part
                        (:instance data-floor-bounds (x size) (d 8)))
                   :in-theory (e/d (data-ash-right) (proof-align-up align-eight-covers-natural-part))))))

(local
 (defthm header-work-fits-object-space
   (implies (mv-nth 0 (data-static-header-work object pending machine))
            (<= (data-static-work-cost (mv-nth 1 (data-static-header-work object pending machine)))
                (+ (data-static-work-cost pending) (proof-object-size object machine))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance vector-field-cost-fits-aligned-header
                                    (size (proof-header-size
                                           (proof-load-word (proof-object-address object) machine)))))
                   :in-theory (e/d (proof-object-size)
                                  (proof-align-up vector-field-cost-fits-aligned-header))))))

(local
 (in-theory (disable data-static-header-work data-static-object-spans-p mv-nth)))

(local
 (defthm word-step-cost-is-charged-to-added-object
   (mv-let (ok next extended) (data-static-word-step word depth pending objects base size machine)
     (implies ok
              (<= (+ (data-static-work-cost next) (data-static-object-bytes objects machine))
                  (+ (data-static-work-cost pending) (data-static-object-bytes extended machine)))))
   :hints (("Goal" :use ((:instance header-work-fits-object-space
                                    (object (proof-object
                                             (proof-pointer-address word base) :static
                                             (if (equal (proof-word-tag word) 0) :cons :header)
                                             (data-static-rank (- (proof-pointer-address word base) base))))))))))

(local
 (defthm scan-step-consumes-at-least-one-unit
   (mv-let (ok next extended) (data-static-scan-step task pending objects base size machine)
     (implies ok
              (< (+ (data-static-work-cost next) (data-static-object-bytes objects machine))
                 (+ (data-static-work-cost (cons task pending))
                    (data-static-object-bytes extended machine)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance word-step-cost-is-charged-to-added-object
                                    (word (cadr task)) (depth (caddr task))))
                   :in-theory (disable data-static-word-step data-static-object-bytes
                                       word-step-cost-is-charged-to-added-object)))))

(local
 (defthm allocation-size-is-natural
   (natp (proof-object-size object machine))
   :rule-classes :type-prescription
   :hints (("Goal" :use ((:instance align-eight-covers-natural-part
                                    (size (proof-header-size
                                           (proof-load-word (proof-object-address object) machine)))))
                   :in-theory (e/d (proof-object-size)
                                  (proof-align-up align-eight-covers-natural-part))))))

(defthm data-static-object-byte-count-is-natural
  (natp (data-static-object-bytes objects machine))
  :rule-classes :type-prescription)

; Each unused byte can pay for at most one additional work step.
(defun data-static-scan-budget (pending objects size machine)
  (+ (data-static-work-cost pending) size (- (data-static-object-bytes objects machine))))

(defthmd data-static-nonempty-scan-has-positive-budget
  (implies (and (consp pending) (integerp base) (integerp size) (<= 32 size)
                (data-static-object-spans-p objects base size machine))
           (<= 1 (data-static-scan-budget pending objects size machine)))
  :hints (("Goal" :use data-static-objects-use-at-most-image-bytes
                  :in-theory (disable data-static-object-bytes))))

(defthmd data-static-scan-step-preserves-budget
  (mv-let (ok next extended) (data-static-scan-step task pending objects base size machine)
    (implies (and ok (integerp size) (natp fuel)
                  (<= (data-static-scan-budget (cons task pending) objects size machine) fuel))
             (<= (data-static-scan-budget next extended size machine) (1- fuel))))
  :hints (("Goal" :use scan-step-consumes-at-least-one-unit
                  :in-theory (disable data-static-scan-step data-static-work-cost data-static-object-bytes))))

(defthmd data-static-scan-stable-above-budget
  (implies (and (integerp base) (integerp size) (<= 32 size)
                (data-static-object-spans-p objects base size machine)
                (natp fuel) (natp extra) (<= (data-static-scan-budget pending objects size machine) fuel))
           (equal (mv-list 2 (data-static-scan pending objects base size machine (+ fuel extra)))
                  (mv-list 2 (data-static-scan pending objects base size machine fuel))))
  :hints (("Goal" :induct (data-static-scan pending objects base size machine fuel)
                  :in-theory (disable data-static-scan-step data-static-scan-budget
                                      data-static-work-cost data-static-object-bytes)
                  :expand ((data-static-scan pending objects base size machine (+ fuel extra))))
          ("Subgoal *1/2" :use data-static-nonempty-scan-has-positive-budget)
          ("Subgoal *1/3"
           :use ((:instance data-static-scan-step-preserves-budget
                            (pending (cdr pending)) (task (car pending)))))))

(local
 (defthm one-step-per-constant-entry
   (equal (data-static-work-cost (data-static-constant-work bindings depth)) (len bindings))
   :hints (("Goal" :induct (data-static-constant-work bindings depth)))))

(defthmd data-static-image-work-cost
  (equal (data-static-work-cost (data-static-image-work base size bindings)) (+ 7 (len bindings)))
  :hints (("Goal" :in-theory (disable data-static-constant-work))))

(local
 (defthm empty-static-object-list-has-spans
   (data-static-object-spans-p nil base size machine)
   :hints (("Goal" :in-theory (enable data-static-object-spans-p)))))

(defthmd data-static-image-map-fuel-is-sufficient
  (let* ((size (car image))
         (bindings (data-table-bindings constants 12))
         (pending (data-static-image-work base size bindings))
         (fuel (+ 16 size (len bindings))))
    (implies (and (integerp base) (integerp size) (<= 32 size) (natp extra))
             (equal (mv-list 2 (data-static-scan pending nil base size machine (+ fuel extra)))
                    (mv-list 2 (data-static-image-map base image constants machine)))))
  :hints (("Goal" :use ((:instance data-static-scan-stable-above-budget
                                   (size (car image)) (objects nil)
                                   (pending (data-static-image-work base (car image)
                                                                    (data-table-bindings constants 12)))
                                   (fuel (+ 16 (car image) (len (data-table-bindings constants 12))))))
                  :in-theory (e/d (data-static-image-work-cost)
                                 (data-static-scan data-static-image-work data-table-bindings
                                  data-static-work-cost data-static-object-spans-p)))))
