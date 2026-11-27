(in-package "BOYMOO-PROOFS")

(include-book "allocation-trace")
(include-book "scan-completeness")

(logic)
(set-verify-guards-eagerness 0)

(defun data-allocation-shape-p (allocation)
  (case (car allocation)
    (:cons (and (equal (len (cdr allocation)) 2) (data-encodable-chunks-p (cdr allocation))))
    (:string (and (stringp (cadr allocation)) (null (cddr allocation))))
    (:header (let ((type (cadr allocation)) (payload (cddr allocation)))
               (and (data-encodable-chunks-p payload)
                    (or (member-equal type '(3 6))
                        (and (member-equal type '(2 4 5)) (equal (len payload) 2))))))
    (otherwise nil)))

(defun data-allocation-trace-shapes-p (trace)
  (if (atom trace)
      (null trace)
    (and (data-allocation-shape-p (car trace)) (data-allocation-trace-shapes-p (cdr trace)))))

(defun data-allocation-record (allocation offset base)
  (proof-object (+ base offset) :static (if (eq (car allocation) :cons) :cons :header)
                (data-static-rank offset)))

(defun data-allocation-trace-map (trace offset base)
  (if (atom trace)
      nil
    (cons (data-allocation-record (car trace) offset base)
          (data-allocation-trace-map (cdr trace) (+ offset (data-allocation-size (car trace))) base))))

(local
 (in-theory (disable floor ash length data-placed-characters-p
                     data-allocation-trace-chunks data-chunks-size data-chunk-characters
                     proof-load-word proof-align-up proof-header-size proof-header-type)))

(local
 (defthm encodable-chunks-occupy-words
   (implies (data-encodable-chunks-p chunks) (data-word-chunks-p chunks))
   :hints (("Goal" :induct (data-encodable-chunks-p chunks)))))

(local
 (defthm padded-string-count-is-a-multiple-of-eight
   (implies (natp size)
            (equal (boymoo-compiler::aligned-size size 3) (* 8 (floor (+ 7 size) 8))))
   :hints (("Goal" :in-theory (enable data-ash-left data-ash-right)))))

(local (in-theory (disable boymoo-compiler::aligned-size)))

(local
 (defthm ceiling-word-count-at-nonnegative-byte-count
   (implies (natp size)
            (equal (ceiling size 8)
                   (+ (floor size 8) (if (integerp (* 1/8 size)) 0 1))))
   :hints (("Goal" :use ((:instance acl2::rational-implies1 (acl2::x (* 1/8 size)))
                         (:instance acl2::rational-implies2 (acl2::x (* 1/8 size))))
                   :in-theory (e/d (ceiling floor) (acl2::rational-implies2))
                   :nonlinearp t))))

(defthmd data-model-padded-size-is-compiler-padded-size
  (implies (natp size)
           (equal (proof-align-up size 8) (boymoo-compiler::aligned-size size 3)))
  :hints (("Goal" :use ((:instance data-floor-bounds (x size) (d 8))
                        (:instance data-floor-unique (x (+ 7 size)) (d 8)
                                   (q (+ (floor size 8) (if (integerp (* 1/8 size)) 0 1))))
                        (:instance data-floor-unique (x size) (d 8) (q (* 1/8 size))))
                  :in-theory (e/d (proof-align-up) (ceiling)))))

(local
 (defthm word-byte-count-cancels-in-a-word-quotient
   (equal (* 1/8 (* 8 count)) (fix count))
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 1/8) (acl2::y 8) (acl2::z count)))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm floor-of-nonnegative-byte-count-is-nonnegative
   (implies (natp count) (<= 0 (floor count 8)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance data-floor-bounds (x count) (d 8)))))))

(defthm data-allocation-size-is-a-positive-word-count
  (implies (data-allocation-shape-p allocation)
           (and (integerp (* 1/8 (data-allocation-size allocation)))
                (<= 8 (data-allocation-size allocation))))
  :rule-classes (:rewrite
                 (:linear :corollary (implies (data-allocation-shape-p allocation)
                                             (<= 8 (data-allocation-size allocation)))))
  :hints (("Goal" :in-theory (enable data-chunks-size))))

(local
 (defthm aligned-model-size-keeps-word-counts
   (equal (proof-align-up (* 8 (len words)) 8) (* 8 (len words)))
   :hints (("Goal" :use ((:instance data-floor-unique (x (+ 7 (* 8 (len words)))) (d 8) (q (len words))))
                   :in-theory (enable data-model-padded-size-is-compiler-padded-size)))))

(local
 (defthm header-payload-count-from-word-count
   (equal (* 256 (* 8 count)) (* 2048 count))
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 256) (acl2::y 8) (acl2::z count)))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm allocation-header-encodes-payload-size
   (let* ((payload (if (eq (car allocation) :string) (length (cadr allocation)) (* 8 (len (cddr allocation)))))
          (type (if (eq (car allocation) :string) 1 (cadr allocation)))
          (header (car (data-allocation-chunks allocation))))
     (implies (and (data-allocation-shape-p allocation) (not (eq (car allocation) :cons))
                   (< (data-allocation-size allocation) *proof-space-size*))
              (and (unsigned-byte-p 64 header) (equal (proof-header-size header) payload)
                   (equal (proof-header-type header) type))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-static-sized-header-fits-and-decodes
                                    (payload (if (eq (car allocation) :string) (length (cadr allocation))
                                               (* 8 (len (cddr allocation)))))
                                    (type (if (eq (car allocation) :string) 1 (cadr allocation))))
                         (:instance data-aligned-size-eight-bounds (size (length (cadr allocation)))))
                   :in-theory (enable data-chunks-size)))))

(local
 (defthm chunk-stream-is-a-true-list
   (true-listp (data-chunk-characters chunk))
   :hints (("Goal" :use data-chunk-characters-are-characters))))

(local
 (defthm placing-forward-chunks-places-the-head-and-tail
   (implies (integerp address)
            (equal (data-placed-characters-p (data-forward-chunk-characters (cons chunk rest)) address machine)
                   (and (data-placed-characters-p (data-chunk-characters chunk) address machine)
                        (data-placed-characters-p (data-forward-chunk-characters rest)
                                                  (+ address (data-chunk-size chunk)) machine))))))

(local (in-theory (disable data-forward-chunk-characters)))

(local
 (defthm placed-allocation-loads-header-chunk
   (implies (and (data-allocation-shape-p allocation) (not (eq (car allocation) :cons))
                 (integerp address) (unsigned-byte-p 64 (car (data-allocation-chunks allocation)))
                 (data-placed-characters-p (data-forward-chunk-characters (data-allocation-chunks allocation))
                                           address machine))
            (equal (proof-load-word address machine) (car (data-allocation-chunks allocation))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-placed-chunk-loads-encoded-word
                                    (chunk (car (data-allocation-chunks allocation)))))))))

(defthmd data-placed-allocation-record-has-the-serialized-size
  (let ((record (data-allocation-record allocation offset base)))
    (implies (and (data-allocation-shape-p allocation) (< (data-allocation-size allocation) *proof-space-size*)
                  (integerp base) (integerp offset)
                  (data-placed-characters-p (data-forward-chunk-characters (data-allocation-chunks allocation))
                                            (+ base offset) machine))
             (equal (proof-object-size record machine) (data-allocation-size allocation))))
  :hints (("Goal" :use (allocation-header-encodes-payload-size
                        (:instance placed-allocation-loads-header-chunk (address (+ base offset))))
                  :in-theory (e/d (data-model-padded-size-is-compiler-padded-size data-chunks-size)
                                 (data-static-rank)))))

(local
 (in-theory (disable data-allocation-size data-allocation-shape-p proof-object-size
                     data-static-rank proof-object-record-p proof-subspan-p proof-span-p mod)))

(local
 (defthm a-byte-count-in-whole-words-has-zero-remainder
   (implies (and (integerp address) (integerp (* 1/8 address)))
            (equal (mod address 8) 0))
   :hints (("Goal" :use ((:instance data-floor-unique (d 8) (x address) (q (* 1/8 address))))
                   :in-theory (enable mod)))))

(local
 (defthm whole-word-sum-has-a-whole-word-count
   (implies (and (integerp (* 1/8 first)) (integerp (* 1/8 second)))
            (integerp (* 1/8 (+ first second))))))

(local
 (defthm static-rank-is-natural
   (natp (data-static-rank offset))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable data-static-rank)))))

(local
 (defthm placed-allocation-has-a-static-record-and-span
   (let* ((record (data-allocation-record allocation offset base))
          (bytes (data-allocation-size allocation)))
     (implies (and (data-allocation-shape-p allocation) (proof-span-p base size)
                   (< size *proof-space-size*) (natp offset) (<= 32 offset) (<= (+ offset bytes) size)
                   (integerp (* 1/8 base)) (integerp (* 1/8 offset))
                   (data-placed-characters-p (data-forward-chunk-characters (data-allocation-chunks allocation))
                                             (+ base offset) machine))
              (and (proof-object-record-p record)
                   (proof-subspan-p (+ base offset) (proof-object-size record machine) (+ base 32) (+ base size)))))
   :hints (("Goal" :use (data-placed-allocation-record-has-the-serialized-size)
                   :in-theory (enable proof-object-record-p proof-span-p proof-subspan-p)))))

(local
 (defthm allocation-size-is-natural
   (natp (data-allocation-size allocation))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable data-allocation-size)))))

(local
 (defthm rightward-allocations-are-disjoint-from-an-earlier-span
   (implies (and (integerp base) (integerp offset) (<= end (+ base offset)))
            (proof-object-disjoint-p start end (data-allocation-trace-map trace offset base) machine))
   :hints (("Goal" :induct (data-allocation-trace-map trace offset base)))))

(local
 (defthm object-bytes-are-a-true-list
   (true-listp (data-forward-chunk-characters chunks))
   :hints (("Goal" :use data-forward-chunk-characters-are-characters))))

(local
 (defthm bytes-of-joined-chunks-are-consecutive
   (equal (data-forward-chunk-characters (append first second))
          (append (data-forward-chunk-characters first) (data-forward-chunk-characters second)))
   :hints (("Goal" :in-theory (enable data-forward-chunk-characters)))))

(defthm data-placed-allocation-trace-splits-at-the-end-of-each-object
  (implies (integerp address)
           (equal (data-placed-characters-p
                   (data-forward-chunk-characters (data-allocation-trace-chunks (cons allocation rest)))
                   address machine)
                  (and (data-placed-characters-p (data-forward-chunk-characters (data-allocation-chunks allocation))
                                                 address machine)
                       (data-placed-characters-p (data-forward-chunk-characters (data-allocation-trace-chunks rest))
                                                 (+ address (data-allocation-size allocation)) machine))))
  :hints (("Goal" :in-theory (enable data-allocation-size)
                  :expand ((data-allocation-trace-chunks (cons allocation rest))))))

(local
 (defthm nonempty-trace-byte-count-includes-the-first-object
   (implies (consp trace)
            (equal (data-chunks-size (data-allocation-trace-chunks trace))
                   (+ (data-allocation-size (car trace))
                      (data-chunks-size (data-allocation-trace-chunks (cdr trace))))))
   :hints (("Goal" :use ((:instance data-cons-allocation-trace-counts-its-first-object
                                    (allocation (car trace)) (rest (cdr trace))))))))

(local
 (defthm nonempty-placed-trace-splits-into-first-object-and-rest
   (implies (and (consp trace) (integerp address))
            (equal (data-placed-characters-p (data-forward-chunk-characters (data-allocation-trace-chunks trace))
                                             address machine)
                   (and (data-placed-characters-p
                         (data-forward-chunk-characters (data-allocation-chunks (car trace))) address machine)
                        (data-placed-characters-p
                         (data-forward-chunk-characters (data-allocation-trace-chunks (cdr trace)))
                         (+ address (data-allocation-size (car trace))) machine))))
   :hints (("Goal" :use ((:instance data-placed-allocation-trace-splits-at-the-end-of-each-object
                                    (allocation (car trace)) (rest (cdr trace))))))))

(local (in-theory (disable data-allocation-record data-placed-allocation-record-has-the-serialized-size)))

(local
 (defthm static-address-minus-base-is-the-offset
   (implies (integerp offset) (equal (+ base (- base) offset) offset))
   :hints (("Goal" :use ((:instance associativity-of-+ (acl2::x base) (acl2::y (- base)) (acl2::z offset)))
                   :in-theory (disable associativity-of-+)))))

(defthmd data-trace-map-has-exact-disjoint-static-spans
  (implies (and (data-allocation-trace-shapes-p trace) (proof-span-p base size) (< size *proof-space-size*)
                (natp offset) (<= 32 offset) (integerp (* 1/8 offset)) (integerp (* 1/8 base))
                (<= (+ offset (data-chunks-size (data-allocation-trace-chunks trace))) size)
                (data-placed-characters-p (data-forward-chunk-characters (data-allocation-trace-chunks trace))
                                          (+ base offset) machine))
           (data-static-object-spans-p (data-allocation-trace-map trace offset base) base size machine))
  :hints (("Goal" :induct (data-allocation-trace-map trace offset base)
                  :in-theory (disable (:definition data-allocation-trace-map) data-static-object-spans-p)
                  :expand ((data-allocation-trace-map trace offset base) (data-allocation-trace-map nil offset base)
                           (data-allocation-trace-shapes-p trace)
                           (data-static-object-spans-p nil base size machine)
                           (:free (record records) (data-static-object-spans-p (cons record records) base size machine))))
          ("Subgoal *1/2"
           :use ((:instance data-placed-allocation-record-has-the-serialized-size (allocation (car trace)))
                 (:instance data-allocation-size-is-a-positive-word-count (allocation (car trace)))
                 (:instance placed-allocation-has-a-static-record-and-span (allocation (car trace))))
           :in-theory (e/d (data-allocation-record proof-span-p) (data-allocation-chunks data-chunk-size)))))

(defun data-allocation-references (allocation)
  (cond ((eq (car allocation) :cons) (cdr allocation))
        ((and (eq (car allocation) :header) (member-equal (cadr allocation) '(2 4 5 6))) (cddr allocation))
        (t nil)))

(defun data-ranked-allocation-words-p (words rank base records)
  (if (atom words)
      (null words)
    (and (data-ranked-word-p (car words) rank base records)
         (data-ranked-allocation-words-p (cdr words) rank base records))))

(defun data-trace-references-are-ranked-p (trace offset base records)
  (if (atom trace)
      (null trace)
    (let ((allocation (car trace)))
      (and (data-ranked-allocation-words-p (data-encoded-words (data-allocation-references allocation))
                                          (data-static-rank offset) base records)
           (data-trace-references-are-ranked-p (cdr trace) (+ offset (data-allocation-size allocation))
                                              base records)))))

(local
 (in-theory (disable data-ranked-word-p data-allocation-size)))

(local
 (defun ranked-memory-field-induction (words address)
   (if (atom words)
       address
     (ranked-memory-field-induction (cdr words) (+ 8 address)))))

(local
 (defthm loaded-ranked-words-give-ranked-field-task
   (implies (and (data-memory-words-p words address machine)
                 (data-ranked-allocation-words-p words rank base records))
            (data-ranked-field-words-p address (len words) rank base records machine))
   :hints (("Goal" :induct (ranked-memory-field-induction words address)))))

(local
 (defthm encoded-fields-have-original-field-count
   (equal (len (data-encoded-words words)) (len words))))

(local
 (defthm field-word-count-is-the-payload-size-in-words
   (and (equal (ash (* 8 (len words)) -3) (len words))
        (equal (mod (* 8 (len words)) 8) 0))
   :hints (("Goal" :use ((:instance data-floor-unique (x (* 8 (len words))) (d 8) (q (len words))))
                   :in-theory (enable data-ash-right mod)))))

(local
 (defthm placed-allocation-loads-the-reference-fields
   (let* ((words (data-allocation-references allocation))
          (address (if (eq (car allocation) :cons) start (+ start 8))))
     (implies (and (data-allocation-shape-p allocation) (integerp start)
                   (data-placed-characters-p (data-forward-chunk-characters (data-allocation-chunks allocation))
                                             start machine))
              (data-memory-words-p (data-encoded-words words) address machine)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-placed-encodable-chunks-load-their-words
                                    (chunks (data-allocation-references allocation))
                                    (address (if (eq (car allocation) :cons) start (+ start 8))))
                         (:instance data-chunk-characters-size
                                    (chunk (car (data-allocation-chunks allocation)))))
                   :in-theory (enable data-allocation-shape-p)))))

(local
 (defthm placed-rank-checked-allocation-has-ranked-work
   (let ((record (data-allocation-record allocation offset base)))
     (implies (and (data-allocation-shape-p allocation) (< (data-allocation-size allocation) *proof-space-size*)
                   (integerp base) (integerp offset)
                   (data-placed-characters-p (data-forward-chunk-characters (data-allocation-chunks allocation))
                                             (+ base offset) machine)
                   (data-ranked-allocation-words-p (data-encoded-words (data-allocation-references allocation))
                                                   (data-static-rank offset) base records))
              (mv-let (ok work) (data-static-header-work record nil machine)
                (and ok (data-ranked-tasks-p work base records machine)))))
   :rule-classes nil
   :hints (("Goal"
            :use (allocation-header-encodes-payload-size
                  (:instance placed-allocation-loads-header-chunk (address (+ base offset)))
                  (:instance placed-allocation-loads-the-reference-fields (start (+ base offset)))
                  (:instance loaded-ranked-words-give-ranked-field-task
                             (words (data-encoded-words (data-allocation-references allocation)))
                             (address (if (eq (car allocation) :cons) (+ base offset) (+ 8 base offset)))
                             (rank (data-static-rank offset))))
            :in-theory (e/d (data-allocation-record data-allocation-shape-p)
                            (loaded-ranked-words-give-ranked-field-task data-ranked-field-words-p
                             data-ranked-allocation-words-p data-encoded-words data-memory-words-p))))))

(defthmd data-trace-reference-check-establishes-ranked-records
  (implies (and (data-allocation-trace-shapes-p trace) (integerp base) (natp offset)
                (< (data-chunks-size (data-allocation-trace-chunks trace)) *proof-space-size*)
                (data-trace-references-are-ranked-p trace offset base records)
                (data-placed-characters-p (data-forward-chunk-characters (data-allocation-trace-chunks trace))
                                          (+ base offset) machine))
           (data-ranked-records-p (data-allocation-trace-map trace offset base) base records machine))
  :hints (("Goal" :induct (data-allocation-trace-map trace offset base)
                  :in-theory (disable data-ranked-records-p (:definition data-allocation-trace-map) data-static-header-work
                                      data-allocation-references data-ranked-allocation-words-p
                                      data-encoded-words data-ranked-tasks-p)
                  :expand ((data-allocation-trace-map trace offset base) (data-allocation-trace-map nil offset base)
                           (data-allocation-trace-shapes-p trace)
                           (data-trace-references-are-ranked-p trace offset base records)
                           (data-ranked-records-p nil base records machine)
                           (:free (object objects) (data-ranked-records-p (cons object objects) base records machine))))
          ("Subgoal *1/2"
           :use ((:instance placed-rank-checked-allocation-has-ranked-work (allocation (car trace)))))))

(defthmd data-placed-allocation-trace-constructs-ranked-image-witness
  (let* ((size (car image)) (objects (data-allocation-trace-map trace 32 base)))
    (implies (and (data-allocation-trace-shapes-p trace) (proof-span-p base size) (< size *proof-space-size*)
                  (integerp (* 1/8 base)) (<= (+ 32 (data-chunks-size (data-allocation-trace-chunks trace))) size)
                  (data-placed-characters-p (data-forward-chunk-characters (data-allocation-trace-chunks trace))
                                            (+ base 32) machine)
                  (data-trace-references-are-ranked-p trace 32 base objects)
                  (data-ranked-tasks-p (data-static-image-work base size (data-table-bindings constants 12))
                                       base objects machine))
             (data-static-image-witness-p base image constants machine objects)))
  :hints (("Goal" :use ((:instance data-trace-map-has-exact-disjoint-static-spans (offset 32) (size (car image)))
                        (:instance data-trace-reference-check-establishes-ranked-records
                                   (offset 32) (records (data-allocation-trace-map trace 32 base))))
                  :in-theory (enable proof-span-p))))
