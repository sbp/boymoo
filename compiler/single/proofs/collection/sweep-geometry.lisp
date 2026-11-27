(in-package "BOYMOO-PROOFS")

(include-book "sweep-input")
(include-book "sweep-loop")
(include-book "sweep-call")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-sweep-exact-regions-p (records regions)
  (or (endp records)
      (let ((base (caar records)) (size (cadar records)))
        (and (member-equal (proof-region base (+ base size) :rw) regions)
             (collection-sweep-exact-regions-p (cdr records) regions)))))

(local
 (in-theory (disable proof-load-word proof-world-machine proof-world-regions
                     proof-header-type proof-header-size
                     proof-covered-p proof-align-up proof-world-page-size
                     collection-read-word collection-forwarding
                     proof-heap-base proof-stack-base proof-stack-end proof-machine-limit
                     proof-disjoint-p mod boymoo-model::a64-unsigned)))

(local
 (defthm collection-sweep-region-record-reads-original-word
   (equal (proof-load-word address (proof-world-machine world)) (collection-read-word address world))
   :hints (("Goal" :in-theory (enable collection-read-word)))))

(defthm collection-published-sweep-records-name-exact-mapping-regions
  (let* ((mappings (proof-external-objects head fuel world objects))
         (records (collection-published-sweep-records (cdr mappings) world work)))
    (implies (and mappings (unsigned-byte-p 64 head))
             (collection-sweep-exact-regions-p records (proof-world-regions world))))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects))))

(local
 (defun collection-sweep-chain-induction (first second)
   (if (or (endp first) (endp second))
       nil
     (collection-sweep-chain-induction (cdr first) (cdr second)))))

(local
 (defthm collection-sweep-snapshots-at-same-link-have-same-length
   (implies (and (collection-sweep-snapshot-p first world)
                 (collection-sweep-snapshot-p second world)
                 (equal (collection-sweep-next-head first) (collection-sweep-next-head second)))
            (equal (len first) (len second)))
   :rule-classes nil
   :hints (("Goal"
            :induct (collection-sweep-chain-induction first second)
            :in-theory (disable collection-sweep-next-head)
            :expand ((collection-sweep-next-head first) (collection-sweep-next-head second))))))

(local
 (defun collection-sweep-suffix-from (head records)
   (cond ((endp records) nil)
         ((equal head (caar records)) records)
         (t (collection-sweep-suffix-from head (cdr records))))))

(local
 (defthm collection-sweep-suffix-keeps-snapshot-and-length-bound
   (let ((suffix (collection-sweep-suffix-from head records)))
     (implies (and (collection-sweep-snapshot-p records world)
                   (member-equal head (strip-cars records)))
              (and (collection-sweep-snapshot-p suffix world)
                   (equal (collection-sweep-next-head suffix) head)
                   (<= (len suffix) (len records)))))
   :rule-classes nil
   :hints (("Goal" :induct (collection-sweep-suffix-from head records)))))

(local
 (in-theory (disable collection-sweep-suffix-from collection-sweep-snapshot-p)))

(defthm collection-sweep-snapshot-has-unique-mapping-bases
  (implies (collection-sweep-snapshot-p records world)
           (no-duplicatesp-equal (strip-cars records)))
  :rule-classes nil
  :hints (("Goal" :induct (len records))
          ("Subgoal *1/1"
           :expand ((collection-sweep-snapshot-p records world))
           :use ((:instance collection-sweep-suffix-keeps-snapshot-and-length-bound
                            (head (caar records)) (records (cdr records)))
                 (:instance collection-sweep-snapshots-at-same-link-have-same-length
                            (first records)
                            (second (collection-sweep-suffix-from (caar records) (cdr records))))))))

(local
 (defthm collection-region-member-separates-from-listed-span
   (implies (and (proof-region-disjoint-p base end regions)
                 (member-equal region regions))
            (proof-disjoint-p base end (car region) (cadr region)))
   :hints (("Goal" :induct (member-equal region regions)))))

(local
 (defthm collection-distinct-mapping-regions-are-separated
   (implies (and (proof-regions-p regions)
                 (member-equal first regions)
                 (member-equal second regions)
                 (not (equal first second)))
            (proof-disjoint-p (car first) (cadr first) (car second) (cadr second)))
   :rule-classes nil
   :hints (("Goal"
            :induct (len regions)
            :in-theory (disable proof-region-p proof-region-disjoint-p))
           ("Subgoal *1/1"
            :use ((:instance collection-region-member-separates-from-listed-span
                             (base (caar regions)) (end (cadar regions))
                             (region first) (regions (cdr regions)))
                  (:instance collection-region-member-separates-from-listed-span
                             (base (caar regions)) (end (cadar regions))
                             (region second) (regions (cdr regions))))
            :in-theory (e/d (proof-disjoint-p)
                             (proof-region-p proof-region-disjoint-p
                              collection-region-member-separates-from-listed-span))))))

(local
 (defthm collection-exact-mapping-region-is-separated-from-other-records
   (implies (and (collection-sweep-exact-regions-p records (proof-world-regions world))
                 (collection-sweep-snapshot-p records world)
                 (proof-regions-p (proof-world-regions world))
                 (member-equal (proof-region base end :rw) (proof-world-regions world))
                 (not (member-equal base (strip-cars records))))
            (collection-sweep-spans-separate-p base end records))
   :hints (("Goal"
            :induct (len records)
            :in-theory (disable proof-regions-p proof-span-p))
           ("Subgoal *1/1"
            :expand ((collection-sweep-snapshot-p records world))
            :use ((:instance collection-distinct-mapping-regions-are-separated
                             (first (proof-region base end :rw))
                             (second (proof-region (caar records) (+ (caar records) (cadar records)) :rw))
                             (regions (proof-world-regions world))))
            :in-theory (disable proof-regions-p)))))

(defthm collection-sweep-exact-regions-and-snapshot-give-disjoint-spans
  (implies (and (collection-sweep-snapshot-p records world)
                (collection-sweep-exact-regions-p records (proof-world-regions world))
                (proof-regions-p (proof-world-regions world)))
           (collection-sweep-spans-disjoint-p records))
  :rule-classes nil
  :hints (("Goal" :induct (len records) :in-theory (disable proof-regions-p))
          ("Subgoal *1/1"
           :expand ((collection-sweep-snapshot-p records world))
           :use ((:instance collection-sweep-snapshot-has-unique-mapping-bases)
                 (:instance collection-exact-mapping-region-is-separated-from-other-records
                            (base (caar records)) (end (+ (caar records) (cadar records)))
                            (records (cdr records))))
           :in-theory (disable proof-regions-p
                               collection-exact-mapping-region-is-separated-from-other-records))))

(local
 (defthm collection-published-string-accounting-bounds-retained-sweep-bytes
   (implies (proof-string-accounting-p headers original)
            (unsigned-byte-p 64
                             (collection-sweep-retained-bytes
                              (collection-published-sweep-records headers original work))))
   :hints (("Goal"
            :use ((:instance collection-published-sweep-retains-at-most-mapped-bytes))
            :in-theory (disable collection-published-sweep-records collection-sweep-retained-bytes
                                proof-external-bytes collection-published-sweep-retains-at-most-mapped-bytes
                                proof-string-bytes-since-collection proof-string-budget)))))

(defthm collection-published-list-supplies-sweep-loop-invariant
  (let* ((mappings (proof-external-objects head fuel original objects))
         (headers (cdr mappings))
         (records (collection-published-sweep-records headers original work))
         (regions (proof-world-regions current))
         (link (proof-world-reg 19 current)))
    (implies (and mappings (unsigned-byte-p 64 head)
                  (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin current)
                  (not (proof-world-stop current))
                  (alistp (boymoo-model::a64-memory (proof-world-machine current)))
                  (proof-page-size-p (proof-world-page-size current))
                  (proof-regions-p regions)
                  (equal regions (proof-world-regions original))
                  (collection-sweep-metadata-preserved-p headers original current)
                  (collection-external-mark-table-p headers work current)
                  (proof-string-accounting-p headers original)
                  (equal (proof-world-reg 22 current) 0)
                  (proof-covered-p link 8 :write regions)
                  (equal (collection-read-word link current) head)
                  (collection-sweep-spans-separate-p link (+ link 8) records)
                  (collection-trace-placed-p (collection-sweep-loop-code origin) current)
                  (collection-sweep-zero-replies-p (collection-sweep-discard-count records)
                                                   (proof-world-replies current)))
             (collection-sweep-loop-invariant-p records origin current)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-published-sweep-records-match-links-sizes-and-marks)
                 (:instance collection-published-sweep-records-name-exact-mapping-regions (world original))
                 (:instance collection-published-string-accounting-bounds-retained-sweep-bytes
                            (headers (cdr (proof-external-objects head fuel original objects))))
                 (:instance collection-sweep-exact-regions-and-snapshot-give-disjoint-spans
                            (world current)
                            (records (collection-published-sweep-records
                                      (cdr (proof-external-objects head fuel original objects)) original work))))
           :in-theory (disable collection-published-string-accounting-bounds-retained-sweep-bytes
                               proof-external-objects collection-published-sweep-records
                               proof-regions-p proof-string-accounting-p
                               collection-sweep-next-head collection-sweep-spans-disjoint-p
                               collection-trace-placed-p collection-sweep-snapshot-p
                               collection-sweep-entry-p proof-page-size-p proof-world-reg
                               collection-external-mark-table-p collection-sweep-metadata-preserved-p
                               collection-sweep-loop-code collection-sweep-retained-bytes
                               collection-sweep-discard-count
                               boymoo-model::a64-memory))))

(defthm collection-published-sweep-decision-matches-root-reachability
  (let* ((base (proof-heap-base world))
         (graph (collection-published-object-graph objects base objects (proof-world-machine world)))
         (roots (collection-published-roots world objects))
         (lower (proof-inactive-floor world))
         (upper (proof-inactive-end world))
         (work (collection-traverse roots graph lower upper))
         (headers (cdr (proof-external-objects (proof-external-head world) (len objects) world objects)))
         (records (collection-published-sweep-records headers world work))
         (retain (caddr (assoc-equal (- header 24) records)))
         (witness (cdr (assoc-equal header (collection-traversal-paths roots graph lower upper)))))
    (implies (and (proof-heap-p world objects packages)
                  (integerp header) (member-equal header headers))
             (and (implies retain
                           (and (equal (car witness) header)
                                (collection-reverse-path-p witness roots graph)))
                  (implies (and (member-equal (car path) roots)
                                (collection-edge-path-p path graph)
                                (member-equal header path)
                                (assoc-equal header graph))
                           retain))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-published-sweep-record-uses-forwarding-map
                            (original world)
                            (headers (cdr (proof-external-objects (proof-external-head world) (len objects)
                                                                 world objects)))
                            (work (collection-traverse
                                   (collection-published-roots world objects)
                                   (collection-published-object-graph
                                    objects (proof-heap-base world) objects (proof-world-machine world))
                                   (proof-inactive-floor world) (proof-inactive-end world))))
                 (:instance collection-published-forwarding-has-root-witness (address header))
                 (:instance collection-traversal-assigns-every-reachable-object
                            (address header)
                            (roots (collection-published-roots world objects))
                            (graph (collection-published-object-graph
                                    objects (proof-heap-base world) objects (proof-world-machine world)))
                            (lower (proof-inactive-floor world)) (upper (proof-inactive-end world))))
           :in-theory (disable proof-heap-p proof-external-objects proof-external-head
                               proof-inactive-floor proof-inactive-end
                               collection-published-sweep-record-uses-forwarding-map
                               collection-published-object-graph collection-published-roots
                               collection-published-sweep-records collection-traverse
                               collection-traversal-paths collection-reverse-path-p collection-edge-path-p))))

(local
 (defthm collection-sweep-frame-pair-access
   (let ((sp (boymoo-model::a64-sp (proof-world-machine world))))
     (and (implies (<= 16 sp)
                   (equal (proof-instruction-access-p '(:pair nil 31 29 30 :pre -16) world)
                          (and (equal (mod sp 16) 0)
                               (proof-covered-p (- sp 16) 16 :write (proof-world-regions world)))))
          (equal (proof-instruction-access-p '(:pair t 31 29 30 :post 16) world)
                 (and (equal (mod sp 16) 0)
                      (proof-covered-p sp 16 :read (proof-world-regions world))))))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned mod)))))

(local
 (defthm collection-sweep-accounting-pair-access
   (equal (proof-instruction-access-p '(:pair nil 17 31 22 :offset 72) world)
          (proof-covered-p (boymoo-model::a64-unsigned 64 (+ 72 (proof-world-reg 17 world)))
                           16 :write (proof-world-regions world)))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-sweep-state-actions-keep-normal-execution
   (and (equal (proof-world-stop (collection-write-register register value world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-pc address world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-flags flags world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-word address value world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-sp address world))
               (proof-world-stop world)))
   :hints (("Goal"
            :use ((:instance collection-kernel-metadata-after-cpu-change (slot 7)))
            :in-theory (e/d (proof-world-stop)
                             (collection-write-register collection-write-pc collection-write-flags
                              collection-write-word collection-write-sp nth update-nth
                              collection-kernel-metadata-after-cpu-change))))))

(local
 (defthm collection-sweep-state-actions-keep-word
   (and (equal (collection-read-word address (collection-write-register register value world))
               (collection-read-word address world))
        (equal (collection-read-word address (collection-write-pc pc world))
               (collection-read-word address world))
        (equal (collection-read-word address (collection-write-flags flags world))
               (collection-read-word address world)))
   :hints (("Goal"
            :in-theory (e/d (collection-read-word proof-load-word boymoo-model::a64-load)
                             (proof-world-machine collection-write-register collection-write-pc
                              collection-write-flags boymoo-model::a64-memory
                              boymoo-model::a64-read-bytes
                              collection-sweep-region-record-reads-original-word))))))

(local
 (in-theory (disable proof-world-machine proof-world-pc proof-world-reg proof-world-stop proof-world-regions
                     proof-regions-p proof-reg proof-load-word proof-covered-p proof-instruction-at-p
                     proof-instruction-effect collection-cpu-p collection-read-word
                     collection-write-register collection-write-pc collection-write-flags
                     collection-write-word collection-write-sp collection-subtract-flags
                     boymoo-model::a64-unsigned boymoo-model::a64-sp boymoo-model::a64-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory mod
                     (:definition ash) (:definition acl2::binary-logand))))

(local
 (defthm collection-sweep-frame-coverage-splits-pair
   (implies (proof-covered-p address 16 :write regions)
            (and (proof-span-p address 16)
                 (proof-covered-p address 8 :write regions)
                 (proof-covered-p (+ address 8) 8 :write regions)))
   :hints (("Goal"
            :use ((:instance collection-covered-address-is-a-span (width 16) (access :write))
                  (:instance collection-covered-subspan (base address) (extent 16) (width 8) (access :write))
                  (:instance collection-covered-subspan (base address) (address (+ address 8))
                             (extent 16) (width 8) (access :write)))
            :in-theory (disable collection-covered-address-is-a-span)))))

(defthm collection-placed-sweep-prologue-is-ready
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (trace (collection-sweep-prologue-trace origin))
         (regions (proof-world-regions world)))
    (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-strings") origin world)
                  (not (proof-world-stop world))
                  (equal (mod sp 16) 0)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (proof-covered-p (- sp 16) 16 :write regions)
                  (collection-trace-placed-p trace world))
             (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:sweep-string"))) world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-frame-coverage-splits-pair
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (regions (proof-world-regions world))))
           :in-theory (disable collection-sweep-frame-coverage-splits-pair
                               collection-covered-address-is-a-span))))

(defthm collection-placed-sweep-epilogue-is-ready
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world))
         (trace (collection-sweep-epilogue-trace origin))
         (regions (proof-world-regions world))
         (link (collection-read-word (+ sp 8) world)))
    (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-done") origin world)
                  (not (proof-world-stop world))
                  (equal (mod sp 16) 0)
                  (<= 128 heap)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (proof-covered-p sp 16 :read regions)
                  (proof-covered-p (- heap 56) 16 :write regions)
                  (proof-disjoint-p sp (+ sp 16) (- heap 56) (- heap 40))
                  (not (member-equal link (strip-cars trace)))
                  (collection-trace-placed-p trace world))
             (collection-trace-ready-p trace (list link) world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-frame-coverage-splits-pair
                            (address (- (proof-world-reg 28 world) 56)) (regions (proof-world-regions world)))
                 (:instance collection-covered-address-is-a-span
                            (address (boymoo-model::a64-sp (proof-world-machine world)))
                            (width 16) (access :read) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-disjoint-p)
                            (collection-covered-address-is-a-span collection-sweep-frame-coverage-splits-pair)))))

(local
 (in-theory (disable collection-sweep-prologue-trace collection-sweep-epilogue-trace
                     collection-sweep-traversal-trace collection-trace-effect
                     collection-trace-ready-p proof-segment-p collection-sweep-loop-invariant-p
                     collection-sweep-traversal-input-p collection-sweep-spans-separate-p)))

(local
 (defthm collection-ready-sweep-boundaries-and-loop-compose
   (let* ((prologue (collection-sweep-prologue-trace origin))
          (traversal (collection-sweep-traversal-trace records origin))
          (tail (collection-sweep-epilogue-trace origin))
          (loop (collection-trace-effect prologue world))
          (body-end (collection-sweep-body-end records origin world))
          (loop-cut (list (+ origin (collection-linux-offset "rt:sweep-string"))))
          (done-cut (list (+ origin (collection-linux-offset "rt:sweep-done"))))
          (return-cut (list (proof-world-reg 30 world))))
     (implies (and (collection-trace-ready-p prologue loop-cut world)
                   (collection-trace-ready-p traversal done-cut loop)
                   (collection-trace-ready-p tail return-cut body-end)
                   (not (intersectp-equal (strip-cars prologue) return-cut))
                   (not (intersectp-equal (strip-cars traversal) return-cut)))
              (collection-trace-ready-p (collection-sweep-call-trace records origin)
                                        return-cut world)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-ready-trace-of-append
                             (first (collection-sweep-traversal-trace records origin))
                             (second (collection-sweep-epilogue-trace origin))
                             (first-cut (list (+ origin (collection-linux-offset "rt:sweep-done"))))
                             (cuts (list (proof-world-reg 30 world)))
                             (world (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
                  (:instance collection-ready-trace-of-append
                             (first (collection-sweep-prologue-trace origin))
                             (second (append (collection-sweep-traversal-trace records origin)
                                             (collection-sweep-epilogue-trace origin)))
                             (first-cut (list (+ origin (collection-linux-offset "rt:sweep-string"))))
                             (cuts (list (proof-world-reg 30 world)))))
            :in-theory (disable collection-ready-trace-of-append)))))

(defthm collection-checked-sweep-call-follows-from-loop-invariant
  (let* ((prologue (collection-sweep-prologue-trace origin))
         (traversal (collection-sweep-traversal-trace records origin))
         (tail (collection-sweep-epilogue-trace origin))
         (loop (collection-trace-effect prologue world))
         (body-end (collection-sweep-body-end records origin world))
         (trace (collection-sweep-call-trace records origin))
         (after (collection-trace-effect trace world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world))
         (return-cut (list (proof-world-reg 30 world))))
    (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-strings") origin world)
                  (<= 16 sp) (<= 128 heap)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-disjoint-p (- sp 16) sp (- heap 72) (- heap 40))
                  (collection-sweep-spans-separate-p (- sp 16) sp records)
                  (alistp (boymoo-model::a64-memory (proof-world-machine body-end)))
                  (collection-sweep-loop-invariant-p records origin loop)
                  (collection-trace-ready-p prologue
                                            (list (+ origin (collection-linux-offset "rt:sweep-string"))) world)
                  (collection-trace-ready-p tail return-cut body-end)
                  (not (intersectp-equal (strip-cars prologue) return-cut))
                  (not (intersectp-equal (strip-cars traversal) return-cut)))
             (and (proof-segment-p (len trace) return-cut world :cut after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (collection-read-word (- heap 56) after) 0)
                  (equal (collection-read-word (- heap 48) after)
                         (max *proof-minimum-string-budget* (collection-sweep-retained-bytes records)))
                  (equal (proof-world-replies after)
                         (nthcdr (collection-sweep-discard-count records) (proof-world-replies world)))
                  (equal (proof-world-regions after)
                         (collection-sweep-surviving-regions records (proof-world-regions world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-invariant-supplies-checked-traversal
                            (world (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
                 (:instance collection-ready-sweep-boundaries-and-loop-compose)
                 (:instance collection-ready-trace-reaches-cut
                            (trace (collection-sweep-call-trace records origin))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance collection-sweep-call-returns-and-debits-kernel-replies))
           :in-theory (disable collection-sweep-call-returns-and-debits-kernel-replies
                               collection-sweep-call-trace collection-sweep-body-end
                               collection-sweep-retained-bytes collection-sweep-discard-count
                               collection-sweep-surviving-regions))))

(local
 (defthm collection-sweep-ready-trace-ends-at-cut
   (implies (collection-trace-ready-p trace (list cut) world)
            (and (equal (proof-world-pc (collection-trace-effect trace world)) cut)
                 (not (proof-world-stop (collection-trace-effect trace world)))))
   :rule-classes nil
   :hints (("Goal"
            :induct (collection-trace-ready-p trace (list cut) world)
            :in-theory (e/d (collection-trace-ready-p collection-trace-effect)
                             (proof-instruction-access-p))))))

(defthm collection-sweep-invariant-protects-caller-link-to-accounting
  (let* ((prologue (collection-sweep-prologue-trace origin))
         (loop (collection-trace-effect prologue world))
         (end (collection-sweep-body-end records origin world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world)))
    (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-strings") origin world)
                  (<= 16 sp) (<= 128 heap)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-covered-p (- sp 16) 16 :write (proof-world-regions world))
                  (proof-disjoint-p (- sp 16) sp (- heap 72) (- heap 40))
                  (collection-sweep-spans-separate-p (- sp 16) sp records)
                  (collection-sweep-loop-invariant-p records origin loop))
             (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-done") origin end)
                  (not (proof-world-stop end))
                  (equal (boymoo-model::a64-sp (proof-world-machine end)) (- sp 16))
                  (equal (proof-world-reg 28 end) heap)
                  (equal (collection-read-word (+ 8 (boymoo-model::a64-sp (proof-world-machine end))) end)
                         (proof-world-reg 30 world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-invariant-supplies-checked-traversal
                            (world (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
                 (:instance collection-sweep-ready-trace-ends-at-cut
                            (world (collection-trace-effect (collection-sweep-prologue-trace origin) world))
                            (trace (collection-sweep-traversal-trace records origin))
                            (cut (+ origin (collection-linux-offset "rt:sweep-done"))))
                 (:instance collection-sweep-traversal-keeps-stack-and-unclobbered-registers
                            (world (collection-trace-effect (collection-sweep-prologue-trace origin) world))
                            (register 28))
                 (:instance collection-sweep-body-protects-saved-pair
                            (world (collection-trace-effect (collection-sweep-prologue-trace origin) world))
                            (linkp t))
                 (:instance collection-sweep-prologue-saves-pair-and-starts-list (register 28))
                 (:instance collection-covered-address-is-a-span
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (width 16) (access :write) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-disjoint-p)
                            (collection-sweep-traversal-keeps-stack-and-unclobbered-registers
                             collection-sweep-prologue-saves-pair-and-starts-list
                             collection-covered-address-is-a-span)))))

; The caller's return address is the saved link in the nested frame.
; The coverage premises describe the worlds at the two boundaries.
(defthm collection-placed-sweep-call-returns-from-loop-invariant
  (let* ((prologue (collection-sweep-prologue-trace origin))
         (traversal (collection-sweep-traversal-trace records origin))
         (tail (collection-sweep-epilogue-trace origin))
         (loop (collection-trace-effect prologue world))
         (body-end (collection-sweep-body-end records origin world))
         (trace (collection-sweep-call-trace records origin))
         (after (collection-trace-effect trace world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world))
         (body-sp (boymoo-model::a64-sp (proof-world-machine body-end)))
         (body-heap (proof-world-reg 28 body-end))
         (regions (proof-world-regions world))
         (body-regions (proof-world-regions body-end))
         (link (proof-world-reg 30 world))
         (return-cut (list link)))
    (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-strings") origin world)
                  (not (proof-world-stop world))
                  (<= 16 sp) (<= 128 heap)
                  (equal (mod sp 16) 0)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (proof-covered-p (- sp 16) 16 :write regions)
                  (proof-disjoint-p (- sp 16) sp (- heap 72) (- heap 40))
                  (collection-sweep-spans-separate-p (- sp 16) sp records)
                  (collection-trace-placed-p prologue world)
                  (collection-sweep-loop-invariant-p records origin loop)
                  (equal (mod body-sp 16) 0)
                  (alistp (boymoo-model::a64-memory (proof-world-machine body-end)))
                  (proof-regions-p body-regions)
                  (proof-covered-p body-sp 16 :read body-regions)
                  (proof-covered-p (- body-heap 56) 16 :write body-regions)
                  (proof-disjoint-p body-sp (+ body-sp 16) (- body-heap 56) (- body-heap 40))
                  (collection-trace-placed-p tail body-end)
                  (not (member-equal link (strip-cars tail)))
                  (not (intersectp-equal (strip-cars prologue) return-cut))
                  (not (intersectp-equal (strip-cars traversal) return-cut)))
             (and (proof-segment-p (len trace) return-cut world :cut after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) link)
                  (equal (collection-read-word (- heap 56) after) 0)
                  (equal (collection-read-word (- heap 48) after)
                         (max *proof-minimum-string-budget* (collection-sweep-retained-bytes records)))
                  (equal (proof-world-replies after)
                         (nthcdr (collection-sweep-discard-count records) (proof-world-replies world)))
                  (equal (proof-world-regions after)
                         (collection-sweep-surviving-regions records regions)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-placed-sweep-prologue-is-ready)
                 (:instance collection-sweep-invariant-protects-caller-link-to-accounting)
                 (:instance collection-placed-sweep-epilogue-is-ready
                            (world (collection-sweep-body-end records origin world)))
                 (:instance collection-checked-sweep-call-follows-from-loop-invariant))
           :in-theory (disable collection-sweep-entry-p collection-sweep-body-end
                               collection-sweep-call-trace collection-trace-placed-p
                               collection-sweep-retained-bytes collection-sweep-discard-count
                               collection-sweep-surviving-regions))))
