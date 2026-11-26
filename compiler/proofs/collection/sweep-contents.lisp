(in-package "BOYMOO-PROOFS")

(include-book "sweep-traversal")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-sweep-spans-separate-p (start end records)
  (if (endp records)
      t
    (let* ((head (caar records))
           (size (cadar records)))
      (and (proof-span-p head size) (<= 24 size)
           (proof-disjoint-p start end head (+ head size))
           (collection-sweep-spans-separate-p start end (cdr records))))))

(defun collection-sweep-spans-disjoint-p (records)
  (if (endp records)
      t
    (let ((head (caar records)) (size (cadar records)))
      (and (proof-span-p head size) (<= 24 size)
           (collection-sweep-spans-separate-p head (+ head size) (cdr records))
           (collection-sweep-spans-disjoint-p (cdr records))))))

(defthm collection-sweep-subspan-separates-from-same-mappings
  (implies (and (proof-subspan-p address width start end)
                (collection-sweep-spans-separate-p start end records))
           (collection-sweep-spans-separate-p address (+ address width) records))
  :rule-classes nil
  :hints (("Goal" :induct (collection-sweep-spans-separate-p start end records))))

(local
 (in-theory (disable collection-trace-effect collection-sweep-round-trace
                     collection-sweep-retain-trace collection-sweep-discard-trace
                     collection-read-word proof-load-word proof-world-reg proof-world-machine
                     proof-world-pc collection-write-word collection-write-register
                     collection-write-pc collection-cpu-p proof-instruction-effect
                     boymoo-model::a64-memory boymoo-model::a64-unsigned
                     proof-world-regions proof-clear-span proof-clear-memory
                     collection-relinquish-p collection-relinquish-range
                     (:definition ash) (:definition acl2::binary-logior)
                     (:definition acl2::binary-logand))))

(local
 (defthm collection-sweep-word-from-equal-byte-memories
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-read-word address first) (collection-read-word address second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                   (boymoo-model::a64-read-bytes))))))

(local
 (defthm collection-sweep-ready-round-protects-word-on-retain
   (let* ((head (car record)) (size (cadr record))
          (after (collection-trace-effect (collection-sweep-retain-trace origin) world)))
     (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world)
                   (collection-sweep-round-input-p record world)
                   (caddr record) (<= 24 size) (proof-span-p head size)
                   (proof-span-p address 8)
                   (proof-disjoint-p address (+ address 8) head (+ head size)))
              (equal (collection-read-word address after) (collection-read-word address world))))
   :hints (("Goal"
            :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                  (:instance collection-disjoint-word-store-preserves-word
                             (start (+ 16 (car record))) (value 0))
                  (:instance collection-sweep-word-from-equal-byte-memories
                             (first (collection-trace-effect (collection-sweep-retain-trace origin) world))
                             (second (collection-write-word (+ 16 (car record)) 0 world))))
            :in-theory (disable collection-sweep-retains-one-mapping-and-resets-mark
                                collection-disjoint-word-store-preserves-word
                                collection-sweep-entry-p)))))

(local
 (defthm collection-sweep-ready-round-protects-word-on-discard
   (let* ((link (proof-world-reg 19 world))
          (head (car record)) (size (cadr record))
          (after (collection-trace-effect (collection-sweep-discard-trace origin) world)))
     (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world)
                   (collection-sweep-round-input-p record world)
                   (not (caddr record)) (proof-span-p address 8)
                   (proof-disjoint-p address (+ address 8) head (+ head size))
                   (proof-disjoint-p address (+ address 8) link (+ link 8)))
              (equal (collection-read-word address after) (collection-read-word address world))))
   :hints (("Goal"
            :use ((:instance collection-sweep-discards-one-mapping-and-relinks)
                  (:instance collection-disjoint-word-store-preserves-word
                             (start (proof-world-reg 19 world))
                             (value (collection-read-word (car record) world)))
                  (:instance collection-sweep-word-from-equal-byte-memories
                             (first (collection-trace-effect (collection-sweep-discard-trace origin) world))
                             (second (proof-clear-span
                                      (car record) (+ (car record) (cadr record))
                                      (collection-write-word (proof-world-reg 19 world)
                                                             (collection-read-word (car record) world) world))))
                  (:instance collection-clear-preserves-word-outside-range
                             (base (car record)) (end (+ (car record) (cadr record)))
                             (world (collection-write-word (proof-world-reg 19 world)
                                                           (collection-read-word (car record) world) world))))
            :in-theory (e/d (collection-cleared-world-memory)
                             (collection-sweep-discards-one-mapping-and-relinks
                              collection-disjoint-word-store-preserves-word
                              collection-clear-preserves-word-outside-range
                              collection-sweep-entry-p))))))

(local
 (defthm collection-sweep-end-keeps-words-and-regions
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (after (collection-trace-effect (collection-linux-trace "rt:sweep-string" '(0 1) origin)
                                          world)))
     (implies (collection-sweep-entry-p entry origin world)
              (and (equal (collection-read-word address after) (collection-read-word address world))
                   (equal (proof-world-regions after) (proof-world-regions world)))))
   :hints (("Goal" :in-theory (enable collection-trace-effect)))))

(local
 (defthm collection-sweep-round-moves-link-only-to-retained-mapping
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (after (collection-trace-effect (collection-sweep-round-trace record origin) world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (collection-sweep-round-input-p record world))
              (equal (proof-world-reg 19 after)
                     (if (caddr record) (car record) (proof-world-reg 19 world)))))
   :hints (("Goal" :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                         (:instance collection-sweep-discards-one-mapping-and-relinks))
                   :in-theory (e/d (collection-sweep-round-trace)
                                    (collection-sweep-entry-p
                                     collection-sweep-retains-one-mapping-and-resets-mark
                                     collection-sweep-discards-one-mapping-and-relinks))))))

(defthm collection-sweep-traversal-preserves-word-outside-links-and-mappings
  (let* ((link (proof-world-reg 19 world))
         (after (collection-trace-effect (collection-sweep-traversal-trace records origin) world)))
    (implies (and (collection-sweep-traversal-input-p records origin world)
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) link (+ link 8))
                  (collection-sweep-spans-separate-p address (+ address 8) records))
             (equal (collection-read-word address after) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-sweep-traversal-input-p records origin world)
           :in-theory (disable collection-sweep-entry-p collection-sweep-round-input-p
                               collection-sweep-round-moves-link-only-to-retained-mapping
                               collection-sweep-ready-round-protects-word-on-retain
                               collection-sweep-ready-round-protects-word-on-discard))
          ("Subgoal *1/2"
           :cases ((caddar records))
           :use ((:instance collection-sweep-round-moves-link-only-to-retained-mapping (record (car records)))
                 (:instance collection-sweep-ready-round-protects-word-on-retain (record (car records)))
                 (:instance collection-sweep-ready-round-protects-word-on-discard (record (car records))))
           :in-theory (enable collection-sweep-round-trace))
          ("Subgoal *1/1" :use ((:instance collection-sweep-end-keeps-words-and-regions)))))

(defun collection-sweep-surviving-regions (records regions)
  (if (endp records)
      regions
    (collection-sweep-surviving-regions
     (cdr records)
     (if (caddar records)
         regions
       (proof-remove-region-span (caar records) (cadar records) regions)))))

(defthm collection-sweep-traversal-removes-exactly-discarded-regions
  (let* ((after (collection-trace-effect (collection-sweep-traversal-trace records origin) world)))
    (implies (collection-sweep-traversal-input-p records origin world)
             (equal (proof-world-regions after)
                    (collection-sweep-surviving-regions records (proof-world-regions world)))))
  :rule-classes nil
  :hints (("Goal" :induct (collection-sweep-traversal-input-p records origin world)
                  :in-theory (disable collection-sweep-entry-p collection-sweep-round-input-p
                                      proof-remove-region-span
                                      collection-sweep-retains-one-mapping-and-resets-mark
                                      collection-sweep-discards-one-mapping-and-relinks))
          ("Subgoal *1/2"
           :cases ((caddar records))
           :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                 (:instance collection-sweep-discards-one-mapping-and-relinks))
           :in-theory (enable collection-sweep-round-input-p collection-sweep-round-trace))
          ("Subgoal *1/1" :use ((:instance collection-sweep-end-keeps-words-and-regions)))))

; A retained mapping keeps its size and has its mark cleared. The
; global link and each retained link point to the next survivor.
(defun collection-sweep-surviving-links-p (link records world)
  (if (endp records)
      (equal (collection-read-word link world) 0)
    (let ((head (caar records)))
      (if (caddar records)
          (and (equal (collection-read-word link world) head)
               (equal (collection-read-word (+ head 8) world) (cadar records))
               (equal (collection-read-word (+ head 16) world) 0)
               (collection-sweep-surviving-links-p head (cdr records) world))
        (collection-sweep-surviving-links-p link (cdr records) world)))))

(local
 (defthm collection-sweep-retained-size-unchanged-in-round
   (let* ((head (car record)) (size (cadr record))
          (after (collection-trace-effect (collection-sweep-retain-trace origin) world)))
     (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world)
                   (collection-sweep-round-input-p record world) (caddr record))
              (equal (collection-read-word (+ head 8) after) size)))
   :hints (("Goal"
            :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                  (:instance collection-sweep-word-from-equal-byte-memories
                             (address (+ 8 (car record)))
                             (first (collection-trace-effect (collection-sweep-retain-trace origin) world))
                             (second (collection-write-word (+ 16 (car record)) 0 world)))
                  (:instance collection-disjoint-word-store-preserves-word
                             (address (+ 8 (car record))) (start (+ 16 (car record))) (value 0)))
            :in-theory (disable collection-sweep-entry-p
                                collection-sweep-retains-one-mapping-and-resets-mark
                                collection-disjoint-word-store-preserves-word)))))

(local
 (defthm collection-sweep-suffix-keeps-a-survivor-word
   (let* ((record (car records))
          (head (car record))
          (round (collection-trace-effect (collection-sweep-retain-trace origin) world))
          (after (collection-trace-effect (collection-sweep-traversal-trace (cdr records) origin) round)))
     (implies (and (consp records) (caddr record)
                   (collection-sweep-traversal-input-p records origin world)
                   (proof-span-p address 8)
                   (proof-disjoint-p address (+ address 8) head (+ head 8))
                   (collection-sweep-spans-separate-p address (+ address 8) (cdr records)))
              (equal (collection-read-word address after) (collection-read-word address round))))
   :hints (("Goal"
            :use ((:instance collection-sweep-round-moves-link-only-to-retained-mapping (record (car records)))
                  (:instance collection-sweep-traversal-preserves-word-outside-links-and-mappings
                             (records (cdr records))
                             (world (collection-trace-effect (collection-sweep-retain-trace origin) world))))
            :expand ((collection-sweep-traversal-input-p records origin world))
            :in-theory (e/d (collection-sweep-round-trace)
                             (collection-sweep-entry-p collection-sweep-round-input-p
                              collection-sweep-traversal-input-p
                              collection-sweep-round-moves-link-only-to-retained-mapping
                              collection-sweep-traversal-trace))))))

(local
 (defthm collection-sweep-suffix-keeps-current-survivor-size-and-mark
   (let* ((head (caar records))
          (size (cadar records))
          (address (+ head (if mark 16 8)))
          (after (collection-trace-effect (collection-sweep-traversal-trace records origin) world)))
     (implies (and (consp records) (caddar records)
                   (collection-sweep-traversal-input-p records origin world)
                   (collection-sweep-spans-disjoint-p records))
              (equal (collection-read-word address after) (if mark 0 size))))
   :hints (("Goal" :cases (mark)
            :do-not-induct t
            :expand ((collection-sweep-traversal-input-p records origin world)
                     (collection-sweep-traversal-trace records origin)
                     (collection-sweep-spans-disjoint-p records))
            :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                  (:instance collection-sweep-retained-size-unchanged-in-round (record (car records)))
                  (:instance collection-sweep-subspan-separates-from-same-mappings
                             (records (cdr records)) (address (+ (caar records) (if mark 16 8)))
                             (width 8) (start (caar records)) (end (+ (caar records) (cadar records))))
                  (:instance collection-sweep-suffix-keeps-a-survivor-word
                             (address (+ (caar records) (if mark 16 8)))))
            :in-theory (e/d (collection-sweep-round-trace)
                             (collection-sweep-entry-p collection-sweep-retains-one-mapping-and-resets-mark
                              collection-sweep-retained-size-unchanged-in-round
                              collection-sweep-traversal-input-p collection-sweep-traversal-trace
                              collection-sweep-spans-disjoint-p collection-sweep-spans-separate-p
                              collection-sweep-suffix-keeps-a-survivor-word))))))

(local
 (defthm collection-sweep-suffix-keeps-link-to-current-survivor
   (let* ((link (proof-world-reg 19 world))
          (after (collection-trace-effect (collection-sweep-traversal-trace records origin) world)))
     (implies (and (consp records) (caddar records)
                   (collection-sweep-traversal-input-p records origin world)
                   (collection-sweep-spans-separate-p link (+ link 8) records)
                   (proof-span-p link 8))
              (equal (collection-read-word link after) (caar records))))
   :hints (("Goal"
            :do-not-induct t
            :expand ((collection-sweep-traversal-input-p records origin world)
                     (collection-sweep-traversal-trace records origin)
                     (collection-sweep-spans-separate-p (proof-world-reg 19 world)
                                                        (+ 8 (proof-world-reg 19 world)) records))
            :use ((:instance collection-sweep-ready-round-protects-word-on-retain
                             (address (proof-world-reg 19 world)) (record (car records)))
                  (:instance collection-sweep-suffix-keeps-a-survivor-word
                             (address (proof-world-reg 19 world))))
            :in-theory (e/d (collection-sweep-round-trace)
                             (collection-sweep-entry-p collection-sweep-ready-round-protects-word-on-retain
                              collection-sweep-traversal-input-p collection-sweep-traversal-trace
                              collection-sweep-spans-separate-p
                              collection-sweep-suffix-keeps-a-survivor-word))))))

(defthm collection-sweep-traversal-links-survivors-and-clears-their-marks
  (let* ((link (proof-world-reg 19 world))
         (after (collection-trace-effect (collection-sweep-traversal-trace records origin) world)))
    (implies (and (collection-sweep-traversal-input-p records origin world)
                  (collection-sweep-spans-disjoint-p records)
                  (collection-sweep-spans-separate-p link (+ link 8) records)
                  (proof-span-p link 8))
             (collection-sweep-surviving-links-p link records after)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-sweep-traversal-input-p records origin world)
           :in-theory (disable collection-sweep-entry-p collection-sweep-round-input-p
                               collection-sweep-suffix-keeps-link-to-current-survivor
                               collection-sweep-suffix-keeps-current-survivor-size-and-mark
                               collection-sweep-round-moves-link-only-to-retained-mapping))
          ("Subgoal *1/2"
           :cases ((caddar records))
           :do-not-induct t
           :use ((:instance collection-sweep-suffix-keeps-link-to-current-survivor)
                 (:instance collection-sweep-subspan-separates-from-same-mappings
                            (records (cdr records)) (address (caar records)) (width 8)
                            (start (caar records)) (end (+ (caar records) (cadar records))))
                 (:instance collection-sweep-suffix-keeps-current-survivor-size-and-mark (mark t))
                 (:instance collection-sweep-suffix-keeps-current-survivor-size-and-mark (mark nil))
                 (:instance collection-sweep-round-moves-link-only-to-retained-mapping
                            (record (car records))))
           :in-theory (enable collection-sweep-round-trace))
          ("Subgoal *1/1"
           :use ((:instance collection-sweep-end-keeps-words-and-regions
                            (address (proof-world-reg 19 world)))))))
