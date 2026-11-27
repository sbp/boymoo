(in-package "BOYMOO-PROOFS")

(include-book "large-publication")
(include-book "published-heap")
(include-book "writes-heap")

(logic)
(set-verify-guards-eagerness 0)

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm allocation-string-accounting-after-appending-mapping
    (let* ((old-total (proof-external-bytes headers (proof-world-machine before)))
           (new-machine (proof-world-machine after)))
      (implies (and (proof-string-accounting-p headers before)
                    (natp size) (equal (mod size *proof-runtime-page*) 0)
                    (equal (proof-external-bytes headers new-machine) old-total)
                    (equal (proof-load-word (- header 16) new-machine) size)
                    (< (+ size old-total) (expt 2 63))
                    (equal (proof-string-bytes-since-collection after)
                           (+ (proof-string-bytes-since-collection before) size))
                    (equal (proof-string-budget after) (proof-string-budget before)))
               (proof-string-accounting-p (cons header headers) after)))
    :rule-classes nil
    :hints (("Goal"
             :in-theory (disable proof-string-bytes-since-collection proof-string-budget
                                 allocation-runtime-word-as-load proof-runtime-word proof-load-word mod)))))

(local (include-book "arithmetic/top" :dir :system))

(defthm allocation-external-record-in-agreeing-span
  (implies (and (proof-regions-p (proof-world-regions before))
                (member-equal (proof-region head end :rw) (proof-world-regions before))
                (<= (+ head 32) end)
                (proof-memory-span-agrees-p head end before after))
           (and (equal (allocation-load-word head after) (allocation-load-word head before))
                (equal (allocation-load-word (+ 8 head) after) (allocation-load-word (+ 8 head) before))
                (equal (allocation-load-word (+ 16 head) after) (allocation-load-word (+ 16 head) before))
                (equal (allocation-load-word (+ 24 head) after) (allocation-load-word (+ 24 head) before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-region-member-has-valid-span
                  (start head) (mode :rw) (regions (proof-world-regions before)))
                 (:instance allocation-word-in-agreeing-span (lower head) (upper end) (address head))
                 (:instance allocation-word-in-agreeing-span (lower head) (upper end) (address (+ 8 head)))
                 (:instance allocation-word-in-agreeing-span (lower head) (upper end) (address (+ 16 head)))
                 (:instance allocation-word-in-agreeing-span (lower head) (upper end) (address (+ 24 head))))
           :in-theory (disable proof-regions-p proof-region proof-memory-span-agrees-p))))

(local
 (defthm allocation-external-objects-of-end-marker
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(local
 (defthm allocation-fixed-external-head-and-tail
   (equal (proof-fixed-external-p (cons header headers) before after)
          (and (proof-memory-span-agrees-p
                (- header 24) (+ (- header 24) (proof-load-word (- header 16) (proof-world-machine before))) before after)
               (proof-fixed-external-p headers before after)))
   :hints (("Goal" :in-theory (disable proof-memory-span-agrees-p proof-load-word)))))

(defthm allocation-external-objects-from-fixed-mapping-memory
  (let* ((old-list (proof-external-objects head fuel before objects))
         (headers (cdr old-list)))
    (implies (and old-list
                  (allocation-same-external-bounds-p before after)
                  (proof-regions-p (proof-world-regions before))
                  (proof-fixed-external-p headers before after))
             (and (equal (proof-external-objects head fuel after objects) old-list)
                  (equal (proof-external-bytes headers (proof-world-machine after))
                         (proof-external-bytes headers (proof-world-machine before))))))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel before objects)
           :expand ((:free (world) (proof-external-objects head fuel world objects)))
           :in-theory (e/d (allocation-same-external-bounds-p allocation-load-word)
                           ((:definition proof-external-objects) proof-heap-base proof-machine-limit
                            proof-runtime-word allocation-runtime-word-as-load proof-load-word
                            proof-align-up proof-regions-p proof-header-size proof-header-type
                            proof-disjoint-p proof-memory-span-agrees-p (:definition proof-fixed-external-p) mod)))
          ("Subgoal *1/2"
           :use ((:instance allocation-align-up-bounds
                  (size (+ 32 (proof-header-size (proof-load-word (+ head 24) (proof-world-machine before)))))
                  (alignment *proof-runtime-page*))
                 (:instance allocation-external-record-in-agreeing-span
                  (end (+ head (proof-load-word (+ head 8) (proof-world-machine before)))))
                 (:instance allocation-region-member-has-valid-span
                  (start head) (mode :rw) (regions (proof-world-regions before))
                  (end (+ head (proof-load-word (+ head 8) (proof-world-machine before)))))))))

(defun allocation-external-spans-avoid-writes-p (headers writes world)
  (if (atom headers)
      t
    (let* ((head (- (car headers) 24))
           (end (+ head (proof-load-word (+ head 8) (proof-world-machine world)))))
      (and (natp head) (natp end) (<= end *allocation-word-modulus*)
           (allocation-word-writes-avoid-span-p writes head end)
           (allocation-external-spans-avoid-writes-p (cdr headers) writes world)))))

(defthm allocation-word-writes-keep-external-mapping-spans
  (implies (and (allocation-external-spans-avoid-writes-p headers writes before)
                (equal (allocation-memory after) (allocation-memory (allocation-write-words writes before))))
           (proof-fixed-external-p headers before after))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-external-spans-avoid-writes-p headers writes before)
           :in-theory (disable allocation-write-words proof-load-word
                               allocation-word-writes-avoid-span-p proof-memory-span-agrees-p))
          ("Subgoal *1/2"
           :use ((:instance allocation-word-writes-keep-protected-span
                  (world before) (lower (- (car headers) 24))
                  (upper (+ (- (car headers) 24) (proof-load-word (- (car headers) 16) (proof-world-machine before)))))))))

(defthm allocation-large-keeps-old-external-list
  (let* ((head (proof-external-head before))
         (old-list (proof-external-objects head (len objects) before objects))
         (writes (allocation-large-initialization-writes before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (allocation-same-external-bounds-p before after)
                  (proof-regions-p (proof-world-regions before))
                  old-list (allocation-external-spans-avoid-writes-p (cdr old-list) writes before))
             (and (equal (proof-external-objects head (len objects) after objects) old-list)
                  (equal (proof-external-bytes (cdr old-list) (proof-world-machine after))
                         (proof-external-bytes (cdr old-list) (proof-world-machine before))))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialization-write-footprint
                 (:instance allocation-word-writes-keep-external-mapping-spans
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))
                  (writes (allocation-large-initialization-writes before)))
                 (:instance allocation-external-objects-from-fixed-mapping-memory
                  (head (proof-external-head before)) (fuel (len objects))))
           :in-theory (disable proof-external-objects proof-external-head proof-external-bytes proof-fixed-external-p
                               allocation-external-spans-avoid-writes-p allocation-large-initialization-writes
                               allocation-write-words allocation-large-mapped-entry-p allocation-large-insertion-p
                               allocation-large-header-p proof-regions-p))))

(defthm allocation-large-accounting-after-publication
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))
         (old-total (proof-external-bytes headers (proof-world-machine before))))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (equal (proof-heap-base after) (proof-heap-base before))
                  (equal size (allocation-large-mapping-size length))
                  (equal (proof-external-bytes headers (proof-world-machine after)) old-total)
                  (proof-string-accounting-p headers before)
                  (< (+ old-total size) (expt 2 63)))
             (proof-string-accounting-p (cons (+ mapping 24) headers) after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialization-preserves-bookkeeping
                 (:instance allocation-string-accounting-after-appending-mapping
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))
                  (header (+ 24 (proof-world-reg 0 before))) (size (proof-world-reg 20 before))))
           :in-theory (e/d (allocation-load-word)
                           (proof-external-objects proof-external-head proof-external-bytes proof-string-accounting-p
                            proof-string-budget proof-string-bytes-since-collection proof-load-word proof-align-up
                            allocation-runtime-word-as-load allocation-large-mapped-entry-p allocation-large-insertion-p
                            allocation-large-header-p mod)))))

(defthm allocation-large-writes-avoid-disjoint-span
  (let* ((mapping (proof-world-reg 0 before))
         (end (+ mapping (proof-world-reg 20 before)))
         (base (proof-heap-base before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (proof-disjoint-p mapping end lower upper)
                  (proof-disjoint-p (- base 128) base lower upper))
             (allocation-word-writes-avoid-span-p (allocation-large-initialization-writes before) lower upper)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-code-origin-p allocation-large-string-address
                                     allocation-string-header))))

(defthm allocation-listed-region-avoids-fresh-mapping
  (implies (and (proof-region-disjoint-p start end regions)
                (member-equal (proof-region lower upper mode) regions))
           (proof-disjoint-p start end lower upper))
  :rule-classes nil
  :hints (("Goal" :induct (proof-region-disjoint-p start end regions)
           :in-theory (disable proof-disjoint-p))))

(defthm allocation-large-cleared-header-is-zero
  (let ((mapping (proof-world-reg 0 before))
        (size (proof-world-reg 20 before)))
    (implies (and (proof-span-p mapping size) (<= 32 size)
                  (equal (allocation-memory before) (proof-clear-memory mapping (+ mapping size) memory)))
             (equal (proof-load-word (+ mapping 24) (proof-world-machine before)) 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-read-within-cleared-span
                  (address (+ 24 (proof-world-reg 0 before))) (bytes 8) (start (proof-world-reg 0 before))
                  (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))))
           :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                           (proof-clear-memory boymoo-model::a64-read-bytes)))))

(defthm allocation-large-fresh-region-writes-avoid-existing-external-spans
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (regions (proof-world-regions before))
         (new-region (proof-region mapping (+ mapping size) :rw))
         (list (proof-external-objects head fuel before objects)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal regions (cons new-region old-regions))
                  (proof-regions-p regions)
                  (<= (proof-heap-base before) (proof-spaces-end before))
                  (equal (proof-load-word (+ mapping 24) (proof-world-machine before)) 0)
                  list)
             (allocation-external-spans-avoid-writes-p
              (cdr list) (allocation-large-initialization-writes before) before)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel before objects)
           :expand ((proof-external-objects head fuel before objects))
           :in-theory (disable (:definition proof-external-objects) allocation-large-mapped-entry-p
                               allocation-large-initialization-writes allocation-word-writes-avoid-span-p
                               proof-load-word proof-header-size proof-header-type proof-runtime-word
                               allocation-runtime-word-as-load proof-heap-base proof-align-up))
          ("Subgoal *1/2"
           :use ((:instance allocation-large-writes-avoid-disjoint-span
                  (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before)))))
                 (:instance allocation-region-member-has-valid-span
                  (start head) (end (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                  (mode :rw) (regions (proof-world-regions before)))
                 (:instance allocation-listed-region-avoids-fresh-mapping
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                  (mode :rw) (regions old-regions))))))

(defthm allocation-large-initialization-avoids-runtime-word
  (let ((address (+ (- (proof-heap-base before) 128) offset)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (member-equal offset '(0 8 16 24 32 40 48 64 80)))
             (and (proof-span-p address 8)
                  (allocation-word-writes-avoid-span-p (allocation-large-initialization-writes before)
                                                       address (+ address 8)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-code-origin-p allocation-large-string-address
                                     allocation-string-header))))

(defthm allocation-large-initialization-keeps-runtime-word
  (let* ((writes (allocation-large-initialization-writes before))
         (shadow (allocation-write-words writes before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal (proof-heap-base after) (proof-heap-base before))
                  (equal (allocation-memory after) (allocation-memory shadow))
                  (member-equal offset '(0 8 16 24 32 40 48 64 80)))
             (equal (proof-runtime-word offset after) (proof-runtime-word offset before))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialization-avoids-runtime-word
                 (:instance allocation-word-writes-keep-word-in-avoided-span
                  (writes (allocation-large-initialization-writes before)) (world before)
                  (address (+ (- (proof-heap-base before) 128) offset))
                  (lower (+ (- (proof-heap-base before) 128) offset))
                  (upper (+ (- (proof-heap-base before) 128) offset 8)))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first after) (last (allocation-write-words (allocation-large-initialization-writes before) before))))
           :in-theory (e/d (proof-runtime-word)
                           (allocation-runtime-word-as-load proof-load-word proof-heap-base
                            allocation-equal-memory-is-model-equivalence allocation-large-mapped-entry-p
                            allocation-large-initialization-writes allocation-write-words
                            allocation-word-writes-avoid-span-p)))))

(defthm allocation-large-postmap-keeps-heap-registers
  (implies (and (allocation-large-mapped-entry-p origin before)
                (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
           (and (equal (proof-machine-limit after) (proof-machine-limit before))
                (equal (proof-stack-limit after) (proof-stack-limit before))
                (equal (proof-stack-top after) (proof-stack-top before))
                (equal (proof-heap-limit after) (proof-heap-limit before))
                (equal (proof-box-top after) (proof-box-top before))
                (equal (proof-heap-base after) (proof-heap-base before))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference
                                     allocation-code-origin-p allocation-large-string-address))))

(defthm allocation-large-static-and-stack-footprint
  (let* ((mapping (proof-world-reg 0 before))
         (end (+ mapping (proof-world-reg 20 before)))
         (base (proof-heap-base before))
         (size (proof-static-size base (proof-world-machine before)))
         (writes (allocation-large-initialization-writes before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (proof-heap-layout-p before)
                  (proof-disjoint-p mapping end (- base *proof-heap-prefix*) (proof-spaces-end before))
                  (proof-disjoint-p mapping end (proof-stack-base before) (proof-stack-end before)))
             (and (allocation-word-writes-avoid-span-p writes base (+ base size))
                  (allocation-word-writes-avoid-span-p writes (proof-stack-base before) (proof-stack-end before)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-large-writes-avoid-disjoint-span
                  (lower (proof-heap-base before))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-large-writes-avoid-disjoint-span
                  (lower (proof-stack-base before)) (upper (proof-stack-end before))))
           :in-theory (disable allocation-large-mapped-entry-p proof-heap-layout-p
                               allocation-large-initialization-writes allocation-word-writes-avoid-span-p
                               proof-runtime-word allocation-runtime-word-as-load proof-static-size
                               proof-heap-base proof-machine-limit))))
