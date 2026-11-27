(in-package "BOYMOO-PROOFS")

(include-book "region-tally")
(include-book "external-list")
(include-book "segments")
(include-book "../foundations/loading")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-linux-writable-regions-p (regions)
  (if (atom regions)
      t
    (and (implies (eq (caddar regions) :rw)
                  (<= (cadar regions) (expt 2 63)))
         (allocation-linux-writable-regions-p (cdr regions)))))

(defthm allocation-linux-write-coverage-bounds-end
  (implies (and (allocation-linux-writable-regions-p regions)
                (proof-covered-p start size :write regions))
           (<= (+ start size) (expt 2 63)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-covered-p start size :write regions)
           :in-theory (disable proof-span-p))))

(defthm allocation-linux-write-regions-bound-stack-reservation
  (implies (and (proof-heap-layout-p world)
                (allocation-linux-writable-regions-p (proof-world-regions world)))
           (<= (proof-stack-end world) (expt 2 63)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-linux-write-coverage-bounds-end
                  (start (proof-stack-base world)) (size *proof-value-reservation*)
                  (regions (proof-world-regions world))))
           :in-theory (disable allocation-linux-writable-regions-p proof-regions-p
                               proof-covered-p proof-align-up proof-disjoint-p mod))))

(local
 (defthm allocation-linux-writable-member-bounds-end
   (implies (and (allocation-linux-writable-regions-p regions)
                 (member-equal (proof-region start end :rw) regions))
            (<= end (expt 2 63)))
   :rule-classes nil
   :hints (("Goal" :induct (allocation-linux-writable-regions-p regions)))))

(local
 (defun allocation-external-regions (headers machine)
   (if (atom headers)
       nil
     (let* ((header (car headers))
            (start (- header 24))
            (size (proof-load-word (- header 16) machine)))
       (cons (proof-region start (+ start size) :rw)
             (allocation-external-regions (cdr headers) machine))))))

(local
 (defthm allocation-external-list-selects-mapped-byte-total
   (equal (allocation-region-bytes (allocation-external-regions headers machine))
          (proof-external-bytes headers machine))
   :hints (("Goal" :induct (allocation-external-regions headers machine)
            :in-theory (disable proof-load-word)))))

(local
 (defthm allocation-external-walk-at-zero
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(local
 (defun allocation-external-two-fuels-induction (head fuel other-fuel machine)
   (declare (xargs :measure (nfix fuel)))
   (if (and (not (equal head 0)) (posp fuel) (posp other-fuel))
       (allocation-external-two-fuels-induction (proof-load-word head machine)
                                               (1- fuel) (1- other-fuel) machine)
     head)))

(local
 (defthm allocation-successful-external-walk-is-independent-of-fuel
   (implies (and (proof-external-objects head fuel world objects)
                 (proof-external-objects head other-fuel world objects))
            (equal (proof-external-objects head fuel world objects)
                   (proof-external-objects head other-fuel world objects)))
   :rule-classes nil
   :hints (("Goal" :induct (allocation-external-two-fuels-induction head fuel other-fuel (proof-world-machine world))
            :expand ((:free (limit) (proof-external-objects head limit world objects)))
            :in-theory (disable (:definition proof-external-objects) proof-load-word proof-align-up
                                proof-header-size proof-header-type proof-disjoint-p
                                proof-runtime-word allocation-runtime-word-as-load)))))

(local
 (defthm allocation-other-successful-walk-has-no-more-entries
   (implies (and (proof-external-objects head fuel world objects)
                 (proof-external-objects head other-fuel world objects))
            (<= (len (cdr (proof-external-objects head other-fuel world objects)))
                (len (cdr (proof-external-objects head fuel world objects)))))
   :rule-classes nil
   :hints (("Goal" :use allocation-successful-external-walk-is-independent-of-fuel
            :in-theory (disable proof-external-objects)))))

; A repeated mapping would give a shorter successful traversal from
; the same head, contrary to independence of the fuel bound.
(local
 (defthm allocation-external-walk-at-visit-has-no-more-entries
   (let* ((machine (proof-world-machine world))
          (entries (cdr (proof-external-objects head fuel world objects)))
          (wanted-region (proof-region wanted (+ wanted (proof-load-word (+ wanted 8) machine)) :rw)))
     (implies (and (natp head) (natp wanted)
                   (member-equal wanted-region (allocation-external-regions entries machine))
                   (proof-external-objects wanted wanted-fuel world objects))
              (<= (len (cdr (proof-external-objects wanted wanted-fuel world objects)))
                  (len entries))))
   :rule-classes nil
   :hints (("Goal" :induct (proof-external-objects head fuel world objects)
            :expand ((proof-external-objects head fuel world objects))
            :in-theory (disable (:definition proof-external-objects) proof-load-word proof-align-up
                                proof-header-size proof-header-type proof-disjoint-p
                                proof-runtime-word allocation-runtime-word-as-load))
           ("Subgoal *1/2"
            :use ((:instance allocation-other-successful-walk-has-no-more-entries
                   (other-fuel wanted-fuel)))))))

(local
 (defthm allocation-external-list-selects-distinct-registered-regions
   (let* ((machine (proof-world-machine world))
          (regions (proof-world-regions world))
          (entries (cdr (proof-external-objects head fuel world objects)))
          (selected (allocation-external-regions entries machine)))
     (implies (and (natp head) (proof-regions-p regions)
                   (allocation-linux-writable-regions-p regions))
              (and (subsetp-equal selected regions)
                   (no-duplicatesp-equal selected)
                   (allocation-regions-within-p 1 (expt 2 63) selected))))
   :rule-classes nil
   :hints (("Goal" :induct (proof-external-objects head fuel world objects)
            :expand ((proof-external-objects head fuel world objects))
            :in-theory (disable (:definition proof-external-objects)
                                allocation-linux-writable-regions-p proof-regions-p
                                proof-load-word proof-align-up proof-header-size proof-header-type proof-disjoint-p
                                proof-runtime-word allocation-runtime-word-as-load))
           ("Subgoal *1/2"
            :use ((:instance allocation-external-walk-at-visit-has-no-more-entries
                   (wanted head) (wanted-fuel fuel) (head (proof-load-word head (proof-world-machine world)))
                   (fuel (1- fuel)))
                  (:instance allocation-linux-writable-member-bounds-end
                   (regions (proof-world-regions world)) (start head)
                   (end (+ head (proof-load-word (+ head 8) (proof-world-machine world))))))))))

(local
 (defthm allocation-known-region-disjoint-from-member
   (implies (and (proof-region-disjoint-p start end regions)
                 (member-equal region regions))
            (proof-disjoint-p start end (car region) (cadr region)))
   :rule-classes nil
   :hints (("Goal" :induct (proof-region-disjoint-p start end regions)
            :in-theory (disable proof-disjoint-p)))))

(local
 (defthm allocation-registered-distinct-regions-are-disjoint
   (implies (and (proof-regions-p regions) (member-equal region regions)
                 (member-equal other regions) (not (equal region other)))
            (proof-disjoint-p (car region) (cadr region) (car other) (cadr other)))
   :rule-classes nil
   :hints (("Goal" :induct (proof-regions-p regions)
            :in-theory (disable proof-region-p proof-region-disjoint-p))
           ("Subgoal *1/2"
            :use ((:instance allocation-known-region-disjoint-from-member
                   (start (caar regions)) (end (cadar regions)) (regions (cdr regions)))
                  (:instance allocation-known-region-disjoint-from-member
                   (start (caar regions)) (end (cadar regions)) (regions (cdr regions)) (region other)))))))

(local
 (defthm allocation-registered-region-disjoint-from-distinct-selection
   (implies (and (proof-regions-p regions) (member-equal region regions)
                 (subsetp-equal selected regions) (not (member-equal region selected)))
            (proof-region-disjoint-p (car region) (cadr region) selected))
   :rule-classes nil
   :hints (("Goal" :induct (subsetp-equal selected regions)
            :in-theory (disable proof-regions-p proof-disjoint-p))
           ("Subgoal *1/2"
            :use ((:instance allocation-registered-distinct-regions-are-disjoint
                   (other (car selected))))))))

(local
 (defthm allocation-member-region-is-valid
   (implies (and (proof-regions-p regions) (member-equal region regions))
            (proof-region-p region))
   :rule-classes nil
   :hints (("Goal" :induct (proof-regions-p regions)
            :in-theory (disable proof-region-p proof-region-disjoint-p)))))

(local
 (defthm allocation-selected-regions-stay-well-formed
   (implies (and (proof-regions-p regions) (subsetp-equal selected regions)
                 (true-listp selected) (no-duplicatesp-equal selected))
            (proof-regions-p selected))
   :rule-classes nil
   :hints (("Goal" :induct (subsetp-equal selected regions)
            :in-theory (disable proof-region-p proof-region-disjoint-p))
           ("Subgoal *1/2"
            :use ((:instance allocation-member-region-is-valid (region (car selected)))
                  (:instance allocation-registered-region-disjoint-from-distinct-selection
                   (region (car selected)) (selected (cdr selected))))))))

(local
 (defthm allocation-fresh-region-disjoint-from-selection
   (implies (and (subsetp-equal selected regions)
                 (proof-region-disjoint-p start end regions))
            (proof-region-disjoint-p start end selected))
   :hints (("Goal" :induct (subsetp-equal selected regions)
            :in-theory (disable proof-disjoint-p))
           ("Subgoal *1/2"
            :use ((:instance allocation-known-region-disjoint-from-member
                   (region (car selected))))))))

(defthm allocation-adding-fresh-region-bounds-external-byte-total
  (let* ((machine (proof-world-machine world))
         (regions (proof-world-regions world))
         (entries (cdr (proof-external-objects head fuel world objects))))
    (implies (and (natp head)
                  (proof-regions-p regions) (allocation-linux-writable-regions-p regions)
                  (integerp start) (integerp end) (<= 1 start) (< start end) (<= end (expt 2 63))
                  (proof-region-disjoint-p start end regions))
             (< (+ (proof-external-bytes entries machine) (- end start)) (expt 2 63))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-external-list-selects-distinct-registered-regions
                 (:instance allocation-selected-regions-stay-well-formed
                  (selected (allocation-external-regions
                             (cdr (proof-external-objects head fuel world objects)) (proof-world-machine world)))
                  (regions (proof-world-regions world)))
                 (:instance allocation-fresh-region-disjoint-from-selection
                  (selected (allocation-external-regions
                             (cdr (proof-external-objects head fuel world objects)) (proof-world-machine world)))
                  (regions (proof-world-regions world)))
                 (:instance allocation-regions-total-fits-range
                  (lower 1) (upper (expt 2 63))
                  (regions (cons (proof-region start end :rw)
                                 (allocation-external-regions
                                  (cdr (proof-external-objects head fuel world objects)) (proof-world-machine world))))))
           :in-theory (disable allocation-external-regions allocation-linux-writable-regions-p
                               proof-region-disjoint-p proof-external-objects proof-external-bytes
                               proof-load-word subsetp-equal no-duplicatesp-equal))))

(local
 (defthm allocation-remove-region-span-keeps-linux-bounds
   (implies (allocation-linux-writable-regions-p regions)
            (allocation-linux-writable-regions-p (proof-remove-region-span start size regions)))
   :hints (("Goal" :induct (proof-remove-region-span start size regions)
            :in-theory (disable unsigned-byte-p)))))

(local
 (defthm allocation-region-field-of-update
   (implies (natp slot)
            (equal (proof-world-regions (update-nth slot value world))
                   (if (equal slot 1) value (proof-world-regions world))))
   :hints (("Goal" :in-theory (enable proof-world-regions)))))

(local (in-theory (disable update-nth)))

(local
 (defthm allocation-cleared-world-keeps-regions
   (equal (proof-world-regions (proof-clear-span start end world))
          (proof-world-regions world))
   :hints (("Goal" :in-theory (disable proof-clear-memory proof-world-machine)))))

(local
 (defthm allocation-svc-return-keeps-regions
   (equal (proof-world-regions (proof-svc-return reply world))
          (proof-world-regions world))
   :hints (("Goal" :in-theory (disable proof-world-replies proof-world-machine proof-world-pc
                                      boymoo-model::a64-set-pc boymoo-model::a64-write-reg)))))

(local
 (defthm allocation-linux-map-keeps-writable-bounds
   (implies (allocation-linux-writable-regions-p (proof-world-regions world))
            (allocation-linux-writable-regions-p (proof-world-regions (proof-linux-map reply world))))
   :hints (("Goal" :in-theory (disable proof-region-disjoint-p proof-svc-return proof-clear-span
                                      proof-world-reg proof-page-size-p proof-align-up proof-linux-errno-p mod)))))

(local
 (defthm allocation-linux-release-keeps-writable-bounds
   (implies (allocation-linux-writable-regions-p (proof-world-regions world))
            (allocation-linux-writable-regions-p
             (proof-world-regions (proof-linux-release unmap reply world))))
   :hints (("Goal" :in-theory (disable proof-remove-region-span proof-svc-return proof-clear-span
                                      proof-covered-p proof-world-reg proof-page-size-p proof-align-up mod)))))

(local
 (defthm allocation-linux-streams-keep-regions
   (and (equal (proof-world-regions (proof-linux-read reply world)) (proof-world-regions world))
        (equal (proof-world-regions (proof-linux-write reply world)) (proof-world-regions world)))
   :hints (("Goal" :in-theory (disable proof-covered-p proof-svc-return proof-store-bytes proof-byte-list
                                      proof-world-input proof-world-reg proof-linux-errno-p)))))

(local
 (defthm allocation-linux-svc-keeps-writable-bounds
   (implies (allocation-linux-writable-regions-p (proof-world-regions world))
            (allocation-linux-writable-regions-p (proof-world-regions (proof-linux-svc event world))))
   :hints (("Goal" :in-theory (disable allocation-linux-writable-regions-p proof-world-reg
                                      proof-world-replies proof-linux-map proof-linux-release
                                      proof-linux-read proof-linux-write)))))

(defthm allocation-linux-writable-regions-preserved-by-step
  (implies (allocation-linux-writable-regions-p (proof-world-regions world))
           (allocation-linux-writable-regions-p (proof-world-regions (proof-step world))))
  :hints (("Goal"
           :in-theory (e/d (proof-step proof-instruction-effect)
                           (allocation-linux-writable-regions-p proof-execute proof-fetchable-p
                            proof-instruction-access-p proof-decode-at proof-linux-svc
                            proof-world-pc proof-world-stop proof-world-machine)))))

(defthm allocation-linux-writable-regions-preserved-by-prefix
  (implies (and (allocation-linux-writable-regions-p (proof-world-regions before))
                (allocation-prefix-p steps cuts before after))
           (allocation-linux-writable-regions-p (proof-world-regions after)))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-prefix-p steps cuts before after)
           :in-theory (disable allocation-linux-writable-regions-p proof-step))))

(defthm allocation-linux-loader-keeps-writable-region-bounds
  (implies (allocation-linux-writable-regions-p regions)
           (allocation-linux-writable-regions-p
            (proof-world-regions (proof-load-linux file machine regions page input replies))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-load-linux proof-world proof-world-regions)
                           (proof-elf-p proof-elf-entry proof-covered-p proof-region-disjoint-p
                            proof-regions-p proof-page-size-p proof-align-up proof-clear-memory
                            proof-load-cleared-string boymoo-model::a64-set-pc
                            boymoo-model::a64-sp boymoo-model::a64-memory mod)))))
