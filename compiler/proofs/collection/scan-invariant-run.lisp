(in-package "BOYMOO-PROOFS")

(include-book "scan-memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-load-word collection-read-word proof-reg proof-world-reg
                     proof-world-pc proof-instruction-effect collection-cpu-p
                     collection-source-marker-p collection-external-mark-p
                     collection-forwarding collection-source-pending-p
                     collection-copy-field-count collection-copy-field-offset collection-copy-is-raw-p
                     collection-datum-assigned-p collection-relocate-datum
                     boymoo-model::a64-unsigned boymoo-model::a64-memory boymoo-model::a64-read-bytes
                     proof-heap-base proof-stack-base proof-stack-top (:definition ash)
                     (:definition acl2::binary-logior) (:definition acl2::binary-logand))))

(local
 (defthm collection-observations-of-word-lists-depend-only-on-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-slot-words count address first)
                   (collection-slot-words count address second)))
   :rule-classes nil
   :hints (("Goal" :induct (collection-slot-words count address first)
                   :in-theory (enable collection-read-word proof-load-word boymoo-model::a64-load)))))

(local
 (defthm collection-committed-slot-observations-depend-only-on-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-scanned-fields-p count source target base objects original first work)
                   (collection-scanned-fields-p count source target base objects original second work)))
   :rule-classes nil
   :hints (("Goal"
            :induct (collection-scanned-fields-p count source target base objects original first work)
            :in-theory (enable collection-read-word proof-load-word boymoo-model::a64-load)))))

(local
 (defthm collection-graph-observations-depend-only-on-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-graph-bytes-observed-p graph base objects original first work)
                   (collection-graph-bytes-observed-p graph base objects original second work)))
   :rule-classes nil
   :hints (("Goal"
            :induct (len graph)
            :in-theory (e/d (collection-source-marker-p collection-external-mark-p
                                                       collection-read-word proof-load-word boymoo-model::a64-load)
                             (collection-slot-words collection-scanned-fields-p)))
           ("Subgoal *1/1"
            :use ((:instance collection-observations-of-word-lists-depend-only-on-memory
                             (count (collection-copy-field-count (cadar graph)
                                                                 (collection-read-word (caar graph) original)))
                             (address (+ (cdr (assoc-equal (caar graph) (collection-forwarding work)))
                                         (collection-copy-field-offset (cadar graph)))))
                  (:instance collection-committed-slot-observations-depend-only-on-memory
                             (count (collection-copy-field-count (cadar graph)
                                                                 (collection-read-word (caar graph) original)))
                             (source (+ (caar graph) (collection-copy-field-offset (cadar graph))))
                             (target (+ (cdr (assoc-equal (caar graph) (collection-forwarding work)))
                                        (collection-copy-field-offset (cadar graph))))))))))

(local
 (defthm collection-scan-selection-keeps-byte-memory
   (implies (and (collection-cpu-p world) (not (collection-scan-pending-p work)))
            (equal (boymoo-model::a64-memory
                    (proof-world-machine
                     (collection-trace-effect (collection-scan-selection-trace work origin) world)))
                   (boymoo-model::a64-memory (proof-world-machine world))))
   :hints (("Goal"
            :in-theory (e/d (collection-scan-selection-trace collection-trace-effect
                                                            collection-scan-pending-p)
                             (collection-write-pc collection-write-flags collection-subtract-flags
                              boymoo-model::a64-condition boymoo-model::a64-nzcv))))))

; Each body supplies the memory effects of the calls that occur in that
; round. The selection instructions belong to the concrete trace.
(defun collection-scan-script-memory-effects-p (bodies work origin graph original objects world)
  (declare (xargs :measure (acl2-count bodies)))
  (if (collection-scan-pending-p work)
      (and (consp bodies)
           (let* ((selected (collection-trace-effect (collection-scan-selection-trace work origin) world))
                  (after (collection-trace-effect (car bodies) selected))
                  (base (proof-heap-base original))
                  (bottom (proof-stack-base original))
                  (count (ash (- (proof-stack-top original) bottom) -3)))
             (and (equal (collection-slot-words 1 (+ base 24) world)
                         (collection-slot-words 1 (+ base 24) after))
                  (equal (collection-slot-words count bottom world)
                         (collection-slot-words count bottom after))
                  (collection-scan-graph-effects-p graph base objects original world after work)
                  (collection-scan-script-memory-effects-p
                   (cdr bodies) (collection-scan-one work) origin graph original objects after))))
    (collection-cpu-p world)))

(local
 (in-theory (disable collection-scan-memory-p collection-scan-selection-trace
                     collection-trace-effect collection-slot-words collection-scanned-fields-p
                     collection-graph-bytes-observed-p collection-finish-scan collection-scan-one)))

(local
 (defthm collection-last-selection-keeps-scan-memory-invariant
   (let ((next (collection-trace-effect (collection-scan-selection-trace work origin) world)))
     (implies (and (collection-scan-memory-p graph original objects world work)
                   (collection-cpu-p world) (not (collection-scan-pending-p work)))
              (collection-scan-memory-p graph original objects next work)))
   :hints (("Goal"
            :use ((:instance collection-graph-observations-depend-only-on-memory
                             (first world) (base (proof-heap-base original))
                             (second (collection-trace-effect (collection-scan-selection-trace work origin) world)))
                  (:instance collection-committed-slot-observations-depend-only-on-memory
                             (first world) (base (proof-heap-base original)) (count 1)
                             (source (+ (proof-heap-base original) 24)) (target (+ (proof-heap-base original) 24))
                             (second (collection-trace-effect (collection-scan-selection-trace work origin) world)))
                  (:instance collection-committed-slot-observations-depend-only-on-memory
                             (first world) (base (proof-heap-base original))
                             (count (ash (- (proof-stack-top original) (proof-stack-base original)) -3))
                             (source (proof-stack-base original)) (target (proof-stack-base original))
                             (second (collection-trace-effect (collection-scan-selection-trace work origin) world))))
            :in-theory (enable collection-scan-memory-p)))))

(local
 (defthm collection-scan-memory-effects-prepare-next-round
   (let ((after (collection-trace-effect
                 (car bodies)
                 (collection-trace-effect (collection-scan-selection-trace work origin) world))))
     (implies (and (collection-scan-script-memory-effects-p bodies work origin graph original objects world)
                   (collection-scan-pending-p work))
              (and (consp bodies)
                   (collection-scan-script-memory-effects-p
                    (cdr bodies) (collection-scan-one work) origin graph original objects after)
                   (implies (collection-scan-memory-p graph original objects world work)
                            (collection-scan-memory-p graph original objects after (collection-scan-one work))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-scan-round-preserves-memory-invariant
                             (before world)
                             (after (collection-trace-effect
                                     (car bodies)
                                     (collection-trace-effect (collection-scan-selection-trace work origin) world)))))
            :expand ((collection-scan-script-memory-effects-p bodies work origin graph original objects world))
            :in-theory (disable collection-scan-script-memory-effects-p collection-scan-graph-effects-p
                                collection-scan-pending-p)))))

(local
 (defthm collection-empty-scan-memory-effects-give-cpu
   (implies (and (not (collection-scan-pending-p work))
                 (collection-scan-script-memory-effects-p bodies work origin graph original objects world))
            (collection-cpu-p world))
   :rule-classes nil
   :hints (("Goal"
            :expand ((collection-scan-script-memory-effects-p bodies work origin graph original objects world))
            :in-theory (disable collection-scan-script-memory-effects-p collection-scan-pending-p)))))

(local
 (defun collection-scan-memory-induction (bodies work origin world)
   (declare (xargs :measure (acl2-count bodies)))
   (if (and (consp bodies) (collection-scan-pending-p work))
       (collection-scan-memory-induction
        (cdr bodies) (collection-scan-one work) origin
        (collection-trace-effect
         (car bodies) (collection-trace-effect (collection-scan-selection-trace work origin) world)))
     world)))

(defthm collection-scan-script-preserves-memory-invariant
  (let* ((trace (collection-scan-script-trace bodies work origin))
         (final (collection-trace-effect trace world)))
    (implies (and (collection-scan-memory-p graph original objects world work)
                  (collection-scan-script-memory-effects-p bodies work origin graph original objects world))
             (collection-scan-memory-p graph original objects final (collection-finish-scan work))))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-scan-memory-induction bodies work origin world)
           :expand ((collection-finish-scan work) (collection-scan-script-trace bodies work origin))
           :in-theory (e/d (collection-scan-pending-p)
                            (collection-scan-script-trace collection-scan-graph-effects-p
                             collection-scan-script-memory-effects-p)))
          ("Subgoal *1/1"
           :use ((:instance collection-scan-memory-effects-prepare-next-round)))
          ("Subgoal *1/2"
           :use ((:instance collection-empty-scan-memory-effects-give-cpu)
                 (:instance collection-scan-memory-effects-prepare-next-round)))))

(defthm collection-checked-scan-reaches-finish-with-observed-memory
  (let* ((trace (collection-scan-script-trace bodies work origin))
         (final (collection-trace-effect trace world)))
    (implies (and (collection-scan-control-p work origin world)
                  (collection-scan-script-input-p bodies work origin world)
                  (collection-scan-memory-p graph original objects world work)
                  (collection-scan-script-memory-effects-p bodies work origin graph original objects world))
             (and (proof-segment-p (len trace) (list (+ origin (collection-linux-offset "rt:collect-finish")))
                                   world :cut final)
                  (collection-scan-memory-p graph original objects final (collection-finish-scan work)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-checked-scan-script-reaches-finish)
                 (:instance collection-scan-script-preserves-memory-invariant))
           :in-theory (theory 'minimal-theory))))
