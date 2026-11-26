(in-package "BOYMOO-PROOFS")

(include-book "scan-transition")
(include-book "source-markers")

(logic)
(set-verify-guards-eagerness 0)

; A header's type and rounded payload length come from the original
; object. The copy keeps its header through all scan rounds.
(defun collection-copy-field-offset (kind)
  (if (eq kind :cons) 0 8))

(defun collection-copy-field-count (kind header)
  (if (eq kind :cons) 2 (collection-header-payload-words header)))

(defun collection-copy-is-raw-p (kind header)
  (and (eq kind :header) (member-equal (proof-header-type header) '(1 3))))

(defun collection-copy-payload-observed-p (source kind base objects original current work)
  (let* ((entry (assoc-equal source (collection-forwarding work)))
         (copy (cdr entry))
         (header (collection-read-word source original))
         (offset (collection-copy-field-offset kind))
         (count (collection-copy-field-count kind header)))
    (or (not entry)
        (and (implies (eq kind :header)
                      (equal (collection-read-word copy current) header))
             (if (or (collection-copy-is-raw-p kind header)
                     (collection-source-pending-p source work))
                 (equal (collection-slot-words count (+ copy offset) current)
                        (collection-slot-words count (+ source offset) original))
               (collection-scanned-fields-p count (+ source offset) (+ copy offset)
                                            base objects original current work))))))

(defun collection-graph-bytes-observed-p (graph base objects original current work)
  (if (endp graph)
      t
    (let ((source (caar graph)) (kind (cadar graph)))
      (and (if (eq kind :external)
               (collection-external-mark-p source work current)
             (and (collection-source-marker-p source kind base work original current)
                  (collection-copy-payload-observed-p source kind base objects original current work)))
           (collection-graph-bytes-observed-p (cdr graph) base objects original current work)))))

; At the selection label both the dynamic root and the initialized
; stack are committed. Each source and its destination observation
; concern the same forwarding map and pending queues.
(defun collection-scan-memory-p (graph original objects current work)
  (let* ((base (proof-heap-base original))
         (bottom (proof-stack-base original))
         (count (ash (- (proof-stack-top original) bottom) -3)))
    (and (collection-scanned-fields-p 1 (+ base 24) (+ base 24)
                                      base objects original current work)
         (collection-scanned-fields-p count bottom bottom base objects original current work)
         (collection-graph-bytes-observed-p graph base objects original current work))))

(local
 (in-theory (disable collection-source-pending-p collection-selected-record
                     collection-forwarding collection-unseen collection-scan-one
                     collection-forwarding-agrees-p collection-scanned-fields-p
                     collection-slot-words collection-read-word proof-load-word proof-world-machine
                     collection-header-payload-words collection-copy-is-raw-p
                     collection-copy-field-offset collection-copy-field-count
                     collection-source-marker-p collection-external-mark-p
                     proof-heap-base proof-stack-base proof-stack-top
                     boymoo-model::a64-unsigned (:definition ash))))

(local
 (defthm collection-unselected-assigned-source-keeps-queue-status
   (implies (and (not (assoc-equal source (collection-unseen work)))
                 (not (equal source (car (collection-selected-record work)))))
            (iff (collection-source-pending-p source (collection-scan-one work))
                 (collection-source-pending-p source work)))
   :hints (("Goal"
            :use ((:instance collection-scan-keeps-unselected-source-pending (query source))
                  (:instance collection-scan-cannot-requeue-a-committed-source (query source)))))))

(defthm collection-unselected-copy-observation-survives-scan
  (let* ((entry (assoc-equal source (collection-forwarding work)))
         (copy (cdr entry))
         (header (collection-read-word source original))
         (offset (collection-copy-field-offset kind))
         (count (collection-copy-field-count kind header)))
    (implies (and entry (collection-forwarding-agrees-p source entry work)
                  (not (equal source (car (collection-selected-record work))))
                  (collection-copy-payload-observed-p source kind base objects original before work)
                  (implies (eq kind :header)
                           (equal (collection-read-word copy after) (collection-read-word copy before)))
                  (equal (collection-slot-words count (+ copy offset) after)
                         (collection-slot-words count (+ copy offset) before)))
             (collection-copy-payload-observed-p source kind base objects original after
                                                 (collection-scan-one work))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-unselected-assigned-source-keeps-queue-status)
                 (:instance collection-scan-assignment-agrees-after-scan-one
                            (address source) (entry (assoc-equal source (collection-forwarding work))))
                 (:instance collection-later-scan-preserves-committed-fields
                            (count (collection-copy-field-count kind (collection-read-word source original)))
                            (source (+ source (collection-copy-field-offset kind)))
                            (target (+ (cdr (assoc-equal source (collection-forwarding work)))
                                       (collection-copy-field-offset kind)))))
           :in-theory (e/d (collection-forwarding-agrees-p)
                            (collection-unselected-assigned-source-keeps-queue-status
                             collection-scan-assignment-agrees-after-scan-one)))))

(defthm collection-scan-round-keeps-committed-roots-on-unchanged-slots
  (let* ((base (proof-heap-base original))
         (bottom (proof-stack-base original))
         (count (ash (- (proof-stack-top original) bottom) -3)))
    (implies (and (collection-scan-memory-p graph original objects before work)
                  (equal (collection-slot-words 1 (+ base 24) after)
                         (collection-slot-words 1 (+ base 24) before))
                  (equal (collection-slot-words count bottom after)
                         (collection-slot-words count bottom before))
                  (collection-graph-bytes-observed-p graph base objects original after
                                                       (collection-scan-one work)))
             (collection-scan-memory-p graph original objects after (collection-scan-one work))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-later-scan-preserves-committed-fields
                            (count 1) (source (+ (proof-heap-base original) 24))
                            (target (+ (proof-heap-base original) 24)) (base (proof-heap-base original)))
                 (:instance collection-later-scan-preserves-committed-fields
                            (count (ash (- (proof-stack-top original) (proof-stack-base original)) -3))
                            (source (proof-stack-base original)) (target (proof-stack-base original))
                            (base (proof-heap-base original))))
           :in-theory (disable collection-graph-bytes-observed-p))))

; Only a new copy or the selected copy needs a new payload observation.
; The other copies need preservation of their header and payload words.
; A forwarder changes source words or a mark only at its own source.
(defun collection-scan-record-effects-p (record base objects original before after work)
  (let* ((source (car record))
         (kind (cadr record))
         (next (collection-scan-one work))
         (entry (assoc-equal source (collection-forwarding work)))
         (new-entry (assoc-equal source (collection-forwarding next)))
         (copy (cdr entry))
         (offset (collection-copy-field-offset kind))
         (count (collection-copy-field-count kind (collection-read-word source original)))
         (same-assignment (equal entry new-entry)))
    (if (eq kind :external)
        (if same-assignment
            (equal (collection-read-word (- source 8) after)
                   (collection-read-word (- source 8) before))
          (collection-external-mark-p source next after))
      (and (if same-assignment
               (and (equal (collection-read-word source after) (collection-read-word source before))
                    (implies (eq kind :cons)
                             (equal (collection-read-word (+ source 8) after)
                                    (collection-read-word (+ source 8) before))))
             (collection-source-marker-p source kind base next original after))
           (cond ((not new-entry) t)
                 ((and entry (collection-forwarding-agrees-p source entry work)
                       (not (equal source (car (collection-selected-record work)))))
                  (and (implies (eq kind :header)
                               (equal (collection-read-word copy after) (collection-read-word copy before)))
                       (equal (collection-slot-words count (+ copy offset) after)
                              (collection-slot-words count (+ copy offset) before))))
                 (t (collection-copy-payload-observed-p source kind base objects original after next)))))))

(defun collection-scan-graph-effects-p (graph base objects original before after work)
  (or (endp graph)
      (and (collection-scan-record-effects-p (car graph) base objects original before after work)
           (collection-scan-graph-effects-p (cdr graph) base objects original before after work))))

(local
 (defthm collection-unchanged-marker-keeps-source-observation
   (implies (and (collection-source-marker-p source kind base work original before)
                 (equal (assoc-equal source (collection-forwarding work))
                        (assoc-equal source (collection-forwarding next)))
                 (equal (collection-read-word source after) (collection-read-word source before))
                 (implies (eq kind :cons)
                          (equal (collection-read-word (+ source 8) after)
                                 (collection-read-word (+ source 8) before))))
            (collection-source-marker-p source kind base next original after))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable collection-source-marker-p)))))

(local
 (defthm collection-unchanged-mark-keeps-external-observation
   (implies (and (collection-external-mark-p source work before)
                 (equal (assoc-equal source (collection-forwarding work))
                        (assoc-equal source (collection-forwarding next)))
                 (equal (collection-read-word (- source 8) after)
                        (collection-read-word (- source 8) before)))
            (collection-external-mark-p source next after))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable collection-external-mark-p)))))

(local
 (defthm collection-source-without-assignment-needs-no-copy-observation
   (implies (not (assoc-equal source (collection-forwarding work)))
            (collection-copy-payload-observed-p source kind base objects original current work))))

(local
 (in-theory (disable collection-copy-payload-observed-p)))

(defthm collection-scan-round-preserves-graph-observations
  (implies (and (collection-graph-bytes-observed-p graph base objects original before work)
                (collection-scan-graph-effects-p graph base objects original before after work))
           (collection-graph-bytes-observed-p graph base objects original after (collection-scan-one work)))
  :rule-classes nil
  :hints (("Goal"
           :induct (len graph)
           :in-theory (disable collection-scan-record-effects-p))
          ("Subgoal *1/1"
           :use ((:instance collection-unchanged-marker-keeps-source-observation
                            (source (caar graph)) (kind (cadar graph)) (next (collection-scan-one work)))
                 (:instance collection-unchanged-mark-keeps-external-observation
                            (source (caar graph)) (next (collection-scan-one work)))
                 (:instance collection-unselected-copy-observation-survives-scan
                            (source (caar graph)) (kind (cadar graph))))
           :in-theory (enable collection-scan-record-effects-p))))

(defthm collection-scan-round-preserves-memory-invariant
  (let* ((base (proof-heap-base original))
         (bottom (proof-stack-base original))
         (count (ash (- (proof-stack-top original) bottom) -3)))
    (implies (and (collection-scan-memory-p graph original objects before work)
                  (equal (collection-slot-words 1 (+ base 24) after)
                         (collection-slot-words 1 (+ base 24) before))
                  (equal (collection-slot-words count bottom after)
                         (collection-slot-words count bottom before))
                  (collection-scan-graph-effects-p graph base objects original before after work))
             (collection-scan-memory-p graph original objects after (collection-scan-one work))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-scan-round-keeps-committed-roots-on-unchanged-slots)
                 (:instance collection-scan-round-preserves-graph-observations
                            (base (proof-heap-base original))))
           :in-theory (disable collection-graph-bytes-observed-p collection-scan-graph-effects-p))))
