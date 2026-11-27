(in-package "BOYMOO-PROOFS")

(include-book "subseq-start-call")
(include-book "root-storage")
(include-book "publication-memory")
(include-book "cell-memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-subseq-root-register-is-word
   (unsigned-byte-p 64 (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg)))
   :rule-classes nil))

(local
 (defthm sequence-root-push-keeps-live-world
   (implies (and (proof-heap-layout-p before) (equal (cdr after) (cdr before)))
            (not (proof-world-stop after)))
   :hints (("Goal"
            :in-theory (disable proof-world-stop)
            :expand ((proof-heap-layout-p before))
            :use sequence-world-tail-fields))
   :rule-classes nil))

(local
 (defthm sequence-value-stack-push-spans
   (let* ((top (proof-stack-top world))
          (lower (proof-stack-base world))
          (metadata (- (proof-heap-base world) 88)))
     (implies (and (proof-heap-layout-p world)
                   (posp top)
                   (unsigned-byte-p 64 (+ top 16))
                   (<= (+ top 16) (proof-stack-limit world)))
              (and (proof-span-p top 16)
                   (proof-span-p lower (- top lower))
                   (proof-span-p metadata 8)
                   (proof-disjoint-p metadata (+ metadata 8) top (+ top 16)))))
   :hints
   (("Goal"
     :in-theory (enable proof-span-p proof-disjoint-p)
     :expand ((proof-heap-layout-p world))
     :use (sequence-heap-layout-bounds)))
   :rule-classes nil))

(local
 (defthm sequence-subseq-push-keeps-stack-base
   (let* ((top (proof-stack-top before))
          (metadata (- (proof-heap-base before) 88)))
     (implies (and (proof-span-p metadata 8)
                   (proof-disjoint-p metadata (+ metadata 8) top (+ top 16))
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (sequence-machine-write-confined-p top (+ top 16)
                                                      (proof-world-machine before)
                                                      (proof-world-machine after)))
              (equal (proof-stack-base after) (proof-stack-base before))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-stack-base proof-runtime-word proof-load-word)
                     (proof-world-machine sequence-machine-write-confined-p))
     :use ((:instance sequence-load-outside-confined-write
                      (address (- (proof-heap-base before) 88))
                      (count 8) (start (proof-stack-top before)) (end (+ 16 (proof-stack-top before)))
                      (first (proof-world-machine before)) (last (proof-world-machine after))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-root-pair-views
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (base (proof-heap-base before))
          (top (proof-stack-top before))
          (source (proof-world-reg 5 before))
          (end (proof-world-reg 7 before)))
     (implies
      (and (proof-reg-value-p 5 datum before objects packages)
           (proof-reg-value-p 7 effective-end before objects packages)
           (equal (proof-heap-base after) base)
           (equal (proof-load-word top last) source)
           (equal (proof-load-word (+ top 8) last) end)
           (sequence-object-storage-agrees-p objects first last))
      (and (equal (proof-stack-views 2 top base objects packages last)
                  (list :slots (proof-value-view datum) (proof-value-view effective-end)))
           (proof-machine-value-p source datum after objects packages)
           (proof-machine-value-p end effective-end after objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p)
                     (proof-world-machine proof-world-reg proof-heap-base proof-view proof-load-word
                      proof-stack-views proof-stack-top sequence-object-storage-agrees-p))
     :expand ((:free (address) (proof-stack-views 2 address (proof-heap-base before)
                                               objects packages (proof-world-machine after)))
              (:free (address) (proof-stack-views 1 address (proof-heap-base before)
                                               objects packages (proof-world-machine after)))
              (:free (address) (proof-stack-views 0 address (proof-heap-base before)
                                               objects packages (proof-world-machine after))))
     :use ((:instance sequence-view-on-agreed-objects
                      (word (proof-world-reg 5 before)) (base (proof-heap-base before))
                      (first (proof-world-machine before)) (last (proof-world-machine after)))
           (:instance sequence-view-on-agreed-objects
                      (word (proof-world-reg 7 before)) (base (proof-heap-base before))
                      (first (proof-world-machine before)) (last (proof-world-machine after))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-root-push-memory-and-words
   (let* ((first (proof-world-machine before))
          (top (proof-stack-top before))
          (lower (proof-stack-base before))
          (after (sequence-execute *sequence-subseq-numeric-start-call* before))
          (last (proof-world-machine after)))
     (implies (and (proof-heap-layout-p before)
                   (consp (boymoo-model::a64-registers first))
                   (natp image-base) (posp top)
                   (equal (proof-world-pc before) (+ image-base *sequence-subseq-numeric-offset* 8))
                   (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 24))
                   (unsigned-byte-p 64 (+ top 16))
                   (<= (+ top 16) (proof-stack-limit before)))
              (and (equal (proof-heap-base after) (proof-heap-base before))
                   (equal (proof-stack-base after) lower)
                   (equal (proof-stack-top after) (+ top 16))
                   (equal (proof-load-word top last) (proof-world-reg 5 before))
                   (equal (proof-load-word (+ top 8) last) (proof-world-reg 7 before))
                   (proof-span-p lower (- top lower))
                   (sequence-machine-write-confined-p top (+ top 16) first last)
                   (sequence-machine-span-agrees-p lower top first last))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-load-word proof-disjoint-p sequence-write-cell)
                     (proof-world-machine proof-world-reg proof-world-pc proof-heap-base proof-heap-layout-p
                      proof-stack-base proof-stack-top sequence-execute sequence-machine-span-agrees-p
                      sequence-machine-write-confined-p sequence-cell-write-first-word sequence-cell-write-rest-word))
     :use (sequence-subseq-arithmetic-start-count-call
           (:instance sequence-subseq-root-register-is-word (world before) (register 5))
           (:instance sequence-subseq-root-register-is-word (world before) (register 7))
           (:instance sequence-value-stack-push-spans (world before))
           (:instance sequence-save-pair-confines-memory-write
                      (address (proof-stack-top before)) (saved (proof-world-reg 5 before))
                      (link (proof-world-reg 7 before)) (first (proof-world-machine before))
                      (last (proof-world-machine (sequence-execute *sequence-subseq-numeric-start-call* before))))
           (:instance sequence-subseq-push-keeps-stack-base
                      (after (sequence-execute *sequence-subseq-numeric-start-call* before)))
           (:instance sequence-agreement-outside-confined-write
                      (lower (proof-stack-base before)) (upper (proof-stack-top before))
                      (start (proof-stack-top before)) (end (+ 16 (proof-stack-top before)))
                      (first (proof-world-machine before))
                      (last (proof-world-machine (sequence-execute *sequence-subseq-numeric-start-call* before))))
           (:instance sequence-cell-write-first-word
                      (address (proof-stack-top before)) (first (proof-world-reg 5 before))
                      (rest (proof-world-reg 7 before)) (memory (boymoo-model::a64-memory (proof-world-machine before))))
           (:instance sequence-cell-write-rest-word
                      (address (proof-stack-top before)) (first (proof-world-reg 5 before))
                      (rest (proof-world-reg 7 before)) (memory (boymoo-model::a64-memory (proof-world-machine before)))))))
   :rule-classes nil))

(defthm sequence-subseq-numeric-pushes-represented-roots
  (let* ((first (proof-world-machine before))
         (top (proof-stack-top before))
         (next (+ top 16))
         (prefix (proof-stack-prefix top before objects packages))
         (path *sequence-subseq-numeric-start-call*)
         (after (sequence-execute path before))
         (last (proof-world-machine after))
         (cuts (list (+ image-base *sequence-subseq-count-offset*))))
    (implies
     (and (proof-heap-p before objects packages)
          (consp (boymoo-model::a64-registers first))
          (proof-reg-value-p 5 datum before objects packages)
          (proof-reg-value-p 7 effective-end before objects packages)
          (posp top)
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-numeric-offset* 8))
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 24))
          (unsigned-byte-p 64 next)
          (<= next (proof-stack-limit before))
          (proof-object-disjoint-p top next objects first)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-stack-top after) next)
          (proof-prefix-preserved-p top before after objects objects packages)
          (equal (proof-stack-prefix next after objects packages)
                 (cons :slots (append (cdr prefix)
                                      (list (proof-value-view datum) (proof-value-view effective-end)))))
          (proof-machine-value-p (proof-load-word top last) datum after objects packages)
          (proof-machine-value-p (proof-load-word (+ top 8) last) effective-end after objects packages))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-map-p proof-object-disjoint-p
                        proof-segment-p proof-prefix-preserved-p proof-stack-prefix proof-world-machine
                        proof-world-reg proof-world-pc proof-world-stop proof-heap-base proof-load-word
                        proof-stack-base proof-stack-top sequence-execute sequence-instruction-path
                        proof-stack-views sequence-object-storage-agrees-p)
    :use (sequence-subseq-root-push-memory-and-words sequence-subseq-arithmetic-start-count-call
          (:instance sequence-root-push-keeps-live-world
                     (after (sequence-execute *sequence-subseq-numeric-start-call* before)))
          (:instance sequence-subseq-root-pair-views
                     (after (sequence-execute *sequence-subseq-numeric-start-call* before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions *sequence-subseq-numeric-start-call*)
                     (cuts (list (+ image-base *sequence-subseq-count-offset*)))
                     (after (sequence-execute *sequence-subseq-numeric-start-call* before)))
          (:instance sequence-disjoint-reservation-preserves-object-storage
                     (pending objects) (seen nil) (base (proof-heap-base before))
                     (start (proof-stack-top before)) (end (+ 16 (proof-stack-top before)))
                     (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute *sequence-subseq-numeric-start-call* before))))
          (:instance sequence-pushed-root-views
                     (more 2) (after (sequence-execute *sequence-subseq-numeric-start-call* before))))
    :expand ((proof-heap-p before objects packages))))
  :rule-classes nil)
