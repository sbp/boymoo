(in-package "BOYMOO-PROOFS")

(include-book "subseq-entry")
(include-book "subseq-immediate-frame")
(include-book "subseq-empty-list")
(include-book "static-roots")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-subseq-empty-clobbers* '(0 1 2 3 5 6 7 19 20 21))

(defun sequence-subseq-empty-counted-p (entry before)
  (let ((machine (proof-world-machine before))
        (stack (boymoo-model::a64-sp (proof-world-machine entry))))
    (and (sequence-subseq-stack-room-p entry)
         (not (proof-world-stop entry))
         (not (proof-world-stop before))
         (consp (boymoo-model::a64-registers machine))
         (equal (proof-world-reg 19 before) 0)
         (equal (proof-world-reg 21 before) 0)
         (equal (boymoo-model::a64-sp machine) (- stack 32))
         (equal (boymoo-model::a64-memory machine) (sequence-subseq-caller-save-memory entry))
         (equal (cdr before) (cdr entry))
         (proof-register-frame-p 29 *sequence-subseq-empty-clobbers* entry before))))

(local
 (defthm sequence-subseq-caller-save-is-a-span
   (let ((stack (boymoo-model::a64-sp (proof-world-machine entry))))
     (implies (sequence-subseq-stack-room-p entry)
              (proof-span-p (- stack 32) 32)))
   :hints (("Goal" :in-theory (enable sequence-subseq-stack-room-p proof-span-p)))
   :rule-classes nil))

(local
 (defthm sequence-subseq-empty-restored-register-frame
   (implies (and (proof-register-frame-p 29 *sequence-subseq-empty-clobbers* before after)
                 (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                 (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                 (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
                 (equal (proof-world-reg 30 after) (proof-world-reg 30 before)))
            (and (proof-register-frame-p 30 (proof-runtime-clobbers 'subseq) before after)
                 (sequence-heap-registers-agree-p before after)))
   :hints
   (("Goal"
     :in-theory (enable sequence-heap-registers-agree-p
                        proof-heap-base proof-box-top proof-heap-limit proof-stack-top
                        proof-stack-limit proof-machine-limit)
     :expand ((:free (register clobbers first last)
                     (proof-register-frame-p register clobbers first last)))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-empty-return-restores-frame
   (let ((after (sequence-execute *sequence-subseq-empty-list-path* before))
         (stack (boymoo-model::a64-sp (proof-world-machine entry))))
     (implies
      (and (proof-heap-layout-p entry)
           (sequence-subseq-empty-counted-p entry before))
      (and (proof-frame-return-p (proof-runtime-clobbers 'subseq) t entry after)
           (sequence-stack-write-p (- stack 32) stack entry after)
           (equal (proof-world-reg 0 after) *proof-nil*))))
   :hints
   (("Goal"
    :do-not-induct t
    :in-theory (e/d (proof-frame-return-p)
                     (proof-register-frame-p sequence-stack-write-p
                      proof-load-word proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                      proof-heap-layout-p proof-span-p sequence-subseq-stack-room-p
                      sequence-subseq-caller-save-memory sequence-execute))
     :use (sequence-subseq-empty-list-return-effects
           (:instance sequence-sp-bits (machine (proof-world-machine entry)))
           sequence-subseq-caller-save-is-a-span
           (:instance sequence-subseq-saved-registers-read-back (before entry) (after before))
           (:instance sequence-register-frame-with-more-clobbers (limit 29)
                      (old '(0 1 19 20 21)) (new *sequence-subseq-empty-clobbers*)
                      (after (sequence-execute *sequence-subseq-empty-list-path* before)))
           (:instance sequence-register-frame-transitive (limit 29) (clobbers *sequence-subseq-empty-clobbers*)
                      (before entry) (middle before) (after (sequence-execute *sequence-subseq-empty-list-path* before)))
           (:instance sequence-subseq-empty-restored-register-frame (before entry)
                      (after (sequence-execute *sequence-subseq-empty-list-path* before)))
           (:instance sequence-subseq-retains-its-machine-stack-frame (before entry)
                      (after (sequence-execute *sequence-subseq-empty-list-path* before))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-empty-return-keeps-caller
   (let ((after (sequence-execute *sequence-subseq-empty-list-path* before)))
     (implies
      (and (proof-heap-p entry objects packages)
           (sequence-subseq-empty-counted-p entry before))
      (and (proof-frame-return-p (proof-runtime-clobbers 'subseq) t entry after)
           (proof-fixed-heap-p entry after objects)
           (proof-preserved-heap-p nil entry after objects objects packages)
           (proof-reg-value-p 0 nil after objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p)
                     (proof-frame-return-p proof-preserved-heap-p proof-machine-value-p proof-heap-p
                      proof-fixed-heap-p proof-world-machine proof-world-reg proof-heap-layout-p
                      sequence-stack-write-p sequence-subseq-empty-counted-p sequence-execute))
     :use (sequence-subseq-empty-return-restores-frame
           (:instance sequence-confined-stack-write-preserves-heap (before entry)
                      (after (sequence-execute *sequence-subseq-empty-list-path* before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine entry)) 32))
                      (end (boymoo-model::a64-sp (proof-world-machine entry))))
           (:instance sequence-static-truth-values-in-heap (world entry))
           (:instance sequence-confined-stack-write-preserves-value (before entry)
                      (after (sequence-execute *sequence-subseq-empty-list-path* before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine entry)) 32))
                      (end (boymoo-model::a64-sp (proof-world-machine entry)))
                      (word *proof-nil*) (datum nil)))))
   :rule-classes nil))

(defun sequence-subseq-empty-list-instruction-path (datum limit before)
  (append (sequence-subseq-entry-view-prefix before)
          (sequence-subseq-end-path datum limit)
          *sequence-subseq-immediate-counts*
          *sequence-subseq-empty-list-path*))

(local
 (defthm sequence-subseq-empty-list-instruction-order
   (let* ((ready (sequence-subseq-entry-end-world datum limit before))
          (counted (sequence-execute *sequence-subseq-immediate-counts* ready)))
     (equal (sequence-execute (sequence-subseq-empty-list-instruction-path datum limit before) before)
            (sequence-execute *sequence-subseq-empty-list-path* counted)))
   :hints
   (("Goal"
     :in-theory (disable acl2::binary-append sequence-execute sequence-execute-append
                         sequence-subseq-end-path sequence-subseq-view-path)
     :use ((:instance sequence-execute-append (world before)
                      (first (sequence-subseq-entry-view-prefix before))
                      (second (append (sequence-subseq-end-path datum limit)
                                      *sequence-subseq-immediate-counts* *sequence-subseq-empty-list-path*)))
           (:instance sequence-execute-append (world before)
                      (first *sequence-subseq-view-call*) (second (sequence-subseq-view-path before)))
           (:instance sequence-execute-append (world (sequence-subseq-view-return before))
                      (first (sequence-subseq-end-path datum limit))
                      (second (append *sequence-subseq-immediate-counts* *sequence-subseq-empty-list-path*)))
           (:instance sequence-execute-append (world (sequence-subseq-entry-end-world datum limit before))
                      (first *sequence-subseq-immediate-counts*) (second *sequence-subseq-empty-list-path*)))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-empty-entry-counts
   (let* ((ready (sequence-subseq-entry-end-world datum limit before))
          (size-check (+ image-base *sequence-subseq-checked-offset*))
          (counted (sequence-execute *sequence-subseq-immediate-counts* ready)))
     (implies (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
                   (sequence-subseq-entry-checked-p datum limit image-base before)
                   (not (proof-world-stop before))
                   (not (stringp datum))
                   (proof-immediate-integer-p start)
                   (proof-immediate-integer-p (sequence-end limit datum))
                   (equal (sequence-result-size datum start limit) 0)
                   (unsigned-byte-p 64 size-check)
                   (sequence-instruction-path *sequence-subseq-immediate-counts* (list size-check) ready))
              (sequence-subseq-empty-counted-p before counted)))
   :hints
   (("Goal"
     :in-theory (disable proof-runtime-pre-p proof-reg-value-p proof-register-frame-p proof-segment-p
                         proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                         proof-immediate-integer-p sequence-runtime-count sequence-subseq-entry-end-world
                         sequence-subseq-caller-save-memory sequence-end sequence-result-size sequence-execute
                         sequence-instruction-path sequence-subseq-entry-checked-p sequence-subseq-stack-room-p)
     :use (sequence-subseq-entry-to-effective-end
           (:instance sequence-subseq-counts-from-represented-immediates
                      (before (sequence-subseq-entry-end-world datum limit before)))
           (:instance sequence-register-frame-with-more-clobbers (limit 29)
                      (old '(1 2 3 5 6 7 21)) (new *sequence-subseq-empty-clobbers*)
                      (after (sequence-subseq-entry-end-world datum limit before)))
           (:instance sequence-register-frame-with-more-clobbers (limit 29)
                      (old '(0 6 7 19 20)) (new *sequence-subseq-empty-clobbers*)
                      (before (sequence-subseq-entry-end-world datum limit before))
                      (after (sequence-execute *sequence-subseq-immediate-counts*
                                               (sequence-subseq-entry-end-world datum limit before))))
           (:instance sequence-register-frame-transitive (limit 29) (clobbers *sequence-subseq-empty-clobbers*)
                      (middle (sequence-subseq-entry-end-world datum limit before))
                      (after (sequence-execute *sequence-subseq-immediate-counts*
                                               (sequence-subseq-entry-end-world datum limit before)))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-empty-entry-source-value
   (implies (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
                 (not (stringp datum))
                 (equal (sequence-result-size datum start limit) 0))
            (and (proof-heap-p before objects packages)
                 (not (proof-world-stop before))
                 (equal (proof-runtime-value 'subseq (list datum start limit) program)
                        (boymoo-model::core-value nil))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-runtime-pre-p proof-reg-value-p)
                     (proof-heap-p proof-runtime-value proof-machine-value-p proof-world-stop proof-world-reg
                      proof-world-machine proof-program-packages-p proof-label-address
                      sequence-result-size sequence-elements))
     :use (sequence-subseq-zero-list-size-source-result
           (:instance sequence-represented-sequence-length-bounded (world before) (word (proof-world-reg 0 before)))
           (:instance sequence-heap-layout-bounds (world before)))))
   :rule-classes nil))

(defthm sequence-subseq-empty-list-immediate-runtime-contract
  (let* ((ready (sequence-subseq-entry-end-world datum limit before))
         (path (sequence-subseq-empty-list-instruction-path datum limit before))
         (cuts (list (proof-world-reg 30 before)))
         (after (sequence-execute path before))
         (size-check (+ image-base *sequence-subseq-checked-offset*)))
    (implies
     (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
          (sequence-subseq-entry-checked-p datum limit image-base before)
          (not (stringp datum))
          (proof-immediate-integer-p start)
          (proof-immediate-integer-p (sequence-end limit datum))
          (equal (sequence-result-size datum start limit) 0)
          (unsigned-byte-p 64 size-check)
          (sequence-instruction-path *sequence-subseq-immediate-counts* (list size-check) ready)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-runtime-return-p 'subseq (list datum start limit) program before after objects objects packages)
          (proof-fixed-heap-p before after objects))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (proof-runtime-return-p proof-datum-return-p proof-frame-return-p)
                    (proof-runtime-pre-p proof-runtime-value proof-heap-p proof-fixed-heap-p proof-preserved-heap-p
                     proof-reg-value-p proof-register-frame-p proof-world-machine proof-world-reg proof-world-pc
                     proof-world-stop proof-immediate-integer-p proof-segment-p sequence-subseq-empty-counted-p
                     sequence-subseq-empty-list-instruction-path sequence-subseq-entry-end-world sequence-end
                     sequence-result-size sequence-execute sequence-instruction-path sequence-subseq-entry-checked-p))
    :use (sequence-subseq-empty-list-instruction-order sequence-subseq-empty-entry-counts
          sequence-subseq-empty-entry-source-value
          (:instance sequence-subseq-empty-return-keeps-caller (entry before)
                     (before (sequence-execute *sequence-subseq-immediate-counts*
                                               (sequence-subseq-entry-end-world datum limit before))))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-subseq-empty-list-instruction-path datum limit before))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute (sequence-subseq-empty-list-instruction-path datum limit before) before))))))
  :rule-classes nil)
