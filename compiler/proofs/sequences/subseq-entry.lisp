(in-package "BOYMOO-PROOFS")

(include-book "subseq-entry-view")
(include-book "subseq-end")
(include-book "call-segments")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-entry-view-prefix (before)
  (append *sequence-subseq-view-call* (sequence-subseq-view-path before)))

(defun sequence-subseq-entry-end-world (datum limit before)
  (sequence-execute (sequence-subseq-end-path datum limit) (sequence-subseq-view-return before)))

(defun sequence-subseq-entry-checked-p (datum limit image-base before)
  (let* ((first (proof-world-machine before))
         (returned (sequence-subseq-view-return before))
         (prefix (sequence-subseq-entry-view-prefix before))
         (suffix (sequence-subseq-end-path datum limit))
         (view-link (+ image-base *sequence-subseq-offset* 24))
         (target (+ image-base *sequence-subseq-end-ready-offset*))
         (tag (+ image-base *sequence-subseq-tag-length-offset*))
         (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before))))
    (and (sequence-subseq-stack-room-p before)
         (consp (boymoo-model::a64-registers first))
         (natp image-base)
         (equal (proof-world-pc before) (+ image-base *sequence-subseq-offset*))
         (unsigned-byte-p 64 view-link)
         (unsigned-byte-p 64 target)
         (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
         (sequence-instruction-path *sequence-subseq-view-call* (list (+ image-base *sequence-view-offset*)) before)
         (sequence-instruction-path (sequence-subseq-view-path before) (list view-link)
                                    (sequence-subseq-called-view before))
         (sequence-instruction-path prefix (list view-link) before)
         (sequence-instruction-path prefix (list target) before)
         (implies (and (null limit) (not (stringp datum)))
                  (and (unsigned-byte-p 64 (+ image-base *sequence-list-length-offset* 32))
                       (sequence-instruction-path
                        (sequence-list-length-path datum) (list tag)
                        (sequence-execute *sequence-subseq-list-end-call* returned))))
         (sequence-instruction-path suffix (list target) returned))))

(defthm sequence-subseq-entry-image-and-stack
  (implies (sequence-subseq-entry-checked-p datum limit image-base before)
           (and (natp image-base) (sequence-subseq-stack-room-p before)))
  :hints
  (("Goal"
    :in-theory (disable sequence-subseq-stack-room-p sequence-subseq-view-path
                        sequence-subseq-end-path sequence-subseq-entry-view-prefix
                        sequence-subseq-view-return sequence-subseq-called-view
                        sequence-execute sequence-instruction-path)))
  :rule-classes :forward-chaining)

(local
 (defthm sequence-subseq-entry-payload-address-is-nonzero
   (not (equal (+ 8 (proof-pointer-address word base)) 0))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))))

(defthm sequence-subseq-entry-to-effective-end
  (let* ((first (proof-world-machine before))
         (prefix (sequence-subseq-entry-view-prefix before))
         (suffix (sequence-subseq-end-path datum limit))
         (target (+ image-base *sequence-subseq-end-ready-offset*))
         (after (sequence-subseq-entry-end-world datum limit before))
         (last (proof-world-machine after)))
    (implies
     (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
          (sequence-subseq-entry-checked-p datum limit image-base before))
     (and (proof-segment-p (+ (len prefix) (len suffix)) (list target) before :cut after)
          (equal (proof-world-pc after) target)
          (not (proof-world-stop after))
          (consp (boymoo-model::a64-registers last))
          (proof-reg-value-p 5 datum after objects packages)
          (proof-reg-value-p 6 start after objects packages)
          (proof-reg-value-p 7 (sequence-end limit datum) after objects packages)
          (equal (proof-world-reg 21 after) (if (stringp datum) 1 0))
          (proof-register-frame-p 29 '(1 2 3 5 6 7 21) before after)
          (equal (boymoo-model::a64-sp last) (- (boymoo-model::a64-sp first) 32))
          (equal (boymoo-model::a64-memory last) (sequence-subseq-caller-save-memory before))
          (equal (cdr after) (cdr before)))))
  :hints
  (("Goal"
    :in-theory (disable proof-runtime-pre-p proof-heap-p proof-reg-value-p proof-segment-p proof-register-frame-p
                        proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                        proof-heap-base proof-pointer-address sequence-execute sequence-instruction-path
                        sequence-subseq-called-view sequence-subseq-view-return sequence-subseq-view-path
                        sequence-subseq-end-path sequence-list-length-path sequence-end
                        sequence-subseq-caller-save-memory acl2::binary-append sequence-execute-append)
    :use (sequence-subseq-view-ready
          (:instance sequence-subseq-end-ready (before (sequence-subseq-view-return before)))
          (:instance sequence-register-frame-with-more-clobbers (limit 29)
                     (old '(1 2 3 5 6 7)) (new '(1 2 3 5 6 7 21)) (after (sequence-subseq-view-return before)))
          (:instance sequence-register-frame-with-more-clobbers (limit 29)
                     (old '(2 3 7 21)) (new '(1 2 3 5 6 7 21))
                     (before (sequence-subseq-view-return before)) (after (sequence-subseq-entry-end-world datum limit before)))
          (:instance sequence-register-frame-transitive (limit 29) (clobbers '(1 2 3 5 6 7 21))
                     (middle (sequence-subseq-view-return before)) (after (sequence-subseq-entry-end-world datum limit before)))
          (:instance sequence-execute-append (world before)
                     (first *sequence-subseq-view-call*) (second (sequence-subseq-view-path before)))
          (:instance sequence-append-checked-instructions
                     (instructions (sequence-subseq-entry-view-prefix before))
                     (cuts (list (+ image-base *sequence-subseq-end-ready-offset*)))
                     (suffix (len (sequence-subseq-end-path datum limit))) (reason :cut)
                     (after (sequence-subseq-entry-end-world datum limit before))))
    :expand ((sequence-subseq-view-return before)
             (sequence-subseq-called-view before))))
  :rule-classes nil)
