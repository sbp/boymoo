(in-package "BOYMOO-PROOFS")

(include-book "subseq-entry")
(include-book "subseq-immediate-frame")
(include-book "datum-stop")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-immediate-size-prefix (datum limit before)
  (append (sequence-subseq-entry-view-prefix before)
          (sequence-subseq-end-path datum limit)
          *sequence-subseq-immediate-counts*
          *sequence-subseq-size-check*))

(local
 (defthm sequence-subseq-immediate-size-prefix-execution
   (let* ((ready (sequence-subseq-entry-end-world datum limit before))
          (counted (sequence-execute *sequence-subseq-immediate-counts* ready)))
     (equal (sequence-execute (sequence-subseq-immediate-size-prefix datum limit before) before)
            (sequence-execute *sequence-subseq-size-check* counted)))
   :hints
   (("Goal"
     :in-theory (disable acl2::binary-append sequence-execute sequence-execute-append
                         sequence-subseq-end-path sequence-subseq-view-path)
     :use ((:instance sequence-execute-append (world before)
                      (first (sequence-subseq-entry-view-prefix before))
                      (second (append (sequence-subseq-end-path datum limit)
                                      *sequence-subseq-immediate-counts* *sequence-subseq-size-check*)))
           (:instance sequence-execute-append (world before)
                      (first *sequence-subseq-view-call*) (second (sequence-subseq-view-path before)))
           (:instance sequence-execute-append (world (sequence-subseq-view-return before))
                      (first (sequence-subseq-end-path datum limit))
                      (second (append *sequence-subseq-immediate-counts* *sequence-subseq-size-check*)))
           (:instance sequence-execute-append (world (sequence-subseq-entry-end-world datum limit before))
                      (first *sequence-subseq-immediate-counts*) (second *sequence-subseq-size-check*)))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-size-check-keeps-output
   (let ((after (sequence-execute *sequence-subseq-size-check* before)))
     (implies (consp (boymoo-model::a64-registers (proof-world-machine before)))
              (and (consp (boymoo-model::a64-registers (proof-world-machine after)))
                   (equal (cdr after) (cdr before)))))
   :hints (("Goal" :in-theory (e/d (sequence-execute proof-world-machine)
                                    (proof-instruction-effect sequence-signed-word))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-tail-has-same-stdout
   (implies (equal (cdr before) (cdr after))
            (equal (proof-world-stdout before) (proof-world-stdout after)))
   :hints (("Goal" :in-theory (enable proof-world-stdout)))
   :rule-classes nil))

(defthm sequence-subseq-immediate-reaches-oversized-result
  (let* ((ready (sequence-subseq-entry-end-world datum limit before))
         (prefix (sequence-subseq-immediate-size-prefix datum limit before))
         (at-size (sequence-execute prefix before))
         (checked (+ image-base *sequence-subseq-checked-offset*))
         (target (+ image-base *sequence-datum-size-offset*))
         (size (sequence-result-size datum start limit)))
    (implies
     (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
          (sequence-subseq-entry-checked-p datum limit image-base before)
          (proof-immediate-integer-p start)
          (proof-immediate-integer-p (sequence-end limit datum))
          (<= *proof-space-size* size)
          (unsigned-byte-p 64 checked) (unsigned-byte-p 64 target)
          (sequence-instruction-path *sequence-subseq-immediate-counts* (list checked) ready))
     (and (equal (proof-world-pc at-size) target)
          (not (proof-world-stop at-size))
          (consp (boymoo-model::a64-registers (proof-world-machine at-size)))
          (equal (proof-world-stdout at-size) (proof-world-stdout before))
          (proof-resource-bound-p (if (stringp datum) :string-size :allocation-size)
                                  (if (stringp datum) size (* 16 size)) at-size))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (proof-resource-bound-p)
                    (proof-runtime-pre-p proof-world-stop proof-world-machine proof-world-stdout proof-world-reg
                     proof-world-pc proof-segment-p proof-reg-value-p proof-heap-base proof-register-frame-p
                     sequence-execute sequence-instruction-path sequence-result-size sequence-end
                     sequence-subseq-immediate-size-prefix sequence-subseq-entry-end-world
                     sequence-subseq-entry-checked-p proof-immediate-integer-p sequence-runtime-count
                     sequence-subseq-entry-view-prefix sequence-subseq-end-path sequence-subseq-view-path
                     sequence-subseq-end-prefix sequence-string-view-path acl2::binary-append))
    :use (sequence-subseq-entry-to-effective-end sequence-subseq-immediate-size-prefix-execution
          (:instance sequence-subseq-counts-from-represented-immediates
                     (before (sequence-subseq-entry-end-world datum limit before)))
          (:instance sequence-subseq-size-branch
                     (before (sequence-execute *sequence-subseq-immediate-counts*
                                               (sequence-subseq-entry-end-world datum limit before))))
          (:instance sequence-subseq-size-check-keeps-output
                     (before (sequence-execute *sequence-subseq-immediate-counts*
                                               (sequence-subseq-entry-end-world datum limit before))))
          (:instance sequence-subseq-tail-has-same-stdout
                     (after (sequence-execute (sequence-subseq-immediate-size-prefix datum limit before) before))))))
  :rule-classes nil)

(defthm sequence-subseq-immediate-size-exhaustion
  (let* ((ready (sequence-subseq-entry-end-world datum limit before))
         (checked (+ image-base *sequence-subseq-checked-offset*))
         (prefix (sequence-subseq-immediate-size-prefix datum limit before))
         (at-size (sequence-execute prefix before))
         (first (sequence-execute *sequence-datum-diagnostic-call* at-size))
         (second (sequence-execute *sequence-datum-newline-call* printed))
         (after (sequence-execute *sequence-datum-exit-path* ended))
         (size (sequence-result-size datum start limit))
         (fuel (sequence-datum-handler-step-count at-size printed first-fuel second-fuel)))
    (implies
     (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
          (sequence-subseq-entry-checked-p datum limit image-base before)
          (proof-immediate-integer-p start)
          (proof-immediate-integer-p (sequence-end limit datum))
          (<= *proof-space-size* size)
          (unsigned-byte-p 64 checked)
          (unsigned-byte-p 64 (+ image-base *sequence-datum-size-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*))
          (null (proof-world-stdout before))
          (sequence-instruction-path *sequence-subseq-immediate-counts* (list checked) ready)
          (sequence-instruction-path prefix nil before)
          (sequence-instruction-path *sequence-datum-diagnostic-call* nil at-size)
          (sequence-diagnostic-write-return-p first-fuel first printed)
          (sequence-instruction-path *sequence-datum-newline-call* nil printed)
          (sequence-diagnostic-write-return-p second-fuel second ended)
          (sequence-instruction-path *sequence-datum-exit-path* nil ended))
     (and (proof-resource-bound-p (if (stringp datum) :string-size :allocation-size)
                                  (if (stringp datum) size (* 16 size)) at-size)
          (proof-resource-observation-p after)
          (proof-segment-p (+ (len prefix) fuel) nil before (cons :exit 3) after))))
  :hints
  (("Goal"
    :in-theory (disable proof-runtime-pre-p proof-segment-p proof-resource-bound-p proof-resource-observation-p
                        proof-world-stop proof-world-machine proof-world-stdout proof-world-pc
                        sequence-subseq-entry-checked-p sequence-execute sequence-instruction-path
                        sequence-result-size sequence-end sequence-subseq-immediate-size-prefix
                        sequence-subseq-entry-end-world sequence-datum-handler-step-count
                        sequence-diagnostic-write-return-p)
    :use (sequence-subseq-immediate-reaches-oversized-result
          (:instance sequence-datum-size-handler-completes
                     (before (sequence-execute (sequence-subseq-immediate-size-prefix datum limit before) before)))
          (:instance sequence-append-checked-instructions
                     (instructions (sequence-subseq-immediate-size-prefix datum limit before))
                     (cuts nil) (reason (cons :exit 3))
                     (suffix (sequence-datum-handler-step-count
                              (sequence-execute (sequence-subseq-immediate-size-prefix datum limit before) before)
                              printed first-fuel second-fuel))
                     (after (sequence-execute *sequence-datum-exit-path* ended))))))
  :rule-classes nil)
