(in-package "BOYMOO-PROOFS")

(include-book "copy-loops")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-instruction-path-without-cuts
  (implies (sequence-instruction-path instructions cuts before)
           (sequence-instruction-path instructions nil before))
  :hints (("Goal"
           :in-theory (enable sequence-instruction-path)
           :induct (sequence-instruction-path instructions cuts before)))
  :rule-classes nil)

(defthm sequence-segment-after-checked-prefix
  (let ((middle (sequence-execute instructions before)))
    (implies
     (and (sequence-instruction-path instructions cuts before)
          (natp fuel)
          (proof-segment-p fuel nil middle reason after))
     (proof-segment-p (+ (len instructions) fuel) nil before reason after)))
  :hints (("Goal"
           :use (sequence-instruction-path-without-cuts
                 (:instance sequence-run-of-instruction-path
                            (world before) (cuts nil)))
           :in-theory (disable sequence-run-of-instruction-path)))
  :rule-classes nil)

(defthm sequence-subseq-size-stop-with-handler
  (let* ((machine (proof-world-machine before))
         (limit (sequence-runtime-count (- (sequence-end end datum) start)))
         (size (sequence-result-size datum start end))
         (cuts (list (+ image-base *sequence-datum-size-offset*)))
         (path *sequence-subseq-size-check*)
         (at-handler (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 19 before) limit)
          (<= *proof-space-size* limit)
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-check-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-datum-size-offset*))
          (sequence-instruction-path path cuts before)
          (natp fuel)
          (proof-segment-p fuel nil at-handler (cons :exit 3) after)
          (proof-resource-observation-p after))
     (and (proof-resource-bound-p (if (stringp datum) :string-size :allocation-size)
                                  (if (stringp datum) size (* 16 size)) at-handler)
          (proof-segment-p (+ (len path) fuel) nil before (cons :exit 3) after))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-resource-bound-p proof-resource-observation-p
                        proof-world-reg sequence-result-size sequence-runtime-count sequence-end)
    :use
    (sequence-subseq-size-cutpoint
     (:instance sequence-segment-after-checked-prefix
                (instructions *sequence-subseq-size-check*)
                (cuts (list (+ image-base *sequence-datum-size-offset*)))
                (reason (cons :exit 3))))))
  :rule-classes nil)
