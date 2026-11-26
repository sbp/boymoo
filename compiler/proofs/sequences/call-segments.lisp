(in-package "BOYMOO-PROOFS")

(include-book "execution")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-segment-count (fuel cuts before)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (proof-world-stop before)
          (member-equal (proof-world-pc before) cuts))
      0
    (1+ (sequence-segment-count (1- fuel) cuts (proof-step before)))))

(defthm sequence-segment-count-is-natural
  (natp (sequence-segment-count fuel cuts before))
  :rule-classes :type-prescription)

(defthm sequence-callee-run-to-prefix
  (implies (and (proof-segment-p fuel (cons link cuts) before :cut middle)
                (not (proof-world-stop middle))
                (not (member-equal (proof-world-pc middle) cuts)))
           (equal (proof-run (sequence-segment-count fuel (cons link cuts) before) cuts before)
                  (mv :limit middle)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-run sequence-segment-count)
                    (proof-step proof-world-stop proof-world-pc))
    :induct (sequence-segment-count fuel (cons link cuts) before)))
  :rule-classes nil)

(defthm sequence-append-returning-call
  (implies (and (natp suffix)
                (proof-segment-p fuel (cons link cuts) before :cut middle)
                (not (proof-world-stop middle))
                (not (member-equal (proof-world-pc middle) cuts))
                (proof-segment-p suffix cuts middle reason after))
           (proof-segment-p (+ (sequence-segment-count fuel (cons link cuts) before) suffix)
                            cuts before reason after))
  :hints
  (("Goal"
    :in-theory (disable sequence-segment-count proof-step proof-run proof-world-pc)
    :use (sequence-callee-run-to-prefix
          (:instance sequence-run-append-at-noncut
                     (prefix (sequence-segment-count fuel (cons link cuts) before))))))
  :rule-classes nil)

(defthm sequence-append-checked-instructions
  (implies (and (natp suffix)
                (sequence-instruction-path instructions cuts before)
                (proof-segment-p suffix cuts (sequence-execute instructions before) reason after))
           (proof-segment-p (+ (len instructions) suffix) cuts before reason after))
  :hints (("Goal"
           :in-theory (disable sequence-run-of-instruction-path)
           :use ((:instance sequence-run-of-instruction-path (fuel suffix) (world before)))))
  :rule-classes nil)

(defthm sequence-stop-segment-of-instruction-path
  (let ((after (sequence-execute instructions before)))
    (implies (and (sequence-instruction-path instructions cuts before)
                  (proof-world-stop after))
             (proof-segment-p (len instructions) cuts before (proof-world-stop after) after)))
  :hints
  (("Goal"
    :in-theory (enable proof-run)
    :use ((:instance sequence-run-of-instruction-path (fuel 0) (world before)))))
  :rule-classes nil)
