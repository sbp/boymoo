(in-package "BOYMOO-PROOFS")

(include-book "machine")

(logic)
(set-verify-guards-eagerness 0)

; A prefix excludes the supplied cutpoints at every instruction that
; it executes. Its endpoint may be a cutpoint.
(defun collection-prefix-p (count cuts world)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (disable proof-step)))))
  (or (zp count)
      (and (not (proof-world-stop world))
           (not (member-equal (proof-world-pc world) cuts))
           (collection-prefix-p (1- count) cuts (proof-step world)))))

(local (in-theory (disable proof-world-stop proof-world-pc proof-step)))

(defthm collection-prefix-append
  (implies (and (natp first) (natp second))
           (equal (collection-prefix-p (+ first second) cuts world)
                  (and (collection-prefix-p first cuts world)
                       (collection-prefix-p second cuts (proof-advance first world)))))
  :hints (("Goal" :induct (proof-advance first world)
                  :in-theory (disable proof-advance-append))))

(defthm collection-run-after-prefix
  (implies (and (natp count) (natp fuel) (collection-prefix-p count cuts world))
           (equal (proof-run (+ count fuel) cuts world)
                  (proof-run fuel cuts (proof-advance count world))))
  :hints (("Goal" :induct (proof-advance count world))))

(defthm collection-prefix-ending-at-cut-is-segment
  (let ((after (proof-advance count before)))
    (implies (and (natp count)
                  (collection-prefix-p count cuts before)
                  (not (proof-world-stop after))
                  (member-equal (proof-world-pc after) cuts))
             (proof-segment-p count cuts before :cut after)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance collection-run-after-prefix
                                   (world before) (fuel 0)))
                  :in-theory (disable collection-run-after-prefix
                                      collection-prefix-p proof-advance)
                  :expand ((proof-run 0 cuts (proof-advance count before))))))

(local (in-theory (disable proof-instruction-at-p proof-instruction-access-p
                            proof-instruction-effect proof-run)))

(defthm collection-ready-trace-gives-prefix
  (implies (and (collection-trace-ready-p trace terminal world)
                (not (intersectp-equal (strip-cars trace) cuts)))
           (and (collection-prefix-p (len trace) cuts world)
                (equal (proof-advance (len trace) world)
                       (collection-trace-effect trace world))
                (not (proof-world-stop (collection-trace-effect trace world)))))
  :hints (("Goal" :induct (collection-trace-ready-p trace terminal world)
                  :in-theory (disable collection-prefix-append proof-advance-append))
          ("Subgoal *1/2"
           :use ((:instance proof-step-from-instruction (instruction (cdar trace)))))))

(defthm collection-trace-effect-of-append
  (equal (collection-trace-effect (append first second) world)
         (collection-trace-effect second (collection-trace-effect first world)))
  :hints (("Goal" :induct (collection-trace-effect first world))))

(defthm collection-ready-trace-of-append
  (implies (and (collection-trace-ready-p first first-cut world)
                (collection-trace-ready-p second cuts (collection-trace-effect first world))
                (not (intersectp-equal (strip-cars first) cuts)))
           (collection-trace-ready-p (append first second) cuts world))
  :hints (("Goal" :induct (collection-trace-ready-p first first-cut world)
                  :in-theory (disable collection-trace-effect-of-append))))
