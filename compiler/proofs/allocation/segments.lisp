(in-package "BOYMOO-PROOFS")

(include-book "execution")

(logic)
(set-verify-guards-eagerness 0)

; The prefix takes exactly the specified number of steps, with no stop
; or listed cut before its last state.
(defun allocation-prefix-p (count cuts before after)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (equal before after)
    (and (not (proof-world-stop before))
         (not (member-equal (proof-world-pc before) cuts))
         (allocation-prefix-p (1- count) cuts (proof-step before) after))))

(defthm allocation-path-end-of-append
  (equal (allocation-path-end (append first last) world)
         (allocation-path-end last (allocation-path-end first world)))
  :hints (("Goal" :induct (allocation-path-end first world))))

(defthm allocation-path-ready-of-append
  (implies (true-listp first)
           (equal (allocation-path-ready-p (append first last) cuts world)
                  (and (allocation-path-ready-p first cuts world)
                       (allocation-path-ready-p last cuts (allocation-path-end first world)))))
  :hints (("Goal" :induct (allocation-path-ready-p first cuts world))))

(defthm allocation-prefix-from-path
  (implies (allocation-path-ready-p path cuts before)
           (allocation-prefix-p (len path) cuts before
                                (allocation-path-end path before)))
  :hints (("Goal" :induct (allocation-path-ready-p path cuts before))))

(defthm allocation-run-after-prefix
  (implies (and (allocation-prefix-p count cuts before middle) (natp count))
           (equal (proof-run (+ count (nfix remaining)) cuts before)
                  (proof-run remaining cuts middle)))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-prefix-p count cuts before middle))))

(defthm allocation-segment-after-prefix
  (implies (and (natp count)
                (allocation-prefix-p count cuts before middle)
                (proof-segment-p remaining cuts middle reason after))
           (proof-segment-p (+ count (nfix remaining)) cuts before reason after))
  :rule-classes nil
  :hints (("Goal" :use allocation-run-after-prefix
           :in-theory (disable proof-run allocation-prefix-p))))

(defthm allocation-path-ready-without-cuts
  (implies (allocation-path-ready-p path cuts before)
           (allocation-path-ready-p path nil before))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-path-ready-p path cuts before))))

(defthm allocation-run-stop-reason
  (mv-let (reason world)
    (proof-run count cuts before)
    (implies (consp reason) (equal (proof-world-stop world) reason)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-run count cuts before))))

(defthm allocation-path-then-resource-exit
  (implies (and (allocation-path-ready-p path cuts before)
                (equal cut (allocation-path-end path before))
                (natp stop-steps)
                (proof-segment-p stop-steps nil cut '(:exit . 3) after)
                (null (proof-world-stdout after)))
           (and (proof-segment-p (+ (len path) stop-steps) nil before '(:exit . 3) after)
                (proof-resource-observation-p after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-path-ready-without-cuts
                 (:instance allocation-run-stop-reason (count stop-steps) (cuts nil) (before cut))
                 (:instance allocation-prefix-from-path (cuts nil))
                 (:instance allocation-segment-after-prefix
                  (count (len path)) (remaining stop-steps) (cuts nil) (middle cut) (reason '(:exit . 3))))
           :in-theory (disable allocation-prefix-p allocation-path-ready-p allocation-path-end
                               proof-advance proof-run))))

(defthm allocation-register-frame-transitive
  (implies (and (proof-register-frame-p register clobbers before middle)
                (proof-register-frame-p register clobbers middle after))
           (proof-register-frame-p register clobbers before after))
  :rule-classes nil
  :hints (("Goal" :induct (proof-register-frame-p register clobbers before middle)
           :in-theory (enable proof-register-frame-p))))

(defthm allocation-register-frame-member
  (implies (and (proof-register-frame-p upper clobbers before after)
                (natp register) (natp upper) (<= register upper)
                (not (member-equal register clobbers)))
           (equal (proof-world-reg register after) (proof-world-reg register before)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-register-frame-p upper clobbers before after)
           :in-theory (enable proof-register-frame-p))))

(defthm allocation-register-frame-under-more-clobbers
  (implies (and (subsetp-equal small large)
                (proof-register-frame-p register small before after))
           (proof-register-frame-p register large before after))
  :rule-classes nil
  :hints (("Goal" :induct (proof-register-frame-p register small before after)
           :in-theory (enable proof-register-frame-p))))
