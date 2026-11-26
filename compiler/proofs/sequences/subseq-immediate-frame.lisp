(in-package "BOYMOO-PROOFS")

(include-book "subseq-counts")
(include-book "symbol-fields")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-subseq-immediate-instructions-frame
   (let* ((before-machine (proof-world-machine before))
          (after (sequence-execute *sequence-subseq-immediate-counts* before)))
     (implies (consp (boymoo-model::a64-registers before-machine))
              (and (consp (boymoo-model::a64-registers (proof-world-machine after)))
                   (equal (cdr after) (cdr before))
                   (proof-register-frame-p 29 '(0 6 7 19 20) before after))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-execute boymoo-model::a64-exec-logical)
                     (proof-instruction-effect
                      boymoo-model::a64-condition sequence-conditions-on-result-flags))
     :expand ((:free (limit clobbers first last)
                     (proof-register-frame-p limit clobbers first last)))))
   :rule-classes nil))

(local
 (defthm sequence-represented-immediate-subseq-count-words
   (let* ((start-word (proof-world-reg 6 before))
          (end-word (proof-world-reg 7 before)))
     (implies (and (proof-immediate-integer-p start) (proof-immediate-integer-p end)
                   (proof-reg-value-p 6 start before objects packages)
                   (proof-reg-value-p 7 end before objects packages))
              (and (equal start-word (proof-integer-word start))
                   (equal end-word (proof-integer-word end)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p proof-view)
                     (proof-view-step proof-world-machine proof-world-reg proof-heap-base
                      proof-integer-word proof-pointer-address))
     :use ((:instance sequence-immediate-value-has-canonical-word
                      (datum start) (word (proof-world-reg 6 before)) (base (proof-heap-base before))
                      (machine (proof-world-machine before))
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address (proof-world-reg 6 before)
                                                                            (proof-heap-base before))
                                                     objects))))))
           (:instance sequence-immediate-value-has-canonical-word
                      (datum end) (word (proof-world-reg 7 before)) (base (proof-heap-base before))
                      (machine (proof-world-machine before))
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address (proof-world-reg 7 before)
                                                                            (proof-heap-base before))
                                                     objects)))))))))
   :rule-classes nil))

(defthm sequence-subseq-counts-from-represented-immediates
  (let* ((machine (proof-world-machine before))
         (path *sequence-subseq-immediate-counts*)
         (target (+ image-base *sequence-subseq-checked-offset*))
         (after (sequence-execute path before))
         (last (proof-world-machine after))
         (end (sequence-end limit datum)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-end-ready-offset*))
          (unsigned-byte-p 64 target)
          (proof-immediate-integer-p start) (proof-immediate-integer-p end)
          (proof-reg-value-p 6 start before objects packages)
          (proof-reg-value-p 7 end before objects packages)
          (sequence-instruction-path path (list target) before))
     (and (proof-segment-p (len path) (list target) before :cut after)
          (equal (proof-world-pc after) target)
          (not (proof-world-stop after))
          (proof-register-frame-p 29 '(0 6 7 19 20) before after)
          (equal (proof-world-reg 19 after) (sequence-result-size datum start limit))
          (equal (proof-world-reg 20 after) (sequence-runtime-count start))
          (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
          (consp (boymoo-model::a64-registers last))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine)))))
  :hints
  (("Goal"
    :in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                        proof-reg-value-p proof-register-frame-p proof-integer-word proof-segment-p
                        sequence-result-size sequence-runtime-count sequence-count sequence-execute
                        sequence-end sequence-instruction-path)
    :use (sequence-subseq-immediate-instructions-frame sequence-subseq-immediate-count-segment
          (:instance sequence-represented-immediate-subseq-count-words (end (sequence-end limit datum)))
          (:instance sequence-subseq-immediate-count-effects (end (sequence-end limit datum))))))
  :rule-classes nil)
