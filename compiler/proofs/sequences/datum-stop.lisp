(in-package "BOYMOO-PROOFS")

(include-book "call-segments")
(include-book "resources")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-stop-offset* (sequence-offset "rt:stop"))
(defconst *sequence-write-all-offset* (sequence-offset "rt:write-all"))
(defconst *sequence-datum-message-offset* (sequence-offset "rt:datum-size-message"))
(defconst *sequence-newline-offset* (sequence-offset "rt:newline"))

(sequence-defpath *sequence-datum-diagnostic-call*
  ("rt:datum-size" 0 4) ("rt:stop" 0 3))

(sequence-defpath *sequence-datum-newline-call*
  ("rt:stop" 3 4))

(sequence-defpath *sequence-datum-exit-path*
  ("rt:stop" 7 2) ("sys:exit" 0 2))

(defthm sequence-datum-size-diagnostic-call
  (let ((after (sequence-execute *sequence-datum-diagnostic-call* before)))
    (implies
     (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-datum-size-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-write-all-offset*))
          (equal (proof-world-reg 30 after) (+ image-base *sequence-stop-offset* 12))
          (equal (proof-world-reg 0 after) 2)
          (equal (proof-world-reg 1 after) (+ image-base *sequence-datum-message-offset*))
          (equal (proof-world-reg 2 after) (length "memory exhausted: a datum is too large"))
          (equal (proof-world-reg 22 after) 3)
          (equal (proof-world-stdout after) (proof-world-stdout before)))))
  :hints (("Goal" :in-theory (enable sequence-execute)))
  :rule-classes nil)

(defthm sequence-datum-size-newline-call
  (let ((after (sequence-execute *sequence-datum-newline-call* before)))
    (implies
     (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-stop-offset* 12))
          (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-write-all-offset*))
          (equal (proof-world-reg 30 after) (+ image-base *sequence-stop-offset* 28))
          (equal (proof-world-reg 0 after) 2)
          (equal (proof-world-reg 1 after) (+ image-base *sequence-newline-offset*))
          (equal (proof-world-reg 2 after) 1)
          (equal (proof-world-reg 22 after) (proof-world-reg 22 before))
          (equal (proof-world-stdout after) (proof-world-stdout before)))))
  :hints (("Goal" :in-theory (enable sequence-execute)))
  :rule-classes nil)

(defthm sequence-datum-size-exit-effects
  (let ((after (sequence-execute *sequence-datum-exit-path* before)))
    (implies (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
                  (equal (proof-world-reg 22 before) 3))
             (and (proof-exit-status-p 3 after)
                  (equal (proof-world-stdout after) (proof-world-stdout before))
                  (equal (proof-world-replies after) (proof-world-replies before)))))
  :hints (("Goal" :in-theory (enable sequence-execute proof-instruction-effect)))
  :rule-classes nil)

(defun sequence-diagnostic-write-return-p (fuel before after)
  (and (proof-segment-p fuel (list (proof-world-reg 30 before)) before :cut after)
       (proof-frame-return-p *proof-volatile-registers* t before after)
       (equal (proof-world-stdout after) (proof-world-stdout before))
       (consp (boymoo-model::a64-registers (proof-world-machine after)))))

(defun sequence-diagnostic-call-count (instructions fuel before)
  (let ((called (sequence-execute instructions before)))
    (+ (len instructions)
       (sequence-segment-count fuel (list (proof-world-reg 30 called)) called))))

(defun sequence-datum-handler-step-count (before printed first-fuel second-fuel)
  (+ (sequence-diagnostic-call-count *sequence-datum-diagnostic-call* first-fuel before)
     (sequence-diagnostic-call-count *sequence-datum-newline-call* second-fuel printed)
     (len *sequence-datum-exit-path*)))

(local
 (defthm sequence-diagnostic-call-count-is-natural
   (natp (sequence-diagnostic-call-count instructions fuel before))
   :rule-classes :type-prescription))

(local
 (defthm sequence-append-diagnostic-call
   (let ((called (sequence-execute instructions before)))
     (implies (and (sequence-instruction-path instructions nil before)
                   (sequence-diagnostic-write-return-p fuel called returned)
                   (natp suffix)
                   (proof-segment-p suffix nil returned reason after))
              (proof-segment-p (+ (sequence-diagnostic-call-count instructions fuel before) suffix)
                               nil before reason after)))
   :hints
   (("Goal"
     :in-theory (disable proof-register-frame-p proof-segment-p sequence-segment-count
                         proof-world-stdout proof-world-pc proof-world-stop proof-world-reg)
     :use ((:instance sequence-append-returning-call
                      (cuts nil) (link (proof-world-reg 30 (sequence-execute instructions before)))
                      (before (sequence-execute instructions before)) (middle returned))
           (:instance sequence-append-checked-instructions
                      (cuts nil)
                      (suffix (+ (sequence-segment-count fuel
                                                         (list (proof-world-reg 30 (sequence-execute instructions before)))
                                                         (sequence-execute instructions before))
                                 suffix))))))
   :rule-classes nil))

(local
 (defthm sequence-diagnostic-preserves-status
   (implies (sequence-diagnostic-write-return-p fuel before after)
            (equal (proof-world-reg 22 after) (proof-world-reg 22 before)))
   :hints (("Goal" :in-theory (disable proof-register-frame-p)
                   :use ((:instance sequence-register-in-frame
                                    (limit 30) (clobbers *proof-volatile-registers*) (register 22)))))
   :rule-classes nil))

(local
 (defthm sequence-first-diagnostic-returns-status
   (let ((called (sequence-execute *sequence-datum-diagnostic-call* before)))
     (implies (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
                   (natp image-base)
                   (equal (proof-world-pc before) (+ image-base *sequence-datum-size-offset*))
                   (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*))
                   (sequence-diagnostic-write-return-p fuel called printed))
              (and (equal (proof-world-pc printed) (+ image-base *sequence-stop-offset* 12))
                   (consp (boymoo-model::a64-registers (proof-world-machine printed)))
                   (equal (proof-world-reg 22 printed) 3)
                   (equal (proof-world-stdout printed) (proof-world-stdout before)))))
   :hints
   (("Goal"
     :in-theory (disable proof-register-frame-p proof-world-stdout proof-segment-p)
     :use (sequence-datum-size-diagnostic-call
           (:instance sequence-diagnostic-preserves-status
                      (before (sequence-execute *sequence-datum-diagnostic-call* before))
                      (after printed)))))
   :rule-classes nil))

(local
 (defthm sequence-second-diagnostic-returns-status
   (let ((called (sequence-execute *sequence-datum-newline-call* printed)))
     (implies (and (consp (boymoo-model::a64-registers (proof-world-machine printed)))
                   (natp image-base)
                   (equal (proof-world-pc printed) (+ image-base *sequence-stop-offset* 12))
                   (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*))
                   (sequence-diagnostic-write-return-p fuel called ended))
              (and (equal (proof-world-pc ended) (+ image-base *sequence-stop-offset* 28))
                   (consp (boymoo-model::a64-registers (proof-world-machine ended)))
                   (equal (proof-world-reg 22 ended) (proof-world-reg 22 printed))
                   (equal (proof-world-stdout ended) (proof-world-stdout printed)))))
   :hints
   (("Goal"
     :in-theory (disable proof-register-frame-p proof-world-stdout proof-segment-p)
     :use ((:instance sequence-datum-size-newline-call (before printed))
           (:instance sequence-diagnostic-preserves-status
                      (before (sequence-execute *sequence-datum-newline-call* printed))
                      (after ended)))))
   :rule-classes nil))

(defthm sequence-datum-size-handler-completes
  (let* ((first (sequence-execute *sequence-datum-diagnostic-call* before))
         (second (sequence-execute *sequence-datum-newline-call* printed))
         (after (sequence-execute *sequence-datum-exit-path* ended)))
    (implies
     (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-datum-size-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*))
          (null (proof-world-stdout before))
          (sequence-instruction-path *sequence-datum-diagnostic-call* nil before)
          (sequence-diagnostic-write-return-p first-fuel first printed)
          (sequence-instruction-path *sequence-datum-newline-call* nil printed)
          (sequence-diagnostic-write-return-p second-fuel second ended)
          (sequence-instruction-path *sequence-datum-exit-path* nil ended))
     (and (proof-resource-observation-p after)
          (proof-segment-p (sequence-datum-handler-step-count before printed first-fuel second-fuel)
                           nil before (cons :exit 3) after))))
  :hints
  (("Goal"
    :in-theory (disable proof-register-frame-p proof-segment-p sequence-segment-count
                        sequence-diagnostic-call-count sequence-diagnostic-write-return-p
                        proof-world-stdout proof-world-stop proof-world-reg proof-world-pc)
    :use ((:instance sequence-first-diagnostic-returns-status (fuel first-fuel))
          (:instance sequence-second-diagnostic-returns-status (fuel second-fuel))
          (:instance sequence-datum-size-exit-effects (before ended))
          (:instance sequence-stop-segment-of-instruction-path
                     (instructions *sequence-datum-exit-path*) (cuts nil) (before ended))
          (:instance sequence-append-diagnostic-call
                     (instructions *sequence-datum-newline-call*)
                     (fuel second-fuel) (suffix (len *sequence-datum-exit-path*))
                     (before printed) (returned ended) (reason (cons :exit 3))
                     (after (sequence-execute *sequence-datum-exit-path* ended)))
          (:instance sequence-append-diagnostic-call
                     (instructions *sequence-datum-diagnostic-call*) (fuel first-fuel)
                     (suffix (+ (sequence-diagnostic-call-count *sequence-datum-newline-call*
                                                                second-fuel printed)
                                (len *sequence-datum-exit-path*)))
                     (returned printed) (reason (cons :exit 3))
                     (after (sequence-execute *sequence-datum-exit-path* ended))))))
  :rule-classes nil)

(local
 (defthm sequence-subseq-size-check-keeps-diagnostic-state
   (let ((after (sequence-execute *sequence-subseq-size-check* before)))
     (implies (consp (boymoo-model::a64-registers (proof-world-machine before)))
              (and (consp (boymoo-model::a64-registers (proof-world-machine after)))
                   (equal (proof-world-stdout after) (proof-world-stdout before)))))
   :hints (("Goal" :in-theory (enable sequence-execute)))
   :rule-classes nil))

(defthm sequence-oversized-subseq-exits
  (let* ((count (sequence-runtime-count (- (sequence-end end datum) start)))
         (size (sequence-result-size datum start end))
         (path *sequence-subseq-size-check*)
         (handler (sequence-execute path before))
         (first (sequence-execute *sequence-datum-diagnostic-call* handler))
         (second (sequence-execute *sequence-datum-newline-call* printed))
         (after (sequence-execute *sequence-datum-exit-path* ended))
         (handler-fuel (sequence-datum-handler-step-count handler printed first-fuel second-fuel)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (equal (proof-world-reg 19 before) count) (<= *proof-space-size* count)
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-check-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-datum-size-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-newline-offset*))
          (null (proof-world-stdout before))
          (sequence-instruction-path path (list (+ image-base *sequence-datum-size-offset*)) before)
          (sequence-instruction-path *sequence-datum-diagnostic-call* nil handler)
          (sequence-diagnostic-write-return-p first-fuel first printed)
          (sequence-instruction-path *sequence-datum-newline-call* nil printed)
          (sequence-diagnostic-write-return-p second-fuel second ended)
          (sequence-instruction-path *sequence-datum-exit-path* nil ended))
     (and (proof-resource-bound-p (if (stringp datum) :string-size :allocation-size)
                                  (if (stringp datum) size (* 16 size)) handler)
          (proof-resource-observation-p after)
          (proof-segment-p (+ (len path) handler-fuel) nil before (cons :exit 3) after))))
  :hints
  (("Goal"
    :in-theory (disable sequence-execute sequence-segment-count sequence-instruction-path
                        proof-segment-p proof-resource-observation-p proof-resource-bound-p
                        proof-world-stop proof-world-pc proof-world-reg proof-world-stdout
                        proof-world-machine sequence-diagnostic-write-return-p
                        sequence-end sequence-result-size sequence-runtime-count)
    :use (sequence-subseq-size-branch sequence-subseq-size-check-keeps-diagnostic-state
          (:instance sequence-datum-size-handler-completes
                     (before (sequence-execute *sequence-subseq-size-check* before)))
          (:instance sequence-subseq-size-stop-with-handler
                     (fuel (sequence-datum-handler-step-count
                            (sequence-execute *sequence-subseq-size-check* before)
                            printed first-fuel second-fuel))
                     (after (sequence-execute *sequence-datum-exit-path* ended))))))
  :rule-classes nil)
