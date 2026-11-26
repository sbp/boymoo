(in-package "BOYMOO-PROOFS")

(include-book "subseq-view")
(include-book "canonical-symbols")
(include-book "spine-bounds")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-end-prefix (datum limit)
  (cond (limit *sequence-subseq-explicit-end*)
        ((stringp datum) *sequence-subseq-string-end*)
        (t (append *sequence-subseq-list-end-call* (sequence-list-length-path datum)))))

(defun sequence-subseq-end-path (datum limit)
  (if limit
      *sequence-subseq-explicit-end*
    (append (sequence-subseq-end-prefix datum nil) *sequence-subseq-tag-length*)))

(defun sequence-subseq-view-complete-p (datum image-base world)
  (and (not (proof-world-stop world))
       (consp (boymoo-model::a64-registers (proof-world-machine world)))
       (natp image-base)
       (equal (proof-world-pc world) (+ image-base *sequence-subseq-offset* 24))
       (unsigned-byte-p 64 (+ image-base *sequence-subseq-end-ready-offset*))
       (equal (equal (proof-world-reg 1 world) 0) (not (stringp datum)))
       (implies (stringp datum)
                (equal (proof-world-reg 2 world) (len (coerce datum 'list))))))

(local
 (defthm sequence-subseq-length-result-for-default-list-end
   (let* ((machine (proof-world-machine before))
          (called (sequence-execute *sequence-subseq-list-end-call* before))
          (path (sequence-list-length-path datum))
          (after (sequence-execute path called))
          (tag (+ image-base *sequence-subseq-tag-length-offset*)))
     (implies
      (and (not (stringp datum))
           (sequence-subseq-view-complete-p datum image-base before)
           (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (equal (proof-world-reg 7 before) *proof-nil*)
           (unsigned-byte-p 64 (+ image-base *sequence-list-length-offset* 32))
           (sequence-instruction-path path (list tag) called))
      (and (equal (proof-world-pc after) tag)
           (not (proof-world-stop after))
           (equal (proof-world-reg 2 after) (len datum))
           (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
           (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
           (equal (proof-world-reg 21 after) 0)
           (proof-register-frame-p 29 '(2 3 21) before after)
           (equal (proof-heap-base after) (proof-heap-base before))
           (consp (boymoo-model::a64-registers (proof-world-machine after)))
           (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (cdr after) (cdr before)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-frame-return-p proof-heap-base)
                     (proof-heap-p proof-machine-value-p proof-register-frame-p proof-segment-p
                      proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                      sequence-list-length-path sequence-instruction-path sequence-execute sequence-cons-spine-p))
     :use
     (sequence-subseq-end-branch-effects
      (:instance sequence-represented-sequence-length-bounded (word (proof-world-reg 0 before)) (world before))
      (:instance sequence-cons-spine-of-represented-datum (word (proof-world-reg 0 before)) (world before))
      (:instance sequence-cons-spine-on-equal-memory
                 (base (proof-heap-base before)) (word (proof-world-reg 0 before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-list-length-contract (before (sequence-execute *sequence-subseq-list-end-call* before)))
      (:instance sequence-register-frame-on-prefix (limit 30) (prefix 29) (clobbers '(2 3))
                 (before (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-register-frame-with-more-clobbers (limit 29) (old '(21)) (new '(2 3 21))
                 (after (sequence-execute *sequence-subseq-list-end-call* before)))
      (:instance sequence-register-frame-with-more-clobbers (limit 29) (old '(2 3)) (new '(2 3 21))
                 (before (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-register-frame-transitive (limit 29) (clobbers '(2 3 21))
                 (middle (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(2 3)) (register 5)
                 (before (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(2 3)) (register 6)
                 (before (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(2 3)) (register 21)
                 (before (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before))))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(2 3)) (register 28)
                 (before (sequence-execute *sequence-subseq-list-end-call* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-subseq-list-end-call* before)))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-default-end-has-untagged-length
   (let* ((machine (proof-world-machine before))
          (tag (+ image-base *sequence-subseq-tag-length-offset*))
          (after (sequence-execute (sequence-subseq-end-prefix datum nil) before)))
     (implies
      (and (sequence-subseq-view-complete-p datum image-base before)
           (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (equal (proof-world-reg 7 before) *proof-nil*)
           (implies (not (stringp datum))
                    (and (unsigned-byte-p 64 (+ image-base *sequence-list-length-offset* 32))
                         (sequence-instruction-path (sequence-list-length-path datum) (list tag)
                                                    (sequence-execute *sequence-subseq-list-end-call* before)))))
      (and (equal (proof-world-pc after) tag)
           (not (proof-world-stop after))
           (equal (proof-world-reg 2 after) (len (sequence-elements datum)))
           (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
           (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
           (equal (proof-world-reg 21 after) (if (stringp datum) 1 0))
           (proof-register-frame-p 29 '(2 3 21) before after)
           (equal (proof-heap-base after) (proof-heap-base before))
           (consp (boymoo-model::a64-registers (proof-world-machine after)))
           (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (cdr after) (cdr before)))))
   :hints
   (("Goal"
     :in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                         proof-heap-base proof-register-frame-p proof-reg-value-p proof-heap-p
                         sequence-instruction-path sequence-execute sequence-list-length-path acl2::binary-append)
     :use (sequence-subseq-end-branch-effects sequence-subseq-length-result-for-default-list-end
           (:instance sequence-register-frame-with-more-clobbers (limit 29) (old '(21)) (new '(2 3 21))
                      (after (sequence-execute *sequence-subseq-string-end* before))))
     :cases ((stringp datum))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-end-ready-effects
   (let* ((machine (proof-world-machine before))
          (target (+ image-base *sequence-subseq-end-ready-offset*))
          (tag (+ image-base *sequence-subseq-tag-length-offset*))
          (path (sequence-subseq-end-path datum limit))
          (after (sequence-execute path before)))
     (implies
      (and (sequence-subseq-view-complete-p datum image-base before)
           (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (proof-reg-value-p 7 limit before objects packages)
           (implies (and (null limit) (not (stringp datum)))
                    (and (unsigned-byte-p 64 (+ image-base *sequence-list-length-offset* 32))
                         (sequence-instruction-path (sequence-list-length-path datum) (list tag)
                                                    (sequence-execute *sequence-subseq-list-end-call* before)))))
      (and (equal (proof-world-pc after) target)
           (not (proof-world-stop after))
           (consp (boymoo-model::a64-registers (proof-world-machine after)))
           (proof-reg-value-p 7 (sequence-end limit datum) after objects packages)
           (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
           (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
           (equal (proof-world-reg 21 after) (if (stringp datum) 1 0))
           (proof-register-frame-p 29 '(2 3 7 21) before after)
           (equal (proof-heap-base after) (proof-heap-base before))
           (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (cdr after) (cdr before)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p proof-heap-base)
                     (proof-heap-p proof-view proof-world-machine proof-world-reg proof-world-pc
                      proof-world-stop proof-register-frame-p sequence-execute
                      sequence-instruction-path sequence-list-length-path proof-integer-word
                      sequence-tagged-length-view sequence-subseq-end-prefix sequence-elements
                      acl2::binary-append sequence-execute-append))
     :cases ((null limit))
     :use ((:instance sequence-nil-word-is-canonical (word (proof-world-reg 7 before)) (datum limit) (world before))
           (:instance sequence-represented-sequence-length-bounded (word (proof-world-reg 0 before)) (world before))))
    ("Subgoal 1"
     :use (sequence-subseq-default-end-has-untagged-length
           (:instance sequence-execute-append (world before)
                      (first (sequence-subseq-end-prefix datum nil)) (second *sequence-subseq-tag-length*))
           (:instance sequence-subseq-default-end-tags-length
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before)))
           (:instance sequence-register-frame-on-prefix (limit 30) (prefix 29) (clobbers '(7))
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))
           (:instance sequence-register-frame-with-more-clobbers (limit 29) (old '(2 3 21)) (new '(2 3 7 21))
                      (after (sequence-execute (sequence-subseq-end-prefix datum nil) before)))
           (:instance sequence-register-frame-with-more-clobbers (limit 29) (old '(7)) (new '(2 3 7 21))
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))
           (:instance sequence-register-frame-transitive (limit 29) (clobbers '(2 3 7 21))
                      (middle (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))
           (:instance sequence-tagged-length-view
                      (length (len (sequence-elements datum))) (base (proof-heap-base before))
                      (machine (proof-world-machine
                               (sequence-execute (sequence-subseq-end-path datum nil) before))))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(7)) (register 5)
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(7)) (register 6)
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(7)) (register 21)
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(7)) (register 28)
                      (before (sequence-execute (sequence-subseq-end-prefix datum nil) before))
                      (after (sequence-execute (sequence-subseq-end-path datum nil) before)))))
    ("Subgoal 2"
     :use (sequence-subseq-end-branch-effects
           (:instance sequence-register-frame-with-more-clobbers (limit 29) (old '(21)) (new '(2 3 7 21))
                      (after (sequence-execute *sequence-subseq-explicit-end* before)))
           (:instance sequence-view-of-equal-memory
                      (word (proof-world-reg 7 before)) (base (proof-heap-base before))
                      (first (proof-world-machine before))
                      (last (proof-world-machine
                             (sequence-execute *sequence-subseq-explicit-end* before)))))))
   :rule-classes nil))

(defthm sequence-subseq-end-ready
  (let* ((target (+ image-base *sequence-subseq-end-ready-offset*))
         (tag (+ image-base *sequence-subseq-tag-length-offset*))
         (path (sequence-subseq-end-path datum limit))
         (after (sequence-execute path before)))
    (implies
     (and (sequence-subseq-view-complete-p datum image-base before)
          (proof-heap-p before objects packages)
          (proof-reg-value-p 0 datum before objects packages)
          (proof-reg-value-p 5 datum before objects packages)
          (proof-reg-value-p 6 start before objects packages)
          (proof-reg-value-p 7 limit before objects packages)
          (implies (and (null limit) (not (stringp datum)))
                   (and (unsigned-byte-p 64 (+ image-base *sequence-list-length-offset* 32))
                        (sequence-instruction-path (sequence-list-length-path datum) (list tag)
                                                   (sequence-execute *sequence-subseq-list-end-call* before))))
          (sequence-instruction-path path (list target) before))
     (and (proof-segment-p (len path) (list target) before :cut after)
          (equal (proof-world-pc after) target)
          (not (proof-world-stop after))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (proof-reg-value-p 5 datum after objects packages)
          (proof-reg-value-p 6 start after objects packages)
          (proof-reg-value-p 7 (sequence-end limit datum) after objects packages)
          (equal (proof-world-reg 21 after) (if (stringp datum) 1 0))
          (proof-register-frame-p 29 '(2 3 7 21) before after)
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp (proof-world-machine before)))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory (proof-world-machine before))))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p)
                    (proof-heap-p proof-view proof-world-machine proof-world-reg proof-world-pc
                     proof-world-stop proof-heap-base proof-segment-p proof-register-frame-p
                     sequence-instruction-path sequence-execute
                     sequence-subseq-view-complete-p sequence-subseq-end-path sequence-list-length-path sequence-end))
    :use (sequence-subseq-end-ready-effects
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-subseq-end-path datum limit))
                     (cuts (list (+ image-base *sequence-subseq-end-ready-offset*)))
                     (after (sequence-execute (sequence-subseq-end-path datum limit) before)))
          (:instance sequence-view-of-equal-memory (word (proof-world-reg 5 before))
                     (base (proof-heap-base before)) (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute (sequence-subseq-end-path datum limit) before))))
          (:instance sequence-view-of-equal-memory (word (proof-world-reg 6 before))
                     (base (proof-heap-base before)) (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute (sequence-subseq-end-path datum limit) before)))))))
  :rule-classes nil)
