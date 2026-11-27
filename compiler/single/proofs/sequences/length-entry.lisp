(in-package "BOYMOO-PROOFS")

(include-book "readonly-runtime")
(include-book "length-resume")
(include-book "spine-bounds")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-length-call-path (datum before)
  (append (sequence-readonly-view-prefix 'length before)
          (sequence-length-from-view-path datum)))

(local
 (defthm sequence-length-view-ready-for-count
   (let* ((returned (sequence-readonly-view-return 'length before))
          (word (proof-world-reg 0 before))
          (address (proof-pointer-address word (proof-heap-base before))))
     (implies (and (sequence-readonly-view-checked-p 'length before image-base)
                   (proof-heap-p before objects packages)
                   (proof-reg-value-p 0 datum before objects packages)
                   (implies (stringp datum) (unsigned-byte-p 64 (+ address 8))))
              (and (unsigned-byte-p 32 (len (sequence-elements datum)))
                   (if (stringp datum)
                       (and (not (equal (proof-world-reg 1 returned) 0))
                            (equal (proof-world-reg 2 returned) (len (sequence-elements datum))))
                     (and (equal (proof-world-reg 1 returned) 0)
                          (sequence-cons-spine-p datum (proof-world-reg 0 returned)
                                                 (proof-heap-base returned)
                                                 (proof-world-machine returned)))))))
   :hints
   (("Goal"
     :in-theory (enable proof-reg-value-p)
     :use ((:instance sequence-readonly-view-return-is-ready (routine 'length))
           (:instance sequence-stack-write-keeps-heap-invariant
                      (after (sequence-readonly-view-return 'length before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-confined-stack-write-preserves-value
                      (word (proof-world-reg 0 before))
                      (after (sequence-readonly-view-return 'length before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-represented-sequence-length-bounded
                      (world before) (word (proof-world-reg 0 before)))
           (:instance sequence-cons-spine-of-represented-datum
                      (world (sequence-readonly-view-return 'length before))
                      (word (proof-world-reg 0 before))))))
   :rule-classes nil))

(local
 (defthm sequence-length-entry-effects
   (let* ((returned (sequence-readonly-view-return 'length before))
          (called (sequence-execute *sequence-length-view-to-list* returned))
          (machine (proof-world-machine before))
          (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before)))
          (link (proof-world-reg 30 before))
          (path (sequence-length-call-path datum before))
          (after (sequence-execute path before)))
     (implies
      (and (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (sequence-readonly-view-checked-p 'length before image-base)
           (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
           (unsigned-byte-p 64 (+ image-base *sequence-length-tag-offset*))
           (implies (not (stringp datum))
                    (sequence-instruction-path (sequence-list-length-path datum)
                                               (list (+ image-base *sequence-length-tag-offset*))
                                               called))
           (sequence-instruction-path path (list link) before))
      (and (not (proof-world-stop after))
           (equal (proof-world-pc after) link)
           (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
           (equal (proof-world-reg 30 after) link)
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (sequence-caller-save-memory before))
           (equal (cdr after) (cdr before))
           (proof-register-frame-p 28 '(0 1 2 3) before after)
           (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                              objects packages (proof-world-machine after))
                  (boymoo-model::core-prelude 'length (list datum))))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-readonly-view-link)
                     (proof-reg-value-p proof-view proof-segment-p proof-register-frame-p
                      proof-load-word proof-world-stop proof-pointer-address
                      sequence-core-length boymoo-model::core-prelude
                      sequence-elements sequence-length-from-view-path
                      sequence-cons-spine-p sequence-list-length-path acl2::binary-append))
     :use ((:instance sequence-readonly-view-return-is-ready (routine 'length))
           sequence-length-view-ready-for-count
           (:instance sequence-readonly-checked-suffix
                      (routine 'length) (suffix (sequence-length-from-view-path datum))
                      (cuts (list (proof-world-reg 30 before))))
           (:instance sequence-length-from-view-to-source
                      (before (sequence-readonly-view-return 'length before)))
           (:instance sequence-register-frame-transitive
                      (limit 28) (clobbers '(0 1 2 3))
                      (middle (sequence-readonly-view-return 'length before))
                      (after (sequence-execute (sequence-length-call-path datum before) before))))))
   :rule-classes nil))

(defthm sequence-length-runtime-contract
  (let* ((returned (sequence-readonly-view-return 'length before))
         (called (sequence-execute *sequence-length-view-to-list* returned))
         (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before)))
         (link (proof-world-reg 30 before))
         (path (sequence-length-call-path datum before))
         (after (sequence-execute path before)))
    (implies
     (and (proof-runtime-pre-p 'length (list datum) program labels image-base before objects packages)
          (sequence-readonly-view-checked-p 'length before image-base)
          (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
          (unsigned-byte-p 64 (+ image-base *sequence-length-tag-offset*))
          (implies (not (stringp datum))
                   (sequence-instruction-path (sequence-list-length-path datum)
                                              (list (+ image-base *sequence-length-tag-offset*))
                                              called))
          (sequence-instruction-path path (list link) before))
     (and (proof-segment-p (len path) (list link) before :cut after)
          (proof-runtime-return-p 'length (list datum) program before after objects objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-pre-p)
                    (proof-runtime-return-p proof-view proof-register-frame-p proof-frame-return-p
                     proof-reg-value-p proof-program-packages-p proof-label-address proof-world-stop
                     proof-segment-p proof-pointer-address sequence-length-call-path
                     sequence-length-from-view-path sequence-list-length-path boymoo-model::core-prelude))
    :use (sequence-length-entry-effects
          (:instance sequence-readonly-restored-runtime-frame
                     (routine 'length)
                     (after (sequence-execute (sequence-length-call-path datum before) before)))
          (:instance sequence-readonly-datum-contract
                     (routine 'length) (args (list datum))
                     (after (sequence-execute (sequence-length-call-path datum before) before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-length-call-path datum before))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute (sequence-length-call-path datum before) before))))))
  :rule-classes nil)
