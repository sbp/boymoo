(in-package "BOYMOO-PROOFS")

(include-book "readonly-runtime")
(include-book "char-resume")
(include-book "static-roots")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-char-call-path (datum before)
  (append (sequence-readonly-view-prefix 'char before)
          (sequence-char-from-view-path datum (sequence-readonly-view-return 'char before))))

(defun sequence-char-count-checked-p (returned image-base)
  (let ((called (sequence-execute *sequence-char-count-call* returned))
        (link (+ image-base *sequence-char-offset* 24)))
    (and (unsigned-byte-p 64 link)
         (sequence-char-index-readable-p called)
         (sequence-instruction-path (sequence-char-index-path called) (list link) called))))

(local
 (defthm sequence-string-payload-of-represented-datum
   (let* ((machine (proof-world-machine world))
          (address (proof-pointer-address word (proof-heap-base world)))
          (payload (+ address 8))
          (length (len (coerce datum 'list))))
     (implies (and (stringp datum)
                   (unsigned-byte-p 64 payload)
                   (proof-machine-value-p word datum world objects packages))
              (and (proof-span-p payload length)
                   (equal (proof-load-string length payload machine) datum))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-machine-value-p proof-value-p proof-view proof-load-word proof-header-size)
                     (proof-view-step proof-load-string proof-pointer-address))
     :use ((:instance sequence-string-view-of-represented-value
                      (base (proof-heap-base world)) (machine (proof-world-machine world))
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                                     objects))))))
           (:instance sequence-load-string-length
                      (count (proof-header-size
                              (proof-load-word (proof-pointer-address word (proof-heap-base world))
                                               (proof-world-machine world))))
                      (address (+ 8 (proof-pointer-address word (proof-heap-base world))))
                      (machine (proof-world-machine world)))
           (:instance sequence-floor-of-unsigned
                      (dropped 8) (kept 56)
                      (value (proof-load-word (proof-pointer-address word (proof-heap-base world))
                                              (proof-world-machine world)))))))
   :rule-classes nil))

(local
 (defthm sequence-char-view-ready-for-index
   (let* ((returned (sequence-readonly-view-return 'char before))
          (last (proof-world-machine returned))
          (word (proof-world-reg 0 before))
          (address (proof-pointer-address word (proof-heap-base before)))
          (payload (proof-world-reg 1 returned))
          (length (proof-world-reg 2 returned)))
     (implies (and (sequence-readonly-view-checked-p 'char before image-base)
                   (proof-heap-p before objects packages)
                   (proof-reg-value-p 0 datum before objects packages)
                   (proof-reg-value-p 1 position before objects packages)
                   (implies (stringp datum) (unsigned-byte-p 64 (+ address 8))))
              (and (<= (len (sequence-elements datum)) *proof-space-size*)
                   (proof-value-p *proof-nil* nil (proof-heap-base returned) objects packages last)
                   (if (stringp datum)
                       (and (not (equal payload 0))
                            (proof-span-p payload length)
                            (equal datum (proof-load-string length payload last))
                            (proof-reg-value-p 5 position returned objects packages))
                     (equal payload 0)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                     (proof-view proof-value-p proof-span-p proof-load-string
                      proof-pointer-address proof-register-frame-p proof-world-stop
                      sequence-elements proof-load-word))
     :use ((:instance sequence-readonly-view-return-is-ready (routine 'char))
           (:instance sequence-stack-write-keeps-heap-invariant
                      (after (sequence-readonly-view-return 'char before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-confined-stack-write-preserves-value
                      (word (proof-world-reg 0 before))
                      (after (sequence-readonly-view-return 'char before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-confined-stack-write-preserves-value
                      (word (proof-world-reg 1 before)) (datum position)
                      (after (sequence-readonly-view-return 'char before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-represented-sequence-length-bounded
                      (world before) (word (proof-world-reg 0 before)))
           (:instance sequence-static-truth-values-in-heap
                      (world (sequence-readonly-view-return 'char before)))
           (:instance sequence-string-payload-of-represented-datum
                      (world (sequence-readonly-view-return 'char before)) (word (proof-world-reg 0 before))))))
   :rule-classes nil))

(local
 (defthm sequence-char-entry-effects
   (let* ((returned (sequence-readonly-view-return 'char before))
          (machine (proof-world-machine before))
          (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before)))
          (link (proof-world-reg 30 before))
          (path (sequence-char-call-path datum before))
          (after (sequence-execute path before)))
     (implies
      (and (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (proof-reg-value-p 1 position before objects packages)
           (sequence-readonly-view-checked-p 'char before image-base)
           (implies (stringp datum)
                    (and (unsigned-byte-p 64 (+ address 8))
                         (sequence-char-count-checked-p returned image-base)))
           (sequence-instruction-path path (list link) before))
      (and (not (proof-world-stop after))
           (equal (proof-world-pc after) link)
           (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
           (equal (proof-world-reg 30 after) link)
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (sequence-caller-save-memory before))
           (equal (cdr after) (cdr before))
           (proof-register-frame-p 28 '(0 1 2 3 4 5) before after)
           (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                              objects packages (proof-world-machine after))
                  (boymoo-model::core-prelude 'char (list datum position))))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-readonly-view-link)
                     (proof-reg-value-p proof-value-p proof-view proof-segment-p
                      proof-register-frame-p proof-load-word proof-world-stop proof-pointer-address
                      sequence-core-char boymoo-model::core-prelude boymoo-model::core-prelude-values
                      sequence-char-from-view-path sequence-char-index-path sequence-char-index-readable-p
                      sequence-elements proof-load-string acl2::binary-append))
     :use ((:instance sequence-readonly-view-return-is-ready (routine 'char))
           sequence-char-view-ready-for-index
           (:instance sequence-readonly-checked-suffix
                      (routine 'char)
                      (suffix (sequence-char-from-view-path datum
                                                           (sequence-readonly-view-return 'char before)))
                      (cuts (list (proof-world-reg 30 before))))
           (:instance sequence-char-from-view-to-source
                      (before (sequence-readonly-view-return 'char before)))
           (:instance sequence-register-frame-transitive
                      (limit 28) (clobbers '(0 1 2 3 4 5))
                      (middle (sequence-readonly-view-return 'char before))
                      (after (sequence-execute (sequence-char-call-path datum before) before))))))
   :rule-classes nil))

(defthm sequence-char-runtime-contract
  (let* ((returned (sequence-readonly-view-return 'char before))
         (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before)))
         (link (proof-world-reg 30 before))
         (path (sequence-char-call-path datum before))
         (after (sequence-execute path before)))
    (implies
     (and (proof-runtime-pre-p 'char (list datum position) program labels image-base before objects packages)
          (sequence-readonly-view-checked-p 'char before image-base)
          (implies (stringp datum)
                   (and (unsigned-byte-p 64 (+ address 8))
                        (sequence-char-count-checked-p returned image-base)))
          (sequence-instruction-path path (list link) before))
     (and (proof-segment-p (len path) (list link) before :cut after)
          (proof-runtime-return-p 'char (list datum position) program
                                  before after objects objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-pre-p)
                    (proof-runtime-return-p proof-view proof-register-frame-p proof-frame-return-p
                     proof-reg-value-p proof-program-packages-p proof-label-address proof-world-stop
                     proof-segment-p proof-pointer-address sequence-char-call-path
                     sequence-char-count-checked-p proof-core-program
                     boymoo-model::core-prelude))
    :use (sequence-char-entry-effects
          (:instance sequence-readonly-restored-runtime-frame
                     (routine 'char)
                     (after (sequence-execute (sequence-char-call-path datum before) before)))
          (:instance sequence-readonly-datum-contract
                     (routine 'char) (args (list datum position))
                     (after (sequence-execute (sequence-char-call-path datum before) before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-char-call-path datum before))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute (sequence-char-call-path datum before) before))))))
  :rule-classes nil)
