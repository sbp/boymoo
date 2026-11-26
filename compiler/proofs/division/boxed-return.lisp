(in-package "BOYMOO-PROOFS")

(include-book "boxed-entry")
(include-book "sign-view")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-advance proof-world-reg proof-world-pc proof-world-stop
                     proof-world-machine proof-load-word proof-segment-p division-before-cuts-p
                     division-instruction-sequence-ready-p proof-integer-view-p proof-reg-value-p
                     proof-integer-word proof-register-frame-p boymoo-model::a64-memory
                     boymoo-model::a64-sp)))

(defun division-pack-call-contract-p (value count before after objects packages)
  (and (proof-frame-return-p '(0 1 2 3 4) t before after)
       (implies (proof-integer-view-p value (proof-world-reg 0 before) count before)
                (and (proof-reg-value-p 0 value after objects packages)
                     (implies (proof-immediate-integer-p value)
                              (equal (proof-world-reg 0 after) (proof-integer-word value)))))))

(defun division-boxed-finish-steps (pack-steps)
  (+ 5 (nfix pack-steps)))

(defun division-boxed-finish-ready-p (entry value count pack-steps world objects packages)
  (let* ((packing (proof-advance 5 world))
         (returned (proof-advance pack-steps packing))
         (cuts (list (proof-world-reg 30 entry))))
    (and (natp pack-steps)
         (division-boxed-restore-inputs-p entry world)
         (division-instruction-sequence-ready-p *division-boxed-restore-instructions*
                                                (list (+ *division-boxed-restore-to-pack-offset*
                                                         (proof-world-pc world))) world)
         (division-pack-call-contract-p value count packing returned objects packages)
         (division-before-cuts-p (division-boxed-finish-steps pack-steps) cuts world))))

(local
 (defthm division-boxed-packing-receives-view
   (implies (and (division-boxed-finish-ready-p entry value count pack-steps world objects packages)
                 (proof-integer-view-p value (proof-world-reg 0 world) count world))
            (let ((packing (proof-advance 5 world)))
              (and (proof-integer-view-p value (proof-world-reg 0 packing) count packing)
                   (equal (proof-world-reg 30 packing) (proof-world-reg 30 entry)))))
   :hints (("Goal"
            :use ((:instance division-boxed-restores-frame-and-reaches-pack)
                  (:instance division-integer-view-after-equal-memory
                             (address (proof-world-reg 0 world)) (before world) (after (proof-advance 5 world))))
            :in-theory (disable division-boxed-restore-inputs-p division-pack-call-contract-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-finishes-through-pack
  (let* ((steps (division-boxed-finish-steps pack-steps))
         (after (proof-advance steps world))
         (cuts (list (proof-world-reg 30 entry))))
    (implies (and (division-boxed-finish-ready-p entry value count pack-steps world objects packages)
                  (proof-integer-view-p value (proof-world-reg 0 world) count world))
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-reg-value-p 0 value after objects packages)
                  (implies (proof-immediate-integer-p value)
                           (equal (proof-world-reg 0 after) (proof-integer-word value))))))
  :hints (("Goal"
           :use ((:instance division-boxed-packing-receives-view)
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-boxed-finish-steps pack-steps))
                            (cuts (list (proof-world-reg 30 entry))))
                 (:instance proof-advance-append (prefix 5) (suffix pack-steps)))
           :in-theory (disable division-boxed-restore-inputs-p proof-advance-append proof-immediate-integer-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-return-after-checked-prefix
  (let* ((middle (proof-advance prefix world))
         (after (proof-advance suffix middle)))
    (implies (and (natp prefix) (natp suffix)
                  (division-before-cuts-p prefix cuts world)
                  (proof-segment-p suffix cuts middle :cut after))
             (and (proof-segment-p (+ prefix suffix) cuts world :cut after)
                  (equal (proof-advance (+ prefix suffix) world) after))))
  :hints (("Goal"
           :use ((:instance division-run-after-cut-free-prefix)
                 (:instance proof-advance-append))
           :in-theory (e/d (proof-segment-p)
                           (proof-run division-run-after-cut-free-prefix proof-advance-append))
           :do-not-induct t))
  :rule-classes nil)
