(in-package "BOYMOO-PROOFS")

(include-book "subseq-start-call")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-register-only-change-keeps-root-storage
   (implies (sequence-register-only-change-p before after)
            (and (equal (proof-stack-base after) (proof-stack-base before))
                 (equal (proof-stack-top after) (proof-stack-top before))
                 (implies (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                                 datum before objects packages)
                          (proof-machine-value-p (proof-load-word slot (proof-world-machine after))
                                                 datum after objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-register-only-change-p sequence-heap-registers-agree-p
                      proof-stack-base proof-runtime-word proof-load-word proof-machine-value-p)
                     (proof-world-machine proof-world-reg proof-heap-base proof-stack-top proof-value-p))
     :use ((:instance sequence-representation-on-identical-memory (datum datum) (base (proof-heap-base before))
                      (first (proof-world-machine before)) (last (proof-world-machine after))
                      (word (proof-load-word slot (proof-world-machine before)))))))
   :rule-classes nil))

(local
 (defthm sequence-root-is-still-live-in-addition
   (let ((slot (+ (proof-stack-base before) (* 8 index))))
     (implies
      (and (proof-runtime-return-p 'acl2::unary-- (list start) program before returned
                                   old-objects new-objects packages)
           (sequence-register-only-change-p returned called)
           (natp index) (< index (sequence-prefix-length (proof-stack-top before) before))
           (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                  datum before old-objects packages))
      (and (equal (proof-stack-base called) (proof-stack-base before))
           (equal (proof-stack-top called) (proof-stack-top before))
           (< index (sequence-prefix-length (proof-stack-top called) called))
           (proof-machine-value-p (proof-load-word slot (proof-world-machine called))
                                  datum called new-objects packages))))
   :hints
   (("Goal"
     :in-theory (disable proof-runtime-return-p proof-stack-base proof-stack-top proof-world-machine
                         proof-load-word proof-machine-value-p sequence-register-only-change-p)
     :use ((:instance sequence-arithmetic-return-state (routine 'acl2::unary--) (args (list start))
                      (after returned))
           (:instance sequence-runtime-return-preserves-root-slot (routine 'acl2::unary--)
                      (args (list start)) (after returned))
           (:instance sequence-register-only-change-keeps-root-storage
                      (before returned) (after called) (objects new-objects)
                      (slot (+ (proof-stack-base before) (* 8 index)))))))
   :rule-classes nil))

(defun sequence-subseq-numeric-returning-instruction-count
    (image-base neg-fuel add-fuel before negated added)
  (let* ((target (+ image-base *sequence-subseq-checked-offset*))
         (neg-link (+ image-base *sequence-subseq-numeric-offset* 36))
         (add-link (+ image-base *sequence-subseq-numeric-offset* 52))
         (called (sequence-execute *sequence-subseq-addition-call* negated)))
    (+ (sequence-segment-count neg-fuel (list neg-link target) before)
       (len *sequence-subseq-addition-call*)
       (sequence-segment-count add-fuel (list add-link target) called)
       (len (sequence-subseq-after-addition-path added)))))

(local
 (defthm sequence-subseq-join-arithmetic-segments
   (let* ((target (+ image-base *sequence-subseq-checked-offset*))
          (cuts (list target))
          (neg-link (+ image-base *sequence-subseq-numeric-offset* 36))
          (add-link (+ image-base *sequence-subseq-numeric-offset* 52))
          (called (sequence-execute *sequence-subseq-addition-call* negated))
          (suffix (sequence-subseq-after-addition-path added)))
     (implies
      (and (natp image-base)
           (not (proof-world-stop negated)) (equal (proof-world-pc negated) neg-link)
           (not (proof-world-stop added)) (equal (proof-world-pc added) add-link)
           (proof-segment-p neg-fuel (cons neg-link cuts) before :cut negated)
           (sequence-instruction-path *sequence-subseq-addition-call* cuts negated)
           (proof-segment-p add-fuel (cons add-link cuts) called :cut added)
           (proof-segment-p (len suffix) cuts added :cut after))
      (proof-segment-p (sequence-subseq-numeric-returning-instruction-count
                        image-base neg-fuel add-fuel before negated added)
                       cuts before :cut after)))
   :hints
   (("Goal"
     :in-theory (disable sequence-execute sequence-instruction-path proof-segment-p proof-world-stop
                         proof-world-pc sequence-segment-count sequence-subseq-after-addition-path)
     :use
     ((:instance sequence-append-returning-call
                 (before (sequence-execute *sequence-subseq-addition-call* negated))
                 (middle added) (fuel add-fuel) (reason :cut)
                 (link (+ image-base *sequence-subseq-numeric-offset* 52))
                 (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
                 (suffix (len (sequence-subseq-after-addition-path added))))
      (:instance sequence-append-checked-instructions
                 (before negated) (instructions *sequence-subseq-addition-call*) (reason :cut)
                 (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
                 (suffix (+ (sequence-segment-count add-fuel
                                                    (list (+ image-base *sequence-subseq-numeric-offset* 52)
                                                          (+ image-base *sequence-subseq-checked-offset*))
                                                    (sequence-execute *sequence-subseq-addition-call* negated))
                            (len (sequence-subseq-after-addition-path added)))))
      (:instance sequence-append-returning-call
                 (middle negated) (fuel neg-fuel) (reason :cut)
                 (link (+ image-base *sequence-subseq-numeric-offset* 36))
                 (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
                 (suffix (+ (len *sequence-subseq-addition-call*)
                            (sequence-segment-count add-fuel
                                                    (list (+ image-base *sequence-subseq-numeric-offset* 52)
                                                          (+ image-base *sequence-subseq-checked-offset*))
                                                    (sequence-execute *sequence-subseq-addition-call* negated))
                            (len (sequence-subseq-after-addition-path added))))))))
   :rule-classes nil))

(defthm sequence-subseq-numeric-through-both-arithmetic-calls
  (let* ((end (sequence-end limit datum))
         (difference (- end start))
         (neg-result (boymoo-model::core-datum (proof-runtime-value 'acl2::unary-- (list start) program)))
         (target (+ image-base *sequence-subseq-checked-offset*))
         (cuts (list target))
         (neg-link (+ image-base *sequence-subseq-numeric-offset* 36))
         (add-link (+ image-base *sequence-subseq-numeric-offset* 52))
         (base (proof-stack-base before))
         (top (proof-stack-top before))
         (end-slot (+ base (* 8 end-index)))
         (source-slot (+ base (* 8 source-index)))
         (add-target (+ image-base *sequence-subseq-addition-offset*))
         (called (sequence-execute *sequence-subseq-addition-call* negated))
         (size-call (sequence-execute *sequence-subseq-numeric-size-call* added))
         (suffix (sequence-subseq-after-addition-path added))
         (after (sequence-execute suffix added)))
    (implies
     (and (proof-runtime-return-p 'acl2::unary-- (list start) program before negated
                                  old-objects negated-objects packages)
          (proof-runtime-return-p 'acl2::binary-+ (list end neg-result) program called added
                                  negated-objects added-objects packages)
          (equal (proof-world-reg 30 before) neg-link)
          (proof-segment-p neg-fuel (cons neg-link cuts) before :cut negated)
          (proof-segment-p add-fuel (cons add-link cuts) called :cut added)
          (natp image-base)
          (unsigned-byte-p 64 add-link)
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 56))
          (unsigned-byte-p 64 target)
          (consp (boymoo-model::a64-registers (proof-world-machine negated)))
          (consp (boymoo-model::a64-registers (proof-world-machine added)))
          (natp end-index) (< end-index (sequence-prefix-length top before))
          (natp source-index) (< source-index (sequence-prefix-length top before))
          (natp end-slot) (equal end-slot (- top 8))
          (natp source-slot) (equal source-slot (- top 16))
          (proof-machine-value-p (proof-load-word end-slot (proof-world-machine before))
                                 end before old-objects packages)
          (proof-machine-value-p (proof-load-word source-slot (proof-world-machine before))
                                 datum before old-objects packages)
          (equal (proof-world-reg 20 before) (sequence-runtime-count start))
          (proof-program-packages-p program packages)
          (equal (proof-label-address "prim:ACL2::BINARY-+" image-base labels) add-target)
          (sequence-instruction-path *sequence-subseq-addition-call* (list add-target) negated)
          (sequence-instruction-path *sequence-subseq-addition-call* cuts negated)
          (sequence-subseq-size-index-readable-p size-call)
          (sequence-instruction-path (sequence-subseq-size-index-path size-call)
                                     (list (+ image-base *sequence-subseq-numeric-offset* 56)) size-call)
          (sequence-instruction-path suffix cuts added))
     (and (proof-segment-p (sequence-subseq-numeric-returning-instruction-count
                           image-base neg-fuel add-fuel before negated added)
                          cuts before :cut after)
          (proof-runtime-pre-p 'acl2::binary-+ (list end neg-result) program labels image-base
                               called negated-objects packages)
          (equal (proof-world-reg 19 after) (sequence-runtime-count difference))
          (implies (< (proof-world-reg 19 after) *proof-space-size*)
                   (equal (proof-world-reg 19 after) (sequence-result-size datum start limit)))
          (equal (proof-world-reg 20 after) (sequence-runtime-count start))
          (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
          (equal (proof-stack-top after) source-slot)
          (proof-reg-value-p 0 datum after added-objects packages))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable proof-runtime-return-p proof-runtime-pre-p proof-machine-value-p proof-reg-value-p
                        proof-program-packages-p proof-label-address proof-runtime-value proof-heap-p
                        proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-stack-base
                        proof-stack-top proof-load-word proof-segment-p sequence-instruction-path
                        sequence-segment-count sequence-execute sequence-prefix-length sequence-end
                        sequence-result-size sequence-runtime-count sequence-register-only-change-p
                        sequence-subseq-numeric-returning-instruction-count
                        sequence-subseq-after-addition-path sequence-subseq-size-index-path
                        sequence-subseq-size-index-readable-p sequence-runtime-count-exact-for-bounded-size)
    :use ((:instance sequence-subseq-addition-precondition (returned negated) (new-objects negated-objects))
          (:instance sequence-root-is-still-live-in-addition (returned negated) (index source-index)
                     (called (sequence-execute *sequence-subseq-addition-call* negated))
                     (new-objects negated-objects))
          (:instance sequence-subseq-size-from-addition-return
                     (before (sequence-execute *sequence-subseq-addition-call* negated))
                     (returned added) (old-objects negated-objects) (new-objects added-objects))
          (:instance sequence-arithmetic-return-state (routine 'acl2::unary--) (args (list start))
                     (after negated) (new-objects negated-objects))
          (:instance sequence-arithmetic-return-state
                     (routine 'acl2::binary-+)
                     (args (list (sequence-end limit datum)
                                 (boymoo-model::core-datum (proof-runtime-value 'acl2::unary-- (list start) program))))
                     (before (sequence-execute *sequence-subseq-addition-call* negated))
                     (after added) (old-objects negated-objects) (new-objects added-objects))
          (:instance sequence-subseq-join-arithmetic-segments
                     (after (sequence-execute (sequence-subseq-after-addition-path added) added))))))
  :rule-classes nil)
