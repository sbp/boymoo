(in-package "BOYMOO-PROOFS")

(include-book "subseq-call-contracts")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-start-count-return (before)
  (sequence-execute (sequence-subseq-size-index-path before) before))

(defun sequence-subseq-negation-prefix (before)
  (append (sequence-subseq-size-index-path before) *sequence-subseq-negation-call*))

(local
 (defthm sequence-subseq-start-count-preserves-arguments
   (let* ((machine (proof-world-machine before))
          (after (sequence-subseq-start-count-return before))
          (last (proof-world-machine after))
          (path (sequence-subseq-size-index-path before))
          (link (+ image-base *sequence-subseq-numeric-offset* 24)))
     (implies
      (and (proof-heap-p before objects packages)
           (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers machine))
           (equal (proof-world-reg 30 before) link)
           (equal (proof-world-reg 6 before) (proof-world-reg 0 before))
           (proof-reg-value-p 0 start before objects packages)
           (sequence-subseq-size-index-readable-p before)
           (sequence-instruction-path path (list link) before))
      (and (proof-heap-p after objects packages)
           (not (proof-world-stop after))
           (equal (proof-world-pc after) link)
           (equal (proof-world-reg 0 after) (sequence-runtime-count start))
           (proof-reg-value-p 6 start after objects packages)
           (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
           (consp (boymoo-model::a64-registers last))
           (sequence-register-only-change-p before after))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-frame-return-p
                      sequence-register-only-change-p sequence-heap-registers-agree-p)
                     (proof-view proof-value-p proof-heap-p proof-register-frame-p
                      proof-pointer-address proof-word-tag proof-header-type proof-load-word
                      proof-world-machine proof-world-pc proof-world-reg proof-world-stop proof-heap-base
                      proof-fixed-heap-p proof-preserved-heap-p proof-segment-p
                      sequence-index-path sequence-index-value sequence-execute sequence-runtime-count
                      sequence-runtime-count-exact-for-bounded-size sequence-count sequence-instruction-path))
     :use ((:instance sequence-index-count-contract (datum start)) sequence-index-count-effects
           (:instance sequence-register-frame-on-prefix (limit 30) (prefix 28) (clobbers '(0 3 4))
                      (after (sequence-subseq-start-count-return before)))
           (:instance sequence-frame-keeps-heap-registers (clobbers '(0 3 4))
                      (after (sequence-subseq-start-count-return before)))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(0 3 4)) (register 6)
                      (after (sequence-subseq-start-count-return before)))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(0 3 4)) (register 21)
                      (after (sequence-subseq-start-count-return before)))
           (:instance sequence-register-only-change-keeps-heap (after (sequence-subseq-start-count-return before)))
           (:instance sequence-representation-on-identical-memory
                      (word (proof-world-reg 0 before)) (datum start) (base (proof-heap-base before))
                      (first (proof-world-machine before))
                      (last (proof-world-machine (sequence-subseq-start-count-return before)))))
     :expand ((sequence-heap-registers-agree-p before (sequence-subseq-start-count-return before)))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-negation-call-from-start-count
   (let* ((path *sequence-subseq-negation-call*)
          (after (sequence-execute path before))
          (target (+ image-base *sequence-subseq-negation-offset*)))
     (implies
      (and (proof-heap-p before objects packages)
           (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers (proof-world-machine before)))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-subseq-numeric-offset* 24))
           (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 36))
           (proof-reg-value-p 6 start before objects packages)
           (equal (proof-world-reg 0 before) (sequence-runtime-count start))
           (proof-program-packages-p program packages)
           (equal (proof-label-address "prim:ACL2::UNARY--" image-base labels) target))
      (and (proof-runtime-pre-p 'acl2::unary-- (list start) program labels image-base after objects packages)
           (equal (proof-world-pc after) target)
           (not (proof-world-stop after))
           (equal (proof-world-reg 30 after) (+ image-base *sequence-subseq-numeric-offset* 36))
           (equal (proof-world-reg 20 after) (sequence-runtime-count start))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
           (sequence-register-only-change-p before after))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-runtime-pre-p proof-reg-value-p proof-machine-value-p
                      proof-world-stop sequence-register-only-change-p)
                     (proof-view proof-value-p proof-heap-p proof-register-frame-p
                      proof-world-machine proof-world-pc proof-world-reg proof-heap-base
                      proof-fixed-heap-p proof-preserved-heap-p proof-segment-p sequence-execute
                      proof-program-packages-p proof-label-address sequence-runtime-count))
     :use (sequence-subseq-arithmetic-negation-call
           (:instance sequence-frame-keeps-heap-registers (clobbers '(0 20))
                      (after (sequence-execute *sequence-subseq-negation-call* before)))
           (:instance sequence-register-only-change-keeps-heap
                      (after (sequence-execute *sequence-subseq-negation-call* before)))
           (:instance sequence-representation-on-identical-memory
                      (word (proof-world-reg 6 before)) (datum start) (base (proof-heap-base before))
                      (first (proof-world-machine before))
                      (last (proof-world-machine (sequence-execute *sequence-subseq-negation-call* before)))))))
   :rule-classes nil))

(defthm sequence-subseq-negation-precondition
  (let* ((index-path (sequence-subseq-size-index-path before))
         (path (sequence-subseq-negation-prefix before))
         (target (+ image-base *sequence-subseq-negation-offset*))
         (after (sequence-execute path before))
         (link (+ image-base *sequence-subseq-numeric-offset* 24)))
    (implies
     (and (proof-heap-p before objects packages)
          (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (equal (proof-world-reg 30 before) link)
          (equal (proof-world-reg 6 before) (proof-world-reg 0 before))
          (proof-reg-value-p 0 start before objects packages)
          (natp image-base)
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 36))
          (sequence-subseq-size-index-readable-p before)
          (proof-program-packages-p program packages)
          (equal (proof-label-address "prim:ACL2::UNARY--" image-base labels) target)
          (sequence-instruction-path index-path (list link) before)
          (sequence-instruction-path path (list target) before))
     (and (proof-segment-p (len path) (list target) before :cut after)
          (proof-runtime-pre-p 'acl2::unary-- (list start) program labels image-base after objects packages)
          (equal (proof-world-reg 30 after) (+ image-base *sequence-subseq-numeric-offset* 36))
          (equal (proof-world-reg 20 after) (sequence-runtime-count start))
          (equal (proof-world-reg 21 after) (proof-world-reg 21 before)))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-p proof-segment-p proof-runtime-pre-p proof-reg-value-p
                        proof-program-packages-p proof-label-address
                        proof-world-machine proof-world-pc proof-world-reg proof-world-stop
                        sequence-subseq-start-count-return sequence-subseq-size-index-path
                        sequence-subseq-size-index-readable-p sequence-instruction-path sequence-execute
                        sequence-register-only-change-p sequence-runtime-count acl2::binary-append
                        sequence-execute-append)
    :use (sequence-subseq-start-count-preserves-arguments
          (:instance sequence-subseq-negation-call-from-start-count
                     (before (sequence-subseq-start-count-return before)))
          (:instance sequence-execute-append (world before)
                     (first (sequence-subseq-size-index-path before)) (second *sequence-subseq-negation-call*))
          (:instance sequence-segment-of-instruction-path
                     (instructions (append (sequence-subseq-size-index-path before) *sequence-subseq-negation-call*))
                     (cuts (list (+ image-base *sequence-subseq-negation-offset*)))
                     (after (sequence-execute (append (sequence-subseq-size-index-path before)
                                                      *sequence-subseq-negation-call*) before))))
    :expand ((sequence-subseq-start-count-return before))))
  :rule-classes nil)
