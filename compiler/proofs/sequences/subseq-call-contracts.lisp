(in-package "BOYMOO-PROOFS")

(include-book "subseq-arithmetic")
(include-book "root-prefix")
(include-book "register-only")
(include-book "call-segments")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-arithmetic-return-state
  (implies (and (member-eq routine '(acl2::unary-- acl2::binary-+))
                (proof-runtime-return-p routine args program before after
                                        old-objects new-objects packages))
           (and (not (proof-world-stop after))
                (equal (proof-world-pc after) (proof-world-reg 30 before))
                (equal (proof-stack-top after) (proof-stack-top before))
                (equal (proof-stack-base after) (proof-stack-base before))
                (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
                (proof-heap-p after new-objects packages)
                (proof-reg-value-p 0 (boymoo-model::core-datum
                                      (proof-runtime-value routine args program))
                                   after new-objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-return-p proof-datum-return-p proof-frame-return-p
                     proof-preserved-heap-p proof-heap-frame-p proof-runtime-clobbers proof-stack-top)
                    (proof-stack-prefix proof-prefix-preserved-p proof-fixed-heap-p
                     proof-reg-value-p proof-runtime-value proof-heap-p proof-stack-base
                     proof-memory-span-agrees-p proof-dynamic-table-preserved-p
                     proof-register-frame-p))
    :use ((:instance sequence-register-in-frame
                     (limit 30) (register 20) (clobbers (proof-runtime-clobbers routine)))
          (:instance sequence-register-in-frame
                     (limit 30) (register 21) (clobbers (proof-runtime-clobbers routine)))
          (:instance sequence-register-in-frame
                     (limit 30) (register 25) (clobbers (proof-runtime-clobbers routine))))))
  :rule-classes nil)

(defun sequence-subseq-size-index-path (world)
  (sequence-index-path (proof-world-reg 0 world) (proof-heap-base world)
                       (proof-world-machine world)))

(defun sequence-subseq-size-index-readable-p (world)
  (let* ((word (proof-world-reg 0 world))
         (address (proof-pointer-address word (proof-heap-base world))))
    (implies (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type (proof-load-word address (proof-world-machine world))) 3))
             (unsigned-byte-p 64 (+ address 8)))))

(local
 (defthm sequence-count-subseq-difference
   (let* ((path *sequence-subseq-numeric-size-call*)
          (called (sequence-execute path before))
          (index-path (sequence-subseq-size-index-path called))
          (counted (sequence-execute index-path called))
          (link (+ image-base *sequence-subseq-numeric-offset* 56)))
     (implies
      (and (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers (proof-world-machine before)))
           (natp image-base) (unsigned-byte-p 64 link)
           (equal (proof-world-pc before) (+ image-base *sequence-subseq-numeric-offset* 52))
           (proof-reg-value-p 0 difference before objects packages)
           (sequence-subseq-size-index-readable-p called)
           (sequence-instruction-path index-path (list link) called))
      (and (proof-segment-p (len index-path) (list link) called :cut counted)
           (equal (proof-world-pc counted) link)
           (not (proof-world-stop counted))
           (equal (proof-world-reg 0 counted) (sequence-runtime-count difference))
           (equal (proof-world-reg 20 counted) (proof-world-reg 20 before))
           (equal (proof-world-reg 21 counted) (proof-world-reg 21 before))
           (equal (proof-stack-top counted) (proof-stack-top before))
           (equal (proof-heap-base counted) (proof-heap-base before))
           (equal (boymoo-model::a64-memory (proof-world-machine counted))
                  (boymoo-model::a64-memory (proof-world-machine before)))
           (consp (boymoo-model::a64-registers (proof-world-machine counted))))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-world-stop proof-stack-top
                      proof-heap-base)
                     (proof-value-p proof-view proof-frame-return-p proof-register-frame-p
                      proof-segment-p sequence-execute proof-world-pc proof-world-reg
                      proof-world-machine proof-pointer-address proof-load-word proof-word-tag
                      proof-header-type sequence-index-path sequence-index-value sequence-runtime-count))
     :use
     (sequence-subseq-arithmetic-size-count-call
      (:instance sequence-representation-on-identical-memory
                 (word (proof-world-reg 0 before)) (datum difference) (base (proof-heap-base before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine (sequence-execute *sequence-subseq-numeric-size-call* before))))
      (:instance sequence-index-count-contract
                 (before (sequence-execute *sequence-subseq-numeric-size-call* before))
                 (datum difference))
      (:instance sequence-index-count-effects
                 (before (sequence-execute *sequence-subseq-numeric-size-call* before)))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 20)
                 (before (sequence-execute *sequence-subseq-numeric-size-call* before))
                 (after (sequence-execute
                         (sequence-subseq-size-index-path
                          (sequence-execute *sequence-subseq-numeric-size-call* before))
                         (sequence-execute *sequence-subseq-numeric-size-call* before))))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 21)
                 (before (sequence-execute *sequence-subseq-numeric-size-call* before))
                 (after (sequence-execute
                         (sequence-subseq-size-index-path
                          (sequence-execute *sequence-subseq-numeric-size-call* before))
                         (sequence-execute *sequence-subseq-numeric-size-call* before))))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 25)
                 (before (sequence-execute *sequence-subseq-numeric-size-call* before))
                 (after (sequence-execute
                         (sequence-subseq-size-index-path
                          (sequence-execute *sequence-subseq-numeric-size-call* before))
                         (sequence-execute *sequence-subseq-numeric-size-call* before))))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 28)
                 (before (sequence-execute *sequence-subseq-numeric-size-call* before))
                 (after (sequence-execute
                         (sequence-subseq-size-index-path
                          (sequence-execute *sequence-subseq-numeric-size-call* before))
                         (sequence-execute *sequence-subseq-numeric-size-call* before)))))))
   :rule-classes nil))

(local
 (defthm sequence-finish-subseq-numeric-count
   (let* ((first (proof-world-machine before))
          (slot (- (proof-stack-top before) 16))
          (after (sequence-execute *sequence-subseq-numeric-finish* before))
          (target (+ image-base *sequence-subseq-checked-offset*)))
     (implies
      (and (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers first))
           (natp image-base) (natp slot) (unsigned-byte-p 64 target)
           (equal (proof-world-pc before) (+ image-base *sequence-subseq-numeric-offset* 56))
           (proof-machine-value-p (proof-load-word slot first) datum before objects packages)
           (sequence-instruction-path *sequence-subseq-numeric-finish* (list target) before))
      (and (proof-segment-p (len *sequence-subseq-numeric-finish*) (list target) before :cut after)
           (not (proof-world-stop after))
           (equal (proof-world-pc after) target)
           (equal (proof-world-reg 19 after) (proof-world-reg 0 before))
           (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
           (equal (proof-stack-top after) slot)
           (proof-reg-value-p 0 datum after objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-world-stop)
                     (proof-value-p proof-view proof-segment-p sequence-execute
                      proof-world-pc proof-world-reg proof-world-machine proof-stack-top
                      proof-heap-base proof-load-word sequence-instruction-path))
     :use (sequence-subseq-arithmetic-finish-effects
           (:instance sequence-segment-of-instruction-path
                      (instructions *sequence-subseq-numeric-finish*)
                      (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
                      (after (sequence-execute *sequence-subseq-numeric-finish* before)))
           (:instance sequence-representation-on-identical-memory
                      (word (proof-load-word (- (proof-stack-top before) 16) (proof-world-machine before)))
                      (datum datum) (first (proof-world-machine before)) (base (proof-heap-base before))
                      (last (proof-world-machine
                             (sequence-execute *sequence-subseq-numeric-finish* before)))))))
   :rule-classes nil))

(local
 (defthm sequence-frame-and-memory-is-register-only
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-register-frame-p 28 clobbers before after)
                   (not (intersectp-equal '(23 24 25 26 27 28) clobbers))
                   (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
                   (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
                   (equal (cdr after) (cdr before)))
              (sequence-register-only-change-p before after)))
   :hints (("Goal" :in-theory (enable sequence-register-only-change-p)
            :use sequence-frame-keeps-heap-registers))
   :rule-classes nil))

(local
 (defthm sequence-reload-and-move-addition-arguments
   (let* ((first (proof-world-machine before))
          (slot (- (proof-stack-top before) 8))
          (after (sequence-execute *sequence-subseq-addition-call* before)))
     (implies (and (consp (boymoo-model::a64-registers first))
                   (natp image-base) (natp slot)
                   (equal (proof-world-pc before) (+ image-base *sequence-subseq-numeric-offset* 36))
                   (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 52))
                   (proof-heap-p before objects packages)
                   (proof-machine-value-p (proof-load-word slot first) end before objects packages)
                   (proof-reg-value-p 0 negated before objects packages))
              (and (equal (proof-world-pc after) (+ image-base *sequence-subseq-addition-offset*))
                   (equal (proof-world-reg 30 after) (+ image-base *sequence-subseq-numeric-offset* 52))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (proof-stack-top after) (proof-stack-top before))
                   (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                   (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
                   (sequence-register-only-change-p before after)
                   (proof-heap-p after objects packages)
                   (proof-reg-value-p 0 end after objects packages)
                   (proof-reg-value-p 1 negated after objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-world-stop)
                     (proof-value-p proof-view proof-heap-p sequence-execute
                      proof-world-machine proof-stack-top proof-heap-base proof-world-reg
                      proof-register-frame-p proof-load-word sequence-register-only-change-p
                      proof-preserved-heap-p proof-fixed-heap-p))
     :use (sequence-subseq-arithmetic-addition-call
           (:instance sequence-register-only-change-keeps-heap
                      (after (sequence-execute *sequence-subseq-addition-call* before)))
           (:instance sequence-frame-and-memory-is-register-only
                      (clobbers '(0 1 2))
                      (after (sequence-execute *sequence-subseq-addition-call* before)))
           (:instance sequence-representation-on-identical-memory
                      (word (proof-load-word (- (proof-stack-top before) 8) (proof-world-machine before)))
                      (datum end) (first (proof-world-machine before)) (base (proof-heap-base before))
                      (last (proof-world-machine (sequence-execute *sequence-subseq-addition-call* before))))
           (:instance sequence-representation-on-identical-memory
                      (word (proof-world-reg 0 before))
                      (datum negated) (first (proof-world-machine before)) (base (proof-heap-base before))
                      (last (proof-world-machine (sequence-execute *sequence-subseq-addition-call* before)))))))
   :rule-classes nil))

(defthm sequence-subseq-addition-precondition
  (let* ((end (sequence-end limit datum))
         (negated (boymoo-model::core-datum (proof-runtime-value 'acl2::unary-- (list start) program)))
         (target (+ image-base *sequence-subseq-addition-offset*))
         (slot (+ (proof-stack-base before) (* 8 end-index)))
         (path *sequence-subseq-addition-call*)
         (next (sequence-execute path returned)))
    (implies
     (and (proof-runtime-return-p 'acl2::unary-- (list start) program before returned
                                  old-objects new-objects packages)
          (equal (proof-world-reg 30 before) (+ image-base *sequence-subseq-numeric-offset* 36))
          (natp end-index) (< end-index (sequence-prefix-length (proof-stack-top before) before))
          (natp slot)
          (equal slot (- (proof-stack-top before) 8))
          (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                 end before old-objects packages)
          (equal (proof-world-reg 20 before) (sequence-runtime-count start))
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (natp image-base) (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 52))
          (proof-program-packages-p program packages)
          (equal (proof-label-address "prim:ACL2::BINARY-+" image-base labels) target)
          (sequence-instruction-path path (list target) returned))
     (and (proof-segment-p (len path) (list target) returned :cut next)
          (proof-runtime-pre-p 'acl2::binary-+ (list end negated) program labels image-base
                               next new-objects packages)
          (equal (proof-world-reg 30 next) (+ image-base *sequence-subseq-numeric-offset* 52))
          (equal (proof-world-reg 20 next) (sequence-runtime-count start))
          (equal (proof-world-reg 21 next) (proof-world-reg 21 before))
          (equal (proof-stack-top next) (proof-stack-top before))
          (sequence-register-only-change-p returned next))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (proof-runtime-pre-p proof-runtime-entry proof-routine-spelling
                     proof-register-arguments-p)
                    (proof-runtime-value proof-runtime-return-p proof-machine-value-p proof-reg-value-p
                     sequence-execute sequence-end sequence-runtime-count sequence-instruction-path
                     proof-segment-p proof-program-packages-p proof-label-address proof-heap-p
                     proof-world-reg proof-world-pc proof-world-stop proof-stack-top proof-stack-base
                     proof-world-machine proof-load-word sequence-prefix-length sequence-register-only-change-p))
    :use ((:instance sequence-arithmetic-return-state (routine 'acl2::unary--) (args (list start))
                     (after returned))
          (:instance sequence-runtime-return-preserves-root-slot (routine 'acl2::unary--)
                     (args (list start)) (after returned) (index end-index)
                     (datum (sequence-end limit datum)))
          (:instance sequence-reload-and-move-addition-arguments (before returned)
                     (objects new-objects) (end (sequence-end limit datum))
                     (negated (boymoo-model::core-datum
                               (proof-runtime-value 'acl2::unary-- (list start) program))))
          (:instance sequence-segment-of-instruction-path
                     (before returned) (instructions *sequence-subseq-addition-call*)
                     (after (sequence-execute *sequence-subseq-addition-call* returned))
                     (cuts (list (+ image-base *sequence-subseq-addition-offset*)))))))
  :rule-classes nil)

(defun sequence-subseq-after-addition-path (returned)
  (let* ((call *sequence-subseq-numeric-size-call*)
         (called (sequence-execute call returned)))
    (append call (sequence-subseq-size-index-path called) *sequence-subseq-numeric-finish*)))

(local
 (defthm sequence-subseq-suffix-of-checked-path
   (implies (sequence-instruction-path (append prefix suffix) cuts before)
            (sequence-instruction-path suffix cuts (sequence-execute prefix before)))
   :hints (("Goal" :in-theory (enable sequence-instruction-path sequence-execute)
            :induct (sequence-instruction-path prefix cuts before)))
   :rule-classes nil))

(local
 (defthm sequence-subseq-append-associative
   (equal (append (append first second) third) (append first second third))
   :hints (("Goal" :induct (len first)))
   :rule-classes nil))

(local
 (defthm sequence-checked-finish-after-subseq-count
   (let* ((called (sequence-execute *sequence-subseq-numeric-size-call* returned))
          (counted (sequence-execute (sequence-subseq-size-index-path called) called))
          (path (sequence-subseq-after-addition-path returned))
          (target (+ image-base *sequence-subseq-checked-offset*))
          (after (sequence-execute path returned)))
     (implies (sequence-instruction-path path (list target) returned)
              (and (sequence-instruction-path *sequence-subseq-numeric-finish* (list target) counted)
                   (equal after (sequence-execute *sequence-subseq-numeric-finish* counted)))))
   :hints
   (("Goal"
     :in-theory (disable sequence-execute sequence-instruction-path acl2::binary-append
                         sequence-subseq-size-index-path sequence-execute-append)
     :use ((:instance sequence-subseq-suffix-of-checked-path
                      (prefix (append *sequence-subseq-numeric-size-call*
                                      (sequence-subseq-size-index-path
                                       (sequence-execute *sequence-subseq-numeric-size-call* returned))))
                      (suffix *sequence-subseq-numeric-finish*)
                      (before returned)
                      (cuts (list (+ image-base *sequence-subseq-checked-offset*))))
           (:instance sequence-execute-append (world returned)
                      (first *sequence-subseq-numeric-size-call*)
                      (second (sequence-subseq-size-index-path
                               (sequence-execute *sequence-subseq-numeric-size-call* returned))))
           (:instance sequence-execute-append (world returned)
                      (first (append *sequence-subseq-numeric-size-call*
                                     (sequence-subseq-size-index-path
                                      (sequence-execute *sequence-subseq-numeric-size-call* returned))))
                      (second *sequence-subseq-numeric-finish*))
           (:instance sequence-subseq-append-associative
                      (first *sequence-subseq-numeric-size-call*)
                      (second (sequence-subseq-size-index-path
                               (sequence-execute *sequence-subseq-numeric-size-call* returned)))
                      (third *sequence-subseq-numeric-finish*)))))
   :rule-classes nil))

(local
 (defthm sequence-complete-count-of-subseq-difference
   (let* ((called (sequence-execute *sequence-subseq-numeric-size-call* returned))
          (index-path (sequence-subseq-size-index-path called))
          (path (sequence-subseq-after-addition-path returned))
          (target (+ image-base *sequence-subseq-checked-offset*))
          (link (+ image-base *sequence-subseq-numeric-offset* 56))
          (slot (- (proof-stack-top returned) 16))
          (after (sequence-execute path returned)))
     (implies
      (and (not (proof-world-stop returned))
           (consp (boymoo-model::a64-registers (proof-world-machine returned)))
           (natp slot) (natp image-base) (unsigned-byte-p 64 link) (unsigned-byte-p 64 target)
           (equal (proof-world-pc returned) (+ image-base *sequence-subseq-numeric-offset* 52))
           (proof-reg-value-p 0 difference returned objects packages)
           (proof-machine-value-p (proof-load-word slot (proof-world-machine returned))
                                  datum returned objects packages)
           (sequence-subseq-size-index-readable-p called)
           (sequence-instruction-path index-path (list link) called)
           (sequence-instruction-path path (list target) returned))
      (and (proof-segment-p (len path) (list target) returned :cut after)
           (equal (proof-world-reg 19 after) (sequence-runtime-count difference))
           (equal (proof-world-reg 20 after) (proof-world-reg 20 returned))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 returned))
           (equal (proof-stack-top after) slot)
           (proof-reg-value-p 0 datum after objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-machine-value-p proof-load-word)
                     (proof-reg-value-p proof-value-p proof-view proof-segment-p proof-world-pc
                      proof-world-machine proof-world-stop proof-world-reg proof-heap-base
                      proof-stack-top sequence-execute sequence-instruction-path sequence-runtime-count
                      sequence-subseq-size-index-path sequence-subseq-size-index-readable-p
                      sequence-subseq-after-addition-path))
     :use ((:instance sequence-count-subseq-difference (before returned))
           sequence-checked-finish-after-subseq-count
           (:instance sequence-finish-subseq-numeric-count
                      (before (sequence-execute
                               (sequence-subseq-size-index-path
                                (sequence-execute *sequence-subseq-numeric-size-call* returned))
                               (sequence-execute *sequence-subseq-numeric-size-call* returned))))
           (:instance sequence-subseq-arithmetic-finish-effects
                      (before (sequence-execute
                               (sequence-subseq-size-index-path
                                (sequence-execute *sequence-subseq-numeric-size-call* returned))
                               (sequence-execute *sequence-subseq-numeric-size-call* returned))))
           (:instance sequence-representation-on-identical-memory
                      (base (proof-heap-base returned)) (first (proof-world-machine returned))
                      (word (proof-load-word (- (proof-stack-top returned) 16) (proof-world-machine returned)))
                      (last (proof-world-machine
                             (sequence-execute
                              (sequence-subseq-size-index-path
                               (sequence-execute *sequence-subseq-numeric-size-call* returned))
                              (sequence-execute *sequence-subseq-numeric-size-call* returned)))))
           (:instance sequence-segment-of-instruction-path
                      (before returned) (instructions (sequence-subseq-after-addition-path returned))
                      (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
                      (after (sequence-execute (sequence-subseq-after-addition-path returned) returned))))))
   :rule-classes nil))

(defthm sequence-subseq-size-from-addition-return
  (let* ((end (sequence-end limit datum))
         (args (list end (boymoo-model::core-datum (proof-runtime-value 'acl2::unary-- (list start) program))))
         (difference (- end start))
         (path (sequence-subseq-after-addition-path returned))
         (target (+ image-base *sequence-subseq-checked-offset*))
         (index-call (sequence-execute *sequence-subseq-numeric-size-call* returned))
         (slot (+ (proof-stack-base before) (* 8 source-index)))
         (after (sequence-execute path returned)))
    (implies
     (and (proof-runtime-return-p 'acl2::binary-+ args program before returned old-objects new-objects packages)
          (equal (proof-world-reg 30 before) (+ image-base *sequence-subseq-numeric-offset* 52))
          (natp source-index) (< source-index (sequence-prefix-length (proof-stack-top before) before))
          (natp slot) (equal slot (- (proof-stack-top before) 16))
          (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                 datum before old-objects packages)
          (equal (proof-world-reg 20 before) (sequence-runtime-count start))
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (natp image-base)
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-numeric-offset* 56))
          (unsigned-byte-p 64 target)
          (sequence-subseq-size-index-readable-p index-call)
          (sequence-instruction-path (sequence-subseq-size-index-path index-call)
                                     (list (+ image-base *sequence-subseq-numeric-offset* 56)) index-call)
          (sequence-instruction-path path (list target) returned))
     (and (proof-segment-p (len path) (list target) returned :cut after)
          (equal (proof-world-reg 19 after) (sequence-runtime-count difference))
          (implies (< (proof-world-reg 19 after) *proof-space-size*)
                   (equal (proof-world-reg 19 after) (sequence-result-size datum start limit)))
          (equal (proof-world-reg 20 after) (sequence-runtime-count start))
          (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
          (equal (proof-stack-top after) slot)
          (proof-reg-value-p 0 datum after new-objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-result-size)
                    (proof-runtime-return-p proof-runtime-value proof-machine-value-p proof-reg-value-p
                     proof-segment-p proof-world-pc proof-world-machine proof-world-reg proof-world-stop
                     proof-stack-base proof-stack-top proof-load-word sequence-prefix-length sequence-end
                     sequence-runtime-count sequence-count sequence-runtime-count-exact-for-bounded-size
                     sequence-subseq-arithmetic-result sequence-subseq-after-addition-path
                     sequence-subseq-size-index-readable-p sequence-subseq-size-index-path
                     sequence-instruction-path sequence-execute))
    :use (sequence-subseq-arithmetic-result
          (:instance sequence-arithmetic-return-state (routine 'acl2::binary-+) (after returned)
                     (args (list (sequence-end limit datum)
                                 (boymoo-model::core-datum (proof-runtime-value 'acl2::unary-- (list start) program)))))
          (:instance sequence-runtime-return-preserves-root-slot (routine 'acl2::binary-+) (after returned)
                     (args (list (sequence-end limit datum)
                                 (boymoo-model::core-datum (proof-runtime-value 'acl2::unary-- (list start) program))))
                     (index source-index))
          (:instance sequence-complete-count-of-subseq-difference (objects new-objects)
                     (difference (- (sequence-end limit datum) start)))
          (:instance sequence-runtime-count-exact-for-bounded-size (value (- (sequence-end limit datum) start))))))
  :rule-classes nil)
