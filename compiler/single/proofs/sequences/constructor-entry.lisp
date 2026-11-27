(in-package "BOYMOO-PROOFS")

(include-book "constructor-calls")
(include-book "call-segments")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-small-constructor-entry-p (image-base before)
  (and (not (proof-world-stop before))
       (consp (boymoo-model::a64-registers (proof-world-machine before)))
       (natp image-base)
       (equal (proof-world-pc before) (+ image-base *sequence-new-string-offset*))
       (unsigned-byte-p 64 (+ image-base *sequence-new-string-offset* 32))
       (unsigned-byte-p 18 (proof-world-reg 0 before))
       (<= 16 (boymoo-model::a64-sp (proof-world-machine before)))
       (<= (boymoo-model::a64-sp (proof-world-machine before))
           (+ (- (proof-machine-limit before) *proof-machine-margin*)
              *proof-machine-reservation*))))

(defun sequence-small-constructor-continuation-after (before returned)
  (sequence-execute (sequence-small-string-finish-path (proof-world-reg 0 before)) returned))

(defun sequence-small-constructor-step-count (fuel before)
  (let* ((call (sequence-execute *sequence-small-string-request* before))
         (cuts (list (proof-world-reg 30 call) (proof-world-reg 30 before))))
    (+ (len *sequence-small-string-request*)
       (sequence-segment-count fuel cuts call)
       (len (sequence-small-string-finish-path (proof-world-reg 0 before))))))

(local
 (defthm sequence-string-saved-frame-at-allocation
   (let* ((call (sequence-execute *sequence-small-string-request* before))
          (machine (proof-world-machine call))
          (stack (boymoo-model::a64-sp machine))
          (end (+ (- (proof-machine-limit call) *proof-machine-margin*)
                  *proof-machine-reservation*)))
     (implies
      (and (sequence-small-constructor-entry-p image-base before)
           (sequence-instruction-path *sequence-small-string-request*
                                      (list (+ image-base *sequence-header-allocator-offset*)) before))
      (and (proof-subspan-p stack 16 stack end)
           (unsigned-byte-p 64 (+ stack 16))
           (equal (proof-load-word stack machine) (proof-world-reg 0 before))
           (equal (proof-load-word (+ stack 8) machine) (proof-world-reg 30 before)))))
   :hints (("Goal"
            :in-theory (disable proof-load-word proof-world-machine proof-world-reg proof-world-pc
                                proof-segment-p proof-machine-limit sequence-small-string-allocation)
            :use (sequence-small-string-allocation-request sequence-small-string-call-to-allocator)))
   :rule-classes nil))

(defthm sequence-small-string-from-entry
  (let* ((length (proof-world-reg 0 before))
         (call (sequence-execute *sequence-small-string-request* before))
         (path (sequence-small-string-finish-path length))
         (after (sequence-small-constructor-continuation-after before returned))
         (cuts (list (proof-world-reg 30 before)))
         (link (proof-world-reg 30 call))
         (published (cons (proof-object (proof-world-reg 0 returned) :active :header 0) new-objects)))
    (implies
     (and (sequence-small-constructor-entry-p image-base before)
          (sequence-instruction-path *sequence-small-string-request*
                                     (list (+ image-base *sequence-header-allocator-offset*)) before)
          (sequence-instruction-path *sequence-small-string-request* cuts before)
          (proof-segment-p fuel (cons link cuts) call :cut returned)
          (not (equal link (proof-world-reg 30 before)))
          (proof-allocator-return-p :header (sequence-small-string-allocation length)
                                    call returned old-objects new-objects packages)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path path cuts returned))
     (and (proof-segment-p (sequence-small-constructor-step-count fuel before) cuts before :cut after)
          (proof-string-result-p length after published packages))))
  :hints
  (("Goal"
    :in-theory (disable proof-load-word proof-world-machine proof-world-reg proof-world-pc
                        proof-world-stop proof-segment-p proof-string-result-p
                        proof-preserved-heap-p proof-reserved-span-p proof-register-frame-p
                        sequence-segment-count sequence-small-string-allocation sequence-small-string-finish-path)
    :use (sequence-string-saved-frame-at-allocation
          (:instance sequence-small-string-after-allocator
                     (before (sequence-execute *sequence-small-string-request* before)))
          (:instance sequence-append-returning-call
                     (cuts (list (proof-world-reg 30 before)))
                     (link (proof-world-reg 30 (sequence-execute *sequence-small-string-request* before)))
                     (before (sequence-execute *sequence-small-string-request* before)) (middle returned)
                     (suffix (len (sequence-small-string-finish-path (proof-world-reg 0 before))))
                     (reason :cut) (after (sequence-small-constructor-continuation-after before returned)))
          (:instance sequence-append-checked-instructions
                     (instructions *sequence-small-string-request*) (cuts (list (proof-world-reg 30 before)))
                     (suffix (+ (sequence-segment-count
                                 fuel
                                 (list (proof-world-reg 30 (sequence-execute *sequence-small-string-request* before))
                                       (proof-world-reg 30 before))
                                 (sequence-execute *sequence-small-string-request* before))
                                (len (sequence-small-string-finish-path (proof-world-reg 0 before)))))
                     (reason :cut) (after (sequence-small-constructor-continuation-after before returned))))))
  :rule-classes nil)

(defthm sequence-empty-string-from-entry
  (let* ((new-string (sequence-execute *sequence-empty-string-dispatch* before))
         (call (sequence-execute *sequence-small-string-request* new-string))
         (after (sequence-small-constructor-continuation-after new-string returned))
         (cuts (list (proof-world-reg 30 before)))
         (link (proof-world-reg 30 call))
         (published (cons (proof-object (proof-world-reg 0 returned) :active :header 0) new-objects)))
    (implies
     (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-empty-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-empty-string-offset* 8))
          (sequence-instruction-path *sequence-empty-string-dispatch* cuts before)
          (sequence-small-constructor-entry-p image-base new-string)
          (sequence-instruction-path *sequence-small-string-request*
                                     (list (+ image-base *sequence-header-allocator-offset*)) new-string)
          (sequence-instruction-path *sequence-small-string-request* cuts new-string)
          (proof-segment-p fuel (cons link cuts) call :cut returned)
          (not (equal link (proof-world-reg 30 before)))
          (proof-allocator-return-p :header (sequence-small-string-allocation 0)
                                    call returned old-objects new-objects packages)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path (sequence-small-string-finish-path 0) cuts returned))
     (and (proof-segment-p (+ (len *sequence-empty-string-dispatch*)
                              (sequence-small-constructor-step-count fuel new-string))
                           cuts before :cut after)
          (proof-string-result-p 0 after published packages))))
  :hints
  (("Goal"
    :in-theory (disable proof-string-result-p proof-segment-p proof-allocator-return-p
                        sequence-small-constructor-entry-p sequence-small-constructor-continuation-after
                        sequence-small-string-allocation sequence-small-string-finish-path
                        sequence-segment-count sequence-small-constructor-step-count)
    :use (sequence-empty-string-tail-call
          (:instance sequence-small-string-from-entry
                     (before (sequence-execute *sequence-empty-string-dispatch* before)))
          (:instance sequence-append-checked-instructions
                     (instructions *sequence-empty-string-dispatch*) (cuts (list (proof-world-reg 30 before)))
                     (suffix (sequence-small-constructor-step-count
                              fuel (sequence-execute *sequence-empty-string-dispatch* before)))
                     (reason :cut)
                     (after (sequence-small-constructor-continuation-after
                             (sequence-execute *sequence-empty-string-dispatch* before) returned))))))
  :rule-classes nil)

(defconst *sequence-string-constructor-clobbers* (append *proof-volatile-registers* '(26 27)))

(local
 (defthm sequence-small-allocator-keeps-return-frame
   (implies (proof-allocator-return-p :header bytes before after old-objects new-objects packages)
            (and (proof-register-frame-p 29 *sequence-string-constructor-clobbers* before after)
                 (equal (boymoo-model::a64-sp (proof-world-machine before))
                        (boymoo-model::a64-sp (proof-world-machine after)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-allocator-return-p proof-frame-return-p)
                     (proof-preserved-heap-p proof-reserved-span-p proof-register-frame-p))
     :use ((:instance sequence-register-frame-on-prefix
                      (limit 30) (prefix 29) (clobbers *sequence-string-constructor-clobbers*)))))
   :rule-classes nil))

(local
 (defthm sequence-small-constructor-restore-frame
   (implies
    (and (not (proof-world-stop before)) (not (proof-world-stop after))
         (equal (proof-world-pc after) (proof-world-reg 30 before))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 29 *sequence-string-constructor-clobbers* before after))
    (proof-frame-return-p *sequence-string-constructor-clobbers* t before after))
   :hints
   (("Goal"
     :in-theory (e/d (proof-frame-return-p) (proof-register-frame-p))
     :expand ((proof-register-frame-p 30 *sequence-string-constructor-clobbers* before after))))
   :rule-classes nil))

(defthm sequence-small-string-restores-call-frame
  (let* ((length (proof-world-reg 0 before))
         (called (sequence-execute *sequence-small-string-request* before))
         (path (sequence-small-string-finish-path length))
         (after (sequence-small-constructor-continuation-after before returned)))
    (implies
     (and (sequence-small-constructor-entry-p image-base before)
          (sequence-instruction-path *sequence-small-string-request*
                                     (list (+ image-base *sequence-header-allocator-offset*)) before)
          (proof-allocator-return-p :header (sequence-small-string-allocation length)
                                    called returned old-objects new-objects packages)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path path (list (proof-world-reg 30 before)) returned))
     (proof-frame-return-p *sequence-string-constructor-clobbers* t before after)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable proof-allocator-return-p proof-frame-return-p
                        proof-load-word proof-world-machine proof-world-reg proof-world-stop
                        proof-world-pc proof-register-frame-p proof-segment-p proof-heap-p
                        proof-preserved-heap-p proof-reserved-span-p proof-string-result-p sequence-execute
                        sequence-small-string-allocation sequence-small-string-finish-path
                        sequence-instruction-path)
    :use (sequence-string-saved-frame-at-allocation sequence-small-string-allocation-request
          (:instance sequence-small-string-after-allocator
                     (before (sequence-execute *sequence-small-string-request* before)))
          (:instance sequence-small-constructor-restore-frame
                     (after (sequence-small-constructor-continuation-after before returned)))
          (:instance sequence-register-frame-with-more-clobbers
                     (limit 29) (old '(0 1)) (new *sequence-string-constructor-clobbers*)
                     (after (sequence-execute *sequence-small-string-request* before)))
          (:instance sequence-small-allocator-keeps-return-frame
                     (bytes (sequence-small-string-allocation (proof-world-reg 0 before)))
                     (before (sequence-execute *sequence-small-string-request* before)) (after returned))
          (:instance sequence-register-frame-with-more-clobbers
                     (limit 29) (old '(0 1 2 3)) (new *sequence-string-constructor-clobbers*)
                     (before returned) (after (sequence-small-constructor-continuation-after before returned)))
          (:instance sequence-register-frame-transitive
                     (limit 29) (clobbers *sequence-string-constructor-clobbers*)
                     (middle (sequence-execute *sequence-small-string-request* before)) (after returned))
          (:instance sequence-register-frame-transitive
                     (limit 29) (clobbers *sequence-string-constructor-clobbers*)
                     (middle returned) (after (sequence-small-constructor-continuation-after before returned))))))
  :rule-classes nil)

(defthm sequence-small-string-constructor-with-publication
  (let* ((length (proof-world-reg 0 before))
         (called (sequence-execute *sequence-small-string-request* before))
         (path (sequence-small-string-finish-path length))
         (after (sequence-small-constructor-continuation-after before returned))
         (cuts (list (proof-world-reg 30 before)))
         (link (proof-world-reg 30 called))
         (published (cons (proof-object (proof-world-reg 0 returned) :active :header 0) new-objects)))
    (implies
     (and (sequence-small-constructor-entry-p image-base before)
          (sequence-instruction-path *sequence-small-string-request*
                                     (list (+ image-base *sequence-header-allocator-offset*)) before)
          (sequence-instruction-path *sequence-small-string-request* cuts before)
          (proof-segment-p fuel (cons link cuts) called :cut returned)
          (not (equal link (proof-world-reg 30 before)))
          (proof-allocator-return-p :header (sequence-small-string-allocation length)
                                    called returned old-objects new-objects packages)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path path cuts returned)
          (proof-preserved-heap-p nil before after old-objects published packages))
     (and (proof-segment-p (sequence-small-constructor-step-count fuel before) cuts before :cut after)
          (proof-string-constructor-return-p length before after old-objects published packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-string-constructor-return-p)
                    (proof-frame-return-p proof-preserved-heap-p proof-string-result-p
                     proof-segment-p proof-world-machine proof-world-reg sequence-execute
                     proof-allocator-return-p sequence-small-constructor-entry-p
                     sequence-small-constructor-continuation-after sequence-small-constructor-step-count
                     sequence-small-string-allocation sequence-small-string-finish-path
                     sequence-instruction-path))
    :use (sequence-small-string-restores-call-frame sequence-small-string-from-entry)))
  :rule-classes nil)

(local
 (defthm sequence-empty-string-preserves-constructor-frame
   (let ((entered (sequence-execute *sequence-empty-string-dispatch* before)))
     (implies
      (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-empty-string-offset*))
           (unsigned-byte-p 64 (+ image-base *sequence-empty-string-offset* 8))
           (proof-frame-return-p *sequence-string-constructor-clobbers* t entered after))
      (proof-frame-return-p *sequence-string-constructor-clobbers* t before after)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-frame-return-p)
                     (proof-register-frame-p proof-world-machine proof-world-reg proof-world-pc
                      proof-world-stop sequence-execute))
     :use (sequence-empty-string-tail-call
           (:instance sequence-register-frame-with-more-clobbers
                      (limit 30) (old '(0)) (new *sequence-string-constructor-clobbers*)
                      (after (sequence-execute *sequence-empty-string-dispatch* before)))
           (:instance sequence-register-frame-transitive
                      (limit 30) (clobbers *sequence-string-constructor-clobbers*)
                      (middle (sequence-execute *sequence-empty-string-dispatch* before))))))
   :rule-classes nil))

(defthm sequence-empty-string-constructor-with-publication
  (let* ((entered (sequence-execute *sequence-empty-string-dispatch* before))
         (called (sequence-execute *sequence-small-string-request* entered))
         (after (sequence-small-constructor-continuation-after entered returned))
         (cuts (list (proof-world-reg 30 before)))
         (link (proof-world-reg 30 called))
         (published (cons (proof-object (proof-world-reg 0 returned) :active :header 0) new-objects)))
    (implies
     (and (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-empty-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-empty-string-offset* 8))
          (sequence-instruction-path *sequence-empty-string-dispatch* cuts before)
          (sequence-small-constructor-entry-p image-base entered)
          (sequence-instruction-path *sequence-small-string-request*
                                     (list (+ image-base *sequence-header-allocator-offset*)) entered)
          (sequence-instruction-path *sequence-small-string-request* cuts entered)
          (proof-segment-p fuel (cons link cuts) called :cut returned)
          (not (equal link (proof-world-reg 30 before)))
          (proof-allocator-return-p :header (sequence-small-string-allocation 0)
                                    called returned old-objects new-objects packages)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path (sequence-small-string-finish-path 0) cuts returned)
          (proof-preserved-heap-p nil before after old-objects published packages))
     (and (proof-segment-p (+ (len *sequence-empty-string-dispatch*)
                              (sequence-small-constructor-step-count fuel entered))
                           cuts before :cut after)
          (proof-string-constructor-return-p 0 before after old-objects published packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-string-constructor-return-p)
                    (proof-frame-return-p proof-preserved-heap-p proof-string-result-p proof-segment-p
                     proof-world-machine proof-world-reg proof-world-stop proof-world-pc proof-register-frame-p
                     sequence-execute proof-allocator-return-p sequence-small-constructor-entry-p
                     sequence-small-constructor-continuation-after sequence-small-constructor-step-count
                     sequence-small-string-allocation sequence-small-string-finish-path
                     sequence-instruction-path))
    :use (sequence-empty-string-from-entry sequence-empty-string-tail-call
          (:instance sequence-small-string-restores-call-frame
                     (before (sequence-execute *sequence-empty-string-dispatch* before)))
          (:instance sequence-empty-string-preserves-constructor-frame
                     (after (sequence-small-constructor-continuation-after
                             (sequence-execute *sequence-empty-string-dispatch* before) returned))))))
  :rule-classes nil)
