(in-package "BOYMOO-PROOFS")

(include-book "coerce-dispatch")
(include-book "root-prefix")
(include-book "coerce-list")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-coerce-list-loop-offset* (sequence-offset "rt:coerce-list-loop"))

(sequence-defpath *sequence-coerce-list-view-after-allocation*
  ("prim:COMMON-LISP::COERCE" 33 4))

(sequence-defpath *sequence-coerce-list-initialize-tail*
  ("prim:COMMON-LISP::COERCE" 37 1))

(defthm sequence-coerce-list-reload-then-view
  (let* ((machine (proof-world-machine before))
         (slot (- (proof-stack-top before) 8))
         (after (sequence-execute *sequence-coerce-list-view-after-allocation* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base) (natp slot)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset* 132))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-offset* 148)))
     (and (equal (proof-world-pc after) (+ image-base (sequence-offset "rt:string-view")))
          (equal (proof-world-reg 30 after) (+ image-base *sequence-coerce-offset* 148))
          (equal (proof-world-reg 0 after) (proof-load-word slot machine))
          (equal (proof-world-reg 5 after) (proof-world-reg 0 before))
          (equal (proof-stack-top after) slot)
          (equal (proof-heap-base after) (proof-heap-base before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)))
  :rule-classes nil)

(defun sequence-coerce-reloaded-view-path (before)
  (let* ((called (sequence-execute *sequence-coerce-list-view-after-allocation* before)))
    (sequence-string-view-path (proof-world-reg 0 called) (proof-heap-base called)
                               (proof-world-machine called))))

(defun sequence-coerce-list-resume-path (before)
  (append *sequence-coerce-list-view-after-allocation*
          (sequence-coerce-reloaded-view-path before)
          *sequence-coerce-list-initialize-tail*))

(local
 (defthm sequence-coerce-initial-list-tail-effects
   (let* ((machine (proof-world-machine before))
          (after (sequence-execute *sequence-coerce-list-initialize-tail* before)))
     (implies (and (consp (boymoo-model::a64-registers machine))
                   (unsigned-byte-p 64 (+ 4 (proof-world-pc before))))
              (and (equal (proof-world-reg 0 after) *proof-nil*)
                   (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                   (equal (proof-world-reg 2 after) (proof-world-reg 2 before))
                   (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
                   (equal (proof-world-pc after) (+ 4 (proof-world-pc before)))
                   (equal (proof-stack-top after) (proof-stack-top before))
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (consp (boymoo-model::a64-registers (proof-world-machine after)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory machine)))))
   :hints (("Goal" :in-theory (enable sequence-execute)))
   :rule-classes nil))

(local
 (defthm sequence-coerce-list-resume-execution-order
   (let* ((called (sequence-execute *sequence-coerce-list-view-after-allocation* before))
          (view (sequence-coerce-reloaded-view-path before))
          (returned (sequence-execute view called)))
     (equal (sequence-execute (sequence-coerce-list-resume-path before) before)
            (sequence-execute *sequence-coerce-list-initialize-tail* returned)))
   :hints
   (("Goal"
     :in-theory (disable sequence-execute sequence-coerce-reloaded-view-path acl2::binary-append
                         sequence-execute-append)
     :use ((:instance sequence-execute-append (world before)
                      (first *sequence-coerce-list-view-after-allocation*)
                      (second (append (sequence-coerce-reloaded-view-path before)
                                      *sequence-coerce-list-initialize-tail*)))
           (:instance sequence-execute-append
                      (world (sequence-execute *sequence-coerce-list-view-after-allocation* before))
                      (first (sequence-coerce-reloaded-view-path before))
                      (second *sequence-coerce-list-initialize-tail*)))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-reloaded-string-shape
   (let* ((address (proof-pointer-address word base))
          (payload (+ address 8))
          (count (len (coerce datum 'list))))
     (implies (and (stringp datum) (posp count)
                   (proof-value-p word datum base objects packages machine))
              (and (proof-span-p payload count)
                   (equal (proof-load-string count payload machine) datum))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-value-p proof-view)
                     (proof-view-step proof-load-string proof-pointer-address
                      sequence-load-string-characters sequence-load-string-length))
     :use ((:instance sequence-string-view-of-represented-value
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address word base) objects))))))
           (:instance sequence-load-string-length
                      (count (proof-header-size (proof-load-word (proof-pointer-address word base) machine)))
                      (address (+ 8 (proof-pointer-address word base)))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-list-resume-from-live-root
   (let* ((machine (proof-world-machine before))
          (base (proof-heap-base before))
          (slot (- (proof-stack-top before) 8))
          (word (proof-load-word slot machine))
          (called (sequence-execute *sequence-coerce-list-view-after-allocation* before))
          (view (sequence-coerce-reloaded-view-path before))
          (after (sequence-execute (sequence-coerce-list-resume-path before) before)))
     (implies
      (and (stringp datum) (posp (len (coerce datum 'list)))
           (proof-machine-value-p word datum before objects packages)
           (natp slot) (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset* 132))
           (unsigned-byte-p 64 (+ image-base *sequence-coerce-list-loop-offset*))
           (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers machine))
           (sequence-instruction-path view (list (+ image-base *sequence-coerce-offset* 148)) called))
      (and (equal (proof-world-pc after) (+ image-base *sequence-coerce-list-loop-offset*))
           (not (proof-world-stop after))
           (consp (boymoo-model::a64-registers (proof-world-machine after)))
           (equal (proof-world-reg 0 after) *proof-nil*)
           (equal (proof-world-reg 5 after) (proof-world-reg 0 before))
           (equal (proof-stack-top after) slot)
           (equal (proof-heap-base after) base)
           (equal (proof-world-reg 2 after) (len (coerce datum 'list)))
           (equal (proof-world-reg 1 after) (+ 8 (proof-pointer-address word base)))
           (proof-span-p (proof-world-reg 1 after) (proof-world-reg 2 after))
           (equal (proof-load-string (proof-world-reg 2 after) (proof-world-reg 1 after) (proof-world-machine after))
                  datum)
           (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-machine-value-p proof-value-p proof-frame-return-p proof-stack-top proof-heap-base)
                     (proof-view proof-load-word proof-load-string proof-pointer-address
                      proof-world-machine proof-world-reg proof-world-stop proof-world-pc proof-register-frame-p
                      proof-segment-p sequence-execute sequence-string-view-path sequence-coerce-list-resume-path
                      sequence-coerce-reloaded-view-path sequence-instruction-path))
     :expand ((sequence-coerce-reloaded-view-path before))
     :use
     (sequence-coerce-list-resume-execution-order sequence-coerce-list-reload-then-view
      (:instance sequence-view-of-equal-memory
                 (word (proof-load-word (- (proof-stack-top before) 8) (proof-world-machine before)))
                 (base (proof-heap-base before)) (first (proof-world-machine before))
                 (last (proof-world-machine (sequence-execute *sequence-coerce-list-view-after-allocation* before))))
      (:instance sequence-coerce-reloaded-string-shape
                 (word (proof-load-word (- (proof-stack-top before) 8) (proof-world-machine before)))
                 (base (proof-heap-base before)) (machine (proof-world-machine before)))
      (:instance sequence-string-view-field-contract
                 (before (sequence-execute *sequence-coerce-list-view-after-allocation* before)))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 5)
                 (before (sequence-execute *sequence-coerce-list-view-after-allocation* before))
                 (after (sequence-execute (sequence-coerce-reloaded-view-path before)
                                          (sequence-execute *sequence-coerce-list-view-after-allocation* before))))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 25)
                 (before (sequence-execute *sequence-coerce-list-view-after-allocation* before))
                 (after (sequence-execute (sequence-coerce-reloaded-view-path before)
                                          (sequence-execute *sequence-coerce-list-view-after-allocation* before))))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 28)
                 (before (sequence-execute *sequence-coerce-list-view-after-allocation* before))
                 (after (sequence-execute (sequence-coerce-reloaded-view-path before)
                                          (sequence-execute *sequence-coerce-list-view-after-allocation* before))))
      (:instance sequence-coerce-initial-list-tail-effects
                 (before (sequence-execute (sequence-coerce-reloaded-view-path before)
                                           (sequence-execute *sequence-coerce-list-view-after-allocation* before))))
      (:instance sequence-load-string-of-equal-memory
                 (count (len (coerce datum 'list)))
                 (address (+ 8 (proof-pointer-address
                                (proof-load-word (- (proof-stack-top before) 8) (proof-world-machine before))
                                (proof-heap-base before))))
                 (first (proof-world-machine before))
                 (last (proof-world-machine (sequence-execute (sequence-coerce-list-resume-path before) before)))))))
   :rule-classes nil))

(local
 (defthm sequence-cell-allocation-preserves-root-location
   (implies (proof-allocator-return-p :cons bytes before after old-objects new-objects packages)
            (and (proof-prefix-preserved-p (proof-stack-top before) before after old-objects new-objects packages)
                 (equal (proof-stack-top after) (proof-stack-top before))
                 (equal (proof-stack-base after) (proof-stack-base before))
                 (equal (proof-heap-base after) (proof-heap-base before))
                 (not (proof-world-stop after))
                 (equal (proof-world-pc after) (proof-world-reg 30 before))
                 (proof-reserved-span-p :cons (proof-world-reg 0 after) bytes after new-objects)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-allocator-return-p proof-frame-return-p proof-preserved-heap-p
                      proof-heap-frame-p proof-stack-top)
                     (proof-heap-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                      proof-memory-span-agrees-p proof-streams-preserved-p proof-stack-base
                      proof-heap-base proof-reserved-span-p proof-register-frame-p))
     :use ((:instance sequence-register-in-frame (limit 30) (register 25)
                      (clobbers (append *proof-volatile-registers* '(26 27)))))))
   :rule-classes nil))

(defthm sequence-coerce-list-ready-from-allocator
  (let* ((count (len (coerce datum 'list)))
         (slot (+ (proof-stack-base before) (* 8 index)))
         (called (sequence-execute *sequence-coerce-list-view-after-allocation* returned))
         (path (sequence-coerce-list-resume-path returned))
         (target (+ image-base *sequence-coerce-list-loop-offset*))
         (after (sequence-execute path returned)))
    (implies
     (and (stringp datum) (posp count)
          (proof-allocator-return-p :cons (* 16 count) before returned old-objects new-objects packages)
          (equal (proof-world-reg 30 before) (+ image-base *sequence-coerce-offset* 132))
          (natp index) (< index (sequence-prefix-length (proof-stack-top before) before))
          (natp slot) (equal slot (- (proof-stack-top before) 8))
          (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                 datum before old-objects packages)
          (natp image-base) (unsigned-byte-p 64 target)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path (sequence-coerce-reloaded-view-path returned)
                                     (list (+ image-base *sequence-coerce-offset* 148)) called)
          (sequence-instruction-path path (list target) returned))
     (and (proof-segment-p (len path) (list target) returned :cut after)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (proof-stack-top after) slot)
          (equal (proof-world-reg 0 after) *proof-nil*)
          (equal (proof-world-reg 2 after) count)
          (equal (proof-world-reg 5 after) (proof-world-reg 0 returned))
          (proof-span-p (proof-world-reg 1 after) count)
          (equal (proof-load-string count (proof-world-reg 1 after) (proof-world-machine after)) datum)
          (proof-reserved-span-p :cons (proof-world-reg 5 after) (* 16 count) returned new-objects)
          (equal (proof-heap-base after) (proof-heap-base returned))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory (proof-world-machine returned))))))
  :hints
  (("Goal"
    :in-theory (disable proof-allocator-return-p proof-heap-p proof-segment-p proof-reserved-span-p
                        proof-prefix-preserved-p proof-stack-prefix proof-machine-value-p proof-view
                        proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                        proof-stack-base proof-stack-top proof-load-word proof-load-string proof-span-p
                        sequence-coerce-reloaded-view-path sequence-coerce-list-resume-path sequence-prefix-length
                        sequence-execute sequence-instruction-path)
    :use ((:instance sequence-cell-allocation-preserves-root-location (bytes (* 16 (len (coerce datum 'list))))
                     (after returned))
          (:instance sequence-root-view-in-preserved-prefix (top (proof-stack-top before)) (after returned))
          (:instance sequence-coerce-list-resume-from-live-root (before returned) (objects new-objects))
          (:instance sequence-segment-of-instruction-path
                     (before returned) (instructions (sequence-coerce-list-resume-path returned))
                     (cuts (list (+ image-base *sequence-coerce-list-loop-offset*)))
                     (after (sequence-execute (sequence-coerce-list-resume-path returned) returned))))))
  :rule-classes nil)
