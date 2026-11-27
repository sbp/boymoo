(in-package "BOYMOO-PROOFS")

(include-book "frame")
(include-book "handoff")
(include-book "retirement")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-saved-frame-offset (register)
  (case register
    (0 0) (1 8) (29 16) (30 24) (21 32) (22 40) (19 48) (20 56)))

(defun collection-finish-tail-trace (headerp origin)
  (collection-linux-trace "rt:collect-finish"
                          (if headerp '(37 38 39 40 41 42) '(37 38 39 40 41)) origin))

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc proof-world-machine
                     proof-reg proof-load-word collection-cpu-p collection-write-register
                     collection-write-word collection-read-word collection-write-pc collection-write-sp
                     boymoo-model::a64-unsigned boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-read-bytes (:definition ash))))

(defun collection-final-restore-input-p (origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin (car *collection-linux-layout*))
       (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:collect-finish") 148))
       (unsigned-byte-p 64 (+ 64 (boymoo-model::a64-sp (proof-world-machine world))))))

(defthm collection-finish-tail-restores-saved-registers-and-request
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (slot (collection-saved-frame-offset register))
         (headerp (equal (collection-read-word (+ sp 8) world) 0))
         (next (collection-trace-effect (collection-finish-tail-trace headerp origin) world)))
    (implies (collection-final-restore-input-p origin world)
             (and (equal (proof-world-pc next)
                         (+ origin (collection-linux-offset (if headerp "rt:alloc" "rt:alloc-cells"))))
                  (equal (boymoo-model::a64-sp (proof-world-machine next)) (+ sp 64))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop next) (proof-world-stop world))
                  (equal (proof-world-regions next) (proof-world-regions world))
                  (equal (proof-world-replies next) (proof-world-replies world))
                  (proof-streams-preserved-p world next)
                  (equal (proof-world-reg register next)
                         (if slot (collection-read-word (+ sp slot) world)
                           (proof-world-reg register world))))))
  :hints (("Goal" :cases ((equal (collection-read-word (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))
                                                      world) 0)))))

(defthm collection-finish-tail-restores-all-frame-words
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (after (collection-trace-effect (collection-finish-tail-trace headerp origin) world)))
    (implies (and (collection-final-restore-input-p origin world)
                  (equal headerp (equal (collection-read-word (+ sp 8) world) 0)))
             (and (equal (proof-world-pc after)
                         (+ origin (collection-linux-offset (if headerp "rt:alloc" "rt:alloc-cells"))))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ sp 64))
                  (equal (collection-saved-registers after) (collection-frame-words sp world)))))
  :hints (("Goal" :cases (headerp))))

(defconst *collection-saved-frame-registers* '(0 1 19 20 21 22 29 30))

(local
 (defthm collection-named-frame-slot-is-present
   (iff (collection-saved-frame-offset register)
        (member-equal register *collection-saved-frame-registers*))))

(local
 (defthm collection-named-frame-slot-contains-original-register
   (let ((slot (collection-saved-frame-offset register)))
     (implies (and (integerp sp) slot
                   (equal (collection-frame-words sp world) (collection-saved-registers before)))
              (equal (collection-read-word (+ sp slot) world) (proof-world-reg register before))))))

(local
 (in-theory (disable collection-final-restore-input-p collection-frame-words collection-saved-registers
                     collection-saved-frame-offset collection-finish-tail-trace collection-trace-effect)))

(local
 (defthm collection-finish-tail-restores-or-keeps-one-register
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
          (headerp (equal (collection-read-word (+ sp 8) world) 0))
          (after (collection-trace-effect (collection-finish-tail-trace headerp origin) world)))
     (implies (and (collection-final-restore-input-p origin world)
                   (equal (collection-frame-words sp world) (collection-saved-registers before))
                   (or (member-equal register *collection-saved-frame-registers*)
                       (equal (proof-world-reg register world) (proof-world-reg register before))))
              (equal (proof-world-reg register after) (proof-world-reg register before))))
   :hints (("Goal"
            :use ((:instance collection-finish-tail-restores-saved-registers-and-request)
                  (:instance collection-named-frame-slot-contains-original-register
                             (sp (boymoo-model::a64-sp (proof-world-machine world)))))
            :in-theory (disable collection-finish-tail-restores-saved-registers-and-request
                                collection-named-frame-slot-contains-original-register)))))

(local
 (defun collection-restore-register-induction (bound)
   (declare (xargs :measure (nfix bound)))
   (if (zp bound)
       bound
     (collection-restore-register-induction (1- bound)))))

(defthm collection-finish-tail-reestablishes-register-frame
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (headerp (equal (collection-read-word (+ sp 8) world) 0))
         (after (collection-trace-effect (collection-finish-tail-trace headerp origin) world)))
    (implies (and (collection-final-restore-input-p origin world)
                  (equal (collection-frame-words sp world) (collection-saved-registers before))
                  (proof-register-frame-p bound (append *collection-saved-frame-registers* clobbers) before world))
             (proof-register-frame-p bound clobbers before after)))
  :hints (("Goal" :induct (collection-restore-register-induction bound)
                  :in-theory (disable collection-finish-tail-restores-saved-registers-and-request
                                      collection-named-frame-slot-contains-original-register
                                      collection-finish-tail-restores-or-keeps-one-register))
          ("Subgoal *1/2"
           :use ((:instance collection-finish-tail-restores-or-keeps-one-register (register bound))))
          ("Subgoal *1/1"
           :use ((:instance collection-finish-tail-restores-or-keeps-one-register (register bound))))))

(defthm collection-checked-restoration-hands-request-to-allocator
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (headerp (equal (collection-read-word (+ sp 8) world) 0))
         (target (+ origin (collection-linux-offset (if headerp "rt:alloc" "rt:alloc-cells"))))
         (trace (collection-finish-tail-trace headerp origin))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-final-restore-input-p origin world)
                  (equal (+ sp 64) (boymoo-model::a64-sp (proof-world-machine before)))
                  (equal (collection-frame-words sp world) (collection-saved-registers before))
                  (proof-register-frame-p
                   30 (append *collection-saved-frame-registers* *collection-allocation-clobbers*) before world)
                  (collection-trace-ready-p trace (list target) world))
             (and (proof-segment-p (len trace) (list target) world :cut after)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine before)))
                  (proof-register-frame-p 30 *collection-allocation-clobbers* before after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-finish-tail-trace
                                    (equal (collection-read-word (+ 8 (boymoo-model::a64-sp
                                                                      (proof-world-machine world))) world) 0) origin))
                            (cuts (list (+ origin (collection-linux-offset
                                                  (if (equal (collection-read-word
                                                              (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))
                                                              world) 0)
                                                      "rt:alloc" "rt:alloc-cells"))))))
                 (:instance collection-finish-tail-reestablishes-register-frame
                            (bound 30) (clobbers *collection-allocation-clobbers*))
                 (:instance collection-finish-tail-restores-saved-registers-and-request (register 0))
                 (:instance collection-finish-tail-restores-or-keeps-one-register (register 0))
                 (:instance collection-finish-tail-restores-or-keeps-one-register (register 1)))
           :in-theory (disable proof-register-frame-p proof-segment-p proof-streams-preserved-p
                               collection-ready-trace-reaches-cut
                               collection-finish-tail-reestablishes-register-frame
                               collection-finish-tail-restores-saved-registers-and-request
                               collection-finish-tail-restores-or-keeps-one-register))))
