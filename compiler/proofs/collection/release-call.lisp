(in-package "BOYMOO-PROOFS")

(include-book "retirement")
(include-book "frame-protection")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-release-call-trace (origin)
  (collection-linux-trace "rt:release-range" '(0 1 2 3) origin))

(defun collection-release-return-trace (origin)
  (collection-linux-trace "rt:release-range" '(4 5 6) origin))

(defun collection-positive-release-trace (origin)
  (append (collection-release-call-trace origin)
          (collection-relinquish-wrapper-trace nil origin)
          (collection-release-return-trace origin)))

(defun collection-empty-release-trace (origin)
  (collection-linux-trace "rt:release-range" '(0 1 6) origin))

(defun collection-release-saved-pair (frame world)
  (collection-write-word (+ frame 8) (proof-world-reg 30 world)
                         (collection-write-word frame (proof-world-reg 29 world) world)))

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-write-sp collection-subtract-flags
                     boymoo-model::a64-unsigned boymoo-model::a64-sp
                     boymoo-model::a64-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand))))

(defthm collection-empty-release-returns-without-clearing
  (let* ((entry (collection-linux-offset "rt:release-range"))
         (trace (collection-empty-release-trace origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry))
                  (<= (proof-world-reg 1 world) (proof-world-reg 0 world))
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (collection-cpu-p after)
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-replies after) (proof-world-replies world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (implies (not (equal register 1))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-empty-release-trace origin))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable proof-segment-p collection-trace-ready-p))))

(local
 (defthm collection-release-prefix-saves-pair-and-opens-wrapper
   (let* ((entry (collection-linux-offset "rt:release-range"))
          (start (proof-world-reg 0 world))
          (end (proof-world-reg 1 world))
          (sp (boymoo-model::a64-sp (proof-world-machine world)))
          (frame (- sp 16))
          (after (collection-trace-effect (collection-release-call-trace origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin entry))
                   (< start end) (<= 16 sp))
              (and (collection-cpu-p after)
                   (equal (proof-world-pc after) (+ origin (collection-linux-offset "sys:release")))
                   (equal (proof-world-reg 30 after) (+ origin entry 16))
                   (equal (proof-world-reg 0 after) start)
                   (equal (proof-world-reg 1 after) (- end start))
                   (equal (proof-world-replies after) (proof-world-replies world))
                   (equal (proof-world-page-size after) (proof-world-page-size world))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (proof-streams-preserved-p world after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) frame)
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory
                           (proof-world-machine (collection-release-saved-pair frame world))))
                   (implies (not (member-equal register '(1 30)))
                            (equal (proof-world-reg register after) (proof-world-reg register world))))))))

(local
 (defthm collection-release-tail-restores-pair-and-returns
   (let* ((entry (collection-linux-offset "rt:release-range"))
          (sp (boymoo-model::a64-sp (proof-world-machine world)))
          (frame-pointer (collection-read-word sp world))
          (link (collection-read-word (+ sp 8) world))
          (after (collection-trace-effect (collection-release-return-trace origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin entry 16))
                   (equal (proof-world-reg 0 world) 0)
                   (unsigned-byte-p 64 (+ sp 16)))
              (and (equal (proof-world-pc after) link)
                   (collection-cpu-p after)
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (proof-streams-preserved-p world after)
                   (equal (proof-world-reg 29 after) frame-pointer)
                   (equal (proof-world-reg 30 after) link)
                   (equal (proof-world-replies after) (proof-world-replies world))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ sp 16))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (implies (not (member-equal register '(29 30)))
                            (equal (proof-world-reg register after) (proof-world-reg register world))))))))

(local
 (in-theory (disable collection-release-call-trace collection-release-return-trace
                     collection-relinquish-wrapper-trace collection-trace-effect
                     proof-world-regions proof-world-replies proof-world-page-size
                     proof-world-stop proof-clear-memory)))

(local
 (defthm collection-saved-release-pair-survives-clear
   (let* ((saved (collection-release-saved-pair frame world))
          (cleared (proof-clear-span start end saved)))
     (implies (and (proof-span-p frame 16)
                   (proof-disjoint-p frame (+ frame 16) start end)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world))))
              (and (equal (collection-read-word frame cleared) (proof-world-reg 29 world))
                   (equal (collection-read-word (+ frame 8) cleared)
                          (proof-world-reg 30 world)))))
   :hints (("Goal" :in-theory (disable proof-clear-span)))))

(local
 (defthm collection-released-world-projections
   (let ((after (collection-relinquish-range nil start bytes world)))
     (and (equal (proof-world-regions after) (proof-world-regions world))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (proof-clear-memory start (+ start bytes)
                                     (boymoo-model::a64-memory (proof-world-machine world))))))
   :hints (("Goal" :in-theory (e/d (collection-relinquish-range proof-clear-span
                                                              proof-world-regions
                                                              proof-world-machine
                                                              boymoo-model::a64-memory)
                                  (nth update-nth))))))

(defthm collection-release-link-load-depends-on-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-read-word address first) (collection-read-word address second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                   (boymoo-model::a64-read-bytes)))))

(local
 (defthm collection-relinquish-range-depends-on-kernel-fields
   (implies (and (equal (proof-world-regions first) (proof-world-regions second))
                 (equal (proof-world-replies first) (proof-world-replies second))
                 (equal (proof-world-page-size first) (proof-world-page-size second)))
            (equal (collection-relinquish-p start bytes first)
                   (collection-relinquish-p start bytes second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-align-up proof-page-size-p proof-covered-p mod)))))

(local
 (defthm collection-release-wrapper-input-after-save
   (let* ((entry (collection-linux-offset "rt:release-range"))
          (start (proof-world-reg 0 world))
          (end (proof-world-reg 1 world))
          (sp (boymoo-model::a64-sp (proof-world-machine world)))
          (call (collection-trace-effect (collection-release-call-trace origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin entry))
                   (< start end) (<= 16 sp)
                   (collection-relinquish-p start (- end start) world))
              (collection-relinquish-p start (- end start) call)))
   :hints (("Goal"
            :use ((:instance collection-relinquish-range-depends-on-kernel-fields
                             (first world)
                             (second (collection-trace-effect
                                      (collection-release-call-trace origin) world))
                             (start (proof-world-reg 0 world))
                             (bytes (- (proof-world-reg 1 world) (proof-world-reg 0 world)))))
            :in-theory (disable collection-relinquish-p proof-span-p)))))

(local
 (defthm collection-release-frame-has-addressable-span
   (let ((sp (boymoo-model::a64-sp machine)))
     (implies (<= 16 sp) (proof-span-p (- sp 16) 16)))))

(local
 (defthm collection-readd-start-to-interval-length
   (implies (and (integerp start) (integerp end))
            (equal (+ start (- start) end) end))))

(defthm collection-positive-release-clears-range-and-restores-frame
  (let* ((entry (collection-linux-offset "rt:release-range"))
         (start (proof-world-reg 0 world))
         (end (proof-world-reg 1 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (frame (- sp 16))
         (after (collection-trace-effect (collection-positive-release-trace origin) world))
         (saved (collection-release-saved-pair frame world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry))
                  (< start end) (<= 16 sp)
                  (proof-disjoint-p frame sp start end)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (collection-relinquish-p start (- end start) world))
             (and (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (collection-cpu-p after)
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (equal (proof-world-replies after) (cdr (proof-world-replies world)))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (proof-clear-memory start end
                                             (boymoo-model::a64-memory
                                              (proof-world-machine saved))))
                  (implies (not (member-equal register '(0 1 2 8)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance collection-release-wrapper-input-after-save)
                 (:instance collection-release-prefix-saves-pair-and-opens-wrapper)
                 (:instance collection-release-tail-restores-pair-and-returns
                            (world (collection-trace-effect
                                    (collection-relinquish-wrapper-trace nil origin)
                                    (collection-trace-effect
                                     (collection-release-call-trace origin) world))))
                 (:instance collection-linux-relinquish-wrapper-effect
                            (unmap nil)
                            (world (collection-trace-effect
                                    (collection-release-call-trace origin) world)))
                 (:instance collection-saved-release-pair-survives-clear
                            (frame (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (start (proof-world-reg 0 world)) (end (proof-world-reg 1 world)))
                 (:instance collection-release-link-load-depends-on-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (first (collection-trace-effect
                                    (collection-relinquish-wrapper-trace nil origin)
                                    (collection-trace-effect
                                     (collection-release-call-trace origin) world)))
                            (second (proof-clear-span
                                     (proof-world-reg 0 world) (proof-world-reg 1 world)
                                     (collection-release-saved-pair
                                      (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      world))))
                 (:instance collection-release-link-load-depends-on-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 8))
                            (first (collection-trace-effect
                                    (collection-relinquish-wrapper-trace nil origin)
                                    (collection-trace-effect
                                     (collection-release-call-trace origin) world)))
                            (second (proof-clear-span
                                     (proof-world-reg 0 world) (proof-world-reg 1 world)
                                     (collection-release-saved-pair
                                      (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      world)))))
           :in-theory (disable collection-linux-relinquish-wrapper-effect
                               collection-release-prefix-saves-pair-and-opens-wrapper
                               collection-release-wrapper-input-after-save
                               collection-release-tail-restores-pair-and-returns
                               collection-saved-release-pair-survives-clear
                               collection-relinquish-p collection-relinquish-range
                               proof-clear-span proof-span-p))))

(defthm collection-checked-positive-release-restores-caller
  (let* ((entry (collection-linux-offset "rt:release-range"))
         (start (proof-world-reg 0 world))
         (end (proof-world-reg 1 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (trace (collection-positive-release-trace origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry))
                  (< start end) (<= 16 sp)
                  (proof-disjoint-p (- sp 16) sp start end)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (collection-relinquish-p start (- end start) world)
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (equal (proof-world-replies after) (cdr (proof-world-replies world)))
                  (equal (proof-world-regions after) (proof-world-regions world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-positive-release-trace origin))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance collection-positive-release-clears-range-and-restores-frame))
           :in-theory (disable collection-positive-release-clears-range-and-restores-frame
                               collection-positive-release-trace collection-relinquish-p
                               collection-trace-ready-p proof-segment-p proof-span-p))))
