(in-package "BOYMOO-PROOFS")

(include-book "sweep")
(include-book "retirement")
(include-book "frame-protection")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-sweep-retain-trace (origin)
  (append (collection-linux-trace "rt:sweep-string" '(0 1 2 3 4) origin)
          (collection-linux-trace "rt:sweep-keep" '(0 1 2 3) origin)))

(defun collection-sweep-unlink-trace (origin)
  (collection-linux-trace "rt:sweep-string" '(0 1 2 3 4 5 6) origin))

(defun collection-sweep-unmap-continuation (origin)
  (collection-linux-trace "rt:sweep-string" '(7 8) origin))

(defun collection-sweep-discard-trace (origin)
  (append (collection-sweep-unlink-trace origin)
          (collection-relinquish-wrapper-trace t origin)
          (collection-sweep-unmap-continuation origin)))

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned
                     boymoo-model::a64-nzcv boymoo-model::a64-condition boymoo-model::a64-sp
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand))))

(defthm collection-sweep-retains-one-mapping-and-resets-mark
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (link (proof-world-reg 19 world))
         (head (collection-read-word link world))
         (size (collection-read-word (+ head 8) world))
         (total (+ (proof-world-reg 22 world) size))
         (after (collection-trace-effect (collection-sweep-retain-trace origin) world))
         (written (collection-write-word (+ head 16) 0 world)))
    (implies (and (collection-sweep-entry-p entry origin world)
                  (not (equal head 0))
                  (not (equal (collection-read-word (+ head 16) world) 0))
                  (proof-span-p head 24)
                  (unsigned-byte-p 64 total)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world))))
             (and (equal (proof-world-pc after) (+ origin entry))
                  (collection-cpu-p after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (equal (proof-world-reg 19 after) head)
                  (equal (proof-world-reg 22 after) total)
                  (equal (proof-world-replies after) (proof-world-replies world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (collection-read-word (+ head 16) after) 0)
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine written)))
                  (implies (not (member-equal register '(0 1 2 19 20 22)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :in-theory (disable collection-trace-effect-of-append))))

(local
 (defthm collection-unlink-trace-prepares-unmap
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (link (proof-world-reg 19 world))
          (head (collection-read-word link world))
          (size (collection-read-word (+ head 8) world))
          (next (collection-read-word head world))
          (call (collection-trace-effect (collection-sweep-unlink-trace origin) world))
          (written (collection-write-word link next world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (not (equal head 0))
                   (equal (collection-read-word (+ head 16) world) 0)
                   (proof-span-p head 24))
              (and (collection-cpu-p call)
                   (equal (proof-world-pc call) (+ origin (collection-linux-offset "sys:unmap")))
                   (equal (proof-world-reg 30 call) (+ origin entry 28))
                   (equal (proof-world-reg 0 call) head)
                   (equal (proof-world-reg 1 call) size)
                   (equal (proof-world-reg 19 call) link)
                   (equal (proof-world-reg 22 call) (proof-world-reg 22 world))
                   (equal (proof-world-replies call) (proof-world-replies world))
                   (equal (proof-world-page-size call) (proof-world-page-size world))
                   (equal (proof-world-regions call) (proof-world-regions world))
                   (equal (boymoo-model::a64-sp (proof-world-machine call))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (proof-world-stop call) (proof-world-stop world))
                   (proof-streams-preserved-p world call)
                   (equal (boymoo-model::a64-memory (proof-world-machine call))
                          (boymoo-model::a64-memory (proof-world-machine written)))
                   (implies (not (member-equal register '(0 1 2 20 30)))
                            (equal (proof-world-reg register call) (proof-world-reg register world))))))))

(local
 (defthm collection-unmap-continuation-resumes-sweep
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (after (collection-trace-effect (collection-sweep-unmap-continuation origin) world)))
     (implies (and (collection-sweep-entry-p (+ entry 28) origin world)
                   (equal (proof-world-reg 0 world) 0))
              (and (equal (proof-world-pc after) (+ origin entry))
                   (collection-cpu-p after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (proof-streams-preserved-p world after)
                   (equal (proof-world-reg register after) (proof-world-reg register world))
                   (equal (proof-world-replies after) (proof-world-replies world))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world))))))))

(local
 (in-theory (disable collection-sweep-unlink-trace collection-sweep-unmap-continuation
                     collection-relinquish-wrapper-trace
                     collection-trace-effect collection-relinquish-range
                     proof-clear-memory proof-covered-p proof-align-up
                     proof-world-regions proof-world-page-size proof-world-replies proof-world-stop)))

(local
 (defthm collection-unlink-keeps-unmap-permission
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (head (collection-read-word (proof-world-reg 19 world) world))
          (size (collection-read-word (+ head 8) world))
          (after (collection-trace-effect (collection-sweep-unlink-trace origin) world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (not (equal head 0))
                   (equal (collection-read-word (+ head 16) world) 0)
                   (proof-span-p head 24)
                   (collection-relinquish-p head size world))
              (collection-relinquish-p head size after)))
   :hints (("Goal"
            :in-theory (disable collection-sweep-entry-p proof-span-p
                                proof-page-size-p mod)))))

(local
 (defthm collection-read-word-from-equal-memories
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-read-word address first)
                   (collection-read-word address second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                   (boymoo-model::a64-read-bytes))))))

(local
 (defthm collection-relinquished-memory
   (equal (boymoo-model::a64-memory
           (proof-world-machine (collection-relinquish-range unmap base size world)))
          (proof-clear-memory base (+ base size)
                              (boymoo-model::a64-memory (proof-world-machine world))))
   :hints (("Goal" :in-theory (e/d (collection-relinquish-range proof-clear-span
                                                              proof-world-machine
                                                              boymoo-model::a64-memory)
                                  (nth update-nth))))))

(local
 (defthm collection-relinquished-regions
   (equal (proof-world-regions (collection-relinquish-range unmap base size world))
          (if unmap
              (proof-remove-region-span base size (proof-world-regions world))
            (proof-world-regions world)))
   :hints (("Goal" :in-theory (e/d (collection-relinquish-range proof-clear-span
                                                              proof-world-regions)
                                  (nth update-nth))))))

(local
 (defthm collection-updating-link-survives-unmap
   (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                 (proof-span-p link 8)
                 (unsigned-byte-p 64 next)
                 (proof-disjoint-p link (+ link 8) head (+ head size)))
            (equal (collection-read-word
                    link (collection-relinquish-range
                          t head size (collection-write-word link next world)))
                   next))
   :hints (("Goal"
            :use ((:instance collection-read-word-from-equal-memories
                             (first (collection-relinquish-range
                                     t head size (collection-write-word link next world)))
                             (second (proof-clear-span head (+ head size)
                                                       (collection-write-word link next world)))
                             (address link))
                  (:instance collection-clear-preserves-word-outside-range
                             (address link) (base head) (end (+ head size))
                             (world (collection-write-word link next world))))
            :in-theory (e/d (collection-relinquish-range)
                            (proof-clear-span collection-clear-preserves-word-outside-range))))))

(defthm collection-sweep-discards-one-mapping-and-relinks
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (link (proof-world-reg 19 world))
         (head (collection-read-word link world))
         (size (collection-read-word (+ head 8) world))
         (next (collection-read-word head world))
         (after (collection-trace-effect (collection-sweep-discard-trace origin) world))
         (written (collection-write-word link next world))
         (end (+ head size)))
    (implies (and (collection-sweep-entry-p entry origin world)
                  (not (equal head 0))
                  (equal (collection-read-word (+ head 16) world) 0)
                  (proof-span-p head 24)
                  (proof-span-p link 8)
                  (proof-disjoint-p link (+ link 8) head end)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (collection-relinquish-p head size world))
             (and (equal (proof-world-pc after) (+ origin entry))
                  (collection-cpu-p after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (equal (proof-world-reg 19 after) link)
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (collection-read-word link after) next)
                  (equal (proof-world-regions after)
                         (proof-remove-region-span head size (proof-world-regions world)))
                  (equal (proof-world-replies after) (cdr (proof-world-replies world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (proof-clear-memory head end
                                             (boymoo-model::a64-memory
                                              (proof-world-machine written))))
                  (implies (not (member-equal register '(0 1 2 8 20 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance collection-unlink-trace-prepares-unmap)
                 (:instance collection-unlink-keeps-unmap-permission)
                 (:instance collection-unmap-continuation-resumes-sweep
                            (world (collection-trace-effect
                                    (collection-relinquish-wrapper-trace t origin)
                                    (collection-trace-effect (collection-sweep-unlink-trace origin) world))))
                 (:instance collection-linux-relinquish-wrapper-effect
                            (unmap t) (register 19)
                            (world (collection-trace-effect
                                    (collection-sweep-unlink-trace origin) world)))
                 (:instance collection-linux-relinquish-wrapper-effect
                            (unmap t) (register 22)
                            (world (collection-trace-effect
                                    (collection-sweep-unlink-trace origin) world)))
                 (:instance collection-linux-relinquish-wrapper-effect
                            (unmap t)
                            (world (collection-trace-effect
                                    (collection-sweep-unlink-trace origin) world)))
                 (:instance collection-read-word-from-equal-memories
                            (address (proof-world-reg 19 world))
                            (first (collection-trace-effect (collection-sweep-discard-trace origin)
                                                            world))
                            (second (collection-relinquish-range
                                     t (collection-read-word (proof-world-reg 19 world) world)
                                     (collection-read-word
                                      (+ 8 (collection-read-word (proof-world-reg 19 world) world))
                                      world)
                                     (collection-write-word
                                      (proof-world-reg 19 world)
                                      (collection-read-word
                                       (collection-read-word (proof-world-reg 19 world) world)
                                       world)
                                      world)))))
           :in-theory (disable collection-linux-relinquish-wrapper-effect collection-relinquish-p
                               proof-span-p
                               collection-unlink-trace-prepares-unmap
                               collection-unlink-keeps-unmap-permission))))
