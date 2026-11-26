(in-package "BOYMOO-PROOFS")

(include-book "finish")
(include-book "regions")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-relinquish-p (base bytes world)
  (let ((page (proof-world-page-size world)))
    (and (proof-page-size-p page)
         (equal (mod base page) 0)
         (posp bytes)
         (equal (proof-align-up bytes page) bytes)
         (proof-covered-p base bytes :write (proof-world-regions world))
         (consp (proof-world-replies world))
         (equal (car (proof-world-replies world)) 0))))

(defun collection-relinquish-range (unmap base bytes world)
  (let ((cleared (proof-clear-span base (+ base bytes) world)))
    (if unmap
        (update-nth 1 (proof-remove-region-span base bytes (proof-world-regions world))
                    cleared)
      cleared)))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg
                     boymoo-model::a64-unsigned proof-covered-p proof-align-up
                     proof-clear-span proof-remove-region-span
                     (:definition ash) (:definition acl2::binary-logand))))

(defthm collection-successful-linux-release
  (let ((base (proof-world-reg 0 world))
        (bytes (proof-world-reg 1 world)))
    (implies (and (collection-relinquish-p base bytes world)
                  (or unmap (equal (proof-world-reg 2 world) 4)))
             (equal (proof-linux-release unmap 0 world)
                    (proof-svc-return 0
                                      (collection-relinquish-range unmap base bytes world))))))

(local (in-theory (disable proof-linux-release)))

(local
 (defthm collection-svc-zero-effect
   (equal (proof-instruction-effect '(:svc 0) world)
          (proof-linux-svc
           (list :svc 0 (proof-world-reg 16 world) (proof-world-reg 8 world)) world))
   :hints (("Goal" :in-theory (e/d (proof-world-reg proof-reg)
                                   (boymoo-model::a64-read-reg proof-linux-svc))))))

(local (in-theory (disable proof-instruction-effect)))

(defthm collection-svc-executes-relinquish
  (let ((base (proof-world-reg 0 world))
        (bytes (proof-world-reg 1 world)))
    (implies (and (collection-relinquish-p base bytes world)
                  (equal (proof-world-reg 8 world) (if unmap 215 233))
                  (or unmap (equal (proof-world-reg 2 world) 4)))
             (equal (proof-instruction-effect '(:svc 0) world)
                    (proof-svc-return 0 (collection-relinquish-range unmap base bytes world)))))
  :hints (("Goal" :in-theory (disable proof-svc-return))))

(local
 (defthm collection-svc-return-has-register-and-pc-effects
   (equal (proof-svc-return value world)
          (update-nth 6 (cdr (proof-world-replies world))
                      (collection-write-register 0 value
                       (collection-next-instruction world))))))

(local
 (in-theory (disable proof-svc-return collection-write-register collection-write-pc
                     collection-write-sp collection-cpu-p
                     proof-world-machine boymoo-model::a64-memory boymoo-model::a64-sp
                     boymoo-model::a64-registers boymoo-model::a64-nzcv)))

(local
 (defthm collection-world-projections-of-cleared-span
   (let ((after (proof-clear-span base end world)))
     (and (equal (collection-cpu-p after) (collection-cpu-p world))
          (equal (proof-world-reg register after) (proof-world-reg register world))
          (equal (proof-world-pc after) (proof-world-pc world))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp (proof-world-machine world)))
          (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                 (boymoo-model::a64-nzcv (proof-world-machine world)))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (proof-clear-memory base end
                                     (boymoo-model::a64-memory (proof-world-machine world))))
          (implies (natp slot)
                   (equal (nth slot after) (if (equal slot 0) (proof-world-machine after)
                                             (nth slot world))))))
   :hints (("Goal" :in-theory (e/d (proof-clear-span proof-world-machine
                                                   proof-world-reg proof-reg proof-world-pc
                                                   boymoo-model::a64-memory
                                                   boymoo-model::a64-registers boymoo-model::a64-sp
                                                   boymoo-model::a64-nzcv collection-cpu-p)
                                   (proof-clear-memory nth update-nth))))))

(local
 (defthm collection-world-machine-with-kernel-metadata-change
   (implies (and (natp slot) (< 0 slot))
            (equal (proof-world-machine (update-nth slot data world))
                   (proof-world-machine world)))
   :hints (("Goal" :in-theory (enable proof-world-machine)))))

(local
 (defthm collection-world-reg-with-kernel-metadata-change
   (implies (and (natp slot) (< 0 slot))
            (and (equal (proof-world-reg register (update-nth slot data world))
                        (proof-world-reg register world))
                 (equal (proof-world-pc (update-nth slot data world))
                        (proof-world-pc world))
                 (equal (collection-cpu-p (update-nth slot data world))
                        (collection-cpu-p world))))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-world-pc collection-cpu-p)))))

(defun collection-relinquish-wrapper-trace (unmap origin)
  (if unmap
      (collection-linux-trace "sys:unmap" '(0 1 2) origin)
    (collection-linux-trace "sys:release" '(0 1 2 3) origin)))

(defthm collection-kernel-metadata-after-cpu-change
  (implies (and (natp slot) (< 0 slot))
           (and (equal (nth slot (collection-write-pc address world)) (nth slot world))
                (equal (nth slot (collection-write-register register value world))
                       (nth slot world))
                (equal (nth slot (collection-write-word address value world)) (nth slot world))
                (equal (nth slot (collection-write-flags flags world)) (nth slot world))
                (equal (nth slot (collection-write-sp address world)) (nth slot world))))
  :hints (("Goal" :in-theory (enable collection-write-pc collection-write-register
                                     collection-write-word collection-write-flags
                                     collection-write-sp))))

(defthm collection-linux-relinquish-wrapper-effect
  (let* ((label (if unmap "sys:unmap" "sys:release"))
         (base (proof-world-reg 0 world))
         (bytes (proof-world-reg 1 world))
         (next (collection-trace-effect (collection-relinquish-wrapper-trace unmap origin)
                                        world))
         (cleared (collection-relinquish-range unmap base bytes world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin (collection-linux-offset label)))
                  (collection-relinquish-p base bytes world))
             (and (collection-cpu-p next)
                  (equal (proof-world-pc next) (proof-world-reg 30 world))
                  (equal (proof-world-reg 0 next) 0)
                  (equal (proof-world-replies next) (cdr (proof-world-replies world)))
                  (equal (proof-world-regions next) (proof-world-regions cleared))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine cleared)))
                  (equal (boymoo-model::a64-sp (proof-world-machine next))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-stop next) (proof-world-stop world))
                  (proof-streams-preserved-p world next)
                  (implies (not (member-equal register '(0 2 8)))
                           (equal (proof-world-reg register next)
                                  (proof-world-reg register world))))))
  :hints (("Goal"
           :cases (unmap)
           :in-theory (disable proof-clear-memory collection-word-of-wrapped-addend
                               collection-covered-address-is-a-span))))

(defthm collection-checked-linux-relinquish-wrapper
  (let* ((trace (collection-relinquish-wrapper-trace unmap origin))
         (cuts (list (proof-world-reg 30 world)))
         (base (proof-world-reg 0 world))
         (bytes (proof-world-reg 1 world))
         (after (collection-trace-effect trace world))
         (cleared (collection-relinquish-range unmap base bytes world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world)
                         (+ origin (collection-linux-offset (if unmap "sys:unmap" "sys:release"))))
                  (collection-relinquish-p base bytes world)
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (proof-world-reg 0 after) 0)
                  (equal (proof-world-replies after) (cdr (proof-world-replies world)))
                  (equal (proof-world-regions after) (proof-world-regions cleared))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine cleared)))
                  (proof-streams-preserved-p world after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-relinquish-wrapper-trace unmap origin))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance collection-linux-relinquish-wrapper-effect (register 30)))
           :in-theory (disable collection-linux-relinquish-wrapper-effect
                               collection-relinquish-wrapper-trace collection-relinquish-range
                               collection-relinquish-p collection-trace-ready-p
                               collection-trace-effect proof-segment-p proof-streams-preserved-p))))

