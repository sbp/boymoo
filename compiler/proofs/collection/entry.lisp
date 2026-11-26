(in-package "BOYMOO-PROOFS")

(include-book "frame-protection")
(include-book "scanner")
(include-book "retirement")
(include-book "forward-placement")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-request-test-trace (origin)
  (collection-linux-trace "rt:collect" '(0 1 2 3 4 5 6) origin))

(defun collection-dynamic-root-call-trace (origin)
  (collection-linux-trace "rt:collect" '(7 8 9 10 11 12 13) origin))

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-sp
                     collection-write-flags collection-subtract-flags
                     boymoo-model::a64-unsigned boymoo-model::a64-sp boymoo-model::a64-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes (:definition ash))))

(defthm collection-entry-saves-frame-and-selects-request-path
  (let* ((entry (collection-linux-offset "rt:collect"))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (request (proof-world-reg 0 world))
         (after (collection-trace-effect (collection-request-test-trace origin) world)))
    (implies (and (collection-cpu-p world) (<= 64 sp)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (and (collection-cpu-p after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (- sp 64))
                  (equal (collection-frame-words (- sp 64) after) (collection-saved-registers world))
                  (alistp (boymoo-model::a64-memory (proof-world-machine after)))
                  (equal (proof-world-pc after)
                         (+ origin (if (< *proof-space-size* request)
                                       (collection-linux-offset "rt:datum-size") (+ entry 28))))
                  (implies (< *proof-space-size* request)
                           (proof-resource-bound-p :allocation-size request after))
                  (proof-streams-preserved-p world after)
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-replies after) (proof-world-replies world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (implies (not (equal register 2))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :in-theory (enable collection-frame-words collection-saved-registers))))

(defthm collection-setup-opens-dynamic-root-call-at-empty-frontiers
  (let* ((entry (collection-linux-offset "rt:collect"))
         (base (proof-heap-base world))
         (metadata (- base 128))
         (next (collection-trace-effect (collection-dynamic-root-call-trace origin) world)))
    (implies (and (collection-cpu-p world) (<= 128 base)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 28)))
             (and (collection-cpu-p next)
                  (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:forward")))
                  (equal (proof-world-reg 30 next) (+ origin entry 56))
                  (equal (proof-world-reg 0 next) (proof-dynamic-root base (proof-world-machine world)))
                  (equal (proof-world-reg 17 next) metadata)
                  (equal (proof-world-reg 19 next) (proof-active-floor world))
                  (equal (proof-world-reg 20 next) (proof-inactive-floor world))
                  (equal (proof-world-reg 21 next) (proof-inactive-end world))
                  (equal (proof-world-reg 8 next) (proof-world-reg 20 next))
                  (equal (proof-world-reg 22 next) (proof-world-reg 21 next))
                  (equal (boymoo-model::a64-sp (proof-world-machine next))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal register '(0 8 17 19 20 21 22 30)))
                           (equal (proof-world-reg register next) (proof-world-reg register world))))))
  :hints (("Goal"
           :in-theory (disable collection-world-register-bounds collection-world-pc-bounds))
          (and stable-under-simplificationp
               '(:in-theory (enable collection-read-word)))))

(defthm collection-collector-diagnostic-stack-covers-both-frames
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (floor (- (proof-machine-limit world) *proof-machine-margin*))
         (regions (proof-world-regions world)))
    (implies (and (proof-heap-layout-p world) (<= (+ floor 96) sp))
             (and (proof-covered-p (- sp 64) 64 :write regions)
                  (proof-covered-p (- sp 96) 32 :write regions)
                  (equal (mod sp 16) 0))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-covered-subspan
                            (base (- (proof-machine-limit world) *proof-machine-margin*))
                            (extent *proof-machine-reservation*)
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 64))
                            (width 64) (access :write) (regions (proof-world-regions world)))
                 (:instance collection-covered-subspan
                            (base (- (proof-machine-limit world) *proof-machine-margin*))
                            (extent *proof-machine-reservation*)
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 96))
                            (width 32) (access :write) (regions (proof-world-regions world)))
                 (:instance collection-covered-address-is-a-span
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (width *proof-machine-reservation*) (access :write)
                            (regions (proof-world-regions world))))
           :in-theory (disable mod proof-covered-p proof-regions-p proof-machine-limit
                               proof-stack-top proof-stack-limit proof-stack-base proof-stack-end
                               proof-spaces-end proof-static-size proof-box-top proof-cons-floor
                               proof-heap-limit proof-inactive-end proof-active-end proof-active-floor
                               proof-inactive-floor proof-align-up proof-heap-base proof-world-page-size
                               proof-page-size-p proof-world-regions collection-covered-address-is-a-span))))

(local
 (defthm collection-dynamic-root-continuation-access
   (implies (not (equal base 31))
            (equal (proof-instruction-access-p
                    (list :single load 8 base target :offset delta) world)
                   (proof-covered-p (boymoo-model::a64-unsigned 64 (+ (proof-world-reg base world) delta))
                                    8 (if (equal load 1) :read :write) (proof-world-regions world))))
   :hints (("Goal" :in-theory (e/d (proof-world-reg proof-reg boymoo-model::a64-read-reg)
                                  (proof-covered-p boymoo-model::a64-unsigned))))))

(local
 (defthm collection-dynamic-root-continuation-actions-keep-stop
   (and (equal (proof-world-stop (collection-write-register register value world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-pc address world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-word address value world)) (proof-world-stop world)))
   :hints (("Goal" :in-theory (enable proof-world-stop collection-write-register
                                      collection-write-pc collection-write-word)))))

(defthm collection-placed-dynamic-root-continuation-commits-returned-word
  (let* ((trace (collection-linux-trace "rt:collect" '(14 15) origin))
         (cut (+ origin (collection-linux-offset "rt:collect-roots")))
         (address (+ 24 (proof-world-reg 28 world)))
         (stack-base (+ 40 (proof-world-reg 17 world)))
         (regions (proof-world-regions world))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:collect") 56))
                  (not (proof-world-stop world))
                  (proof-regions-p regions)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-covered-p address 8 :write regions)
                  (proof-covered-p stack-base 8 :read regions)
                  (proof-disjoint-p address (+ address 8) stack-base (+ stack-base 8))
                  (collection-trace-placed-p trace world))
             (and (collection-trace-ready-p trace (list cut) world)
                  (equal (collection-read-word address after) (proof-world-reg 0 world))
                  (equal (proof-world-reg 9 after) (collection-read-word stack-base world))
                  (equal (proof-world-pc after) cut)
                  (implies (not (equal register 9))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-covered-address-is-a-span
                            (address (+ 24 (proof-world-reg 28 world))) (width 8) (access :write)
                            (regions (proof-world-regions world)))
                 (:instance collection-covered-address-is-a-span
                            (address (+ 40 (proof-world-reg 17 world))) (width 8) (access :read)
                            (regions (proof-world-regions world))))
           :in-theory (disable proof-world-regions proof-world-stop proof-covered-p proof-regions-p
                               proof-instruction-at-p collection-covered-address-is-a-span
                               collection-rewrites-dynamic-root-before-visiting-stack))))
