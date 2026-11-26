(in-package "BOYMOO-PROOFS")

(include-book "runtime-layout")
(include-book "comparisons")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned
                     boymoo-model::a64-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand))))

(defthm collection-scan-selects-pending-conses-first
  (let* ((entry (collection-linux-offset "rt:scan"))
         (more (< (proof-world-reg 21 world) (proof-world-reg 22 world)))
         (next (collection-trace-effect (collection-linux-trace "rt:scan" '(0 1) origin)
                                        world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (equal (proof-world-pc next)
                    (+ origin (if more (collection-linux-offset "rt:scan-cons")
                                 (+ entry 8)))))))

(defthm collection-scan-tests-pending-headers
  (let* ((entry (collection-linux-offset "rt:scan"))
         (more (< (proof-world-reg 8 world) (proof-world-reg 20 world)))
         (next (collection-trace-effect (collection-linux-trace "rt:scan" '(2 3) origin)
                                        world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 8)))
             (equal (proof-world-pc next)
                    (+ origin (if more (+ entry 16)
                                 (collection-linux-offset "rt:collect-finish")))))))

(defthm collection-tests-pending-request-size
  (let* ((entry (collection-linux-offset "rt:collect"))
         (request (proof-world-reg 0 world))
         (next (collection-trace-effect (collection-linux-trace "rt:collect" '(4 5 6) origin)
                                        world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 16)))
             (and (equal (proof-world-pc next)
                         (+ origin (if (< *proof-space-size* request)
                                       (collection-linux-offset "rt:datum-size")
                                     (+ entry 28))))
                  (implies (< *proof-space-size* request)
                           (proof-resource-bound-p :allocation-size request world))))))

(defthm collection-initializes-destination-cursors
  (let* ((entry (collection-linux-offset "rt:collect"))
         (metadata (- (proof-world-reg 28 world) 128))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect" '(7 8 9 10 11) origin) world)))
    (implies (and (collection-cpu-p world)
                  (<= 128 (proof-world-reg 28 world))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 28)))
             (and (equal (proof-world-pc next) (+ origin entry 48))
                  (equal (proof-world-reg 17 next) metadata)
                  (equal (proof-world-reg 19 next)
                         (boymoo-model::a64-unsigned 64 (collection-read-word metadata world)))
                  (equal (proof-world-reg 20 next)
                         (boymoo-model::a64-unsigned
                          64 (collection-read-word (+ metadata 24) world)))
                  (equal (proof-world-reg 21 next)
                         (boymoo-model::a64-unsigned
                          64 (collection-read-word (+ metadata 32) world)))
                  (equal (proof-world-reg 8 next) (proof-world-reg 20 next))
                  (equal (proof-world-reg 22 next) (proof-world-reg 21 next))))))

(defthm collection-scan-opens-header-payload
  (let* ((entry (collection-linux-offset "rt:scan"))
         (address (proof-world-reg 8 world))
         (header (boymoo-model::a64-unsigned 64 (collection-read-word address world)))
         (size (boymoo-model::a64-unsigned 64 (ash header -8)))
         (rounded (boymoo-model::a64-unsigned 64 (+ size 7)))
         (words (boymoo-model::a64-unsigned 64 (ash rounded -3)))
         (payload (boymoo-model::a64-unsigned 64 (+ address 8)))
         (next (collection-trace-effect
                (collection-linux-trace "rt:scan" '(4 5 6 7 8 9 10) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 16)))
             (and (equal (proof-world-pc next) (+ origin entry 44))
                  (equal (proof-world-reg 10 next)
                         (boymoo-model::a64-unsigned 64 (logand header 255)))
                  (equal (proof-world-reg 11 next) payload)
                  (equal (proof-world-reg 8 next)
                         (boymoo-model::a64-unsigned 64 (+ payload (ash words 3))))))))

(defthm collection-scan-skips-raw-payloads
  (let* ((entry (collection-linux-offset "rt:scan"))
         (stringp (equal (proof-world-reg 10 world) 1))
         (integerp (equal (proof-world-reg 10 world) 3))
         (next (collection-trace-effect
                (collection-linux-trace "rt:scan" (if stringp '(11 12) '(11 12 13 14)) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 44)))
             (equal (proof-world-pc next)
                    (+ origin (if (or stringp integerp)
                                  entry (collection-linux-offset "rt:scan-fields"))))))
  :hints (("Goal" :cases ((equal (proof-world-reg 10 world) 1)))))

(defthm collection-visits-dynamic-root-first
  (let* ((entry (collection-linux-offset "rt:collect"))
         (root-address (+ 24 (proof-world-reg 28 world)))
         (next (collection-trace-effect (collection-linux-trace "rt:collect" '(12 13) origin)
                                        world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 48)))
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:forward")))
                  (equal (proof-world-reg 30 next) (+ origin entry 56))
                  (equal (proof-world-reg 0 next)
                         (boymoo-model::a64-unsigned 64 (collection-read-word root-address world)))))))

(defthm collection-rewrites-dynamic-root-before-visiting-stack
  (let* ((entry (collection-linux-offset "rt:collect"))
         (root-address (+ 24 (proof-world-reg 28 world)))
         (next (collection-trace-effect (collection-linux-trace "rt:collect" '(14 15) origin)
                                        world))
         (stored (collection-write-word root-address (proof-world-reg 0 world) world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 56)))
             (and (equal (proof-world-pc next)
                         (+ origin (collection-linux-offset "rt:collect-roots")))
                  (equal (proof-world-reg 9 next)
                         (boymoo-model::a64-unsigned 64
                          (collection-read-word (+ 40 (proof-world-reg 17 world)) stored)))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine stored)))))))

; The stack-root loop and the header-field loop use the same instruction
; sequence with different cursor registers. The call cutpoint gives the
; forwarder its datum and link. The return cutpoint takes its result.
(defthm collection-slot-loop-opens-forwarding-call
  (let* ((label (if roots "rt:collect-roots" "rt:scan-fields"))
         (entry (collection-linux-offset label))
         (cursor (proof-world-reg (if roots 9 11) world))
         (end (proof-world-reg (if roots 25 8) world))
         (next (collection-trace-effect (collection-linux-trace label '(0 1 2 3) origin)
                                        world)))
    (implies (and (collection-cpu-p world) (< cursor end)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:forward")))
                  (equal (proof-world-reg 30 next) (+ origin entry 16))
                  (equal (proof-world-reg 0 next)
                         (boymoo-model::a64-unsigned 64 (collection-read-word cursor world))))))
  :hints (("Goal" :cases (roots))))

(defthm collection-slot-loop-ends-at-cursor-limit
  (let* ((label (if roots "rt:collect-roots" "rt:scan-fields"))
         (entry (collection-linux-offset label))
         (cursor (proof-world-reg (if roots 9 11) world))
         (end (proof-world-reg (if roots 25 8) world))
         (next (collection-trace-effect (collection-linux-trace label '(0 1) origin)
                                        world)))
    (implies (and (collection-cpu-p world) (<= end cursor)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:scan")))))
  :hints (("Goal" :cases (roots))))

(defthm collection-slot-loop-stores-and-advances
  (let* ((label (if roots "rt:collect-roots" "rt:scan-fields"))
         (entry (collection-linux-offset label))
         (register (if roots 9 11))
         (cursor (proof-world-reg register world))
         (next (collection-trace-effect (collection-linux-trace label '(4 5 6) origin)
                                        world))
         (stored (collection-write-word cursor (proof-world-reg 0 world) world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 16)))
             (and (equal (proof-world-pc next) (+ origin entry))
                  (equal (proof-world-reg register next)
                         (boymoo-model::a64-unsigned 64 (+ cursor 8)))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine stored))))))
  :hints (("Goal" :cases (roots))))

(defthm collection-scan-cons-advances-to-first-field
  (let* ((entry (collection-linux-offset "rt:scan-cons"))
         (cell (boymoo-model::a64-unsigned 64 (- (proof-world-reg 22 world) 16)))
         (next (collection-trace-effect
                (collection-linux-trace "rt:scan-cons" '(0 1 2) origin) world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:forward")))
                  (equal (proof-world-reg 30 next) (+ origin entry 12))
                  (equal (proof-world-reg 22 next) cell)
                  (equal (proof-world-reg 0 next) (collection-read-word cell world))))))

(defthm collection-scan-cons-stores-first-and-forwards-second
  (let* ((entry (collection-linux-offset "rt:scan-cons"))
         (cell (proof-world-reg 22 world))
         (next (collection-trace-effect
                (collection-linux-trace "rt:scan-cons" '(3 4 5) origin) world))
         (stored (collection-write-word cell (proof-world-reg 0 world) world)))
    (implies (and (collection-cpu-p world) (proof-span-p cell 16)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 12)))
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:forward")))
                  (equal (proof-world-reg 30 next) (+ origin entry 24))
                  (equal (proof-world-reg 0 next) (collection-read-word (+ cell 8) world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine stored)))))))

(defthm collection-scan-cons-stores-second-and-resumes
  (let* ((entry (collection-linux-offset "rt:scan-cons"))
         (cell (proof-world-reg 22 world))
         (next (collection-trace-effect
                (collection-linux-trace "rt:scan-cons" '(6 7) origin) world))
         (stored (collection-write-word (+ cell 8) (proof-world-reg 0 world) world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 24)))
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:scan")))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine stored)))))))
