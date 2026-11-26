(in-package "BOYMOO-PROOFS")

(include-book "retirement")
(include-book "segments")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun collection-diagnostic-reply-p (reply count)
  (or (proof-linux-errno-p reply)
      (and (natp reply) (<= reply count))))

(defun collection-write-round-prefix (origin)
  (append (collection-linux-trace "rt:write-loop" '(0 1 2 3 4 5 6) origin)
          (collection-linux-trace "sys:write" '(0) origin)))

(defun collection-write-round-suffix (reply origin)
  (append (collection-linux-trace "sys:write" '(1 2) origin)
          (collection-linux-trace "rt:write-loop"
                                  (if (posp reply) '(7 8 9 10 11) '(7 8)) origin)))

(defun collection-write-round (reply origin)
  (append (collection-write-round-prefix origin)
          (collection-write-round-suffix reply origin)))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc
                     proof-world-regions proof-world-replies proof-world-stdout
                     proof-world-stop proof-reg proof-load-word
                     proof-instruction-effect proof-step proof-covered-p
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-write-flags collection-read-word collection-write-word
                     collection-write-sp collection-subtract-flags
                     boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand))))

(local
 (defthm collection-diagnostic-world-slot-after-cpu-action
   (and (equal (proof-world-regions (collection-write-pc pc world))
               (proof-world-regions world))
        (equal (proof-world-regions (collection-write-register reg value world))
               (proof-world-regions world))
        (equal (proof-world-regions (collection-write-flags flags world))
               (proof-world-regions world))
        (equal (proof-world-replies (collection-write-pc pc world))
               (proof-world-replies world))
        (equal (proof-world-replies (collection-write-register reg value world))
               (proof-world-replies world))
        (equal (proof-world-replies (collection-write-flags flags world))
               (proof-world-replies world))
        (equal (proof-world-stop (collection-write-pc pc world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-register reg value world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-flags flags world)) (proof-world-stop world))
        (equal (proof-world-stdout (collection-write-pc pc world)) (proof-world-stdout world))
        (equal (proof-world-stdout (collection-write-register reg value world))
               (proof-world-stdout world))
        (equal (proof-world-stdout (collection-write-flags flags world))
               (proof-world-stdout world)))
   :hints (("Goal" :in-theory (enable proof-world-regions proof-world-replies
                                     proof-world-stop proof-world-stdout)))))

(defthm collection-write-round-opens-linux-syscall
  (let* ((entry (collection-linux-offset "rt:write-loop"))
         (count (proof-world-reg 21 world))
         (call (collection-trace-effect (collection-write-round-prefix origin) world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry))
                  (posp count) (<= count #x100000))
             (and (collection-cpu-p call)
                  (equal (proof-world-pc call)
                         (+ origin (collection-linux-offset "sys:write") 4))
                  (equal (proof-world-reg 30 call) (+ origin entry 28))
                  (equal (proof-world-reg 0 call) (proof-world-reg 19 world))
                  (equal (proof-world-reg 1 call) (proof-world-reg 20 world))
                  (equal (proof-world-reg 2 call) count)
                  (equal (proof-world-reg 8 call) 64)
                  (equal (proof-world-replies call) (proof-world-replies world))
                  (equal (proof-world-regions call) (proof-world-regions world))
                  (equal (proof-world-stop call) (proof-world-stop world))
                  (equal (proof-world-stdout call) (proof-world-stdout world))
                  (equal (boymoo-model::a64-sp (proof-world-machine call))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine call))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal reg '(0 1 2 8 30)))
                           (equal (proof-world-reg reg call) (proof-world-reg reg world)))))))

(local
 (defthm collection-svc-zero-is-linux-call
   (equal (proof-instruction-effect '(:svc 0) world)
          (proof-linux-svc
           (list :svc 0 (proof-world-reg 16 world) (proof-world-reg 8 world)) world))
   :hints (("Goal" :in-theory (e/d (proof-instruction-effect proof-world-reg proof-reg)
                                   (boymoo-model::a64-read-reg proof-linux-svc))))))

(defthm collection-diagnostic-write-svc-effect
  (let* ((address (proof-world-reg 1 world))
         (count (proof-world-reg 2 world))
         (replies (proof-world-replies world))
         (reply (car replies)))
    (implies (and (equal (proof-world-reg 8 world) 64)
                  (equal (proof-world-reg 0 world) 2)
                  (proof-covered-p address count :read (proof-world-regions world))
                  (consp replies)
                  (collection-diagnostic-reply-p reply count))
             (equal (proof-instruction-effect '(:svc 0) world)
                    (proof-svc-return
                     reply
                     (if (proof-linux-errno-p reply)
                         world
                       (update-nth 5
                                   (append (proof-world-stderr world)
                                           (proof-byte-list reply address (proof-world-machine world)))
                                   world)))))))

(local
 (defthm collection-diagnostic-svc-return-actions
   (equal (proof-svc-return reply world)
          (update-nth 6 (cdr (proof-world-replies world))
                      (collection-write-register 0 reply (collection-next-instruction world))))
   :hints (("Goal" :in-theory (e/d (collection-write-register collection-write-pc proof-world-machine)
                                   (collection-pc-over-register))))))

(local
 (defthm collection-diagnostic-kernel-slot-projections
   (implies (and (natp slot) (< 0 slot))
            (and (equal (proof-world-machine (update-nth slot data world)) (proof-world-machine world))
                 (equal (proof-world-reg reg (update-nth slot data world)) (proof-world-reg reg world))
                 (equal (proof-world-pc (update-nth slot data world)) (proof-world-pc world))
                 (equal (collection-cpu-p (update-nth slot data world)) (collection-cpu-p world))
                 (equal (proof-world-regions (update-nth slot data world))
                        (if (equal slot 1) data (proof-world-regions world)))
                 (equal (proof-world-replies (update-nth slot data world))
                        (if (equal slot 6) data (proof-world-replies world)))
                 (equal (proof-world-stdout (update-nth slot data world))
                        (if (equal slot 4) data (proof-world-stdout world)))
                 (equal (proof-world-stop (update-nth slot data world))
                        (if (equal slot 7) data (proof-world-stop world)))))
   :hints (("Goal" :in-theory (enable proof-world-machine proof-world-reg proof-world-pc
                                     collection-cpu-p proof-world-regions proof-world-replies
                                     proof-world-stdout proof-world-stop)))))

(local
 (defthm collection-diagnostic-service-preserves-machine-frame
   (let* ((reply (car (proof-world-replies world)))
          (next (proof-instruction-effect '(:svc 0) world)))
     (implies (and (collection-cpu-p world)
                   (equal (proof-world-reg 8 world) 64)
                   (equal (proof-world-reg 0 world) 2)
                   (proof-covered-p (proof-world-reg 1 world) (proof-world-reg 2 world)
                                    :read (proof-world-regions world))
                   (consp (proof-world-replies world))
                   (collection-diagnostic-reply-p reply (proof-world-reg 2 world)))
              (and (equal (collection-cpu-p next) (collection-cpu-p world))
                   (equal (proof-world-pc next)
                          (boymoo-model::a64-unsigned 64 (+ 4 (proof-world-pc world))))
                   (equal (proof-world-replies next) (cdr (proof-world-replies world)))
                   (equal (proof-world-regions next) (proof-world-regions world))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (equal (proof-world-stdout next) (proof-world-stdout world))
                   (equal (boymoo-model::a64-sp (proof-world-machine next))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine next))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (equal (proof-world-reg reg next)
                          (if (equal reg 0)
                              (boymoo-model::a64-unsigned 64 reply)
                            (proof-world-reg reg world))))))
   :hints (("Goal"
            :in-theory (disable proof-svc-return proof-linux-svc proof-linux-write
                                collection-diagnostic-reply-p collection-svc-zero-is-linux-call
                                proof-byte-list proof-linux-errno-p)))))

(local
 (defthm collection-diagnostic-test-after-subtracting-zero
   (implies (unsigned-byte-p 64 word)
            (equal (boymoo-model::a64-condition 13 (collection-subtract-flags word 0))
                   (or (equal word 0) (logbitp 63 word))))
   :hints (("Goal" :cases ((logbitp 63 word) (equal word 0))
                   :in-theory (enable boymoo-model::a64-condition
                                      boymoo-model::a64-result-flags
                                      collection-subtract-flags)))))

(local
 (defthm collection-diagnostic-word-high-bit
   (implies (unsigned-byte-p 64 word)
            (equal (logbitp 63 word) (<= (expt 2 63) word)))
   :hints (("Goal" :cases ((< word (expt 2 63)))
                   :in-theory (e/d (logbitp)
                                     (floor acl2::floor-unique-equal-version
                                            acl2::equal-of-0-and-floor-gen))
                   :use ((:instance acl2::floor-unique (acl2::i word)
                                    (acl2::j (expt 2 63)) (acl2::n 0))
                         (:instance acl2::floor-unique (acl2::i word)
                                    (acl2::j (expt 2 63)) (acl2::n 1)))))))

(local
 (defthm collection-diagnostic-negative-reply-word
   (implies (and (integerp reply) (<= -4095 reply) (< reply 0))
            (equal (boymoo-model::a64-unsigned 64 reply) (+ (expt 2 64) reply)))
   :hints (("Goal"
                   :use ((:instance collection-word-ignore-modulus (value reply)))
                   :in-theory (disable collection-word-ignore-modulus)))))

(local
 (in-theory (disable proof-linux-svc proof-linux-write proof-svc-return
                     collection-svc-zero-is-linux-call collection-diagnostic-write-svc-effect
                     collection-diagnostic-reply-p)))

(local
 (defthm collection-diagnostic-reply-is-bounded
   (implies (and (collection-diagnostic-reply-p reply count) (natp count))
            (and (integerp reply) (<= -4095 reply) (<= reply count)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable collection-diagnostic-reply-p)))))

(defun collection-write-loop-input-p (count replies origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin (car *collection-linux-layout*))
       (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:write-loop")))
       (equal (proof-world-reg 19 world) 2)
       (natp count) (<= count #x100000)
       (equal (proof-world-reg 21 world) count)
       (equal (proof-world-replies world) replies)
       (if (zp count)
           t
         (and (proof-covered-p (proof-world-reg 20 world) count :read (proof-world-regions world))
              (unsigned-byte-p 64 (+ (proof-world-reg 20 world) count))))))

(local
 (in-theory (disable collection-write-round-prefix)))

(defthm collection-write-round-consumes-reply
  (let* ((reply (car replies))
         (after (collection-trace-effect (collection-write-round reply origin) world)))
    (implies (and (collection-write-loop-input-p count replies origin world)
                  (posp count) (consp replies)
                  (collection-diagnostic-reply-p reply count))
             (and (collection-cpu-p after)
                  (equal (proof-world-pc after)
                         (+ origin (collection-linux-offset
                                    (if (posp reply) "rt:write-loop" "rt:write-failed"))))
                  (implies (posp reply)
                           (and (equal (proof-world-reg 20 after) (+ (proof-world-reg 20 world) reply))
                                (equal (proof-world-reg 21 after) (- count reply))))
                  (equal (proof-world-replies after) (cdr replies))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (proof-world-stdout after) (proof-world-stdout world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal reg '(0 1 2 8 20 21 30)))
                           (equal (proof-world-reg reg after) (proof-world-reg reg world))))))
  :rule-classes nil
  :hints (("Goal" :cases ((< (car replies) 0) (equal (car replies) 0))
                  :in-theory (disable collection-diagnostic-reply-is-bounded
                                      collection-write-round-opens-linux-syscall)
                  :use ((:instance collection-diagnostic-reply-is-bounded (reply (car replies)))
                        (:instance collection-write-round-opens-linux-syscall)
                        (:instance collection-write-round-opens-linux-syscall (reg 20))
                        (:instance collection-write-round-opens-linux-syscall (reg 21))))))

(defun collection-diagnostic-replies-p (count replies)
  (declare (xargs :measure (acl2-count replies)))
  (or (zp count)
      (and (consp replies)
           (collection-diagnostic-reply-p (car replies) count)
           (or (not (posp (car replies)))
               (collection-diagnostic-replies-p (- count (car replies)) (cdr replies))))))

(defun collection-diagnostic-replies-after (count replies)
  (declare (xargs :measure (acl2-count replies)))
  (cond ((or (zp count) (endp replies)) replies)
        ((posp (car replies))
         (collection-diagnostic-replies-after (- count (car replies)) (cdr replies)))
        (t (cdr replies))))

(defun collection-write-loop-trace (count replies origin)
  (declare (xargs :measure (acl2-count replies)))
  (cond ((zp count)
         (append (collection-linux-trace "rt:write-loop" '(0) origin)
                 (collection-linux-trace "rt:write-done" '(0 1) origin)))
        ((endp replies) nil)
        (t (let ((reply (car replies)))
             (append (collection-write-round reply origin)
                     (if (posp reply)
                         (collection-write-loop-trace (- count reply) (cdr replies) origin)
                       (collection-linux-trace "rt:write-failed" '(0) origin)))))))

(local
 (defthm collection-write-positive-round-keeps-loop-input
   (let* ((reply (car replies))
          (after (collection-trace-effect (collection-write-round reply origin) world)))
     (implies (and (collection-write-loop-input-p count replies origin world)
                   (posp count) (consp replies) (posp reply)
                   (collection-diagnostic-reply-p reply count))
              (collection-write-loop-input-p (- count reply) (cdr replies) origin after)))
   :hints (("Goal"
            :use ((:instance collection-write-round-consumes-reply (reg 19))
                  (:instance collection-covered-subspan
                             (base (proof-world-reg 20 world)) (extent count)
                             (address (+ (proof-world-reg 20 world) (car replies)))
                             (width (- count (car replies)))
                             (access :read) (regions (proof-world-regions world))))
            :in-theory (e/d (collection-diagnostic-reply-p)
                             (collection-write-round collection-trace-effect))))))

(local
 (in-theory (disable collection-write-round collection-write-round-suffix)))

(local
 (defthm collection-write-no-bytes-selects-return
   (let ((after (collection-trace-effect (collection-write-loop-trace 0 replies origin) world)))
     (implies (collection-write-loop-input-p 0 replies origin world)
              (and (collection-cpu-p after)
                   (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:write-return")))
                   (equal (proof-world-replies after) replies)
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (equal (proof-world-stdout after) (proof-world-stdout world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (implies (not (equal reg 0))
                            (equal (proof-world-reg reg after) (proof-world-reg reg world))))))))

(local
 (defthm collection-write-failure-selects-return
   (let ((after (collection-trace-effect (collection-linux-trace "rt:write-failed" '(0) origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:write-failed"))))
              (and (collection-cpu-p after)
                   (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:write-return")))
                   (equal (proof-world-replies after) (proof-world-replies world))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (equal (proof-world-stdout after) (proof-world-stdout world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (implies (not (equal reg 0))
                            (equal (proof-world-reg reg after) (proof-world-reg reg world))))))))

(local
 (defun collection-write-loop-induction (count replies origin world)
   (declare (xargs :measure (acl2-count replies)))
   (if (or (zp count) (endp replies) (not (posp (car replies))))
       world
     (collection-write-loop-induction
      (- count (car replies)) (cdr replies) origin
      (collection-trace-effect (collection-write-round (car replies) origin) world)))))

(defthm collection-write-loop-reaches-restore
  (let* ((trace (collection-write-loop-trace count replies origin))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-write-loop-input-p count replies origin world)
                  (collection-diagnostic-replies-p count replies))
             (and (collection-cpu-p after)
                  (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:write-return")))
                  (equal (proof-world-replies after) (collection-diagnostic-replies-after count replies))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (proof-world-stdout after) (proof-world-stdout world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal reg '(0 1 2 8 20 21 30)))
                           (equal (proof-world-reg reg after) (proof-world-reg reg world))))))
  :hints (("Goal" :induct (collection-write-loop-induction count replies origin world)
                  :in-theory (disable collection-write-loop-input-p
                                      collection-write-positive-round-keeps-loop-input
                                      collection-trace-effect))
          ("Subgoal *1/2"
           :use ((:instance collection-write-round-consumes-reply)
                 (:instance collection-write-positive-round-keeps-loop-input)))
          ("Subgoal *1/1" :cases ((zp count))
           :in-theory (enable collection-write-loop-input-p)
           :use ((:instance collection-write-round-consumes-reply)
                 (:instance collection-write-failure-selects-return
                            (world (collection-trace-effect
                                    (collection-write-round (car replies) origin) world)))))))
