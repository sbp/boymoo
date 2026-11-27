(in-package "BOYMOO-PROOFS")

(include-book "diagnostic-write")
(include-book "frame-protection")
(include-book "scanner")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-write-all-prologue (origin)
  (collection-linux-trace "rt:write-all" '(0 1 2 3 4) origin))

(defun collection-write-all-epilogue (origin)
  (collection-linux-trace "rt:write-return" '(0 1 2) origin))

(defun collection-write-all-trace (count replies origin)
  (append (collection-write-all-prologue origin)
          (collection-write-loop-trace count replies origin)
          (collection-write-all-epilogue origin)))

(defun collection-write-frame (sp world)
  (list (collection-read-word (- sp 32) world)
        (collection-read-word (- sp 24) world)
        (collection-read-word (- sp 16) world)
        (collection-read-word (- sp 8) world)))

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     proof-world-regions proof-world-replies proof-world-stdout proof-world-stop
                     proof-covered-p
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-write-sp collection-subtract-flags
                     boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand)
                     (:definition acl2::binary-logior))))

(defun collection-write-all-input-p (count replies origin world)
  (let ((sp (boymoo-model::a64-sp (proof-world-machine world)))
        (address (proof-world-reg 1 world)))
    (and (collection-cpu-p world)
         (proof-span-p origin (car *collection-linux-layout*))
         (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:write-all")))
         (equal (proof-world-reg 0 world) 2)
         (equal (proof-world-reg 2 world) count)
         (natp count) (<= count #x100000)
         (equal (proof-world-replies world) replies)
         (<= 32 sp)
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (if (zp count)
             t
           (and (proof-covered-p address count :read (proof-world-regions world))
                (unsigned-byte-p 64 (+ address count)))))))

(local
 (defthm collection-write-all-prologue-opens-loop
   (let* ((after (collection-trace-effect (collection-write-all-prologue origin) world))
          (sp (boymoo-model::a64-sp (proof-world-machine world))))
     (implies (collection-write-all-input-p count replies origin world)
              (and (collection-write-loop-input-p count replies origin after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) (- sp 32))
                   (equal (collection-write-frame sp after)
                          (list (proof-world-reg 21 world) (proof-world-reg 30 world)
                                (proof-world-reg 19 world) (proof-world-reg 20 world)))
                   (alistp (boymoo-model::a64-memory (proof-world-machine after)))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (proof-world-stdout after) (proof-world-stdout world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (implies (not (member-equal reg '(19 20 21)))
                            (equal (proof-world-reg reg after) (proof-world-reg reg world))))))
   :hints (("Goal" :in-theory (enable proof-world-replies proof-world-stop proof-world-stdout)))))

(local
 (defthm collection-write-all-epilogue-restores-frame
   (let* ((base (boymoo-model::a64-sp (proof-world-machine world)))
          (sp (+ base 32))
          (after (collection-trace-effect (collection-write-all-epilogue origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:write-return")))
                   (unsigned-byte-p 64 sp))
              (and (collection-cpu-p after)
                   (equal (proof-world-pc after) (cadr (collection-write-frame sp world)))
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                   (equal (proof-world-reg 21 after) (nth 0 (collection-write-frame sp world)))
                   (equal (proof-world-reg 30 after) (nth 1 (collection-write-frame sp world)))
                   (equal (proof-world-reg 19 after) (nth 2 (collection-write-frame sp world)))
                   (equal (proof-world-reg 20 after) (nth 3 (collection-write-frame sp world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (proof-world-replies after) (proof-world-replies world))
                   (equal (proof-world-stdout after) (proof-world-stdout world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (implies (not (member-equal reg '(19 20 21 30)))
                            (equal (proof-world-reg reg after) (proof-world-reg reg world))))))
   :hints (("Goal" :in-theory (enable proof-world-replies proof-world-stop proof-world-stdout)))))

(local
 (defthm collection-write-frame-depends-on-byte-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-write-frame sp first)
                   (collection-write-frame sp second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                   (boymoo-model::a64-read-bytes))))))

(local
 (in-theory (disable collection-write-all-input-p collection-write-frame collection-write-loop-input-p
                     collection-write-all-prologue collection-write-all-epilogue
                     collection-write-loop-trace collection-diagnostic-replies-p
                     collection-diagnostic-replies-after collection-trace-effect)))

(defthm collection-diagnostic-write-all-returns
  (let* ((trace (collection-write-all-trace count replies origin))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-write-all-input-p count replies origin world)
                  (collection-diagnostic-replies-p count replies))
             (and (collection-cpu-p after)
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (proof-world-replies after) (collection-diagnostic-replies-after count replies))
                  (equal (proof-world-stdout after) (proof-world-stdout world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (alistp (boymoo-model::a64-memory (proof-world-machine after)))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (implies (not (member-equal reg '(0 1 2 8)))
                           (equal (proof-world-reg reg after) (proof-world-reg reg world))))))
  :hints (("Goal" :use ((:instance collection-write-all-prologue-opens-loop)
                        (:instance collection-write-loop-reaches-restore
                                   (world (collection-trace-effect (collection-write-all-prologue origin) world)))
                        (:instance collection-write-all-epilogue-restores-frame
                                   (world (collection-trace-effect
                                           (collection-write-loop-trace count replies origin)
                                           (collection-trace-effect (collection-write-all-prologue origin) world))))
                        (:instance collection-write-frame-depends-on-byte-memory
                                   (first (collection-trace-effect
                                           (collection-write-loop-trace count replies origin)
                                           (collection-trace-effect (collection-write-all-prologue origin) world)))
                                   (second (collection-trace-effect (collection-write-all-prologue origin) world))
                                   (sp (boymoo-model::a64-sp (proof-world-machine world)))))
                  :in-theory (e/d (collection-write-frame)
                                   (collection-write-all-prologue-opens-loop
                                    collection-write-all-epilogue-restores-frame
                                    collection-write-loop-reaches-restore)))
          (and stable-under-simplificationp '(:in-theory (enable collection-write-all-input-p)))))

(defun collection-size-message-label (kind)
  (if (eq kind :heap-size) "rt:heap-size-message" "rt:datum-size-message"))

(defun collection-size-message-length (kind)
  (if (eq kind :heap-size)
      (length "memory exhausted: the heap is at its largest")
    (length "memory exhausted: a datum is too large")))

(defun collection-size-diagnostic-input-p (kind origin world)
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (message (+ origin (collection-linux-offset (collection-size-message-label kind))))
         (count (collection-size-message-length kind))
         (newline (+ origin (collection-linux-offset "rt:newline")))
         (regions (proof-world-regions world)))
    (and (member-eq kind '(:allocation-size :heap-size))
         (collection-cpu-p world)
         (proof-span-p origin (car *collection-linux-layout*))
         (equal (proof-world-pc world) (+ origin (collection-linux-offset (proof-resource-label kind))))
         (<= 32 sp)
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (proof-covered-p message count :read regions)
         (proof-covered-p newline 1 :read regions))))

(defun collection-size-diagnostic-open (kind origin)
  (append (collection-linux-trace (proof-resource-label kind) '(0 1 2 3) origin)
          (collection-linux-trace "rt:stop" '(0 1 2) origin)))

(defun collection-size-diagnostic-newline (origin)
  (collection-linux-trace "rt:stop" '(3 4 5 6) origin))

(defun collection-size-diagnostic-exit (origin)
  (append (collection-linux-trace "rt:stop" '(7 8) origin)
          (collection-linux-trace "sys:exit" '(0) origin)))

(defun collection-size-diagnostic-prefix (kind replies origin)
  (let* ((count (collection-size-message-length kind))
         (remaining (collection-diagnostic-replies-after count replies)))
    (append (collection-size-diagnostic-open kind origin)
            (collection-write-all-trace count replies origin)
            (collection-size-diagnostic-newline origin)
            (collection-write-all-trace 1 remaining origin)
            (collection-size-diagnostic-exit origin))))

(local
 (defthm collection-diagnostic-address-instruction-effect
   (implies (and (collection-cpu-p world) (natp target) (< target 31))
            (equal (proof-instruction-effect (list :address target delta nil) world)
                   (collection-write-register target (+ (proof-world-pc world) delta)
                                              (collection-next-instruction world))))
   :hints (("Goal" :in-theory (e/d (proof-instruction-effect collection-cpu-p
                                                           collection-write-register collection-write-pc
                                                           proof-world-pc proof-world-machine)
                                   (collection-pc-over-register proof-linux-svc))))))

(local
 (defthm collection-size-diagnostic-opens-message-write
   (let* ((trace (collection-size-diagnostic-open kind origin))
          (call (collection-trace-effect trace world))
          (count (collection-size-message-length kind)))
     (implies (collection-size-diagnostic-input-p kind origin world)
              (and (collection-write-all-input-p count (proof-world-replies world) origin call)
                   (equal (proof-world-stdout call) (proof-world-stdout world))
                   (equal (proof-world-stop call) (proof-world-stop world))
                   (equal (proof-world-regions call) (proof-world-regions world))
                   (equal (proof-world-reg 22 call) 3)
                   (equal (proof-world-reg 30 call) (+ origin (collection-linux-offset "rt:stop") 12)))))
   :hints (("Goal" :cases ((eq kind :heap-size))
                   :in-theory (enable collection-trace-effect collection-write-all-input-p
                                      proof-world-replies proof-world-stdout proof-world-stop)))))

(local
 (defthm collection-size-diagnostic-opens-newline-write
   (let* ((trace (collection-size-diagnostic-newline origin))
          (call (collection-trace-effect trace world))
          (sp (boymoo-model::a64-sp (proof-world-machine world))))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:stop") 12))
                   (<= 32 sp)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p (+ origin (collection-linux-offset "rt:newline")) 1
                                    :read (proof-world-regions world)))
              (and (collection-write-all-input-p 1 (proof-world-replies world) origin call)
                   (equal (proof-world-stdout call) (proof-world-stdout world))
                   (equal (proof-world-stop call) (proof-world-stop world))
                   (equal (proof-world-reg 22 call) (proof-world-reg 22 world))
                   (equal (proof-world-reg 30 call) (+ origin (collection-linux-offset "rt:stop") 28)))))
   :hints (("Goal" :in-theory (enable collection-trace-effect collection-write-all-input-p
                                      proof-world-replies proof-world-stdout proof-world-stop)))))

(local
 (defthm collection-size-diagnostic-opens-exit-syscall
   (let* ((trace (collection-size-diagnostic-exit origin))
          (call (collection-trace-effect trace world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:stop") 28)))
              (and (equal (proof-world-pc call) (+ origin (collection-linux-offset "sys:exit") 4))
                   (equal (proof-world-reg 0 call) (proof-world-reg 22 world))
                   (equal (proof-world-reg 8 call) 94)
                   (equal (proof-world-stdout call) (proof-world-stdout world))
                   (equal (proof-world-stop call) (proof-world-stop world))
                   (equal (proof-world-replies call) (proof-world-replies world)))))
   :hints (("Goal" :in-theory (enable collection-trace-effect proof-world-replies
                                      proof-world-stdout proof-world-stop)))))

(local
 (in-theory (disable collection-size-diagnostic-open collection-size-diagnostic-newline
                     collection-size-diagnostic-exit collection-write-all-trace)))

(local
 (defun collection-size-diagnostic-newline-call (kind origin world)
   (collection-trace-effect
    (collection-size-diagnostic-newline origin)
    (collection-trace-effect
     (collection-write-all-trace (collection-size-message-length kind) (proof-world-replies world) origin)
     (collection-trace-effect (collection-size-diagnostic-open kind origin) world)))))

(local
 (defthm collection-size-diagnostic-prepares-newline-call
   (let* ((count (collection-size-message-length kind))
          (replies (proof-world-replies world))
          (remaining (collection-diagnostic-replies-after count replies))
          (call (collection-size-diagnostic-newline-call kind origin world)))
     (implies (and (collection-size-diagnostic-input-p kind origin world)
                   (collection-diagnostic-replies-p count replies))
              (and (collection-write-all-input-p 1 remaining origin call)
                   (equal (proof-world-reg 22 call) 3)
                   (equal (proof-world-reg 30 call) (+ origin (collection-linux-offset "rt:stop") 28))
                   (equal (proof-world-stdout call) (proof-world-stdout world))
                   (equal (proof-world-stop call) (proof-world-stop world)))))
   :hints (("Goal"
            :use ((:instance collection-size-diagnostic-opens-message-write)
                  (:instance collection-diagnostic-write-all-returns
                             (count (collection-size-message-length kind))
                             (replies (proof-world-replies world)) (reg 22)
                             (world (collection-trace-effect (collection-size-diagnostic-open kind origin) world)))
                  (:instance collection-size-diagnostic-opens-newline-write
                             (world (collection-trace-effect
                                     (collection-write-all-trace (collection-size-message-length kind)
                                                                 (proof-world-replies world) origin)
                                     (collection-trace-effect (collection-size-diagnostic-open kind origin) world)))))
            :in-theory (e/d (collection-write-all-input-p)
                             (collection-size-diagnostic-opens-message-write
                              collection-diagnostic-write-all-returns
                              collection-size-diagnostic-opens-newline-write))))))

(local
 (defthm collection-size-diagnostic-prefix-includes-newline-call
   (let* ((replies (proof-world-replies world))
          (remaining (collection-diagnostic-replies-after (collection-size-message-length kind) replies)))
     (equal (collection-trace-effect (collection-size-diagnostic-prefix kind replies origin) world)
            (collection-trace-effect
             (collection-size-diagnostic-exit origin)
             (collection-trace-effect (collection-write-all-trace 1 remaining origin)
                                      (collection-size-diagnostic-newline-call kind origin world)))))))

(local
 (in-theory (disable collection-size-diagnostic-newline-call collection-size-diagnostic-prefix)))

(defthm collection-size-diagnostic-reaches-exit-syscall
  (let* ((count (collection-size-message-length kind))
         (replies (proof-world-replies world))
         (remaining (collection-diagnostic-replies-after count replies))
         (trace (collection-size-diagnostic-prefix kind replies origin))
         (call (collection-trace-effect trace world)))
    (implies (and (collection-size-diagnostic-input-p kind origin world)
                  (collection-diagnostic-replies-p count replies)
                  (collection-diagnostic-replies-p 1 remaining))
             (and (equal (proof-world-pc call) (+ origin (collection-linux-offset "sys:exit") 4))
                  (equal (proof-world-reg 0 call) 3)
                  (equal (proof-world-reg 8 call) 94)
                  (equal (proof-world-stdout call) (proof-world-stdout world))
                  (equal (proof-world-stop call) (proof-world-stop world))
                  (equal (proof-world-replies call) (collection-diagnostic-replies-after 1 remaining)))))
  :hints (("Goal"
           :use ((:instance collection-size-diagnostic-prepares-newline-call)
                 (:instance collection-diagnostic-write-all-returns
                            (count 1) (reg 22)
                            (replies (collection-diagnostic-replies-after (collection-size-message-length kind)
                                                                         (proof-world-replies world)))
                            (world (collection-size-diagnostic-newline-call kind origin world)))
                 (:instance collection-size-diagnostic-opens-exit-syscall
                            (world (collection-trace-effect
                                    (collection-write-all-trace
                                     1 (collection-diagnostic-replies-after (collection-size-message-length kind)
                                                                             (proof-world-replies world)) origin)
                                    (collection-size-diagnostic-newline-call kind origin world)))))
           :in-theory (disable collection-size-diagnostic-prepares-newline-call
                               collection-diagnostic-write-all-returns
                               collection-size-diagnostic-opens-exit-syscall))))

(local
 (defthm collection-exit-instruction-produces-status
   (implies (equal (proof-world-reg 8 world) 94)
            (equal (proof-instruction-effect '(:svc 0) world)
                   (proof-world-exit (proof-world-reg 0 world) world)))
   :hints (("Goal" :in-theory (e/d (proof-instruction-effect proof-world-reg proof-reg)
                                   (boymoo-model::a64-read-reg proof-world-exit))))))

(local
 (defthm collection-exit-step-produces-resource-observation
   (implies (and (not (proof-world-stop world))
                 (proof-instruction-at-p '(:svc 0) (proof-world-pc world) world)
                 (equal (proof-world-reg 8 world) 94)
                 (equal (proof-world-reg 0 world) 3)
                 (null (proof-world-stdout world)))
            (proof-resource-observation-p (proof-step world)))
   :hints (("Goal" :use ((:instance proof-step-from-instruction (instruction '(:svc 0))))
                   :in-theory (e/d (proof-world-stop proof-world-stdout proof-world-exit)
                                    (proof-instruction-at-p proof-step proof-step-from-instruction
                                     proof-fetchable-p proof-decode-at))))))

(local
 (defthm collection-checked-prefix-and-step-to-exit
   (implies (and (natp count)
                 (collection-prefix-p count nil before)
                 (equal (proof-advance count before) call)
                 (not (proof-world-stop call))
                 (equal (proof-world-stop (proof-step call)) '(:exit . 3)))
            (proof-segment-p (1+ count) nil before '(:exit . 3) (proof-step call)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-run-after-prefix (world before) (cuts nil) (fuel 1)))
            :expand ((proof-run 1 nil (proof-advance count before))
                     (proof-run 0 nil (proof-step (proof-advance count before))))
            :in-theory (disable proof-step proof-run proof-advance collection-prefix-p
                                collection-run-after-prefix proof-run-reached-without-cuts)))))

(defthm collection-empty-cut-set-has-no-intersection
  (not (intersectp-equal addresses nil))
  :hints (("Goal" :induct (len addresses))))

(defthm collection-checked-size-diagnostic-exits-with-status-three
  (let* ((replies (proof-world-replies world))
         (count (collection-size-message-length kind))
         (trace (collection-size-diagnostic-prefix kind replies origin))
         (call (collection-trace-effect trace world))
         (cut (list (+ origin (collection-linux-offset "sys:exit") 4)))
         (stop (proof-step call)))
    (implies (and (proof-resource-bound-p kind demand world)
                  (collection-size-diagnostic-input-p kind origin world)
                  (collection-diagnostic-replies-p count replies)
                  (collection-diagnostic-replies-p 1 (collection-diagnostic-replies-after count replies))
                  (collection-trace-ready-p trace cut world)
                  (proof-instruction-at-p '(:svc 0) (car cut) call)
                  (null (proof-world-stdout world)))
             (and (proof-segment-p (1+ (len trace)) nil world '(:exit . 3) stop)
                  (proof-resource-observation-p stop))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-gives-prefix
                            (trace (collection-size-diagnostic-prefix kind (proof-world-replies world) origin))
                            (terminal (list (+ origin (collection-linux-offset "sys:exit") 4))) (cuts nil))
                 (:instance collection-size-diagnostic-reaches-exit-syscall)
                 (:instance collection-exit-step-produces-resource-observation
                            (world (collection-trace-effect
                                    (collection-size-diagnostic-prefix kind (proof-world-replies world) origin)
                                    world)))
                 (:instance collection-checked-prefix-and-step-to-exit
                            (count (len (collection-size-diagnostic-prefix kind (proof-world-replies world) origin)))
                            (before world)
                            (call (collection-trace-effect
                                   (collection-size-diagnostic-prefix kind (proof-world-replies world) origin)
                                   world))))
           :in-theory (disable collection-size-diagnostic-input-p collection-size-diagnostic-prefix
                               collection-size-diagnostic-prefix-includes-newline-call
                               collection-size-diagnostic-reaches-exit-syscall
                               collection-exit-step-produces-resource-observation
                               proof-step proof-advance proof-resource-bound-p proof-segment-p
                               proof-instruction-at-p collection-run-after-prefix collection-prefix-p
                               collection-trace-ready-p collection-ready-trace-gives-prefix))))
