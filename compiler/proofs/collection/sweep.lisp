(in-package "BOYMOO-PROOFS")

(include-book "runtime-layout")
(include-book "comparisons")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned
                     boymoo-model::a64-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defun collection-sweep-entry-p (entry origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin (car *collection-linux-layout*))
       (equal (proof-world-pc world) (+ origin entry))))

(defthm collection-sweep-tests-list-end
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (head (boymoo-model::a64-unsigned 64
                 (collection-read-word (proof-world-reg 19 world) world)))
         (next (collection-trace-effect
                (collection-linux-trace "rt:sweep-string" '(0 1) origin) world)))
    (implies (collection-sweep-entry-p entry origin world)
             (and (equal (proof-world-reg 0 next) head)
                  (equal (proof-world-pc next)
                         (+ origin (if (equal head 0)
                                       (collection-linux-offset "rt:sweep-done")
                                     (+ entry 8))))))))

(defthm collection-sweep-tests-mark
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (head (proof-world-reg 0 world))
         (mark (boymoo-model::a64-unsigned 64 (collection-read-word (+ head 16) world)))
         (next (collection-trace-effect
                (collection-linux-trace "rt:sweep-string" '(2 3 4) origin) world)))
    (implies (collection-sweep-entry-p (+ entry 8) origin world)
             (and (equal (proof-world-reg 20 next)
                         (boymoo-model::a64-unsigned 64 (collection-read-word head world)))
                  (equal (proof-world-reg 1 next)
                         (boymoo-model::a64-unsigned 64 (collection-read-word (+ head 8) world)))
                  (equal (proof-world-pc next)
                         (+ origin (if (equal mark 0) (+ entry 20)
                                     (collection-linux-offset "rt:sweep-keep"))))))))

(defthm collection-sweep-unlinks-before-unmap
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (next (collection-trace-effect
                (collection-linux-trace "rt:sweep-string" '(5 6) origin) world))
         (unlinked (collection-write-word (proof-world-reg 19 world)
                                          (proof-world-reg 20 world) world)))
    (implies (collection-sweep-entry-p (+ entry 20) origin world)
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "sys:unmap")))
                  (equal (proof-world-reg 30 next) (+ origin entry 28))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 next) (proof-world-reg 1 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine unlinked)))))))

(defthm collection-sweep-keeps-and-clears-marked-mapping
  (let* ((head (proof-world-reg 0 world))
         (next (collection-trace-effect
                (collection-linux-trace "rt:sweep-keep" '(0 1 2 3) origin) world))
         (unmarked (collection-write-word (+ head 16) 0 world)))
    (implies (collection-sweep-entry-p (collection-linux-offset "rt:sweep-keep") origin world)
             (and (equal (proof-world-pc next) (+ origin (collection-linux-offset "rt:sweep-string")))
                  (equal (proof-world-reg 19 next) head)
                  (equal (proof-world-reg 22 next)
                         (boymoo-model::a64-unsigned
                          64 (+ (proof-world-reg 22 world) (proof-world-reg 1 world))))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine unmarked)))))))

(defthm collection-sweep-installs-next-string-budget
  (let* ((state (- (proof-world-reg 28 world) 128))
         (budget (max *proof-minimum-string-budget* (proof-world-reg 22 world)))
         (next (collection-trace-effect
                (collection-linux-trace "rt:sweep-done" '(0 1 2 3 4) origin) world))
         (written (collection-write-word
                   (+ state 80) budget (collection-write-word (+ state 72) 0 world))))
    (implies (and (collection-sweep-entry-p
                   (collection-linux-offset "rt:sweep-done") origin world)
                  (<= 128 (proof-world-reg 28 world)))
             (and (equal (proof-world-reg 22 next) budget)
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine written)))))))
