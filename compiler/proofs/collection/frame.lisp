(in-package "BOYMOO-PROOFS")

(include-book "runtime-layout")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-sp
                     boymoo-model::a64-unsigned boymoo-model::a64-sp
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defun collection-frame-words (base world)
  (list (collection-read-word base world)
        (collection-read-word (+ base 8) world)
        (collection-read-word (+ base 16) world)
        (collection-read-word (+ base 24) world)
        (collection-read-word (+ base 32) world)
        (collection-read-word (+ base 40) world)
        (collection-read-word (+ base 48) world)
        (collection-read-word (+ base 56) world)))

(defun collection-saved-registers (world)
  (list (proof-world-reg 0 world) (proof-world-reg 1 world)
        (proof-world-reg 29 world) (proof-world-reg 30 world)
        (proof-world-reg 21 world) (proof-world-reg 22 world)
        (proof-world-reg 19 world) (proof-world-reg 20 world)))

(defthm collection-saves-request-and-frame
  (let* ((entry (collection-linux-offset "rt:collect"))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (saved (collection-trace-effect
                 (collection-linux-trace "rt:collect" '(0 1 2 3) origin) world)))
    (implies (and (collection-cpu-p world) (<= 64 sp)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (and (equal (proof-world-pc saved) (+ origin entry 16))
                  (equal (boymoo-model::a64-sp (proof-world-machine saved)) (- sp 64))
                  (equal (collection-frame-words (- sp 64) saved)
                         (collection-saved-registers world))))))

(defthm collection-restores-request-and-frame
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (restored (collection-trace-effect
                    (collection-linux-trace "rt:collect-finish" '(37 38 39 40) origin)
                    world)))
    (implies (and (collection-cpu-p world) (unsigned-byte-p 64 (+ sp 64))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 148)))
             (and (equal (proof-world-pc restored) (+ origin entry 164))
                  (equal (boymoo-model::a64-sp (proof-world-machine restored)) (+ sp 64))
                  (equal (collection-saved-registers restored) (collection-frame-words sp world))
                  (equal (boymoo-model::a64-memory (proof-world-machine restored))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))
