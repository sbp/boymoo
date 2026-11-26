(in-package "BOYMOO-PROOFS")

; The system call wrappers of LINUX-SYSTEM-CODE, up to their SVC.
;
; The exit wrapper sys:exit is the instruction (:movz 8 94 0) followed by
; (:svc 0). From its first instruction, two steps under the kernel rules
; stop the process with the low eight bits of register 0 as its exit
; status.

(include-book "load")

(logic)
(set-verify-guards-eagerness 0)

(defconst *linux-exit-movz* '(:move-wide 2 64 8 94 0))
(defconst *linux-exit-svc* '(:svc 0))

(defthm linux-exit-instructions-are-assembled
  (and (equal (proof-decode (boymoo-compiler::a64-word '(:movz 8 94 0) 0 nil))
              *linux-exit-movz*)
       (equal (proof-decode (boymoo-compiler::a64-word '(:svc 0) 0 nil))
              *linux-exit-svc*))
  :rule-classes nil)

(defthm linux-exit-movz-effect
  (equal (proof-execute *linux-exit-movz* m)
         (update-nth 0 (put-assoc-equal 8 94 (boymoo-model::a64-registers m))
                     (boymoo-model::a64-set-pc (+ (boymoo-model::a64-pc m) 4) m))))

(defthm linux-exit-svc-effect
  (equal (proof-execute *linux-exit-svc* m)
         (list :svc 0
               (boymoo-model::a64-read-reg 16 64 nil m)
               (boymoo-model::a64-read-reg 8 64 nil m))))

(defthm linux-assoc-put-assoc-same
  (equal (assoc-equal k (put-assoc-equal k v a)) (cons k v)))

(defthm linux-assoc-put-assoc-other
  (implies (not (equal j k))
           (equal (assoc-equal j (put-assoc-equal k v a)) (assoc-equal j a))))

(defthm linux-covered-span
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :rule-classes nil)

(defthm linux-nth-update-nth
  (equal (nth i (update-nth j v l))
         (if (equal (nfix i) (nfix j)) v (nth i l))))

(defthm linux-car-update-nth-0
  (equal (car (update-nth 0 v l)) v))

(defthm linux-consp-put-assoc
  (consp (put-assoc-equal k v a)))

(in-theory (disable proof-execute proof-decode boymoo-model::a64-read-bytes
                    update-nth))

(defthm linux-decode-at-after-register-write
  (equal (proof-decode-at a (update-nth 0 r (update-nth 2 p m)))
         (proof-decode-at a m)))

(defthm linux-instruction-at-after-register-write
  (equal (proof-instruction-at-p
          i a (update-nth 0 (update-nth 0 r (update-nth 2 p (car world))) world))
         (proof-instruction-at-p i a world)))

(defthm linux-fetchable-range
  (implies (proof-fetchable-p a world)
           (and (natp a) (<= (+ 4 a) (expt 2 64))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance linux-covered-span
                                   (address a) (size 4) (access :execute)
                                   (regions (proof-world-regions world)))))))

(defthm linux-instruction-at-range
  (implies (proof-instruction-at-p i a world)
           (and (natp a) (<= (+ 4 a) (expt 2 64))))
  :rule-classes nil
  :hints (("Goal" :use linux-fetchable-range
                  :in-theory (disable proof-fetchable-p))))

(defun linux-after-exit-movz (world)
  (update-nth 0
              (update-nth 0
                          (put-assoc-equal 8 94 (boymoo-model::a64-registers
                                                 (nth 0 world)))
                          (boymoo-model::a64-set-pc (+ (proof-world-pc world) 4)
                                                    (nth 0 world)))
              world))

(defthm linux-exit-first-step
  (implies (and (not (proof-world-stop world))
                (proof-instruction-at-p *linux-exit-movz*
                                        (proof-world-pc world) world))
           (equal (proof-step world) (linux-after-exit-movz world)))
  :hints (("Goal" :use ((:instance proof-step-from-instruction
                                   (instruction *linux-exit-movz*)))
                  :in-theory (disable proof-step-from-instruction proof-step
                                      proof-instruction-at-p))))

(defthm linux-exit-second-step
  (implies (and (consp world)
                (not (proof-world-stop world))
                (proof-instruction-at-p *linux-exit-svc*
                                        (+ 4 (proof-world-pc world)) world))
           (equal (proof-world-stop (proof-step (linux-after-exit-movz world)))
                  (cons :exit
                        (boymoo-model::a64-unsigned 8 (proof-world-reg 0 world)))))
  :hints (("Goal" :use ((:instance proof-step-from-instruction
                                   (instruction *linux-exit-svc*)
                                   (world (linux-after-exit-movz world)))
                        (:instance linux-instruction-at-range
                                   (i *linux-exit-svc*)
                                   (a (+ 4 (proof-world-pc world)))))
                  :in-theory (disable proof-step-from-instruction proof-step
                                      proof-instruction-at-p))))

(defthm linux-sys-exit-wrapper
  (implies (and (consp world)
                (not (proof-world-stop world))
                (proof-instruction-at-p *linux-exit-movz*
                                        (proof-world-pc world) world)
                (proof-instruction-at-p *linux-exit-svc*
                                        (+ 4 (proof-world-pc world)) world))
           (equal (proof-world-stop (proof-advance 2 world))
                  (cons :exit
                        (boymoo-model::a64-unsigned 8 (proof-world-reg 0 world)))))
  :hints (("Goal" :expand ((proof-advance 2 world)
                           (proof-advance 1 (proof-step world))
                           (proof-advance 0 (proof-step (proof-step world))))
                  :in-theory (disable proof-step proof-instruction-at-p
                                      linux-after-exit-movz proof-world-stop
                                      proof-world-pc proof-world-reg))))

; The wrappers sys:map, sys:release, sys:unmap, sys:read and sys:write
; each contain (:movz 8 NUMBER 0) followed by (:svc 0), with NUMBER 222,
; 233, 215, 63 and 64. From the MOVZ, two steps reach the world that the
; kernel rule PROOF-LINUX-SVC gives for that system call number, and the
; registers other than register 8 are as they were before the MOVZ.

(defun linux-movz-8 (number)
  (list :move-wide 2 64 8 number 0))

(defthm linux-movz-8-is-assembled
  (and (equal (proof-decode (boymoo-compiler::a64-word '(:movz 8 222 0) 0 nil))
              (linux-movz-8 222))
       (equal (proof-decode (boymoo-compiler::a64-word '(:movz 8 233 0) 0 nil))
              (linux-movz-8 233))
       (equal (proof-decode (boymoo-compiler::a64-word '(:movz 8 215 0) 0 nil))
              (linux-movz-8 215))
       (equal (proof-decode (boymoo-compiler::a64-word '(:movz 8 63 0) 0 nil))
              (linux-movz-8 63))
       (equal (proof-decode (boymoo-compiler::a64-word '(:movz 8 64 0) 0 nil))
              (linux-movz-8 64)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-decode))))

(defthm linux-movz-8-effect
  (implies (and (natp number) (< number 65536))
           (equal (proof-execute (list :move-wide 2 64 8 number 0) m)
                  (update-nth 0 (put-assoc-equal 8 number
                                                 (boymoo-model::a64-registers m))
                              (boymoo-model::a64-set-pc
                               (+ (boymoo-model::a64-pc m) 4) m))))
  :hints (("Goal" :in-theory (enable proof-execute ash update-nth))))

(defun linux-after-movz (number world)
  (update-nth 0
              (update-nth 0
                          (put-assoc-equal 8 number (boymoo-model::a64-registers
                                                     (nth 0 world)))
                          (boymoo-model::a64-set-pc (+ (proof-world-pc world) 4)
                                                    (nth 0 world)))
              world))

(defthm linux-movz-first-step
  (implies (and (natp number) (< number 65536)
                (not (proof-world-stop world))
                (proof-instruction-at-p (linux-movz-8 number)
                                        (proof-world-pc world) world))
           (equal (proof-step world) (linux-after-movz number world)))
  :hints (("Goal" :use ((:instance proof-step-from-instruction
                                   (instruction (linux-movz-8 number))))
                  :in-theory (disable proof-step-from-instruction proof-step
                                      proof-instruction-at-p))))

(defthm linux-svc-second-step
  (implies (and (natp number) (< number 65536)
                (consp world)
                (not (proof-world-stop world))
                (proof-instruction-at-p *linux-exit-svc*
                                        (+ 4 (proof-world-pc world)) world))
           (equal (proof-step (linux-after-movz number world))
                  (proof-linux-svc
                   (list :svc 0 (proof-world-reg 16 world) number)
                   (linux-after-movz number world))))
  :hints (("Goal" :use ((:instance proof-step-from-instruction
                                   (instruction *linux-exit-svc*)
                                   (world (linux-after-movz number world)))
                        (:instance linux-instruction-at-range
                                   (i *linux-exit-svc*)
                                   (a (+ 4 (proof-world-pc world)))))
                  :in-theory (disable proof-step-from-instruction proof-step
                                      proof-instruction-at-p proof-linux-svc))))

(defthm linux-svc-wrapper
  (implies (and (natp number) (< number 65536)
                (consp world)
                (not (proof-world-stop world))
                (proof-instruction-at-p (linux-movz-8 number)
                                        (proof-world-pc world) world)
                (proof-instruction-at-p *linux-exit-svc*
                                        (+ 4 (proof-world-pc world)) world))
           (equal (proof-advance 2 world)
                  (proof-linux-svc
                   (list :svc 0 (proof-world-reg 16 world) number)
                   (linux-after-movz number world))))
  :hints (("Goal" :expand ((proof-advance 2 world)
                           (proof-advance 1 (proof-step world))
                           (proof-advance 0 (proof-step (proof-step world))))
                  :in-theory (disable proof-step proof-instruction-at-p
                                      linux-after-movz proof-world-stop
                                      proof-world-pc proof-world-reg
                                      proof-linux-svc))))

(defthm linux-after-movz-registers
  (implies (and (natp register) (< register 31) (not (equal register 8)))
           (equal (proof-world-reg register (linux-after-movz number world))
                  (proof-world-reg register world))))
