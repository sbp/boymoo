(in-package "BOYMOO-PROOFS")

(include-book "scanner")
(include-book "segments")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-slot-loop-label (roots)
  (if roots "rt:collect-roots" "rt:scan-fields"))

(defun collection-slot-cursor-register (roots)
  (if roots 9 11))

(defun collection-slot-limit-register (roots)
  (if roots 25 8))

(defun collection-slot-call-trace (roots origin)
  (collection-linux-trace (collection-slot-loop-label roots) '(0 1 2 3) origin))

(defun collection-slot-store-trace (roots origin)
  (collection-linux-trace (collection-slot-loop-label roots) '(4 5 6) origin))

(local
 (in-theory (disable proof-instruction-effect proof-world-machine proof-world-reg
                     proof-world-pc proof-world-stop proof-load-word proof-reg
                     collection-cpu-p collection-read-word collection-write-word
                     collection-write-register collection-write-pc collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned
                     boymoo-model::a64-memory boymoo-model::a64-read-bytes
                     boymoo-model::a64-write-bytes (:definition ash)
                     (:definition acl2::binary-logand) (:definition acl2::binary-logior))))

(defthm collection-slot-store-commits-returned-word
  (let* ((label (collection-slot-loop-label roots))
         (entry (+ origin (collection-linux-offset label)))
         (register (collection-slot-cursor-register roots))
         (limit (collection-slot-limit-register roots))
         (cursor (proof-world-reg register world))
         (after (collection-trace-effect (collection-slot-store-trace roots origin) world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ entry 16))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (unsigned-byte-p 64 (+ cursor 8)))
             (and (equal (proof-world-pc after) entry)
                  (equal (proof-world-reg register after) (+ cursor 8))
                  (equal (proof-world-reg limit after) (proof-world-reg limit world))
                  (equal (collection-read-word cursor after) (proof-world-reg 0 world))
                  (implies (and (proof-span-p other 8)
                                (proof-disjoint-p other (+ other 8) cursor (+ cursor 8)))
                           (equal (collection-read-word other after)
                                  (collection-read-word other world))))))
  :hints (("Goal" :cases (roots))))

(local
 (in-theory (disable collection-slot-call-trace collection-slot-store-trace
                     collection-trace-effect collection-trace-ready-p proof-advance
                     collection-slot-loop-label collection-slot-cursor-register
                     collection-slot-limit-register collection-linux-offset
                     proof-span-p proof-disjoint-p)))

(local
 (defthm collection-length-of-appended-traces
   (equal (len (append first second)) (+ (len first) (len second)))))

(local
 (defthm collection-strip-cars-of-appended-traces
   (equal (strip-cars (append first second))
          (append (strip-cars first) (strip-cars second)))))

(local
 (defthm collection-intersection-of-appended-trace-addresses
   (iff (intersectp-equal (append first second) cuts)
        (or (intersectp-equal first cuts) (intersectp-equal second cuts)))))

(local
 (defthm collection-advance-across-three-ready-traces
   (let* ((next (collection-trace-effect first before))
          (returned (collection-trace-effect second next))
          (after (collection-trace-effect third returned))
          (length (+ (len first) (len second) (len third))))
     (implies (and (collection-trace-ready-p first cut-first before)
                   (collection-trace-ready-p second cut-second next)
                   (collection-trace-ready-p third cut-third returned)
                   (not (intersectp-equal (strip-cars (append first second third)) cuts)))
              (and (collection-prefix-p length cuts before)
                   (equal (proof-advance length before) after))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-ready-trace-gives-prefix
                             (trace first) (terminal cut-first) (world before))
                  (:instance collection-ready-trace-gives-prefix
                             (trace second) (terminal cut-second)
                             (world (collection-trace-effect first before)))
                  (:instance collection-ready-trace-gives-prefix
                             (trace third) (terminal cut-third)
                             (world (collection-trace-effect
                                     second (collection-trace-effect first before))))
                  (:instance proof-advance-append
                             (prefix (len first)) (suffix (+ (len second) (len third)))
                             (world before))
                  (:instance proof-advance-append
                             (prefix (len second)) (suffix (len third))
                             (world (collection-trace-effect first before)))
                  (:instance collection-prefix-append
                             (first (len first)) (second (+ (len second) (len third)))
                             (world before))
                  (:instance collection-prefix-append
                             (first (len second)) (second (len third))
                             (world (collection-trace-effect first before))))
            :in-theory (disable collection-ready-trace-gives-prefix collection-prefix-append
                                proof-advance-append collection-prefix-p)))))

; The call and the store have separate cutpoints. At the loop address
; the same slot iteration can be followed by another iteration.
(defthm collection-slot-iteration-forwards-and-commits
  (let* ((label (collection-slot-loop-label roots))
         (entry (+ origin (collection-linux-offset label)))
         (call-address (+ origin (collection-linux-offset "rt:forward")))
         (link (+ entry 16))
         (cursor-register (collection-slot-cursor-register roots))
         (limit-register (collection-slot-limit-register roots))
         (cursor (proof-world-reg cursor-register before))
         (limit (proof-world-reg limit-register before))
         (call (collection-slot-call-trace roots origin))
         (call-world (collection-trace-effect call before))
         (returned (collection-trace-effect forward call-world))
         (tail (collection-slot-store-trace roots origin))
         (after (collection-trace-effect tail returned))
         (trace (append call forward tail)))
    (implies (and (collection-cpu-p before)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc before) entry)
                  (< cursor limit)
                  (collection-trace-ready-p call (list call-address) before)
                  (collection-trace-ready-p forward (list link) call-world)
                  (collection-trace-ready-p tail (list entry) returned)
                  (not (intersectp-equal (strip-cars trace) cuts))
                  (collection-cpu-p returned)
                  (equal (proof-world-pc returned) link)
                  (equal (proof-world-reg cursor-register returned) cursor)
                  (equal (proof-world-reg limit-register returned) limit)
                  (alistp (boymoo-model::a64-memory (proof-world-machine returned)))
                  (unsigned-byte-p 64 (+ cursor 8)))
             (and (collection-prefix-p (len trace) cuts before)
                  (equal (proof-advance (len trace) before) after)
                  (equal (proof-world-reg 0 call-world) (collection-read-word cursor before))
                  (equal (proof-world-pc after) entry)
                  (equal (proof-world-reg cursor-register after) (+ cursor 8))
                  (equal (proof-world-reg limit-register after) limit)
                  (equal (collection-read-word cursor after)
                         (proof-world-reg 0 returned)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-slot-loop-opens-forwarding-call (world before))
                 (:instance collection-advance-across-three-ready-traces
                            (first (collection-slot-call-trace roots origin))
                            (second forward)
                            (third (collection-slot-store-trace roots origin))
                            (cut-first (list (+ origin (collection-linux-offset "rt:forward"))))
                            (cut-second (list (+ origin
                                                 (collection-linux-offset
                                                  (collection-slot-loop-label roots)) 16)))
                            (cut-third (list (+ origin (collection-linux-offset
                                                        (collection-slot-loop-label roots))))))
                 (:instance collection-slot-store-commits-returned-word
                            (other (proof-world-reg (collection-slot-cursor-register roots) before))
                            (world (collection-trace-effect
                                    forward
                                    (collection-trace-effect (collection-slot-call-trace roots origin)
                                                             before)))))
           :cases (roots)
           :in-theory (e/d (collection-slot-call-trace collection-slot-loop-label
                                                       collection-slot-cursor-register
                                                       collection-slot-limit-register)
                           (collection-ready-trace-gives-prefix collection-prefix-p
                            collection-prefix-append proof-advance-append
                            collection-slot-loop-opens-forwarding-call
                            collection-slot-store-commits-returned-word)))))
