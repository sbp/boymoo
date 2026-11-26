(in-package "BOYMOO-PROOFS")

(include-book "forward")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-copy-payload-trace (count origin)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (append (collection-forward-trace :copy-word origin)
            (collection-copy-payload-trace (1- count) origin))))

(defun collection-copy-payload-effect (count world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      world
    (collection-copy-payload-effect (1- count) (collection-copy-word-effect world))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-world-machine
                     collection-cpu-p collection-write-register collection-write-pc
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned)))

(local
 (defthm collection-copy-word-keeps-register-file
   (implies (collection-cpu-p world)
            (collection-cpu-p (collection-copy-word-effect world)))))

(local
 (defthm collection-pc-after-copying-word
   (implies (unsigned-byte-p 64 (+ 24 (proof-world-pc world)))
            (equal (proof-world-pc (collection-copy-word-effect world))
                   (+ (proof-world-pc world)
                      (if (equal (proof-world-reg 3 world) 1) 24 0))))))

(local (in-theory (disable collection-copy-word-effect)))

(defthm collection-copy-payload-exhausts-count
  (implies (and (collection-cpu-p world) (equal count (proof-world-reg 3 world)))
           (equal (proof-world-reg 3 (collection-copy-payload-effect count world)) 0))
  :hints (("Goal" :induct (collection-copy-payload-effect count world))))

(defthm collection-copy-payload-advances-pc-on-last-word
  (implies (and (collection-cpu-p world)
                (equal count (proof-world-reg 3 world))
                (unsigned-byte-p 64 (+ 24 (proof-world-pc world))))
           (equal (proof-world-pc (collection-copy-payload-effect count world))
                  (+ (proof-world-pc world) (if (zp count) 0 24))))
  :hints (("Goal" :induct (collection-copy-payload-effect count world))))

(local
 (defthm collection-copy-payload-trace-length
   (equal (len (collection-copy-payload-trace count origin)) (* 6 (nfix count)))))

(local
 (defthm collection-trace-effect-composes
   (equal (collection-trace-effect (append first rest) world)
          (collection-trace-effect rest (collection-trace-effect first world)))
   :hints (("Goal" :induct (collection-trace-effect first world)
                   :in-theory (disable proof-instruction-effect)))))

(local
 (defthm collection-empty-trace-keeps-world
   (equal (collection-trace-effect nil world) world)))

(local
 (in-theory (disable collection-forward-trace collection-trace-effect
                     proof-instruction-effect append)))

(defthm collection-copy-payload-agrees-with-decoded-trace
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect (collection-copy-payload-trace count origin) world)
                  (collection-copy-payload-effect count world)))
  :hints (("Goal" :induct (collection-copy-payload-effect count world))))

(defthm collection-copy-payload-checked-segment
  (implies (and (collection-cpu-p world)
                (collection-trace-ready-p (collection-copy-payload-trace count origin)
                                          (list (+ origin 212)) world))
           (proof-segment-p (* 6 (nfix count)) (list (+ origin 212))
                            world :cut (collection-copy-payload-effect count world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-copy-payload-trace count origin))
                            (cuts (list (+ origin 212)))))
           :in-theory (disable collection-trace-ready-p proof-segment-p
                               collection-copy-payload-trace collection-copy-payload-effect))))
