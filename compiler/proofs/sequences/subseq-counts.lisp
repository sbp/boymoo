(in-package "BOYMOO-PROOFS")

(include-book "counts")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-subseq-immediate-dispatch*
  ("rt:subseq-end-ready" 0 3))

(sequence-defpath *sequence-subseq-immediate-start*
  ("rt:subseq-end-ready" 3 4))

(sequence-defpath *sequence-subseq-immediate-size*
  ("rt:subseq-end-ready" 7 4))

(defconst *sequence-subseq-immediate-counts*
  (append *sequence-subseq-immediate-dispatch*
          *sequence-subseq-immediate-start*
          *sequence-subseq-immediate-size*))

(defconst *sequence-subseq-end-ready-offset* (sequence-offset "rt:subseq-end-ready"))
(defconst *sequence-subseq-checked-offset* (sequence-offset "rt:subseq-checked"))

(local
 (defthm sequence-immediate-word-parity-and-value
   (implies (proof-immediate-integer-p value)
            (and (oddp (proof-integer-word value))
                 (equal (floor (boymoo-model::a64-signed 64 (proof-integer-word value)) 2)
                        value)))
   :hints (("Goal"
            :in-theory (disable oddp evenp sequence-signed-word
                                sequence-signed-word-of-fitting-value)
            :use ((:instance sequence-signed-word-of-fitting-value (value (+ 1 (* 2 value))))
                  (:instance sequence-floor-unique
                             (value (+ 1 (* 2 value))) (divisor 2) (quotient value))
                  (:instance sequence-floor-half-decomposition (value (+ 1 (* 2 value)))))))))

(local
 (defthm sequence-register-word-of-signed
   (implies (signed-byte-p 64 value)
            (equal (boymoo-model::a64-unsigned 64 value)
                   (if (< value 0) (+ (expt 2 64) value) value)))
   :hints (("Goal"
            :in-theory (disable sequence-truncate-word-plus-modulus)
            :use sequence-truncate-word-plus-modulus))))

(local
 (defthm sequence-modular-difference-of-signed-registers
   (implies (and (signed-byte-p 64 end) (signed-byte-p 64 start))
            (equal (boymoo-model::a64-unsigned
                    64 (- (boymoo-model::a64-unsigned 64 end)
                          (boymoo-model::a64-unsigned 64 start)))
                   (boymoo-model::a64-unsigned 64 (- end start))))
   :hints (("Goal"
            :cases ((< end 0) (< start 0))
            :in-theory (disable sequence-unsigned-of-difference
                                sequence-truncate-word-plus-modulus)
            :use ((:instance sequence-truncate-word-plus-modulus (value (- end start)))
                  (:instance sequence-truncate-word-plus-modulus
                             (value (+ (- (expt 2 64)) end (- start)))))))))

(local
 (defthm sequence-immediate-difference-fits-signed-word
   (implies (and (proof-immediate-integer-p end) (proof-immediate-integer-p start))
            (and (signed-byte-p 64 start)
                 (signed-byte-p 64 end)
                 (signed-byte-p 64 (- end start))))))

(local
 (in-theory (disable sequence-register-word-of-signed
                     sequence-immediate-word-parity-and-value)))

(local
 (defthm sequence-subseq-two-immediates-fall-through
   (let* ((machine (proof-world-machine before))
          (after (sequence-execute *sequence-subseq-immediate-dispatch* before)))
     (implies
      (and (consp (boymoo-model::a64-registers machine))
           (oddp (proof-world-reg 6 before)) (oddp (proof-world-reg 7 before))
           (unsigned-byte-p 64 (+ 12 (proof-world-pc before))))
      (and (equal (proof-world-pc after) (+ 12 (proof-world-pc before)))
           (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
           (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
           (equal (proof-world-reg 7 after) (proof-world-reg 7 before))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
           (consp (boymoo-model::a64-registers (proof-world-machine after)))
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (proof-world-regions after) (proof-world-regions before))
           (equal (boymoo-model::a64-sp (proof-world-machine after))
                  (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (boymoo-model::a64-memory machine)))))
   :hints (("Goal" :in-theory (e/d (sequence-execute boymoo-model::a64-exec-logical)
                                    (oddp evenp))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-fix-immediate-start
   (let* ((machine (proof-world-machine before))
          (after (sequence-execute *sequence-subseq-immediate-start* before)))
     (implies
      (and (consp (boymoo-model::a64-registers machine))
           (proof-immediate-integer-p start) (proof-immediate-integer-p end)
           (equal (proof-world-reg 6 before) (proof-integer-word start))
           (equal (proof-world-reg 7 before) (proof-integer-word end))
           (unsigned-byte-p 64 (+ 16 (proof-world-pc before))))
      (and (equal (proof-world-pc after) (+ 16 (proof-world-pc before)))
           (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
           (equal (proof-world-reg 6 after) (boymoo-model::a64-unsigned 64 start))
           (equal (proof-world-reg 7 after) (boymoo-model::a64-unsigned 64 end))
           (equal (proof-world-reg 20 after) (sequence-count start))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
           (consp (boymoo-model::a64-registers (proof-world-machine after)))
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (proof-world-regions after) (proof-world-regions before))
           (equal (boymoo-model::a64-sp (proof-world-machine after))
                  (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (boymoo-model::a64-memory machine)))))
   :hints (("Goal"
            :in-theory (e/d (sequence-execute)
                            (sequence-count proof-integer-word sequence-signed-word
                             sequence-unsigned-of-difference oddp evenp))
            :use ((:instance sequence-immediate-word-parity-and-value (value start))
                  (:instance sequence-immediate-word-parity-and-value (value end))
                  (:instance sequence-positive-count-from-signed-word (value start) (carry t)))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-fix-immediate-size
   (let* ((machine (proof-world-machine before))
          (after (sequence-execute *sequence-subseq-immediate-size* before)))
     (implies
      (and (consp (boymoo-model::a64-registers machine))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-subseq-end-ready-offset* 28))
           (unsigned-byte-p 64 (+ image-base *sequence-subseq-checked-offset*))
           (proof-immediate-integer-p start) (proof-immediate-integer-p end)
           (equal (proof-world-reg 6 before) (boymoo-model::a64-unsigned 64 start))
           (equal (proof-world-reg 7 before) (boymoo-model::a64-unsigned 64 end)))
      (and (equal (proof-world-pc after) (+ image-base *sequence-subseq-checked-offset*))
           (equal (proof-world-reg 19 after) (sequence-count (- end start)))
           (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
           (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
           (equal (proof-world-reg 0 after) (proof-world-reg 5 before))
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (proof-world-regions after) (proof-world-regions before))
           (equal (boymoo-model::a64-sp (proof-world-machine after))
                  (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (boymoo-model::a64-memory machine)))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-execute)
                     (sequence-count sequence-signed-word sequence-unsigned-of-difference))
     :use
     ((:instance sequence-positive-count-from-signed-word
                 (value (- end start))
                 (carry (<= (boymoo-model::a64-unsigned 64 start)
                            (boymoo-model::a64-unsigned 64 end)))))))
   :rule-classes nil))

(defthm sequence-subseq-immediate-count-effects
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-subseq-immediate-counts* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-end-ready-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-checked-offset*))
          (proof-immediate-integer-p start)
          (proof-immediate-integer-p end)
          (equal (proof-world-reg 6 before) (proof-integer-word start))
          (equal (proof-world-reg 7 before) (proof-integer-word end)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-subseq-checked-offset*))
          (equal (proof-world-reg 20 after) (sequence-count start))
          (equal (proof-world-reg 19 after) (sequence-count (- end start)))
          (equal (proof-world-reg 0 after) (proof-world-reg 5 before))
          (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints
  (("Goal"
    :in-theory (disable sequence-count proof-integer-word proof-world-pc proof-world-reg
                        proof-world-machine sequence-execute-append oddp evenp)
    :use
    (sequence-subseq-two-immediates-fall-through
     (:instance sequence-immediate-word-parity-and-value (value start))
     (:instance sequence-immediate-word-parity-and-value (value end))
     (:instance sequence-subseq-fix-immediate-start
                (before (sequence-execute *sequence-subseq-immediate-dispatch* before)))
     (:instance sequence-subseq-fix-immediate-size
                (before
                 (sequence-execute *sequence-subseq-immediate-start*
                                   (sequence-execute *sequence-subseq-immediate-dispatch*
                                                     before))))
     (:instance sequence-execute-append
                (first *sequence-subseq-immediate-dispatch*)
                (second *sequence-subseq-immediate-start*) (world before))
     (:instance sequence-execute-append
                (first (append *sequence-subseq-immediate-dispatch*
                               *sequence-subseq-immediate-start*))
                (second *sequence-subseq-immediate-size*) (world before)))))
  :rule-classes nil)

(defthm sequence-subseq-immediate-count-segment
  (let* ((end (sequence-end limit datum))
         (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
         (path *sequence-subseq-immediate-counts*)
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-end-ready-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-checked-offset*))
          (proof-immediate-integer-p start)
          (proof-immediate-integer-p end)
          (equal (proof-world-reg 6 before) (proof-integer-word start))
          (equal (proof-world-reg 7 before) (proof-integer-word end))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 20 after) (sequence-runtime-count start))
          (equal (proof-world-reg 19 after) (sequence-result-size datum start limit)))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-integer-word proof-world-reg proof-world-machine
                        proof-world-pc sequence-end)
    :use
    ((:instance sequence-subseq-immediate-count-effects (end (sequence-end limit datum)))
     (:instance sequence-segment-of-instruction-path
                (instructions *sequence-subseq-immediate-counts*)
                (cuts (list (+ image-base *sequence-subseq-checked-offset*)))
                (after (sequence-execute *sequence-subseq-immediate-counts* before))))))
  :rule-classes nil)

(defthm sequence-subseq-arithmetic-result
  (let* ((end (sequence-end limit datum))
         (negated (proof-runtime-value 'acl2::unary-- (list start) program)))
    (equal (proof-runtime-value 'acl2::binary-+
                                (list end (boymoo-model::core-datum negated)) program)
           (boymoo-model::core-value (- end start))))
  :hints (("Goal" :in-theory (enable boymoo-model::core-primitive))))
