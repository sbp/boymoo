(in-package "BOYMOO-PROOFS")

(include-book "effects")
(include-book "linked")
(include-book "gcd-loop")
(include-book "fast-paths")
(include-book "cutpoints")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-public-quotient-instructions* (division-runtime-block "rt:z-quotient" 0 7))
(defconst *division-public-gcd-instructions* (division-runtime-block "rt:z-gcd" 0 9))
(defconst *division-return-one-instructions* (division-runtime-block "rt:one" 0 2))

(defconst *division-quotient-by-one-offset*
  (- (division-runtime-offset "rt:num-type-return") (division-runtime-offset "rt:z-quotient")))
(defconst *division-quotient-to-boxed-offset*
  (- (division-runtime-offset "rt:z-division-op") (division-runtime-offset "rt:z-quotient")))
(defconst *division-gcd-one-offset*
  (- (division-runtime-offset "rt:one") (division-runtime-offset "rt:z-gcd")))
(defconst *division-gcd-to-boxed-offset*
  (- (division-runtime-offset "rt:z-division-op") (division-runtime-offset "rt:z-gcd")))

(local
 (in-theory (disable floor mod ash acl2::binary-logand acl2::binary-logior
                     proof-step proof-advance proof-world-pc proof-world-reg proof-world-machine
                     proof-world-stop proof-world-regions proof-instruction-effect
                     boymoo-model::a64-nzcv boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-shift boymoo-model::a64-condition boymoo-model::a64-result-flags
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defthm division-immediate-word-has-low-bit
  (implies (integerp value)
           (equal (mod (proof-integer-word value) 2) 1))
  :hints (("Goal"
           :use ((:instance division-narrower-mask-of-word (width 1) (value (+ 1 (* 2 value))))
                 (:instance division-signed-mod-bounds (a (+ 1 (* 2 value))) (b (expt 2 64)))
                 (:instance division-signed-remainder-unique (a (+ 1 (* 2 value))) (b 2) (q value) (r 1)))
           :in-theory (e/d (division-a64-unsigned-is-remainder)
                           (division-narrower-mask-of-word)))))

(defthm division-one-word-identifies-one
  (implies (proof-immediate-integer-p value)
           (equal (equal (proof-integer-word value) 3) (equal value 1)))
  :hints (("Goal"
           :cases ((< value 0))
           :use (:instance division-negative-in-word (value (+ 1 (* 2 value)))))))

(local
 (defthm division-and-tested-low-bit
   (implies (and (integerp left) (integerp right))
            (equal (logand (boymoo-model::a64-unsigned 64 (logand left right)) 1)
                   (if (and (equal (mod left 2) 1) (equal (mod right 2) 1)) 1 0)))
   :hints (("Goal"
            :use ((:instance division-unsigned-mask-is-logand
                             (width 1) (word (logand left right)))
                  (:instance division-unsigned-mask-is-logand
                             (width 1) (word (boymoo-model::a64-unsigned 64 (logand left right))))
                  (:instance division-narrower-mask-of-word (width 1) (value (logand left right))))
            :in-theory (disable division-narrower-mask-of-word
                                division-unsigned-mask-is-logand)))))

(local
 (defthm division-branch-on-test-bit
   (implies (or (equal bit 0) (equal bit 1))
            (equal (boymoo-model::a64-condition
                    1 (boymoo-model::a64-unsigned 4
                       (boymoo-model::a64-result-flags 64 bit nil nil)))
                   (equal bit 1)))
   :hints (("Goal"
            :cases ((equal bit 0))
            :in-theory (enable boymoo-model::a64-condition boymoo-model::a64-result-flags)))))

(defun division-public-route (gcd left right)
  (cond ((or (equal right 3) (and gcd (equal left 3))) :one)
        ((and (equal (mod left 2) 1) (equal (mod right 2) 1)) :immediate)
        (t :boxed)))

(defun division-public-target-offset (gcd route)
  (case route
    (:one (if gcd *division-gcd-one-offset* *division-quotient-by-one-offset*))
    (:immediate (if gcd 36 28))
    (otherwise (if gcd *division-gcd-to-boxed-offset* *division-quotient-to-boxed-offset*))))

(defun division-public-dispatch-steps (gcd left right)
  (cond ((and gcd (equal left 3)) 2)
        ((equal right 3) (if gcd 4 2))
        ((and (equal (mod left 2) 1) (equal (mod right 2) 1)) (if gcd 7 5))
        (t (if gcd 9 7))))

(defun division-public-code (gcd)
  (if gcd *division-public-gcd-instructions* *division-public-quotient-instructions*))

(defun division-public-instructions (gcd world)
  (take (division-public-dispatch-steps gcd (proof-world-reg 0 world) (proof-world-reg 1 world))
        (division-public-code gcd)))

(defun division-public-target (gcd world)
  (+ (proof-world-pc world)
     (division-public-target-offset gcd
                                    (division-public-route gcd (proof-world-reg 0 world)
                                                           (proof-world-reg 1 world)))))

(defun division-public-dispatch-layout-p (gcd world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 36 (proof-world-pc world)))
       (unsigned-byte-p 64 (division-public-target gcd world))))

(defun division-public-dispatch-output-p (gcd world after)
  (and (equal (proof-world-pc after) (division-public-target gcd world))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (implies (eq (division-public-route gcd (proof-world-reg 0 world)
                                          (proof-world-reg 1 world))
                    :boxed)
                (equal (proof-world-reg 2 after) (if gcd 1 0)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(defthm division-public-dispatch-effects
  (implies (division-public-dispatch-layout-p gcd world)
           (division-public-dispatch-output-p
            gcd world (division-instruction-sequence (division-public-instructions gcd world) world)))
  :hints (("Goal"
           :cases (gcd)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-public-dispatch-ready-from-code
   (implies (and (division-public-dispatch-layout-p gcd world)
                 (not (proof-world-stop world))
                 (proof-instructions-at-p (division-public-code gcd) (proof-world-pc world) world))
            (division-instruction-sequence-ready-p
             (division-public-instructions gcd world) (list (division-public-target gcd world)) world))
   :hints (("Goal"
            :cases (gcd)
            :in-theory (e/d (division-instruction-at-depends-on-bytes)
                            (proof-instruction-at-p division-decoded-word-at-p))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-public-instructions-length
   (equal (len (division-public-instructions gcd world))
          (division-public-dispatch-steps gcd (proof-world-reg 0 world) (proof-world-reg 1 world)))))

(defthm division-public-dispatch-runs
  (let* ((cuts (list (division-public-target gcd world)))
         (steps (division-public-dispatch-steps gcd (proof-world-reg 0 world) (proof-world-reg 1 world)))
         (after (proof-advance steps world)))
    (implies (and (division-public-dispatch-layout-p gcd world)
                  (not (proof-world-stop world))
                  (proof-instructions-at-p (division-public-code gcd) (proof-world-pc world) world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-public-dispatch-output-p gcd world after))))
  :hints (("Goal"
           :use ((:instance division-public-dispatch-ready-from-code)
                 (:instance division-public-dispatch-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-public-instructions gcd world))
                            (cuts (list (division-public-target gcd world))))
                 (:instance division-instruction-sequence-advances
                            (instructions (division-public-instructions gcd world))
                            (cuts (list (division-public-target gcd world)))))
           :in-theory (disable division-public-dispatch-layout-p division-public-dispatch-output-p
                               division-public-instructions division-public-dispatch-steps
                               division-public-target division-public-code
                               division-instruction-sequence division-instruction-sequence-ready-p
                               proof-instructions-at-p proof-segment-p)))
  :rule-classes nil)
