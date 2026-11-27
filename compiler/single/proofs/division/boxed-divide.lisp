(in-package "BOYMOO-PROOFS")

(include-book "boxed-entry")
(include-book "divide-all")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-boxed-quotient-save-sign-instructions*
  (division-runtime-block "rt:z-gcd-copy" -13 4))
(defconst *division-boxed-quotient-inner-branch*
  (car (division-runtime-block "rt:z-gcd-copy" -9 1)))
(defconst *division-boxed-gcd-inner-branch*
  (car (division-runtime-block "rt:z-gcd-divide" 0 1)))

(local
 (in-theory (disable abs ash floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     division-instruction-prefix-ready-p division-before-cuts-p
                     boymoo-model::a64-memory boymoo-model::a64-sp boymoo-model::a64-write-bytes
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-boxed-inner-branch (gcd)
  (if gcd *division-boxed-gcd-inner-branch* *division-boxed-quotient-inner-branch*))

(defthm division-abs-of-positive-value
  (implies (posp value) (equal (abs value) value))
  :hints (("Goal" :in-theory (enable abs))))

(defun division-boxed-inner-call-instructions (gcd)
  (cons (division-boxed-inner-branch gcd) *division-step-call-instructions*))

(defun division-boxed-inner-target (gcd world)
  (+ (proof-world-pc world) (cadr (division-boxed-inner-branch gcd)) 56))

(defun division-boxed-inner-call-inputs-p (gcd world)
  (and (division-ordinary-world-p world)
       (posp (proof-world-reg 20 world))
       (proof-span-p (proof-world-reg 19 world) (* 5 (proof-world-reg 20 world)))
       (proof-span-p (division-boxed-stack-address 80 world) 8)
       (unsigned-byte-p 64 (+ 4 (proof-world-pc world)))
       (unsigned-byte-p 64 (+ (proof-world-pc world) (cadr (division-boxed-inner-branch gcd))))
       (unsigned-byte-p 64 (division-boxed-inner-target gcd world))))

(defun division-boxed-inner-call-output-p (gcd world after)
  (and (equal (proof-world-pc after) (division-boxed-inner-target gcd world))
       (equal (proof-world-reg 30 after) (+ 4 (proof-world-pc world)))
       (equal (proof-world-reg 0 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 22 world))
       (equal (proof-world-reg 2 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 3 after)
              (proof-load-word (division-boxed-stack-address 80 world) (proof-world-machine world)))
       (equal (proof-world-reg 4 after) (+ (proof-world-reg 19 world) (* 2 (proof-world-reg 20 world))))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (division-boxed-stack-address 0 after) (division-boxed-stack-address 0 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(local
 (defthm division-boxed-load-word-fits
   (unsigned-byte-p 64 (proof-load-word address machine))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8) (memory (boymoo-model::a64-memory machine)))
            :in-theory (e/d (proof-load-word) (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(local
 (defthm division-boxed-inner-call-effects
   (implies (division-boxed-inner-call-inputs-p gcd world)
            (division-boxed-inner-call-output-p
             gcd world (division-instruction-sequence (division-boxed-inner-call-instructions gcd) world)))
   :hints (("Goal"
            :cases (gcd)
            :use (:instance division-boxed-load-word-fits
                            (address (division-boxed-stack-address 80 world)) (machine (proof-world-machine world)))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-call-enters-divider
  (let* ((cuts (list (division-boxed-inner-target gcd world)))
         (after (proof-advance 7 world))
         (instructions (division-boxed-inner-call-instructions gcd)))
    (implies (and (division-boxed-inner-call-inputs-p gcd world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p 7 cuts world :cut after)
                  (division-boxed-inner-call-output-p gcd world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-inner-call-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-boxed-inner-call-instructions gcd))
                            (cuts (list (division-boxed-inner-target gcd world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-boxed-inner-call-instructions gcd))
                            (cuts (list (division-boxed-inner-target gcd world)))))
           :in-theory (disable division-boxed-inner-call-inputs-p division-boxed-inner-call-output-p
                               division-boxed-inner-target division-instruction-sequence)))
  :rule-classes nil)

(local
 (defthm division-positive-normalized-view-magnitude
   (implies (and (division-normalized-limbs-p digits) (consp digits))
            (posp (division-magnitude digits)))
   :hints (("Goal" :induct (division-normalized-limbs-p digits)))))

(local
 (defthm division-positive-read-is-nonempty
   (implies (posp count) (consp (division-read-limbs count address machine)))
   :hints (("Goal" :expand ((division-read-limbs count address machine))))))

(defthm division-view-word-is-its-sign
  (implies (proof-integer-view-p value address count world)
           (equal (proof-load-word (+ 8 address) (proof-world-machine world))
                  (if (< value 0) 1 0)))
  :hints (("Goal"
           :use ((:instance division-view-sign-and-limbs)
                 (:instance division-positive-normalized-view-magnitude
                            (digits (division-read-limbs count (+ 16 address) (proof-world-machine world))))
                 (:instance division-positive-read-is-nonempty
                            (address (+ 16 address)) (machine (proof-world-machine world))))
           :in-theory (disable proof-integer-view-p division-normalized-limbs-p division-read-limbs
                               division-magnitude division-read-limbs-view-magnitude division-read-limbs-normalized
                               division-positive-normalized-view-magnitude division-positive-read-is-nonempty)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-boxed-save-sign-inputs-p (a b a-count b-count world)
  (and (division-ordinary-world-p world) (posp b)
       (unsigned-byte-p 64 (+ 16 (proof-world-pc world)))
       (proof-span-p (division-boxed-stack-address 72 world) 8)
       (proof-span-p (+ 8 (proof-world-reg 21 world)) 8)
       (proof-span-p (+ 8 (proof-world-reg 22 world)) 8)
       (proof-integer-view-p a (proof-world-reg 21 world) a-count world)
       (proof-integer-view-p b (proof-world-reg 22 world) b-count world)))

(defun division-boxed-save-sign-output-p (a world after)
  (let* ((sign (if (< a 0) 1 0))
         (slot (division-boxed-stack-address 72 world)))
    (and (equal (proof-world-pc after) (+ 16 (proof-world-pc world)))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-load-word slot (proof-world-machine after)) sign)
         (equal (division-boxed-stack-address 0 after) (division-boxed-stack-address 0 world))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes 8 slot sign (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(local
 (defthm division-boxed-save-sign-effects
   (implies (division-boxed-save-sign-inputs-p a b a-count b-count world)
            (division-boxed-save-sign-output-p
             a world (division-instruction-sequence *division-boxed-quotient-save-sign-instructions* world)))
   :hints (("Goal"
            :cases ((< a 0))
            :use ((:instance division-view-word-is-its-sign
                             (value a) (address (proof-world-reg 21 world)) (count a-count))
                  (:instance division-view-word-is-its-sign
                             (value b) (address (proof-world-reg 22 world)) (count b-count)))
            :in-theory (disable proof-integer-view-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-saves-quotient-sign
  (let* ((cuts (list (+ 16 (proof-world-pc world))))
         (after (proof-advance 4 world)))
    (implies (and (division-boxed-save-sign-inputs-p a b a-count b-count world)
                  (division-instruction-sequence-ready-p *division-boxed-quotient-save-sign-instructions* cuts world))
             (and (proof-segment-p 4 cuts world :cut after)
                  (division-boxed-save-sign-output-p a world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-save-sign-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-quotient-save-sign-instructions*)
                            (cuts (list (+ 16 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-quotient-save-sign-instructions*)
                            (cuts (list (+ 16 (proof-world-pc world))))))
           :in-theory (disable division-boxed-save-sign-inputs-p division-boxed-save-sign-output-p
                               division-instruction-sequence)))
  :rule-classes nil)
