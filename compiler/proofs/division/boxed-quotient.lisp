(in-package "BOYMOO-PROOFS")

(include-book "boxed-gcd")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-boxed-quotient-sign-instructions* (division-runtime-block "rt:z-gcd-copy" -8 8))
(defconst *division-boxed-restore-instructions* (division-runtime-block "rt:z-division-return" 0 5))
(defconst *division-boxed-sign-to-restore-offset*
  (- (division-runtime-offset "rt:z-division-return")
     (- (division-runtime-offset "rt:z-gcd-copy") 32)))
(defconst *division-boxed-restore-to-pack-offset*
  (- (division-runtime-offset "rt:z-pack") (division-runtime-offset "rt:z-division-return")))

(local
 (in-theory (disable ash floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes boymoo-model::a64-sp
                     boymoo-model::a64-nzcv boymoo-model::a64-condition boymoo-model::a64-shift
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-boxed-sign (world)
  (proof-load-word (+ 72 (boymoo-model::a64-sp (proof-world-machine world))) (proof-world-machine world)))

(defun division-boxed-sign-inputs-p (count world)
  (let ((address (proof-world-reg 19 world)) (sign (division-boxed-sign world)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ 32 (proof-world-pc world)))
         (unsigned-byte-p 64 (+ *division-boxed-sign-to-restore-offset* (proof-world-pc world)))
         (unsigned-byte-p 64 (+ address 8))
         (natp count) (< count (expt 2 29))
         (equal (proof-load-word address (proof-world-machine world)) (+ 3 (* 2048 (1+ count))))
         (or (equal sign 0) (equal sign 1)))))

(defun division-boxed-sign-output-p (count world after)
  (let ((address (proof-world-reg 19 world))
        (sign (if (equal count 0) 0 (division-boxed-sign world))))
    (and (equal (proof-world-reg 0 after) address)
         (equal (proof-world-reg 1 after) sign)
         (equal (proof-world-pc after) (+ *division-boxed-sign-to-restore-offset* (proof-world-pc world)))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 (+ address 8) sign (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-boxed-quotient-sign-effects
  (implies (division-boxed-sign-inputs-p count world)
           (division-boxed-sign-output-p
            count world (division-instruction-sequence *division-boxed-quotient-sign-instructions* world)))
  :hints (("Goal"
           :use (:instance division-quotient-unique
                           (a (+ 3 (* 2048 (1+ count)))) (b 2048) (q (1+ count)) (r 3))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-exact-quotient-has-dividend-sign
   (implies (and (posp b) (proof-exact-quotient-p a b q))
            (equal (if (< a 0) (- (abs q)) (abs q)) q))
   :hints (("Goal"
            :cases ((< q 0) (equal q 0))
            :use ((:instance division-positive-product (a b) (b q))
                  (:instance division-positive-product (a b) (b (- q))))))))

(defthm division-boxed-exact-quotient-writes-signed-view
  (let* ((address (proof-world-reg 19 world))
         (cuts (list (+ *division-boxed-sign-to-restore-offset* (proof-world-pc world))))
         (after (proof-advance 8 world)))
    (implies (and (posp b) (proof-exact-quotient-p a b q)
                  (division-boxed-sign-inputs-p count world)
                  (equal (division-boxed-sign world) (if (< a 0) 1 0))
                  (proof-integer-view-p (abs q) address count world)
                  (proof-span-p address (division-view-bytes count))
                  (division-instruction-sequence-ready-p *division-boxed-quotient-sign-instructions* cuts world))
             (and (proof-segment-p 8 cuts world :cut after)
                  (equal (proof-world-reg 0 after) address)
                  (proof-integer-view-p q address count after))))
  :hints (("Goal"
           :cases ((equal count 0) (< a 0))
           :use ((:instance division-boxed-quotient-sign-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-quotient-sign-instructions*)
                            (cuts (list (+ *division-boxed-sign-to-restore-offset* (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-quotient-sign-instructions*)
                            (cuts (list (+ *division-boxed-sign-to-restore-offset* (proof-world-pc world)))))
                 (:instance division-view-zero-and-one-tests (value (abs q)) (address (proof-world-reg 19 world)))
                 (:instance division-exact-quotient-has-dividend-sign)
                 (:instance division-view-after-writing-sign
                            (value (abs q)) (address (proof-world-reg 19 world))
                            (sign (if (equal count 0) 0 (division-boxed-sign world)))
                            (before world) (after (proof-advance 8 world))))
           :in-theory (disable proof-integer-view-p division-instruction-sequence
                               division-exact-quotient-has-dividend-sign division-boxed-sign)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-boxed-saved-registers-p (entry world)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine)))
    (and (equal sp (- (boymoo-model::a64-sp (proof-world-machine entry)) 144))
         (equal (proof-load-word (+ sp 128) machine) (proof-world-reg 19 entry))
         (equal (proof-load-word (+ sp 136) machine) (proof-world-reg 20 entry))
         (equal (proof-load-word (+ sp 112) machine) (proof-world-reg 21 entry))
         (equal (proof-load-word (+ sp 120) machine) (proof-world-reg 22 entry))
         (equal (proof-load-word (+ sp 96) machine) (proof-world-reg 29 entry))
         (equal (proof-load-word (+ sp 104) machine) (proof-world-reg 30 entry)))))

(defun division-boxed-restore-inputs-p (entry world)
  (and (division-boxed-saved-registers-p entry world)
       (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
       (unsigned-byte-p 64 (+ *division-boxed-restore-to-pack-offset* (proof-world-pc world)))
       (<= 144 (boymoo-model::a64-sp (proof-world-machine entry)))))

(defun division-boxed-restore-output-p (entry world after)
  (and (equal (proof-world-pc after) (+ *division-boxed-restore-to-pack-offset* (proof-world-pc world)))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 entry))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 entry))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 entry))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 entry))
       (equal (proof-world-reg 29 after) (proof-world-reg 29 entry))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 entry))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine entry)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))))

(defthm division-boxed-restore-effects
  (implies (division-boxed-restore-inputs-p entry world)
           (division-boxed-restore-output-p
            entry world (division-instruction-sequence *division-boxed-restore-instructions* world)))
  :hints (("Goal" :do-not '(generalize fertilize) :do-not-induct t))
  :rule-classes nil)

(defthm division-boxed-restores-frame-and-reaches-pack
  (let* ((cuts (list (+ *division-boxed-restore-to-pack-offset* (proof-world-pc world))))
         (after (proof-advance 5 world)))
    (implies (and (division-boxed-restore-inputs-p entry world)
                  (division-instruction-sequence-ready-p *division-boxed-restore-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (division-boxed-restore-output-p entry world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-restore-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-restore-instructions*)
                            (cuts (list (+ *division-boxed-restore-to-pack-offset* (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-restore-instructions*)
                            (cuts (list (+ *division-boxed-restore-to-pack-offset* (proof-world-pc world))))))
           :in-theory (disable division-boxed-restore-output-p division-boxed-restore-inputs-p
                               division-instruction-sequence)))
  :rule-classes nil)
