(in-package "BOYMOO-PROOFS")

(include-book "boxed-quotient")
(include-book "public-immediate")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-boxed-first-view-instructions* (division-runtime-block "rt:z-division-op" 0 9))
(defconst *division-boxed-second-view-instructions* (division-runtime-block "rt:z-division-op" 9 4))
(defconst *division-boxed-reserve-instructions* (division-runtime-block "rt:z-division-op" 13 8))
(defconst *division-boxed-first-refresh-instructions* (division-runtime-block "rt:z-division-op" 21 4))
(defconst *division-boxed-second-refresh-instructions* (division-runtime-block "rt:z-division-op" 25 4))
(defconst *division-boxed-choose-path-instructions* (division-runtime-block "rt:z-division-op" 29 5))
(defconst *division-boxed-entry-to-view*
  (- (division-runtime-offset "rt:z-view") (division-runtime-offset "rt:z-division-op")))
(defconst *division-boxed-entry-to-reserve*
  (- (division-runtime-offset "rt:z-reserve") (division-runtime-offset "rt:z-division-op")))
(defconst *division-boxed-entry-to-copy*
  (- (division-runtime-offset "rt:z-gcd-copy") (division-runtime-offset "rt:z-division-op")))

(local
 (in-theory (disable ash floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     division-instruction-prefix-ready-p division-before-cuts-p
                     boymoo-model::a64-memory boymoo-model::a64-sp boymoo-model::a64-write-bytes
                     boymoo-model::a64-condition boymoo-model::a64-nzcv
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-boxed-stack-address (offset world)
  (+ offset (boymoo-model::a64-sp (proof-world-machine world))))

(defun division-boxed-entry-inputs-p (world)
  (let ((sp (division-boxed-stack-address 0 world)))
    (and (division-ordinary-world-p world)
         (<= 144 sp) (proof-span-p (- sp 144) 144)
         (unsigned-byte-p 64 (+ 36 (proof-world-pc world)))
         (unsigned-byte-p 64 (+ *division-boxed-entry-to-view* (proof-world-pc world))))))

(defun division-boxed-entry-output-p (world after)
  (and (equal (proof-world-pc after) (+ *division-boxed-entry-to-view* (proof-world-pc world)))
       (equal (proof-world-reg 30 after) (+ 36 (proof-world-pc world)))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (division-boxed-stack-address 0 after))
       (equal (proof-world-reg 21 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 1 world))
       (equal (proof-load-word (division-boxed-stack-address 64 after) (proof-world-machine after))
              (proof-world-reg 2 world))
       (division-boxed-saved-registers-p world after)
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(local
 (defthm division-boxed-entry-effects
   (implies (division-boxed-entry-inputs-p world)
            (division-boxed-entry-output-p
             world (division-instruction-sequence *division-boxed-first-view-instructions* world)))
   :hints (("Goal"
            :use ((:instance division-world-register-in-word (register 0))
                  (:instance division-world-register-in-word (register 1))
                  (:instance division-world-register-in-word (register 2))
                  (:instance division-world-register-in-word (register 19))
                  (:instance division-world-register-in-word (register 20))
                  (:instance division-world-register-in-word (register 21))
                  (:instance division-world-register-in-word (register 22))
                  (:instance division-world-register-in-word (register 29))
                  (:instance division-world-register-in-word (register 30)))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-enters-first-view
  (let* ((cuts (list (+ *division-boxed-entry-to-view* (proof-world-pc world))))
         (after (proof-advance 9 world)))
    (implies (and (division-boxed-entry-inputs-p world)
                  (division-instruction-sequence-ready-p *division-boxed-first-view-instructions* cuts world))
             (and (proof-segment-p 9 cuts world :cut after)
                  (division-boxed-entry-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-entry-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-first-view-instructions*)
                            (cuts (list (+ *division-boxed-entry-to-view* (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-first-view-instructions*)
                            (cuts (list (+ *division-boxed-entry-to-view* (proof-world-pc world))))))
           :in-theory (disable division-boxed-entry-inputs-p division-boxed-entry-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defun division-boxed-reservation-inputs-p (a-count b-count world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 32 (proof-world-pc world)))
       (unsigned-byte-p 64 (+ (- *division-boxed-entry-to-reserve* 52) (proof-world-pc world)))
       (unsigned-byte-p 29 a-count) (unsigned-byte-p 29 b-count)
       (equal (proof-world-reg 6 world) a-count)
       (equal (proof-world-reg 2 world) b-count)))

(defun division-boxed-reservation-output-p (a-count b-count world after)
  (let ((buffer (division-buffer-bytes a-count b-count)))
    (and (equal (proof-world-pc after) (+ (- *division-boxed-entry-to-reserve* 52) (proof-world-pc world)))
         (equal (proof-world-reg 30 after) (+ 32 (proof-world-pc world)))
         (equal (proof-world-reg 0 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 1 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 2 after) (* 5 buffer))
         (equal (proof-world-reg 20 after) buffer)
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (division-ordinary-world-p after))))

(local
 (defthm division-boxed-logand-zero
   (implies (integerp word)
            (and (equal (logand 0 word) 0) (equal (logand word 0) 0)))
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(local
 (defthm division-logand-of-doubled-integers
   (implies (and (integerp left) (integerp right))
            (equal (logand (* 2 left) (* 2 right)) (* 2 (logand left right))))
   :hints (("Goal"
            :expand ((logand (* 2 left) (* 2 right)))
            :cases ((equal left 0) (equal right 0))
            :use ((:instance division-signed-quotient-unique (a (* 2 left)) (b 2) (q left) (r 0))
                  (:instance division-signed-quotient-unique (a (* 2 right)) (b 2) (q right) (r 0))
                  (:instance division-signed-remainder-unique (a (* 2 left)) (b 2) (q left) (r 0))
                  (:instance division-evenp-remainder (x (* 2 left))))
            :in-theory (disable acl2::binary-logand evenp)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-short-word-rotate-by-sixty-one
   (implies (unsigned-byte-p 61 word)
            (equal (boymoo-model::a64-ror 64 word 61) (* 8 word)))
   :hints (("Goal"
            :use ((:instance division-ash-right (x word) (width 61))
                  (:instance division-ash-left (x word) (width 3)))
            :in-theory (e/d (boymoo-model::a64-ror)
                            (division-ash-right division-ash-left))
            :do-not-induct t))))

(local
 (defthm division-word-doubling-products
   (implies (integerp word)
            (and (equal (* 2 (* 2 word)) (* 4 word))
                 (equal (* 2 (* 4 word)) (* 8 word))))
   :hints (("Goal"
            :use ((:instance associativity-of-* (x 2) (y 2) (z word))
                  (:instance associativity-of-* (x 2) (y 4) (z word)))
            :in-theory (disable associativity-of-*)))))

(local
 (defthm division-boxed-left-shift-three-value
   (implies (unsigned-byte-p 61 word)
            (equal (logand (logand (boymoo-model::a64-ror 64 word 61) #xfffffffffffffff8)
                           #xffffffffffffffff)
                   (* 8 word)))
   :hints (("Goal"
            :use ((:instance division-logand-of-doubled-integers
                             (left (* 4 word)) (right #x7ffffffffffffffc))
                  (:instance division-logand-of-doubled-integers
                             (left (* 2 word)) (right #x3ffffffffffffffe))
                  (:instance division-logand-of-doubled-integers
                             (left word) (right #x1fffffffffffffff))
                  (:instance division-unsigned-mask-is-logand (width 61))
                  (:instance division-unsigned-mask-is-logand (width 64) (word (* 8 word))))
            :in-theory (disable acl2::binary-logand boymoo-model::a64-ror
                                division-unsigned-mask-is-logand)
            :do-not-induct t))))

(local
 (defthmd division-raw-pc-of-world
   (equal (boymoo-model::a64-pc (proof-world-machine world)) (proof-world-pc world))
   :hints (("Goal" :in-theory (enable proof-world-pc)))))

(local
 (defthm division-boxed-register-after-model-pc
   (equal (boymoo-model::a64-read-reg
           register 64 nil (boymoo-model::a64-set-pc pc (proof-world-machine world)))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc boymoo-model::a64-read-reg
                                     proof-world-reg proof-reg)))))

(local
 (defthm division-boxed-world-machine-after-replace
   (and (equal (proof-world-machine (update-nth 0 machine world)) machine)
        (equal (proof-world-machine (cons machine world)) machine))
   :hints (("Goal" :in-theory (enable proof-world-machine)))))

(local
 (defthm division-boxed-left-shift-three-mask
   (implies (unsigned-byte-p 61 word)
            (equal (logand (logand (* 8 word) #xfffffffffffffff8) #xffffffffffffffff)
                   (* 8 word)))
   :hints (("Goal"
            :use (:instance division-boxed-left-shift-three-value)
            :in-theory (disable division-boxed-left-shift-three-value boymoo-model::a64-ror acl2::binary-logand)))))

(local
 (defthm division-boxed-write-reg-20-is-ordinary
   (not (equal (car (boymoo-model::a64-write-reg 20 64 nil value machine)) :svc))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(local
 (in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-ror acl2::binary-logand)))

(local
 (division-prove-effect division-boxed-left-shift-three
   '(:bitfield 2 64 20 20 61 60 #xfffffffffffffff8 #xffffffffffffffff)
   (division-write-reg 20 nil (* 8 (proof-world-reg 20 world))
                       (division-set-pc (+ 4 (proof-world-pc world)) world))
   ((unsigned-byte-p 61 (proof-world-reg 20 world)))))

(local
 (defthm division-boxed-reservation-effects
   (implies (division-boxed-reservation-inputs-p a-count b-count world)
            (division-boxed-reservation-output-p
             a-count b-count world (division-instruction-sequence *division-boxed-reserve-instructions* world)))
   :hints (("Goal"
            :cases ((< a-count b-count) (equal a-count b-count))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-reserves-five-buffers
  (let* ((cuts (list (+ (- *division-boxed-entry-to-reserve* 52) (proof-world-pc world))))
         (after (proof-advance 8 world)))
    (implies (and (division-boxed-reservation-inputs-p a-count b-count world)
                  (division-instruction-sequence-ready-p *division-boxed-reserve-instructions* cuts world))
             (and (proof-segment-p 8 cuts world :cut after)
                  (division-boxed-reservation-output-p a-count b-count world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-reservation-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-reserve-instructions*)
                            (cuts (list (+ (- *division-boxed-entry-to-reserve* 52) (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-reserve-instructions*)
                            (cuts (list (+ (- *division-boxed-entry-to-reserve* 52) (proof-world-pc world))))))
           :in-theory (disable division-boxed-reservation-inputs-p division-boxed-reservation-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defun division-boxed-view-call-code (phase)
  (case phase
    (:second *division-boxed-second-view-instructions*)
    (:refresh-left *division-boxed-first-refresh-instructions*)
    (otherwise *division-boxed-second-refresh-instructions*)))

(defun division-boxed-view-call-offset (phase)
  (- *division-boxed-entry-to-view*
     (case phase (:second 36) (:refresh-left 84) (otherwise 100))))

(defun division-boxed-view-call-target (phase world)
  (+ (division-boxed-view-call-offset phase) (proof-world-pc world)))

(defun division-boxed-view-call-inputs-p (phase world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 16 (proof-world-pc world)))
       (unsigned-byte-p 64 (division-boxed-stack-address 32 world))
       (unsigned-byte-p 64 (division-boxed-view-call-target phase world))))

(defun division-boxed-view-call-output-p (phase world after)
  (and (equal (proof-world-pc after) (division-boxed-view-call-target phase world))
       (equal (proof-world-reg 30 after) (+ 16 (proof-world-pc world)))
       (equal (proof-world-reg 0 after) (proof-world-reg (if (eq phase :refresh-left) 0 22) world))
       (equal (proof-world-reg 1 after)
              (division-boxed-stack-address (if (eq phase :refresh-left) 0 32) world))
       (equal (proof-world-reg 6 after) (proof-world-reg (if (eq phase :second) 2 6) world))
       (equal (proof-world-reg 19 after) (proof-world-reg (if (eq phase :refresh-left) 2 19) world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after)
              (proof-world-reg (if (or (eq phase :second) (eq phase :refresh-left)) 21 0) world))
       (equal (proof-world-reg 22 after) (proof-world-reg (if (eq phase :refresh-left) 1 22) world))
       (equal (division-boxed-stack-address 0 after) (division-boxed-stack-address 0 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(local
 (defthm division-boxed-view-call-effects
   (implies (division-boxed-view-call-inputs-p phase world)
            (division-boxed-view-call-output-p
             phase world (division-instruction-sequence (division-boxed-view-call-code phase) world)))
   :hints (("Goal"
            :cases ((eq phase :second) (eq phase :refresh-left))
            :use (:instance division-world-sp-in-word)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-passes-view-arguments
  (let* ((cuts (list (division-boxed-view-call-target phase world)))
         (after (proof-advance 4 world))
         (instructions (division-boxed-view-call-code phase)))
    (implies (and (division-boxed-view-call-inputs-p phase world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p 4 cuts world :cut after)
                  (division-boxed-view-call-output-p phase world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-view-call-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-boxed-view-call-code phase))
                            (cuts (list (division-boxed-view-call-target phase world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-boxed-view-call-code phase))
                            (cuts (list (division-boxed-view-call-target phase world)))))
           :in-theory (disable division-boxed-view-call-inputs-p division-boxed-view-call-output-p
                               division-boxed-view-call-target division-instruction-sequence)))
  :rule-classes nil)

(defun division-boxed-mode (world)
  (proof-load-word (division-boxed-stack-address 64 world) (proof-world-machine world)))

(defun division-boxed-initial-remainder (world)
  (+ (proof-world-reg 19 world) (proof-world-reg 20 world)))

(defun division-boxed-choose-path-target (world)
  (+ (proof-world-pc world)
     (if (equal (division-boxed-mode world) 0) 20 (- *division-boxed-entry-to-copy* 116))))

(defun division-boxed-choose-path-inputs-p (world)
  (and (division-ordinary-world-p world)
       (proof-span-p (division-boxed-stack-address 64 world) 24)
       (unsigned-byte-p 64 (division-boxed-initial-remainder world))
       (unsigned-byte-p 64 (division-boxed-choose-path-target world))
       (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
       (or (equal (division-boxed-mode world) 0) (equal (division-boxed-mode world) 1))))

(defun division-boxed-choose-path-output-p (world after)
  (let ((slot (division-boxed-stack-address 80 world))
        (remainder (division-boxed-initial-remainder world)))
    (and (equal (proof-world-pc after) (division-boxed-choose-path-target world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 0 world))
         (equal (proof-world-reg 1 after) (division-boxed-mode world))
         (equal (proof-load-word slot (proof-world-machine after)) remainder)
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes 8 slot remainder (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (division-boxed-stack-address 0 after) (division-boxed-stack-address 0 world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(local
 (defthm division-boxed-choose-path-effects
   (implies (division-boxed-choose-path-inputs-p world)
            (division-boxed-choose-path-output-p
             world (division-instruction-sequence *division-boxed-choose-path-instructions* world)))
   :hints (("Goal"
            :cases ((equal (division-boxed-mode world) 0))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-initializes-remainder-slot
  (let* ((cuts (list (division-boxed-choose-path-target world)))
         (after (proof-advance 5 world)))
    (implies (and (division-boxed-choose-path-inputs-p world)
                  (division-instruction-sequence-ready-p *division-boxed-choose-path-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (division-boxed-choose-path-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-boxed-choose-path-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-boxed-choose-path-instructions*)
                            (cuts (list (division-boxed-choose-path-target world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-boxed-choose-path-instructions*)
                            (cuts (list (division-boxed-choose-path-target world)))))
           :in-theory (disable division-boxed-choose-path-inputs-p division-boxed-choose-path-output-p
                               division-boxed-choose-path-target division-instruction-sequence)))
  :rule-classes nil)
