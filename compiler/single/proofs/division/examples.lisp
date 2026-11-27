(in-package "BOYMOO-PROOFS")

(include-book "emission")
(include-book "limbs")
(include-book "divide-all")
(include-book "normalize-view")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-example-items* (division-linked-example-items))
(defconst *division-example-code* (boymoo-compiler::a64-bytes *division-example-items*))
(defconst *division-example-code-base* #x10000)
(defconst *division-example-heap-base* #x20000)
(defconst *division-example-return* #x26000)

(defun division-example-address (label)
  (+ *division-example-code-base* (division-label-offset label *division-example-items*)))

(defun division-example-world (entry registers)
  (let* ((machine
          (boymoo-model::a64-state
           (append registers
                   '((19 . 19) (20 . 20) (21 . 21) (22 . 22) (29 . 29)
                     (24 . #x24000) (25 . #x23000) (26 . #x22000)
                     (27 . #x21000) (28 . #x20000) (30 . #x26000)))
           #x25000 (division-example-address entry) 0 nil))
         (machine (proof-load-cleared-string
                   *division-example-code* *division-example-code-base* machine))
         (regions (list
                   (proof-region *division-example-code-base*
                                 (+ *division-example-code-base* (length *division-example-code*))
                                 :rx)
                   (proof-region #x20000 #x22000 :rw)
                   (proof-region #x23000 #x24000 :rw)
                   (proof-region #x24000 #x25000 :rw))))
    (proof-world machine regions 4096 nil nil nil nil nil)))

(defun division-example-write-digits (digits address machine)
  (if (atom digits)
      machine
    (division-example-write-digits
     (cdr digits) (+ address 8)
     (boymoo-model::a64-store 8 address (car digits) machine))))

(defun division-example-write-view (digits sign address machine)
  (division-example-write-digits
   digits (+ address 16)
   (boymoo-model::a64-store
    8 (+ address 8) sign
    (boymoo-model::a64-store 8 address (+ 3 (* 2048 (1+ (len digits)))) machine))))

(defun division-example-install-views (world a sign b)
  (update-nth 0 (division-example-write-view
                 b 0 #x20300
                 (division-example-write-view a sign #x20100 (proof-world-machine world)))
              world))

(defun division-example-restored-p (world)
  (and (equal (boymoo-model::a64-sp (proof-world-machine world)) #x25000)
       (equal (proof-world-reg 19 world) 19)
       (equal (proof-world-reg 20 world) 20)
       (equal (proof-world-reg 21 world) 21)
       (equal (proof-world-reg 22 world) 22)
       (equal (proof-world-reg 25 world) #x23000)
       (equal (proof-world-reg 29 world) 29)
       (equal (proof-world-reg 30 world) *division-example-return*)))

(defun division-example-at-cut (label world)
  (if (null label)
      world
    (mv-let (reason at-cut)
      (proof-run 512 (list (division-example-address label)) world)
      (and (equal reason :cut) at-cut))))

(defun division-example-divide-world (a b)
  (division-example-install-views
   (division-example-world "rt:z-divide"
                           '((0 . #x20100) (1 . #x20300) (2 . #x20500)
                             (3 . #x20700) (4 . #x20900)))
   a 0 b))

(defun division-example-divide (a b cut)
  (let* ((world (division-example-divide-world a b))
         (at-cut (division-example-at-cut cut world))
         (dividend (division-magnitude a))
         (divisor (division-magnitude b)))
    (and at-cut
         (mv-let (reason finish)
           (proof-run 512 (list *division-example-return*) at-cut)
           (let ((machine (proof-world-machine finish)))
             (and (equal reason :cut)
                  (division-example-restored-p finish)
                  (equal (proof-world-reg 0 finish) #x20700)
                  (equal (proof-integer-view #x20500 machine)
                         (proof-value-view (floor dividend divisor)))
                  (equal (proof-integer-view #x20700 machine)
                         (proof-value-view (mod dividend divisor)))))))))

(defthm division-example-one-limb
  (division-example-divide '(4294967295 4294967294) '(4294967295)
                           "rt:z-divide-one-limb")
  :rule-classes nil)

(defun division-example-visits (fuel address world)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (proof-world-stop world)
          (equal (proof-world-pc world) *division-example-return*))
      0
    (+ (if (equal (proof-world-pc world) address) 1 0)
       (division-example-visits (1- fuel) address (proof-step world)))))

(defthm division-example-two-corrections
  (let ((a '(0 2147483648 2147483647))
        (b '(4294967295 2147483648))
        (back-edge (+ 32 (division-example-address "rt:z-divide-estimate"))))
    (and (division-example-divide a b "rt:z-divide-estimate")
         (equal (division-example-visits 512 back-edge (division-example-divide-world a b)) 2)))
  :rule-classes nil)

(defthm division-example-add-back
  (division-example-divide '(0 0 2147483648) '(1 0 2147483648)
                           "rt:z-divide-add-back")
  :rule-classes nil)

(defthm division-example-normalization
  (division-example-divide '(17 1 1) '(1 1) "rt:z-divide-shift-right")
  :rule-classes nil)

(defthm division-example-short
  (division-example-divide nil '(1 1) "rt:z-divide-short")
  :rule-classes nil)

(defun division-example-wrapper (entry left right a sign b result cut)
  (let* ((world (division-example-world entry (list (cons 0 left) (cons 1 right))))
         (world (division-example-install-views world a sign b))
         (at-cut (division-example-at-cut cut world)))
    (and at-cut
         (mv-let (reason finish)
           (proof-run 1024 (list *division-example-return*) at-cut)
           (let* ((word (proof-world-reg 0 finish))
                  (machine (proof-world-machine finish)))
             (and (equal reason :cut)
                  (division-example-restored-p finish)
                  (if (proof-immediate-integer-p result)
                      (equal word (proof-integer-word result))
                    (and (equal (proof-word-tag word) 2)
                         (equal (proof-integer-view
                                 (proof-pointer-address word *division-example-heap-base*) machine)
                                (proof-value-view result))))))))))

(defthm division-example-quotient-immediate
  (division-example-wrapper "rt:z-quotient" (proof-integer-word -42) (proof-integer-word 7)
                            nil 0 nil -6 "rt:z-quotient-immediate")
  :rule-classes nil)

(defthm division-example-quotient-boxed
  (division-example-wrapper "rt:z-quotient" #x102 (proof-integer-word (+ *division-radix* 2))
                            '(0 2 1) 1 nil (- *division-radix*) "rt:z-division-op")
  :rule-classes nil)

(defthm division-example-gcd-zero-immediate
  (division-example-wrapper "rt:z-gcd" (proof-integer-word 0) (proof-integer-word 6)
                            nil 0 nil 6 "rt:z-gcd-word-loop")
  :rule-classes nil)

(defthm division-example-gcd-zero-boxed
  (division-example-wrapper "rt:z-gcd" (proof-integer-word 0) #x302
                            nil 0 '(5 2147483648) (+ (expt 2 63) 5) "rt:z-gcd-copy")
  :rule-classes nil)

(defthm division-example-gcd-boxed
  (division-example-wrapper "rt:z-gcd" #x102 #x302
                            '(0 0 3) 1 '(0 0 2) (expt 2 64) "rt:z-gcd-divide")
  :rule-classes nil)

(defun division-example-divider-ready-p (dividend divisor quotient-steps remainder-steps)
  (division-unsigned-ready-p
   (division-magnitude dividend) (division-magnitude divisor)
   (len dividend) (len divisor) quotient-steps remainder-steps
   (division-example-divide-world dividend divisor)))

(defthm division-example-divider-path-premises
  (and (division-example-divider-ready-p nil '(1 1) 8 8)
       (division-example-divider-ready-p '(4294967295 4294967294) '(4294967295) 16 10)
       (division-example-divider-ready-p '(17 1 1) '(1 1) 10 16))
  :rule-classes nil)

(defthm division-example-normalizer-trims-two-zero-limbs
  (let* ((digits '(17 0 0))
         (address #x20100)
         (world (division-example-world "rt:z-normalize" '((0 . #x20100) (1 . 3) (2 . 0))))
         (machine (division-example-write-view digits 0 address (proof-world-machine world)))
         (entered (update-nth 0 machine world))
         (returned (proof-advance 22 entered)))
    (and (division-normalizer-call-ready-p digits entered)
         (equal (division-normalizer-call-steps digits entered) 22)
         (division-unsigned-normalize-return-p digits entered returned)
         (equal (proof-world-reg 1 returned) 1)))
  :rule-classes nil)
