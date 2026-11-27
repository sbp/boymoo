(in-package "BOYMOO-PROOFS")

(include-book "estimate")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate)))

(local
 (defthm division-equal-successors
   (implies (and (integerp a) (integerp b))
            (equal (equal (+ 1 a) (+ 1 b)) (equal a b)))))

(defun division-subtract-digit (digit divisor-digit guess carry)
  (let* ((word (+ (* guess divisor-digit) carry))
         (low (mod word *division-radix*))
         (high (floor word *division-radix*))
         (difference (- digit low))
         (borrow (if (< difference 0) 1 0)))
    (mv (+ difference (* *division-radix* borrow))
        (+ high borrow))))

(defthm division-subtract-product-word
  (implies (and (division-digit-p divisor-digit)
                (division-digit-p guess) (natp carry) (<= carry guess))
           (let ((word (+ (* guess divisor-digit) carry)))
             (and (unsigned-byte-p 64 word)
                  (<= word (* *division-radix* guess)))))
  :hints (("Goal"
           :use (:instance division-positive-product-order
                           (a (1- *division-radix*)) (b divisor-digit) (factor guess))
           :cases ((equal guess 0))
           :nonlinearp t))
  :rule-classes nil)

(defthm division-subtract-digit-correct
  (implies (and (division-digit-p digit)
                (division-digit-p divisor-digit)
                (division-digit-p guess) (natp carry) (<= carry guess))
           (let* ((written (mv-nth 0 (division-subtract-digit digit divisor-digit guess carry)))
                  (next (mv-nth 1 (division-subtract-digit digit divisor-digit guess carry))))
             (and (division-digit-p written)
                  (natp next) (<= next guess)
                  (equal (+ written (* guess divisor-digit) carry)
                         (+ digit (* *division-radix* next))))))
  :hints (("Goal"
           :use ((:instance division-subtract-product-word)
                 (:instance division-mod-bounds
                            (a (+ (* guess divisor-digit) carry)) (b *division-radix*))
                 (:instance division-floor-bounds
                            (a (+ (* guess divisor-digit) carry)) (b *division-radix*))
                 (:instance division-floor-mod-identity
                            (a (+ (* guess divisor-digit) carry)) (b *division-radix*)))
           :in-theory (disable division-floor-mod-identity)))
  :rule-classes nil)

(defun division-add-back-digit (digit divisor-digit carry)
  (let ((word (+ digit divisor-digit carry)))
    (mv (mod word *division-radix*) (floor word *division-radix*))))

(defthm division-add-back-digit-correct
  (implies (and (division-digit-p digit) (division-digit-p divisor-digit)
                (natp carry) (<= carry 1))
           (let* ((word (+ digit divisor-digit carry))
                  (written (mv-nth 0 (division-add-back-digit digit divisor-digit carry)))
                  (next (mv-nth 1 (division-add-back-digit digit divisor-digit carry))))
             (and (unsigned-byte-p 33 word)
                  (division-digit-p written)
                  (natp next) (<= next 1)
                  (equal (+ written (* *division-radix* next)) word))))
  :hints (("Goal"
           :use ((:instance division-mod-bounds
                            (a (+ digit divisor-digit carry)) (b *division-radix*))
                 (:instance division-floor-bounds
                            (a (+ digit divisor-digit carry)) (b *division-radix*))
                 (:instance division-floor-mod-identity
                            (a (+ digit divisor-digit carry)) (b *division-radix*)))
           :in-theory (disable division-floor-mod-identity)))
  :rule-classes nil)

(defun division-subtract-limbs (dividend divisor guess carry)
  (if (atom divisor)
      (mv nil carry)
    (mv-let (written next)
      (division-subtract-digit (car dividend) (car divisor) guess carry)
      (mv-let (high-digits final-carry)
        (division-subtract-limbs (cdr dividend) (cdr divisor) guess next)
        (mv (cons written high-digits) final-carry)))))

(defthm division-subtract-limbs-correct
  (implies (and (division-digits-p dividend) (division-digits-p divisor)
                (equal (len dividend) (len divisor))
                (division-digit-p guess) (natp carry) (<= carry guess))
           (let* ((digits (mv-nth 0 (division-subtract-limbs dividend divisor guess carry)))
                  (final (mv-nth 1 (division-subtract-limbs dividend divisor guess carry))))
             (and (division-digits-p digits)
                  (equal (len digits) (len divisor))
                  (natp final) (<= final guess)
                  (equal (+ (division-magnitude digits)
                            (* guess (division-magnitude divisor))
                            carry)
                         (+ (division-magnitude dividend)
                            (* (division-place-value (len divisor)) final))))))
  :hints (("Goal" :induct (division-subtract-limbs dividend divisor guess carry)
                  :in-theory (disable division-subtract-digit))
          ("Subgoal *1/2"
           :use ((:instance division-subtract-digit-correct
                            (digit (car dividend)) (divisor-digit (car divisor)))
                 (:instance division-scale-equality
                            (factor *division-radix*)
                            (a (let ((next
                                      (mv-nth 1 (division-subtract-digit
                                                 (car dividend) (car divisor) guess carry))))
                                 (+ (division-magnitude
                                     (mv-nth 0 (division-subtract-limbs
                                                (cdr dividend) (cdr divisor) guess next)))
                                    (* guess (division-magnitude (cdr divisor)))
                                    next)))
                            (b (let ((next
                                      (mv-nth 1 (division-subtract-digit
                                                 (car dividend) (car divisor) guess carry))))
                                 (+ (division-magnitude (cdr dividend))
                                    (* (division-place-value (len (cdr divisor)))
                                       (mv-nth 1 (division-subtract-limbs
                                                  (cdr dividend) (cdr divisor) guess next))))))))))
  :rule-classes nil)

(defun division-add-back-limbs (dividend divisor carry)
  (if (atom divisor)
      (mv nil carry)
    (mv-let (written next)
      (division-add-back-digit (car dividend) (car divisor) carry)
      (mv-let (high-digits final-carry)
        (division-add-back-limbs (cdr dividend) (cdr divisor) next)
        (mv (cons written high-digits) final-carry)))))

(defthm division-add-back-limbs-correct
  (implies (and (division-digits-p dividend) (division-digits-p divisor)
                (equal (len dividend) (len divisor))
                (natp carry) (<= carry 1))
           (let* ((digits (mv-nth 0 (division-add-back-limbs dividend divisor carry)))
                  (final (mv-nth 1 (division-add-back-limbs dividend divisor carry))))
             (and (division-digits-p digits)
                  (equal (len digits) (len divisor))
                  (natp final) (<= final 1)
                  (equal (+ (division-magnitude digits)
                            (* (division-place-value (len divisor)) final))
                         (+ (division-magnitude dividend)
                            (division-magnitude divisor)
                            carry)))))
  :hints (("Goal" :induct (division-add-back-limbs dividend divisor carry)
                  :in-theory (disable division-add-back-digit))
          ("Subgoal *1/2"
           :use ((:instance division-add-back-digit-correct
                            (digit (car dividend)) (divisor-digit (car divisor)))
                 (:instance division-scale-equality
                            (factor *division-radix*)
                            (a (let ((next (mv-nth 1 (division-add-back-digit
                                                     (car dividend) (car divisor) carry))))
                                 (mv-let (digits final)
                                   (division-add-back-limbs (cdr dividend) (cdr divisor) next)
                                   (+ (division-magnitude digits)
                                      (* (division-place-value (len (cdr divisor))) final)))))
                            (b (+ (division-magnitude (cdr dividend))
                                  (division-magnitude (cdr divisor))
                                  (mv-nth 1 (division-add-back-digit
                                             (car dividend) (car divisor) carry))))))))
  :rule-classes nil)

(defun division-finish-iteration (dividend divisor guess)
  (let ((difference (- dividend (* guess divisor))))
    (if (< difference 0)
        (mv (1- guess) (+ difference divisor))
      (mv guess difference))))

(defthm division-finish-iteration-correct
  (implies (and (natp dividend) (posp divisor) (division-digit-p guess)
                (< (* (1- guess) divisor) dividend)
                (< dividend (* (1+ guess) divisor)))
           (let ((q (mv-nth 0 (division-finish-iteration dividend divisor guess)))
                 (r (mv-nth 1 (division-finish-iteration dividend divisor guess))))
             (and (division-digit-p q)
                  (natp r) (< r divisor)
                  (equal (+ (* divisor q) r) dividend))))
  :rule-classes nil)
