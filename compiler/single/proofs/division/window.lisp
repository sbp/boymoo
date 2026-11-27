(in-package "BOYMOO-PROOFS")

(include-book "correction")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate)))

(defun division-window-magnitude (digits high)
  (+ (division-magnitude digits) (* (division-place-value (len digits)) high)))

(local
 (defthm division-positive-place-value
   (posp (division-place-value count))
   :rule-classes :type-prescription))

(local
 (defthm division-scale-weak-order
   (implies (and (rationalp a) (rationalp b) (posp place) (<= a b))
            (<= (* a place) (* b place)))
   :hints (("Goal"
            :use (:instance division-positive-product-order (a b) (b a) (factor place))))
   :rule-classes nil))

(local
 (defthm division-expand-high-successor
   (equal (* (1+ high) place) (+ place (* high place)))
   :hints (("Goal"
            :use (:instance distributivity (x place) (y 1) (z high))
            :in-theory (disable distributivity)))
   :rule-classes nil))

(defthm division-window-magnitude-bounds
  (implies (and (division-digits-p digits) (division-digit-p high))
           (and (natp (division-window-magnitude digits high))
                (< (division-window-magnitude digits high)
                   (* *division-radix* (division-place-value (len digits))))))
  :hints (("Goal"
           :use ((:instance division-positive-product-order
                            (a (1- *division-radix*)) (b high)
                            (factor (division-place-value (len digits)))))
           :nonlinearp t))
  :rule-classes nil)

(local
 (defthm division-low-digit-subtraction
   (implies (and (integerp difference)
                 (< (- *division-radix*) difference) (< difference *division-radix*))
            (equal (mod difference *division-radix*)
                   (if (< difference 0) (+ difference *division-radix*) difference)))
   :hints (("Goal"
            :use (:instance division-signed-remainder-unique
                            (a difference) (b *division-radix*)
                            (q (if (< difference 0) -1 0))
                            (r (if (< difference 0) (+ difference *division-radix*) difference)))))
   :rule-classes nil))

(defun division-subtract-window (digits high divisor guess)
  (mv-let (written carry)
    (division-subtract-limbs digits divisor guess 0)
    (let ((difference (- high carry)))
      (mv written (mod difference *division-radix*) (< difference 0)))))

(defthm division-subtract-window-correct
  (implies (and (division-digits-p digits) (division-digit-p high)
                (division-digits-p divisor) (equal (len digits) (len divisor))
                (division-digit-p guess))
           (mv-let (written top borrowed)
             (division-subtract-window digits high divisor guess)
             (let* ((a (division-window-magnitude digits high))
                    (b (division-magnitude divisor))
                    (after (division-window-magnitude written top))
                    (modulus (* *division-radix* (division-place-value (len divisor)))))
               (and (division-digits-p written) (equal (len written) (len divisor))
                    (division-digit-p top)
                    (equal borrowed (< a (* guess b)))
                    (equal (+ after (* guess b))
                           (+ a (if borrowed modulus 0)))))))
  :hints (("Goal"
           :use ((:instance division-subtract-limbs-correct (dividend digits) (carry 0))
                 (:instance division-low-digit-subtraction
                            (difference (- high (mv-nth 1 (division-subtract-limbs digits divisor guess 0)))))
                 (:instance division-magnitude-bound
                            (digits (mv-nth 0 (division-subtract-limbs digits divisor guess 0))))
                 (:instance division-scale-weak-order
                            (a (mv-nth 1 (division-subtract-limbs digits divisor guess 0))) (b high)
                            (place (division-place-value (len divisor))))
                 (:instance division-scale-weak-order
                            (a (1+ high)) (b (mv-nth 1 (division-subtract-limbs digits divisor guess 0)))
                            (place (division-place-value (len divisor))))
                 (:instance division-expand-high-successor
                            (place (division-place-value (len divisor)))))
           :in-theory (disable division-subtract-limbs)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-low-digit-addition
   (implies (and (natp value) (< value (* 2 *division-radix*)))
            (equal (mod value *division-radix*)
                   (if (< value *division-radix*) value (- value *division-radix*))))
   :hints (("Goal"
            :use (:instance division-signed-remainder-unique
                            (a value) (b *division-radix*)
                            (q (if (< value *division-radix*) 0 1))
                            (r (if (< value *division-radix*) value (- value *division-radix*))))))
   :rule-classes nil))

(defun division-add-back-window (digits high divisor)
  (mv-let (written carry)
    (division-add-back-limbs digits divisor 0)
    (let ((sum (+ high carry)))
      (mv written (mod sum *division-radix*) (<= *division-radix* sum)))))

(defthm division-add-back-window-correct
  (implies (and (division-digits-p digits) (division-digit-p high)
                (division-digits-p divisor) (equal (len digits) (len divisor)))
           (mv-let (written top overflow)
             (division-add-back-window digits high divisor)
             (let* ((before (division-window-magnitude digits high))
                    (b (division-magnitude divisor))
                    (after (division-window-magnitude written top))
                    (modulus (* *division-radix* (division-place-value (len divisor)))))
               (and (division-digits-p written) (equal (len written) (len divisor))
                    (division-digit-p top)
                    (equal (+ after (if overflow modulus 0)) (+ before b))))))
  :hints (("Goal"
           :use ((:instance division-add-back-limbs-correct (dividend digits) (carry 0))
                 (:instance division-low-digit-addition
                            (value (+ high (mv-nth 1 (division-add-back-limbs digits divisor 0))))))
           :in-theory (disable division-add-back-limbs)))
  :rule-classes nil)

(defun division-correct-window (digits high divisor guess)
  (mv-let (written top borrowed)
    (division-subtract-window digits high divisor guess)
    (if borrowed
        (mv-let (adjusted upper overflow)
          (division-add-back-window written top divisor)
          (declare (ignore overflow))
          (mv (1- guess) adjusted upper))
      (mv guess written top))))

(defthm division-correct-window-correct
  (implies (and (division-digits-p digits) (division-digit-p high)
                (division-digits-p divisor) (equal (len digits) (len divisor))
                (division-digit-p guess)
                (posp (division-magnitude divisor))
                (< (* (1- guess) (division-magnitude divisor))
                   (division-window-magnitude digits high))
                (< (division-window-magnitude digits high)
                   (* (1+ guess) (division-magnitude divisor))))
           (mv-let (q written top)
             (division-correct-window digits high divisor guess)
             (let ((r (division-window-magnitude written top))
                   (b (division-magnitude divisor)))
               (and (division-digit-p q)
                    (division-digits-p written) (equal (len written) (len divisor))
                    (division-digit-p top)
                    (natp r) (< r b)
                    (equal (+ (* q b) r) (division-window-magnitude digits high))))))
  :hints (("Goal"
           :use ((:instance division-subtract-window-correct)
                 (:instance division-add-back-window-correct
                            (digits (mv-nth 0 (division-subtract-window digits high divisor guess)))
                            (high (mv-nth 1 (division-subtract-window digits high divisor guess))))
                 (:instance division-window-magnitude-bounds)
                 (:instance division-window-magnitude-bounds
                            (digits (mv-nth 0 (division-subtract-window digits high divisor guess)))
                            (high (mv-nth 1 (division-subtract-window digits high divisor guess))))
                 (:instance division-window-magnitude-bounds
                            (digits (mv-nth 0 (division-add-back-window
                                               (mv-nth 0 (division-subtract-window digits high divisor guess))
                                               (mv-nth 1 (division-subtract-window digits high divisor guess))
                                               divisor)))
                            (high (mv-nth 1 (division-add-back-window
                                              (mv-nth 0 (division-subtract-window digits high divisor guess))
                                              (mv-nth 1 (division-subtract-window digits high divisor guess))
                                              divisor))))
                 (:instance division-expand-high-successor
                            (high guess) (place (division-magnitude divisor))))
           :in-theory (disable division-subtract-window division-add-back-window
                               division-window-magnitude division-magnitude)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-window-below-place-has-zero-top
   (implies (and (natp high)
                 (< (division-window-magnitude digits high) (division-place-value (len digits))))
            (equal high 0))
   :hints (("Goal"
            :use (:instance division-scale-weak-order
                            (a 1) (b high) (place (division-place-value (len digits))))
            :cases ((equal high 0))))
   :rule-classes nil))

(defthm division-normalized-window-iteration
  (implies (and (division-window-p head lead next digit a-tail b-tail scale)
                (division-digits-p digits) (division-digit-p high)
                (division-digits-p divisor) (equal (len digits) (len divisor))
                (equal (division-window-magnitude digits high)
                       (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale))
                (equal (division-magnitude divisor)
                       (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))
           (mv-let (q written top)
             (division-correct-window digits high divisor
                                      (division-two-limb-estimate head lead next digit))
             (let ((r (division-window-magnitude written top))
                   (b (division-magnitude divisor)))
               (and (division-digit-p q)
                    (division-digits-p written) (equal (len written) (len divisor))
                    (equal top 0)
                    (natp r) (< r b)
                    (equal (+ (* q b) r) (division-window-magnitude digits high))))))
  :hints (("Goal"
           :use ((:instance division-window-estimate-bounds)
                 (:instance division-correct-window-correct
                            (guess (division-two-limb-estimate head lead next digit)))
                 (:instance division-magnitude-bound (digits divisor))
                 (:instance division-window-below-place-has-zero-top
                            (digits (mv-nth 1 (division-correct-window
                                               digits high divisor
                                               (division-two-limb-estimate head lead next digit))))
                            (high (mv-nth 2 (division-correct-window
                                              digits high divisor
                                              (division-two-limb-estimate head lead next digit)))))
                 (:instance division-positive-product (a (+ (* *division-radix* lead) next))
                            (b scale)))
           :in-theory (disable division-correct-window division-window-magnitude
                               division-magnitude division-two-limb-estimate)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-positional-iteration-invariant
  (implies (and (posp divisor) (natp prefix) (natp upper-quotient)
                (natp upper-remainder) (< upper-remainder divisor)
                (division-digit-p input-digit) (division-digit-p quotient-digit)
                (natp remainder) (< remainder divisor)
                (equal (+ (* divisor upper-quotient) upper-remainder) prefix)
                (equal (+ (* divisor quotient-digit) remainder)
                       (+ (* *division-radix* upper-remainder) input-digit)))
           (equal (+ (* divisor (+ (* *division-radix* upper-quotient) quotient-digit)) remainder)
                  (+ (* *division-radix* prefix) input-digit)))
  :hints (("Goal"
           :use (:instance division-scale-equality
                           (a (+ (* divisor upper-quotient) upper-remainder))
                           (b prefix) (factor *division-radix*))))
  :rule-classes nil)
