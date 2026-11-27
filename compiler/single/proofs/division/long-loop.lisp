(in-package "BOYMOO-PROOFS")

(include-book "window")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate)))

(defun division-normalized-divisor (lead next tail scale)
  (division-prefix-value (+ (* *division-radix* lead) next) tail scale))

(defun division-normalized-divisor-p (lead next tail scale)
  (and (division-leading-digit-p lead) (division-digit-p next)
       (posp scale) (natp tail) (< tail scale)))

(local
 (defthm division-normalized-divisor-bounds
   (implies (division-normalized-divisor-p lead next tail scale)
            (let ((divisor (division-normalized-divisor lead next tail scale)))
              (and (posp divisor)
                   (< divisor (* *division-radix* *division-radix* scale)))))
   :hints (("Goal"
            :use ((:instance division-positive-product (a (+ (* *division-radix* lead) next)) (b scale))
                  (:instance division-positive-product-order
                             (a (1- (* *division-radix* *division-radix*)))
                             (b (+ (* *division-radix* lead) next)) (factor scale)))))
   :rule-classes nil))

(local
 (defthm division-prefix-division-identity
   (implies (and (natp value) (posp scale))
            (equal (division-prefix-value (floor value scale) (mod value scale) scale) value))
   :hints (("Goal"
            :use (:instance division-floor-mod-identity (a value) (b scale))
            :in-theory (disable division-floor-mod-identity)))))

(local
 (defthm division-window-from-dividend
   (implies (and (division-normalized-divisor-p lead next tail scale)
                 (natp dividend)
                 (< dividend (* *division-radix*
                                (division-normalized-divisor lead next tail scale))))
            (let* ((upper (floor dividend scale))
                   (head (floor upper *division-radix*))
                   (digit (mod upper *division-radix*)))
              (and (division-window-p head lead next digit
                                      (mod dividend scale) tail scale)
                   (equal (division-prefix-value (+ (* *division-radix* head) digit)
                                                 (mod dividend scale) scale)
                          dividend))))
   :hints (("Goal"
            :use ((:instance division-normalized-divisor-bounds)
                  (:instance division-mod-bounds (a dividend) (b scale))
                  (:instance division-mod-bounds (a (floor dividend scale)) (b *division-radix*))
                  (:instance division-floor-at-least
                             (a dividend) (b scale)
                             (q (* *division-radix* *division-radix* *division-radix*)))
                  (:instance division-floor-at-least
                             (a (floor dividend scale)) (b *division-radix*)
                             (q (* *division-radix* *division-radix*)))
                  (:instance division-prefix-division-identity (value dividend))
                  (:instance division-floor-mod-identity
                             (a (floor dividend scale)) (b *division-radix*)))
            :in-theory (disable division-floor-mod-identity
                                division-prefix-division-identity division-prefix-value)
            :do-not-induct t))
   :rule-classes nil))

(defun division-normalized-position (dividend lead next tail scale)
  (let* ((upper (floor dividend scale))
         (head (floor upper *division-radix*))
         (digit (mod upper *division-radix*))
         (guess (division-two-limb-estimate head lead next digit))
         (divisor (division-normalized-divisor lead next tail scale)))
    (division-finish-iteration dividend divisor guess)))

(defthm division-normalized-position-correct
  (implies (and (division-normalized-divisor-p lead next tail scale)
                (natp dividend)
                (< dividend (* *division-radix* (division-normalized-divisor lead next tail scale))))
           (mv-let (q r)
             (division-normalized-position dividend lead next tail scale)
             (and (division-digit-p q) (natp r)
                  (< r (division-normalized-divisor lead next tail scale))
                  (equal (+ (* (division-normalized-divisor lead next tail scale) q) r)
                         dividend))))
  :hints (("Goal"
           :use ((:instance division-window-from-dividend)
                 (:instance division-normalized-divisor-bounds)
                 (:instance division-window-estimate-bounds
                            (head (floor (floor dividend scale) *division-radix*))
                            (digit (mod (floor dividend scale) *division-radix*))
                            (a-tail (mod dividend scale)) (b-tail tail))
                 (:instance division-finish-iteration-correct
                            (divisor (division-normalized-divisor lead next tail scale))
                            (guess (division-two-limb-estimate
                                    (floor (floor dividend scale) *division-radix*) lead next
                                    (mod (floor dividend scale) *division-radix*)))))
           :in-theory (disable division-finish-iteration division-prefix-value
                               division-two-limb-estimate division-window-p)
           :do-not-induct t))
  :rule-classes nil)

(defun division-normalized-loop (digits lead next tail scale)
  (if (atom digits)
      (mv nil 0)
    (mv-let (upper-quotient upper-remainder)
      (division-normalized-loop (cdr digits) lead next tail scale)
      (mv-let (q r)
        (division-normalized-position (+ (car digits) (* *division-radix* upper-remainder))
                                      lead next tail scale)
        (mv (cons q upper-quotient) r)))))

(defthm division-normalized-loop-correct
  (implies (and (division-digits-p digits) (division-normalized-divisor-p lead next tail scale))
           (mv-let (quotient remainder)
             (division-normalized-loop digits lead next tail scale)
             (let ((divisor (division-normalized-divisor lead next tail scale)))
               (and (division-digits-p quotient)
                    (equal (len quotient) (len digits))
                    (natp remainder) (< remainder divisor)
                    (equal (+ (* divisor (division-magnitude quotient)) remainder)
                           (division-magnitude digits))))))
  :hints (("Goal"
           :induct (division-normalized-loop digits lead next tail scale)
           :in-theory (disable division-normalized-position division-normalized-divisor
                               division-normalized-divisor-p))
          ("Subgoal *1/1" :use division-normalized-divisor-bounds)
          ("Subgoal *1/2"
           :use ((:instance division-normalized-divisor-bounds)
                 (:instance division-normalized-position-correct
                            (dividend (+ (car digits) (* *division-radix*
                                      (mv-nth 1 (division-normalized-loop (cdr digits) lead next tail scale))))))
                 (:instance division-scale-equality
                            (a (mv-let (q r)
                                 (division-normalized-loop (cdr digits) lead next tail scale)
                                 (+ (* (division-normalized-divisor lead next tail scale)
                                       (division-magnitude q))
                                    r)))
                            (b (division-magnitude (cdr digits)))
                            (factor *division-radix*)))))
  :rule-classes nil)
