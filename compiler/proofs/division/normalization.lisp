(in-package "BOYMOO-PROOFS")

(include-book "estimate")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate ash expt)))

(local
 (defthm division-cancel-inverse-in-sum
   (equal (+ a (- a) b) (fix b))
   :hints (("Goal"
            :use (:instance associativity-of-+ (x a) (y (- a)) (z b))
            :in-theory (disable associativity-of-+)))))

(local
 (defthm division-power-of-two-successor
   (implies (natp width)
            (equal (expt 2 (+ 1 width)) (* 2 (expt 2 width))))
   :hints (("Goal" :use (:instance division-power-of-two-step (width (1+ width)))))))

(local
 (defun division-power-induct (width)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       0
     (division-power-induct (1- width)))))

(defthm division-power-of-two-sum
  (implies (and (natp left) (natp right))
           (equal (expt 2 (+ left right)) (* (expt 2 left) (expt 2 right))))
  :hints (("Goal" :induct (division-power-induct left))
          ("Subgoal *1/2"
           :use ((:instance division-power-of-two-step (width left))
                 (:instance division-power-of-two-step (width (+ left right)))))
          ("Subgoal *1/1" :in-theory (enable expt)))
  :rule-classes nil)

(local
 (defthm division-power-of-two-strict-order
   (implies (and (natp left) (natp right) (< left right))
            (< (expt 2 left) (expt 2 right)))
   :hints (("Goal"
            :use ((:instance division-power-of-two-sum (right (- right left)))
                  (:instance division-power-of-two-step (width (- right left)))
                  (:instance division-power-of-two-positive (width (1- (- right left))))
                  (:instance division-positive-product-order
                             (a 1) (b (expt 2 (- right left))) (factor (expt 2 left))))))
   :rule-classes nil))

(defthm division-integer-length-bounds
  (implies (posp x)
           (let ((width (integer-length x)))
             (and (posp width)
                  (<= (expt 2 (1- width)) x)
                  (< x (expt 2 width)))))
  :hints (("Goal" :induct (integer-length x))
          ("Subgoal *1/3"
           :use ((:instance division-floor-bounds (a x) (b 2))
                 (:instance division-power-of-two-step
                            (width (+ 1 (integer-length (floor x 2))))))
           :cases ((equal (floor x 2) 0))
           :in-theory (e/d (expt) (floor))))
  :rule-classes nil)

(defun division-normalization-shift (leading)
  (- 32 (integer-length leading)))

(local
 (defthm division-normalization-exponents
   (and (equal (expt 2 (+ (division-normalization-shift leading) (integer-length leading)))
               *division-radix*)
        (equal (expt 2 (+ -1 (division-normalization-shift leading) (integer-length leading)))
               (/ *division-radix* 2)))
   :rule-classes nil))

(defthm division-clz-shift-bounds
  (implies (and (division-digit-p leading) (posp leading))
           (let ((shift (division-normalization-shift leading)))
             (and (natp shift) (< shift 32))))
  :hints (("Goal"
           :use ((:instance division-integer-length-bounds (x leading))
                 (:instance division-power-of-two-strict-order
                            (left 31) (right (1- (integer-length leading))))
                 (:instance division-power-of-two-strict-order
                            (left 32) (right (1- (integer-length leading)))))
           :cases ((equal (integer-length leading) 33))
           :in-theory (disable integer-length)))
  :rule-classes nil)

(defthm division-normalized-leading-digit
  (implies (and (division-digit-p leading) (posp leading)
                (natp carry)
                (< carry (expt 2 (division-normalization-shift leading))))
           (division-leading-digit-p
            (+ (ash leading (division-normalization-shift leading)) carry)))
  :hints (("Goal"
           :use ((:instance division-integer-length-bounds (x leading))
                 (:instance division-clz-shift-bounds)
                 (:instance division-normalization-exponents)
                 (:instance division-power-of-two-sum
                            (left (integer-length leading))
                            (right (division-normalization-shift leading)))
                 (:instance division-power-of-two-sum
                            (left (1- (integer-length leading)))
                            (right (division-normalization-shift leading)))
                 (:instance division-positive-product-order
                            (a leading) (b (expt 2 (1- (integer-length leading))))
                            (factor (expt 2 (division-normalization-shift leading))))
                 (:instance division-positive-product-order
                            (b (1+ leading)) (a (expt 2 (integer-length leading)))
                            (factor (expt 2 (division-normalization-shift leading))))
                 (:instance distributivity
                            (x (expt 2 (division-normalization-shift leading))) (y 1) (z leading))
                 (:instance division-ash-left (x leading)
                            (width (division-normalization-shift leading))))
           :in-theory (disable integer-length division-normalization-shift
                               division-ash-left distributivity)))
  :rule-classes nil)

(defun division-left-shift-digit (digit carry scale)
  (let ((word (+ (* digit scale) carry)))
    (mv (mod word *division-radix*) (floor word *division-radix*))))

(defthm division-left-shift-digit-correct
  (implies (and (division-digit-p digit) (posp scale) (<= scale *division-radix*)
                (natp carry) (< carry scale))
           (let* ((word (+ (* digit scale) carry))
                  (out (mv-nth 0 (division-left-shift-digit digit carry scale)))
                  (next (mv-nth 1 (division-left-shift-digit digit carry scale))))
             (and (unsigned-byte-p 64 word)
                  (division-digit-p out)
                  (natp next) (< next scale)
                  (equal (+ out (* *division-radix* next)) word))))
  :hints (("Goal"
           :use ((:instance division-floor-at-least
                            (a (+ (* digit scale) carry)) (b *division-radix*) (q scale))
                 (:instance division-mod-bounds (a (+ (* digit scale) carry)) (b *division-radix*))
                 (:instance division-floor-mod-identity
                            (a (+ (* digit scale) carry)) (b *division-radix*))
                 (:instance division-positive-product-order
                            (a (1- *division-radix*)) (b digit) (factor scale)))
           :nonlinearp t
           :in-theory (disable division-floor-mod-identity)))
  :rule-classes nil)

(defun division-left-shift-limbs (digits carry scale)
  (if (atom digits)
      (mv nil carry)
    (mv-let (digit next)
      (division-left-shift-digit (car digits) carry scale)
      (mv-let (upper final)
        (division-left-shift-limbs (cdr digits) next scale)
        (mv (cons digit upper) final)))))

(defthm division-left-shift-limbs-correct
  (implies (and (division-digits-p digits) (posp scale) (<= scale *division-radix*)
                (natp carry) (< carry scale))
           (mv-let (written final)
             (division-left-shift-limbs digits carry scale)
             (and (division-digits-p written)
                  (equal (len written) (len digits))
                  (natp final) (< final scale)
                  (equal (+ (division-magnitude written)
                            (* (division-place-value (len digits)) final))
                         (+ (* scale (division-magnitude digits)) carry)))))
  :hints (("Goal" :induct (division-left-shift-limbs digits carry scale)
                  :in-theory (disable division-left-shift-digit))
          ("Subgoal *1/2"
           :use ((:instance division-left-shift-digit-correct (digit (car digits)))
                 (:instance division-scale-equality
                            (factor *division-radix*)
                            (a (let ((next (mv-nth 1 (division-left-shift-digit (car digits) carry scale))))
                                 (mv-let (upper final)
                                   (division-left-shift-limbs (cdr digits) next scale)
                                   (+ (division-magnitude upper)
                                      (* (division-place-value (len (cdr digits))) final)))))
                            (b (+ (* scale (division-magnitude (cdr digits)))
                                  (mv-nth 1 (division-left-shift-digit (car digits) carry scale))))))))
  :rule-classes nil)

(local
 (defthm division-original-division-scales
   (implies (and (natp a) (posp b) (posp scale))
            (let ((q (floor a b))
                  (r (* scale (mod a b))))
              (and (natp r) (< r (* b scale))
                   (equal (* a scale) (+ (* b scale q) r)))))
   :hints (("Goal"
            :use ((:instance division-mod-bounds)
                  (:instance division-floor-mod-identity)
                  (:instance division-scale-equality
                             (a (+ (* b (floor a b)) (mod a b)))
                             (b a) (factor scale))
                  (:instance division-positive-product-order
                             (a (mod a b)) (b b) (factor scale)))
            :in-theory (disable division-floor-mod-identity)))
   :rule-classes nil))

(defthm division-undo-normalization
  (implies (and (natp a) (posp b) (posp scale)
                (natp q) (natp scaled-remainder)
                (< scaled-remainder (* b scale))
                (equal (* a scale) (+ (* b scale q) scaled-remainder)))
           (and (equal q (floor a b))
                (equal scaled-remainder (* scale (mod a b)))
                (equal (floor scaled-remainder scale) (mod a b))))
  :hints (("Goal"
           :use ((:instance division-original-division-scales)
                 (:instance division-quotient-unique
                            (a (* a scale)) (b (* b scale)) (r scaled-remainder))
                 (:instance division-quotient-unique
                            (a (* a scale)) (b (* b scale)) (q (floor a b))
                            (r (* scale (mod a b))))
                 (:instance division-remainder-unique
                            (a (* a scale)) (b (* b scale)) (r scaled-remainder))
                 (:instance division-remainder-unique
                            (a (* a scale)) (b (* b scale)) (q (floor a b))
                            (r (* scale (mod a b))))
                 (:instance division-quotient-unique
                            (a (* scale (mod a b))) (b scale) (q (mod a b)) (r 0))
                 (:instance division-mod-bounds)
                 (:instance division-positive-product (a b) (b scale)))))
  :rule-classes nil)

(defun division-leading-limb (digits)
  (if (consp (cdr digits))
      (division-leading-limb (cdr digits))
    (car digits)))

(local
 (defthm division-leading-limb-is-digit
   (implies (and (consp digits) (division-digits-p digits))
            (division-digit-p (division-leading-limb digits)))))

(local
 (defthm division-clz-scale-range
   (implies (and (division-digit-p leading) (posp leading))
            (let ((scale (expt 2 (division-normalization-shift leading))))
              (and (posp scale) (< scale *division-radix*))))
   :hints (("Goal"
            :use ((:instance division-clz-shift-bounds)
                  (:instance division-power-of-two-strict-order
                             (left (division-normalization-shift leading)) (right 32)))
            :in-theory (disable division-normalization-shift)))
   :rule-classes nil))

(local
 (defthm division-left-shift-limbs-cons
   (implies (consp digits)
            (equal (division-left-shift-limbs digits carry scale)
                   (mv-let (digit next)
                     (division-left-shift-digit (car digits) carry scale)
                     (mv-let (upper final)
                       (division-left-shift-limbs (cdr digits) next scale)
                       (mv (cons digit upper) final)))))
   :hints (("Goal" :expand ((division-left-shift-limbs digits carry scale))))
   :rule-classes nil))

(local
 (defthm division-left-shift-limbs-stays-nonempty
   (equal (consp (mv-nth 0 (division-left-shift-limbs digits carry scale))) (consp digits))
   :hints (("Goal" :expand ((division-left-shift-limbs digits carry scale))))))

(local
 (defun division-leading-shift-induct (digits carry scale)
   (if (consp (cdr digits))
       (mv-let (digit next)
         (division-left-shift-digit (car digits) carry scale)
         (declare (ignore digit))
         (division-leading-shift-induct (cdr digits) next scale))
     carry)))

(local
 (defthm division-left-shift-bounded-leading
   (implies (and (consp digits) (division-digits-p digits)
                 (posp scale) (<= scale *division-radix*)
                 (<= (/ *division-radix* 2) (* scale (division-leading-limb digits)))
                 (<= (+ (* scale (division-leading-limb digits)) scale) *division-radix*)
                 (natp carry) (< carry scale))
            (mv-let (shifted final)
              (division-left-shift-limbs digits carry scale)
              (and (division-leading-digit-p (division-leading-limb shifted))
                   (equal final 0))))
   :hints (("Goal"
            :induct (division-leading-shift-induct digits carry scale)
            :in-theory (disable division-left-shift-digit division-leading-digit-p))
           ("Subgoal *1/1"
            :use ((:instance division-left-shift-digit-correct (digit (car digits)))
                  (:instance division-left-shift-limbs-cons)))
           ("Subgoal *1/2"
            :use (:instance division-left-shift-limbs-cons)
            :in-theory (enable division-left-shift-digit division-leading-digit-p)))
   :rule-classes nil))

(defthm division-left-shift-normalizes-divisor
  (implies (and (consp digits) (division-digits-p digits)
                (posp (division-leading-limb digits))
                (equal scale (expt 2 (division-normalization-shift (division-leading-limb digits))))
                (natp carry) (< carry scale))
           (mv-let (shifted final)
             (division-left-shift-limbs digits carry scale)
             (and (division-leading-digit-p (division-leading-limb shifted))
                  (equal final 0))))
  :hints (("Goal"
           :use ((:instance division-leading-limb-is-digit)
                 (:instance division-clz-scale-range (leading (division-leading-limb digits)))
                 (:instance division-clz-shift-bounds (leading (division-leading-limb digits)))
                 (:instance division-normalized-leading-digit
                            (leading (division-leading-limb digits)) (carry 0))
                 (:instance division-normalized-leading-digit
                            (leading (division-leading-limb digits)) (carry (1- scale)))
                 (:instance division-ash-left
                            (x (division-leading-limb digits))
                            (width (division-normalization-shift (division-leading-limb digits))))
                 (:instance division-left-shift-bounded-leading))
           :in-theory (disable division-left-shift-limbs division-normalization-shift
                               division-leading-limb division-leading-limb-is-digit division-ash-left)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-floor-with-whole-part
   (implies (and (natp whole) (natp partial) (posp scale))
            (equal (floor (+ (* scale whole) partial) scale)
                   (+ whole (floor partial scale))))
   :hints (("Goal"
            :use ((:instance division-mod-bounds (a partial) (b scale))
                  (:instance division-floor-mod-identity (a partial) (b scale))
                  (:instance division-quotient-unique
                             (a (+ (* scale whole) partial)) (b scale)
                             (q (+ whole (floor partial scale))) (r (mod partial scale))))
            :in-theory (disable division-floor-mod-identity)))
   :rule-classes nil))

(defthm division-right-shift-digit-correct
  (implies (and (division-digit-p digit) (division-digit-p upper)
                (posp scale) (< scale *division-radix*))
           (equal (mod (floor (+ digit (* *division-radix* upper)) scale) *division-radix*)
                  (mv-nth 0 (division-one-limb-step digit (mod upper scale) scale))))
  :hints (("Goal"
           :use ((:instance division-mod-bounds (a upper) (b scale))
                 (:instance division-floor-mod-identity (a upper) (b scale))
                 (:instance division-scale-equality
                            (a (+ (* scale (floor upper scale)) (mod upper scale)))
                            (b upper) (factor *division-radix*))
                 (:instance division-floor-with-whole-part
                            (whole (* *division-radix* (floor upper scale)))
                            (partial (+ digit (* *division-radix* (mod upper scale)))))
                 (:instance division-one-limb-step-correct (remainder (mod upper scale)) (divisor scale))
                 (:instance division-remainder-unique
                            (a (floor (+ digit (* *division-radix* upper)) scale))
                            (b *division-radix*)
                            (q (floor upper scale))
                            (r (mv-nth 0 (division-one-limb-step digit (mod upper scale) scale)))))
           :in-theory (disable division-floor-mod-identity)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-clz-assoc-after-write
   (equal (assoc-equal 10 (put-assoc-equal 10 value registers)) (cons 10 value))
   :hints (("Goal" :induct (put-assoc-equal 10 value registers)))))

(defthm division-clz-count-in-model
  (let ((leading (proof-reg 10 machine)))
    (implies (and (division-digit-p leading) (posp leading))
             (equal (- (proof-reg 10 (proof-execute '(:clz 10 10) machine)) 32)
                    (division-normalization-shift leading))))
  :hints (("Goal"
           :use (:instance division-clz-shift-bounds (leading (proof-reg 10 machine)))
           :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-is-remainder
                               integer-length)
           :do-not-induct t))
  :rule-classes nil)
