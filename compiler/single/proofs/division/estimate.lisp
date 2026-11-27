(in-package "BOYMOO-PROOFS")

(include-book "limbs")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate)))

(defun division-leading-digit-p (lead)
  (and (division-digit-p lead)
       (<= (/ *division-radix* 2) lead)))

(defun division-estimate-stop-p (guess rest next digit)
  (or (<= *division-radix* rest)
      (<= (* guess next) (+ (* *division-radix* rest) digit))))

(defun division-correct-estimate (guess rest lead next digit)
  (declare (xargs :measure (nfix guess)))
  (if (or (zp guess) (division-estimate-stop-p guess rest next digit))
      guess
    (division-correct-estimate (1- guess) (+ rest lead) lead next digit)))

(defthm division-digit-product-bound
  (implies (and (division-digit-p x) (division-digit-p y))
           (< (* x y) (* *division-radix* *division-radix*)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm division-estimate-test-correct
  (implies (and (division-digit-p guess)
                (division-digit-p next) (division-digit-p digit)
                (natp rest) (natp lead))
           (equal (division-estimate-stop-p guess rest next digit)
                  (<= (* guess (+ (* *division-radix* lead) next))
                      (+ (* *division-radix* (+ (* guess lead) rest)) digit))))
  :hints (("Goal" :cases ((<= *division-radix* rest))
                  :nonlinearp t))
  :rule-classes nil)

(defthm division-correct-estimate-maximal
  (implies (and (division-digit-p guess)
                (division-leading-digit-p lead)
                (division-digit-p next) (division-digit-p digit)
                (natp rest))
           (let* ((head (+ (* guess lead) rest))
                  (two-divisor-digits (+ (* *division-radix* lead) next))
                  (three-dividend-digits (+ (* *division-radix* head) digit))
                  (q (division-correct-estimate guess rest lead next digit)))
             (and (division-digit-p q)
                  (<= q guess)
                  (<= (* q two-divisor-digits) three-dividend-digits)
                  (implies (< q guess)
                           (< three-dividend-digits (* (+ 1 q) two-divisor-digits))))))
  :hints (("Goal" :induct (division-correct-estimate guess rest lead next digit)
                  :in-theory (disable division-estimate-stop-p))
          ("Subgoal *1/2" :use division-estimate-test-correct)
          ("Subgoal *1/1" :use division-estimate-test-correct))
  :rule-classes nil)

(defun division-first-estimate (head lead)
  (min (1- *division-radix*) (floor head lead)))

(defthm division-first-estimate-bounds
  (implies (and (natp head) (posp lead))
           (let ((q (division-first-estimate head lead)))
             (and (division-digit-p q)
                  (<= (* q lead) head)
                  (implies (< q (1- *division-radix*))
                           (< head (* (+ 1 q) lead))))))
  :hints (("Goal"
           :use ((:instance division-floor-bounds (a head) (b lead))
                 (:instance division-positive-product-order
                            (a (floor head lead)) (b (1- *division-radix*))
                            (factor lead)))
           :nonlinearp t))
  :rule-classes nil)

(defun division-two-limb-estimate (head lead next digit)
  (let ((guess (division-first-estimate head lead)))
    (division-correct-estimate guess (- head (* guess lead)) lead next digit)))

(defthm division-two-limb-estimate-bounds
  (implies (and (natp head) (division-leading-digit-p lead)
                (division-digit-p next) (division-digit-p digit))
           (let* ((guess (division-first-estimate head lead))
                  (q (division-two-limb-estimate head lead next digit))
                  (top-divisor (+ (* *division-radix* lead) next))
                  (top-dividend (+ (* *division-radix* head) digit)))
             (and (division-digit-p q)
                  (<= q guess)
                  (<= (* q top-divisor) top-dividend)
                  (implies (< q guess)
                           (< top-dividend (* (+ 1 q) top-divisor)))
                  (implies (and (equal q guess) (< q (1- *division-radix*)))
                           (< head (* (+ 1 q) lead))))))
  :hints (("Goal"
           :use ((:instance division-first-estimate-bounds)
                 (:instance division-correct-estimate-maximal
                            (guess (division-first-estimate head lead))
                            (rest (- head (* lead (division-first-estimate head lead))))))
           :in-theory (disable division-first-estimate division-correct-estimate)))
  :rule-classes nil)

(local
 (defthm division-third-candidate-fits
   (implies (and (division-digit-p guess) (<= 2 guess)
                 (division-leading-digit-p lead)
                 (division-digit-p next) (division-digit-p digit)
                 (natp head) (<= (* guess lead) head))
            (<= (* (- guess 2) (+ (* *division-radix* lead) next))
                (+ (* *division-radix* head) digit)))
   :hints (("Goal" :use (:instance division-digit-product-bound (x (- guess 2)) (y next))))
   :rule-classes nil))

(defthm division-estimate-at-most-two-corrections
  (implies (and (natp head) (division-leading-digit-p lead)
                (division-digit-p next) (division-digit-p digit))
           (<= (division-first-estimate head lead)
               (+ 2 (division-two-limb-estimate head lead next digit))))
  :hints (("Goal"
           :use ((:instance division-first-estimate-bounds)
                 (:instance division-two-limb-estimate-bounds)
                 (:instance division-third-candidate-fits
                            (guess (division-first-estimate head lead)))
                 (:instance division-positive-product-order
                            (a (- (division-first-estimate head lead) 2))
                            (b (1+ (division-two-limb-estimate head lead next digit)))
                            (factor (+ (* *division-radix* lead) next))))
           :in-theory (disable division-first-estimate division-two-limb-estimate)))
  :rule-classes nil)

(defun division-prefix-value (head tail scale)
  (+ (* head scale) tail))

(defthm division-prefix-rejects-product
  (implies (and (natp a-head) (natp b-head) (posp scale) (natp q)
                (natp a-tail) (< a-tail scale) (natp b-tail)
                (< a-head (* q b-head)))
           (< (division-prefix-value a-head a-tail scale)
              (* q (division-prefix-value b-head b-tail scale))))
  :hints (("Goal"
           :use ((:instance division-positive-product-order
                            (a (* q b-head)) (b (1+ a-head)) (factor scale)))
           :nonlinearp t))
  :rule-classes nil)

(defthm division-prefix-estimate-lower-product
  (implies (and (natp a-head) (natp b-head) (<= *division-radix* b-head)
                (posp scale) (division-digit-p q)
                (natp a-tail) (natp b-tail) (< b-tail scale)
                (<= (* q b-head) a-head))
           (< (* (1- q) (division-prefix-value b-head b-tail scale))
              (division-prefix-value a-head a-tail scale)))
  :hints (("Goal"
           :use ((:instance division-positive-product-order
                            (a a-head) (b (* q b-head)) (factor scale))
                 (:instance division-positive-product-order
                            (a q) (b *division-radix*) (factor scale))
                 (:instance division-positive-product-order
                            (a b-tail) (b scale) (factor q))
                 (:instance division-positive-product-order
                            (a b-head) (b *division-radix*) (factor scale)))
           :cases ((equal q 0))))
  :rule-classes nil)

(defun division-window-p (head lead next digit a-tail b-tail scale)
  (and (unsigned-byte-p 64 head)
       (division-leading-digit-p lead)
       (division-digit-p next) (division-digit-p digit)
       (posp scale)
       (natp a-tail) (< a-tail scale)
       (natp b-tail) (< b-tail scale)
       (< (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale)
          (* *division-radix*
             (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))))

(local
 (defthm division-prefix-regroup
   (equal (division-prefix-value (+ (* *division-radix* high) digit) tail scale)
          (division-prefix-value high
                                 (division-prefix-value digit tail scale)
                                 (* *division-radix* scale)))
   :rule-classes nil))

(local
 (defthm division-prefix-tail-bound
   (implies (and (division-digit-p digit) (natp tail)
                 (posp scale) (< tail scale))
            (and (natp (division-prefix-value digit tail scale))
                 (< (division-prefix-value digit tail scale) (* *division-radix* scale))))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm division-window-estimate-bounds
  (implies (division-window-p head lead next digit a-tail b-tail scale)
           (let ((q (division-two-limb-estimate head lead next digit))
                 (a (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale))
                 (b (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))
             (and (division-digit-p q)
                  (< (* (1- q) b) a)
                  (< a (* (1+ q) b)))))
  :hints (("Goal"
           :use ((:instance division-two-limb-estimate-bounds)
                 (:instance division-prefix-estimate-lower-product
                            (q (division-two-limb-estimate head lead next digit))
                            (a-head (+ (* *division-radix* head) digit))
                            (b-head (+ (* *division-radix* lead) next))))
           :in-theory (disable division-prefix-value division-first-estimate
                               division-two-limb-estimate))
          ("Goal'"
           :cases ((< (division-two-limb-estimate head lead next digit)
                      (division-first-estimate head lead))
                   (equal (division-two-limb-estimate head lead next digit)
                          (1- *division-radix*))))
          ("Subgoal 3"
           :use ((:instance division-prefix-rejects-product
                            (q (1+ (division-two-limb-estimate head lead next digit)))
                            (a-head head) (b-head lead)
                            (a-tail (division-prefix-value digit a-tail scale))
                            (b-tail (division-prefix-value next b-tail scale))
                            (scale (* *division-radix* scale)))
                 (:instance division-prefix-regroup (high head) (tail a-tail))
                 (:instance division-prefix-regroup (high lead) (digit next) (tail b-tail))
                 (:instance division-prefix-tail-bound (tail a-tail))
                 (:instance division-prefix-tail-bound (digit next) (tail b-tail))))
          ("Subgoal 2"
           :use (:instance division-prefix-rejects-product
                           (q (1+ (division-two-limb-estimate head lead next digit)))
                           (a-head (+ (* *division-radix* head) digit))
                           (b-head (+ (* *division-radix* lead) next)))))
  :rule-classes nil)

(defthm division-estimate-words-fit
  (implies (and (unsigned-byte-p 64 head)
                (division-digit-p guess) (division-leading-digit-p lead)
                (division-digit-p next) (division-digit-p digit)
                (<= (* guess lead) head))
           (let ((rest (- head (* guess lead))))
             (and (unsigned-byte-p 64 rest)
                  (unsigned-byte-p 64 (* guess next))
                  (implies (< rest *division-radix*)
                           (unsigned-byte-p 64 (+ (* *division-radix* rest) digit)))
                  (implies (posp guess)
                           (unsigned-byte-p 64 (+ rest lead))))))
  :hints (("Goal"
           :use ((:instance division-positive-product-order (a guess) (b 1) (factor lead))
                 (:instance division-digit-product-bound (x guess) (y next)))
           :nonlinearp t))
  :rule-classes nil)
