(in-package "BOYMOO-PROOFS")

(include-book "long-loop")
(include-book "normalization")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod)))

(defun division-one-limb-result (digits divisor)
  (mv-let (quotient remainder)
    (division-one-limb-loop digits divisor)
    (mv (division-trim-limbs quotient)
        (if (equal remainder 0) nil (list remainder)))))

(defthm division-one-limb-result-correct
  (implies (and (division-digits-p digits)
                (division-digit-p divisor) (posp divisor))
           (mv-let (quotient remainder)
             (division-one-limb-result digits divisor)
             (and (division-normalized-limbs-p quotient)
                  (division-normalized-limbs-p remainder)
                  (<= (len remainder) 1)
                  (< (division-magnitude remainder) divisor)
                  (equal (+ (* divisor (division-magnitude quotient))
                            (division-magnitude remainder))
                         (division-magnitude digits)))))
  :hints (("Goal"
           :use ((:instance division-one-limb-loop-correct)
                 (:instance division-trim-limbs-correct
                            (digits (mv-nth 0 (division-one-limb-loop digits divisor)))))
           :in-theory (disable division-one-limb-loop division-trim-limbs)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-normalized-loop-gives-unscaled-result
  (implies (and (natp a) (posp b) (division-digits-p scaled-digits)
                (division-normalized-divisor-p lead next tail scale)
                (equal (division-magnitude scaled-digits) (* a scale))
                (equal (division-normalized-divisor lead next tail scale) (* b scale)))
           (mv-let (digits scaled-remainder)
             (division-normalized-loop scaled-digits lead next tail scale)
             (let* ((quotient (division-trim-limbs digits))
                    (r (floor scaled-remainder scale)))
               (and (division-normalized-limbs-p quotient)
                    (natp r) (< r b)
                    (equal (+ (* b (division-magnitude quotient)) r) a)))))
  :hints (("Goal"
           :use ((:instance division-normalized-loop-correct (digits scaled-digits))
                 (:instance division-undo-normalization
                            (q (division-magnitude
                                (mv-nth 0 (division-normalized-loop scaled-digits lead next tail scale))))
                            (scaled-remainder
                             (mv-nth 1 (division-normalized-loop scaled-digits lead next tail scale))))
                 (:instance division-trim-limbs-correct
                            (digits (mv-nth 0 (division-normalized-loop scaled-digits lead next tail scale))))
                 (:instance division-mod-bounds)
                 (:instance division-floor-mod-identity))
           :in-theory (disable division-normalized-loop division-normalized-divisor
                               division-trim-limbs division-floor-mod-identity
                               division-normalized-limbs-p)
           :do-not-induct t))
  :rule-classes nil)
