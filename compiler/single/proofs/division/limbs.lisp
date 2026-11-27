(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate)))

(defun division-digit-p (digit)
  (unsigned-byte-p 32 digit))

(defun division-digits-p (digits)
  (if (atom digits)
      (null digits)
    (and (division-digit-p (car digits))
         (division-digits-p (cdr digits)))))

; Digits are stored with the least significant digit first.
(defun division-magnitude (digits)
  (if (atom digits)
      0
    (+ (nfix (car digits))
       (* *division-radix* (division-magnitude (cdr digits))))))

(defun division-place-value (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* *division-radix* (division-place-value (1- count)))))

(defthm division-magnitude-bound
  (implies (division-digits-p digits)
           (< (division-magnitude digits)
              (division-place-value (len digits))))
  :rule-classes :linear)

(defun division-one-limb-step (digit remainder divisor)
  (let* ((word (+ digit (* *division-radix* remainder)))
         (quotient (floor word divisor)))
    (mv quotient (- word (* quotient divisor)))))

(defthm division-one-limb-step-correct
  (implies (and (division-digit-p digit)
                (division-digit-p divisor) (posp divisor)
                (natp remainder) (< remainder divisor))
           (let* ((word (+ digit (* *division-radix* remainder)))
                  (quotient (mv-nth 0 (division-one-limb-step digit remainder divisor)))
                  (next (mv-nth 1 (division-one-limb-step digit remainder divisor))))
             (and (unsigned-byte-p 64 word)
                  (division-digit-p quotient)
                  (natp next)
                  (< next divisor)
                  (equal (+ (* divisor quotient) next) word))))
  :hints (("Goal"
           :use ((:instance division-floor-bounds
                            (a (+ digit (* *division-radix* remainder))) (b divisor))
                 (:instance division-floor-at-least
                            (a (+ digit (* *division-radix* remainder))) (b divisor)
                            (q *division-radix*)))
           :nonlinearp t))
  :rule-classes nil)

(defun division-one-limb-loop (digits divisor)
  (if (atom digits)
      (mv nil 0)
    (mv-let (high-quotient high-remainder)
      (division-one-limb-loop (cdr digits) divisor)
      (mv-let (digit remainder)
        (division-one-limb-step (car digits) high-remainder divisor)
        (mv (cons digit high-quotient) remainder)))))

(defthm division-one-limb-loop-correct
  (implies (and (division-digits-p digits)
                (division-digit-p divisor) (posp divisor))
           (let ((quotient (mv-nth 0 (division-one-limb-loop digits divisor)))
                 (remainder (mv-nth 1 (division-one-limb-loop digits divisor))))
             (and (division-digits-p quotient)
                  (equal (len quotient) (len digits))
                  (natp remainder)
                  (< remainder divisor)
                  (equal (+ (* divisor (division-magnitude quotient)) remainder)
                         (division-magnitude digits)))))
  :hints (("Goal" :induct (division-one-limb-loop digits divisor)
                  :in-theory (disable division-one-limb-step))
          ("Subgoal *1/2"
           :use ((:instance division-one-limb-step-correct
                            (digit (car digits))
                            (remainder (mv-nth 1 (division-one-limb-loop (cdr digits) divisor))))
                 (:instance division-scale-equality
                            (a (+ (* divisor (division-magnitude
                                              (mv-nth 0 (division-one-limb-loop (cdr digits) divisor))))
                                  (mv-nth 1 (division-one-limb-loop (cdr digits) divisor))))
                            (b (division-magnitude (cdr digits)))
                            (factor *division-radix*)))
           :nonlinearp t))
  :rule-classes nil)
