(in-package "BOYMOO-PROOFS")

(include-book "equality-views")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-fraction-p (value)
  (and (rationalp value) (not (integerp value))))

(defund p6-rational-comparison-size (value)
  (if (p6-fraction-p value) 3 1))

; The cost counts the nodes in the comparison tree. An integer, string,
; character or symbol is a leaf even when its comparison reads memory.
(defun p6-datum-comparison-size (value)
  (cond ((consp value)
         (+ 1 (p6-datum-comparison-size (car value)) (p6-datum-comparison-size (cdr value))))
        ((complex-rationalp value)
         (+ 1 (p6-rational-comparison-size (realpart value))
            (p6-rational-comparison-size (imagpart value))))
        (t (p6-rational-comparison-size value))))

(defthm p6-datum-comparison-size-positive
  (posp (p6-datum-comparison-size value))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (p6-datum-comparison-size value)
                  :in-theory (enable p6-rational-comparison-size))))

(defund p6-pair-comparison-size (left right)
  (+ (p6-datum-comparison-size left) (p6-datum-comparison-size right)))

(defun p6-comparison-work-size (pairs)
  (if (atom pairs)
      0
    (+ (p6-pair-comparison-size (caar pairs) (cdar pairs))
       (p6-comparison-work-size (cdr pairs)))))

(defthm p6-comparison-work-size-natural
  (natp (p6-comparison-work-size pairs))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (p6-comparison-work-size pairs) :in-theory (enable p6-pair-comparison-size))))

(defund p6-datum-comparison-fields (left right)
  (cond ((and (consp left) (consp right))
         (list (cons (car left) (car right)) (cons (cdr left) (cdr right))))
        ((and (p6-fraction-p left) (p6-fraction-p right))
         (list (cons (numerator left) (numerator right)) (cons (denominator left) (denominator right))))
        ((and (complex-rationalp left) (complex-rationalp right))
         (list (cons (realpart left) (realpart right)) (cons (imagpart left) (imagpart right))))))

(local
 (defthm p6-rational-datum-has-rational-size
   (implies (rationalp value)
            (equal (p6-datum-comparison-size value) (p6-rational-comparison-size value)))
   :hints (("Goal" :expand ((p6-datum-comparison-size value))))))

(defthm p6-decomposing-datum-pair-reduces-work
  (let ((fields (p6-datum-comparison-fields left right)))
    (implies fields
             (< (p6-comparison-work-size fields) (p6-pair-comparison-size left right))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-datum-comparison-fields p6-pair-comparison-size
                              p6-rational-comparison-size p6-fraction-p)
           :expand ((p6-datum-comparison-size left) (p6-datum-comparison-size right)))))

(local
 (defthm p6-comparison-work-size-of-append
   (equal (p6-comparison-work-size (append first second))
          (+ (p6-comparison-work-size first) (p6-comparison-work-size second)))
   :hints (("Goal" :induct (len first)))))

(defun p6-pending-datum-equalities-p (pairs)
  (or (atom pairs)
      (and (equal (caar pairs) (cdar pairs)) (p6-pending-datum-equalities-p (cdr pairs)))))

(defthm p6-comparison-fields-preserve-equality
  (let ((fields (p6-datum-comparison-fields left right)))
    (implies fields
             (equal (p6-pending-datum-equalities-p fields) (equal left right))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-datum-comparison-fields p6-fraction-p)
           :use ((:instance p6-rational-equality-by-parts (first left) (second right))
                 (:instance p6-complex-equality-by-parts (first left) (second right))))))

(local
 (defthm p6-pending-equalities-of-append
   (equal (p6-pending-datum-equalities-p (append first second))
          (and (p6-pending-datum-equalities-p first) (p6-pending-datum-equalities-p second)))
   :hints (("Goal" :induct (p6-pending-datum-equalities-p first)))))

(defun p6-compare-pending-datums (pairs)
  (declare (xargs :measure (p6-comparison-work-size pairs)
                  :hints (("Goal"
                           :in-theory (enable p6-pair-comparison-size)
                           :use ((:instance p6-decomposing-datum-pair-reduces-work
                                            (left (caar pairs)) (right (cdar pairs))))))))
  (if (atom pairs)
      t
    (let ((left (caar pairs)) (right (cdar pairs)) (rest (cdr pairs)))
      (let ((fields (p6-datum-comparison-fields left right)))
        (if fields
            (p6-compare-pending-datums (append fields rest))
          (and (equal left right) (p6-compare-pending-datums rest)))))))

(defthm p6-comparison-work-computes-conjunction
  (equal (p6-compare-pending-datums pairs) (p6-pending-datum-equalities-p pairs))
  :rule-classes nil
  :hints (("Goal" :induct (p6-compare-pending-datums pairs))
          (and stable-under-simplificationp
               '(:use ((:instance p6-comparison-fields-preserve-equality (left (caar pairs)) (right (cdar pairs))))))))
