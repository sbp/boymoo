(in-package "BOYMOO-PROOFS")

(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

; The first limb is least significant. High zero limbs are suppressed
; only until the first nonzero limb is written.
(defun data-limb-list-p (limbs)
  (if (atom limbs)
      (null limbs)
    (and (unsigned-byte-p 32 (car limbs)) (data-limb-list-p (cdr limbs)))))

(defun data-limb-list-value (limbs)
  (if (atom limbs)
      0
    (+ (car limbs) (* 4294967296 (data-limb-list-value (cdr limbs))))))

(defun data-limb-list-normalized-p (limbs)
  (and (consp limbs)
       (if (consp (cdr limbs)) (data-limb-list-normalized-p (cdr limbs))
         (posp (car limbs)))))

(defun data-limb-encoding-p (limbs magnitude width leading)
  (and (data-limb-list-p limbs)
       (equal (data-limb-list-value limbs) magnitude)
       (<= (len limbs) width)
       (if leading
           (if (zp magnitude) (equal limbs nil) (data-limb-list-normalized-p limbs))
         (equal (len limbs) width))))

(local
 (in-theory (disable ash floor expt boymoo-compiler::low-bits)))

(local
 (defthm append-associative-for-limbs
   (equal (append (append first second) tail) (append first second tail))))

(local
 (defun limb-split-induction (magnitude width leading fuel)
   (declare (xargs :measure (nfix fuel)))
   (if (or (and leading (zp magnitude)) (<= width 1) (zp fuel))
       (list magnitude width leading fuel)
     (let* ((half (ash width -1))
            (bits (* 32 half))
            (high (ash magnitude (- bits))))
       (list (limb-split-induction high (- width half) leading (1- fuel))
             (limb-split-induction (boymoo-compiler::low-bits magnitude bits) half
                                   (and leading (zp high)) (1- fuel)))))))

(local
 (defthm limb-accumulator-append
   (equal (boymoo-compiler::data-integer-limbs magnitude width leading fuel (append prefix tail))
          (append (boymoo-compiler::data-integer-limbs magnitude width leading fuel prefix) tail))
   :hints (("Goal" :induct (boymoo-compiler::data-integer-limbs magnitude width leading fuel prefix)))))

(defthmd data-integer-limbs-append-tail
  (equal (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)
         (append (boymoo-compiler::data-integer-limbs magnitude width leading fuel nil) tail))
  :hints (("Goal" :use ((:instance limb-accumulator-append (prefix nil)))
                  :in-theory (disable limb-accumulator-append boymoo-compiler::data-integer-limbs))))

(local
 (defthm limb-split-at-empty-tail
   (implies (and (not (and leading (zp magnitude))) (< 1 width) (posp fuel))
            (let* ((half (ash width -1))
                   (bits (* 32 half))
                   (high (ash magnitude (- bits))))
              (equal (boymoo-compiler::data-integer-limbs magnitude width leading fuel nil)
                     (append (boymoo-compiler::data-integer-limbs
                              (boymoo-compiler::low-bits magnitude bits) half
                              (and leading (zp high)) (1- fuel) nil)
                             (boymoo-compiler::data-integer-limbs
                              high (- width half) leading (1- fuel) nil)))))
   :hints (("Goal" :expand ((boymoo-compiler::data-integer-limbs magnitude width leading fuel nil))
                   :use ((:instance data-integer-limbs-append-tail
                                    (magnitude (boymoo-compiler::low-bits magnitude (* 32 (ash width -1))))
                                    (width (ash width -1))
                                    (leading (and leading (zp (ash magnitude (- (* 32 (ash width -1)))))))
                                    (fuel (1- fuel))
                                    (tail (boymoo-compiler::data-integer-limbs
                                           (ash magnitude (- (* 32 (ash width -1))))
                                           (- width (ash width -1)) leading (1- fuel) nil))))))))

(local
 (defthm limbs-p-of-append
   (implies (and (data-limb-list-p low) (data-limb-list-p high))
            (data-limb-list-p (append low high)))))

(local
 (defthm normal-limbs-of-append
   (implies (data-limb-list-normalized-p high)
            (data-limb-list-normalized-p (append low high)))
   :hints (("Goal" :induct (append low high)))))

(local
 (defthm length-of-appended-limbs
   (equal (len (append low high)) (+ (len low) (len high)))))

(local
 (defthm true-limb-list
   (implies (data-limb-list-p limbs) (true-listp limbs))))

(local
 (defthm limb-radix-power-step
   (implies (natp exponent)
            (equal (expt 2 (+ 32 exponent)) (* 4294967296 (expt 2 exponent))))
   :hints (("Goal" :use ((:instance data-two-power-of-sum (lower 32) (upper exponent)))))))

(local
 (defthm limb-value-of-append
   (equal (data-limb-list-value (append low high))
          (+ (data-limb-list-value low)
             (* (data-limb-list-value high) (expt 2 (* 32 (len low))))))
   :hints (("Goal" :induct (append low high))
           ("Subgoal *1/2" :use ((:instance data-swap-front-factors
                                            (a 4294967296) (b (data-limb-list-value high))
                                            (c (expt 2 (* 32 (len (cdr low)))))))))))

(local
 (defthm limb-value-is-natural
   (implies (data-limb-list-p limbs) (natp (data-limb-list-value limbs)))))

(local
 (defthm limb-half-width-bounds
   (implies (and (posp width) (< 1 width))
            (and (posp (ash width -1)) (< (ash width -1) width)))
   :hints (("Goal" :use ((:instance data-floor-bounds (x width) (d 2)))
                   :in-theory (enable data-ash-right)))))

(local
 (defthm limb-high-magnitude-bounds
   (implies (and (natp magnitude) (natp half) (natp remaining)
                 (< magnitude (expt 2 (+ (* 32 half) (* 32 remaining)))))
            (and (natp (ash magnitude (- (* 32 half))))
                 (< (ash magnitude (- (* 32 half))) (expt 2 (* 32 remaining)))))
   :hints (("Goal" :use ((:instance data-floor-bounds (x magnitude) (d (expt 2 (* 32 half))))
                        (:instance data-two-power-of-sum (lower (* 32 half)) (upper (* 32 remaining))))
                   :in-theory (enable data-ash-right) :nonlinearp t))))

(local
 (defthm limb-split-reconstructs-magnitude
   (implies (and (integerp magnitude) (natp half))
            (equal (+ (boymoo-compiler::low-bits magnitude (* 32 half))
                      (* (ash magnitude (- (* 32 half))) (expt 2 (* 32 half))))
                   magnitude))
   :hints (("Goal" :in-theory (enable data-low-bits-remainder data-ash-right)))))

(local
 (defthm limb-split-in-range
   (implies (and (natp magnitude) (posp width) (< 1 width) (natp fuel)
                 (<= width (1+ fuel)) (< magnitude (expt 2 (* 32 width))))
            (let* ((half (ash width -1))
                   (remaining (- width half))
                   (bits (* 32 half))
                   (high (ash magnitude (- bits)))
                   (low (boymoo-compiler::low-bits magnitude bits)))
              (and (posp half) (posp remaining) (posp fuel)
                   (<= half fuel) (<= remaining fuel)
                   (natp high) (< high (expt 2 (* 32 remaining)))
                   (natp low) (< low (expt 2 bits)))))
   :rule-classes nil
   :hints (("Goal" :use (limb-half-width-bounds
                        (:instance data-low-bits-in-range (word magnitude) (width (* 32 (ash width -1))))
                        (:instance limb-high-magnitude-bounds
                                   (half (ash width -1)) (remaining (- width (ash width -1)))))
                   :in-theory (disable limb-high-magnitude-bounds data-low-bits-in-range
                                       limb-half-width-bounds)))))

(local
 (defthm limb-encodings-compose
   (implies (and (natp low-value) (natp high-value)
                 (data-limb-encoding-p high high-value remaining leading)
                 (data-limb-encoding-p low low-value half (and leading (zp high-value))))
            (data-limb-encoding-p (append low high)
                                  (+ low-value (* high-value (expt 2 (* 32 half))))
                                  (+ half remaining) leading))
   :hints (("Goal" :in-theory (disable data-limb-list-p data-limb-list-value
                                       data-limb-list-normalized-p)
                   :cases ((equal high-value 0))))))

(defthmd data-integer-limbs-normalized-value
  (implies (and (natp magnitude) (posp width) (natp fuel)
                (<= width (1+ fuel)) (< magnitude (expt 2 (* 32 width))))
           (data-limb-encoding-p (boymoo-compiler::data-integer-limbs magnitude width leading fuel nil)
                                 magnitude width leading))
  :hints (("Goal" :induct (limb-split-induction magnitude width leading fuel)
                  :in-theory (disable boymoo-compiler::data-integer-limbs data-limb-encoding-p
                                      limb-half-width-bounds limb-split-reconstructs-magnitude
                                      limb-encodings-compose))
          ("Subgoal *1/2" :use (limb-split-in-range
                                 (:instance limb-split-reconstructs-magnitude (half (ash width -1)))
                                 (:instance limb-encodings-compose
                                            (half (ash width -1)) (remaining (- width (ash width -1)))
                                            (high-value (ash magnitude (- (* 32 (ash width -1)))))
                                            (low-value (boymoo-compiler::low-bits magnitude (* 32 (ash width -1))))
                                            (low (boymoo-compiler::data-integer-limbs
                                                  (boymoo-compiler::low-bits magnitude (* 32 (ash width -1)))
                                                  (ash width -1)
                                                  (and leading (zp (ash magnitude (- (* 32 (ash width -1))))))
                                                  (1- fuel) nil))
                                            (high (boymoo-compiler::data-integer-limbs
                                                   (ash magnitude (- (* 32 (ash width -1))))
                                                   (- width (ash width -1)) leading (1- fuel) nil)))))
          ("Subgoal *1/1" :in-theory (enable boymoo-compiler::data-integer-limbs data-limb-encoding-p))))
