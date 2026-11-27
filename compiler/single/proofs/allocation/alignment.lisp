(in-package "BOYMOO-PROOFS")

(include-book "words")

(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-align-up-bounds
  (implies (and (natp size) (posp alignment))
           (and (natp (proof-align-up size alignment))
                (<= size (proof-align-up size alignment))
                (< (proof-align-up size alignment) (+ size alignment))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm allocation-align-up-multiple
  (implies (and (natp size) (posp alignment))
           (equal (mod (proof-align-up size alignment) alignment) 0)))

(defthm allocation-align-up-of-multiple
  (implies (and (natp size) (posp alignment) (equal (mod size alignment) 0))
           (equal (proof-align-up size alignment) size))
  :hints (("Goal" :in-theory (disable mod))))

(local
 (defthm allocation-alignment-quotient-is-integer
   (implies (and (natp size) (posp alignment))
            (integerp (/ (proof-align-up size alignment) alignment)))))

(local
 (defthm allocation-integers-at-distance-less-than-one
   (implies (and (integerp a) (integerp b) (< a (+ 1 b)))
            (<= a b))))

(defthm allocation-align-eight-below-aligned-limit
  (implies (and (natp size) (natp limit)
                (<= size limit) (equal (mod limit 8) 0))
           (<= (proof-align-up size 8) limit))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-align-up-bounds (alignment 8))
                 (:instance allocation-align-up-of-multiple (size limit) (alignment 8))
                 (:instance allocation-alignment-quotient-is-integer (alignment 8))
                 (:instance allocation-alignment-quotient-is-integer (size limit) (alignment 8))
                 (:instance allocation-integers-at-distance-less-than-one
                  (a (/ (proof-align-up size 8) 8)) (b (/ limit 8))))
           :in-theory (disable mod proof-align-up allocation-align-up-of-multiple
                               allocation-integers-at-distance-less-than-one
                               allocation-alignment-quotient-is-integer))))

(defthm allocation-page-alignment-of-runtime-multiple
  (implies (and (natp size) (equal (mod size *proof-runtime-page*) 0)
                (proof-page-size-p page))
           (equal (proof-align-up size page) size))
  :hints (("Goal" :cases ((equal page 4096) (equal page 16384))
           :in-theory (disable proof-align-up mod))))

(defthm allocation-round-up-with-shifts
  (implies (natp size)
           (equal (ash (ash (+ size (1- *proof-runtime-page*)) -16) 16)
                  (proof-align-up size *proof-runtime-page*)))
  :rule-classes nil)

(defthm allocation-doubled-stack-size-alignment
  (implies (and (integerp base) (integerp old-limit)
                (equal (mod base 8) 0) (equal (mod old-limit 8) 0))
           (equal (mod (+ base (* 2 (- old-limit base))) 8) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable mod))))

(defthm allocation-stack-reservation-alignment
  (implies (and (integerp base) (equal (mod base 8) 0))
           (equal (mod (+ base *proof-value-reservation*) 8) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable mod))))

(defthm allocation-length-test-shift
  (implies (unsigned-byte-p 64 word)
           (and (unsigned-byte-p 64 (ash word -32))
                (equal (equal (ash word -32) 0) (< word *proof-space-size*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(defthm allocation-large-rounding-fits
  (let* ((sum (+ length 32 (1- *proof-runtime-page*)))
         (blocks (ash sum -16))
         (size (ash blocks 16)))
    (implies (and (natp length) (< length *proof-space-size*))
             (and (unsigned-byte-p 64 sum)
                  (unsigned-byte-p 64 blocks)
                  (unsigned-byte-p 64 size)
                  (equal size (proof-align-up (+ length 32) *proof-runtime-page*)))))
  :hints (("Goal" :use ((:instance allocation-round-up-with-shifts (size (+ length 32))))
           :in-theory (disable proof-align-up))))

(defthm allocation-stack-slot-count
  (implies (natp count)
           (equal (ash (* 8 count) -3) count)))

(defthm allocation-aligned-eight-sum
  (implies (and (integerp first) (integerp second)
                (equal (mod first 8) 0) (equal (mod second 8) 0))
           (equal (mod (+ first second) 8) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable mod))))

(defthm allocation-slot-bytes-fit
  (implies (natp size)
           (and (natp (ash size -3))
                (<= (* 8 (ash size -3)) size)
                (implies (<= 8 size) (posp (ash size -3)))))
  :rule-classes nil)

(defthm allocation-header-size-natural
  (implies (natp word) (natp (proof-header-size word)))
  :rule-classes :type-prescription)

(defthm allocation-external-record-fits-mapping
  (let ((size (proof-align-up (+ 32 length) *proof-runtime-page*)))
    (implies (natp length)
             (<= (+ 24 (max 16 (+ 8 (proof-align-up length 8)))) size)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-align-up-bounds (size (+ 32 length)) (alignment *proof-runtime-page*))
                 (:instance allocation-alignment-quotient-is-integer
                  (size (+ 32 length)) (alignment *proof-runtime-page*))
                 (:instance allocation-align-eight-below-aligned-limit
                  (size length) (limit (- (proof-align-up (+ 32 length) *proof-runtime-page*) 32))))
           :in-theory (disable proof-align-up mod allocation-alignment-quotient-is-integer))))
