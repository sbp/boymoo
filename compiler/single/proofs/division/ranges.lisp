(in-package "BOYMOO-PROOFS")

(include-book "limbs")

(logic)
(set-verify-guards-eagerness 0)

(defun division-buffer-bytes (a-count b-count)
  (* 8 (+ 3 (max a-count b-count))))

(defun division-reservation-bytes (a-count b-count)
  (* 5 (division-buffer-bytes a-count b-count)))

(defthm division-reservation-word-bounds
  (implies (and (natp a-count) (< a-count (expt 2 29))
                (natp b-count) (< b-count (expt 2 29)))
           (and (unsigned-byte-p 64 (division-buffer-bytes a-count b-count))
                (unsigned-byte-p 64 (division-reservation-bytes a-count b-count))))
  :rule-classes nil)

(defun division-buffer-base (base stride slot)
  (+ base (* stride slot)))

(local
 (defthm division-buffer-base-zero
   (implies (natp base)
            (equal (division-buffer-base base stride 0) base))
   :hints (("Goal" :use (:instance distributivity (x stride) (y 0) (z 0))))))

(defthm division-buffer-range
  (implies (and (proof-span-p base (* 5 stride)) (posp stride)
                (natp slot) (< slot 5)
                (natp offset) (natp bytes) (<= (+ offset bytes) stride)
                (< offset stride))
           (proof-subspan-p (+ (division-buffer-base base stride slot) offset)
                            bytes
                            (division-buffer-base base stride slot)
                            (+ (division-buffer-base base stride slot) stride)))
  :hints (("Goal" :cases ((equal slot 0) (equal slot 1) (equal slot 2)
                         (equal slot 3) (equal slot 4))))
  :rule-classes nil)

(defthm division-distinct-buffers
  (implies (and (natp base) (posp stride)
                (natp left) (natp right) (not (equal left right)))
           (proof-disjoint-p (division-buffer-base base stride left)
                             (division-buffer-base base stride (1+ left))
                             (division-buffer-base base stride right)
                             (division-buffer-base base stride (1+ right))))
  :hints (("Goal"
           :use ((:instance division-positive-product-order
                            (a right) (b (1+ left)) (factor stride))
                 (:instance division-positive-product-order
                            (a left) (b (1+ right)) (factor stride)))
           :cases ((< left right))))
  :rule-classes nil)

(defun division-gcd-slot-p (slot)
  (member-equal slot '(1 3 4)))

(defthm division-gcd-rotation-preserves-slots
  (implies (and (division-gcd-slot-p a-slot)
                (division-gcd-slot-p b-slot)
                (division-gcd-slot-p remainder-slot)
                (not (equal a-slot b-slot))
                (not (equal a-slot remainder-slot))
                (not (equal b-slot remainder-slot)))
           (and (division-gcd-slot-p b-slot)
                (division-gcd-slot-p remainder-slot)
                (division-gcd-slot-p a-slot)
                (not (equal b-slot remainder-slot))
                (not (equal b-slot a-slot))
                (not (equal remainder-slot a-slot))))
  :rule-classes nil)

; The window contains one more dividend digit than divisor digits.
(defthm division-normalized-window-ranges
  (implies (and (natp a-count) (natp b-count) (<= 2 b-count)
                (natp position) (<= (+ position b-count) a-count)
                (division-gcd-slot-p remainder-slot)
                (proof-span-p base (division-reservation-bytes a-count b-count)))
           (let* ((stride (division-buffer-bytes a-count b-count))
                  (remainder (division-buffer-base base stride remainder-slot))
                  (scratch (division-buffer-base base stride 2)))
             (and (proof-subspan-p (+ base 16 (* 8 position)) 8 base (+ base stride))
                  (proof-subspan-p (+ remainder 16 (* 8 position))
                                   (* 8 (1+ b-count)) remainder (+ remainder stride))
                  (proof-subspan-p scratch (* 8 b-count) scratch (+ scratch stride)))))
  :hints (("Goal"
           :use ((:instance division-buffer-range
                            (stride (division-buffer-bytes a-count b-count))
                            (slot 0) (offset (+ 16 (* 8 position))) (bytes 8))
                 (:instance division-buffer-range
                            (stride (division-buffer-bytes a-count b-count))
                            (slot remainder-slot) (offset (+ 16 (* 8 position)))
                            (bytes (* 8 (1+ b-count))))
                 (:instance division-buffer-range
                            (stride (division-buffer-bytes a-count b-count))
                            (slot 2) (offset 0) (bytes (* 8 b-count))))
           :in-theory (disable proof-subspan-p division-buffer-base)))
  :rule-classes nil)

(defthm division-one-limb-ranges
  (implies (and (posp a-count)
                (natp position) (< position a-count)
                (division-gcd-slot-p remainder-slot)
                (proof-span-p base (division-reservation-bytes a-count 1)))
           (let* ((stride (division-buffer-bytes a-count 1))
                  (remainder (division-buffer-base base stride remainder-slot)))
             (and (proof-subspan-p (+ base 16 (* 8 position)) 8 base (+ base stride))
                  (proof-subspan-p (+ remainder 16) 8 remainder (+ remainder stride)))))
  :hints (("Goal"
           :use ((:instance division-buffer-range
                            (stride (division-buffer-bytes a-count 1))
                            (slot 0) (offset (+ 16 (* 8 position))) (bytes 8))
                 (:instance division-buffer-range
                            (stride (division-buffer-bytes a-count 1))
                            (slot remainder-slot) (offset 16) (bytes 8)))
           :in-theory (disable proof-subspan-p division-buffer-base)))
  :rule-classes nil)

(defthm division-covered-subspan
  (implies (and (proof-covered-p lower (- upper lower) access regions)
                (proof-subspan-p address size lower upper))
           (proof-covered-p address size access regions))
  :hints (("Goal" :induct (proof-covered-p lower (- upper lower) access regions)))
  :rule-classes nil)

(defthm division-covered-slice
  (implies (and (proof-covered-p base bytes access regions)
                (natp offset) (posp size) (<= (+ offset size) bytes))
           (proof-covered-p (+ base offset) size access regions))
  :hints (("Goal" :induct (proof-covered-p base bytes access regions)))
  :rule-classes nil)
