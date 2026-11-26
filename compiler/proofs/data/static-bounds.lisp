(in-package "BOYMOO-PROOFS")

(include-book "objects")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-compiler::low-bits ash floor evenp)))

(defthmd data-static-reference-fits-and-points-at-offset
  (let* ((offset (* 8 slot)) (word (+ offset tag)))
    (implies (and (proof-span-p base size) (natp slot) (< offset size) (< size *proof-space-size*)
                  (member-equal tag '(0 2)))
             (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) tag)
                  (equal (proof-pointer-address word base) (+ base offset)))))
  :hints (("Goal" :use ((:instance data-low-bits-unique (width 3) (word (+ (* 8 slot) tag))
                                   (q slot) (residue tag))
                        (:instance data-low-bits-unique (width 1) (word (+ (* 8 slot) tag))
                                   (q (+ (* 4 slot) (* 1/2 tag))) (residue 0))
                        (:instance data-low-bit-parity (word (+ (* 8 slot) tag))))
                  :in-theory (e/d (data-machine-unsigned-is-low-bits)
                                 (data-low-bit-parity data-low-bits-in-range)))))

(defthmd data-static-sized-header-fits-and-decodes
  (let ((header (+ type (* 256 payload))))
    (implies (and (natp payload) (< payload *proof-space-size*) (unsigned-byte-p 8 type))
             (and (unsigned-byte-p 64 header)
                  (equal (proof-header-type header) type)
                  (equal (proof-header-size header) payload))))
  :hints (("Goal" :use ((:instance data-header-type-and-size (size payload)))
                  :in-theory (disable proof-header-type proof-header-size))))

(defthmd data-static-offset-rank-is-below-root
  (implies (and (natp offset) (integerp size) (<= 112 size) (< offset size))
           (< (data-static-rank offset) (+ 1 (nfix (ash size -3)))))
  :hints (("Goal" :use ((:instance data-floor-bounds (x size) (d 8))
                        (:instance data-floor-bounds (x offset) (d 8)))
                  :in-theory (enable data-ash-right))))

(local
 (defthm bucket-slot-count-is-4096
   (equal (len (data-ascending-bucket-words tree 12)) 4096)
   :hints (("Goal" :use ((:instance data-bucket-vector-contains-one-word-per-path (bits 12)))
                   :in-theory (disable data-ascending-bucket-words)))))

(local
 (defthm bucket-vector-has-32768-payload-bytes
   (implies (integerp (car block))
            (equal (car (boymoo-compiler::data-bucket-vector tree 12 block)) (+ 32768 (car block))))
   :hints (("Goal" :use ((:instance data-words-allocate-consecutively
                                    (words (data-ascending-bucket-words tree 12)))
                         (:instance data-bucket-vector-serializes-ascending-leaves (bits 12)))
                   :in-theory (disable boymoo-compiler::data-bucket-vector data-ascending-bucket-words
                                       boymoo-compiler::data-words boymoo-compiler::reverse-onto)))))

(defthmd data-build-size-includes-the-bucket-vector
  (mv-let (common-lisp package-word state-data) (data-before-buckets lines package-lines)
    (declare (ignore package-word))
    (let* ((block (boymoo-compiler::data-block state-data))
           (offset (car block))
           (image (car (boymoo-compiler::data-build lines package-lines))))
      (implies (and common-lisp (data-block-sized-p block 80)
                    (not (boymoo-compiler::data-heap-limit lines nil)))
               (and (equal (car image) (+ offset 32776)) (<= 32856 (car image))))))
  :hints (("Goal" :use data-build-image-and-index
                  :in-theory (disable boymoo-compiler::data-build data-before-buckets
                                      boymoo-compiler::data-bucket-vector boymoo-compiler::reverse-onto
                                      boymoo-compiler::data-write data-chunks-size))))

(defthmd data-build-bounded-image-has-representable-size
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (size (car image)))
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (mv-nth 0 (data-before-buckets lines package-lines)) (< size *proof-space-size*))
             (and (proof-image-p image) (<= 32856 size) (unsigned-byte-p 64 size)
                  (equal (mod size 8) 0))))
  :hints (("Goal" :use (data-build-image-has-exact-size-for-storage-input
                        data-build-body-is-sized-for-storage-input data-build-size-includes-the-bucket-vector
                        data-build-declared-size-is-word-aligned)
                  :in-theory (disable boymoo-compiler::data-build data-before-buckets data-image-parts
                                      data-block-sized-p data-program-storage-input-p
                                      data-package-lines-storage-input-p proof-image-p mod))))
