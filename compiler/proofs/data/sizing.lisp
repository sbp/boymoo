(in-package "BOYMOO-PROOFS")

(include-book "buckets")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::aligned-size ash)))

(defthm data-chunks-size-is-natural
  (natp (data-chunks-size chunks))
  :rule-classes :type-prescription)

(defthm data-sized-block-offset-is-natural
  (implies (data-block-sized-p block start) (natp (car block)))
  :rule-classes :forward-chaining)

(local
 (defthm data-sized-block-count
   (implies (data-block-sized-p block start)
            (and (equal (car block) (+ start (data-chunks-size (cdr block))))
                 (<= start (car block))))
   :rule-classes :forward-chaining))

(local
 (defthm word-chunks-of-append
   (equal (data-word-chunks-p (append first second))
          (and (data-word-chunks-p first) (data-word-chunks-p second)))))

(defthm data-bucket-leaves-are-word-chunks
  (implies (data-static-bucket-tree-p tree bits)
           (data-word-chunks-p (data-ascending-bucket-words tree bits)))
  :hints (("Goal" :induct (data-ascending-bucket-words tree bits))))

(defthm data-bucket-vector-preserves-measured-block-size
  (implies (and (data-static-bucket-tree-p tree bits) (data-block-sized-p block start))
           (data-block-sized-p (boymoo-compiler::data-bucket-vector tree bits block) start))
  :hints (("Goal" :in-theory (e/d (data-bucket-vector-serializes-ascending-leaves)
                                 (boymoo-compiler::data-words boymoo-compiler::data-bucket-vector
                                  data-static-bucket-tree-p data-block-sized-p)))))

(local
 (defthm final-bucket-append-has-integer-start
   (implies (and (data-static-bucket-tree-p (caddr state-data) 12)
                 (data-block-sized-p (boymoo-compiler::data-block state-data) 80))
            (data-block-sized-p
             (boymoo-compiler::data-bucket-vector
              (caddr state-data) 12
              (boymoo-compiler::data-word 8388614 (boymoo-compiler::data-block state-data)))
             80))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-bucket-vector
                                       boymoo-compiler::data-word data-static-bucket-tree-p
                                       data-block-sized-p)))))

(defthmd data-build-count-matches-image-under-body-invariant
  (mv-let (common-lisp package-word state-data) (data-before-buckets lines package-lines)
    (declare (ignore package-word))
    (let ((image (car (boymoo-compiler::data-build lines package-lines))))
      (implies (and common-lisp (data-static-bucket-tree-p (caddr state-data) 12)
                    (data-block-sized-p (boymoo-compiler::data-block state-data) 80))
               (and (proof-image-p image) (<= 80 (car image))))))
  :hints (("Goal" :use (data-build-fragment-count-agreement
                       (:instance final-bucket-append-has-integer-start
                                  (state-data (mv-nth 2 (data-before-buckets lines package-lines))))
                       (:instance data-block-sized-p-of-heap-limit-block
                                  (limit (boymoo-compiler::data-heap-limit lines nil))
                                  (block (let ((state-data (mv-nth 2 (data-before-buckets lines package-lines))))
                                           (boymoo-compiler::data-bucket-vector
                                            (caddr state-data) 12
                                            (boymoo-compiler::data-word
                                             8388614 (boymoo-compiler::data-block state-data)))))
                                  (start 80)))
                  :in-theory (e/d (data-build-image-and-index)
                                 (data-before-buckets boymoo-compiler::data-build
                                  boymoo-compiler::data-bucket-vector boymoo-compiler::data-word
                                  final-bucket-append-has-integer-start data-block-sized-p
                                  data-block-sized-p-of-heap-limit-block
                                  data-static-bucket-tree-p proof-fragments-size proof-fragments-p
                                  boymoo-compiler::data-write boymoo-compiler::reverse-onto)))))
