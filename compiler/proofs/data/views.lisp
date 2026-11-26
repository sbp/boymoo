(in-package "BOYMOO-PROOFS")

(include-book "static-values")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(defthmd data-header-type-and-size
  (implies (and (natp size) (unsigned-byte-p 8 type))
           (let ((header (+ type (* 256 size))))
             (and (equal (proof-header-type header) type)
                  (equal (proof-header-size header) size))))
  :hints (("Goal" :use ((:instance data-low-bits-unique
                                   (width 8) (residue type) (q size) (word (+ type (* 256 size))))
                       (:instance data-floor-unique
                                  (d 256) (q size) (x (+ type (* 256 size)))))
                  :in-theory (e/d (data-machine-unsigned-is-low-bits data-ash-right)
                                 (boymoo-compiler::low-bits boymoo-model::a64-unsigned ash floor)))))

(defun data-rank-for-word (word base objects)
  (nfix (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))

(defun data-word-visible-at-rank-p (word depth base objects)
  (and (posp depth)
       (or (oddp word) (equal (proof-word-tag word) 4)
           (< (data-rank-for-word word base objects) depth))))

(local
 (in-theory (disable proof-pointer-address proof-word-tag proof-load-word proof-load-string
                     proof-span-p proof-object-rank proof-object-kind evenp)))

(defthmd data-view-at-greater-rank
  (implies (data-word-visible-at-rank-p word depth base objects)
           (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-view word base objects packages machine)))
  :hints (("Goal" :expand ((proof-view-step :word word 0 depth base objects packages machine)
                           (proof-view-step :word word 0 (1+ (data-rank-for-word word base objects))
                                            base objects packages machine))
                  :in-theory (disable proof-integer-view proof-symbol-value proof-rational-value
                                      proof-complex-value proof-header-type proof-header-size))))

(defthmd data-view-of-static-string-fields
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (size (length string)))
    (implies (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (natp (proof-object-rank object)) (eq (proof-object-kind object) :header)
                  (stringp string) (proof-span-p address (+ 8 size))
                  (equal (proof-load-word address machine) (+ 1 (* 256 size)))
                  (equal (proof-load-string size (+ address 8) machine) string))
             (proof-value-p word string base objects packages machine)))
  :hints (("Goal" :use ((:instance data-header-type-and-size (size (length string)) (type 1)))
                  :in-theory (disable proof-header-type proof-header-size length))))

(defun data-child-value-p (word value rank base objects packages machine)
  (and (data-word-visible-at-rank-p word rank base objects)
       (proof-value-p word value base objects packages machine)))

(defthmd data-view-of-static-cons-fields
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object)))
    (implies (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 0)
                  object (posp rank) (eq (proof-object-kind object) :cons)
                  (proof-span-p address 16)
                  (data-child-value-p (proof-load-word address machine) first rank base objects packages machine)
                  (data-child-value-p (proof-load-word (+ address 8) machine) second rank
                                      base objects packages machine))
             (proof-value-p word (cons first second) base objects packages machine)))
  :hints (("Goal" :in-theory (e/d (data-view-at-greater-rank)
                                 (data-rank-for-word data-word-visible-at-rank-p proof-view proof-view-step))
                  :expand ((proof-view word base objects packages machine)
                           (:free (depth)
                                  (proof-view-step :word word 0 depth base objects packages machine))))))

(defun data-two-field-view (type first second packages)
  (let ((left (proof-value-view first)) (right (proof-value-view second)))
    (case type
      (2 (proof-symbol-value left right packages))
      (4 (proof-rational-value left right))
      (5 (proof-complex-value left right))
      (otherwise nil))))

(defthmd data-view-of-static-two-field-header
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object)))
    (implies (and (member-equal type '(2 4 5)) (unsigned-byte-p 64 word) (not (oddp word))
                  (equal (proof-word-tag word) 2) object (posp rank) (eq (proof-object-kind object) :header)
                  (proof-span-p address 24)
                  (equal (proof-load-word address machine) (+ 4096 type))
                  (data-child-value-p (proof-load-word (+ address 8) machine) first rank
                                      base objects packages machine)
                  (data-child-value-p (proof-load-word (+ address 16) machine) second rank
                                      base objects packages machine))
             (equal (proof-view word base objects packages machine)
                    (data-two-field-view type first second packages))))
  :hints (("Goal" :use ((:instance data-header-type-and-size (size 16)))
                  :in-theory (e/d (data-view-at-greater-rank)
                                 (data-rank-for-word data-word-visible-at-rank-p proof-view proof-view-step proof-header-type
                                  proof-header-size proof-symbol-value proof-rational-value
                                  proof-complex-value proof-integer-view))
                  :expand ((proof-view word base objects packages machine)
                           (:free (depth)
                                  (proof-view-step :word word 0 depth base objects packages machine))))))
