(in-package "BOYMOO-PROOFS")

(include-book "chunk-retention")
(include-book "encoded-chunks")
(include-book "static-bounds")

(logic)
(set-verify-guards-eagerness 0)

(defun data-builtin-symbol-word (truth)
  (if truth *proof-t* *proof-nil*))

(defun data-builtin-name-word (truth)
  (if truth 98 82))

(defun data-builtin-name (truth)
  (if truth "T" "NIL"))

(local
 (in-theory (disable boymoo-compiler::data-build data-before-buckets data-image-parts
                     proof-load-word proof-load-string proof-view proof-value-p proof-pointer-address
                     proof-word-tag evenp data-placed-characters-p proof-image-at-p)))

(local
 (defthm common-lisp-number-is-the-package-lookup
   (equal (mv-nth 0 (data-before-buckets lines package-lines))
          (boymoo-compiler::index-get
           "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (data-before-buckets)
                                  (boymoo-compiler::index-get boymoo-compiler::data-package-numbers
                                   boymoo-compiler::data-initial boymoo-compiler::data-packages
                                   boymoo-compiler::data-program-symbols))))))

(local
 (defthm initial-name-payloads-are-separated-by-16-bytes
   (implies (and (integerp base)
                 (data-placed-characters-p (data-chunks-characters '("T" 257 "NIL" 769))
                                           (+ base 80) machine))
            (and (data-placed-characters-p (data-forward-chunk-characters '(769 "NIL"))
                                          (+ base 80) machine)
                 (data-placed-characters-p (data-forward-chunk-characters '(257 "T"))
                                           (+ base 96) machine)))
   :hints (("Goal" :use ((:instance data-placed-characters-of-append
                                    (first (data-forward-chunk-characters '(769 "NIL")))
                                    (second (data-forward-chunk-characters '(257 "T")))
                                    (address (+ base 80))))
                   :in-theory (disable data-placed-characters-of-append)))))

(defthmd data-build-loads-builtin-name-fields
  (let ((name (data-builtin-name truth)) (address (+ base (if truth 96 80))))
    (implies (and (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
                  (data-program-storage-input-p lines)
                  (boymoo-compiler::index-get
                   "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil))
                  (integerp base))
             (and (equal (proof-load-word address machine) (+ 1 (* 256 (length name))))
                  (equal (proof-load-string (length name) (+ 8 address) machine) name))))
  :hints (("Goal" :use (data-build-places-initial-name-chunks
                        initial-name-payloads-are-separated-by-16-bytes
                        (:instance data-placed-string-allocation-loads-fields
                                   (string "NIL") (address (+ base 80)))
                        (:instance data-placed-string-allocation-loads-fields
                                   (string "T") (address (+ base 96))))
                  :in-theory (disable data-placed-characters-of-append
                                      data-program-storage-input-p boymoo-compiler::data-package-numbers
                                      boymoo-compiler::index-get))))

(local
 (defthm initial-symbol-header-chunks
   (let* ((header (car (data-image-parts lines package-lines)))
          (number (mv-nth 0 (data-before-buckets lines package-lines)))
          (index (if truth 7 4)))
     (implies number
              (and (equal (nth index header) 4098)
                   (equal (nth (1+ index) header) (data-builtin-name-word truth))
                   (equal (nth (+ 2 index) header) (+ 1 (* 2 number))))))
   :hints (("Goal" :in-theory (e/d (data-image-parts)
                                  (boymoo-compiler::data-bucket-vector))))))

(defthmd data-build-loads-builtin-symbol-fields
  (let* ((number (mv-nth 0 (data-before-buckets lines package-lines)))
         (address (+ base (if truth 56 32))))
    (implies (and (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
                  (natp number) (proof-immediate-integer-p number) (integerp base))
             (and (equal (proof-load-word address machine) 4098)
                  (equal (proof-load-word (+ 8 address) machine) (data-builtin-name-word truth))
                  (equal (proof-load-word (+ 16 address) machine) (proof-integer-word number)))))
  :hints (("Goal" :use ((:instance data-build-loads-header-field (field (if truth 7 4)))
                        (:instance data-build-loads-header-field (field (if truth 8 5)))
                        (:instance data-build-loads-header-field (field (if truth 9 6)))
                        (:instance initial-symbol-header-chunks)
                        (:instance data-immediate-integer-twos-complement
                                   (integer (mv-nth 0 (data-before-buckets lines package-lines)))))
                  :in-theory (disable initial-symbol-header-chunks proof-integer-word))))

(defun data-builtin-symbol-records-p (truth base objects)
  (let ((symbol-address (+ base (if truth 56 32)))
        (name-address (+ base (if truth 96 80))))
    (and (equal (assoc-equal symbol-address objects)
                (proof-object symbol-address :static :header (if truth 13 11)))
         (equal (assoc-equal name-address objects)
                (proof-object name-address :static :header (if truth 12 10))))))

(local
 (defthm common-lisp-witness-resolves-nil-and-t
   (implies (and (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP"))
            (equal (intern-in-package-of-symbol (data-builtin-name truth) witness)
                   (if truth t nil)))
   :hints (("Goal" :use ((:instance acl2::intern-in-package-of-symbol-symbol-name
                                    (acl2::x (if truth t nil)) (acl2::y witness)))
                   :in-theory (disable acl2::intern-in-package-of-symbol-symbol-name)))))

(local
 (defthm initial-symbol-word-points-at-header
   (implies (proof-span-p base 112)
            (and (unsigned-byte-p 64 (data-builtin-symbol-word truth))
                 (not (oddp (data-builtin-symbol-word truth)))
                 (equal (proof-word-tag (data-builtin-symbol-word truth)) 2)
                 (equal (proof-pointer-address (data-builtin-symbol-word truth) base)
                        (+ base (if truth 56 32)))))
   :hints (("Goal" :use ((:instance data-static-reference-fits-and-points-at-offset
                                    (slot (if truth 7 4)) (tag 2) (size 112)))))))

(local
 (defthm initial-name-word-points-at-header
   (implies (proof-span-p base 112)
            (and (unsigned-byte-p 64 (data-builtin-name-word truth))
                 (not (oddp (data-builtin-name-word truth)))
                 (equal (proof-word-tag (data-builtin-name-word truth)) 2)
                 (equal (proof-pointer-address (data-builtin-name-word truth) base)
                        (+ base (if truth 96 80)))))
   :hints (("Goal" :use ((:instance data-static-reference-fits-and-points-at-offset
                                    (slot (if truth 12 10)) (tag 2) (size 112)))))))

(local
 (defthm builtin-name-is-the-earlier-child
   (let ((word (data-builtin-name-word truth)) (name (data-builtin-name truth)))
     (implies (and (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
                   (proof-span-p base 112) (data-program-storage-input-p lines)
                   (natp (mv-nth 0 (data-before-buckets lines package-lines)))
                   (data-builtin-symbol-records-p truth base objects))
              (data-child-value-p word name (if truth 13 11) base objects packages machine)))
   :rule-classes nil
   :hints (("Goal" :use (data-build-loads-builtin-name-fields initial-name-word-points-at-header
                         common-lisp-number-is-the-package-lookup
                         (:instance data-view-of-static-string-fields
                                    (word (data-builtin-name-word truth)) (string (data-builtin-name truth))))
                   :in-theory (disable data-program-storage-input-p boymoo-compiler::index-get
                                       boymoo-compiler::data-package-numbers
                                       initial-name-word-points-at-header)))))

(local
 (defthm visible-immediate-number-is-a-child-value
   (implies (and (proof-immediate-integer-p number) (posp rank))
            (data-child-value-p (proof-integer-word number) number rank base objects packages machine))
   :hints (("Goal" :use ((:instance data-view-of-immediate-integer (integer number)))
                   :in-theory (disable proof-immediate-integer-p proof-integer-word)))))

(local
 (defthm builtin-two-fields-denote-the-source-symbol
   (let* ((package (nth number packages)) (witness (proof-package-witness package)))
     (implies (and (natp number) (proof-immediate-integer-p number) (< number (len packages))
                   (equal (proof-package-name package) "COMMON-LISP")
                   (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP"))
              (equal (data-two-field-view 2 (data-builtin-name truth) number packages)
                     (proof-value-view (if truth t nil)))))
   :hints (("Goal" :use ((:instance common-lisp-witness-resolves-nil-and-t
                                    (witness (proof-package-witness (nth number packages)))))
                   :in-theory (disable common-lisp-witness-resolves-nil-and-t proof-immediate-integer-p)))))

(defthmd data-build-view-of-builtin-symbol
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (number (mv-nth 0 (data-before-buckets lines package-lines)))
         (package (nth number packages))
         (witness (proof-package-witness package)))
    (implies (and (proof-image-at-p image base machine) (proof-span-p base 112)
                  (data-program-storage-input-p lines) (natp number) (proof-immediate-integer-p number)
                  (< number (len packages)) (equal (proof-package-name package) "COMMON-LISP")
                  (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP")
                  (data-builtin-symbol-records-p truth base objects))
             (proof-value-p (data-builtin-symbol-word truth) (if truth t nil) base objects packages machine)))
  :hints (("Goal" :use (builtin-name-is-the-earlier-child data-build-loads-builtin-symbol-fields
                        initial-symbol-word-points-at-header
                        (:instance visible-immediate-number-is-a-child-value
                                   (number (mv-nth 0 (data-before-buckets lines package-lines)))
                                   (rank (if truth 13 11)))
                        (:instance builtin-two-fields-denote-the-source-symbol
                                   (number (mv-nth 0 (data-before-buckets lines package-lines))))
                        (:instance data-view-of-static-two-field-header
                                   (type 2) (word (data-builtin-symbol-word truth))
                                   (first (data-builtin-name truth))
                                   (second (mv-nth 0 (data-before-buckets lines package-lines)))))
                  :in-theory (e/d (proof-value-p)
                                 (data-program-storage-input-p proof-immediate-integer-p proof-integer-word
                                  data-child-value-p data-two-field-view visible-immediate-number-is-a-child-value
                                  builtin-two-fields-denote-the-source-symbol
                                  boymoo-compiler::index-get boymoo-compiler::data-package-numbers
                                  initial-symbol-word-points-at-header initial-name-word-points-at-header)))))
