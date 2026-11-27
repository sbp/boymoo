(in-package "BOYMOO-PROOFS")

(include-book "program-allocation-trace")
(include-book "package-allocation-trace")
(include-book "allocation-map")

(logic)
(set-verify-guards-eagerness 0)

(defun data-initial-allocation-trace (common-lisp)
  (let* ((package (+ 1 (* 2 common-lisp)))
         (nil-bucket (data-bucket-for-name common-lisp "NIL"))
         (t-bucket (data-bucket-for-name common-lisp "T"))
         (t-tail (boymoo-compiler::bucket-get t-bucket 12 (boymoo-compiler::bucket-set nil-bucket 12 144 nil))))
    (list (list :string "NIL") (list :string "T")
          (list :cons package 82) (list :cons 112 34) (list :cons 128 34)
          (list :cons package 98) (list :cons 160 58) (list :cons 176 t-tail))))

(local
 (defthm empty-static-bucket-is-nil
   (equal (boymoo-compiler::bucket-get bucket bits nil) 34)))

(local
 (defthm bucket-head-is-never-a-string-for-an-empty-tree-with-one-entry
   (implies (and (natp bits) (not (stringp word)))
            (not (stringp (boymoo-compiler::bucket-get query bits (boymoo-compiler::bucket-set key bits word nil)))))
   :hints (("Goal" :use ((:instance data-bucket-lookup-after-set (tree nil) (bucket key)))
                   :in-theory (disable boymoo-compiler::bucket-get boymoo-compiler::bucket-set)))))

(defthmd data-initial-allocation-trace-is-the-initial-block
  (equal (boymoo-compiler::data-block (mv-nth 2 (boymoo-compiler::data-initial common-lisp)))
         (data-allocation-trace-block (data-initial-allocation-trace common-lisp) '(80)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::text-hash boymoo-compiler::low-bits
                                      boymoo-compiler::table-put boymoo-compiler::index-set
                                      boymoo-compiler::bucket-get boymoo-compiler::bucket-set))))

(local
 (in-theory (disable boymoo-compiler::data-initial data-initial-allocation-trace
                     boymoo-compiler::index-get boymoo-compiler::data-package-numbers
                     boymoo-compiler::data-packages data-packages-allocation-trace
                     boymoo-compiler::data-program-symbols data-program-allocation-trace
                     data-ascending-bucket-words boymoo-compiler::data-bucket-vector)))

(defun data-build-body-allocation-trace (lines package-lines)
  (let* ((packages (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (common-lisp (boymoo-compiler::index-get "COMMON-LISP" packages)))
    (if (not common-lisp)
        nil
      (mv-let (nil-name t-name initial) (boymoo-compiler::data-initial common-lisp)
        (declare (ignore nil-name t-name))
        (mv-let (package-word named) (boymoo-compiler::data-packages package-lines 0 packages initial nil)
          (declare (ignore package-word))
          (let ((program (boymoo-compiler::data-program-symbols lines packages named)))
            (append (data-initial-allocation-trace common-lisp)
                    (data-packages-allocation-trace package-lines packages initial nil)
                    (data-program-allocation-trace lines packages named)
                    (list (list* :header 6 (data-ascending-bucket-words (caddr program) 12))))))))))

(local
 (defthm ascending-bucket-words-form-a-list
   (true-listp (data-ascending-bucket-words tree bits))
   :hints (("Goal" :in-theory (enable data-ascending-bucket-words)))))

(local
 (defthm bucket-slot-vector-has-4096-fields
   (equal (len (data-ascending-bucket-words tree 12)) 4096)
   :hints (("Goal" :use ((:instance data-bucket-vector-contains-one-word-per-path (bits 12)))))))

(local
 (defthm last-bucket-allocation-trace-is-the-bucket-vector
   (implies (and (integerp (car block)) (data-static-bucket-tree-p tree 12))
            (equal (boymoo-compiler::data-bucket-vector tree 12 (boymoo-compiler::data-word 8388614 block))
                   (data-allocation-trace-block (list (list* :header 6 (data-ascending-bucket-words tree 12))) block)))
   :hints (("Goal" :use ((:instance data-vector-allocation-trace-is-the-vector-block
                                    (words (data-ascending-bucket-words tree 12))))
                   :in-theory (e/d (data-bucket-vector-serializes-ascending-leaves)
                                   (boymoo-compiler::data-words data-allocation-trace-block ash))))))

(local
 (defthm joining-traces-associates-with-bucket-trace
   (equal (append (append first second) rest) (append first second rest))))

(local
 (defthm block-of-a-sized-state-in-the-builder-is-integer
   (implies (data-state-sized-p state-data 80)
            (integerp (car (boymoo-compiler::data-block state-data))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-state-sized-p data-block-sized-p)))))

(local
 (defthm integer-block-offset-survives-adding-a-trace
   (implies (integerp (car block)) (integerp (car (data-allocation-trace-block trace block))))))

(local
 (in-theory (disable data-allocation-trace-block data-state-sized-p data-block-sized-p
                     boymoo-compiler::data-block boymoo-compiler::data-vector boymoo-compiler::data-word
                     data-program-storage-input-p data-package-lines-storage-input-p data-static-bucket-tree-p)))

(defthmd data-build-body-trace-agrees-with-image-parts
  (let ((body (data-allocation-trace-block (data-build-body-allocation-trace lines package-lines) '(80))))
    (implies (and (mv-nth 0 (data-before-buckets lines package-lines))
                  (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines))
             (and (equal (mv-nth 1 (data-image-parts lines package-lines)) (cdr body))
                  (equal (car (mv-nth 0 (data-image-parts lines package-lines))) (car body)))))
  :hints (("Goal" :use (data-build-body-has-bucket-tree data-build-body-is-sized-for-storage-input)
                  :in-theory (e/d (data-initial-allocation-trace-is-the-initial-block
                                  data-packages-allocation-trace-is-the-package-block
                                  data-program-allocation-trace-is-the-program-block
                                  data-following-allocation-traces-appends-their-objects)
                                 (data-build-body-has-bucket-tree)))))

; The first four header words precede the two fixed symbol objects.
(defun data-build-allocation-trace (lines package-lines)
  (mv-let (common-lisp package-word state-data) (data-before-buckets lines package-lines)
    (declare (ignore package-word state-data))
    (if (not common-lisp)
        nil
      (let ((package (+ 1 (* 2 common-lisp))))
        (list* (list :header 2 82 package) (list :header 2 98 package)
               (data-build-body-allocation-trace lines package-lines))))))

(local
 (in-theory (disable data-build-body-allocation-trace boymoo-compiler::data-build
                     boymoo-compiler::data-write boymoo-compiler::reverse-onto
                     data-chunks-characters data-forward-chunk-characters data-chunks-size)))

(local
 (defthm joining-forward-chunks-concatenates-their-bytes
   (equal (data-forward-chunk-characters (append first rest))
          (append (data-forward-chunk-characters first) (data-forward-chunk-characters rest)))
   :hints (("Goal" :in-theory (enable data-forward-chunk-characters)))))

(local
 (defthm forward-bytes-are-a-true-list
   (true-listp (data-forward-chunk-characters chunks))
   :hints (("Goal" :use data-forward-chunk-characters-are-characters))))

(local
 (defthm reversed-bytes-are-a-true-list
   (true-listp (data-chunks-characters chunks))
   :hints (("Goal" :use data-chunks-characters-are-characters))))

(local
 (defthm prefix-of-word-chunks-contains-only-word-chunks
   (implies (data-word-chunks-p chunks) (data-word-chunks-p (take count chunks)))
   :hints (("Goal" :induct (take count chunks)))))

(local
 (defthm word-chunk-prefix-has-requested-length
   (implies (natp count) (equal (len (take count chunks)) count))
   :hints (("Goal" :induct (take count chunks)))))

(local
 (defthm first-four-header-words-occupy-32-bytes
   (implies (car (data-image-parts lines package-lines))
            (equal (len (data-forward-chunk-characters (take 4 (car (data-image-parts lines package-lines)))))
                   32))
   :hints (("Goal" :use data-image-header-has-ten-words
                   :in-theory (disable data-image-header-has-ten-words data-image-parts take)))))

(local
 (defthm emitted-image-characters-are-header-and-body
   (let* ((parts (data-image-parts lines package-lines)) (image (car (boymoo-compiler::data-build lines package-lines))))
     (implies (car parts)
              (equal (data-fragment-characters (cdr image))
                     (append (data-forward-chunk-characters (car parts)) (data-chunks-characters (mv-nth 1 parts))))))
   :hints (("Goal" :in-theory (e/d (data-build-image-and-index)
                                   (data-image-parts data-write-short-word-chunks))))))

(local
 (defthm trace-body-chunks-come-after-the-fixed-symbols
   (let* ((header (car (data-image-parts lines package-lines)))
          (body (data-allocation-trace-chunks (data-build-body-allocation-trace lines package-lines)))
          (trace (data-build-allocation-trace lines package-lines)))
     (implies (mv-nth 0 (data-before-buckets lines package-lines))
              (equal (append header body) (append (take 4 header) (data-allocation-trace-chunks trace)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable data-before-buckets
                                       boymoo-compiler::data-bucket-add boymoo-compiler::data-words)))))

(local
 (in-theory (disable data-image-parts data-before-buckets data-build-allocation-trace
                     data-allocation-trace-chunks take)))

(local
 (defthm trace-body-bytes-come-after-the-fixed-symbols
   (let* ((header (car (data-image-parts lines package-lines)))
          (body (data-allocation-trace-chunks (data-build-body-allocation-trace lines package-lines)))
          (trace (data-build-allocation-trace lines package-lines)))
     (implies (mv-nth 0 (data-before-buckets lines package-lines))
              (equal (append (data-forward-chunk-characters header) (data-forward-chunk-characters body))
                     (append (data-forward-chunk-characters (take 4 header))
                             (data-forward-chunk-characters (data-allocation-trace-chunks trace))))))
   :rule-classes nil
   :hints (("Goal" :use (trace-body-chunks-come-after-the-fixed-symbols
                         (:instance (:theorem (implies (equal first rest)
                                                        (equal (data-forward-chunk-characters first)
                                                               (data-forward-chunk-characters rest))))
                                    (first (append (car (data-image-parts lines package-lines))
                                                   (data-allocation-trace-chunks
                                                    (data-build-body-allocation-trace lines package-lines))))
                                    (rest (append (take 4 (car (data-image-parts lines package-lines)))
                                                  (data-allocation-trace-chunks
                                                   (data-build-allocation-trace lines package-lines))))))))))

(defthmd data-build-fragments-serialize-allocation-trace
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (prefix (take 4 (car (data-image-parts lines package-lines))))
         (trace (data-build-allocation-trace lines package-lines)))
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (mv-nth 0 (data-before-buckets lines package-lines)))
             (equal (data-fragment-characters (cdr image))
                    (append (data-forward-chunk-characters prefix)
                            (data-forward-chunk-characters (data-allocation-trace-chunks trace))))))
  :hints (("Goal" :use (data-build-body-trace-agrees-with-image-parts
                        emitted-image-characters-are-header-and-body trace-body-bytes-come-after-the-fixed-symbols)
                  :in-theory (enable data-allocation-trace-block))))

(local
 (defthm joined-byte-count-is-the-sum
   (equal (len (append first rest)) (+ (len first) (len rest)))))

(defthmd data-build-places-allocation-trace-at-offset-32
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (trace (data-build-allocation-trace lines package-lines))
         (chunks (data-allocation-trace-chunks trace)))
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (mv-nth 0 (data-before-buckets lines package-lines))
                  (proof-image-at-p image base machine))
             (and (equal (car image) (+ 32 (data-chunks-size chunks)))
                  (data-placed-characters-p (data-forward-chunk-characters chunks) (+ base 32) machine))))
  :hints (("Goal" :use (data-image-produced-by-data-build-has-header
                        (:instance data-fragment-characters-size
                                   (fragments (cdr (car (boymoo-compiler::data-build lines package-lines)))))
                        (:instance data-placed-fragments-agree-with-flattened-bytes
                                   (fragments (cdr (car (boymoo-compiler::data-build lines package-lines))))
                                   (address base)))
                  :in-theory (e/d (data-build-fragments-serialize-allocation-trace)
                                 (proof-fragments-size proof-fragments-p proof-fragments-at-p
                                  data-image-produced-by-data-build-has-header data-fragment-characters-size
                                  emitted-image-characters-are-header-and-body
                                  data-placed-characters-p data-fragment-characters)))))
