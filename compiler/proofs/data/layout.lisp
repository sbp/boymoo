(in-package "BOYMOO-PROOFS")

(include-book "serialization")

(logic)
(set-verify-guards-eagerness 0)

; A block's chunks are written from the offset at which its allocation began.
(defun data-block-sized-p (block start)
  (and (consp block) (natp start)
       (equal (car block) (+ start (data-chunks-size (cdr block))))))

(local
 (in-theory (disable boymoo-compiler::aligned-size)))

(defthm data-block-sized-p-of-word
  (implies (and (data-block-sized-p block start) (not (stringp word)))
           (data-block-sized-p (boymoo-compiler::data-word word block) start)))

(defthm data-block-sized-p-of-text
  (implies (and (data-block-sized-p block start) (stringp text))
           (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-text type text block)) start))
  :hints (("Goal" :in-theory (disable ash))))

(defthm data-block-sized-p-of-cell
  (implies (and (data-block-sized-p block start) (not (stringp a)) (not (stringp d)))
           (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-cell a d block)) start))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-word data-block-sized-p))))

(defthm data-block-sized-p-of-fields
  (implies (and (data-block-sized-p block start) (not (stringp a)) (not (stringp b)))
           (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-fields type a b block)) start))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-word data-block-sized-p))))

(defthm data-block-sized-p-of-words
  (implies (and (data-block-sized-p block start) (data-word-chunks-p words))
           (data-block-sized-p (boymoo-compiler::data-words words block) start))
  :hints (("Goal" :induct (boymoo-compiler::data-words words block)
                  :in-theory (disable boymoo-compiler::data-word data-block-sized-p))))

(defthmd data-words-allocate-consecutively
  (implies (integerp (car block))
           (equal (boymoo-compiler::data-words words block)
                  (cons (+ (car block) (* 8 (len words)))
                        (boymoo-compiler::reverse-onto words (cdr block)))))
  :hints (("Goal" :induct (boymoo-compiler::data-words words block))))

(defthm data-block-sized-p-of-vector
  (implies (and (data-block-sized-p block start) (data-word-chunks-p words))
           (data-block-sized-p (mv-nth 1 (boymoo-compiler::data-vector words block)) start))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-word
                                      boymoo-compiler::data-words data-block-sized-p))))

(defun data-static-header-words (size package-word bucket-word common-lisp)
  (let ((tagged-package (+ 1 (* 2 common-lisp))))
    (list size package-word bucket-word *proof-nil*
          4098 82 tagged-package 4098 98 tagged-package)))

(local
 (defthm names-from-data-initial
   (and (equal (mv-nth 0 (boymoo-compiler::data-initial package)) 82)
        (equal (mv-nth 1 (boymoo-compiler::data-initial package)) 98))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-bucket-add
                                       boymoo-compiler::table-put
                                       boymoo-compiler::index-set)))))

(local
 (defthm package-vector-word-is-not-a-string
   (not (stringp (car (boymoo-compiler::data-package-vectors
                        names packages declarations state-data reversed))))
   :hints (("Goal" :induct (boymoo-compiler::data-package-vectors
                            names packages declarations state-data reversed)
                   :in-theory (disable boymoo-compiler::data-intern
                                       boymoo-compiler::data-text
                                       boymoo-compiler::data-with-block
                                       boymoo-compiler::data-words)))))

(local
 (defthm package-table-word-is-not-a-string
   (not (stringp (car (boymoo-compiler::data-packages
                        lines number packages state-data reversed))))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-package-vectors
                                       boymoo-compiler::data-package-declarations)))))

(local
 (defthm bucket-vector-end-is-not-a-string
   (implies (not (stringp (car block)))
            (not (stringp (car (boymoo-compiler::data-bucket-vector tree bits block)))))
   :hints (("Goal" :induct (boymoo-compiler::data-bucket-vector tree bits block)))))

; The remaining allocation after this state is the bucket vector.
(defun data-before-buckets (lines package-lines)
  (let* ((package-index (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (common-lisp (boymoo-compiler::index-get "COMMON-LISP" package-index)))
    (if (not common-lisp)
        (mv nil nil nil)
      (mv-let (nil-name t-name state-data)
        (boymoo-compiler::data-initial common-lisp)
        (declare (ignore nil-name t-name))
        (mv-let (package-word state-data)
          (boymoo-compiler::data-packages package-lines 0 package-index state-data nil)
          (mv common-lisp package-word
              (boymoo-compiler::data-program-symbols lines package-index state-data)))))))

; With a heap limit, an odd word holding it follows the bucket vector.
(defun data-heap-limit-block (limit block)
  (if limit (boymoo-compiler::data-word (+ 1 (* 2 limit)) block) block))

(defthm data-block-sized-p-of-heap-limit-block
  (implies (data-block-sized-p block start)
           (data-block-sized-p (data-heap-limit-block limit block) start)))

(defthm data-heap-limit-block-without-a-limit
  (equal (data-heap-limit-block nil block) block))

(defthm heap-limit-block-end-is-not-a-string
  (implies (not (stringp (car block)))
           (not (stringp (car (data-heap-limit-block limit block))))))

(in-theory (disable data-heap-limit-block))

; The image is split into its fixed header and the allocation chunks.
(defun data-image-parts (lines package-lines)
  (mv-let (common-lisp package-word state-data) (data-before-buckets lines package-lines)
    (if (not common-lisp)
        (mv nil nil nil)
      (let* ((block (boymoo-compiler::data-block state-data))
             (bucket-word (+ 2 (car block)))
             (block (boymoo-compiler::data-bucket-vector
                     (caddr state-data) 12 (boymoo-compiler::data-word 8388614 block)))
             (block (data-heap-limit-block (boymoo-compiler::data-heap-limit lines nil) block)))
        (mv (data-static-header-words (car block) package-word bucket-word common-lisp)
            (cdr block) (cadr state-data))))))

(local
 (in-theory (disable boymoo-compiler::data-initial boymoo-compiler::data-package-numbers
                     boymoo-compiler::data-packages boymoo-compiler::data-program-symbols
                     boymoo-compiler::data-bucket-vector boymoo-compiler::index-get
                     boymoo-compiler::data-write boymoo-compiler::data-heap-limit)))

(defthmd data-build-image-and-index
  (mv-let (header reversed index) (data-image-parts lines package-lines)
    (and (equal (car (boymoo-compiler::data-build lines package-lines))
                (and header
                     (cons (car header)
                           (boymoo-compiler::data-write
                            (boymoo-compiler::reverse-onto header nil)
                            (boymoo-compiler::data-write reversed nil)))))
         (equal (mv-nth 1 (boymoo-compiler::data-build lines package-lines)) index)))
  :hints (("Goal" :in-theory (enable data-heap-limit-block))))

; Later books treat the heap limit through the theorems about it.
(in-theory (disable boymoo-compiler::data-heap-limit))

(defthm data-image-header-has-ten-words
  (let ((header (car (data-image-parts lines package-lines))))
    (implies header (and (consp header) (equal (len header) 10) (data-word-chunks-p header)))))

(defthm data-image-header-initial-root-field
  (let ((header (car (data-image-parts lines package-lines))))
    (implies header (equal (nth 3 header) *proof-nil*))))

(defthmd data-build-fragment-count-agreement
  (mv-let (header reversed index) (data-image-parts lines package-lines)
    (declare (ignore index))
    (let ((image (car (boymoo-compiler::data-build lines package-lines))))
      (implies header
               (and (proof-fragments-p (cdr image))
                    (equal (proof-fragments-size (cdr image)) (+ 80 (data-chunks-size reversed)))
                    (equal (car image) (car header))))))
  :hints (("Goal" :in-theory (e/d (data-build-image-and-index)
                                 (data-image-parts boymoo-compiler::data-build
                                  boymoo-compiler::reverse-onto data-write-short-word-chunks)))))

(defthmd data-build-header-fragment
  (mv-let (header reversed index) (data-image-parts lines package-lines)
    (declare (ignore index))
    (implies header
             (equal (cdr (car (boymoo-compiler::data-build lines package-lines)))
                    (cons (coerce (data-forward-chunk-characters header) 'string)
                          (boymoo-compiler::data-write reversed nil)))))
  :hints (("Goal" :in-theory (e/d (data-build-image-and-index)
                                 (data-image-parts boymoo-compiler::data-build
                                  boymoo-compiler::reverse-onto data-write-short-word-chunks)))))
