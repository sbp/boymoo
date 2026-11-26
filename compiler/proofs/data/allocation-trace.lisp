(in-package "BOYMOO-PROOFS")

(include-book "list-images")
(include-book "boxed")
(include-book "rows")

(logic)
(set-verify-guards-eagerness 0)

; A cons allocation has two word chunks. A string has a byte count,
; and other headers have a sequence of word chunks as their payload.
(defun data-allocation-chunks (allocation)
  (case (car allocation)
    (:cons (cdr allocation))
    (:string (let ((string (cadr allocation)))
               (list (+ 1 (* 256 (length string))) string)))
    (otherwise (cons (+ (cadr allocation) (* 2048 (len (cddr allocation)))) (cddr allocation)))))

(defun data-allocation-size (allocation)
  (data-chunks-size (data-allocation-chunks allocation)))

(defun data-allocation-trace-chunks (trace)
  (if (atom trace)
      nil
    (append (data-allocation-chunks (car trace)) (data-allocation-trace-chunks (cdr trace)))))

(defun data-allocation-trace-block (trace block)
  (let ((chunks (data-allocation-trace-chunks trace)))
    (cons (+ (car block) (data-chunks-size chunks)) (boymoo-compiler::reverse-onto chunks (cdr block)))))

(local
 (in-theory (disable data-chunk-size boymoo-compiler::aligned-size ash length)))

(local
 (defthm sum-of-consecutive-chunk-sizes
   (equal (data-chunks-size (append first second))
          (+ (data-chunks-size first) (data-chunks-size second)))))

(local
 (defthm reversed-chunks-combine-in-allocation-order
   (equal (boymoo-compiler::reverse-onto (append first second) tail)
          (boymoo-compiler::reverse-onto second (boymoo-compiler::reverse-onto first tail)))))

(local
 (defthm joining-traces-joins-their-chunks
   (equal (data-allocation-trace-chunks (append first second))
          (append (data-allocation-trace-chunks first) (data-allocation-trace-chunks second)))))

(defthmd data-following-allocation-traces-appends-their-objects
  (equal (data-allocation-trace-block second (data-allocation-trace-block first block))
         (data-allocation-trace-block (append first second) block)))

(defthm data-empty-allocation-trace-keeps-the-block
  (implies (and (consp block) (integerp (car block)))
           (equal (data-allocation-trace-block nil block) block)))

(local
 (defthm reversing-chunks-preserves-the-size-increment
   (equal (data-chunks-size (boymoo-compiler::reverse-onto chunks tail))
          (+ (data-chunks-size chunks) (data-chunks-size tail)))))

(defthm data-allocation-trace-preserves-sized-blocks
  (implies (data-block-sized-p block start)
           (data-block-sized-p (data-allocation-trace-block trace block) start)))

(defthm data-cons-allocation-trace-counts-its-first-object
  (equal (data-chunks-size (data-allocation-trace-chunks (cons allocation rest)))
         (+ (data-allocation-size allocation) (data-chunks-size (data-allocation-trace-chunks rest)))))

(defthmd data-cons-allocation-trace-is-the-cell-block
  (implies (and (not (stringp first)) (not (stringp rest)))
           (equal (mv-nth 1 (boymoo-compiler::data-cell first rest block))
                  (data-allocation-trace-block (list (list :cons first rest)) block)))
  :hints (("Goal" :in-theory (enable data-chunk-size))))

(defthmd data-string-allocation-trace-is-the-text-block
  (implies (stringp string)
           (equal (mv-nth 1 (boymoo-compiler::data-text 1 string block))
                  (data-allocation-trace-block (list (list :string string)) block)))
  :hints (("Goal" :in-theory (e/d (data-chunk-size data-ash-left) (ash)))))

(defthmd data-two-field-allocation-trace-is-the-fields-block
  (implies (and (not (stringp first)) (not (stringp second)))
           (equal (mv-nth 1 (boymoo-compiler::data-fields type first second block))
                  (data-allocation-trace-block (list (list :header type first second)) block)))
  :hints (("Goal" :in-theory (enable data-chunk-size))))

(defthmd data-vector-allocation-trace-is-the-vector-block
  (implies (and (data-word-chunks-p words) (true-listp words) (integerp (car block)))
           (equal (mv-nth 1 (boymoo-compiler::data-vector words block))
                  (data-allocation-trace-block (list (list* :header 6 words)) block)))
  :hints (("Goal" :use (data-vector-allocates-header-and-fields)
                  :in-theory (e/d (data-chunk-size) (boymoo-compiler::data-vector)))))

(defun data-list-cell-allocation-trace (words tail offset)
  (if (atom words)
      nil
    (cons (list :cons (car words) tail)
          (data-list-cell-allocation-trace (cdr words) offset (+ 16 offset)))))

(defthm data-list-cell-trace-chunks-are-the-pair-chunks
  (equal (data-allocation-trace-chunks (data-list-cell-allocation-trace words tail offset))
         (data-forward-list-cell-chunks words tail offset)))

(local
 (defthm list-cells-allocate-from-a-cons-block
   (implies (consp block) (consp (mv-nth 1 (boymoo-compiler::data-list-cells words tail block))))))

(local
 (defthm list-cell-trace-consumes-one-pair-per-word
   (implies (and (data-word-chunks-p words) (not (stringp tail)) (integerp offset))
            (equal (data-chunks-size (data-forward-list-cell-chunks words tail offset)) (* 16 (len words))))
   :hints (("Goal" :induct (data-forward-list-cell-chunks words tail offset)
                   :in-theory (enable data-chunk-size)))))

(defthmd data-list-cell-allocation-trace-is-the-list-block
  (implies (and (integerp (car block)) (data-word-chunks-p words) (not (stringp tail)) (consp block))
           (equal (mv-nth 1 (boymoo-compiler::data-list-cells words tail block))
                  (data-allocation-trace-block (data-list-cell-allocation-trace words tail (car block)) block)))
  :hints (("Goal" :use ((:instance data-list-cells-allocate-consecutive-pairs (reversed words))
                        (:instance data-list-cell-chunks-match-forward-allocation-order
                                   (offset (car block)) (prior (cdr block))))
                  :in-theory (disable boymoo-compiler::data-list-cells data-list-cell-allocation-trace
                                      data-forward-list-cell-chunks data-list-cell-chunks
                                      boymoo-compiler::reverse-onto))))

(local
 (defthm limb-writer-produces-only-word-chunks
   (implies (and (not (stringp magnitude)) (data-word-chunks-p tail))
            (data-word-chunks-p (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)))
   :hints (("Goal" :induct (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)
                   :in-theory (disable boymoo-compiler::low-bits)))))

(local
 (defthm boxed-limbs-are-word-chunks
   (implies (integerp value) (data-word-chunks-p (data-boxed-integer-limbs value width)))))

(defun data-integer-allocation-trace (value width)
  (if (and (<= -4611686018427387904 value) (< value 4611686018427387904))
      nil
    (list (list* :header 3 (if (< value 0) 1 0) (data-boxed-integer-limbs value width)))))

(defthmd data-integer-allocation-trace-is-the-written-block
  (implies (and (integerp value) (integerp (car block)) (consp block))
           (equal (mv-nth 1 (boymoo-compiler::data-write-integer value width block))
                  (data-allocation-trace-block (data-integer-allocation-trace value width) block)))
  :hints (("Goal" :use ((:instance data-write-boxed-integer-allocates-fields (text-length width))
                        (:instance data-serialized-immediate-integer (integer value) (text-length width)))
                  :in-theory (e/d (data-chunk-size)
                                 (boymoo-compiler::data-write-integer data-boxed-integer-limbs)))))

(defun data-bucket-insertion-trace (package name name-word symbol-word state-data)
  (let* ((start (car (boymoo-compiler::data-block state-data)))
         (old (boymoo-compiler::bucket-get (data-bucket-for-name package name) 12 (caddr state-data))))
    (list (list :cons (+ 1 (* 2 package)) name-word)
          (list :cons start symbol-word)
          (list :cons (+ start 16) old))))

(local
 (defthm bucket-head-is-a-word-chunk
   (implies (data-static-bucket-tree-p tree bits)
            (not (stringp (boymoo-compiler::bucket-get bucket bits tree))))))

(defthmd data-bucket-insertion-trace-is-the-published-block
  (implies (and (natp (car (boymoo-compiler::data-block state-data)))
                (data-state-buckets-p state-data) (not (stringp name-word)) (not (stringp symbol-word)))
           (equal (boymoo-compiler::data-block
                   (boymoo-compiler::data-bucket-add package name name-word symbol-word state-data))
                  (data-allocation-trace-block (data-bucket-insertion-trace package name name-word symbol-word state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :use (data-bucket-add-publishes-three-cells)
                  :in-theory (e/d (data-chunk-size) (boymoo-compiler::data-bucket-add
                                                   boymoo-compiler::bucket-get data-static-bucket-tree-p)))))
