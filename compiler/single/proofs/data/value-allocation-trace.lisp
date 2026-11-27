(in-package "BOYMOO-PROOFS")

(include-book "allocation-trace")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable char length subseq ash data-block-sized-p data-state-sized-p
                     data-allocation-trace-block mv-nth
                     boymoo-compiler::find-char boymoo-compiler::hex-byte
                     boymoo-compiler::data-word boymoo-compiler::data-words)))

(local
 (defthm appending-traces-is-associative
   (equal (append (append first second) last) (append first second last))))

(local
 (defthm decimal-reader-returns-an-integer-or-nil
   (implies (integerp accumulator)
            (let ((value (boymoo-compiler::decimal-value text start remaining accumulator)))
              (or (not value) (integerp value))))
   :hints (("Goal" :induct (boymoo-compiler::decimal-value text start remaining accumulator)))))

(local
 (defthm integer-reader-returns-an-integer-or-nil
   (let ((value (boymoo-compiler::data-integer-value text start end))) (or (not value) (integerp value)))
   :hints (("Goal" :use ((:instance decimal-reader-returns-an-integer-or-nil
                                    (accumulator 0) (remaining (- end start)))
                         (:instance decimal-reader-returns-an-integer-or-nil
                                    (accumulator 0) (start (1+ start)) (remaining (- end (1+ start)))))
                   :in-theory (disable boymoo-compiler::decimal-value
                                       decimal-reader-returns-an-integer-or-nil)))))

(local
 (defthm block-of-sized-state-is-consp
   (implies (data-block-sized-p block 80) (consp block))
   :hints (("Goal" :in-theory (enable data-block-sized-p)))
   :rule-classes :forward-chaining))

(local
 (defthm literal-integer-allocation-trace-is-the-written-block
   (implies (data-block-sized-p block 80)
            (let ((value (boymoo-compiler::data-integer-value text start end)))
              (equal (mv-nth 1 (boymoo-compiler::data-write-integer value width block))
                     (data-allocation-trace-block (data-integer-allocation-trace value width) block))))
   :hints (("Goal" :use ((:instance data-integer-allocation-trace-is-the-written-block
                                    (value (boymoo-compiler::data-integer-value text start end)))
                         integer-reader-returns-an-integer-or-nil)
                   :in-theory (e/d (data-integer-allocation-trace)
                                   (boymoo-compiler::data-integer-value boymoo-compiler::data-write-integer
                                    integer-reader-returns-an-integer-or-nil))
                   :expand ((boymoo-compiler::data-write-integer nil width block))))))

(local
 (defthm integer-writer-reference-is-a-word-chunk
   (not (stringp (mv-nth 0 (boymoo-compiler::data-write-integer value width block))))
   :hints (("Goal" :in-theory (disable boymoo-compiler::data-integer-limbs)))))

(local
 (in-theory (disable boymoo-compiler::data-write-integer boymoo-compiler::data-integer-value
                     data-integer-allocation-trace boymoo-compiler::data-fields)))

(defun data-rational-allocation-trace (text block)
  (let* ((end (length text)) (slash (boymoo-compiler::find-char text 0 end #\/)))
    (if (not slash)
        (data-integer-allocation-trace (boymoo-compiler::data-integer-value text 0 end) end)
      (let* ((start (1+ slash)) (num (boymoo-compiler::data-integer-value text 0 slash))
             (den (boymoo-compiler::data-integer-value text start end)))
        (if (or (equal num 0) (<= den 1) (not (equal (denominator (/ num den)) den)))
            nil
          (mv-let (num-word next) (boymoo-compiler::data-write-integer num slash block)
            (mv-let (den-word last) (boymoo-compiler::data-write-integer den (- end start) next)
              (declare (ignore last))
              (append (data-integer-allocation-trace num slash)
                      (data-integer-allocation-trace den (- end start))
                      (list (list :header 4 num-word den-word))))))))))

(defthmd data-rational-allocation-trace-is-the-written-block
  (implies (data-block-sized-p block 80)
           (equal (mv-nth 1 (boymoo-compiler::data-rational text block))
                  (data-allocation-trace-block (data-rational-allocation-trace text block) block)))
  :hints (("Goal" :in-theory (enable data-two-field-allocation-trace-is-the-fields-block
                                     data-following-allocation-traces-appends-their-objects))))

(defun data-number-allocation-trace (text block)
  (if (not (equal (char text 0) #\#))
      (data-rational-allocation-trace text block)
    (let* ((end (1- (length text))) (space (boymoo-compiler::find-char text 3 (- end 3) #\Space)))
      (if (not (and space (equal (char text 1) #\C) (equal (char text 2) #\() (equal (char text end) #\))))
          nil
        (let ((real (subseq text 3 space)) (imaginary (subseq text (1+ space) end)))
          (mv-let (real-word next) (boymoo-compiler::data-rational real block)
            (mv-let (imaginary-word last) (boymoo-compiler::data-rational imaginary next)
              (declare (ignore last))
              (append (data-rational-allocation-trace real block)
                      (data-rational-allocation-trace imaginary next)
                      (and (not (equal imaginary-word '(:integer . 0)))
                           (list (list :header 5 real-word imaginary-word)))))))))))

(local
 (in-theory (disable boymoo-compiler::data-rational data-rational-allocation-trace)))

(defthmd data-number-allocation-trace-is-the-written-block
  (implies (data-block-sized-p block 80)
           (equal (mv-nth 1 (boymoo-compiler::data-number text block))
                  (data-allocation-trace-block (data-number-allocation-trace text block) block)))
  :hints (("Goal" :in-theory (enable data-rational-allocation-trace-is-the-written-block
                                     data-two-field-allocation-trace-is-the-fields-block
                                     data-following-allocation-traces-appends-their-objects))))

(local
 (in-theory (disable boymoo-compiler::data-number data-number-allocation-trace
                     boymoo-compiler::index-get boymoo-compiler::index-set boymoo-compiler::table-get
                     boymoo-compiler::table-put boymoo-compiler::text-hash boymoo-compiler::data-bucket-add
                     boymoo-compiler::data-text boymoo-compiler::aligned-size
                     boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part)))

(defun data-intern-allocation-trace (number name state-data)
  (if (data-name-table-lookup number name state-data)
      nil
    (mv-let (name-word named) (boymoo-compiler::data-text 1 name (boymoo-compiler::data-block state-data))
      (mv-let (symbol-word next) (boymoo-compiler::data-fields 2 name-word (+ 1 (* 2 number)) named)
        (list* (list :string name) (list :header 2 name-word (+ 1 (* 2 number)))
               (data-bucket-insertion-trace number name name-word symbol-word
                                            (boymoo-compiler::data-with-block next state-data)))))))

(local
 (defthm field-reference-is-a-word-chunk
   (not (stringp (mv-nth 0 (boymoo-compiler::data-fields type first second block))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-fields)))))

(local
 (defthm string-reference-is-a-word-chunk
   (not (stringp (mv-nth 0 (boymoo-compiler::data-text 1 name block))))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-text boymoo-compiler::data-word)))))

(local
 (defthm replacing-unused-name-table-keeps-bucket-trace
   (equal (data-bucket-insertion-trace number name name-word symbol-word (cons names (cdr state-data)))
          (data-bucket-insertion-trace number name name-word symbol-word state-data))))

(local
 (defthm replacing-unused-name-table-keeps-bucket-shape
   (equal (data-state-buckets-p (cons names (cdr state-data))) (data-state-buckets-p state-data))))

(local
 (defthm sized-state-keeps-a-sized-block-in-its-tail
   (implies (data-state-sized-p state-data 80)
            (and (data-block-sized-p (cdddr state-data) 80) (consp (cdddr state-data))
                 (integerp (car (cdddr state-data)))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-state-sized-p data-block-sized-p)))))

(local
 (defthm bucket-slot-determines-shape-in-a-composite-state
   (equal (data-state-buckets-p (list* names constants (caddr state-data) block))
          (data-state-buckets-p state-data))))

(local
 (defthm sized-state-offset-is-natural
   (implies (data-state-sized-p state-data 80)
            (and (consp (boymoo-compiler::data-block state-data))
                 (natp (car (boymoo-compiler::data-block state-data)))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-state-sized-p data-block-sized-p)))))

(local
 (defthm new-block-is-a-field-of-a-composite-state
   (equal (boymoo-compiler::data-block (list* names constants buckets block)) block)))

(local
 (defthm trace-block-with-natural-offset-keeps-a-natural-offset
   (implies (natp (car block))
            (and (natp (car (data-allocation-trace-block trace block)))
                 (integerp (car (data-allocation-trace-block trace block)))))
   :hints (("Goal" :in-theory (enable data-allocation-trace-block)))))

(local (in-theory (disable boymoo-compiler::data-block)))

(defthmd data-intern-allocation-trace-is-the-interned-block
  (implies (and (data-state-sized-p state-data 80) (stringp name))
           (equal (boymoo-compiler::data-block (mv-nth 2 (boymoo-compiler::data-intern number name state-data)))
                  (data-allocation-trace-block (data-intern-allocation-trace number name state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :in-theory (e/d (data-bucket-insertion-trace-is-the-published-block
                                  data-string-allocation-trace-is-the-text-block
                                  data-two-field-allocation-trace-is-the-fields-block
                                  data-following-allocation-traces-appends-their-objects)
                                 (data-state-buckets-p)))))

(local
 (in-theory (disable boymoo-compiler::data-intern data-intern-allocation-trace boymoo-compiler::decode-part)))

(local
 (defthm recording-a-constant-keeps-the-block-field
   (equal (boymoo-compiler::data-block (boymoo-compiler::data-remember text entry state-data))
          (boymoo-compiler::data-block state-data))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-block)))))

(local (in-theory (disable boymoo-compiler::data-remember)))

(defun data-symbol-allocation-trace (text packages state-data)
  (if (or (not (stringp text)) (equal (char text 0) #\") (equal (char text 0) #\#)
          (boymoo-compiler::index-get text (cadr state-data)))
      nil
    (let* ((split (boymoo-compiler::symbol-separator text))
           (number (and split (boymoo-compiler::index-get
                               (boymoo-compiler::decode-symbol-part text 0 split) packages))))
      (and number
           (data-intern-allocation-trace number (boymoo-compiler::decode-symbol-part text (+ split 2) (length text))
                                         state-data)))))

(defthmd data-symbol-allocation-trace-is-the-symbol-block
  (implies (and (data-state-sized-p state-data 80) (data-symbol-storage-input-p text))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data)))
                  (data-allocation-trace-block (data-symbol-allocation-trace text packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :in-theory (enable data-intern-allocation-trace-is-the-interned-block))))

(local
 (in-theory (disable boymoo-compiler::data-symbol data-symbol-allocation-trace)))

(defun data-atom-allocation-trace (text packages state-data)
  (if (boymoo-compiler::index-get text (cadr state-data))
      nil
    (let ((first (char text 0)))
      (cond ((and (not (equal first #\")) (not (equal first #\#)) (boymoo-compiler::symbol-separator text))
             (data-symbol-allocation-trace text packages state-data))
            ((and (equal first #\#) (equal (char text 1) #\\) (equal (length text) 4)) nil)
            ((equal first #\") (list (list :string (boymoo-compiler::decode-part text 0 (length text)))))
            (t (data-number-allocation-trace text (boymoo-compiler::data-block state-data)))))))

(defthmd data-atom-allocation-trace-is-the-atom-block
  (implies (and (data-state-sized-p state-data 80) (data-atom-storage-input-p text))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-atom text packages state-data)))
                  (data-allocation-trace-block (data-atom-allocation-trace text packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :in-theory (e/d (data-symbol-allocation-trace-is-the-symbol-block
                                  data-string-allocation-trace-is-the-text-block
                                  data-number-allocation-trace-is-the-written-block)
                                 (data-symbol-storage-input-p)))))

(local
 (in-theory (disable boymoo-compiler::data-atom data-atom-allocation-trace boymoo-compiler::data-list-cells
                     data-atom-storage-input-p data-symbol-storage-input-p data-list-cell-allocation-trace)))

(defun data-datum-allocation-trace (kind parsed packages state-data reversed)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :datum) 1 0))))
  (if (eq kind :datum)
      (if (consp parsed)
          (data-datum-allocation-trace :items parsed packages state-data nil)
        (data-atom-allocation-trace parsed packages state-data))
    (cond ((atom parsed)
           (data-list-cell-allocation-trace reversed *proof-nil* (car (boymoo-compiler::data-block state-data))))
          ((equal (car parsed) ".")
           (if (and (consp reversed) (consp (cdr parsed)) (stringp (cadr parsed)) (not (cddr parsed))
                    (not (equal (cadr parsed) boymoo-compiler::*nil-name*)))
               (mv-let (tail named) (boymoo-compiler::data-atom (cadr parsed) packages state-data)
                 (append (data-atom-allocation-trace (cadr parsed) packages state-data)
                         (data-list-cell-allocation-trace reversed tail (car (boymoo-compiler::data-block named)))))
             nil))
          (t (mv-let (entry named) (boymoo-compiler::data-datum (car parsed) packages state-data)
               (append (data-datum-allocation-trace :datum (car parsed) packages state-data nil)
                       (data-datum-allocation-trace :items (cdr parsed) packages named (cons entry reversed))))))))

(local
 (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum
                     data-datum-storage-input-p data-datum-allocation-trace)))

(local
 (defthm datum-and-list-allocations-match-the-trace
   (implies (and (data-state-sized-p state-data 80) (data-datum-storage-input-p kind parsed)
                 (data-word-chunks-p reversed))
            (equal (boymoo-compiler::data-block
                    (mv-nth 1 (if (eq kind :datum) (boymoo-compiler::data-datum parsed packages state-data)
                                (boymoo-compiler::data-list-datum parsed packages state-data reversed))))
                   (data-allocation-trace-block (data-datum-allocation-trace kind parsed packages state-data reversed)
                                                (boymoo-compiler::data-block state-data))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed)
                   :expand ((boymoo-compiler::data-datum parsed packages state-data)
                            (boymoo-compiler::data-list-datum parsed packages state-data reversed)
                            (:free (mode) (data-datum-storage-input-p mode parsed))
                            (:free (mode) (data-datum-allocation-trace mode parsed packages state-data reversed)))
                   :in-theory (enable data-atom-allocation-trace-is-the-atom-block
                                      data-list-cell-allocation-trace-is-the-list-block
                                      data-following-allocation-traces-appends-their-objects)))))

(defthmd data-datum-allocation-trace-is-the-datum-block
  (implies (and (data-state-sized-p state-data 80) (data-datum-storage-input-p :datum parsed))
           (equal (boymoo-compiler::data-block (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data)))
                  (data-allocation-trace-block (data-datum-allocation-trace :datum parsed packages state-data nil)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :use ((:instance datum-and-list-allocations-match-the-trace (kind :datum) (reversed nil))))))

(defun data-constant-allocation-trace (text packages state-data)
  (if (equal (char text 0) #\()
      (if (boymoo-compiler::index-get text (cadr state-data))
          nil
        (let ((forms (boymoo-compiler::read-lines text 0 (length text) nil nil nil (length text))))
          (data-datum-allocation-trace :datum (car forms) packages state-data nil)))
    (data-atom-allocation-trace text packages state-data)))

(defthmd data-constant-allocation-trace-is-the-constant-block
  (implies (and (data-state-sized-p state-data 80) (data-constant-storage-input-p text))
           (equal (boymoo-compiler::data-block (boymoo-compiler::data-constant text packages state-data))
                  (data-allocation-trace-block (data-constant-allocation-trace text packages state-data)
                                               (boymoo-compiler::data-block state-data))))
  :hints (("Goal" :in-theory (e/d (data-datum-allocation-trace-is-the-datum-block
                                  data-atom-allocation-trace-is-the-atom-block)
                                 (boymoo-compiler::read-lines)))))
