(in-package "BOYMOO-PROOFS")

(include-book "reader")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(defun data-rational-text-p (text)
  (let* ((end (length text))
         (slash (boymoo-compiler::find-char text 0 end #\/)))
    (if slash
        (let ((num (data-text-integer text 0 slash))
              (den (data-text-integer text (1+ slash) end)))
          (and (data-integer-text-p text 0 slash)
               (data-integer-text-p text (1+ slash) end)
               (not (equal num 0)) (< 1 den) (equal (denominator (/ num den)) den)))
      (data-integer-text-p text 0 end))))

(defun data-rational-text-value (text)
  (let* ((end (length text))
         (slash (boymoo-compiler::find-char text 0 end #\/)))
    (if slash
        (/ (data-text-integer text 0 slash) (data-text-integer text (1+ slash) end))
      (data-text-integer text 0 end))))

(local
 (in-theory (disable boymoo-compiler::find-char boymoo-compiler::data-integer-value
                     boymoo-compiler::data-write-integer boymoo-compiler::data-fields
                     data-integer-text-p data-text-integer char length)))

(defthmd data-rational-text-allocates-normalized-fields
  (let* ((end (length text))
         (slash (boymoo-compiler::find-char text 0 end #\/))
         (start (1+ slash)))
    (implies (data-rational-text-p text)
             (equal (mv-list 2 (boymoo-compiler::data-rational text block))
                    (if slash
                        (mv-let (numerator block)
                          (boymoo-compiler::data-write-integer (data-text-integer text 0 slash) slash block)
                          (mv-let (denominator block)
                            (boymoo-compiler::data-write-integer (data-text-integer text start end)
                                                                 (- end start) block)
                            (mv-list 2 (boymoo-compiler::data-fields 4 numerator denominator block))))
                      (mv-list 2 (boymoo-compiler::data-write-integer
                                  (data-text-integer text 0 end) end block))))))
  :hints (("Goal" :in-theory (enable data-read-canonical-integer))))

(local
 (defthm field-object-reference-is-a-number
   (acl2-numberp (car (boymoo-compiler::data-fields type first second block)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-fields)))))

(local
 (defthm integer-writer-encodes-zero-exactly
   (equal (equal (car (boymoo-compiler::data-write-integer value length block)) '(:integer . 0))
          (equal value 0))
   :hints (("Goal" :in-theory (e/d (boymoo-compiler::data-write-integer)
                                  (boymoo-compiler::data-words boymoo-compiler::data-integer-limbs ash))))))

(defthmd data-rational-encodes-zero-exactly
  (implies (data-rational-text-p text)
           (equal (equal (car (boymoo-compiler::data-rational text block)) '(:integer . 0))
                  (equal (data-rational-text-value text) 0)))
  :hints (("Goal" :in-theory (enable data-read-canonical-integer))))

(defun data-complex-text-p (text)
  (let* ((end (1- (length text)))
         (space (boymoo-compiler::find-char text 3 (- end 3) #\Space)))
    (and (stringp text) (< 4 end) space
         (equal (char text 0) #\#) (equal (char text 1) #\C)
         (equal (char text 2) #\() (equal (char text end) #\))
         (data-rational-text-p (subseq text 3 space))
         (data-rational-text-p (subseq text (1+ space) end))
         (not (equal (data-rational-text-value (subseq text (1+ space) end)) 0)))))

(defthmd data-complex-text-allocates-normalized-fields
  (let* ((end (1- (length text)))
         (space (boymoo-compiler::find-char text 3 (- end 3) #\Space))
         (real-text (subseq text 3 space))
         (imaginary-text (subseq text (1+ space) end)))
    (implies (data-complex-text-p text)
             (equal (mv-list 2 (boymoo-compiler::data-number text block))
                    (mv-let (real block)
                      (boymoo-compiler::data-rational real-text block)
                      (mv-let (imaginary block)
                        (boymoo-compiler::data-rational imaginary-text block)
                        (mv-list 2 (boymoo-compiler::data-fields 5 real imaginary block)))))))
  :hints (("Goal" :in-theory (e/d (data-rational-encodes-zero-exactly)
                                 (boymoo-compiler::data-rational data-rational-text-p
                                  data-rational-text-value subseq)))))

(defthmd data-view-of-normalized-number-fields
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object))
         (value (if (equal type 4) (/ first second) (complex first second))))
    (implies (and (or (and (equal type 4) (integerp first) (integerp second) (< 1 second)
                           (equal (numerator value) first) (equal (denominator value) second))
                      (and (equal type 5) (rationalp first) (rationalp second) (not (equal second 0))))
                  (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (posp rank) (eq (proof-object-kind object) :header)
                  (proof-span-p address 24)
                  (equal (proof-load-word address machine) (+ 4096 type))
                  (data-child-value-p (proof-load-word (+ address 8) machine) first rank
                                      base objects packages machine)
                  (data-child-value-p (proof-load-word (+ address 16) machine) second rank
                                      base objects packages machine))
             (proof-value-p word value base objects packages machine)))
  :hints (("Goal" :use (data-view-of-static-two-field-header)
                  :in-theory (disable proof-view proof-view-step proof-load-word proof-pointer-address
                                      proof-word-tag data-child-value-p proof-span-p evenp))))
