(in-package "BOYMOO-PROOFS")

(include-book "static-serialization")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-static-datum-word-p (datum)
  (or (null datum) (integerp (if (consp datum) (cdr datum) datum))))

(local
 (defthm assembly-first-static-result
   (equal (mv-nth 0 results) (car results))))

(local
 (defthm assembly-second-static-result
   (equal (mv-nth 1 results) (cadr results))))

(local (in-theory (disable ash length boymoo-compiler::low-bits
                           boymoo-compiler::aligned-size
                           boymoo-compiler::data-integer-value
                           boymoo-compiler::find-char boymoo-compiler::decimal-value
                           (:executable-counterpart boymoo-compiler::compiler-error))))

(defthm assembly-static-datum-is-not-string
  (implies (assembly-static-datum-word-p datum)
           (not (stringp datum))))

(defthm assembly-integer-is-static-datum
  (implies (integerp datum)
           (assembly-static-datum-word-p datum)))

(local (in-theory (disable assembly-static-datum-word-p)))

(defthm assembly-sized-block-has-integer-offset
  (implies (assembly-static-block-p block)
           (integerp (car block)))
  :rule-classes (:rewrite :forward-chaining))

(defthm assembly-empty-static-block-is-sized
  (assembly-static-block-p '(80)))

(local
 (defthm assembly-static-length-is-natural
   (natp (length text))
   :hints (("Goal" :in-theory (enable length)))
   :rule-classes :type-prescription))

(local
 (defthm assembly-aligned-static-string-size-is-integer
   (integerp (boymoo-compiler::aligned-size (length text) 3))
   :hints (("Goal" :use ((:instance assembly-eight-byte-padding-bounds (size (length text))))))))

(defthm assembly-static-block-sizes-data-word
  (implies (and (assembly-static-block-p block) (not (stringp word)))
           (assembly-static-block-p (boymoo-compiler::data-word word block))))

(defthm assembly-static-block-sizes-data-text
  (implies (and (assembly-static-block-p block) (stringp text))
           (and (integerp (car (boymoo-compiler::data-text type text block)))
                (assembly-static-block-p (cadr (boymoo-compiler::data-text type text block))))))

(defthm assembly-static-block-sizes-data-cell
  (implies (and (assembly-static-block-p block) (not (stringp a)) (not (stringp d)))
           (and (integerp (car (boymoo-compiler::data-cell a d block)))
                (assembly-static-block-p (cadr (boymoo-compiler::data-cell a d block))))))

(defthm assembly-static-block-sizes-data-fields
  (implies (and (assembly-static-block-p block) (not (stringp a)) (not (stringp b)))
           (and (integerp (car (boymoo-compiler::data-fields type a b block)))
                (assembly-static-block-p (cadr (boymoo-compiler::data-fields type a b block))))))

(local (in-theory (disable assembly-static-block-p assembly-static-chunks-size
                           boymoo-compiler::data-word boymoo-compiler::data-fields
                           boymoo-compiler::data-cell boymoo-compiler::data-text)))

(local
 (defthm assembly-static-block-sizes-data-words
   (implies (and (assembly-static-block-p block) (assembly-static-words-p words))
            (assembly-static-block-p (boymoo-compiler::data-words words block)))))

(defthm assembly-static-block-sizes-data-vector
  (implies (and (assembly-static-block-p block) (assembly-static-words-p words))
           (and (integerp (car (boymoo-compiler::data-vector words block)))
                (assembly-static-block-p (cadr (boymoo-compiler::data-vector words block))))))

(defthm assembly-static-block-sizes-list-cells
  (implies (and (assembly-static-block-p block)
                (assembly-static-words-p reversed)
                (assembly-static-datum-word-p tail))
           (and (assembly-static-datum-word-p
                  (car (boymoo-compiler::data-list-cells reversed tail block)))
                (assembly-static-block-p
                  (cadr (boymoo-compiler::data-list-cells reversed tail block)))))
  :hints (("Goal" :induct (boymoo-compiler::data-list-cells reversed tail block))))

(local
 (defthm assembly-limbs-are-static-words
   (implies (and (integerp magnitude) (assembly-static-words-p tail))
            (assembly-static-words-p
             (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)))
   :hints (("Goal" :induct (boymoo-compiler::data-integer-limbs magnitude width leading fuel tail)
                   :in-theory (enable boymoo-compiler::low-bits)))))

(local (in-theory (disable boymoo-compiler::data-integer-limbs boymoo-compiler::data-words)))

(defthm assembly-static-block-sizes-data-write-integer
  (implies (and (assembly-static-block-p block) (integerp value))
           (and (assembly-static-datum-word-p
                 (car (boymoo-compiler::data-write-integer value text-length block)))
                (assembly-static-block-p
                 (cadr (boymoo-compiler::data-write-integer value text-length block)))))
  :hints (("Goal" :in-theory (enable assembly-static-datum-word-p))))

(defun assembly-decimal-digits-p (text start left)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      t
    (let ((digit (- (char-code (char text start)) 48)))
      (and (<= 0 digit) (<= digit 9)
           (assembly-decimal-digits-p text (+ start 1) (- left 1))))))

(defun assembly-canonical-integer-token-p (text start end)
  (and (stringp text) (natp start) (natp end)
       (< start end) (<= end (length text))
       (let* ((minus (equal (char text start) #\-))
              (first (if minus (+ start 1) start))
              (left (- end first)))
         (and (< 0 left)
              (not (and (equal (char text first) #\0) (or minus (< 1 left))))
              (assembly-decimal-digits-p text first left)))))

(local
 (defthm assembly-decimal-fold-is-integer
   (implies (and (integerp negative) (assembly-decimal-digits-p text start left))
            (integerp (boymoo-compiler::decimal-value text start left negative)))
   :hints (("Goal"
            :induct (boymoo-compiler::decimal-value text start left negative)
            :in-theory (enable boymoo-compiler::decimal-value)))
   :rule-classes :type-prescription))

(defthm assembly-canonical-integer-token-parses
  (implies (assembly-canonical-integer-token-p text start end)
           (integerp (boymoo-compiler::data-integer-value text start end)))
  :hints (("Goal" :in-theory (e/d (boymoo-compiler::data-integer-value)
                                  (assembly-decimal-digits-p))))
  :rule-classes :type-prescription)

(local (in-theory (disable assembly-canonical-integer-token-p)))

(defun assembly-static-rational-input-p (text)
  (let* ((end (length text))
         (slash (boymoo-compiler::find-char text 0 end #\/)))
    (if slash
        (and (assembly-canonical-integer-token-p text 0 slash)
             (assembly-canonical-integer-token-p text (+ slash 1) end))
      (assembly-canonical-integer-token-p text 0 end))))

(local (in-theory (disable boymoo-compiler::data-write-integer char subseq)))

(defthm assembly-static-block-sizes-data-rational
  (implies (and (assembly-static-block-p block) (assembly-static-rational-input-p text))
           (and (assembly-static-datum-word-p (car (boymoo-compiler::data-rational text block)))
                (assembly-static-block-p (cadr (boymoo-compiler::data-rational text block))))))

(defun assembly-static-number-input-p (text)
  (if (equal (char text 0) #\#)
      (let* ((end (- (length text) 1))
             (space (boymoo-compiler::find-char text 3 (- end 3) #\Space)))
        (and space
             (assembly-static-rational-input-p (subseq text 3 space))
             (assembly-static-rational-input-p (subseq text (+ space 1) end))))
    (assembly-static-rational-input-p text)))

(local (in-theory (disable assembly-static-rational-input-p boymoo-compiler::data-rational)))

(defthm assembly-static-block-sizes-data-number
  (implies (and (assembly-static-block-p block) (assembly-static-number-input-p text))
           (and (assembly-static-datum-word-p (car (boymoo-compiler::data-number text block)))
                (assembly-static-block-p (cadr (boymoo-compiler::data-number text block))))))
