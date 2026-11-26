(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(defun data-decimal-digits-p (text start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((code (char-code (char text start))))
      (and (<= 48 code) (<= code 57)
           (data-decimal-digits-p text (1+ start) (1- count))))))

; The first digit contributes its place value independently of the
; accumulator maintained by the compiler's scanner.
(defun data-decimal-place-value (text start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (* (- (char-code (char text start)) 48) (expt 10 (1- count)))
       (data-decimal-place-value text (1+ start) (1- count)))))

(local
 (defthm decimal-expt-step
   (implies (posp n) (equal (expt 10 n) (* 10 (expt 10 (1- n)))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt 10 n))))))

(local
 (defthm decimal-negative-constant-product
   (equal (- (* -48 x)) (* 48 x))
   :hints (("Goal" :use ((:instance data-product-of-minus (a x) (b 48)))
                   :in-theory (disable data-product-of-minus)))))

(defthmd data-decimal-value-by-place
  (implies (and (integerp accumulator) (data-decimal-digits-p text start count))
           (equal (boymoo-compiler::decimal-value text start count accumulator)
                  (- (* (expt 10 (nfix count)) accumulator)
                     (data-decimal-place-value text start count))))
  :hints (("Goal" :induct (boymoo-compiler::decimal-value text start count accumulator)
                  :in-theory (disable char expt))
          ("Subgoal *1/3" :use ((:instance decimal-expt-step (n count))
                                (:instance data-swap-front-factors
                                           (a accumulator) (b 10) (c (expt 10 (1- count))))))))

(defun data-integer-text-p (text start end)
  (let* ((negative (and (< start end) (equal (char text start) #\-)))
         (digit-start (if negative (1+ start) start))
         (count (- end digit-start)))
    (and (stringp text) (natp start) (natp end) (<= end (length text))
         (posp count)
         (or (not (equal (char text digit-start) #\0))
             (and (not negative) (equal count 1)))
         (data-decimal-digits-p text digit-start count))))

(defun data-text-integer (text start end)
  (if (equal (char text start) #\-)
      (- (data-decimal-place-value text (1+ start) (- end (1+ start))))
    (data-decimal-place-value text start (- end start))))

(defthmd data-read-canonical-integer
  (implies (data-integer-text-p text start end)
           (equal (boymoo-compiler::data-integer-value text start end)
                  (data-text-integer text start end)))
  :hints (("Goal" :in-theory (e/d (data-decimal-value-by-place)
                                 (boymoo-compiler::decimal-value data-decimal-place-value
                                  data-decimal-digits-p char)))))

(defthmd data-serialized-immediate-integer
  (implies (proof-immediate-integer-p integer)
           (and (equal (proof-constant-word
                        (mv-nth 0 (boymoo-compiler::data-write-integer integer text-length block)))
                       (proof-integer-word integer))
                (equal (mv-nth 1 (boymoo-compiler::data-write-integer integer text-length block))
                       block)))
  :hints (("Goal" :in-theory (disable proof-integer-word))))

(defun data-hex-digit-character (digit)
  (code-char (+ digit (if (< digit 10) 48 55))))

(local
 (defthm hex-value-of-canonical-digit
   (implies (and (natp digit) (< digit 16))
            (equal (boymoo-compiler::hex-value (data-hex-digit-character digit)) digit))))

(local
 (defthm hex-digit-decomposition
   (implies (and (natp code) (< code 256))
            (and (natp (floor code 16)) (< (floor code 16) 16)
                 (natp (mod code 16)) (< (mod code 16) 16)
                 (equal (+ (* 16 (floor code 16)) (mod code 16)) code)))
   :hints (("Goal" :use ((:instance data-floor-bounds (x code) (d 16)))
                   :in-theory (disable floor)))))

(local
 (defthm canonical-hex-byte
   (implies (and (natp code) (< code 256)
                 (equal (char text start) (data-hex-digit-character (floor code 16)))
                 (equal (char text (1+ start)) (data-hex-digit-character (mod code 16))))
            (equal (boymoo-compiler::hex-byte text start) code))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable data-hex-digit-character boymoo-compiler::hex-value
                                       floor mod char)))))

(defun data-character-text-p (text byte)
  (let ((code (char-code byte)))
    (and (characterp byte) (stringp text) (equal (length text) 4)
         (equal (char text 0) #\#) (equal (char text 1) #\\)
         (equal (char text 2) (data-hex-digit-character (floor code 16)))
         (equal (char text 3) (data-hex-digit-character (mod code 16))))))

(defthmd data-read-canonical-character
  (implies (data-character-text-p text byte)
           (equal (boymoo-compiler::hex-byte text 2) (char-code byte)))
  :hints (("Goal" :use ((:instance canonical-hex-byte (start 2) (code (char-code byte))))
                  :in-theory (disable boymoo-compiler::hex-byte floor mod char))))

(defun data-character-printed-literally-p (byte delimiter)
  (let ((code (char-code byte)))
    (and (<= 32 code) (<= code 126)
         (not (equal byte delimiter))
         (not (equal byte #\\)))))

(defun data-escaped-spelling-p (characters text start count delimiter)
  (if (atom characters)
      (and (null characters) (equal count 0))
    (let* ((byte (car characters))
           (code (char-code byte)))
      (and (characterp byte)
           (if (data-character-printed-literally-p byte delimiter)
               (and (posp count) (equal (char text start) byte)
                    (data-escaped-spelling-p (cdr characters) text (1+ start) (1- count) delimiter))
             (and (integerp count) (<= 3 count)
                  (equal (char text start) #\\)
                  (equal (char text (1+ start)) (data-hex-digit-character (floor code 16)))
                  (equal (char text (+ 2 start)) (data-hex-digit-character (mod code 16)))
                  (data-escaped-spelling-p (cdr characters) text (+ 3 start) (- count 3)
                                          delimiter)))))))

(local
 (defun data-decode-spelling-induction (characters start count delimiter acc)
   (if (atom characters)
       (list start count delimiter acc)
     (let ((size (if (data-character-printed-literally-p (car characters) delimiter) 1 3)))
       (data-decode-spelling-induction (cdr characters) (+ size start) (- count size)
                                       delimiter (cons (car characters) acc))))))

(defthmd data-decode-canonical-escaped-characters
  (implies (and (member-equal delimiter '(#\" #\|))
                (data-escaped-spelling-p characters text start count delimiter))
           (equal (boymoo-compiler::decode-characters text start count delimiter acc)
                  (coerce (boymoo-compiler::reverse-onto acc characters) 'string)))
  :hints (("Goal" :induct (data-decode-spelling-induction characters start count delimiter acc)
                  :in-theory (disable char floor mod data-hex-digit-character
                                      boymoo-compiler::hex-byte))
          ("Subgoal *1/2" :use ((:instance canonical-hex-byte
                                           (code (char-code (car characters))) (start (1+ start)))))))
