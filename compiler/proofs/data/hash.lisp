(in-package "BOYMOO-PROOFS")

(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor expt boymoo-compiler::low-bits boymoo-model::a64-unsigned)))

(defthmd data-low-bits-after-radix-multiple
  (implies (and (integerp word) (integerp multiplier) (natp width))
           (equal (boymoo-compiler::low-bits (+ word (* multiplier (expt 2 width))) width)
                  (boymoo-compiler::low-bits word width)))
  :hints (("Goal" :use ((:instance data-low-bits-remainder)
                       (:instance data-low-bits-in-range)
                       (:instance data-low-bits-unique
                                  (word (+ word (* multiplier (expt 2 width))))
                                  (q (+ multiplier (floor word (expt 2 width))))
                                  (residue (boymoo-compiler::low-bits word width))))
                  :in-theory (disable data-low-bits-in-range))))

(defthmd data-low-bits-reduce-affine-input
  (implies (and (integerp word) (integerp factor) (integerp offset) (natp width))
           (equal (boymoo-compiler::low-bits (+ offset (* factor (boymoo-compiler::low-bits word width))) width)
                  (boymoo-compiler::low-bits (+ offset (* factor word)) width)))
  :hints (("Goal" :use (data-low-bits-remainder
                       (:instance data-low-bits-after-radix-multiple
                                  (word (+ offset (* factor (boymoo-compiler::low-bits word width))))
                                  (multiplier (* factor (floor word (expt 2 width)))))))))

(local
 (defthm twelve-bit-radix-squared
   (equal (* 4096 (* 4096 x)) (* 16777216 x))
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 4096) (acl2::y 4096) (acl2::z x)))
                   :in-theory (disable associativity-of-*)))))

(defthm data-low-twelve-bits-of-low-twenty-four
  (implies (integerp word)
           (equal (boymoo-compiler::low-bits (boymoo-compiler::low-bits word 24) 12)
                  (boymoo-compiler::low-bits word 12)))
  :hints (("Goal" :use ((:instance data-low-bits-remainder (width 24))
                       (:instance data-low-bits-after-radix-multiple
                                  (word (boymoo-compiler::low-bits word 24)) (width 12)
                                  (multiplier (* 4096 (floor word (expt 2 24)))))))))

(local
 (defthm low-bits-is-integer
   (implies (and (integerp value) (natp width))
            (integerp (boymoo-compiler::low-bits value width)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use ((:instance data-low-bits-in-range (word value)))
                   :in-theory (disable data-low-bits-in-range)))))

(local
 (defthm hash-character-code-is-integer
   (integerp (char-code ch))
   :rule-classes :type-prescription
   :hints (("Goal" :cases ((characterp ch))))))

(local
 (defthm compiler-hash-string-has-integer-result
   (implies (integerp hash)
            (integerp (boymoo-compiler::hash-string text start count hash)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (boymoo-compiler::hash-string text start count hash)))))

(defun data-hash-character-source-p (text start count characters)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (null characters)
    (and (consp characters) (equal (char text start) (car characters))
         (data-hash-character-source-p text (1+ start) (1- count) (cdr characters)))))

(local
 (defun data-hash-scanner-induction (text start count hash characters)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (list text start hash characters)
     (data-hash-scanner-induction
      text (1+ start) (1- count)
      (boymoo-compiler::low-bits (+ (* 33 hash) (char-code (char text start))) 24)
      (cdr characters)))))

(local
 (defthm low-bits-of-already-reduced
   (implies (and (integerp word) (natp width))
            (equal (boymoo-compiler::low-bits (boymoo-compiler::low-bits word width) width)
                   (boymoo-compiler::low-bits word width)))))

(local
 (defthm proof-hash-characters-of-nonempty-list
   (implies (and (syntaxp (symbolp characters)) (consp characters))
            (equal (proof-hash-characters characters hash width)
                   (proof-hash-characters
                    (cdr characters)
                    (boymoo-model::a64-unsigned width (+ (* 33 hash) (char-code (car characters))))
                    width)))
   :hints (("Goal" :expand ((proof-hash-characters characters hash width))))))

(local
 (defthm machine-hash-update-of-reduced-hash
   (implies (integerp hash)
            (equal (boymoo-model::a64-unsigned
                    12 (+ (char-code ch) (* 33 (boymoo-compiler::low-bits hash 12))))
                   (boymoo-compiler::low-bits (+ (char-code ch) (* 33 hash)) 12)))
   :hints (("Goal" :use ((:instance data-machine-unsigned-is-low-bits
                                    (word (+ (char-code ch) (* 33 (boymoo-compiler::low-bits hash 12))))
                                    (width 12))
                        (:instance data-low-bits-reduce-affine-input
                                   (word hash) (factor 33) (offset (char-code ch)) (width 12)))
                   :in-theory (disable char-code)))))

(defthmd data-compiler-hash-scanner-agrees
  (implies (and (integerp hash) (data-hash-character-source-p text start count characters))
           (equal (boymoo-compiler::low-bits (boymoo-compiler::hash-string text start count hash) 12)
                  (proof-hash-characters characters (boymoo-compiler::low-bits hash 12) 12)))
  :hints (("Goal" :induct (data-hash-scanner-induction text start count hash characters)
                  :in-theory (e/d (data-machine-unsigned-is-low-bits data-low-bits-reduce-affine-input)
                                 (char)))))

(local
 (defthm hash-cdr-of-nthcdr
   (implies (natp start)
            (equal (nthcdr (1+ start) characters) (cdr (nthcdr start characters))))
   :hints (("Goal" :induct (nthcdr start characters)))))

(local
 (defthm hash-car-of-nthcdr
   (equal (car (nthcdr start characters)) (nth start characters))
   :hints (("Goal" :induct (nthcdr start characters)))))

(local
 (defun data-hash-suffix-induction (characters start)
   (if (atom characters)
       start
     (data-hash-suffix-induction (cdr characters) (1+ start)))))

(local
 (defthm hash-characters-are-string-suffix
   (implies (and (natp start) (stringp text)
                 (equal characters (nthcdr start (coerce text 'list))))
            (data-hash-character-source-p text start (len characters) characters))
   :hints (("Goal" :induct (data-hash-suffix-induction characters start)
                   :in-theory (disable nthcdr)))))

(local
 (defthm string-hash-source-characters
   (implies (stringp text)
            (data-hash-character-source-p text 0 (length text) (coerce text 'list)))
   :hints (("Goal" :use ((:instance hash-characters-are-string-suffix
                                    (start 0) (characters (coerce text 'list))))))))

(defthmd data-compiler-bucket-hash-agrees
  (implies (and (stringp name) (natp number))
           (equal (boymoo-compiler::low-bits (+ (boymoo-compiler::text-hash name) (* 7919 number)) 12)
                  (proof-symbol-hash number name 12)))
  :hints (("Goal" :use ((:instance data-compiler-hash-scanner-agrees
                                   (text name) (start 0) (count (length name))
                                   (hash 0) (characters (coerce name 'list)))
                       (:instance data-low-bits-reduce-affine-input
                                  (word (boymoo-compiler::text-hash name)) (width 12)
                                  (factor 1) (offset (* 7919 number))))
                  :in-theory (e/d (data-machine-unsigned-is-low-bits)
                                 (boymoo-compiler::hash-string proof-hash-characters)))))
