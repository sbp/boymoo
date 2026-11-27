(in-package "BOYMOO-PROOFS")

(include-book "limbs")
(include-book "reader")
(include-book "views")
(include-book "image")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash expt floor char)))

(local
 (defthm decimal-powers-at-positive-count
   (implies (posp count)
            (and (equal (expt 10 count) (* 10 (expt 10 (1- count))))
                 (equal (expt 2 (* 4 count)) (* 16 (expt 2 (* 4 (1- count)))))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt 10 count))
                   :use ((:instance data-two-power-of-sum (lower 4) (upper (* 4 (1- count)))))))))

(local
 (defthm decimal-power-is-positive-integer
   (implies (natp count) (posp (expt 10 count)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (expt 10 count) :in-theory (enable (:induction expt)))
           ("Subgoal *1/3" :expand ((expt 10 count))))))

(local
 (defthm decimal-power-fits-four-bits-per-digit
   (implies (natp count) (<= (expt 10 count) (expt 2 (* 4 count))))
   :hints (("Goal" :induct (expt 10 count) :in-theory (enable (:induction expt)))
           ("Subgoal *1/3" :use decimal-powers-at-positive-count))))

(local
 (defthm decimal-place-value-in-range
   (implies (and (natp count) (data-decimal-digits-p text start count))
            (and (natp (data-decimal-place-value text start count))
                 (< (data-decimal-place-value text start count) (expt 10 count))))
   :hints (("Goal" :induct (data-decimal-place-value text start count))
           ("Subgoal *1/2" :use decimal-powers-at-positive-count :nonlinearp t))))

(local
 (defthm powers-of-two-monotone-for-natural-exponents
   (implies (and (natp a) (natp b) (<= a b))
            (<= (expt 2 a) (expt 2 b)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-two-power-of-sum (lower (- b a)) (upper a))
                        (:instance data-expt-two-positive-integer (width (- b a)))
                        (:instance data-expt-two-positive-integer (width a)))
                   :nonlinearp t
                   :in-theory (e/d (associativity-of-+ acl2::commutativity-2-of-+)
                                  (data-expt-two-positive-integer))))))

(local
 (defthm natural-limb-capacity-from-text-length
   (implies (posp text-length)
            (let ((width (ash (+ text-length 7) -3)))
              (and (posp width) (<= width text-length)
                   (<= (* 4 text-length) (* 32 width)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-floor-bounds (x (+ text-length 7)) (d 8)))
                   :in-theory (enable data-ash-right)))))

(local
 (defthm decimal-place-value-is-integer
   (integerp (data-decimal-place-value text start count))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (data-decimal-place-value text start count)))))

(local
 (defthm decimal-magnitude-is-natural
   (natp (abs (data-text-integer text start end)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable data-decimal-place-value)))))

(local
 (defthm decimal-magnitude-fits-four-bits-per-character
   (implies (data-integer-text-p text start end)
            (< (abs (data-text-integer text start end)) (expt 2 (* 4 (- end start)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance decimal-place-value-in-range (count (- end start)))
                        (:instance decimal-place-value-in-range (start (1+ start)) (count (- end (1+ start))))
                        (:instance decimal-power-fits-four-bits-per-digit (count (- end start)))
                        (:instance decimal-power-fits-four-bits-per-digit (count (- end (1+ start))))
                        (:instance powers-of-two-monotone-for-natural-exponents
                                   (a (* 4 (- end (1+ start)))) (b (* 4 (- end start)))))
                   :in-theory (disable data-decimal-place-value decimal-place-value-in-range
                                       decimal-power-fits-four-bits-per-digit)))))

(defthmd data-integer-text-fits-limb-width
  (implies (data-integer-text-p text start end)
           (let* ((text-length (- end start))
                  (width (ash (+ text-length 7) -3))
                  (magnitude (abs (data-text-integer text start end))))
             (and (posp width) (<= width text-length) (natp magnitude)
                  (< magnitude (expt 2 (* 32 width))))))
  :hints (("Goal" :use (decimal-magnitude-fits-four-bits-per-character
                       (:instance natural-limb-capacity-from-text-length (text-length (- end start)))
                       (:instance powers-of-two-monotone-for-natural-exponents
                                  (a (* 4 (- end start))) (b (* 32 (ash (+ 7 (- end start)) -3)))))
                  :in-theory (disable data-text-integer abs data-decimal-digits-p))))

(defun data-boxed-integer-limbs (value text-length)
  (boymoo-compiler::data-integer-limbs (abs value) (ash (+ text-length 7) -3) t text-length nil))

(defun data-boxed-integer-fields (value limbs)
  (list* (+ 3 (* 2048 (1+ (len limbs)))) (if (< value 0) 1 0) limbs))

(local
 (defthm decimal-value-is-integer
   (integerp (data-text-integer text start end))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable data-decimal-place-value)))))

(defthmd data-boxed-integer-text-has-normalized-limbs
  (let* ((value (data-text-integer text start end))
         (limbs (data-boxed-integer-limbs value (- end start))))
    (implies (and (data-integer-text-p text start end) (not (proof-immediate-integer-p value)))
             (and (data-limb-list-p limbs) (data-limb-list-normalized-p limbs)
                  (equal (data-limb-list-value limbs) (abs value)))))
  :hints (("Goal" :use (data-integer-text-fits-limb-width
                       (:instance data-integer-limbs-normalized-value
                                  (width (ash (+ 7 (- end start)) -3))
                                  (magnitude (abs (data-text-integer text start end)))
                                  (fuel (- end start)) (leading t)))
                  :in-theory (disable data-text-integer boymoo-compiler::data-integer-limbs
                                      data-limb-list-value data-limb-list-normalized-p
                                      data-limb-list-p data-decimal-digits-p))))

(local
 (defthm reverse-onto-of-cons
   (equal (boymoo-compiler::reverse-onto (cons first rest) tail)
          (boymoo-compiler::reverse-onto rest (cons first tail)))))

(defthmd data-write-boxed-integer-allocates-fields
  (let* ((limbs (data-boxed-integer-limbs value text-length))
         (fields (data-boxed-integer-fields value limbs)))
    (implies (and (integerp value) (not (proof-immediate-integer-p value)) (integerp (car block)))
             (equal (mv-list 2 (boymoo-compiler::data-write-integer value text-length block))
                    (list (+ 2 (car block))
                          (cons (+ (car block) (* 8 (len fields)))
                                (boymoo-compiler::reverse-onto fields (cdr block)))))))
  :hints (("Goal" :in-theory (e/d (data-words-allocate-consecutively data-ash-left)
                                 (boymoo-compiler::data-words boymoo-compiler::data-integer-limbs
                                  boymoo-compiler::reverse-onto)))))

(defthmd data-canonical-boxed-integer-allocates-fields
  (let* ((end (length text))
         (value (data-text-integer text 0 end))
         (limbs (data-boxed-integer-limbs value end))
         (fields (data-boxed-integer-fields value limbs)))
    (implies (and (data-integer-text-p text 0 end) (not (proof-immediate-integer-p value))
                  (integerp (car block)))
             (equal (mv-list 2 (boymoo-compiler::data-integer text block))
                    (list (+ 2 (car block))
                          (cons (+ (car block) (* 8 (len fields)))
                                (boymoo-compiler::reverse-onto fields (cdr block)))))))
  :hints (("Goal" :use ((:instance data-read-canonical-integer (start 0) (end (length text)))
                       (:instance data-write-boxed-integer-allocates-fields
                                  (value (data-text-integer text 0 (length text)))
                                  (text-length (length text))))
                  :in-theory (disable data-text-integer data-integer-text-p length
                                      data-boxed-integer-limbs data-boxed-integer-fields
                                      boymoo-compiler::data-write-integer
                                      boymoo-compiler::data-integer-value
                                      boymoo-compiler::reverse-onto proof-immediate-integer-p))))

(local
 (defun limb-load-induction (limbs address)
   (if (atom limbs)
       address
     (limb-load-induction (cdr limbs) (+ address 8)))))

(defthmd data-loaded-limbs-agree-with-encoding
  (implies (and (data-limb-list-p limbs) (data-memory-words-p limbs address machine))
           (and (equal (proof-limb-magnitude (len limbs) address machine)
                       (data-limb-list-value limbs))
                (equal (proof-limbs-p (len limbs) address machine)
                       (or (atom limbs) (data-limb-list-normalized-p limbs)))))
  :hints (("Goal" :induct (limb-load-induction limbs address)
                  :in-theory (disable proof-load-word))))

(local
 (defthm payload-size-of-boxed-integer
   (let ((size (* 8 (1+ count))))
     (implies (natp count)
              (and (equal (mod size 8) 0) (equal (ash size -3) (1+ count)))))
   :hints (("Goal" :use ((:instance data-floor-unique (x (* 8 (1+ count))) (d 8) (q (1+ count))))
                   :in-theory (enable data-ash-right)))))

(local
 (defthm positive-limb-count
   (implies (data-limb-list-normalized-p limbs) (< 0 (len limbs)))
   :rule-classes :linear))

(local
 (defthm product-of-header-and-word-scales
   (equal (* 256 (* 8 count)) (* 2048 count))
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 256) (acl2::y 8) (acl2::z count)))
                   :in-theory (disable associativity-of-*)))))

(defthmd data-integer-view-of-boxed-fields
  (let ((fields (data-boxed-integer-fields value limbs)))
    (implies (and (integerp value) (data-limb-list-p limbs) (data-limb-list-normalized-p limbs)
                  (equal (data-limb-list-value limbs) (abs value))
                  (data-memory-words-p fields address machine)
                  (proof-span-p address (* 8 (len fields))))
             (and (equal (proof-header-type (proof-load-word address machine)) 3)
                  (proof-span-p address (+ 8 (proof-header-size (proof-load-word address machine))))
                  (equal (proof-integer-view address machine) (proof-value-view value)))))
  :hints (("Goal" :use ((:instance data-header-type-and-size (type 3) (size (* 8 (1+ (len limbs)))))
                       (:instance payload-size-of-boxed-integer (count (len limbs)))
                       (:instance data-loaded-limbs-agree-with-encoding (address (+ address 16))))
                  :in-theory (disable proof-load-word proof-span-p proof-header-size proof-header-type
                                      proof-limb-magnitude proof-limbs-p mod
                                      payload-size-of-boxed-integer data-limb-list-value
                                      data-limb-list-normalized-p data-limb-list-p))))

(local
 (defthm limbs-fit-in-u64-words
   (implies (data-limb-list-p limbs) (data-u64-word-list-p limbs))))

(local
 (defthm canonical-boxed-fields-are-u64-words
   (implies (and (data-limb-list-p limbs) (unsigned-byte-p 64 (+ 3 (* 2048 (1+ (len limbs))))))
            (data-u64-word-list-p (data-boxed-integer-fields value limbs)))
   :hints (("Goal" :in-theory (disable data-limb-list-p)))))

(defthmd data-view-of-canonical-boxed-integer
  (let* ((value (data-text-integer text start end))
         (limbs (data-boxed-integer-limbs value (- end start)))
         (fields (data-boxed-integer-fields value limbs))
         (address (proof-pointer-address word base))
         (object (assoc-equal address objects)))
    (implies (and (data-integer-text-p text start end) (not (proof-immediate-integer-p value))
                  (unsigned-byte-p 64 (car fields))
                  (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (natp (proof-object-rank object)) (eq (proof-object-kind object) :header)
                  (proof-span-p address (* 8 (len fields)))
                  (data-placed-characters-p (data-forward-chunk-characters fields) address machine))
             (proof-value-p word value base objects packages machine)))
  :hints (("Goal" :use (data-boxed-integer-text-has-normalized-limbs
                       (:instance data-placed-u64-chunks-load-their-words
                                  (words (data-boxed-integer-fields
                                          (data-text-integer text start end)
                                          (data-boxed-integer-limbs (data-text-integer text start end)
                                                                   (- end start))))
                                  (address (proof-pointer-address word base)))
                       (:instance data-integer-view-of-boxed-fields
                                  (value (data-text-integer text start end))
                                  (limbs (data-boxed-integer-limbs (data-text-integer text start end)
                                                                  (- end start)))
                                  (address (proof-pointer-address word base))
                                  (machine machine)))
                  :in-theory (disable proof-word-tag proof-pointer-address proof-integer-view
                                      proof-view-step proof-load-word proof-immediate-integer-p
                                      proof-header-type proof-header-size proof-span-p
                                      data-placed-characters-p data-boxed-integer-limbs
                                      data-text-integer data-integer-text-p evenp
                                      data-limb-list-p data-limb-list-value
                                      data-limb-list-normalized-p data-forward-chunk-characters
                                      proof-symbol-value proof-rational-value proof-complex-value
                                      proof-load-string mod)
                  :expand ((:free (depth)
                                  (proof-view-step :word word 0 depth base objects packages machine))))))
