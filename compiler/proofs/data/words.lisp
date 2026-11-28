(in-package "BOYMOO-PROOFS")

(include-book "placement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::low-bits ash floor expt)))

(local
 (defthm split-word-trailing-bit
   (implies (integerp word)
            (equal (+ (boymoo-compiler::low-bits word 1) (* 2 (floor word 2))) word))
   :hints (("Goal" :use ((:instance data-low-bits-remainder (width 1)))
                   :in-theory (disable data-low-bit-parity)))))

(local
 (defthm and-with-zero-or-minus-one
   (implies (integerp word)
            (and (equal (logand 0 word) 0) (equal (logand word 0) 0)
                 (equal (logand -1 word) word) (equal (logand word -1) word)))
   :hints (("Goal" :expand ((logand 0 word) (logand word 0)
                            (logand -1 word) (logand word -1))))))

(local
 (defthm logand-trailing-bit-step
   (implies (and (integerp first) (integerp second))
            (equal (logand first second)
                   (+ (* 2 (logand (floor first 2) (floor second 2)))
                      (if (and (oddp first) (oddp second)) 1 0))))
   :rule-classes nil
   :hints (("Goal" :expand ((logand first second))
                   :use ((:instance split-word-trailing-bit (word first))
                         (:instance split-word-trailing-bit (word second)))
                   :in-theory (disable split-word-trailing-bit acl2::binary-logand evenp)))))

(local
 (defthm floor-half-of-complement
   (implies (integerp word)
            (equal (floor (+ -1 (- word)) 2) (+ -1 (- (floor word 2)))))
   :hints (("Goal" :use ((:instance data-floor-bounds (x word) (d 2))
                        (:instance data-floor-unique (x (lognot word)) (d 2)
                                   (q (lognot (floor word 2)))))))))

(local
 (defthm parity-of-complement
   (implies (integerp word) (equal (evenp (+ -1 (- word))) (oddp word)))
   :hints (("Goal" :use ((:instance data-low-bit-parity)
                        (:instance data-low-bit-parity (word (lognot word)))
                        (:instance data-low-bits-remainder (width 1))
                        (:instance data-low-bits-remainder (width 1) (word (lognot word))))
                   :in-theory (disable evenp data-low-bit-parity)))))

(local
 (defthm logior-trailing-bit-step
   (implies (and (integerp first) (integerp second))
            (equal (logior first second)
                   (+ (* 2 (logior (floor first 2) (floor second 2)))
                      (if (or (oddp first) (oddp second)) 1 0))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance logand-trailing-bit-step
                                    (first (lognot first)) (second (lognot second))))
                   :in-theory (disable acl2::binary-logand evenp)))))

(local
 (defthm word-power-of-two-step
   (implies (posp width)
            (equal (expt 2 width) (* 2 (expt 2 (1- width)))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt 2 width))))))

(local
 (defthm floor-half-of-double
   (implies (integerp number) (equal (floor (* 2 number) 2) number))
   :hints (("Goal" :use ((:instance data-floor-unique (x (* 2 number)) (d 2) (q number)))))))

(local
 (defthm evenp-of-double
   (implies (integerp number) (evenp (* 2 number)))
   :hints (("Goal" :use ((:instance split-word-trailing-bit (word (* 2 number)))
                        (:instance data-low-bit-parity (word (* 2 number))))
                   :in-theory (disable split-word-trailing-bit data-low-bit-parity evenp)))))

(local
 (defun fuse-fields-induction (low width)
   (declare (xargs :measure (nfix width)))
   (if (zp width) low (fuse-fields-induction (floor low 2) (1- width)))))

(local
 (defthm higher-power-shift-is-double
   (implies (and (posp width) (integerp high))
            (equal (* high (expt 2 width)) (* 2 (* high (expt 2 (1- width))))))
   :rule-classes nil
   :hints (("Goal" :use (word-power-of-two-step
                        (:instance data-swap-front-factors (a high) (b 2) (c (expt 2 (1- width)))))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(local
 (defthm half-of-higher-power-shift
   (implies (and (posp width) (integerp high))
            (and (equal (floor (* high (expt 2 width)) 2) (* high (expt 2 (1- width))))
                 (evenp (* high (expt 2 width)))))
   :hints (("Goal" :use higher-power-shift-is-double
                   :in-theory (disable evenp commutativity-of-* associativity-of-*)))))

(defthmd data-fuse-disjoint-bit-fields
  (implies (and (natp low) (natp high) (natp width) (< low (expt 2 width)))
           (equal (logior low (* (expt 2 width) high)) (+ low (* (expt 2 width) high))))
  :hints (("Goal" :induct (fuse-fields-induction low width)
                  :in-theory (disable acl2::binary-logior acl2::binary-logand evenp))
          ("Subgoal *1/2" :use ((:instance word-power-of-two-step)
                                higher-power-shift-is-double
                                (:instance logior-trailing-bit-step
                                           (first low) (second (* (expt 2 width) high)))
                                (:instance data-floor-bounds (x low) (d 2))
                                (:instance split-word-trailing-bit (word low)))
                          :in-theory (disable split-word-trailing-bit acl2::binary-logior
                                              acl2::binary-logand evenp))
          ("Subgoal *1/1" :in-theory (enable acl2::binary-logior))))

(local
 (defthm fused-byte-and-word
   (implies (and (unsigned-byte-p 8 low) (natp high))
            (equal (logior low (ash high 8)) (+ low (* 256 high))))
   :hints (("Goal" :use ((:instance data-fuse-disjoint-bit-fields (width 8)))
                   :in-theory (e/d (data-ash-left) (acl2::binary-logior))))))

(defun data-little-endian-value (characters)
  (if (atom characters)
      0
    (+ (char-code (car characters)) (* 256 (data-little-endian-value (cdr characters))))))

(local
 (defthm data-little-endian-value-is-natural
   (implies (character-listp characters) (natp (data-little-endian-value characters)))))

(defthm data-read-word-is-little-endian
  (implies (character-listp characters)
           (equal (data-characters-read-word characters) (data-little-endian-value characters)))
  :hints (("Goal" :induct (data-little-endian-value characters)
                  :in-theory (disable acl2::binary-logior))))

(local
 (defthm code-of-low-byte
   (implies (integerp word)
            (equal (char-code (code-char (boymoo-compiler::low-bits word 8)))
                   (boymoo-compiler::low-bits word 8)))
   :hints (("Goal" :use ((:instance data-low-bits-in-range (width 8)))
                   :in-theory (disable data-low-bits-in-range)))))

(local
 (defthm eight-times-remaining-plus-eight
   (equal (+ 8 (* 8 (1- count))) (* 8 count))))

(local
 (defthm minus-of-eight-times-value
   (equal (- (* 8 count)) (* -8 count))
   :hints (("Goal" :use ((:instance data-product-of-minus (a count) (b 8)))
                   :in-theory (disable data-product-of-minus)))))

(defthmd data-prepend-word-little-endian-value
  (implies (and (integerp word) (natp count))
           (equal (data-little-endian-value (boymoo-compiler::prepend-word word count tail))
                  (+ (boymoo-compiler::low-bits word (* 8 count))
                     (* (expt 2 (* 8 count)) (data-little-endian-value tail)))))
  :hints (("Goal" :induct (boymoo-compiler::prepend-word word count tail))
          ("Subgoal *1/1" :use ((:instance data-low-bits-remainder (width 0))))
          ("Subgoal *1/2" :use ((:instance data-low-bits-of-two-fields
                                           (lower (* 8 (1- count))) (upper 8))
                                (:instance data-two-power-of-sum
                                           (lower (* 8 (1- count))) (upper 8))
                                (:instance data-swap-front-factors
                                           (a (data-little-endian-value tail)) (b 256)
                                           (c (expt 2 (* 8 (1- count)))))))))

(local
 (defthm prepend-word-preserves-byte-characters
   (implies (character-listp tail)
            (character-listp (boymoo-compiler::prepend-word word count tail)))
   :hints (("Goal" :induct (boymoo-compiler::prepend-word word count tail)))))

(defthmd data-read-serialized-word
  (implies (integerp word)
           (equal (data-characters-read-word (boymoo-compiler::prepend-word word 8 nil))
                  (boymoo-compiler::low-bits word 64)))
  :hints (("Goal" :use ((:instance data-prepend-word-little-endian-value (count 8) (tail nil)))
                  :in-theory (disable boymoo-compiler::prepend-word data-characters-read-word))))

(local
 (defthm low-bit-tag-of-doubled-integer
   (implies (integerp integer)
            (equal (boymoo-compiler::low-bits (+ 1 (* 2 integer)) 64)
                   (+ 1 (* 2 (boymoo-compiler::low-bits integer 63)))))
   :hints (("Goal" :use ((:instance data-low-bits-in-range (word integer) (width 63))
                        (:instance data-low-bits-remainder (word integer) (width 63))
                        (:instance data-low-bits-unique
                                   (word (+ 1 (* 2 integer))) (width 64)
                                   (q (floor integer (expt 2 63)))
                                   (residue (+ 1 (* 2 (boymoo-compiler::low-bits integer 63))))))
                   :in-theory (disable data-low-bits-in-range)))))

(defthmd data-read-serialized-immediate-word
  (implies (integerp integer)
           (equal (data-characters-read-word (boymoo-compiler::prepend-integer integer nil))
                  (proof-integer-word integer)))
  :hints (("Goal" :use ((:instance data-low-bits-of-two-fields (word integer) (lower 7) (upper 56))
                       (:instance data-low-bits-in-range (word integer) (width 7))
                       (:instance data-prepend-word-little-endian-value
                                  (word (ash integer -7)) (count 7) (tail nil)))
                  :in-theory (e/d (data-machine-unsigned-is-low-bits)
                                 (boymoo-compiler::prepend-word data-characters-read-word
                                  data-low-bits-in-range boymoo-model::a64-unsigned)))))

(local
 (defthm serialized-word-has-eight-characters
   (implies (integerp word)
            (equal (len (boymoo-compiler::prepend-word word 8 nil)) 8))
   :hints (("Goal" :use ((:instance data-chunk-characters-size (chunk word)))
                   :in-theory (disable data-chunk-characters-size boymoo-compiler::prepend-word)))))

(defthmd data-load-serialized-word
  (implies (and (integerp word) (integerp address)
                (data-placed-characters-p (boymoo-compiler::prepend-word word 8 nil) address machine))
           (equal (proof-load-word address machine) (boymoo-compiler::low-bits word 64)))
  :hints (("Goal" :use ((:instance data-load-placed-word
                                   (characters (boymoo-compiler::prepend-word word 8 nil)))
                       data-read-serialized-word)
                  :in-theory (disable boymoo-compiler::prepend-word data-characters-read-word
                                      data-placed-characters-p boymoo-model::a64-load))))

(defthm data-image-produced-by-data-build-has-header
  (implies (proof-image-p (car (boymoo-compiler::data-build lines package-lines)))
           (car (data-image-parts lines package-lines)))
  :hints (("Goal" :use data-build-image-and-index
                  :in-theory (disable data-image-parts boymoo-compiler::data-build
                                      proof-fragments-size proof-fragments-p
                                      boymoo-compiler::data-write boymoo-compiler::reverse-onto))))

(defthmd data-build-loads-header-field
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (header (car (data-image-parts lines package-lines)))
         (word (nth field header))
         (address (+ base (* 8 field))))
    (implies (and (proof-image-at-p image base machine) (natp field) (< field 10)
                  (unsigned-byte-p 64 word))
             (equal (proof-load-word address machine) word)))
  :hints (("Goal" :use (data-build-places-header
                       (:instance data-placed-word-chunk-at-index
                                  (chunks (car (data-image-parts lines package-lines))) (index field))
                       (:instance data-load-serialized-word
                                  (word (nth field (car (data-image-parts lines package-lines))))
                                  (address (+ base (* 8 field)))))
                  :in-theory (disable data-image-parts boymoo-compiler::data-build
                                      proof-fragments-at-p proof-image-p proof-load-word
                                      data-placed-characters-p boymoo-compiler::prepend-word))))

(defthmd data-build-loads-static-size
  (let ((image (car (boymoo-compiler::data-build lines package-lines))))
    (implies (and (proof-image-at-p image base machine) (unsigned-byte-p 64 (car image)))
             (equal (proof-static-size base machine) (car image))))
  :hints (("Goal" :use ((:instance data-build-loads-header-field (field 0))
                       data-build-image-and-index)
                  :in-theory (disable data-image-parts boymoo-compiler::data-build
                                      proof-fragments-at-p proof-image-p proof-load-word
                                      boymoo-compiler::data-write boymoo-compiler::reverse-onto))))
