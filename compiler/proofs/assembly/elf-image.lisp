(in-package "BOYMOO-PROOFS")

(include-book "image-decoding")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash floor mod expt
                           assembly-high assembly-low assembly-cat assembly-power-of-two
                           boymoo-compiler::image-string
                           assembly-fragment-characters proof-fragments-p)))

(defun assembly-read-le-characters (count characters)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (char-code (car characters))
       (* 256 (assembly-read-le-characters (1- count) (cdr characters))))))

(local
 (defthm assembly-car-of-nthcdr
   (equal (car (nthcdr index chars)) (nth index chars))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-cdr-commutes-with-nthcdr
   (equal (cdr (nthcdr index chars)) (nthcdr index (cdr chars)))
   :hints (("Goal" :induct (nthcdr index chars)))))

(defthm assembly-file-le-reads-characters
  (implies (and (stringp file) (natp index))
           (equal (proof-file-le count index file)
                  (assembly-read-le-characters count (nthcdr index (coerce file 'list)))))
  :hints (("Goal" :induct (proof-file-le count index file))
          ("Subgoal *1/2"
           :expand ((assembly-read-le-characters count (nthcdr index (coerce file 'list)))))))

(local
 (defthm assembly-elf-low-byte
   (implies (integerp word)
            (equal (- word (* 256 (assembly-high 8 word)))
                   (assembly-low 8 word)))
   :hints (("Goal"
            :use ((:instance assembly-cat-of-low-and-high (width 8) (x word)))
            :in-theory (e/d (assembly-cat) (assembly-cat-of-low-and-high))))))

(local
 (defthm assembly-elf-leading-byte
   (implies (and (posp count) (integerp word))
            (equal (boymoo-compiler::elf-prepend-le word count rest)
                   (cons (code-char (assembly-low 8 word))
                         (boymoo-compiler::elf-prepend-le
                          (assembly-high 8 word) (1- count) rest))))))

(local
 (defthm assembly-elf-high-fits-field
   (implies (and (posp count) (unsigned-byte-p (* 8 count) word))
            (unsigned-byte-p (* 8 (1- count)) (assembly-high 8 word)))
   :hints (("Goal"
            :use ((:instance assembly-power-of-two-of-sum (a 8) (b (* 8 (1- count))))
                  (:instance assembly-floor-bounds (x word) (d 256)))
            :in-theory (e/d (assembly-high)
                            (unsigned-byte-p assembly-power-of-two-of-sum))))))

(defthm assembly-elf-field-characters-p
  (implies (character-listp rest)
           (character-listp (boymoo-compiler::elf-prepend-le word count rest))))

(defthm assembly-length-of-elf-field
  (equal (len (boymoo-compiler::elf-prepend-le word count rest))
         (+ (nfix count) (len rest))))

(local
 (defthm assembly-elf-field-append
   (equal (append (boymoo-compiler::elf-prepend-le word count chars) rest)
          (boymoo-compiler::elf-prepend-le word count (append chars rest)))))

(local
 (defthm assembly-elf-zero-padding-field
   (equal (boymoo-compiler::elf-prepend-zeroes count rest)
          (boymoo-compiler::elf-prepend-le 0 count rest))))

(local
 (defun assembly-elf-field-skip-induction (word count index)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (list word index)
     (assembly-elf-field-skip-induction (ash word -8) (1- count) (1- index)))))

(defthm assembly-nthcdr-past-elf-field
  (implies (and (natp count) (natp index) (<= count index))
           (equal (nthcdr index (boymoo-compiler::elf-prepend-le word count rest))
                  (nthcdr (- index count) rest)))
  :hints (("Goal" :induct (assembly-elf-field-skip-induction word count index)
                  :in-theory (disable assembly-elf-leading-byte))))

(defthm assembly-elf-field-round-trip
  (implies (and (natp count) (unsigned-byte-p (* 8 count) word))
           (equal (assembly-read-le-characters
                   count (boymoo-compiler::elf-prepend-le word count rest))
                  word))
  :hints (("Goal"
           :induct (boymoo-compiler::elf-prepend-le word count rest)
           :in-theory (disable (:definition boymoo-compiler::elf-prepend-le)
                               assembly-elf-low-byte
                               acl2::char-code-code-char-is-identity))
          ("Subgoal *1/2"
           :use ((:instance assembly-cat-of-low-and-high (width 8) (x word))
                 (:instance acl2::char-code-code-char-is-identity
                            (acl2::n (assembly-low 8 word)))
                 (:instance assembly-low-bounds (width 8) (value word))
                 assembly-elf-high-fits-field)
           :in-theory (e/d (assembly-cat)
                           (assembly-cat-of-low-and-high
                            unsigned-byte-p assembly-elf-high-fits-field)))))

(local (in-theory (disable boymoo-compiler::elf-prepend-le
                           boymoo-compiler::elf-prepend-zeroes
                           (:executable-counterpart boymoo-compiler::elf-prepend-le)
                           (:executable-counterpart boymoo-compiler::elf-prepend-zeroes)
                           assembly-elf-leading-byte
                           assembly-read-le-characters)))

(defun assembly-elf-image-entry-p (image offset)
  (and (proof-image-p image)
       (natp offset) (equal (mod offset 4) 0)
       (<= (+ offset 4) (car image))
       (<= (+ *proof-linux-code-base* (car image)) (expt 2 63))))

(defthm assembly-elf-word-alignment
  (implies (and (natp offset) (equal (mod offset 4) 0))
           (equal (ash (ash offset -2) 2) offset))
  :hints (("Goal"
           :use ((:instance assembly-cat-of-low-and-high (width 2) (x offset))
                 (:instance assembly-floor-bounds (x offset) (d 4)))
           :in-theory (e/d (assembly-cat mod assembly-low assembly-high)
                           (assembly-cat-of-low-and-high)))))

(local
 (defthm assembly-elf-base-alignment
   (implies (and (natp offset) (equal (mod offset 4) 0))
            (equal (mod (+ *proof-linux-code-base* offset) 4) 0))
   :hints (("Goal"
            :use ((:instance assembly-floor-unique
                             (x (+ *proof-linux-code-base* offset)) (d 4)
                             (q (+ (/ *proof-linux-code-base* 4) (floor offset 4)))))
            :in-theory (enable mod)))))

(local
 (defthm assembly-elf-header-preserves-characters
   (implies (character-listp characters)
            (character-listp (boymoo-compiler::elf-prepend-header entry size characters)))))

(local
 (defthm assembly-elf-header-append
   (equal (append (boymoo-compiler::elf-prepend-header entry size nil) characters)
          (boymoo-compiler::elf-prepend-header entry size characters))))

(local
 (defthm assembly-elf-appends-image-characters
   (implies (assembly-elf-image-entry-p image offset)
            (equal (coerce (boymoo-compiler::elf-image-executable image offset) 'list)
                   (boymoo-compiler::elf-prepend-header
                    (+ *proof-linux-code-base* offset)
                    (+ *proof-linux-code-offset* (car image))
                    (assembly-fragment-characters (cdr image)))))
   :hints (("Goal"
            :use (assembly-elf-word-alignment)
            :in-theory (e/d (proof-fragments-p assembly-fragment-characters)
                            (boymoo-compiler::elf-prepend-header
                             assembly-elf-word-alignment assembly-ash-right-constant assembly-ash-left))))))

(defthm assembly-elf-image-file
  (let ((file (boymoo-compiler::elf-image-executable image offset)))
    (implies (assembly-elf-image-entry-p image offset)
             (and (proof-elf-p file)
                  (equal (proof-elf-entry file) (+ *proof-linux-code-base* offset))
                  (equal (length file) (+ *proof-linux-code-offset* (car image)))
                  (equal (nthcdr *proof-linux-code-offset* (coerce file 'list))
                         (assembly-fragment-characters (cdr image))))))
  :hints (("Goal"
           :use (assembly-elf-appends-image-characters)
           :in-theory (disable assembly-elf-appends-image-characters
                               boymoo-compiler::elf-image-executable
                               proof-file-le))))

(in-theory (disable assembly-read-le-characters assembly-file-le-reads-characters
                    assembly-elf-field-characters-p assembly-length-of-elf-field
                    assembly-nthcdr-past-elf-field
                    assembly-elf-field-round-trip))

(in-theory (disable assembly-elf-word-alignment))
