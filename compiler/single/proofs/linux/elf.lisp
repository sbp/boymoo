(in-package "BOYMOO-PROOFS")

; The executable file that ELF-IMAGE-EXECUTABLE writes is accepted by the
; loader's recognizer PROOF-ELF-P, and its characters are the header
; followed by the characters of the image fragments.

(include-book "../foundations/interfaces")
(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

; The characters of a list of string fragments, in order.
(defun linux-fragment-characters (fragments)
  (if (atom fragments)
      nil
    (append (coerce (car fragments) 'list)
            (linux-fragment-characters (cdr fragments)))))

; The little-endian number held in the first COUNT characters of CHARS.
(defun linux-le-list (count chars)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (char-code (car chars))
       (* 256 (linux-le-list (1- count) (cdr chars))))))

;;; Image strings

(local
 (defun linux-prepend-induction (s i chars)
   (declare (xargs :measure (nfix i)))
   (if (zp i)
       (list s chars)
     (linux-prepend-induction s (- i 1) (cons (char s (- i 1)) chars)))))

(local
 (defthm linux-take-one-more
   (implies (natp i)
            (equal (take (+ 1 i) xs)
                   (append (take i xs) (list (nth i xs)))))
   :hints (("Goal" :induct (take i xs)))))

(local
 (defthm linux-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm linux-take-zero
   (equal (take 0 xs) nil)))

(local
 (defthm linux-image-prepend-chars
   (implies (natp i)
            (equal (boymoo-compiler::image-prepend-chars s i chars)
                   (append (take i (coerce s 'list)) chars)))
   :hints (("Goal" :induct (linux-prepend-induction s i chars)
                   :in-theory (disable take))
           ("Subgoal *1/2"
            :use ((:instance linux-take-one-more (i (- i 1)) (xs (coerce s 'list))))))))

(local
 (defthm linux-take-of-len
   (implies (true-listp xs)
            (equal (take (len xs) xs) xs))
   :hints (("Goal" :induct (len xs)
                   :in-theory (disable linux-take-one-more)))))

(local
 (defthm linux-image-prepend-whole-string
   (implies (stringp s)
            (equal (boymoo-compiler::image-prepend-chars s (len (coerce s (quote list))) chars)
                   (append (coerce s 'list) chars)))
   :hints (("Goal" :in-theory (disable linux-take-one-more)))))

(local
 (defthm linux-fragment-characters-onto
   (implies (proof-fragments-p fragments)
            (equal (boymoo-compiler::image-characters
                    (boymoo-compiler::reverse-onto fragments reversed) chars)
                   (boymoo-compiler::image-characters
                    reversed (append (linux-fragment-characters fragments) chars))))
   :hints (("Goal"
            :induct (boymoo-compiler::reverse-onto fragments reversed)
            :in-theory (disable linux-image-prepend-chars)))))

(defthm linux-character-listp-of-fragment-characters
  (character-listp (linux-fragment-characters fragments)))

(defthm linux-image-string-characters
  (implies (proof-fragments-p fragments)
           (equal (boymoo-compiler::image-string fragments)
                  (coerce (linux-fragment-characters fragments) 'string))))

(defthm linux-fragment-characters-length
  (implies (proof-fragments-p fragments)
           (equal (len (linux-fragment-characters fragments))
                  (proof-fragments-size fragments))))

(defthm linux-image-string-length
  (implies (proof-fragments-p fragments)
           (equal (length (boymoo-compiler::image-string fragments))
                  (proof-fragments-size fragments))))

;;; Little-endian fields

(local
 (defthm linux-car-nthcdr
   (equal (car (nthcdr i l)) (nth i l))))

(local
 (defthm linux-cdr-nthcdr
   (implies (natp i)
            (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))))

(defthm linux-file-le-as-list
  (implies (and (stringp file) (natp index))
           (equal (proof-file-le count index file)
                  (linux-le-list count (nthcdr index (coerce file 'list)))))
  :hints (("Goal" :induct (proof-file-le count index file))))

(defthm linux-prepend-le-append
  (equal (append (boymoo-compiler::elf-prepend-le w n acc) c)
         (boymoo-compiler::elf-prepend-le w n (append acc c))))

(defthm linux-prepend-zeroes-append
  (equal (append (boymoo-compiler::elf-prepend-zeroes n acc) c)
         (boymoo-compiler::elf-prepend-zeroes n (append acc c))))

(defthm linux-prepend-le-len
  (equal (len (boymoo-compiler::elf-prepend-le w n acc))
         (+ (nfix n) (len acc))))

(defthm linux-prepend-zeroes-len
  (equal (len (boymoo-compiler::elf-prepend-zeroes n acc))
         (+ (nfix n) (len acc))))

(defthm linux-prepend-le-character-listp
  (equal (character-listp (boymoo-compiler::elf-prepend-le w n acc))
         (character-listp acc)))

(defthm linux-prepend-zeroes-character-listp
  (equal (character-listp (boymoo-compiler::elf-prepend-zeroes n acc))
         (character-listp acc)))

(local
 (defun linux-prepend-le-induction (w n acc i)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list w acc i)
     (linux-prepend-le-induction (ash w -8) (- n 1) acc (- i 1)))))

(defthm linux-prepend-le-nthcdr
  (implies (and (natp i) (natp n) (<= n i))
           (equal (nthcdr i (boymoo-compiler::elf-prepend-le w n acc))
                  (nthcdr (- i n) acc)))
  :hints (("Goal" :induct (linux-prepend-le-induction w n acc i))))

(defthm linux-prepend-zeroes-nthcdr
  (implies (and (natp i) (natp n) (<= n i))
           (equal (nthcdr i (boymoo-compiler::elf-prepend-zeroes n acc))
                  (nthcdr (- i n) acc)))
  :hints (("Goal" :induct (linux-prepend-le-induction w n acc i))))

(local
 (defthm linux-prepend-zeroes-step
   (implies (not (zp n))
            (equal (boymoo-compiler::elf-prepend-zeroes n acc)
                   (cons (code-char 0)
                         (boymoo-compiler::elf-prepend-zeroes (- n 1) acc))))
   :rule-classes nil
   :hints (("Goal" :induct (boymoo-compiler::elf-prepend-zeroes n acc)))))

(local
 (defun linux-count-induction (n)
   (if (zp n) n (linux-count-induction (- n 1)))))

(defthm linux-le-list-of-prepend-zeroes
  (equal (linux-le-list n (boymoo-compiler::elf-prepend-zeroes n acc)) 0)
  :hints (("Goal" :induct (linux-count-induction n)
                  :in-theory (disable boymoo-compiler::elf-prepend-zeroes))
          ("Subgoal *1/2" :use linux-prepend-zeroes-step)))

(defthm linux-le-list-of-prepend-le
  (implies (and (natp w) (< w (expt 256 n)))
           (equal (linux-le-list n (boymoo-compiler::elf-prepend-le w n acc))
                  w))
  :hints (("Goal" :induct (boymoo-compiler::elf-prepend-le w n acc)
                  :in-theory (disable linux-floor-bounds))
          ("Subgoal *1/2" :use ((:instance linux-floor-bounds (x (* 1/256 w)))))))

(in-theory (disable boymoo-compiler::elf-prepend-le
                    boymoo-compiler::elf-prepend-zeroes
                    (:executable-counterpart boymoo-compiler::elf-prepend-le)
                    (:executable-counterpart boymoo-compiler::elf-prepend-zeroes)))

(defthm linux-prepend-header-append
  (equal (append (boymoo-compiler::elf-prepend-header entry size acc) c)
         (boymoo-compiler::elf-prepend-header entry size (append acc c))))

(defthm linux-prepend-header-len
  (equal (len (boymoo-compiler::elf-prepend-header entry size acc))
         (+ 4096 (len acc))))

(defthm linux-prepend-header-character-listp
  (equal (character-listp (boymoo-compiler::elf-prepend-header entry size acc))
         (character-listp acc)))

(defthm linux-prepend-header-body
  (equal (nthcdr 4096 (boymoo-compiler::elf-prepend-header entry size acc))
         acc))

(in-theory (disable boymoo-compiler::elf-prepend-header))

;;; The executable file

(defthm linux-elf-image-executable-characters
  (implies (and (proof-image-p image)
                (natp entry)
                (equal (mod entry 4) 0)
                (<= (+ entry 4) (car image)))
           (equal (coerce (boymoo-compiler::elf-image-executable image entry) 'list)
                  (boymoo-compiler::elf-prepend-header
                   (+ *proof-linux-code-base* entry)
                   (+ *proof-linux-code-offset* (car image))
                   (linux-fragment-characters (cdr image))))))

(in-theory (disable boymoo-compiler::elf-image-executable))

; The hypotheses say that the image is well formed, that the entry offset
; is a multiple of four with a whole instruction after it in the image,
; and that the loaded file ends below 2^63.
(defun linux-elf-arguments-p (image entry)
  (and (proof-image-p image)
       (natp entry)
       (equal (mod entry 4) 0)
       (<= (+ entry 4) (car image))
       (<= (+ *proof-linux-code-base* (car image)) (expt 2 63))))

(defthm linux-elf-image-executable-length
  (implies (linux-elf-arguments-p image entry)
           (equal (length (boymoo-compiler::elf-image-executable image entry))
                  (+ *proof-linux-code-offset* (car image)))))

(defthm linux-elf-image-executable-code
  (implies (linux-elf-arguments-p image entry)
           (equal (nthcdr *proof-linux-code-offset*
                          (coerce (boymoo-compiler::elf-image-executable image entry)
                                  'list))
                  (linux-fragment-characters (cdr image)))))

(defthm linux-elf-image-executable-entry
  (implies (linux-elf-arguments-p image entry)
           (equal (proof-elf-entry (boymoo-compiler::elf-image-executable image entry))
                  (+ *proof-linux-code-base* entry)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::elf-prepend-header))))

(defthm linux-elf-image-executable-accepted
  (implies (linux-elf-arguments-p image entry)
           (proof-elf-p (boymoo-compiler::elf-image-executable image entry)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::elf-prepend-header))))

; The writer, like PROOF-ELF-P, asks for a whole four-byte instruction at
; the entry. For a five-byte image with its entry at offset 4 it writes
; the empty string, as it does for every entry that it refuses.
(defthm linux-entry-check-example
  (equal (boymoo-compiler::elf-image-executable
          (cons 5 (list (coerce (list #\a #\b #\c #\d #\e) 'string)))
          4)
         "")
  :hints (("Goal" :in-theory (enable boymoo-compiler::elf-image-executable))))
