(in-package "BOYMOO-PROOFS")

(include-book "macho-header")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-macho-image-text-size (image)
  (boymoo-compiler::macho-segment-size (+ *assembly-macho-code-offset* (car image))))

(defun assembly-macho-slot-count (text-size)
  (floor text-size 4096))

(defconst *assembly-macho-signature-hash-offset* 115)

(defun assembly-macho-image-entry-p (image entry)
  (and (proof-image-p image)
       (natp entry)
       (equal (mod entry 4) 0)
       (<= (+ entry 4) (car image))
       (< (assembly-macho-image-text-size image) (expt 2 32))))

(local (in-theory (disable ash floor mod assembly-power-of-two)))

(local
 (defthm assembly-macho-blob-size-formula
   (implies (natp slots)
            (equal (boymoo-compiler::macho-blob-size slots) (+ 115 (* 32 slots))))))

(defthm assembly-macho-signature-size-formula
  (implies (natp slots)
           (equal (boymoo-compiler::macho-signature-size slots) (+ 128 (* 32 slots))))
  :hints (("Goal"
           :use ((:instance assembly-floor-unique
                            (x (+ 130 (* 32 slots))) (d 16) (q (+ 8 (* 2 slots)))))
           :in-theory (enable assembly-high))))

(local (in-theory (disable boymoo-compiler::macho-signature-size)))

(defthm assembly-macho-image-file-parameters
  (let* ((size (assembly-macho-image-text-size image))
         (slots (assembly-macho-slot-count size)))
    (implies (assembly-macho-image-entry-p image entry)
             (and (natp size)
                  (<= (+ *assembly-macho-code-offset* (car image)) size)
                  (posp slots)
                  (unsigned-byte-p 32 size)
                  (unsigned-byte-p 32 (+ *assembly-macho-code-offset* entry))
                  (unsigned-byte-p 32 (boymoo-compiler::macho-signature-size slots)))))
  :hints (("Goal"
           :use ((:instance assembly-macho-segment-rounding
                            (bytes (+ *assembly-macho-code-offset* (car image))))
                 (:instance assembly-floor-bounds (x (assembly-macho-image-text-size image)) (d 4096)))
           :in-theory (e/d (assembly-macho-slot-count)
                           (boymoo-compiler::macho-segment-size)))))

(local
 (defthm assembly-sha256-add-states-preserves-count
   (equal (len (boymoo-compiler::sha256-add-states left right)) (len left))))

(local
 (defthm assembly-sha256-compress-preserves-count
   (equal (len (boymoo-compiler::sha256-compress words digest)) (len digest))
   :hints (("Goal" :in-theory (disable boymoo-compiler::sha256-add-states
                                       boymoo-compiler::sha256-rounds)))))

(local
 (defthm assembly-sha256-blocks-preserves-count
   (equal (len (boymoo-compiler::sha256-blocks text at count end message-end padded-end bits digest))
          (len digest))
   :hints (("Goal"
            :induct (boymoo-compiler::sha256-blocks text at count end message-end padded-end bits digest)
            :in-theory (disable boymoo-compiler::sha256-compress boymoo-compiler::sha256-block-words)))))

(local
 (defthm assembly-sha256-range-word-count
   (equal (len (boymoo-compiler::sha256-range-words text start end message-end)) 8)
   :hints (("Goal" :in-theory (disable boymoo-compiler::sha256-blocks)))))

(local
 (defthm assembly-sha256-page-word-count
   (equal (len (mv-nth 0 (boymoo-compiler::sha256-page chunks at size))) 8)
   :hints (("Goal" :in-theory (disable boymoo-compiler::sha256-range-words
                                       boymoo-compiler::sha256-page-pieces
                                       boymoo-compiler::image-string)))))

(local
 (defthm assembly-length-of-sha256-big-endian-field
   (equal (len (boymoo-compiler::sha256-prepend-be word count acc))
          (+ (nfix count) (len acc)))))

(local
 (defthm assembly-sha256-big-endian-characters
   (implies (character-listp acc)
            (character-listp (boymoo-compiler::sha256-prepend-be word count acc)))))

(local (in-theory (disable boymoo-compiler::sha256-prepend-be)))

(local
 (defthm assembly-length-of-macho-big-endian-fields
   (equal (len (boymoo-compiler::macho-prepend-be32s words acc)) (+ (* 4 (len words)) (len acc)))))

(local
 (defthm assembly-macho-big-endian-characters
   (implies (character-listp acc)
            (character-listp (boymoo-compiler::macho-prepend-be32s words acc)))))

(local
 (defthm assembly-length-of-sha256-serialized-digest
   (equal (len (boymoo-compiler::sha256-prepend-digest words acc))
          (+ (* 4 (len words)) (len acc)))))

(defthm assembly-sha256-digest-characters
  (implies (character-listp acc)
           (character-listp (boymoo-compiler::sha256-prepend-digest words acc))))

(local
 (defthm assembly-string-length-of-characters
   (implies (character-listp chars)
            (equal (length (coerce chars 'string)) (len chars)))))

(local
 (defthm assembly-sha256-digest-string-length
   (equal (length (coerce (boymoo-compiler::sha256-prepend-digest words nil) 'string))
          (* 4 (len words)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::sha256-prepend-digest length)))))

(local (in-theory (disable boymoo-compiler::macho-blob-size
                           boymoo-compiler::sha256-range-words boymoo-compiler::sha256-prepend-digest
                           boymoo-compiler::macho-prepend-padded-name boymoo-compiler::macho-prepend-be32s
                           boymoo-compiler::macho-prepend-zeroes
                           (:executable-counterpart boymoo-compiler::macho-prepend-zeroes))))

(local
 (defthm assembly-macho-signature-prefix-length
   (equal (length (boymoo-compiler::macho-signature-prefix header text-size slots)) 147)
   :hints (("Goal"
            :in-theory (e/d (assembly-length-of-macho-prepended-zeroes
                             assembly-macho-prepend-zeroes-characters
                             assembly-length-of-macho-padded-name assembly-macho-padded-name-characters)
                            (length))))))

(local
 (defthm assembly-nthcdr-past-sha256-big-endian-field
   (implies (and (natp width) (natp offset) (<= width offset))
            (equal (nthcdr offset (boymoo-compiler::sha256-prepend-be word width chars))
                   (nthcdr (- offset width) chars)))
   :hints (("Goal"
            :induct (boymoo-compiler::sha256-prepend-be word width chars)
            :in-theory (enable boymoo-compiler::sha256-prepend-be)))))

(local
 (defun assembly-macho-skip-fields-induction (words offset)
   (if (atom words)
       offset
     (assembly-macho-skip-fields-induction (cdr words) (- offset 4)))))

(local
 (defthm assembly-nthcdr-past-macho-big-endian-fields
   (implies (and (natp offset) (<= (* 4 (len words)) offset))
            (equal (nthcdr offset (boymoo-compiler::macho-prepend-be32s words chars))
                   (nthcdr (- offset (* 4 (len words))) chars)))
   :hints (("Goal" :induct (assembly-macho-skip-fields-induction words offset)
                   :in-theory (enable boymoo-compiler::macho-prepend-be32s)))))

(defthm assembly-macho-signature-prefix-contains-header-hash
  (equal (nthcdr *assembly-macho-signature-hash-offset*
                  (coerce (boymoo-compiler::macho-signature-prefix header text-size slots) 'list))
         (boymoo-compiler::sha256-prepend-digest
          (boymoo-compiler::sha256-range-words
           header 0 *assembly-macho-code-offset* *assembly-macho-code-offset*)
          nil))
  :hints (("Goal"
           :in-theory (enable assembly-macho-prepend-zeroes-characters
                              assembly-macho-padded-name-characters
                              assembly-nthcdr-past-macho-prepended-zeroes
                              assembly-nthcdr-past-macho-padded-name)))
  :rule-classes nil)

(local
 (defthm assembly-fragment-size-of-reverse-onto
   (equal (proof-fragments-size (boymoo-compiler::reverse-onto chunks tail))
          (+ (proof-fragments-size chunks) (proof-fragments-size tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto chunks tail)))))

(local
 (defthm assembly-fragments-p-of-reverse-onto
   (implies (and (proof-fragments-p chunks) (proof-fragments-p tail))
            (proof-fragments-p (boymoo-compiler::reverse-onto chunks tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto chunks tail)))))

(local (in-theory (disable boymoo-compiler::reverse-onto boymoo-compiler::sha256-page
                           boymoo-compiler::macho-signature-prefix
                           boymoo-compiler::macho-header)))

(local
 (defthm assembly-macho-code-slots-fragments
   (implies (proof-fragments-p digests)
            (proof-fragments-p (boymoo-compiler::macho-code-slots chunks at count digests)))
   :hints (("Goal" :induct (boymoo-compiler::macho-code-slots chunks at count digests)))))

(local
 (defthm assembly-macho-code-slots-size
   (equal (proof-fragments-size (boymoo-compiler::macho-code-slots chunks at count digests))
          (+ (* 32 (nfix count)) (proof-fragments-size digests)))
   :hints (("Goal" :induct (boymoo-compiler::macho-code-slots chunks at count digests)
                   :in-theory (disable length mv-nth)))))

(local
 (defthm assembly-leading-zero-commutes-with-zero-prefix
   (equal (append (assembly-zero-characters count) (cons (code-char 0) chars))
          (cons (code-char 0) (append (assembly-zero-characters count) chars)))))

(local
 (defthm assembly-macho-image-zeroes-from-characters
   (implies (character-listp chars)
            (equal (boymoo-compiler::image-zeroes count chars)
                   (coerce (append (assembly-zero-characters count) chars) 'string)))
   :hints (("Goal" :induct (boymoo-compiler::image-zeroes count chars)))))

(local
 (defthm assembly-macho-padding-fragments
   (implies (proof-fragments-p chunks)
            (proof-fragments-p (boymoo-compiler::image-padding count chunks)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::image-zeroes)))))

(local
 (defthm assembly-macho-zero-characters-are-characters
   (character-listp (assembly-zero-characters count))))

(local
 (defthm assembly-macho-zero-character-count
   (equal (len (assembly-zero-characters count)) (nfix count))))

(local
 (defthm assembly-macho-padding-size
   (equal (proof-fragments-size (boymoo-compiler::image-padding count chunks))
          (+ (nfix count) (proof-fragments-size chunks)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::image-zeroes length)))))

(local
 (defthm assembly-macho-image-onto-fragments
   (implies (and (proof-fragments-p chunks) (proof-fragments-p tail))
            (proof-fragments-p (boymoo-compiler::image-onto chunks tail)))))

(local
 (defthm assembly-macho-image-onto-size
   (implies (proof-fragments-p tail)
            (equal (proof-fragments-size (boymoo-compiler::image-onto chunks tail))
                   (+ (proof-fragments-size chunks) (proof-fragments-size tail))))))

(defun assembly-macho-signature-fragments (header image text-size)
  (let* ((slots (assembly-macho-slot-count text-size))
         (sig-size (boymoo-compiler::macho-signature-size slots))
         (digests (boymoo-compiler::macho-code-slots (cdr image) 0 (1- slots) nil))
         (padding (- sig-size (boymoo-compiler::macho-blob-size slots))))
    (cons (boymoo-compiler::macho-signature-prefix header text-size slots)
          (boymoo-compiler::image-onto digests (boymoo-compiler::image-padding padding nil)))))

(defthm assembly-macho-signature-fragments-size
  (let ((slots (assembly-macho-slot-count text-size))
        (fragments (assembly-macho-signature-fragments header image text-size)))
    (implies (posp slots)
             (and (proof-fragments-p fragments)
                  (equal (proof-fragments-size fragments)
                         (boymoo-compiler::macho-signature-size slots)))))
  :hints (("Goal"
           :in-theory (disable boymoo-compiler::macho-code-slots boymoo-compiler::image-onto
                               boymoo-compiler::image-padding length))))

(local
 (defthm assembly-macho-fragments-of-append
   (implies (and (proof-fragments-p chunks) (proof-fragments-p tail))
            (proof-fragments-p (append chunks tail)))))

(local
 (defthm assembly-macho-flatten-first-fragment
   (equal (assembly-fragment-characters (cons fragment rest))
          (append (coerce fragment 'list) (assembly-fragment-characters rest)))))

(local
 (defthm assembly-macho-flatten-fragment-append
   (equal (assembly-fragment-characters (append chunks tail))
          (append (assembly-fragment-characters chunks) (assembly-fragment-characters tail)))))

(local
 (defthm assembly-macho-reverse-onto
   (equal (boymoo-compiler::reverse-onto chunks tail) (revappend chunks tail))
   :hints (("Goal" :in-theory (enable boymoo-compiler::reverse-onto)))))

(local
 (defthm assembly-macho-reverse-chunks-twice
   (equal (revappend (revappend chunks middle) tail)
          (revappend middle (append chunks tail)))
   :hints (("Goal" :induct (revappend chunks middle)))))

(local
 (defthm assembly-macho-onto-preserves-fragment-order
   (implies (and (proof-fragments-p chunks) (proof-fragments-p tail))
            (equal (boymoo-compiler::image-onto chunks tail)
                   (append chunks tail)))))

(local
 (defthm assembly-macho-fragment-padding-bytes
   (equal (assembly-fragment-characters (boymoo-compiler::image-padding count chunks))
          (append (assembly-zero-characters count) (assembly-fragment-characters chunks)))))

(local
 (defthm assembly-macho-signature-drop-prefix-characters
   (implies (and (natp count) (<= count (len prefix)))
            (equal (nthcdr count (append prefix tail))
                   (append (nthcdr count prefix) tail)))
   :hints (("Goal" :induct (nthcdr count prefix)))))

(local
 (defthm assembly-macho-signature-prefix-character-count
   (equal (len (coerce (boymoo-compiler::macho-signature-prefix header size slots) 'list)) 147)
   :hints (("Goal"
            :use ((:instance assembly-macho-signature-prefix-length (text-size size)))
            :in-theory (disable assembly-macho-signature-prefix-length)))))

(defthm assembly-macho-signature-hash-tail
  (let* ((slots (assembly-macho-slot-count size))
         (digest (boymoo-compiler::sha256-range-words
                  header 0 *assembly-macho-code-offset* *assembly-macho-code-offset*)))
    (implies (posp slots)
             (equal (nthcdr *assembly-macho-signature-hash-offset*
                             (assembly-fragment-characters
                              (assembly-macho-signature-fragments header image size)))
                    (append (boymoo-compiler::sha256-prepend-digest digest nil)
                            (assembly-fragment-characters
                             (boymoo-compiler::macho-code-slots (cdr image) 0 (1- slots) nil))
                            (assembly-zero-characters 13)))))
  :hints (("Goal"
           :use ((:instance assembly-macho-signature-prefix-contains-header-hash
                            (text-size size) (slots (assembly-macho-slot-count size))))
           :in-theory (disable length assembly-macho-slot-count assembly-zero-characters)))
  :rule-classes nil)

(local
 (defthm assembly-macho-coerce-file-characters
   (implies (proof-fragments-p chunks)
            (equal (coerce (boymoo-compiler::image-string chunks) 'list)
                   (assembly-fragment-characters chunks)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::image-string
                                       assembly-fragment-characters)))))

(local
 (defthm assembly-macho-slots-from-aligned-text
   (implies (natp size)
            (equal (ash size -12) (assembly-macho-slot-count size)))
   :hints (("Goal" :in-theory (enable assembly-high)))))

(local (in-theory (disable assembly-macho-signature-fragments assembly-macho-slot-count
                           boymoo-compiler::macho-segment-size
                           boymoo-compiler::macho-code-slots boymoo-compiler::image-string
                           boymoo-compiler::image-padding boymoo-compiler::image-onto
                           assembly-fragment-characters assembly-zero-characters)))

(local
 (defthm assembly-macho-file-fragment-construction
   (let* ((size (assembly-macho-image-text-size image))
          (sig-size (boymoo-compiler::macho-signature-size (assembly-macho-slot-count size)))
          (header (boymoo-compiler::macho-header entry size sig-size))
          (padding (- size (+ *assembly-macho-code-offset* (car image)))))
     (implies (assembly-macho-image-entry-p image entry)
              (equal (boymoo-compiler::macho-image-executable image entry)
                     (boymoo-compiler::image-string
                      (cons header
                            (boymoo-compiler::image-onto
                             (cdr image)
                             (boymoo-compiler::image-padding
                              padding (assembly-macho-signature-fragments header image size))))))))
   :hints (("Goal"
            :in-theory (e/d (assembly-elf-word-alignment assembly-macho-signature-fragments)
                            (assembly-ash-right assembly-ash-right-constant assembly-ash-left))
            :use (assembly-macho-image-file-parameters)))
   :rule-classes nil))

(defthm assembly-macho-image-file-characters
  (let* ((size (assembly-macho-image-text-size image))
         (sig-size (boymoo-compiler::macho-signature-size (assembly-macho-slot-count size)))
         (header (boymoo-compiler::macho-header entry size sig-size))
         (padding (- size (+ *assembly-macho-code-offset* (car image)))))
    (implies (assembly-macho-image-entry-p image entry)
             (equal (coerce (boymoo-compiler::macho-image-executable image entry) 'list)
                    (append (coerce header 'list)
                            (assembly-fragment-characters (cdr image))
                            (assembly-zero-characters padding)
                            (assembly-fragment-characters
                             (assembly-macho-signature-fragments header image size))))))
  :hints (("Goal"
           :use (assembly-macho-file-fragment-construction assembly-macho-image-file-parameters
                 (:instance assembly-macho-signature-fragments-size
                            (text-size (assembly-macho-image-text-size image))
                            (header (boymoo-compiler::macho-header
                                     entry (assembly-macho-image-text-size image)
                                     (boymoo-compiler::macho-signature-size
                                      (assembly-macho-slot-count (assembly-macho-image-text-size image)))))))
           :in-theory (disable boymoo-compiler::macho-image-executable
                               assembly-macho-image-text-size assembly-image-string-characters
                               assembly-macho-signature-fragments-size)))
  :rule-classes nil)

(local (in-theory (disable boymoo-compiler::macho-image-executable)))

(defun assembly-macho-text-characters (header image size)
  (append (coerce header 'list)
          (assembly-fragment-characters (cdr image))
          (assembly-zero-characters (- size (+ *assembly-macho-code-offset* (car image))))))

(local
 (defthm assembly-length-of-appended-characters
   (equal (len (append first rest)) (+ (len first) (len rest)))))

(local
 (defthm assembly-character-list-of-appended-characters
   (implies (and (character-listp first) (character-listp rest))
            (character-listp (append first rest)))))

(local
 (defthm assembly-count-of-macho-header-characters
   (equal (len (coerce (boymoo-compiler::macho-header entry size sig-size) 'list))
          *assembly-macho-code-offset*)
   :hints (("Goal"
            :use ((:instance assembly-macho-header-length (text-size size) (signature-size sig-size)))
            :in-theory (disable assembly-macho-header-length boymoo-compiler::macho-header)))))

(local
 (defthm assembly-macho-text-character-count
   (implies (and (proof-image-p image)
                 (integerp size)
                 (<= (+ *assembly-macho-code-offset* (car image)) size))
            (let ((header (boymoo-compiler::macho-header entry size sig-size)))
              (equal (len (assembly-macho-text-characters header image size)) size)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::macho-header
                                       assembly-fragment-characters)))))

(local
 (defthm assembly-macho-file-character-decomposition
   (let* ((size (assembly-macho-image-text-size image))
          (sig-size (boymoo-compiler::macho-signature-size (assembly-macho-slot-count size)))
          (header (boymoo-compiler::macho-header entry size sig-size)))
     (implies (assembly-macho-image-entry-p image entry)
              (equal (coerce (boymoo-compiler::macho-image-executable image entry) 'list)
                     (append (assembly-macho-text-characters header image size)
                             (assembly-fragment-characters
                              (assembly-macho-signature-fragments header image size))))))
   :hints (("Goal" :use (assembly-macho-image-file-characters)
                   :in-theory (disable assembly-macho-image-entry-p assembly-macho-image-text-size)))
   :rule-classes nil))

(defthm assembly-macho-file-length-and-header
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (size (assembly-macho-image-text-size image))
         (sig-size (boymoo-compiler::macho-signature-size (assembly-macho-slot-count size))))
    (implies (assembly-macho-image-entry-p image entry)
             (and (assembly-macho-header-p file size entry sig-size)
                  (equal (length file) (+ size sig-size)))))
  :hints (("Goal"
           :use (assembly-macho-image-file-characters assembly-macho-image-file-parameters
                 (:instance assembly-macho-header-fields
                            (text-size (assembly-macho-image-text-size image))
                            (signature-size
                             (boymoo-compiler::macho-signature-size
                              (assembly-macho-slot-count (assembly-macho-image-text-size image)))))
                 (:instance assembly-macho-header-with-file-tail
                            (header
                             (boymoo-compiler::macho-header
                              entry (assembly-macho-image-text-size image)
                              (boymoo-compiler::macho-signature-size
                               (assembly-macho-slot-count (assembly-macho-image-text-size image)))))
                            (text-size (assembly-macho-image-text-size image))
                            (signature-size
                             (boymoo-compiler::macho-signature-size
                              (assembly-macho-slot-count (assembly-macho-image-text-size image))))
                            (suffix
                             (append (assembly-fragment-characters (cdr image))
                                     (assembly-zero-characters
                                      (- (assembly-macho-image-text-size image)
                                         (+ *assembly-macho-code-offset* (car image))))
                                     (assembly-fragment-characters
                                      (assembly-macho-signature-fragments
                                       (boymoo-compiler::macho-header
                                        entry (assembly-macho-image-text-size image)
                                        (boymoo-compiler::macho-signature-size
                                         (assembly-macho-slot-count (assembly-macho-image-text-size image))))
                                       image (assembly-macho-image-text-size image)))))))
           :in-theory (disable assembly-macho-header-p assembly-macho-image-text-size
                               assembly-macho-signature-size-formula)))
  :rule-classes nil)

(local
 (defthm assembly-take-of-whole-prefix
   (implies (true-listp prefix)
            (equal (take (len prefix) (append prefix tail)) prefix))
   :hints (("Goal" :induct (len prefix)))))

(local
 (defthm assembly-nthcdr-after-whole-prefix
   (equal (nthcdr (len prefix) (append prefix tail)) tail)
   :hints (("Goal" :induct (len prefix)))))

(local
 (defthm assembly-split-at-characters-of-known-length
   (implies (and (true-listp prefix) (equal count (len prefix))
                 (equal characters (append prefix tail)))
            (and (equal (take count characters) prefix)
                 (equal (nthcdr count characters) tail)))
   :rule-classes nil))

(defthm assembly-macho-file-text-and-signature
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (size (assembly-macho-image-text-size image))
         (sig-size (boymoo-compiler::macho-signature-size (assembly-macho-slot-count size)))
         (header (boymoo-compiler::macho-header entry size sig-size))
         (characters (coerce file 'list))
         (text (assembly-macho-text-characters header image size)))
    (implies (assembly-macho-image-entry-p image entry)
             (and (equal (take size characters) text)
                  (equal (nthcdr size characters)
                         (assembly-fragment-characters
                          (assembly-macho-signature-fragments header image size))))))
  :hints (("Goal"
           :use (assembly-macho-file-character-decomposition assembly-macho-image-file-parameters
                 (:instance assembly-split-at-characters-of-known-length
                            (count (assembly-macho-image-text-size image))
                            (characters (coerce (boymoo-compiler::macho-image-executable image entry) 'list))
                            (prefix
                             (assembly-macho-text-characters
                              (boymoo-compiler::macho-header
                               entry (assembly-macho-image-text-size image)
                               (boymoo-compiler::macho-signature-size
                                (assembly-macho-slot-count (assembly-macho-image-text-size image))))
                              image (assembly-macho-image-text-size image)))
                            (tail
                             (assembly-fragment-characters
                              (assembly-macho-signature-fragments
                               (boymoo-compiler::macho-header
                                entry (assembly-macho-image-text-size image)
                                (boymoo-compiler::macho-signature-size
                                 (assembly-macho-slot-count (assembly-macho-image-text-size image))))
                               image (assembly-macho-image-text-size image))))))
           :in-theory (disable assembly-macho-image-text-size assembly-macho-text-characters
                               assembly-macho-signature-size-formula)))
  :rule-classes nil)

(local
 (defthm assembly-macho-text-characters-after-header
   (equal (nthcdr *assembly-macho-code-offset*
                  (assembly-macho-text-characters
                   (boymoo-compiler::macho-header entry size signature-size) image size))
          (append (assembly-fragment-characters (cdr image))
                  (assembly-zero-characters (- size (+ *assembly-macho-code-offset* (car image))))))
   :hints (("Goal"
            :use ((:instance assembly-nthcdr-after-whole-prefix
                             (prefix (coerce (boymoo-compiler::macho-header
                                              entry size signature-size) 'list))
                             (tail (append (assembly-fragment-characters (cdr image))
                                           (assembly-zero-characters
                                            (- size (+ *assembly-macho-code-offset* (car image))))))))
            :in-theory (disable assembly-nthcdr-after-whole-prefix)))))

(local
 (defthm assembly-macho-text-characters-are-characters
   (implies (and (stringp header) (proof-image-p image))
            (character-listp (assembly-macho-text-characters header image size)))))

(defthm assembly-macho-text-file-contents
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (size (assembly-macho-image-text-size image))
         (text (take size (coerce file 'list))))
    (implies (assembly-macho-image-entry-p image entry)
             (and (character-listp text)
                  (equal (len text) size)
                  (equal (nthcdr *assembly-macho-code-offset* text)
                         (append (assembly-fragment-characters (cdr image))
                                 (assembly-zero-characters
                                  (- size (+ *assembly-macho-code-offset* (car image)))))))))
  :hints (("Goal"
           :use (assembly-macho-file-text-and-signature assembly-macho-image-file-parameters)
           :in-theory (disable assembly-macho-image-text-size assembly-macho-text-characters
                               assembly-macho-signature-size-formula)))
  :rule-classes nil)

(in-theory (disable assembly-macho-image-file-parameters assembly-sha256-digest-characters))
