(in-package "BOYMOO-PROOFS")

(include-book "elf-image")

(logic)
(set-verify-guards-eagerness 0)

(defconst *assembly-macho-code-offset* #x1000)
(defconst *assembly-macho-page-size* #x4000)
(defconst *assembly-macho-preferred-base* #x100000000)

(defun assembly-macho-text-size (file)
  (proof-file-le 8 136 file))

(defun assembly-macho-entry-offset (file)
  (proof-file-le 8 336 file))

(defun assembly-macho-signature-offset (file)
  (proof-file-le 4 360 file))

(defun assembly-macho-signature-size (file)
  (proof-file-le 4 364 file))

(defun assembly-macho-header-p (file text-size entry signature-size)
  (and (stringp file)
       (equal (proof-file-le 4 0 file) #xfeedfacf)
       (equal (proof-file-le 4 4 file) #x0100000c)
       (equal (proof-file-le 4 8 file) 0)
       (equal (proof-file-le 4 12 file) 2)
       (equal (proof-file-le 4 16 file) 7)
       (equal (proof-file-le 4 20 file) 336)
       (equal (proof-file-le 4 24 file) #x200085)
       (equal (proof-file-le 4 28 file) 0)
       (equal (proof-file-le 4 32 file) 25)
       (equal (proof-file-le 4 36 file) 72)
       (equal (proof-file-le 16 40 file) #x4f52455a454741505f5f)
       (equal (proof-file-le 8 56 file) 0)
       (equal (proof-file-le 8 64 file) *assembly-macho-preferred-base*)
       (equal (proof-file-le 8 72 file) 0)
       (equal (proof-file-le 8 80 file) 0)
       (equal (proof-file-le 4 88 file) 0)
       (equal (proof-file-le 4 92 file) 0)
       (equal (proof-file-le 4 96 file) 0)
       (equal (proof-file-le 4 100 file) 0)
       (equal (proof-file-le 4 104 file) 25)
       (equal (proof-file-le 4 108 file) 72)
       (equal (proof-file-le 16 112 file) #x545845545f5f)
       (equal (proof-file-le 8 128 file) *assembly-macho-preferred-base*)
       (equal (assembly-macho-text-size file) text-size)
       (equal (proof-file-le 8 144 file) 0)
       (equal (proof-file-le 8 152 file) text-size)
       (equal (proof-file-le 4 160 file) 5)
       (equal (proof-file-le 4 164 file) 5)
       (equal (proof-file-le 4 168 file) 0)
       (equal (proof-file-le 4 172 file) 0)
       (equal (proof-file-le 4 176 file) 25)
       (equal (proof-file-le 4 180 file) 72)
       (equal (proof-file-le 16 184 file) #x544944454b4e494c5f5f)
       (equal (proof-file-le 8 200 file) (+ *assembly-macho-preferred-base* text-size))
       (equal (proof-file-le 8 208 file) (boymoo-compiler::macho-segment-size signature-size))
       (equal (proof-file-le 8 216 file) text-size)
       (equal (proof-file-le 8 224 file) signature-size)
       (equal (proof-file-le 4 232 file) 1)
       (equal (proof-file-le 4 236 file) 1)
       (equal (proof-file-le 4 240 file) 0)
       (equal (proof-file-le 4 244 file) 0)
       (equal (proof-file-le 4 248 file) #x80000022)
       (equal (proof-file-le 4 252 file) 48)
       (equal (proof-file-le 4 256 file) 0)
       (equal (proof-file-le 4 260 file) 0)
       (equal (proof-file-le 4 264 file) 0)
       (equal (proof-file-le 4 268 file) 0)
       (equal (proof-file-le 4 272 file) 0)
       (equal (proof-file-le 4 276 file) 0)
       (equal (proof-file-le 4 280 file) 0)
       (equal (proof-file-le 4 284 file) 0)
       (equal (proof-file-le 4 288 file) 0)
       (equal (proof-file-le 4 292 file) 0)
       (equal (proof-file-le 4 296 file) 14)
       (equal (proof-file-le 4 300 file) 32)
       (equal (proof-file-le 4 304 file) 12)
       (equal (proof-file-le 4 328 file) #x80000028)
       (equal (proof-file-le 4 332 file) 24)
       (equal (assembly-macho-entry-offset file) (+ *assembly-macho-code-offset* entry))
       (equal (proof-file-le 8 344 file) 0)
       (equal (proof-file-le 4 352 file) 29)
       (equal (proof-file-le 4 356 file) 16)
       (equal (assembly-macho-signature-offset file) text-size)
       (equal (assembly-macho-signature-size file) signature-size)))

(local (in-theory (disable ash floor mod assembly-power-of-two)))

(defthm assembly-macho-segment-rounding
  (implies (natp bytes)
           (let ((size (boymoo-compiler::macho-segment-size bytes)))
             (and (natp size)
                  (<= bytes size)
                  (< size (+ bytes *assembly-macho-page-size*))
                  (integerp (* (/ *assembly-macho-page-size*) size)))))
  :hints (("Goal"
           :use ((:instance assembly-floor-bounds (x (+ bytes 16383)) (d 16384))
                 (:instance acl2::associativity-of-* (acl2::x 1/16384) (acl2::y 16384)
                             (acl2::z (floor (+ bytes 16383) 16384))))
           :in-theory (e/d (assembly-high)
                           (acl2::associativity-of-*))))
  :rule-classes nil)

(local
 (defthm assembly-macho-le-matches-elf-le
   (equal (boymoo-compiler::macho-prepend-le word count acc)
          (boymoo-compiler::elf-prepend-le word count acc))
   :hints (("Goal" :induct (boymoo-compiler::macho-prepend-le word count acc)))))

(defthm assembly-macho-prepend-zeroes-characters
  (implies (character-listp acc)
           (character-listp (boymoo-compiler::macho-prepend-zeroes count acc))))

(local
 (defthm assembly-macho-nth-character
   (implies (and (character-listp characters) (natp index) (< index (len characters)))
            (characterp (nth index characters)))
   :hints (("Goal" :induct (nth index characters)))))

(local
 (defthm assembly-macho-char-in-bounds
   (implies (and (stringp name) (natp index) (< index (length name)))
            (characterp (char name index)))))

(local
 (defthm assembly-macho-prepend-string-characters
   (implies (and (stringp name) (<= count (length name)) (character-listp acc))
            (character-listp (boymoo-compiler::macho-prepend-string name count acc)))
   :hints (("Goal" :induct (boymoo-compiler::macho-prepend-string name count acc)
                   :in-theory (disable char length)))))

(defthm assembly-length-of-macho-prepended-zeroes
  (equal (len (boymoo-compiler::macho-prepend-zeroes count acc))
         (+ (nfix count) (len acc))))

(local
 (defthm assembly-length-of-macho-prepended-string
   (equal (len (boymoo-compiler::macho-prepend-string name count acc))
          (+ (nfix count) (len acc)))))

(local
 (defthm assembly-nthcdr-of-prepended-character
   (implies (posp index)
            (equal (nthcdr index (cons char acc)) (nthcdr (1- index) acc)))))

(defthm assembly-nthcdr-past-macho-prepended-zeroes
  (implies (and (natp count) (natp index) (<= count index))
           (equal (nthcdr index (boymoo-compiler::macho-prepend-zeroes count acc))
                  (nthcdr (- index count) acc)))
  :hints (("Goal" :induct (boymoo-compiler::macho-prepend-zeroes count acc))))

(local
 (defthm assembly-nthcdr-past-macho-prepended-string
   (implies (and (natp count) (natp index) (<= count index))
            (equal (nthcdr index (boymoo-compiler::macho-prepend-string name count acc))
                   (nthcdr (- index count) acc)))
   :hints (("Goal" :induct (boymoo-compiler::macho-prepend-string name count acc)))))

(local
 (defthm assembly-append-of-macho-prepended-zeroes
   (equal (append (boymoo-compiler::macho-prepend-zeroes count acc) suffix)
          (boymoo-compiler::macho-prepend-zeroes count (append acc suffix)))))

(local
 (defthm assembly-append-of-macho-prepended-string
   (equal (append (boymoo-compiler::macho-prepend-string name count acc) suffix)
          (boymoo-compiler::macho-prepend-string name count (append acc suffix)))))

(local
 (defthm assembly-append-of-macho-padded-name
   (equal (append (boymoo-compiler::macho-prepend-padded-name name size acc) suffix)
          (boymoo-compiler::macho-prepend-padded-name name size (append acc suffix)))))

(local
 (defthm assembly-macho-name-field-bytes
   (and (equal (assembly-read-le-characters 16
                                            (boymoo-compiler::macho-prepend-padded-name "__PAGEZERO" 16 acc))
               #x4f52455a454741505f5f)
        (equal (assembly-read-le-characters 16
                                            (boymoo-compiler::macho-prepend-padded-name "__TEXT" 16 acc))
               #x545845545f5f)
        (equal (assembly-read-le-characters 16
                                            (boymoo-compiler::macho-prepend-padded-name "__LINKEDIT" 16 acc))
               #x544944454b4e494c5f5f))
   :hints (("Goal"
            :use ((:instance assembly-append-of-macho-padded-name
                             (name "__PAGEZERO") (size 16) (acc nil) (suffix acc))
                  (:instance assembly-append-of-macho-padded-name
                             (name "__TEXT") (size 16) (acc nil) (suffix acc))
                  (:instance assembly-append-of-macho-padded-name
                             (name "__LINKEDIT") (size 16) (acc nil) (suffix acc)))
            :in-theory (e/d (assembly-read-le-characters)
                            (assembly-append-of-macho-padded-name
                             boymoo-compiler::macho-prepend-padded-name))))))

(defthm assembly-length-of-macho-padded-name
  (implies (and (natp size) (<= (length name) size))
           (equal (len (boymoo-compiler::macho-prepend-padded-name name size acc))
                  (+ size (len acc)))))

(defthm assembly-macho-padded-name-characters
  (implies (and (stringp name) (character-listp acc))
           (character-listp (boymoo-compiler::macho-prepend-padded-name name size acc))))

(defthm assembly-nthcdr-past-macho-padded-name
  (implies (and (natp size) (natp index) (<= (length name) size) (<= size index))
           (equal (nthcdr index (boymoo-compiler::macho-prepend-padded-name name size acc))
                  (nthcdr (- index size) acc))))

(local (in-theory
        (e/d (assembly-file-le-reads-characters assembly-elf-field-characters-p
              assembly-length-of-elf-field assembly-nthcdr-past-elf-field assembly-elf-field-round-trip)
             (proof-file-le assembly-read-le-characters
              boymoo-compiler::macho-prepend-zeroes boymoo-compiler::macho-prepend-string
              boymoo-compiler::macho-prepend-padded-name boymoo-compiler::macho-prepend-le
              boymoo-compiler::elf-prepend-le
              (:executable-counterpart boymoo-compiler::macho-prepend-zeroes)
              (:executable-counterpart boymoo-compiler::macho-prepend-string)
              (:executable-counterpart boymoo-compiler::elf-prepend-le)))))

(defthm assembly-macho-header-length
  (equal (length (boymoo-compiler::macho-header entry text-size signature-size))
         *assembly-macho-code-offset*))

(local
 (defthm assembly-macho-segment-size-fits-header
   (implies (unsigned-byte-p 32 bytes)
            (unsigned-byte-p 64 (boymoo-compiler::macho-segment-size bytes)))
   :hints (("Goal" :use (assembly-macho-segment-rounding)
                   :in-theory (disable boymoo-compiler::macho-segment-size)))))

(defthm assembly-macho-header-fields
  (implies (and (natp entry) (unsigned-byte-p 32 (+ *assembly-macho-code-offset* entry))
                (unsigned-byte-p 32 text-size) (unsigned-byte-p 32 signature-size))
           (assembly-macho-header-p (boymoo-compiler::macho-header entry text-size signature-size)
                                    text-size entry signature-size))
  :hints (("Goal" :in-theory (disable boymoo-compiler::macho-segment-size)))
  :rule-classes nil)

(local
 (defthm assembly-little-endian-reading-stays-in-prefix
   (implies (and (natp count) (<= count (len prefix)))
            (equal (assembly-read-le-characters count (append prefix suffix))
                   (assembly-read-le-characters count prefix)))
   :hints (("Goal" :induct (assembly-read-le-characters count prefix)
                   :in-theory (enable assembly-read-le-characters)))))

(local
 (defthm assembly-nthcdr-of-append-within-prefix
   (implies (and (natp index) (<= index (len prefix)))
            (equal (nthcdr index (append prefix suffix))
                   (append (nthcdr index prefix) suffix)))
   :hints (("Goal" :induct (nthcdr index prefix)))))

(local
 (defthm assembly-length-after-nthcdr
   (implies (and (natp index) (<= index (len prefix)))
            (equal (len (nthcdr index prefix)) (- (len prefix) index)))
   :hints (("Goal" :induct (nthcdr index prefix)))))

(local
 (defthm assembly-macho-append-characters
   (implies (and (character-listp first) (character-listp rest))
            (character-listp (append first rest)))))

(local
 (defthm assembly-macho-file-field-stays-in-header
   (implies (and (stringp header) (character-listp suffix)
                 (natp count) (natp index) (<= (+ count index) (length header)))
            (equal (proof-file-le count index
                                  (coerce (append (coerce header 'list) suffix) 'string))
                   (proof-file-le count index header)))))

(defthm assembly-macho-header-with-file-tail
  (implies (and (assembly-macho-header-p header text-size entry signature-size)
                (<= 368 (length header)) (character-listp suffix))
           (assembly-macho-header-p (coerce (append (coerce header 'list) suffix) 'string)
                                    text-size entry signature-size))
  :hints (("Goal" :in-theory (disable assembly-file-le-reads-characters
                                      boymoo-compiler::macho-segment-size)))
  :rule-classes nil)

(in-theory (disable assembly-macho-prepend-zeroes-characters
                    assembly-length-of-macho-prepended-zeroes
                    assembly-length-of-macho-padded-name
                    assembly-macho-padded-name-characters
                    assembly-nthcdr-past-macho-prepended-zeroes
                    assembly-nthcdr-past-macho-padded-name))
