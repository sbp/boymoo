(in-package "BOYMOO-PROOFS")

(include-book "image-decoding")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash mod floor expt assembly-low assembly-power-of-two
                           boymoo-model::a64-unsigned)))

(local
 (defthm assembly-a64-byte-after-binding
   (equal (boymoo-model::a64-byte address (cons (cons key value) memory))
          (if (equal (boymoo-model::a64-unsigned 64 address) key)
              (boymoo-model::a64-unsigned 8 value)
            (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :in-theory (disable assembly-a64-unsigned-is-low)))))

(local
 (defthm assembly-a64-double-byte-mask
   (equal (assembly-low 8 (assembly-low 8 value))
          (assembly-low 8 value))
   :hints (("Goal" :use ((:instance assembly-low-bounds (width 8)))))))

(local
 (defthm assembly-a64-load-one-byte
   (equal (boymoo-model::a64-load 1 address machine)
          (boymoo-model::a64-byte address (boymoo-model::a64-memory machine)))
   :hints (("Goal"
            :expand ((:free (memory) (boymoo-model::a64-read-bytes 1 address memory))
                     (:free (start memory) (boymoo-model::a64-read-bytes 0 start memory)))))))

(local (in-theory (disable boymoo-model::a64-byte boymoo-model::a64-load)))

(local
 (defthm assembly-cleared-address-has-no-binding
   (implies (and (natp address) (<= lower address) (< address upper))
            (not (assoc-equal address (proof-clear-memory lower upper memory))))
   :hints (("Goal" :induct (proof-clear-memory lower upper memory)))))

(defthm assembly-byte-of-cleared-memory
  (implies (and (unsigned-byte-p 64 address) (<= lower address) (< address upper))
           (equal (boymoo-model::a64-byte address (proof-clear-memory lower upper memory)) 0))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-byte) (proof-clear-memory)))))

(defthm assembly-overlay-byte-at
  (implies (and (unsigned-byte-p 64 address) (natp start)
                (<= (+ start (len bytes)) (expt 2 64)))
           (equal (boymoo-model::a64-byte address (proof-overlay-bytes bytes start memory omit-zero))
                  (if (and (<= start address) (< address (+ start (len bytes))))
                      (let ((byte (boymoo-model::a64-unsigned 8 (nth (- address start) bytes))))
                        (if (and omit-zero (equal byte 0))
                            (boymoo-model::a64-byte address memory)
                          byte))
                    (boymoo-model::a64-byte address memory))))
  :hints (("Goal" :induct (proof-overlay-bytes bytes start memory omit-zero)
                  :in-theory (disable assembly-a64-unsigned-is-low))
          ("Subgoal *1/2"
           :cases ((equal address start) (< address start))
           :use ((:instance assembly-low-of-fitting-value (width 64) (value address))
                 (:instance assembly-low-of-fitting-value (width 64) (value start)))
           :in-theory (enable assembly-a64-unsigned-is-low))
          ("Subgoal *1/3"
           :cases ((equal address start) (< address start))
           :in-theory (enable assembly-a64-unsigned-is-low))))

(local
 (defthm assembly-count-of-string-bytes
   (equal (len (proof-string-bytes chars)) (len chars))))

(local
 (defthm assembly-string-byte-at-index
   (implies (and (natp index) (< index (len chars)))
            (equal (nth index (proof-string-bytes chars))
                   (char-code (nth index chars))))
   :hints (("Goal" :induct (nth index chars)))))

(defun assembly-load-cleared-file (file base clear-end machine)
  (proof-load-cleared-string
   file base
   (update-nth 4 (proof-clear-memory base clear-end (boymoo-model::a64-memory machine))
               machine)))

(defthm assembly-loaded-file-zero-tail-byte
  (implies (and (stringp file) (natp base)
                (unsigned-byte-p 64 address)
                (<= (+ base (length file)) address)
                (< address clear-end))
           (equal (boymoo-model::a64-load 1 address (assembly-load-cleared-file file base clear-end machine))
                  0))
  :hints (("Goal" :in-theory (disable proof-clear-memory proof-overlay-bytes proof-string-bytes))))

(local
 (defthm assembly-null-character-has-zero-code
   (implies (characterp ch)
            (equal (equal (char-code ch) 0)
                   (equal ch (code-char 0))))
   :hints (("Goal"
            :use ((:instance acl2::code-char-char-code-is-identity (acl2::c ch)))
            :in-theory (disable acl2::code-char-char-code-is-identity)))))

(local
 (defthm assembly-loaded-file-character
   (let ((address (+ base index))
         (end (+ base (length file))))
     (implies (and (stringp file) (natp base) (natp index)
                   (< index (length file))
                   (<= end clear-end) (<= end (expt 2 64)))
              (equal (code-char (boymoo-model::a64-load
                                 1 address (assembly-load-cleared-file file base clear-end machine)))
                     (char file index))))
   :hints (("Goal" :in-theory (disable proof-overlay-bytes proof-string-bytes
                                       proof-clear-memory)))))

(local
 (defun assembly-file-suffix-induction (chars index)
   (if (consp chars)
       (assembly-file-suffix-induction (cdr chars) (1+ (nfix index)))
     index)))

(local
 (defthm assembly-file-character-of-suffix
   (equal (car (nthcdr index chars)) (nth index chars))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-file-suffix-successor
   (implies (natp index)
            (equal (nthcdr (1+ index) chars)
                   (cdr (nthcdr index chars))))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-file-suffix-within-bounds
   (iff (consp (nthcdr index chars)) (< (nfix index) (len chars)))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-file-suffix-past-end
   (implies (and (true-listp chars) (<= (len chars) (nfix index)))
            (equal (nthcdr index chars) nil))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-loaded-file-places-suffix
   (implies (and (stringp file) (natp base) (natp index)
                 (equal chars (nthcdr index (coerce file 'list)))
                 (<= (+ base (length file)) clear-end)
                 (<= (+ base (length file)) (expt 2 64)))
            (assembly-characters-at-p
             chars (+ base index) (assembly-load-cleared-file file base clear-end machine)))
   :hints (("Goal" :induct (assembly-file-suffix-induction chars index)
                   :in-theory (disable assembly-load-cleared-file
                                       assembly-a64-load-one-byte
                                       assembly-loaded-file-character
                                       char))
           ("Subgoal *1/1"
            :use (assembly-loaded-file-character)
            :in-theory (disable assembly-load-cleared-file assembly-a64-load-one-byte
                                assembly-loaded-file-character)))
   :rule-classes nil))

(defthm assembly-loaded-file-places-characters
  (implies (and (stringp file) (natp base)
                (<= (+ base (length file)) clear-end)
                (<= (+ base (length file)) (expt 2 64)))
           (assembly-characters-at-p
            (coerce file 'list) base (assembly-load-cleared-file file base clear-end machine)))
  :hints (("Goal" :use ((:instance assembly-loaded-file-places-suffix
                                   (index 0) (chars (coerce file 'list))))
                  :in-theory (disable assembly-load-cleared-file
                                      assembly-characters-at-p)))
  :rule-classes nil)

(local
 (defun assembly-skip-character-induction (chars address count)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons chars address)
     (assembly-skip-character-induction (cdr chars) (1+ (ifix address)) (1- count)))))

(defthm assembly-placed-characters-after-prefix
  (implies (and (assembly-characters-at-p chars address machine)
                (integerp address) (natp count) (<= count (len chars)))
           (assembly-characters-at-p (nthcdr count chars) (+ address count) machine))
  :hints (("Goal" :induct (assembly-skip-character-induction chars address count)
                  :in-theory (disable assembly-a64-load-one-byte)))
  :rule-classes nil)

(local
 (defthm assembly-readback-of-placed-characters
   (implies (assembly-characters-at-p chars address machine)
            (equal (proof-byte-characters (proof-byte-list (len chars) address machine))
                   chars))
   :hints (("Goal" :induct (assembly-characters-at-p chars address machine)
                   :in-theory (disable assembly-a64-load-one-byte)))))

(defthm assembly-fragments-from-placed-characters
  (implies (and (integerp address) (proof-fragments-p fragments)
                (assembly-characters-at-p
                 (assembly-fragment-characters fragments) address machine))
           (proof-fragments-at-p fragments address machine))
  :hints (("Goal" :induct (proof-fragments-at-p fragments address machine)
                  :in-theory (disable proof-byte-list proof-byte-characters
                                      assembly-characters-at-p assembly-a64-load-one-byte))))
