(in-package "BOYMOO-PROOFS")

(include-book "bits")
(include-book "layout")

(logic)
(set-verify-guards-eagerness 0)

(defthm data-machine-unsigned-fits
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-unsigned width word)))
  :hints (("Goal" :use ((:instance data-machine-unsigned-is-low-bits (word (ifix word))))
                  :in-theory (disable boymoo-compiler::low-bits ash expt acl2::binary-logand))))

(local
 (defthm logior-with-zero
   (implies (integerp word) (equal (logior word 0) word))
   :hints (("Goal" :expand ((logior word 0))))))

(local
 (defthm read-zero-bytes
   (equal (boymoo-model::a64-read-bytes 0 address memory) 0)
   :hints (("Goal" :expand ((boymoo-model::a64-read-bytes 0 address memory))))))

(local
 (defthm byte-load-is-memory-byte
   (equal (boymoo-model::a64-load 1 address machine)
          (boymoo-model::a64-byte address (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-byte)
                   :expand ((:free (memory) (boymoo-model::a64-read-bytes 1 address memory)))))))

(local
 (defthm data-memory-byte-fits
   (unsigned-byte-p 8 (boymoo-model::a64-byte address memory))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned unsigned-byte-p)))))

(local
 (in-theory (disable boymoo-model::a64-load boymoo-model::a64-byte
                     boymoo-model::a64-unsigned boymoo-compiler::low-bits ash)))

(defun data-placed-characters-p (characters address machine)
  (if (atom characters)
      (null characters)
    (and (equal (boymoo-model::a64-load 1 address machine) (char-code (car characters)))
         (data-placed-characters-p (cdr characters) (1+ address) machine))))

(local
 (defthm code-char-with-unsigned-byte
   (implies (and (unsigned-byte-p 8 byte) (characterp ch))
            (equal (equal (code-char byte) ch) (equal byte (char-code ch))))
   :hints (("Goal" :use ((:instance acl2::code-char-char-code-is-identity (acl2::c ch))
                        (:instance acl2::char-code-code-char-is-identity (acl2::n byte)))
                   :in-theory (disable acl2::code-char-char-code-is-identity
                                       acl2::char-code-code-char-is-identity)))))

(local
 (defun placed-characters-induction (characters address)
   (if (atom characters) address
     (placed-characters-induction (cdr characters) (1+ address)))))

(local
 (defthm equal-cons-to-existing-list
   (implies (consp characters)
            (equal (equal (cons first rest) characters)
                   (and (equal first (car characters)) (equal rest (cdr characters)))))
   :hints (("Goal" :use ((:instance acl2::cons-car-cdr (acl2::x characters)))
                   :in-theory (disable acl2::cons-car-cdr)))))

(local
 (defthm placed-characters-is-byte-list-equality
   (implies (and (character-listp characters) (integerp address))
            (equal (equal (proof-byte-characters (proof-byte-list (len characters) address machine))
                          characters)
                   (data-placed-characters-p characters address machine)))
   :hints (("Goal" :induct (placed-characters-induction characters address)
                   :in-theory (disable unsigned-byte-p)))))

(local
 (defthm byte-characters-are-characters
   (character-listp (proof-byte-characters bytes))))

(local
 (defthm equal-coerced-character-lists
   (implies (and (character-listp first) (character-listp second))
            (equal (equal (coerce first 'string) (coerce second 'string))
                   (equal first second)))
   :hints (("Goal" :use ((:instance acl2::coerce-inverse-1 (acl2::x first))
                        (:instance acl2::coerce-inverse-1 (acl2::x second)))
                   :in-theory (disable acl2::coerce-inverse-1)))))

(defthmd data-load-string-places-characters
  (implies (and (character-listp characters) (integerp address))
           (equal (equal (proof-load-string (len characters) address machine)
                         (coerce characters 'string))
                  (data-placed-characters-p characters address machine)))
  :hints (("Goal" :in-theory (disable proof-byte-characters proof-byte-list data-placed-characters-p))))

(local
 (defun data-placed-append-induction (first address)
   (if (atom first) address
     (data-placed-append-induction (cdr first) (1+ address)))))

(defthm data-placed-characters-of-append
  (implies (and (true-listp first) (integerp address))
           (equal (data-placed-characters-p (append first second) address machine)
                  (and (data-placed-characters-p first address machine)
                       (data-placed-characters-p second (+ address (len first)) machine))))
  :hints (("Goal" :induct (data-placed-append-induction first address))))

; These are the little-endian digits of a word, starting at its low byte.
(defun data-characters-read-word (characters)
  (if (atom characters)
      0
    (logior (char-code (car characters)) (ash (data-characters-read-word (cdr characters)) 8))))

(defthmd data-load-placed-word
  (implies (and (data-placed-characters-p characters address machine)
                (integerp address))
           (equal (boymoo-model::a64-load (len characters) address machine)
                  (data-characters-read-word characters)))
  :hints (("Goal" :induct (placed-characters-induction characters address)
                  :in-theory (e/d (boymoo-model::a64-load)
                                 (acl2::binary-logior proof-byte-list byte-load-is-memory-byte)))))

(local
 (defthm character-list-of-chunk-is-true-list
   (true-listp (data-chunk-characters chunk))
   :hints (("Goal" :use data-chunk-characters-are-characters
                   :in-theory (disable data-chunk-characters-are-characters data-chunk-characters)))))

(local
 (defun data-placed-word-chunk-induction (index chunks address)
   (if (or (zp index) (atom chunks)) address
     (data-placed-word-chunk-induction (1- index) (cdr chunks) (+ address 8)))))

(defthmd data-placed-word-chunk-at-index
  (implies (and (data-word-chunks-p chunks)
                (data-placed-characters-p (data-forward-chunk-characters chunks) base machine)
                (integerp base) (natp index) (< index (len chunks)))
           (data-placed-characters-p (data-chunk-characters (nth index chunks))
                                     (+ base (* 8 index)) machine))
  :hints (("Goal" :induct (data-placed-word-chunk-induction index chunks base)
                  :in-theory (disable data-placed-characters-p data-chunk-characters))))

(local
 (defthm placed-first-fragment
   (implies (and (proof-image-at-p image base machine) (consp (cdr image))
                 (character-listp characters)
                 (equal (cadr image) (coerce characters 'string)))
            (data-placed-characters-p characters base machine))
   :hints (("Goal" :use ((:instance data-load-string-places-characters (address base)))
                   :in-theory (disable proof-load-string data-placed-characters-p)))))

(local
 (in-theory (disable boymoo-compiler::data-build data-image-parts
                     data-forward-chunk-characters data-placed-characters-p
                     proof-load-string)))

(defthmd data-build-places-header
  (implies (and (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
                (car (data-image-parts lines package-lines)))
           (data-placed-characters-p
            (data-forward-chunk-characters (car (data-image-parts lines package-lines))) base machine))
  :hints (("Goal" :use ((:instance placed-first-fragment
                                   (image (car (boymoo-compiler::data-build lines package-lines)))
                                   (characters (data-forward-chunk-characters
                                                (car (data-image-parts lines package-lines))))))
                  :in-theory (e/d (data-build-header-fragment)
                                 (placed-first-fragment boymoo-compiler::data-write
                                  proof-image-at-p data-header-stays-in-one-fragment)))))

(defthmd data-build-places-nil-root-bytes
  (implies (and (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
                (car (data-image-parts lines package-lines)))
           (data-placed-characters-p (boymoo-compiler::prepend-word *proof-nil* 8 nil)
                                     (+ base 24) machine))
  :hints (("Goal" :use (data-build-places-header
                       (:instance data-placed-word-chunk-at-index
                                  (index 3) (chunks (car (data-image-parts lines package-lines)))))
                  :in-theory (disable proof-fragments-at-p proof-fragments-size
                                      proof-fragments-p proof-image-p boymoo-compiler::prepend-word))))

(defthmd data-build-has-empty-dynamic-root
  (implies (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
           (equal (proof-dynamic-root base machine) *proof-nil*))
  :hints (("Goal" :use (data-build-places-nil-root-bytes
                       (:instance data-load-placed-word (address (+ base 24))
                                  (characters (boymoo-compiler::prepend-word *proof-nil* 8 nil))))
                  :in-theory (e/d (data-build-image-and-index)
                                 (proof-fragments-at-p proof-fragments-size proof-fragments-p
                                  proof-load-string boymoo-compiler::data-write
                                  boymoo-compiler::reverse-onto)))))
