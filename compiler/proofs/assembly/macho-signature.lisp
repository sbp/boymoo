(in-package "BOYMOO-PROOFS")

(include-book "macho-image")
(include-book "macho-hash-pages")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-macho-page-digest (characters)
  (let* ((size boymoo-compiler::*macho-hash-page-size*)
         (page (assembly-page-string size characters))
         (words (boymoo-compiler::sha256-range-words page 0 size size)))
    (coerce (boymoo-compiler::sha256-prepend-digest words nil) 'string)))

(defun assembly-macho-page-digests (characters count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (assembly-macho-page-digest characters)
          (assembly-macho-page-digests
           (nthcdr boymoo-compiler::*macho-hash-page-size* characters) (1- count)))))

(local
 (defthm assembly-signature-reverse-onto-is-revappend
   (equal (boymoo-compiler::reverse-onto chunks tail) (revappend chunks tail))))

(local (in-theory (disable mv-nth nthcdr take
                           assembly-fragment-remaining-characters assembly-fragment-position-p
                           assembly-fragment-characters assembly-page-string
                           boymoo-compiler::sha256-page boymoo-compiler::sha256-range-words
                           boymoo-compiler::sha256-prepend-digest boymoo-compiler::reverse-onto)))

(defthm assembly-macho-page-digest-is-sha256
  (implies (character-listp characters)
           (equal (assembly-macho-page-digest characters)
                  (boymoo-compiler::sha256
                   (assembly-page-string boymoo-compiler::*macho-hash-page-size* characters))))
  :hints (("Goal" :in-theory (disable length)))
  :rule-classes nil)

(defthm assembly-macho-code-slots-hash-flat-pages
  (implies (and (assembly-fragment-position-p chunks at) (natp count))
           (equal (boymoo-compiler::macho-code-slots chunks at count digests)
                  (revappend digests
                             (assembly-macho-page-digests
                              (assembly-fragment-remaining-characters chunks at) count))))
  :hints (("Goal" :induct (boymoo-compiler::macho-code-slots chunks at count digests))
          ("Subgoal *1/2"
           :use ((:instance assembly-sha256-page-hashes-contiguous-bytes
                            (size boymoo-compiler::*macho-hash-page-size*)))))
  :rule-classes nil)

(local
 (defun assembly-macho-pad-digests-induction (characters count padding)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       padding
     (let ((size boymoo-compiler::*macho-hash-page-size*))
       (assembly-macho-pad-digests-induction
        (nthcdr size characters) (1- count)
        (nfix (- padding (nfix (- size (len characters))))))))))

(defthm assembly-macho-digests-with-explicit-zeroes
  (implies (and (natp count) (natp padding) (true-listp characters))
           (equal (assembly-macho-page-digests
                   (append characters (assembly-zero-characters padding)) count)
                  (assembly-macho-page-digests characters count)))
  :hints (("Goal" :induct (assembly-macho-pad-digests-induction characters count padding))
          ("Subgoal *1/2"
           :use ((:instance assembly-page-suffix-with-explicit-zeroes
                            (count boymoo-compiler::*macho-hash-page-size*) (chars characters))
                 (:instance assembly-page-string-with-explicit-zeroes
                            (count boymoo-compiler::*macho-hash-page-size*) (chars characters)))))
  :rule-classes nil)

(local
 (defthm assembly-signature-length-of-append
   (equal (len (append prefix tail)) (+ (len prefix) (len tail)))))

(local
 (defthm assembly-signature-take-complete-prefix
   (implies (true-listp prefix)
            (equal (take (len prefix) (append prefix tail)) prefix))
   :hints (("Goal" :induct (len prefix) :in-theory (enable take)))))

(local
 (defthm assembly-signature-drop-complete-prefix
   (equal (nthcdr (len prefix) (append prefix tail)) tail)
   :hints (("Goal" :induct (len prefix) :in-theory (enable nthcdr)))))

(local
 (defthm assembly-signature-page-string-copies-prefix
   (implies (true-listp prefix)
            (equal (assembly-page-string (len prefix) (append prefix tail))
                   (coerce prefix 'string)))
   :hints (("Goal" :in-theory (enable assembly-page-string assembly-page-prefix)))))

(local
 (defthm assembly-signature-header-digest
   (implies (and (stringp header) (equal (len (coerce header 'list)) 4096) (posp slots))
            (equal (assembly-macho-page-digests (append (coerce header 'list) tail) slots)
                   (cons (coerce (boymoo-compiler::sha256-prepend-digest
                                  (boymoo-compiler::sha256-range-words header 0 4096 4096) nil)
                                 'string)
                         (assembly-macho-page-digests tail (1- slots)))))
   :hints (("Goal"
            :use ((:instance assembly-signature-page-string-copies-prefix
                             (prefix (coerce header 'list)))
                  (:instance assembly-signature-drop-complete-prefix
                             (prefix (coerce header 'list))))
            :in-theory (disable assembly-signature-page-string-copies-prefix
                                assembly-signature-drop-complete-prefix)))))

(local
 (defthm assembly-signature-code-slots-from-image
   (implies (and (proof-image-p image) (natp count))
            (equal (boymoo-compiler::macho-code-slots (cdr image) 0 count nil)
                   (assembly-macho-page-digests (assembly-fragment-characters (cdr image)) count)))
   :hints (("Goal"
            :use ((:instance assembly-macho-code-slots-hash-flat-pages
                             (chunks (cdr image)) (at 0) (digests nil)))
            :in-theory (e/d (assembly-fragment-position-p assembly-fragment-remaining-characters
                             nthcdr)
                            (boymoo-compiler::macho-code-slots assembly-macho-page-digests))))))

(local
 (defthm assembly-signature-flatten-first-fragment
   (equal (assembly-fragment-characters (cons first rest))
          (append (coerce first 'list) (assembly-fragment-characters rest)))
   :hints (("Goal" :in-theory (enable assembly-fragment-characters)))))

(local (in-theory (disable boymoo-compiler::macho-code-slots assembly-macho-page-digests
                           assembly-macho-slot-count boymoo-compiler::macho-signature-size
                           assembly-macho-signature-fragments)))

(defthm assembly-macho-signature-hashes-text-pages
  (let* ((slots (assembly-macho-slot-count size))
         (text (assembly-macho-text-characters header image size))
         (signature (assembly-fragment-characters
                     (assembly-macho-signature-fragments header image size))))
    (implies (and (proof-image-p image) (stringp header) (equal (length header) 4096)
                  (posp slots) (integerp size) (<= (+ *assembly-macho-code-offset* (car image)) size))
             (equal (nthcdr *assembly-macho-signature-hash-offset* signature)
                    (append (assembly-fragment-characters (assembly-macho-page-digests text slots))
                            (assembly-zero-characters 13)))))
  :hints (("Goal"
           :use (assembly-macho-signature-hash-tail
                 (:instance assembly-macho-digests-with-explicit-zeroes
                            (count (1- (assembly-macho-slot-count size)))
                            (characters (assembly-fragment-characters (cdr image)))
                            (padding (- size (+ *assembly-macho-code-offset* (car image))))))
           :in-theory (e/d (assembly-sha256-digest-characters) (proof-image-p))))
  :rule-classes nil)

(local
 (defthm assembly-macho-slot-count-spans-aligned-text
   (implies (and (natp size) (integerp (* 1/16384 size)))
            (equal (* 4096 (assembly-macho-slot-count size)) size))
   :hints (("Goal"
            :use ((:instance assembly-floor-unique (x size) (d 4096) (q (* 1/4096 size)))
                  (:instance acl2::associativity-of-* (acl2::x 4) (acl2::y 1/16384) (acl2::z size))
                  (:instance acl2::associativity-of-* (acl2::x 4096) (acl2::y 1/4096) (acl2::z size)))
            :in-theory (e/d (assembly-macho-slot-count)
                            (acl2::associativity-of-* floor))))))

(defthm assembly-macho-file-stores-text-page-digests
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (size (assembly-macho-image-text-size image))
         (slots (assembly-macho-slot-count size))
         (characters (coerce file 'list))
         (text (take size characters))
         (signature (nthcdr size characters)))
    (implies (assembly-macho-image-entry-p image entry)
             (and (equal (* 4096 slots) size)
                  (equal (nthcdr *assembly-macho-signature-hash-offset* signature)
                         (append (assembly-fragment-characters (assembly-macho-page-digests text slots))
                                 (assembly-zero-characters 13))))))
  :hints (("Goal"
           :use (assembly-macho-file-text-and-signature assembly-macho-image-file-parameters
                 (:instance assembly-macho-segment-rounding
                            (bytes (+ *assembly-macho-code-offset* (car image))))
                 (:instance assembly-macho-signature-hashes-text-pages
                            (size (assembly-macho-image-text-size image))
                            (header (boymoo-compiler::macho-header
                                     entry (assembly-macho-image-text-size image)
                                     (boymoo-compiler::macho-signature-size
                                      (assembly-macho-slot-count (assembly-macho-image-text-size image)))))))
           :in-theory (disable assembly-macho-text-characters
                               boymoo-compiler::macho-image-executable boymoo-compiler::macho-header
                               boymoo-compiler::macho-segment-size)))
  :rule-classes nil)
