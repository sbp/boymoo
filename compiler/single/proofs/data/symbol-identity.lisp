(in-package "BOYMOO-PROOFS")

(include-book "symbol-spelling")

(logic)
(set-verify-guards-eagerness 0)

(defun data-escape-characters (characters delimiter)
  (if (atom characters)
      nil
    (let ((byte (car characters)) (rest (data-escape-characters (cdr characters) delimiter)))
      (if (data-character-printed-literally-p byte delimiter)
          (cons byte rest)
        (list* #\\ (data-hex-digit-character (floor (char-code byte) 16))
               (data-hex-digit-character (mod (char-code byte) 16)) rest)))))

(local
 (defthm car-of-string-suffix
   (equal (car (nthcdr start characters)) (nth start characters))
   :hints (("Goal" :induct (nthcdr start characters)))))

(local
 (defthm cdr-of-string-suffix
   (implies (natp start)
            (equal (cdr (nthcdr start characters)) (nthcdr (1+ start) characters)))
   :hints (("Goal" :induct (nthcdr start characters)))))

(local
 (defthm suffixes-at-zero-and-one
   (and (equal (nthcdr 0 characters) characters)
        (equal (nthcdr 1 characters) (cdr characters)))))

(local
 (defthm take-zero-bytes
   (equal (take 0 characters) nil)))

(local
 (defthm take-one-byte
   (implies (posp count)
            (equal (take count characters) (cons (car characters) (take (1- count) (cdr characters)))))
   :hints (("Goal" :expand ((take count characters))))))

(local
 (defthm take-three-bytes
   (implies (and (integerp count) (<= 3 count))
            (equal (take count characters)
                   (list* (car characters) (cadr characters) (caddr characters)
                          (take (- count 3) (cdddr characters)))))
   :rule-classes nil))

(defthmd data-escaped-spelling-is-its-character-encoding
  (implies (and (natp start) (stringp text)
                (data-escaped-spelling-p characters text start count delimiter))
           (equal (take count (nthcdr start (coerce text 'list)))
                  (data-escape-characters characters delimiter)))
  :hints (("Goal" :induct (data-escaped-spelling-p characters text start count delimiter)
                  :in-theory (disable floor mod data-hex-digit-character take nthcdr
                                      data-character-printed-literally-p))
          ("Subgoal *1/6" :use ((:instance take-three-bytes (characters (nthcdr start (coerce text 'list))))))))

(local
 (defun plain-character-list-p (characters)
   (if (atom characters)
       (null characters)
     (and (boymoo-compiler::plain-symbol-char-p (car characters))
          (plain-character-list-p (cdr characters))))))

(local
 (defthm plain-symbol-span-is-a-plain-character-list
   (implies (and (stringp text) (natp start) (natp count))
            (equal (boymoo-compiler::plain-symbol-part-p text start count)
                   (plain-character-list-p (take count (nthcdr start (coerce text 'list))))))
   :hints (("Goal" :induct (boymoo-compiler::plain-symbol-part-p text start count)
                   :in-theory (disable boymoo-compiler::plain-symbol-char-p take nthcdr)))))

(local
 (defthm take-of-characters-has-the-requested-length
   (implies (natp count)
            (equal (len (take count characters)) count))))

(local
 (defthm take-of-characters-within-length-is-character-list
   (implies (and (natp count) (<= count (len characters)) (character-listp characters))
            (character-listp (take count characters)))))

(local
 (defthm string-has-list-of-characters
   (implies (stringp text) (character-listp (coerce text 'list)))))

(local
 (defthm suffix-of-character-list-is-character-list
   (implies (character-listp characters) (character-listp (nthcdr start characters)))
   :hints (("Goal" :induct (nthcdr start characters)))))

(local
 (defthm length-of-in-range-suffix
   (implies (and (natp start) (<= start (len characters)))
            (equal (len (nthcdr start characters)) (- (len characters) start)))
   :hints (("Goal" :induct (nthcdr start characters)))))

(local
 (defthm string-slice-is-subseq-character-list
   (implies (and (stringp text) (natp start) (natp end) (<= start end) (<= end (length text)))
            (equal (coerce (subseq text start end) 'list)
                   (take (- end start) (nthcdr start (coerce text 'list)))))
   :hints (("Goal" :in-theory (e/d (length subseq acl2::subseq-list) (take nthcdr))))))

(local
 (defthm take-within-suffix-extends-by-one-byte
   (implies (natp count)
            (equal (take (1+ count) characters)
                   (append (take count characters) (list (nth count characters)))))
   :hints (("Goal" :induct (take count characters)))))

(local
 (defthm nth-in-suffix
   (implies (and (natp start) (natp count))
            (equal (nth count (nthcdr start characters)) (nth (+ start count) characters)))
   :hints (("Goal" :induct (nthcdr start characters)))))

(defun data-symbol-part-characters (part)
  (let ((length (length part)) (characters (coerce part 'list)))
    (if (and (< 0 length) (boymoo-compiler::plain-symbol-part-p part 0 length))
        characters
      (cons #\| (append (data-escape-characters characters #\|) (list #\|))))))

(local
 (defthm taking-all-characters-returns-them
   (implies (true-listp characters) (equal (take (len characters) characters) characters))
   :hints (("Goal" :induct (len characters)
                   :in-theory (disable take-within-suffix-extends-by-one-byte take)))))

(local
 (defthm bare-spelling-selects-bare-encoding
   (implies (and (data-symbol-part-spelling-p text start end part)
                 (not (equal (char text start) #\|)))
            (and (< 0 (length part)) (boymoo-compiler::plain-symbol-part-p part 0 (length part))))
   :hints (("Goal" :use ((:instance plain-symbol-span-is-a-plain-character-list (count (- end start)))
                         (:instance plain-symbol-span-is-a-plain-character-list
                                    (text part) (start 0) (count (length part))))
                   :in-theory (e/d (length)
                                  (plain-symbol-span-is-a-plain-character-list subseq
                                   boymoo-compiler::plain-symbol-part-p boymoo-compiler::plain-symbol-char-p
                                   char data-delimited-text-p take nthcdr))))))

(local
 (defthm take-slice-including-two-delimiters
   (implies (and (natp start) (integerp end) (<= (+ start 2) end))
            (equal (take (- end start) (nthcdr start characters))
                   (cons (nth start characters)
                         (append (take (- end (+ start 2)) (nthcdr (1+ start) characters))
                                 (list (nth (1- end) characters))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance take-one-byte (count (- end start)) (characters (nthcdr start characters)))
                         (:instance take-within-suffix-extends-by-one-byte
                                    (count (- end (+ start 2))) (characters (nthcdr (1+ start) characters)))
                         (:instance nth-in-suffix (count (- end (+ start 2))) (start (1+ start))))
                   :in-theory (disable take nthcdr take-one-byte take-within-suffix-extends-by-one-byte
                                       nth-in-suffix)))))

(local
 (in-theory (disable take nthcdr take-within-suffix-extends-by-one-byte
                     boymoo-compiler::plain-symbol-part-p boymoo-compiler::plain-symbol-char-p
                     data-escaped-spelling-p data-escape-characters floor mod subseq
                     data-hex-digit-character length)))

(local
 (defthm bare-symbol-part-spells-its-character-encoding
   (implies (and (data-symbol-part-spelling-p text start end part) (not (equal (char text start) #\|)))
            (equal (take (- end start) (nthcdr start (coerce text 'list)))
                   (data-symbol-part-characters part)))
   :rule-classes nil
   :hints (("Goal" :use (bare-spelling-selects-bare-encoding string-slice-is-subseq-character-list)
                   :in-theory (disable bare-spelling-selects-bare-encoding string-slice-is-subseq-character-list
                                       data-delimited-text-p char)))))

(local
 (defthm barred-symbol-part-spells-its-character-encoding
   (implies (and (data-symbol-part-spelling-p text start end part) (equal (char text start) #\|))
            (equal (take (- end start) (nthcdr start (coerce text 'list)))
                   (data-symbol-part-characters part)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance take-slice-including-two-delimiters (characters (coerce text 'list)))
                         (:instance data-escaped-spelling-is-its-character-encoding
                                    (characters (coerce part 'list)) (start (1+ start))
                                    (count (- end (+ start 2))) (delimiter #\|)))
                   :in-theory (disable take-one-byte)
                   :do-not-induct t))))

(defthmd data-symbol-part-spelling-is-its-character-encoding
  (implies (data-symbol-part-spelling-p text start end part)
           (equal (take (- end start) (nthcdr start (coerce text 'list)))
                  (data-symbol-part-characters part)))
  :hints (("Goal" :use (bare-symbol-part-spells-its-character-encoding barred-symbol-part-spells-its-character-encoding)
                  :in-theory (disable data-symbol-part-spelling-p data-symbol-part-characters char))))

(local
 (defthm split-list-at-position
   (implies (and (true-listp xs) (natp split) (<= split (len xs)))
            (equal (append (take split xs) (nthcdr split xs)) xs))
   :hints (("Goal" :induct (nthcdr split xs)
                   :in-theory (enable nthcdr)))))

(local
 (defthm in-range-suffix-is-a-cons
   (implies (and (natp index) (< index (len characters))) (consp (nthcdr index characters)))
   :hints (("Goal" :induct (nthcdr index characters) :in-theory (enable nthcdr)))))

(local
 (defthm suffix-after-two-separators
   (implies (and (natp split) (< (1+ split) (len characters)))
            (equal (nthcdr split characters)
                   (list* (nth split characters) (nth (1+ split) characters) (nthcdr (+ 2 split) characters))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::cons-car-cdr (acl2::x (nthcdr split characters)))
                         (:instance acl2::cons-car-cdr (acl2::x (nthcdr (1+ split) characters))))
                   :in-theory (disable acl2::cons-car-cdr)))))

(local
 (defthm whole-suffix-is-its-full-slice
   (implies (and (true-listp characters) (natp start) (<= start (len characters)))
            (equal (take (- (len characters) start) (nthcdr start characters)) (nthcdr start characters)))
   :hints (("Goal" :use (length-of-in-range-suffix
                         (:instance taking-all-characters-returns-them (characters (nthcdr start characters))))
                   :in-theory (e/d (nthcdr) (taking-all-characters-returns-them length-of-in-range-suffix))))))

(local
 (defthm symbol-spelling-bounds-and-separators
   (implies (data-symbol-spelling-p text split package name)
            (and (stringp text) (natp split) (< (+ 2 split) (length text))
                 (equal (char text split) #\:) (equal (char text (1+ split)) #\:)
                 (data-symbol-part-spelling-p text 0 split package)
                 (data-symbol-part-spelling-p text (+ 2 split) (length text) name)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-symbol-spelling-p text split package name))))
   :hints (("Goal" :in-theory (disable data-delimited-text-p char)))))

(defthmd data-canonical-symbol-text-is-its-character-encoding
  (implies (data-symbol-spelling-p text split package name)
           (equal (coerce text 'list)
                  (append (data-symbol-part-characters package) (list #\: #\:)
                          (data-symbol-part-characters name))))
  :hints (("Goal" :use (symbol-spelling-bounds-and-separators
                        (:instance data-symbol-part-spelling-is-its-character-encoding (start 0) (end split) (part package))
                        (:instance data-symbol-part-spelling-is-its-character-encoding
                                   (start (+ 2 split)) (end (length text)) (part name))
                        (:instance split-list-at-position (xs (coerce text 'list)))
                        (:instance suffix-after-two-separators (characters (coerce text 'list)))
                        (:instance whole-suffix-is-its-full-slice
                                   (start (+ 2 split)) (characters (coerce text 'list))))
                  :in-theory (e/d (length)
                                 (data-symbol-spelling-p data-symbol-part-characters data-symbol-part-spelling-p
                                  data-escape-characters take nthcdr nth len split-list-at-position
                                  whole-suffix-is-its-full-slice symbol-spelling-bounds-and-separators))
                  :do-not-induct t)))

(defthm data-canonical-symbol-spellings-are-unique
  (implies (and (data-symbol-spelling-p left left-split package name)
                (data-symbol-spelling-p right right-split package name))
           (equal left right))
  :rule-classes nil
  :hints (("Goal" :use ((:instance data-canonical-symbol-text-is-its-character-encoding (text left) (split left-split))
                        (:instance data-canonical-symbol-text-is-its-character-encoding (text right) (split right-split))
                        (:instance acl2::coerce-inverse-2 (acl2::x left))
                        (:instance acl2::coerce-inverse-2 (acl2::x right)))
                  :in-theory (disable data-symbol-spelling-p data-symbol-part-characters acl2::coerce-inverse-2))))

(defthm data-one-symbol-spelling-cannot-denote-two-source-symbols
  (implies (and (data-source-symbol-agrees-p text first) (data-source-symbol-agrees-p text second))
           (equal first second))
  :rule-classes nil
  :hints (("Goal" :use ((:instance acl2::intern-in-package-of-symbol-symbol-name
                                   (acl2::x first) (acl2::y second))
                        (:instance acl2::intern-in-package-of-symbol-symbol-name
                                   (acl2::x second) (acl2::y second)))
                  :in-theory (disable boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                                      acl2::intern-in-package-of-symbol-symbol-name length))))
