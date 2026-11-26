(in-package "BOYMOO-PROOFS")

(include-book "token-spans")
(include-book "source")
(include-book "allocation")

(logic)
(set-verify-guards-eagerness 0)

(defun data-symbol-part-spelling-p (text start end part)
  (and (stringp text) (stringp part) (natp start) (natp end) (< start end) (<= end (length text))
       (if (equal (char text start) #\|)
           (and (data-delimited-text-p text start end (coerce part 'list))
                (or (equal (length part) 0)
                    (not (boymoo-compiler::plain-symbol-part-p part 0 (length part)))))
         (and (boymoo-compiler::plain-symbol-part-p text start (- end start))
              (equal (subseq text start end) part)))))

(defun data-symbol-spelling-p (text split package name)
  (and (natp split) (equal (char text split) #\:) (equal (char text (1+ split)) #\:)
       (data-symbol-part-spelling-p text 0 split package)
       (data-symbol-part-spelling-p text (+ split 2) (length text) name)))

(local
 (in-theory (disable char length subseq data-delimited-text-p
                     boymoo-compiler::symbol-separator boymoo-compiler::find-char)))

(local
 (defthm spelling-of-a-symbol-part-has-string-text
   (implies (data-symbol-part-spelling-p text start end part) (stringp text))
   :rule-classes :forward-chaining))

(defthmd data-decode-canonical-symbol-part
  (implies (data-symbol-part-spelling-p text start end part)
           (equal (boymoo-compiler::decode-symbol-part text start end) part))
  :hints (("Goal" :use ((:instance data-decode-canonical-barred-symbol-part (characters (coerce part 'list))))
                  :in-theory (disable boymoo-compiler::plain-symbol-part-p boymoo-compiler::decode-part))))

(local
 (defthm absence-is-an-unsuccessful-search
   (implies (natp start)
            (equal (data-byte-absent-p text start count byte)
                   (not (boymoo-compiler::find-char text start count byte))))
   :hints (("Goal" :induct (data-byte-absent-p text start count byte)
                   :in-theory (enable boymoo-compiler::find-char)))))

(local
 (defthm plain-symbol-part-has-no-colon
   (implies (boymoo-compiler::plain-symbol-part-p text start count)
            (data-byte-absent-p text start count #\:))
   :hints (("Goal" :induct (boymoo-compiler::plain-symbol-part-p text start count)
                   :in-theory (disable absence-is-an-unsuccessful-search)))))

(local
 (defthm plain-symbol-part-starts-with-plain-byte
   (implies (and (posp count) (boymoo-compiler::plain-symbol-part-p text start count))
            (boymoo-compiler::plain-symbol-char-p (char text start)))
   :hints (("Goal" :expand ((boymoo-compiler::plain-symbol-part-p text start count))))))

(local
 (defthm canonical-barred-part-has-delimiters
   (implies (and (data-delimited-text-p text 0 split characters) (equal (char text 0) #\|))
            (and (integerp split) (<= 2 split) (equal (char text (1- split)) #\|)
                 (data-byte-absent-p text 1 (- split 2) #\|)))
   :hints (("Goal" :use ((:instance data-canonical-content-has-no-raw-delimiter
                                    (delimiter #\|) (start 1) (count (- split 2))))
                   :in-theory (enable data-delimited-text-p)))))

(local
 (defthm length-of-initial-delimited-body-and-suffix
   (and (equal (+ split (- size split)) (fix size))
        (equal (+ (- split 2) (+ 1 (- size split))) (1- size)))
   :rule-classes nil))

(defthmd data-canonical-symbol-separator
  (implies (data-symbol-spelling-p text split package name)
           (equal (boymoo-compiler::symbol-separator text) split))
  :hints (("Goal" :use ((:instance data-find-byte-after-prefix
                                   (start 0) (count split) (byte #\:) (suffix (- (length text) split)))
                        (:instance data-find-byte-after-prefix
                                   (start 1) (count (- split 2)) (byte #\|)
                                   (suffix (+ 1 (- (length text) split))))
                        (:instance length-of-initial-delimited-body-and-suffix (size (length text)))
                        (:instance canonical-barred-part-has-delimiters (characters (coerce package 'list)))
                        (:instance plain-symbol-part-starts-with-plain-byte (start 0) (count split))
                        (:instance plain-symbol-part-has-no-colon (start 0) (count split)))
                  :in-theory (e/d (boymoo-compiler::symbol-separator)
                                 (absence-is-an-unsuccessful-search data-byte-absent-p
                                  boymoo-compiler::plain-symbol-char-p
                                  boymoo-compiler::plain-symbol-part-p plain-symbol-part-has-no-colon
                                  plain-symbol-part-starts-with-plain-byte canonical-barred-part-has-delimiters)))))

(defthmd data-canonical-symbol-denotes-source-symbol
  (implies (and (symbolp symbol)
                (data-symbol-spelling-p text split (symbol-package-name symbol) (symbol-name symbol)))
           (data-source-symbol-agrees-p text symbol))
  :hints (("Goal" :use ((:instance data-canonical-symbol-separator
                                   (package (symbol-package-name symbol)) (name (symbol-name symbol)))
                        (:instance data-decode-canonical-symbol-part
                                   (start 0) (end split) (part (symbol-package-name symbol)))
                        (:instance data-decode-canonical-symbol-part
                                   (start (+ split 2)) (end (length text)) (part (symbol-name symbol))))
                  :in-theory (disable data-symbol-part-spelling-p
                                      boymoo-compiler::decode-symbol-part))))

(defthm data-related-source-symbol-fits-storage
  (implies (data-source-symbol-agrees-p text symbol)
           (data-symbol-storage-input-p text))
  :hints (("Goal" :in-theory (disable boymoo-compiler::decode-symbol-part))))
