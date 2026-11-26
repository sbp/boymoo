(in-package "BOYMOO-PROOFS")

(include-book "strings")
(include-book "image")
(include-book "views")
(include-book "tables")

(logic)
(set-verify-guards-eagerness 0)

(defun data-string-object-chunks (string)
  (list (+ 1 (* 256 (length string))) string))

(defthmd data-text-allocates-string-object
  (implies (and (stringp string) (integerp (car block)))
           (equal (mv-list 2 (boymoo-compiler::data-text 1 string block))
                  (list (+ 2 (car block))
                        (cons (+ 8 (car block) (boymoo-compiler::aligned-size (length string) 3))
                              (boymoo-compiler::reverse-onto (data-string-object-chunks string) (cdr block))))))
  :hints (("Goal" :in-theory (e/d (data-ash-left) (ash length boymoo-compiler::aligned-size)))))

(local
 (in-theory (disable char length boymoo-compiler::decode-part boymoo-compiler::index-get
                     boymoo-compiler::index-set boymoo-compiler::data-text data-delimited-text-p
                     boymoo-compiler::data-symbol boymoo-compiler::data-number
                     boymoo-compiler::read-lines boymoo-compiler::data-datum)))

(defun data-quoted-string-text-p (text characters)
  (and (equal (char text 0) #\") (data-delimited-text-p text 0 (length text) characters)))

(defthmd data-uncached-string-allocates-decoded-text
  (implies (and (data-quoted-string-text-p text characters)
                (not (boymoo-compiler::index-get text (cadr state-data))))
           (mv-let (word block)
             (boymoo-compiler::data-text 1 (coerce characters 'string) (boymoo-compiler::data-block state-data))
             (equal (mv-list 2 (boymoo-compiler::data-atom text packages state-data))
                    (list word
                          (boymoo-compiler::data-remember
                           text word (boymoo-compiler::data-with-block block state-data))))))
  :hints (("Goal" :use ((:instance data-decode-canonical-delimited-text (start 0) (end (length text))))
                  :in-theory (disable boymoo-compiler::data-remember boymoo-compiler::data-with-block))))

(local
 (defthm quoted-string-text-is-string
   (implies (data-quoted-string-text-p text characters) (stringp text))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-delimited-text-p)))))

(local
 (defthm type-one-object-reference
   (equal (car (boymoo-compiler::data-text 1 string block)) (+ 2 (car block)))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-text)))))

(defthmd data-constant-records-canonical-string
  (let* ((block (boymoo-compiler::data-block state-data))
         (old (boymoo-compiler::index-get text (cadr state-data)))
         (next (boymoo-compiler::data-constant text packages state-data)))
    (implies (and (data-quoted-string-text-p text characters) (data-table-p (cadr state-data) 12))
             (equal (boymoo-compiler::index-get text (cadr next)) (or old (+ 2 (car block))))))
  :hints (("Goal" :use (quoted-string-text-is-string
                       (:instance data-decode-canonical-delimited-text (start 0) (end (length text))))
                  :in-theory (disable boymoo-compiler::data-block data-table-p
                                      quoted-string-text-is-string))))

(local
 (in-theory (disable data-placed-characters-p proof-load-word proof-load-string
                     proof-word-tag proof-pointer-address proof-span-p evenp ash)))

(local
 (defthm string-chunk-characters-are-a-list
   (true-listp (data-chunk-characters chunk))
   :hints (("Goal" :use data-chunk-characters-are-characters))))

(local
 (defthm placed-text-chunk-loads-exact-string
   (implies (and (stringp string) (integerp address)
                 (data-placed-characters-p (data-chunk-characters string) address machine))
            (equal (proof-load-string (length string) address machine) string))
   :hints (("Goal" :use ((:instance data-load-string-places-characters
                                    (characters (coerce string 'list))))
                   :in-theory (e/d (length)
                                  (boymoo-compiler::aligned-size data-zero-characters))))))

(defthmd data-view-of-placed-string-object
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (chunks (data-string-object-chunks string)))
    (implies (and (stringp string) (unsigned-byte-p 64 (car chunks))
                  (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (natp (proof-object-rank object)) (eq (proof-object-kind object) :header)
                  (proof-span-p address (+ 8 (length string)))
                  (data-placed-characters-p (data-forward-chunk-characters chunks) address machine))
             (proof-value-p word string base objects packages machine)))
  :hints (("Goal" :use (data-view-of-static-string-fields
                       (:instance data-placed-u64-chunks-load-their-words
                                  (words (list (+ 1 (* 256 (length string)))))
                                  (address (proof-pointer-address word base)))
                       (:instance placed-text-chunk-loads-exact-string
                                  (address (+ 8 (proof-pointer-address word base)))))
                  :in-theory (disable data-chunk-characters
                                      proof-value-p placed-text-chunk-loads-exact-string))))

(defthmd data-canonical-string-constant-map-agreement
  (let* ((block (boymoo-compiler::data-block state-data))
         (string (coerce characters 'string))
         (old (boymoo-compiler::index-get text (cadr state-data)))
         (word (or old (+ 2 (car block))))
         (next (boymoo-compiler::data-constant text package-index state-data))
         (address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (chunks (data-string-object-chunks string)))
    (implies (and (data-quoted-string-text-p text characters) (data-table-p (cadr state-data) 12)
                  (unsigned-byte-p 64 (car chunks)) (unsigned-byte-p 64 word)
                  (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (natp (proof-object-rank object)) (eq (proof-object-kind object) :header)
                  (proof-span-p address (+ 8 (length string)))
                  (data-placed-characters-p (data-forward-chunk-characters chunks) address machine))
             (proof-constant-map-p (list (cons text string)) (cadr next) base objects packages machine)))
  :hints (("Goal" :use ((:instance data-constant-records-canonical-string (packages package-index))
                       (:instance data-view-of-placed-string-object
                                  (string (coerce characters 'string))
                                  (word (or (boymoo-compiler::index-get text (cadr state-data))
                                            (+ 2 (car (boymoo-compiler::data-block state-data)))))))
                  :in-theory (disable boymoo-compiler::data-constant boymoo-compiler::data-block
                                      data-quoted-string-text-p data-string-object-chunks
                                      data-forward-chunk-characters data-table-p proof-value-p))))
