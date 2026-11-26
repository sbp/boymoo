(in-package "BOYMOO-PROOFS")

(include-book "image")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-load-string data-placed-characters-p
                     boymoo-compiler::prepend-word boymoo-compiler::prepend-integer
                     boymoo-model::a64-load boymoo-compiler::low-bits)))

(defthmd data-placed-chunk-loads-encoded-word
  (let ((word (proof-constant-word chunk)))
    (implies (and word (integerp address)
                  (data-placed-characters-p (data-chunk-characters chunk) address machine))
             (equal (proof-load-word address machine) word)))
  :hints (("Goal" :use ((:instance data-load-placed-word (characters (data-chunk-characters chunk)))
                        (:instance data-read-serialized-immediate-word (integer (cdr chunk)))
                        (:instance data-read-serialized-word (word chunk)))
                  :in-theory (enable proof-load-word))))

(defun data-encodable-chunks-p (chunks)
  (if (atom chunks)
      (null chunks)
    (and (proof-constant-word (car chunks)) (data-encodable-chunks-p (cdr chunks)))))

(defun data-encoded-words (chunks)
  (if (atom chunks)
      nil
    (cons (proof-constant-word (car chunks)) (data-encoded-words (cdr chunks)))))

(local
 (defthm encodable-chunk-is-a-word
   (implies (proof-constant-word chunk)
            (and (not (stringp chunk)) (equal (data-chunk-size chunk) 8)))))

(local
 (defthm chunk-characters-form-a-list
   (true-listp (data-chunk-characters chunk))
   :hints (("Goal" :use data-chunk-characters-are-characters
                   :in-theory (disable data-chunk-characters)))))

(local
 (defun encoded-chunks-induction (chunks address)
   (if (atom chunks)
       address
     (encoded-chunks-induction (cdr chunks) (+ address 8)))))

(defthmd data-placed-encodable-chunks-load-their-words
  (implies (and (data-encodable-chunks-p chunks) (integerp address)
                (data-placed-characters-p (data-forward-chunk-characters chunks) address machine))
           (data-memory-words-p (data-encoded-words chunks) address machine))
  :hints (("Goal" :induct (encoded-chunks-induction chunks address)
                  :in-theory (disable data-chunk-characters data-chunk-size proof-constant-word))
          ("Subgoal *1/2" :use ((:instance data-placed-chunk-loads-encoded-word (chunk (car chunks)))))))

(local
 (defthm string-byte-list-has-string-length
   (implies (stringp string)
            (and (true-listp (coerce string 'list)) (character-listp (coerce string 'list))
                 (equal (len (coerce string 'list)) (length string))))))

(defthmd data-placed-string-chunk-loads-text
  (implies (and (stringp string) (integerp address)
                (data-placed-characters-p (data-chunk-characters string) address machine))
           (equal (proof-load-string (length string) address machine) string))
  :hints (("Goal" :use ((:instance data-load-string-places-characters (characters (coerce string 'list))))
                  :in-theory (disable data-zero-characters boymoo-compiler::aligned-size length))))

(defthmd data-placed-string-allocation-loads-fields
  (let ((header (+ 1 (* 256 (length string)))))
    (implies (and (stringp string) (integerp address) (unsigned-byte-p 64 header)
                  (data-placed-characters-p (data-forward-chunk-characters (list header string))
                                            address machine))
             (and (equal (proof-load-word address machine) header)
                  (equal (proof-load-string (length string) (+ 8 address) machine) string))))
  :hints (("Goal" :use ((:instance data-placed-chunk-loads-encoded-word
                                   (chunk (+ 1 (* 256 (length string)))))
                        (:instance data-placed-string-chunk-loads-text (address (+ 8 address))))
                  :in-theory (disable data-chunk-characters length))))

(defthmd data-view-of-placed-string-allocation
  (let* ((address (proof-pointer-address word base))
         (size (length string))
         (object (assoc-equal address objects)))
    (implies (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (natp (proof-object-rank object)) (eq (proof-object-kind object) :header)
                  (stringp string) (proof-span-p address (+ 8 size))
                  (unsigned-byte-p 64 (+ 1 (* 256 size)))
                  (data-placed-characters-p (data-forward-chunk-characters (list (+ 1 (* 256 size)) string))
                                            address machine))
             (proof-value-p word string base objects packages machine)))
  :hints (("Goal" :use (data-view-of-static-string-fields
                        (:instance data-placed-string-allocation-loads-fields
                                   (address (proof-pointer-address word base))))
                  :in-theory (disable proof-pointer-address proof-word-tag proof-value-p
                                      proof-span-p data-forward-chunk-characters length evenp))))
