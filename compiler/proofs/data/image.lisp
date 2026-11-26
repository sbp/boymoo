(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-placed-characters-p proof-load-string
                     boymoo-compiler::data-write proof-load-word)))

(local
 (defthm character-list-from-string
   (implies (stringp text) (character-listp (coerce text 'list)))))

(local
 (defthm true-list-from-character-list
   (implies (character-listp chars) (true-listp chars))))

(local
 (defthm placed-empty-character-list
   (data-placed-characters-p nil address machine)
   :hints (("Goal" :in-theory (enable data-placed-characters-p)))))

(local
 (defthm string-at-address-places-characters
   (implies (and (stringp text) (integerp address)
                 (equal (proof-load-string (length text) address machine) text))
            (data-placed-characters-p (coerce text 'list) address machine))
   :hints (("Goal" :use ((:instance data-load-string-places-characters
                                    (characters (coerce text 'list))))))))

(defthmd data-placed-fragments-agree-with-flattened-bytes
  (implies (and (proof-fragments-p fragments) (integerp address)
                (proof-fragments-at-p fragments address machine))
           (data-placed-characters-p (data-fragment-characters fragments) address machine))
  :hints (("Goal" :induct (proof-fragments-at-p fragments address machine))))

(local
 (defthm header-characters-have-length-eighty
   (let ((header (car (data-image-parts lines package-lines))))
     (implies header (equal (len (data-forward-chunk-characters header)) 80)))
   :hints (("Goal" :use ((:instance data-forward-chunk-characters-size
                                    (chunks (car (data-image-parts lines package-lines)))))
                   :in-theory (disable data-image-parts data-forward-chunk-characters)))))

(local
 (defthm character-list-from-data-header
   (true-listp (data-forward-chunk-characters chunks))
   :hints (("Goal" :use data-forward-chunk-characters-are-characters))))

(defthmd data-build-places-body-chunks
  (let* ((parts (data-image-parts lines package-lines))
         (image (car (boymoo-compiler::data-build lines package-lines))))
    (implies (and (car parts) (proof-image-at-p image base machine))
             (data-placed-characters-p (data-chunks-characters (mv-nth 1 parts)) (+ base 80) machine)))
  :hints (("Goal" :use ((:instance data-placed-fragments-agree-with-flattened-bytes
                                   (fragments (cdr (car (boymoo-compiler::data-build lines package-lines))))
                                   (address base))
                       data-build-header-fragment)
                  :in-theory (disable boymoo-compiler::data-build data-image-parts
                                      proof-fragments-p proof-fragments-at-p proof-fragments-size
                                      data-forward-chunk-characters data-chunks-characters))))

(local
 (defthm append-associative-for-chunk-characters
   (equal (append (append first second) third) (append first second third))))

(local
 (defthm reverse-chunk-characters-of-append
   (equal (data-chunks-characters (append later earlier))
          (append (data-chunks-characters earlier) (data-chunks-characters later)))
   :hints (("Goal" :induct (append later earlier)))))

(local
 (defthm true-list-of-reverse-chunk-characters
   (true-listp (data-chunks-characters reversed))
   :hints (("Goal" :use data-chunks-characters-are-characters))))

(defthmd data-placed-allocation-chunks
  (implies (and (integerp address)
                (data-placed-characters-p
                 (data-chunks-characters (append later (boymoo-compiler::reverse-onto allocated earlier)))
                 address machine))
           (data-placed-characters-p (data-forward-chunk-characters allocated)
                                     (+ address (data-chunks-size earlier)) machine))
  :hints (("Goal" :in-theory (disable data-forward-chunk-characters data-chunks-characters
                                      boymoo-compiler::reverse-onto data-chunks-size))))

(defun data-u64-word-list-p (words)
  (if (atom words)
      (null words)
    (and (unsigned-byte-p 64 (car words)) (data-u64-word-list-p (cdr words)))))

(defun data-memory-words-p (words address machine)
  (if (atom words)
      (null words)
    (and (equal (proof-load-word address machine) (car words))
         (data-memory-words-p (cdr words) (+ address 8) machine))))

(local
 (defthm unsigned-word-has-eight-characters
   (implies (unsigned-byte-p 64 word)
            (equal (len (data-chunk-characters word)) 8))))

(local
 (defthm placed-u64-chunk-loads-its-value
   (implies (and (unsigned-byte-p 64 word) (integerp address)
                 (data-placed-characters-p (data-chunk-characters word) address machine))
            (equal (proof-load-word address machine) word))
   :hints (("Goal" :use (data-load-serialized-word)
                   :in-theory (disable boymoo-compiler::prepend-word)))))

(local
 (defthm true-list-from-chunk-characters
   (true-listp (data-chunk-characters chunk))
   :hints (("Goal" :use data-chunk-characters-are-characters))))

(local
 (defun placed-words-induction (words address)
   (if (atom words)
       address
     (placed-words-induction (cdr words) (+ address 8)))))

(defthmd data-placed-u64-chunks-load-their-words
  (implies (and (data-u64-word-list-p words) (integerp address)
                (data-placed-characters-p (data-forward-chunk-characters words) address machine))
           (data-memory-words-p words address machine))
  :hints (("Goal" :induct (placed-words-induction words address)
                  :in-theory (disable data-chunk-characters placed-u64-chunk-loads-its-value))
          ("Subgoal *1/2" :use ((:instance placed-u64-chunk-loads-its-value (word (car words)))))))
