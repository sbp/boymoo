(in-package "BOYMOO-PROOFS")

(include-book "macho-hash-range")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-fragment-position-p (chunks at)
  (and (proof-fragments-p chunks) (natp at)
       (if (consp chunks) (<= at (length (car chunks))) (equal at 0))))

(defun assembly-fragment-remaining-characters (chunks at)
  (nthcdr at (assembly-fragment-characters chunks)))

(defun assembly-page-prefix (count chars)
  (take (min (nfix count) (len chars)) chars))

(defun assembly-page-string (count chars)
  (coerce (append (assembly-page-prefix count chars)
                  (assembly-zero-characters (- (nfix count) (len (assembly-page-prefix count chars)))))
          'string))

(local
 (defthm assembly-length-of-page-characters-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm assembly-length-of-page-characters-suffix
   (implies (and (natp at) (<= at (len chars)))
            (equal (len (nthcdr at chars)) (- (len chars) at)))
   :hints (("Goal" :induct (nthcdr at chars)))))

(local
 (defthm assembly-characters-of-page-suffix
   (implies (character-listp chars)
            (character-listp (nthcdr at chars)))))

(local
 (defthm assembly-characters-of-page-take
   (implies (and (natp count) (<= count (len chars)) (character-listp chars))
            (character-listp (take count chars)))))

(local
 (defthm assembly-take-whole-page-prefix
   (implies (true-listp prefix)
            (equal (take (len prefix) prefix) prefix))
   :hints (("Goal" :induct (len prefix)))))

(local
 (defthm assembly-take-before-end-of-page-prefix
   (implies (and (natp count) (<= count (len prefix)))
            (equal (take count (append prefix suffix)) (take count prefix)))
   :hints (("Goal" :induct (take count prefix)))))

(local
 (defthm assembly-take-through-page-prefix
   (implies (and (natp count) (<= (len prefix) count))
            (equal (take count (append prefix suffix))
                   (append prefix (take (- count (len prefix)) suffix))))
   :hints (("Goal" :induct (take count prefix)))))

(local
 (defthm assembly-nthcdr-past-page-prefix
   (implies (and (natp count) (<= (len prefix) count))
            (equal (nthcdr count (append prefix suffix))
                   (nthcdr (- count (len prefix)) suffix)))
   :hints (("Goal" :induct (nthcdr count prefix)))))

(local
 (defthm assembly-nthcdr-within-page-prefix
   (implies (and (natp count) (<= count (len prefix)))
            (equal (nthcdr count (append prefix suffix))
                   (append (nthcdr count prefix) suffix)))
   :hints (("Goal" :induct (nthcdr count prefix)))))

(local
 (defthm assembly-sha256-nthcdr-of-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr b (nthcdr a chars)) (nthcdr (+ a b) chars)))
   :hints (("Goal" :induct (nthcdr a chars)))))

(local
 (defthm assembly-span-of-subseq-list
   (implies (and (natp start) (natp end) (<= start end))
            (equal (acl2::subseq-list chars start end)
                   (take (- end start) (nthcdr start chars))))))

(local
 (defthm assembly-characters-of-string-subseq
   (implies (and (stringp text) (natp start) (natp end)
                 (<= start end) (<= end (length text)))
            (equal (coerce (subseq text start end) 'list)
                   (take (- end start) (nthcdr start (coerce text 'list)))))))

(local
 (defthm assembly-page-prefix-within-fragment
   (implies (and (natp count) (<= count (len prefix)))
            (equal (assembly-page-prefix count (append prefix tail))
                   (take count prefix)))))

(local
 (defthm assembly-page-prefix-crosses-fragment
   (implies (and (true-listp prefix) (natp count) (<= (len prefix) count))
            (equal (assembly-page-prefix count (append prefix tail))
                   (append prefix (assembly-page-prefix (- count (len prefix)) tail))))))

(local
 (defthm assembly-append-fragment-characters
   (equal (assembly-fragment-characters (append first rest))
          (append (assembly-fragment-characters first) (assembly-fragment-characters rest)))))

(local
 (defthm assembly-fragment-characters-after-position
   (implies (and (consp chunks) (assembly-fragment-position-p chunks at))
            (equal (assembly-fragment-remaining-characters chunks at)
                   (append (nthcdr at (coerce (car chunks) 'list))
                           (assembly-fragment-characters (cdr chunks)))))))

(local
 (defthm assembly-sha256-reverse-onto-is-revappend
   (equal (boymoo-compiler::reverse-onto chunks tail) (revappend chunks tail))))

(local
 (defthm assembly-append-after-reversing-page-pieces
   (equal (append (revappend pieces rest) tail)
          (revappend pieces (append rest tail)))))

(local
 (defthm assembly-page-append-associative
   (equal (append (append first second) rest)
          (append first (append second rest)))))

(local
 (defthm assembly-fragment-characters-at-start
   (equal (assembly-fragment-remaining-characters chunks 0)
          (assembly-fragment-characters chunks))))

(local
 (defthm assembly-fragment-characters-of-revappend
   (implies (consp tail)
            (equal (assembly-fragment-characters (revappend pieces tail))
                   (append (assembly-fragment-characters (revappend pieces nil))
                           (assembly-fragment-characters tail))))
   :hints (("Goal"
            :use ((:instance assembly-append-fragment-characters
                             (first (revappend pieces nil)) (rest tail)))
            :in-theory (disable assembly-append-fragment-characters)))))

(local
 (defthm assembly-take-string-suffix-through-end
   (implies (and (stringp text) (natp start) (<= start (len (coerce text 'list))))
            (equal (take (+ (- start) (len (coerce text 'list)))
                         (nthcdr start (coerce text 'list)))
                   (nthcdr start (coerce text 'list))))
   :hints (("Goal"
            :use ((:instance assembly-take-whole-page-prefix
                             (prefix (nthcdr start (coerce text 'list)))))
            :in-theory (disable assembly-take-whole-page-prefix)))))

(local
 (defthm assembly-page-nthcdr-through-end
   (implies (true-listp chars)
            (equal (nthcdr (len chars) chars) nil))))

(local
 (defthm assembly-page-empty-prefix
   (equal (assembly-page-prefix count nil) nil)))

(local
 (defthm assembly-page-prefix-of-zero
   (equal (assembly-page-prefix 0 chars) nil)))

(local
 (defthm assembly-characters-after-empty-fragment-position
   (implies (not (consp chunks))
            (equal (assembly-fragment-remaining-characters chunks at) nil))))

(local
 (defthm assembly-sha256-fragments-after-revappend
   (implies (and (proof-fragments-p pieces) (proof-fragments-p rest))
            (proof-fragments-p (revappend pieces rest)))))

(local
 (defthm assembly-page-result-component-of-cons
   (equal (mv-nth n (cons first rest))
          (if (zp n) first (mv-nth (1- n) rest)))))

(local (in-theory (disable mv-nth boymoo-compiler::reverse-onto
                           assembly-page-prefix subseq
                           assembly-fragment-remaining-characters)))

(defthm assembly-sha256-page-pieces-exact
  (mv-let (output rest next)
    (boymoo-compiler::sha256-page-pieces chunks at left pieces)
    (let ((before (assembly-fragment-remaining-characters chunks at)))
      (implies (and (assembly-fragment-position-p chunks at) (natp left) (proof-fragments-p pieces))
               (and (proof-fragments-p output)
                    (equal (assembly-fragment-characters output)
                           (append (assembly-fragment-characters (revappend pieces nil))
                                   (assembly-page-prefix left before)))
                    (assembly-fragment-position-p rest next)
                    (equal (assembly-fragment-remaining-characters rest next)
                           (nthcdr left before))))))
  :hints (("Goal"
           :induct (boymoo-compiler::sha256-page-pieces chunks at left pieces)))
  :rule-classes nil)

(local (in-theory (disable boymoo-compiler::sha256-page-pieces
                           boymoo-compiler::sha256-range-words
                           boymoo-compiler::image-string)))

(local
 (defthm assembly-length-of-taken-page-characters
   (equal (len (take count chars)) (nfix count))))

(local
 (defthm assembly-page-prefix-length
   (equal (len (assembly-page-prefix count chars)) (min (nfix count) (len chars)))
   :hints (("Goal" :in-theory (enable assembly-page-prefix)))))

(local
 (defthm assembly-fragment-position-at-start
   (equal (assembly-fragment-position-p chunks 0) (proof-fragments-p chunks))))

(local
 (defthm assembly-page-characters-of-string-fragments
   (implies (proof-fragments-p chunks)
            (equal (coerce (boymoo-compiler::image-string chunks) 'list)
                   (assembly-fragment-characters chunks)))))

(local
 (defthm assembly-page-message-within-fragment
   (let ((before (assembly-fragment-remaining-characters chunks at)))
     (implies (and (consp chunks) (assembly-fragment-position-p chunks at)
                   (natp size) (<= (+ at size) (len (coerce (car chunks) 'list))))
              (equal (assembly-sha256-message (car chunks) at (+ at size) (+ at size))
                     (assembly-page-string size before))))))

(local
 (defthm assembly-sha256-message-of-copied-page
   (implies (and (stringp page) (natp size)
                 (equal (coerce page 'list) (assembly-page-prefix size before)))
            (and (assembly-sha256-message-range-p page 0 (len (coerce page 'list)) size)
                 (equal (assembly-sha256-message page 0 (len (coerce page 'list)) size)
                        (assembly-page-string size before))))
   :hints (("Goal" :in-theory (enable assembly-page-prefix)))
   :rule-classes nil))

(local (in-theory (disable assembly-page-string assembly-sha256-message)))

(local
 (defthm assembly-sha256-words-of-page-within-fragment
   (let ((message (assembly-page-string size
                                        (assembly-fragment-remaining-characters chunks at))))
     (implies (and (consp chunks) (assembly-fragment-position-p chunks at)
                   (natp size) (<= (+ at size) (len (coerce (car chunks) 'list))))
              (equal (boymoo-compiler::sha256-range-words (car chunks) at (+ at size) (+ at size))
                     (boymoo-compiler::sha256-range-words message 0 size size))))
   :hints (("Goal"
            :use ((:instance assembly-sha256-range-uses-explicit-message
                             (text (car chunks)) (start at)
                             (data-end (+ at size)) (message-end (+ at size))))))))

(local
 (defthm assembly-sha256-words-of-copied-page
   (let* ((page (boymoo-compiler::image-string pieces))
          (length (len (coerce page 'list))))
     (implies (and (proof-fragments-p pieces) (natp size)
                   (equal (assembly-fragment-characters pieces) (assembly-page-prefix size before)))
              (equal (boymoo-compiler::sha256-range-words page 0 length size)
                     (boymoo-compiler::sha256-range-words
                      (assembly-page-string size before) 0 size size))))
   :hints (("Goal"
            :use ((:instance assembly-sha256-message-of-copied-page
                             (page (boymoo-compiler::image-string pieces)))
                  (:instance assembly-sha256-range-uses-explicit-message
                             (text (boymoo-compiler::image-string pieces)) (start 0)
                             (data-end (len (coerce (boymoo-compiler::image-string pieces) 'list)))
                             (message-end size)))
            :in-theory (disable assembly-image-string-characters)))
   :rule-classes nil))

(defthm assembly-sha256-page-hashes-contiguous-bytes
  (mv-let (words rest next)
    (boymoo-compiler::sha256-page chunks at size)
    (let* ((before (assembly-fragment-remaining-characters chunks at))
           (message (assembly-page-string size before)))
      (implies (and (assembly-fragment-position-p chunks at) (natp size))
               (and (equal words (boymoo-compiler::sha256-range-words message 0 size size))
                    (assembly-fragment-position-p rest next)
                    (equal (assembly-fragment-remaining-characters rest next)
                           (nthcdr size before))))))
  :hints (("Goal"
           :use (assembly-sha256-words-of-page-within-fragment
                 (:instance assembly-sha256-page-pieces-exact (left size) (pieces nil))
                 (:instance assembly-sha256-words-of-copied-page
                            (pieces (mv-nth 0 (boymoo-compiler::sha256-page-pieces chunks at size nil)))
                            (before (assembly-fragment-remaining-characters chunks at))))
           :in-theory (disable assembly-image-string-characters
                               assembly-sha256-words-of-page-within-fragment)))
  :rule-classes nil)

(local
 (defun assembly-page-zero-count-induction (count padding)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       padding
     (assembly-page-zero-count-induction (1- count) (1- padding)))))

(local
 (defthm assembly-page-zero-prefix
   (implies (and (natp count) (natp padding) (<= count padding))
            (equal (take count (assembly-zero-characters padding))
                   (assembly-zero-characters count)))
   :hints (("Goal" :induct (assembly-page-zero-count-induction count padding)))))

(local
 (defthm assembly-page-zero-suffix
   (implies (and (natp count) (natp padding))
            (equal (nthcdr count (assembly-zero-characters padding))
                   (assembly-zero-characters (- padding count))))
   :hints (("Goal" :induct (assembly-page-zero-count-induction count padding)))))

(local
 (defthm assembly-length-of-page-zero-characters
   (equal (len (assembly-zero-characters padding)) (nfix padding))))

(local
 (defthm assembly-page-zeroes-are-characters
   (character-listp (assembly-zero-characters count))))

(local
 (defthm assembly-page-append-of-character-lists
   (implies (and (character-listp first) (character-listp rest))
            (character-listp (append first rest)))))

(defthm assembly-page-string-length
  (implies (and (character-listp chars) (natp count))
           (equal (length (assembly-page-string count chars)) count))
  :hints (("Goal" :in-theory (enable assembly-page-string assembly-page-prefix))))

(local
 (defthm assembly-append-page-zero-characters
   (equal (append (assembly-zero-characters first) (assembly-zero-characters rest))
          (assembly-zero-characters (+ (nfix first) (nfix rest))))))

(local
 (defthm assembly-nthcdr-after-page-end
   (implies (and (natp count) (true-listp chars) (<= (len chars) count))
            (equal (nthcdr count chars) nil))
   :hints (("Goal" :induct (nthcdr count chars)))))

(local
 (defthm assembly-no-page-zeroes-at-nonpositive-count
   (implies (zp count)
            (equal (assembly-zero-characters count) nil))))

(local (in-theory (disable assembly-zero-characters)))

(defthm assembly-page-suffix-with-explicit-zeroes
  (implies (and (natp count) (natp padding) (true-listp chars))
           (equal (nthcdr count (append chars (assembly-zero-characters padding)))
                  (append (nthcdr count chars)
                          (assembly-zero-characters
                           (nfix (- padding (nfix (- count (len chars)))))))))
  :hints (("Goal" :cases ((<= count (len chars)))))
  :rule-classes nil)

(defthm assembly-page-string-with-explicit-zeroes
  (implies (and (natp count) (natp padding) (true-listp chars))
           (equal (assembly-page-string count (append chars (assembly-zero-characters padding)))
                  (assembly-page-string count chars)))
  :hints (("Goal"
           :in-theory (enable assembly-page-string assembly-page-prefix)
           :cases ((< count (len chars)) (< count (+ (len chars) padding))
                   (equal padding (+ count (- (len chars)))))))
  :rule-classes nil)
