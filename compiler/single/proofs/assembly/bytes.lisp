(in-package "BOYMOO-PROOFS")

(include-book "label-table")
(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-fragment-characters (fragments)
  (if (atom fragments)
      nil
    (append (coerce (car fragments) 'list)
            (assembly-fragment-characters (cdr fragments)))))

(defun assembly-byte-character (word index)
  (code-char (boymoo-compiler::low-bits (ash word (* -8 index)) 8)))

(defun assembly-word-characters (word count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (append (assembly-word-characters word (1- count))
            (list (assembly-byte-character word (1- count))))))

(defun assembly-zero-characters (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (code-char 0) (assembly-zero-characters (1- count)))))

(defun assembly-adr-far-words (rd target pc)
  (list
   (boymoo-compiler::a64-adr #x90000000 rd (- (ash target -12) (ash pc -12)))
   (if (equal rd 31)
       #xaa1f03ff
     (boymoo-compiler::a64-uimm #x91000000 rd rd
                               (boymoo-compiler::low-bits target 12) 0))))

(defun assembly-item-words (item pc labels)
  (case (car item)
    ((:label :image :bytes :quad) nil)
    (:adr-far
     (assembly-adr-far-words (cadr item)
                            (boymoo-compiler::a64-offset (caddr item) labels) pc))
    ((:adds :subs :cmp :cmn)
     (if (boymoo-compiler::a64-zero-source-p item)
         (mv-let (first second)
           (boymoo-compiler::a64-zero-source-words item)
           (list first second))
       (list (boymoo-compiler::a64-word item pc labels))))
    (otherwise (list (boymoo-compiler::a64-word item pc labels)))))

(defun assembly-words-characters (words)
  (if (atom words)
      nil
    (append (assembly-word-characters (car words) 4)
            (assembly-words-characters (cdr words)))))

(defun assembly-item-characters (item pc labels)
  (case (car item)
    (:label nil)
    (:image (assembly-fragment-characters (caddr item)))
    (:bytes
     (let ((string (cadr item)))
       (append (coerce string 'list)
               (assembly-zero-characters
                (- (boymoo-compiler::a64-image-item-size item)
                   (length string))))))
    (:quad (assembly-word-characters (cadr item) 8))
    (otherwise (assembly-words-characters (assembly-item-words item pc labels)))))

(defun assembly-items-characters (items pc labels)
  (if (atom items)
      nil
    (append (assembly-item-characters (car items) pc labels)
            (assembly-items-characters
             (cdr items)
             (+ pc (boymoo-compiler::a64-image-item-size (car items)))
             labels))))

(defun assembly-reversed-characters (items end labels)
  (if (atom items)
      nil
    (let ((pc (- end (boymoo-compiler::a64-image-item-size (car items)))))
      (append (assembly-reversed-characters (cdr items) pc labels)
              (assembly-item-characters (car items) pc labels)))))

(defun assembly-data-p (item)
  (case (car item)
    (:image (proof-image-p (cons (cadr item) (caddr item))))
    (:bytes (stringp (cadr item)))
    (:quad (and (integerp (cadr item))
                (<= (- (expt 2 63)) (cadr item))
                (< (cadr item) (expt 2 64))))
    (otherwise t)))

(defun assembly-data-list-p (items)
  (if (atom items)
      t
    (and (assembly-data-p (car items))
         (assembly-data-list-p (cdr items)))))

(local (in-theory (disable boymoo-compiler::a64-image-item-size
                           boymoo-compiler::a64-word
                           boymoo-compiler::a64-zero-source-words
                           boymoo-compiler::a64-zero-source-p
                           boymoo-compiler::a64-adr
                           boymoo-compiler::a64-uimm
                           boymoo-compiler::a64-offset
                           boymoo-compiler::low-bits
                           ash)))

(local
 (defthm assembly-prepend-word-characters
   (equal (boymoo-compiler::prepend-word word count rest)
          (append (assembly-word-characters word count) rest))
   :hints (("Goal" :induct (boymoo-compiler::prepend-word word count rest)))))

(local
 (defthm assembly-word-characters-are-characters
   (character-listp (assembly-word-characters word count))
   :hints (("Goal" :induct (assembly-word-characters word count)))))

(local
 (defthm assembly-words-characters-are-characters
   (character-listp (assembly-words-characters words))))

(local
 (defthm assembly-zero-characters-are-characters
   (character-listp (assembly-zero-characters count))))

(local
 (defthm assembly-zero-characters-commute
   (equal (append (assembly-zero-characters count) (cons (code-char 0) rest))
          (cons (code-char 0) (append (assembly-zero-characters count) rest)))))

(local
 (defthm assembly-image-zeroes-characters
   (equal (boymoo-compiler::image-zeroes count rest)
          (coerce (append (assembly-zero-characters count) rest) 'string))
   :hints (("Goal" :induct (boymoo-compiler::image-zeroes count rest)))))

(local
 (defthm assembly-flatten-image-flush
   (implies (character-listp chars)
            (equal (assembly-fragment-characters
                    (boymoo-compiler::image-flush chars chunks))
                   (append chars (assembly-fragment-characters chunks))))))

(local
 (defthm assembly-flatten-image-padding
   (equal (assembly-fragment-characters (boymoo-compiler::image-padding count chunks))
          (append (assembly-zero-characters count)
                  (assembly-fragment-characters chunks)))))

(local
 (defthm assembly-reverse-onto-is-revappend
   (equal (boymoo-compiler::reverse-onto xs rest)
          (revappend xs rest))))

(local
 (defthm assembly-revappend-of-revappend
   (equal (revappend (revappend xs ys) rest)
          (revappend ys (append xs rest)))
   :hints (("Goal" :induct (revappend xs ys)))))

(local
 (defthm assembly-revappend-with-append
   (equal (revappend xs (append ys rest))
          (append (revappend xs ys) rest))
   :hints (("Goal" :induct (revappend xs ys)))))

(local
 (defthm assembly-fragment-characters-of-append
   (equal (assembly-fragment-characters (append xs ys))
          (append (assembly-fragment-characters xs)
                  (assembly-fragment-characters ys)))))

(local
 (defthm assembly-revappend-one
   (equal (revappend xs (list x))
          (append (revappend xs nil) (list x)))
   :hints (("Goal" :use ((:instance assembly-revappend-with-append
                                    (ys nil) (rest (list x))))
                   :in-theory (disable assembly-revappend-with-append)))))

(local
 (defthm assembly-flatten-image-onto
   (equal (assembly-fragment-characters (boymoo-compiler::image-onto first rest))
          (append (assembly-fragment-characters first)
                  (assembly-fragment-characters rest)))))

(local
 (defthm assembly-take-next
   (implies (natp n)
            (equal (append (take n xs) (list (nth n xs)))
                   (take (+ 1 n) xs)))
   :hints (("Goal" :induct (take n xs)))))

(local
 (defthm assembly-take-all
   (implies (true-listp xs)
            (equal (take (len xs) xs) xs))))

(local
 (defthm assembly-image-prepend-chars
   (implies (and (stringp string) (natp i))
            (equal (boymoo-compiler::image-prepend-chars string i chars)
                   (append (take i (coerce string 'list)) chars)))
   :hints (("Goal" :induct (boymoo-compiler::image-prepend-chars string i chars))
           ("Subgoal *1/2"
            :use ((:instance assembly-take-next (n (1- i)) (xs (coerce string 'list))))
            :in-theory (disable assembly-take-next)))))

(local
 (defthm assembly-image-characters
   (implies (proof-fragments-p reversed)
            (equal (boymoo-compiler::image-characters reversed chars)
                   (append (assembly-fragment-characters (revappend reversed nil))
                           chars)))
   :hints (("Goal" :induct (boymoo-compiler::image-characters reversed chars))
           ("Subgoal *1/1" :expand ((revappend reversed nil))))))

(local
 (defthm assembly-fragments-p-of-revappend
   (implies (true-listp xs)
            (equal (proof-fragments-p (revappend xs ys))
                   (and (proof-fragments-p xs) (proof-fragments-p ys))))
   :hints (("Goal" :induct (revappend xs ys)))))

(local
 (defthm assembly-fragments-p-true-list
   (implies (proof-fragments-p chunks)
            (true-listp chunks))
   :rule-classes :forward-chaining))

(defthm assembly-image-string-characters
  (implies (proof-fragments-p chunks)
           (equal (boymoo-compiler::image-string chunks)
                  (coerce (assembly-fragment-characters chunks) 'string))))

(defthm assembly-fragment-characters-count
  (implies (proof-fragments-p chunks)
           (equal (len (assembly-fragment-characters chunks))
                  (proof-fragments-size chunks))))

(defthm assembly-fragment-characters-are-characters
  (implies (proof-fragments-p chunks)
           (character-listp (assembly-fragment-characters chunks))))

(local
 (defthm assembly-fragments-p-of-append
   (implies (true-listp xs)
            (equal (proof-fragments-p (append xs ys))
                   (and (proof-fragments-p xs) (proof-fragments-p ys))))))

(local
 (defthm assembly-fragments-p-of-image-onto
   (implies (and (proof-fragments-p first) (proof-fragments-p rest))
            (proof-fragments-p (boymoo-compiler::image-onto first rest)))))

(local
 (defthm assembly-character-list-of-append
   (implies (and (character-listp xs) (character-listp ys))
            (character-listp (append xs ys)))))

(local
 (defthm assembly-quad-in-range
   (implies (and (integerp value) (<= (- (expt 2 63)) value) (< value (expt 2 64)))
            (or (and (<= 0 value)
                     (equal (ash value -64) 0))
                (equal (ash value -63) -1)))
   :hints (("Goal" :cases ((< value 0))
                   :use ((:instance assembly-floor-unique
                                    (x value) (q -1) (d (expt 2 63))))))))

(local
 (defthm assembly-emit-characters
   (implies (and (not (member-eq (car item) '(:label :bytes :image)))
                 (assembly-data-p item))
            (equal (boymoo-compiler::a64-emit item pc labels chars)
                   (append (assembly-item-characters item pc labels) chars)))
   :hints (("Goal" :use ((:instance assembly-quad-in-range (value (cadr item))))
                   :in-theory (disable assembly-quad-in-range)))))

(local
 (defthm assembly-emitted-characters-list
   (implies (not (member-eq (car item) '(:label :bytes :image)))
            (character-listp (assembly-item-characters item pc labels)))))

(defun assembly-no-labels-p (items)
  (if (atom items)
      t
    (and (not (eq (caar items) :label))
         (assembly-no-labels-p (cdr items)))))

(local
 (defthm assembly-emit-character-list
   (implies (and (character-listp chars)
                 (not (member-eq (car item) '(:label :bytes :image)))
                 (assembly-data-p item))
            (character-listp (boymoo-compiler::a64-emit item pc labels chars)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::a64-emit assembly-data-p
                                      assembly-item-characters)))))

(local
 (defthm assembly-len-zero-of-true-list
   (implies (true-listp xs)
            (equal (equal (len xs) 0) (equal xs nil)))
   :hints (("Goal" :expand ((len xs))))))

(local
 (defthm assembly-empty-string-characters
   (implies (and (stringp text) (zp (length text)))
            (equal (coerce text 'list) nil))))

(defthm assembly-items-characters-of-append
  (implies (acl2-numberp pc)
           (equal (assembly-items-characters (append first rest) pc labels)
                  (append (assembly-items-characters first pc labels)
                          (assembly-items-characters rest (+ pc (assembly-size first)) labels))))
  :hints (("Goal" :induct (assembly-items-characters first pc labels)
                  :in-theory (disable assembly-item-characters))))

(defthm assembly-items-characters-without-labels
  (implies (acl2-numberp pc)
           (equal (assembly-items-characters (assembly-code-items items) pc labels)
                  (assembly-items-characters items pc labels)))
  :hints (("Goal" :induct (assembly-items-characters items pc labels))))

(defthm assembly-reversed-characters-forward
  (implies (acl2-numberp end)
           (equal (assembly-reversed-characters items end labels)
                  (assembly-items-characters
                   (revappend items nil) (- end (assembly-size items)) labels)))
  :hints (("Goal" :induct (assembly-reversed-characters items end labels)
                  :in-theory (disable assembly-item-characters))))

(local
 (defthm assembly-fragments-p-of-image-flush
   (implies (and (character-listp chars) (proof-fragments-p chunks))
            (proof-fragments-p (boymoo-compiler::image-flush chars chunks)))))

(local
 (defthm assembly-image-zeroes-is-a-string
   (stringp (boymoo-compiler::image-zeroes count chars))))

(local
 (defthm assembly-fragments-p-of-image-padding
   (implies (proof-fragments-p chunks)
            (proof-fragments-p (boymoo-compiler::image-padding count chunks)))))

(local
 (defthm assembly-fragment-list-cons
   (equal (proof-fragments-p (cons string chunks))
          (and (stringp string) (proof-fragments-p chunks)))))

(local
 (defthm assembly-data-image-fragments
   (implies (and (eq (car item) :image) (assembly-data-p item))
            (proof-fragments-p (caddr item)))))

(local
 (defthm assembly-data-byte-string
   (implies (and (eq (car item) :bytes) (assembly-data-p item))
            (stringp (cadr item)))))

(defthm assembly-write-chunks-characters
  (implies (and (character-listp chars)
                (proof-fragments-p chunks)
                (assembly-no-labels-p reversed)
                (assembly-data-list-p reversed))
           (let ((output (boymoo-compiler::a64-write-chunks
                          reversed end labels chars buffered chunks)))
             (and (proof-fragments-p output)
                  (equal (assembly-fragment-characters output)
                         (append (assembly-reversed-characters reversed end labels)
                                 (append chars (assembly-fragment-characters chunks)))))))
  :hints (("Goal"
           :induct (boymoo-compiler::a64-write-chunks
                    reversed end labels chars buffered chunks)
           :in-theory (disable boymoo-compiler::a64-emit boymoo-compiler::image-flush
                               boymoo-compiler::image-padding boymoo-compiler::image-onto
                               assembly-item-words assembly-data-p
                               assembly-word-characters assembly-words-characters
                               assembly-reversed-characters-forward
                               proof-fragments-p))))

(local
 (defthm assembly-data-list-p-of-code-items
   (implies (assembly-data-list-p items)
            (assembly-data-list-p (assembly-code-items items)))))

(local
 (defthm assembly-data-list-p-of-revappend
   (equal (assembly-data-list-p (revappend items rest))
          (and (assembly-data-list-p items) (assembly-data-list-p rest)))
   :hints (("Goal" :induct (revappend items rest)))))

(local
 (defthm assembly-no-labels-in-code-items
   (assembly-no-labels-p (assembly-code-items items))))

(local
 (defthm assembly-no-labels-p-of-revappend
   (equal (assembly-no-labels-p (revappend items rest))
          (and (assembly-no-labels-p items) (assembly-no-labels-p rest)))
   :hints (("Goal" :induct (revappend items rest)))))

(defthm assembly-flattened-image
  (implies (and (assembly-layout-input-p items 0 nil ranks)
                (assembly-data-list-p items)
                (assoc-equal entry (assembly-labels items 0)))
           (mv-let (image offset)
             (boymoo-compiler::a64-assemble-image items entry)
             (and (equal (car image) (assembly-size items))
                  (proof-fragments-p (cdr image))
                  (equal (assembly-fragment-characters (cdr image))
                         (assembly-items-characters
                          items 0 (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil))))
                  (equal offset (cdr (assoc-equal entry (assembly-labels items 0)))))))
  :hints (("Goal"
           :use ((:instance assembly-layout-end-and-order (pc 0) (table nil) (rest nil))
                 assembly-layout-entry-offset)
           :in-theory (disable boymoo-compiler::a64-layout
                               assembly-layout-end-and-order assembly-layout-entry-offset
                               assembly-layout-input-p))))

(defthm assembly-byte-padding-bounds
  (implies (and (eq (car item) :bytes) (stringp (cadr item)))
           (let* ((count (length (cadr item)))
                  (size (boymoo-compiler::a64-image-item-size item)))
             (and (<= count size) (<= size (+ count 3)))))
  :hints (("Goal"
           :use ((:instance assembly-floor-bounds
                            (x (+ 3 (length (cadr item)))) (d 4)))
           :in-theory (enable boymoo-compiler::a64-image-item-size assembly-high)))
  :rule-classes (:rewrite :linear))

(local
 (defthm assembly-len-of-append
   (equal (len (append xs ys)) (+ (len xs) (len ys)))
   :hints (("Goal" :induct (append xs ys)))))

(defthm assembly-word-characters-count
  (equal (len (assembly-word-characters word count)) (nfix count))
  :hints (("Goal" :in-theory (disable assembly-byte-character))))

(local
 (defthm assembly-zero-characters-count
   (equal (len (assembly-zero-characters count)) (nfix count))))

(defthm assembly-words-characters-count
  (equal (len (assembly-words-characters words)) (* 4 (len words))))

(defthm assembly-item-character-count
  (implies (assembly-data-p item)
           (equal (len (assembly-item-characters item pc labels))
                  (boymoo-compiler::a64-image-item-size item)))
  :hints (("Goal"
           :use ((:instance assembly-byte-padding-bounds))
           :in-theory (e/d (boymoo-compiler::a64-image-item-size)
                           (assembly-byte-padding-bounds assembly-words-characters
                            assembly-word-characters assembly-zero-characters)))))

(defthm assembly-items-character-count
  (implies (assembly-data-list-p items)
           (equal (len (assembly-items-characters items pc labels))
                  (assembly-size items)))
  :hints (("Goal" :induct (assembly-items-characters items pc labels)
                  :in-theory (disable assembly-item-characters assembly-data-p))))

(defthm assembly-image-well-formed
  (implies (and (assembly-layout-input-p items 0 nil ranks)
                (assembly-data-list-p items)
                (assoc-equal entry (assembly-labels items 0)))
           (proof-image-p (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))))
  :hints (("Goal"
           :use (assembly-flattened-image
                 (:instance assembly-fragment-characters-count
                            (chunks (cdr (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry)))))
                 (:instance assembly-items-character-count
                            (pc 0) (labels (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))))
           :in-theory (disable boymoo-compiler::a64-layout boymoo-compiler::a64-write
                               boymoo-compiler::a64-offset assembly-items-characters
                               assembly-layout-input-p assembly-flattened-image
                               assembly-fragment-characters-count assembly-items-character-count))))
