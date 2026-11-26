(in-package "BOYMOO-PROOFS")

(include-book "label-table")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash expt floor mod assembly-power-of-two assembly-cat)))

(defun assembly-character-number (chars)
  (if (atom chars)
      0
    (assembly-cat (* 8 (len (cdr chars)))
                  (assembly-character-number (cdr chars)) (char-code (car chars)))))

(local
 (defthm assembly-character-number-bounds
   (and (<= 0 (assembly-character-number chars))
        (< (assembly-character-number chars) (assembly-power-of-two (* 8 (len chars)))))
   :hints (("Goal" :induct (assembly-character-number chars))
           ("Subgoal *1/2"
            :use ((:instance assembly-cat-bounds
                             (n (* 8 (len (cdr chars)))) (m 8)
                             (low (assembly-character-number (cdr chars)))
                             (high (char-code (car chars)))))
            :in-theory (disable assembly-cat-bounds)))
   :rule-classes :linear))

(local
 (defthm assembly-positive-integer-at-least-one
   (implies (posp n) (<= 1 n))))

(local
 (defthm assembly-gap-between-integers
   (implies (and (integerp x) (integerp y) (< x y))
            (<= (+ 1 x) y))
   :hints (("Goal" :use ((:instance assembly-positive-integer-at-least-one (n (- y x))))
                   :in-theory (disable assembly-positive-integer-at-least-one)))
   :rule-classes nil))

(local
 (defthm assembly-cat-comparison
   (implies (and (natp width) (natp a) (natp b) (integerp x) (integerp y)
                 (< a (assembly-power-of-two width)) (< b (assembly-power-of-two width)))
            (equal (< (assembly-cat width a x) (assembly-cat width b y))
                   (or (< x y) (and (equal x y) (< a b)))))
   :hints (("Goal" :cases ((< x y) (< y x) (< a b))
                   :use (assembly-gap-between-integers
                         (:instance assembly-gap-between-integers (x y) (y x))
                         (:instance assembly-scale-order
                                    (a y) (b (+ 1 x)) (d (assembly-power-of-two width)))
                         (:instance assembly-scale-order
                                    (a x) (b (+ 1 y)) (d (assembly-power-of-two width))))
                   :in-theory (enable assembly-cat)
                   :nonlinearp t))))

(defun assembly-character-list-less (a b)
  (if (atom a)
      nil
    (let ((x (char-code (car a)))
          (y (char-code (car b))))
      (if (equal x y)
          (assembly-character-list-less (cdr a) (cdr b))
        (< x y)))))

(local
 (defthm assembly-equal-length-nonempty
   (implies (and (consp a) (equal (len a) (len b)))
            (and (consp b) (equal (len (cdr a)) (len (cdr b)))))
   :hints (("Goal" :expand ((len a) (len b))))
   :rule-classes nil))

(local
 (defthm assembly-character-number-is-integer
   (integerp (assembly-character-number chars))
   :rule-classes :type-prescription))

(local
 (defthm assembly-character-list-order
   (implies (equal (len a) (len b))
            (equal (assembly-character-list-less a b)
                   (< (assembly-character-number a) (assembly-character-number b))))
   :hints (("Goal" :induct (assembly-character-list-less a b)
                   :in-theory (disable assembly-cat))
           ("Subgoal *1/3" :use (assembly-equal-length-nonempty
                                (:instance assembly-cat-comparison
                                           (width (* 8 (len (cdr a))))
                                           (a (assembly-character-number (cdr a)))
                                           (b (assembly-character-number (cdr b)))
                                           (x (char-code (car a))) (y (char-code (car b)))))
                            :expand ((assembly-character-number a) (assembly-character-number b)))
           ("Subgoal *1/2" :use (assembly-equal-length-nonempty
                                (:instance assembly-cat-comparison
                                           (width (* 8 (len (cdr a))))
                                           (a (assembly-character-number (cdr a)))
                                           (b (assembly-character-number (cdr b)))
                                           (x (char-code (car a))) (y (char-code (car b)))))
                            :expand ((assembly-character-number a) (assembly-character-number b))))))

(local
 (defthm assembly-char-code-injective
   (implies (and (characterp a) (characterp b))
            (equal (equal (char-code a) (char-code b)) (equal a b)))
   :hints (("Goal"
            :use ((:instance acl2::code-char-char-code-is-identity (acl2::c a))
                  (:instance acl2::code-char-char-code-is-identity (acl2::c b)))
            :in-theory (disable acl2::code-char-char-code-is-identity)))))

(local
 (defthm assembly-character-list-order-is-total
   (implies (and (character-listp a) (character-listp b) (equal (len a) (len b)))
            (iff (or (assembly-character-list-less a b) (assembly-character-list-less b a))
                 (not (equal a b))))
   :hints (("Goal" :induct (assembly-character-list-less a b)
                   :in-theory (disable assembly-character-list-order)))))

(local
 (defthm assembly-character-number-is-injective
   (implies (and (character-listp a) (character-listp b) (equal (len a) (len b)))
            (equal (equal (assembly-character-number a) (assembly-character-number b))
                   (equal a b)))
   :hints (("Goal" :use (assembly-character-list-order-is-total)
                   :in-theory (disable assembly-character-list-order-is-total
                                       assembly-character-number)))))

(defun assembly-text-number (string)
  (let ((chars (coerce string 'list)))
    (+ (assembly-power-of-two (* 8 (len chars))) (assembly-character-number chars))))

(local
 (defthm assembly-text-number-bounds
   (implies (stringp string)
            (and (<= (assembly-power-of-two (* 8 (length string))) (assembly-text-number string))
                 (< (assembly-text-number string)
                    (* 2 (assembly-power-of-two (* 8 (length string)))))))
   :hints (("Goal" :in-theory (disable assembly-character-number)))
   :rule-classes :linear))

(local
 (defthm assembly-positive-width-power-at-least-two
   (implies (posp width) (<= 2 (assembly-power-of-two width)))
   :hints (("Goal" :use ((:instance assembly-power-of-two-of-sum (a 1) (b (1- width))))
                   :in-theory (disable assembly-power-of-two-of-sum)))
   :rule-classes :linear))

(local
 (defthm assembly-power-at-higher-width
   (implies (and (natp short) (natp long) (< short long))
            (<= (* 2 (assembly-power-of-two short)) (assembly-power-of-two long)))
   :hints (("Goal"
            :use ((:instance assembly-power-of-two-of-sum (a short) (b (- long short)))
                  (:instance assembly-positive-width-power-at-least-two (width (- long short))))
            :in-theory (disable assembly-power-of-two-of-sum
                                assembly-positive-width-power-at-least-two)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm assembly-shorter-text-has-smaller-number
   (implies (and (stringp a) (stringp b) (< (length a) (length b)))
            (< (assembly-text-number a) (assembly-text-number b)))
   :hints (("Goal"
            :use ((:instance assembly-power-at-higher-width
                             (short (* 8 (length a))) (long (* 8 (length b))))
                  (:instance assembly-text-number-bounds (string a))
                  (:instance assembly-text-number-bounds (string b)))
            :in-theory (disable assembly-text-number)))))

(local
 (defthm assembly-nthcdr-first
   (implies (natp index)
            (equal (car (nthcdr index chars)) (nth index chars)))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-next-nthcdr
   (implies (natp index)
            (equal (cdr (nthcdr index chars)) (nthcdr (+ 1 index) chars)))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-nthcdr-at-end
   (implies (true-listp chars) (equal (nthcdr (len chars) chars) nil))
   :hints (("Goal" :induct (len chars)))))

(local
 (defthm assembly-nthcdr-nonempty-before-end
   (implies (and (natp index) (< index (len chars)))
            (consp (nthcdr index chars)))
   :hints (("Goal" :induct (nthcdr index chars)))))

(local
 (defthm assembly-table-string-order
   (implies (and (stringp a) (stringp b)
                 (natp index) (natp left)
                 (equal (+ index left) (length a))
                 (equal (+ index left) (length b)))
            (equal (boymoo-compiler::table-string-less a b index left)
                   (assembly-character-list-less (nthcdr index (coerce a 'list))
                                                 (nthcdr index (coerce b 'list)))))
   :hints (("Goal" :induct (boymoo-compiler::table-string-less a b index left)
                   :in-theory (disable assembly-character-list-order
                                       assembly-character-list-order-is-total)))))

(local
 (defthm assembly-ordered-texts-of-same-length
   (implies (and (stringp a) (stringp b) (equal (length a) (length b)))
            (equal (boymoo-compiler::table-string-less a b 0 (length a))
                   (< (assembly-text-number a) (assembly-text-number b))))
   :hints (("Goal"
            :use ((:instance assembly-table-string-order (index 0) (left (length a))))
            :cases ((< (assembly-character-number (coerce a 'list))
                       (assembly-character-number (coerce b 'list))))
            :in-theory (disable assembly-table-string-order boymoo-compiler::table-string-less)))))

(defthm assembly-table-text-less-by-number
  (implies (and (stringp a) (stringp b))
           (equal (boymoo-compiler::table-text-less a b)
                  (< (assembly-text-number a) (assembly-text-number b))))
  :hints (("Goal" :cases ((< (length a) (length b)) (< (length b) (length a)))
                  :use (assembly-shorter-text-has-smaller-number
                        (:instance assembly-shorter-text-has-smaller-number (a b) (b a))
                        assembly-ordered-texts-of-same-length)
                  :in-theory (disable assembly-shorter-text-has-smaller-number
                                      assembly-table-string-order assembly-ordered-texts-of-same-length
                                      boymoo-compiler::table-string-less assembly-text-number))))

(defthmd assembly-text-number-injective
  (implies (and (stringp a) (stringp b))
           (equal (equal (assembly-text-number a) (assembly-text-number b)) (equal a b)))
  :hints (("Goal"
           :cases ((< (length a) (length b)) (< (length b) (length a)))
           :use (assembly-shorter-text-has-smaller-number
                 (:instance assembly-shorter-text-has-smaller-number (a b) (b a))
                 (:instance acl2::coerce-inverse-2 (acl2::x a))
                 (:instance acl2::coerce-inverse-2 (acl2::x b))
                 (:instance assembly-character-number-is-injective
                            (a (coerce a 'list)) (b (coerce b 'list))))
           :in-theory (disable assembly-shorter-text-has-smaller-number
                               assembly-character-number-is-injective
                               assembly-character-number acl2::coerce-inverse-2))))

(defun assembly-compiler-label-p (key)
  (or (stringp key)
      (and (equal key (list (car key) (cadr key)))
           (or (and (eq (car key) :fn) (stringp (cadr key)))
               (and (eq (car key) :local) (natp (cadr key)))))))

(defun assembly-label-family (key)
  (cond ((stringp key) 0)
        ((eq (car key) :fn) 1)
        (t 2)))

(defun assembly-label-value (key)
  (cond ((stringp key) (assembly-text-number key))
        ((eq (car key) :fn) (assembly-text-number (cadr key)))
        (t (nfix (cadr key)))))

(local
 (defthm assembly-text-number-is-natural
   (natp (assembly-text-number string))
   :hints (("Goal" :use ((:instance assembly-character-number-bounds (chars (coerce string 'list))))))
   :rule-classes :type-prescription))

(local
 (defthm assembly-label-value-is-natural
   (natp (assembly-label-value key))
   :hints (("Goal" :in-theory (disable assembly-text-number)))
   :rule-classes :type-prescription))

(defthm assembly-compiler-label-order
  (implies (and (assembly-compiler-label-p a) (assembly-compiler-label-p b))
           (equal (boymoo-compiler::table-key-less a b)
                  (or (< (assembly-label-family a) (assembly-label-family b))
                      (and (equal (assembly-label-family a) (assembly-label-family b))
                           (< (assembly-label-value a) (assembly-label-value b))))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::table-text-less assembly-text-number))))

(local
 (defthm assembly-label-family-and-value-identify-key
   (implies (and (assembly-compiler-label-p a) (assembly-compiler-label-p b)
                 (equal (assembly-label-family a) (assembly-label-family b)))
            (equal (equal (assembly-label-value a) (assembly-label-value b)) (equal a b)))
   :hints (("Goal" :in-theory (e/d (assembly-text-number-injective)
                                    (assembly-text-number))))))

(defun assembly-compiler-label-list-p (keys)
  (if (atom keys)
      (null keys)
    (and (assembly-compiler-label-p (car keys))
         (assembly-compiler-label-list-p (cdr keys)))))

(defun assembly-label-stride (keys)
  (if (atom keys)
      1
    (+ (assembly-label-value (car keys)) (assembly-label-stride (cdr keys)))))

(defun assembly-label-rank-value (key stride)
  (+ (* stride (assembly-label-family key)) (assembly-label-value key)))

(local
 (defthm assembly-label-ranks-are-rational
   (implies (rationalp stride) (rationalp (assembly-label-rank-value key stride)))
   :hints (("Goal" :in-theory (disable assembly-label-value)))
   :rule-classes (:rewrite :type-prescription)))

(defun assembly-label-rank-entries (keys stride)
  (if (atom keys)
      nil
    (acons (car keys) (assembly-label-rank-value (car keys) stride)
           (assembly-label-rank-entries (cdr keys) stride))))

(defun assembly-compiler-label-ranks (keys)
  (assembly-label-rank-entries keys (assembly-label-stride keys)))

(local
 (defun assembly-label-list-fits-p (keys stride)
   (if (atom keys)
       t
     (and (< (assembly-label-value (car keys)) stride)
          (assembly-label-list-fits-p (cdr keys) stride)))))

(local
 (defthm assembly-label-stride-is-positive
   (posp (assembly-label-stride keys))
   :hints (("Goal" :in-theory (disable assembly-label-value)))
   :rule-classes :type-prescription))

(local
 (defthm assembly-label-list-fits-larger-stride
   (implies (and (rationalp smaller) (rationalp larger) (<= smaller larger)
                 (assembly-label-list-fits-p keys smaller))
            (assembly-label-list-fits-p keys larger))
   :hints (("Goal" :induct (assembly-label-list-fits-p keys smaller)
                   :in-theory (disable assembly-label-value)))
   :rule-classes nil))

(local
 (defthm assembly-label-list-fits-own-stride
   (assembly-label-list-fits-p keys (assembly-label-stride keys))
   :hints (("Goal" :induct (assembly-label-stride keys)
                   :in-theory (disable assembly-label-value))
           ("Subgoal *1/2"
            :use ((:instance assembly-label-list-fits-larger-stride
                             (keys (cdr keys))
                             (smaller (assembly-label-stride (cdr keys)))
                             (larger (assembly-label-stride keys))))))))

(local
 (defthm assembly-generated-rank-compares-labels
   (implies (and (assembly-compiler-label-p a) (assembly-compiler-label-p b)
                 (posp stride)
                 (< (assembly-label-value a) stride)
                 (< (assembly-label-value b) stride))
            (and (equal (< (assembly-label-rank-value a stride)
                           (assembly-label-rank-value b stride))
                        (boymoo-compiler::table-key-less a b))
                 (equal (equal (assembly-label-rank-value a stride)
                               (assembly-label-rank-value b stride))
                        (equal a b))))
   :hints (("Goal"
            :use (assembly-compiler-label-order assembly-label-family-and-value-identify-key)
            :cases ((< (assembly-label-value a) (assembly-label-value b)))
            :in-theory (disable boymoo-compiler::table-key-less
                                assembly-compiler-label-order
                                assembly-label-family-and-value-identify-key
                                assembly-label-value)))))

(local
 (defthm assembly-generated-rank-agrees-with-list
   (implies (and (assembly-compiler-label-p key)
                 (assembly-compiler-label-list-p keys)
                 (posp stride) (< (assembly-label-value key) stride)
                 (assembly-label-list-fits-p keys stride)
                 (not (member-equal key keys)))
            (assembly-ranked-against-p
             (cons key (assembly-label-rank-value key stride))
             (assembly-label-rank-entries keys stride)))
   :hints (("Goal" :induct (assembly-label-rank-entries keys stride)
                   :in-theory (disable assembly-compiler-label-p assembly-label-rank-value
                                       boymoo-compiler::table-key-less assembly-label-value))
           ("Subgoal *1/2"
            :use ((:instance assembly-generated-rank-compares-labels (a key) (b (car keys)))
                  (:instance assembly-generated-rank-compares-labels (a (car keys)) (b key)))))))

(local
 (defthm assembly-compiler-label-never-precedes-itself
   (implies (assembly-compiler-label-p key)
            (not (boymoo-compiler::table-key-less key key)))
   :hints (("Goal" :use ((:instance assembly-compiler-label-order (a key) (b key)))
                   :in-theory (disable assembly-compiler-label-order
                                       boymoo-compiler::table-key-less)))))

(local
 (defthm assembly-generated-rank-list-p
   (implies (and (assembly-compiler-label-list-p keys)
                 (posp stride) (assembly-label-list-fits-p keys stride)
                 (no-duplicatesp-equal keys))
            (assembly-ranking-p (assembly-label-rank-entries keys stride)))
   :hints (("Goal" :induct (assembly-label-rank-entries keys stride)
                   :in-theory (disable assembly-compiler-label-p assembly-label-rank-value
                                       boymoo-compiler::table-key-less assembly-label-value)))))

(defthm assembly-compiler-label-ranks-pass-check
  (implies (and (assembly-compiler-label-list-p keys) (no-duplicatesp-equal keys))
           (assembly-ranking-p (assembly-compiler-label-ranks keys)))
  :hints (("Goal" :use ((:instance assembly-generated-rank-list-p
                                   (stride (assembly-label-stride keys))))
                  :in-theory (disable assembly-compiler-label-list-p))))

(local
 (defthm assembly-ranks-cover-member
   (implies (member-equal key keys)
            (assoc-equal key (assembly-label-rank-entries keys stride)))))

(local
 (defthm assembly-ranks-cover-entries
   (implies (subsetp-equal (assembly-keys entries) keys)
            (assembly-ranked-entries-p entries (assembly-label-rank-entries keys stride)))
   :hints (("Goal" :induct (len entries)))))

(defthmd assembly-subset-survives-cons
  (implies (subsetp-equal a b)
           (subsetp-equal a (cons key b)))
  :hints (("Goal" :induct (subsetp-equal a b))))

(defthmd assembly-subset-of-self
  (subsetp-equal keys keys)
  :hints (("Goal" :induct (len keys)
                  :in-theory (enable assembly-subset-survives-cons))))

(local
 (defthm assembly-all-keys-are-covered-by-their-ranks
   (assembly-ranked-entries-p entries (assembly-compiler-label-ranks (assembly-keys entries)))
   :hints (("Goal" :use ((:instance assembly-ranks-cover-entries
                                    (keys (assembly-keys entries))
                                    (stride (assembly-label-stride (assembly-keys entries)))))
                   :in-theory (e/d (assembly-subset-of-self)
                                   (assembly-ranks-cover-entries))))))

(local
 (defthm assembly-no-labels-in-the-empty-table
   (assembly-labels-unused-p entries nil)
   :hints (("Goal" :in-theory (disable boymoo-compiler::label-hash)))))

(defthm assembly-layout-input-for-compiler-labels
  (let ((keys (assembly-keys (assembly-labels items 0))))
    (implies (and (assembly-layout-sizes-p items)
                  (assembly-compiler-label-list-p keys)
                  (no-duplicatesp-equal keys))
             (assembly-layout-input-p items 0 nil (assembly-compiler-label-ranks keys))))
  :hints (("Goal"
           :use ((:instance assembly-compiler-label-ranks-pass-check
                            (keys (assembly-keys (assembly-labels items 0)))))
           :in-theory (disable assembly-compiler-label-ranks-pass-check
                                assembly-compiler-label-ranks assembly-labels
                                assembly-compiler-label-list-p))))
