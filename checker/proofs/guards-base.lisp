(in-package "BOYMOO")

(include-book "base")

(defthm cg-pair-of-is-cons
  (equal (consp (pair-of k al))
         (if (pair-of k al) t nil)))

(defthm cg-character-listp-rev-onto
  (implies (and (character-listp x) (character-listp acc))
           (character-listp (rev-onto x acc))))

(defthm cg-character-listp-app
  (implies (and (character-listp x) (character-listp y))
           (character-listp (app x y))))

(defthm cg-character-listp-rev
  (implies (character-listp x)
           (character-listp (rev x))))

(local
 (defthm cg-trie-child-of-drop
   (implies (not (equal c d))
            (equal (trie-child c (trie-drop d kids))
                   (trie-child c kids)))
   :hints (("Goal" :induct (trie-drop d kids)))))

(local
 (defun cg-trie-update-induction (query key node)
   (declare (xargs :guard t :measure (acl2-count key)))
   (if (and (consp query) (consp key) (equal (car query) (car key)))
       (cg-trie-update-induction (cdr query) (cdr key)
                                 (if (consp node)
                                     (trie-child (car key) (cdr node))
                                   nil))
     (list query key node))))

(defthm cg-trie-get-of-put
  (implies (and (true-listp query) (true-listp key))
           (equal (trie-get query (trie-put key value node))
                  (if (equal query key) value (trie-get query node))))
  :hints (("Goal" :induct (cg-trie-update-induction query key node)
           :in-theory (disable trie-drop))))

(local
 (defthm cg-digit-count-range
   (implies (and (natp d) (<= d 9))
            (let ((value (digit-count n p d)))
              (and (integerp value)
                   (<= 0 value)
                   (<= value 9))))
   :rule-classes
   ((:rewrite)
    (:linear :corollary
     (implies (and (natp d) (<= d 9)) (<= 0 (digit-count n p d))))
    (:linear :corollary
     (implies (and (natp d) (<= d 9)) (<= (digit-count n p d) 9))))))

; A nonempty run begins with an integer at least as large as its first
; power. Capping the run at this head produces the same list.
(local
 (defthm cg-tens-up-to-head
   (implies (and (integerp n) (posp p) (<= p n))
            (let ((result (tens-up-to n p acc)))
              (and (consp result)
                   (integerp (car result))
                   (<= p (car result)))))
   :rule-classes ((:rewrite)
                  (:linear :corollary
                   (implies (and (integerp n) (posp p) (<= p n))
                            (<= p (car (tens-up-to n p acc))))))))

(local
 (defthm cg-tens-up-to-stop
   (implies (< n p)
            (equal (tens-up-to n p acc) acc))
   :hints (("Goal" :expand ((tens-up-to n p acc))))))

(local
 (defthm cg-tens-up-to-single
   (implies (posp p)
            (equal (tens-up-to p p acc) (cons p acc)))
   :hints (("Goal" :expand ((tens-up-to p p acc))))))

(local
 (defthm cg-tens-up-to-head-cap
   (implies (and (integerp n) (posp p) (<= p n))
            (equal (tens-up-to (car (tens-up-to n p acc)) p acc)
                   (tens-up-to n p acc)))
   :hints (("Goal" :induct (tens-up-to n p acc))
           ("Subgoal *1/1" :cases ((< n (* 10 p)))))))

; Removing the head either leaves the supplied accumulator or leaves
; the run capped at the next power.
(local
 (defthm cg-tens-up-to-tail-cap
   (implies (and (integerp n) (posp p) (<= p n))
            (let ((tail (cdr (tens-up-to n p acc))))
              (or (equal tail acc)
                  (and (consp tail)
                       (integerp (car tail))
                       (<= p (car tail))
                       (equal (tens-up-to (car tail) p acc) tail)))))
   :rule-classes nil
   :hints (("Goal" :induct (tens-up-to n p acc))
           ("Subgoal *1/1" :cases ((< n (* 10 p)))))))

(local
 (defthm cg-tens-up-to-empty-or-positive
   (implies (and (not (consp acc)) (consp (tens-up-to n p acc)))
            (and (integerp n) (integerp p) (< 0 p) (<= p n)))
   :hints (("Goal" :expand ((tens-up-to n p acc))))))

(verify-guards decimal-digits
  :hints (("Goal"
           :use ((:instance cg-tens-up-to-tail-cap
                            (n (car ps)) (p 1) (acc nil)))
           :in-theory (disable tens-up-to digit-count))))

(verify-guards decimal
  :hints (("Goal" :in-theory (disable decimal-digits tens-up-to))))

(defthm cg-character-listp-decimal-digits
  (character-listp (decimal-digits n ps))
  :hints (("Goal" :induct (decimal-digits n ps))))

(defthm cg-character-listp-decimal
  (character-listp (decimal n)))
