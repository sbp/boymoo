(in-package "BOYMOO-PROOFS")

(include-book "source")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::table-string-less boymoo-compiler::table-text-less
                    boymoo-compiler::table-key-less char length nthcdr nth))

(defthm generated-string-key-order
  (implies (and (stringp first) (stringp second))
           (equal (boymoo-compiler::table-key-less first second)
                  (boymoo-compiler::table-text-less first second)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::table-key-less boymoo-compiler::table-key-kind))))

(local
 (defun generated-string-suffix-induction (index remaining)
   (declare (xargs :measure (nfix remaining)))
   (if (zp remaining)
       index
     (generated-string-suffix-induction (1+ index) (1- remaining)))))

(local
 (defthm generated-string-slice-less-transitive
   (implies (and (boymoo-compiler::table-string-less first second index remaining)
                 (boymoo-compiler::table-string-less second third index remaining))
            (boymoo-compiler::table-string-less first third index remaining))
   :hints (("Goal" :induct (generated-string-suffix-induction index remaining))
           ("Subgoal *1/2"
            :expand ((boymoo-compiler::table-string-less first second index remaining)
                     (boymoo-compiler::table-string-less second third index remaining)
                     (boymoo-compiler::table-string-less first third index remaining)))
           ("Subgoal *1/1" :in-theory (enable boymoo-compiler::table-string-less)))
   :rule-classes nil))

(defthm generated-scope-string-order-transitive
  (implies (and (boymoo-compiler::table-text-less first second)
                (boymoo-compiler::table-text-less second third))
           (boymoo-compiler::table-text-less first third))
  :hints (("Goal"
           :use (:instance generated-string-slice-less-transitive (index 0) (remaining (length first)))
           :in-theory (enable boymoo-compiler::table-text-less)))
  :rule-classes nil)

(local
 (defthm generated-string-slice-less-irreflexive
   (not (boymoo-compiler::table-string-less text text index remaining))
   :hints (("Goal" :induct (generated-string-suffix-induction index remaining)
                   :in-theory (enable boymoo-compiler::table-string-less)))))

(defthm generated-scope-string-order-irreflexive
  (not (boymoo-compiler::table-text-less text text))
  :hints (("Goal" :in-theory (enable boymoo-compiler::table-text-less))))

(defthm generated-scope-string-order-asymmetric
  (implies (boymoo-compiler::table-text-less first second)
           (not (boymoo-compiler::table-text-less second first)))
  :hints (("Goal" :use (:instance generated-scope-string-order-transitive (third first))))
  :rule-classes nil)

(local
 (defthm generated-nthcdr-of-next-is-cdr
   (implies (natp index)
            (equal (nthcdr (1+ index) elements) (cdr (nthcdr index elements))))
   :hints (("Goal" :induct (nthcdr index elements) :in-theory (enable nthcdr)))))

(local
 (defthm generated-nthcdr-car-is-nth
   (implies (natp index)
            (equal (car (nthcdr index elements)) (nth index elements)))
   :hints (("Goal" :induct (nthcdr index elements) :in-theory (enable nthcdr nth)))))

(local
 (defthm generated-cons-suffix-length
   (implies (and (natp index) (<= index (len elements)))
            (equal (len (nthcdr index elements)) (- (len elements) index)))
   :hints (("Goal" :induct (nthcdr index elements) :in-theory (enable nthcdr)))))

(local
 (defthm generated-character-codes-identify-characters
   (implies (and (characterp first) (characterp second))
            (equal (equal (char-code first) (char-code second)) (equal first second)))
   :hints (("Goal" :use ((:instance acl2::code-char-char-code-is-identity (acl2::c first))
                          (:instance acl2::code-char-char-code-is-identity (acl2::c second)))
                   :in-theory (disable acl2::code-char-char-code-is-identity)))
   :rule-classes nil))

(local
 (defthm generated-nth-of-characters-is-character
   (implies (and (character-listp elements) (natp index) (< index (len elements)))
            (characterp (nth index elements)))
   :hints (("Goal" :induct (nth index elements) :in-theory (enable nth)))))

(local
 (defthm generated-nthcdr-of-list-is-list
   (implies (true-listp elements) (true-listp (nthcdr index elements)))
   :hints (("Goal" :induct (nthcdr index elements) :in-theory (enable nthcdr)))
   :rule-classes :type-prescription))

(local
 (defthm generated-nthcdr-at-true-list-length
   (implies (true-listp elements)
            (equal (nthcdr (len elements) elements) nil))
   :hints (("Goal" :induct (len elements)
                   :in-theory (e/d (nthcdr) (generated-nthcdr-of-next-is-cdr))))))

(local
 (defthm generated-string-suffix-at-end
   (implies (stringp text)
            (equal (nthcdr (len (coerce text 'list)) (coerce text 'list)) nil))
   :hints (("Goal" :use (:instance generated-nthcdr-at-true-list-length (elements (coerce text 'list)))
                   :in-theory (disable generated-nthcdr-at-true-list-length)))
   :rule-classes nil))

(local
 (defthm generated-conses-equal-by-components
   (implies (and (consp first) (consp second)
                 (equal (car first) (car second)) (equal (cdr first) (cdr second)))
            (equal first second))
   :rule-classes nil))

(local
 (defthm generated-string-slice-without-order-has-equal-suffixes
   (implies (and (stringp first) (stringp second) (natp index) (natp remaining)
                 (equal (+ index remaining) (length first))
                 (equal (+ index remaining) (length second))
                 (not (boymoo-compiler::table-string-less first second index remaining))
                 (not (boymoo-compiler::table-string-less second first index remaining)))
            (equal (nthcdr index (coerce first 'list)) (nthcdr index (coerce second 'list))))
   :hints (("Goal" :induct (generated-string-suffix-induction index remaining))
           ("Subgoal *1/2"
            :expand ((boymoo-compiler::table-string-less first second index remaining)
                     (boymoo-compiler::table-string-less second first index remaining))
            :use ((:instance generated-character-codes-identify-characters
                             (first (char first index)) (second (char second index)))
                  (:instance generated-cons-suffix-length (elements (coerce first 'list)))
                  (:instance generated-cons-suffix-length (elements (coerce second 'list)))
                  (:instance generated-conses-equal-by-components
                             (first (nthcdr index (coerce first 'list)))
                             (second (nthcdr index (coerce second 'list)))))
            :in-theory (e/d (char length) (generated-cons-suffix-length)))
           ("Subgoal *1/1"
            :use ((:instance generated-string-suffix-at-end (text first))
                  (:instance generated-string-suffix-at-end (text second)))
            :in-theory (enable length)))
   :rule-classes nil))

(defthm generated-scope-string-order-total
  (implies (and (stringp first) (stringp second) (not (equal first second))
                (not (boymoo-compiler::table-text-less first second)))
           (boymoo-compiler::table-text-less second first))
  :hints (("Goal"
           :use ((:instance generated-string-slice-without-order-has-equal-suffixes
                            (index 0) (remaining (length first)))
                 (:instance acl2::coerce-inverse-2 (acl2::x first))
                 (:instance acl2::coerce-inverse-2 (acl2::x second)))
           :in-theory (e/d (boymoo-compiler::table-text-less nthcdr) (acl2::coerce-inverse-2))))
  :rule-classes nil)
