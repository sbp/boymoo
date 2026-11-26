(in-package "BOYMOO-PROOFS")

(include-book "range-checks")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-label-names (items)
  (if (atom items)
      nil
    (if (eq (caar items) :label)
        (cons (cadar items) (assembly-label-names (cdr items)))
      (assembly-label-names (cdr items)))))

(defun assembly-references (items)
  (if (atom items)
      nil
    (if (assembly-item-refers-to-label-p (car items))
        (cons (assembly-item-target-label (car items)) (assembly-references (cdr items)))
      (assembly-references (cdr items)))))

(defun assembly-no-image-items-p (items)
  (if (atom items)
      t
    (and (not (eq (caar items) :image))
         (assembly-no-image-items-p (cdr items)))))

(defthm assembly-label-names-of-layout
  (equal (assembly-keys (assembly-labels items pc)) (assembly-label-names items))
  :hints (("Goal" :induct (assembly-labels items pc)
                  :in-theory (disable assembly-keys-of-labels assembly-labels-after-prefix
                                      boymoo-compiler::a64-image-item-size))))

(defthm assembly-assoc-label-of-layout
  (iff (assoc-equal key (assembly-labels items pc))
       (member-equal key (assembly-label-names items)))
  :hints (("Goal" :induct (assembly-labels items pc)
                  :in-theory (disable assembly-labels-after-prefix
                                      boymoo-compiler::a64-image-item-size))))

(local
 (defthm assembly-data-check-of-append
   (equal (assembly-data-list-p (append prefix suffix))
          (and (assembly-data-list-p prefix) (assembly-data-list-p suffix)))
   :hints (("Goal" :induct (append prefix suffix)
                   :in-theory (disable assembly-data-p)))))

(defthm assembly-fixed-items-supply-image-layout
  (implies (and (assembly-fixed-item-list-p items)
                (no-duplicatesp-equal (assembly-label-names items)))
           (assembly-image-layout-p items))
  :hints (("Goal" :induct (assembly-fixed-item-list-p items)
                  :in-theory (disable assembly-executable-item-p
                                      assembly-fixed-item-fields-p
                                      assembly-label-key-p assembly-labels))))

(defun assembly-word-offset-p (offset)
  (and (natp offset) (integerp (* 1/4 offset))))

(local (in-theory (disable floor mod ash assembly-labels-after-prefix)))

(local
 (defthm assembly-word-offset-of-sum
   (implies (and (assembly-word-offset-p a) (assembly-word-offset-p b))
            (assembly-word-offset-p (+ a b)))
   :hints (("Goal" :in-theory (enable acl2::distributivity)))))

(local
 (defthm assembly-word-offset-of-four-times
   (implies (natp words)
            (assembly-word-offset-p (* 4 words)))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 1/4) (acl2::y 4) (acl2::z words)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm assembly-floor-of-natural-is-natural
   (implies (natp offset)
            (natp (floor offset 4)))
   :hints (("Goal" :use ((:instance assembly-floor-bounds (x offset) (d 4)))))))

(local
 (defthm assembly-word-offset-of-padded-size
   (implies (natp size)
            (assembly-word-offset-p (boymoo-compiler::aligned-size size 2)))
   :hints (("Goal" :in-theory (enable assembly-high)))))

(local (in-theory (disable assembly-word-offset-p boymoo-compiler::aligned-size)))

(defthm assembly-word-offset-of-ordinary-item-size
  (implies (not (eq (car item) :image))
           (assembly-word-offset-p (boymoo-compiler::a64-image-item-size item))))

(local (in-theory (disable boymoo-compiler::a64-image-item-size)))

(defthm assembly-word-offset-of-image-free-size
  (implies (assembly-no-image-items-p items)
           (assembly-word-offset-p (assembly-size items)))
  :hints (("Goal" :induct (assembly-size items))))

(defthm assembly-word-offset-of-label
  (implies (and (assembly-no-image-items-p items)
                (assembly-word-offset-p pc)
                (assoc-equal key (assembly-labels items pc)))
           (assembly-word-offset-p (assembly-label-offset key (assembly-labels items pc))))
  :hints (("Goal" :induct (assembly-labels items pc)))
  :rule-classes nil)

(local
 (defthm assembly-word-offset-implies-alignment
   (implies (assembly-word-offset-p offset)
            (equal (mod offset 4) 0))
   :hints (("Goal"
            :use ((:instance assembly-floor-bounds (x offset) (d 4))
                  (:instance assembly-floor-unique (x offset) (d 4) (q (* 1/4 offset)))
                  (:instance acl2::associativity-of-* (acl2::x 4) (acl2::y 1/4) (acl2::z offset)))
            :in-theory (enable mod assembly-word-offset-p)))))

(defthm assembly-resolved-aligned-addresses
  (implies (and (assembly-no-image-items-p items)
                (assembly-no-image-items-p image)
                (assembly-word-offset-p pc)
                (subsetp-equal (assembly-references items) (assembly-label-names image)))
           (assembly-resolved-item-addresses-p items pc (assembly-labels image 0)))
  :hints (("Goal" :induct (assembly-items-characters items pc nil)
                  :in-theory (disable assembly-item-characters assembly-labels
                                      assembly-code-item-p assembly-item-refers-to-label-p
                                      assembly-item-target-label assembly-label-offset))
           ("Subgoal *1/2"
            :use ((:instance assembly-word-offset-of-label
                             (items image) (pc 0)
                             (key (assembly-item-target-label (car items)))))))
  :rule-classes nil)

(local
 (defthm assembly-data-check-of-final-image
   (equal (assembly-data-list-p (list (list :image (car data) (cdr data))))
          (proof-image-p data))))

(local
 (defthm assembly-labels-of-final-image
   (implies (acl2-numberp pc)
            (equal (assembly-labels (append prefix (list (list :image (car data) (cdr data)))) pc)
                   (assembly-labels prefix pc)))
   :hints (("Goal" :in-theory (e/d (assembly-labels-after-prefix)
                                   (assembly-size binary-append))))))

(defthm assembly-image-layout-with-final-data
  (implies (and (assembly-image-layout-p prefix) (proof-image-p data))
           (assembly-image-layout-p
            (append prefix (list (list :image (car data) (cdr data))))))
  :hints (("Goal" :in-theory (e/d (assembly-labels-after-prefix)
                                 (assembly-labels assembly-size
                                  assembly-data-list-p proof-image-p))))
  :rule-classes nil)

(local
 (defthm assembly-image-item-has-no-executable-field
   (assembly-items-executable-p (list (list :image (car data) (cdr data))) pc labels)))

(defthm assembly-image-program-with-final-data
  (implies (and (assembly-fixed-item-list-p prefix)
                (no-duplicatesp-equal (assembly-label-names prefix))
                (assembly-no-image-items-p prefix)
                (subsetp-equal (assembly-references prefix) (assembly-label-names prefix))
                (< (assembly-size prefix) (expt 2 20))
                (proof-image-p data))
           (assembly-image-program-p
            (append prefix (list (list :image (car data) (cdr data))))))
  :hints (("Goal"
           :use ((:instance assembly-resolved-aligned-addresses (items prefix) (image prefix) (pc 0))
                 (:instance assembly-image-program-for-small-image (items prefix))
                 assembly-image-layout-with-final-data)
           :in-theory (e/d (assembly-labels-after-prefix)
                           (assembly-fixed-item-list-p assembly-label-names
                            assembly-labels assembly-resolved-item-addresses-p
                            assembly-items-executable-p assembly-image-layout-p
                            assembly-data-list-p assembly-size proof-image-p))))
  :rule-classes nil)
