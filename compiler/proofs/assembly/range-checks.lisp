(in-package "BOYMOO-PROOFS")

(include-book "image-decoding")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod assembly-power-of-two
                           boymoo-compiler::a64-image-item-size)))

(defthm assembly-label-offset-bounds
  (implies (and (natp pc) (assembly-layout-sizes-p items)
                (assoc-equal key (assembly-labels items pc)))
           (let ((offset (assembly-label-offset key (assembly-labels items pc))))
             (and (natp offset)
                  (<= pc offset)
                  (<= offset (+ pc (assembly-size items))))))
  :hints (("Goal" :induct (assembly-labels items pc)
                  :in-theory (disable assembly-labels-after-prefix)))
  :rule-classes nil)

(local
 (defthm assembly-quarters-cancel-four
   (equal (* 1/4 (* 4 value)) (fix value))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 1/4) (acl2::y 4) (acl2::z value)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm assembly-multiply-by-quarter-preserves-equality
   (implies (equal a b)
            (equal (* 1/4 a) (* 1/4 b)))
   :rule-classes nil))

(local
 (defthm assembly-divide-aligned-offset
   (implies (and (integerp address) (equal (mod address 4) 0))
            (equal (* 1/4 address) (floor address 4)))
   :hints (("Goal"
            :use ((:instance assembly-multiply-by-quarter-preserves-equality
                             (a address) (b (* 4 (floor address 4)))))
            :in-theory (enable mod)))))

(defthm assembly-branch-field-fits-small-image
  (implies (and (natp pc) (natp target)
                (< pc (expt 2 20)) (< target (expt 2 20))
                (equal (mod pc 4) 0) (equal (mod target 4) 0))
           (and (assembly-signed-scaled-p 19 2 (- target pc))
                (assembly-signed-scaled-p 26 2 (- target pc))))
  :hints (("Goal"
           :use ((:instance assembly-divide-aligned-offset (address pc))
                 (:instance assembly-divide-aligned-offset (address target)))
           :in-theory (disable assembly-divide-aligned-offset)))
  :rule-classes nil)

(local
 (defthm assembly-page-number-in-small-image
   (implies (and (natp offset) (< offset (expt 2 20)))
            (and (<= 0 (floor offset 4096))
                 (< (floor offset 4096) 256)))
   :hints (("Goal" :use ((:instance assembly-floor-bounds (x offset) (d 4096)))))
   :rule-classes nil))

(defthm assembly-address-fields-fit-small-image
  (implies (and (natp pc) (natp target)
                (< pc (expt 2 20)) (< target (expt 2 20)))
           (and (assembly-signed-scaled-p 21 0 (- target pc))
                (assembly-signed-scaled-p 21 0
                                         (- (floor target 4096) (floor pc 4096)))))
  :hints (("Goal"
           :use ((:instance assembly-page-number-in-small-image (offset pc))
                 (:instance assembly-page-number-in-small-image (offset target)))))
  :rule-classes nil)

(defun assembly-fixed-item-fields-p (item)
  (assembly-executable-item-p item 0 (list (cons (assembly-item-target-label item) 0))))

(defun assembly-fixed-item-p (item)
  (cond ((assembly-code-item-p item) (assembly-fixed-item-fields-p item))
        ((eq (car item) :label) (assembly-label-key-p (cadr item)))
        (t (assembly-data-p item))))

(defun assembly-fixed-item-list-p (items)
  (if (atom items)
      (null items)
    (and (assembly-fixed-item-p (car items))
         (assembly-fixed-item-list-p (cdr items)))))

(defthm assembly-fixed-fields-of-system-and-runtime
  (and (assembly-fixed-item-list-p (boymoo-compiler::linux-system-code))
       (assembly-fixed-item-list-p (boymoo-compiler::system-code))
       (assembly-fixed-item-list-p (boymoo-compiler::runtime-code)))
  :hints (("Goal" :in-theory (union-theories
                            (theory 'acl2::minimal-theory)
                            '((:executable-counterpart assembly-fixed-item-list-p)
                              (:executable-counterpart boymoo-compiler::linux-system-code)
                              (:executable-counterpart boymoo-compiler::system-code)
                              (:executable-counterpart boymoo-compiler::runtime-code)))))
  :rule-classes nil)

(defthm assembly-item-fields-fit-small-image
  (let ((target (assembly-label-offset (assembly-item-target-label item) offsets)))
    (implies (and (assembly-fixed-item-fields-p item)
                  (natp pc) (equal (mod pc 4) 0) (<= pc size) (< size (expt 2 20))
                  (implies (assembly-item-refers-to-label-p item)
                           (and (natp target) (<= target size)
                                (implies (member-eq (car item) '(:b :bl :b-cond :cbz :cbnz))
                                         (equal (mod target 4) 0)))))
             (assembly-executable-item-p item pc offsets)))
  :hints (("Goal"
           :use ((:instance assembly-branch-field-fits-small-image
                            (target (assembly-label-offset (assembly-item-target-label item) offsets)))
                 (:instance assembly-address-fields-fit-small-image
                            (target (assembly-label-offset (assembly-item-target-label item) offsets))))
           :in-theory (disable assembly-signed-scaled-p)))
  :rule-classes nil)

(defun assembly-resolved-item-addresses-p (items pc offsets)
  (if (atom items)
      t
    (let ((item (car items)))
      (and (implies (assembly-code-item-p item)
                    (and (equal (mod pc 4) 0)
                         (implies (assembly-item-refers-to-label-p item)
                                  (and (assoc-equal (assembly-item-target-label item) offsets)
                                       (implies (member-eq (car item) '(:b :bl :b-cond :cbz :cbnz))
                                                (equal (mod (assembly-label-offset
                                                             (assembly-item-target-label item) offsets)
                                                            4)
                                                       0))))))
           (assembly-resolved-item-addresses-p
            (cdr items) (+ pc (boymoo-compiler::a64-image-item-size item)) offsets)))))

(local
 (defthm assembly-layout-size-is-nonnegative
   (implies (assembly-layout-sizes-p items)
            (<= 0 (assembly-size items)))
   :hints (("Goal" :induct (assembly-size items)))
   :rule-classes :linear))

(local
 (defthm assembly-resolved-items-fit-small-image
   (let ((offsets (assembly-labels image 0))
         (size (assembly-size image)))
     (implies (and (assembly-layout-sizes-p items)
                   (assembly-layout-sizes-p image)
                   (natp pc) (<= (+ pc (assembly-size items)) size)
                   (< size (expt 2 20))
                   (assembly-fixed-item-list-p items)
                   (assembly-resolved-item-addresses-p items pc offsets))
              (assembly-items-executable-p items pc offsets)))
   :hints (("Goal" :induct (assembly-items-characters items pc nil)
                   :in-theory (disable assembly-executable-item-p assembly-fixed-item-fields-p
                                       assembly-code-item-p assembly-item-refers-to-label-p
                                       assembly-item-target-label assembly-label-offset
                                       assembly-labels assembly-labels-after-prefix assembly-item-characters))
           ("Subgoal *1/2"
            :use ((:instance assembly-item-fields-fit-small-image
                             (item (car items)) (offsets (assembly-labels image 0))
                             (size (assembly-size image)))
                  (:instance assembly-label-offset-bounds
                             (items image) (pc 0) (key (assembly-item-target-label (car items)))))))
   :rule-classes nil))

(local
 (defthm assembly-layout-witness-requires-natural-sizes
   (implies (assembly-layout-input-p items 0 nil ranks)
            (assembly-layout-sizes-p items))
   :hints (("Goal" :in-theory (disable assembly-labels assembly-layout-sizes-p
                                       assembly-ranking-p assembly-ranked-entries-p
                                       assembly-labels-unused-p assembly-table-p)))
   :rule-classes nil))

(defthm assembly-image-program-for-small-image
  (implies (and (assembly-image-layout-p items) (assembly-fixed-item-list-p items)
                (< (assembly-size items) (expt 2 20))
                (assembly-resolved-item-addresses-p items 0 (assembly-labels items 0)))
           (assembly-image-program-p items))
  :hints (("Goal"
           :use (assembly-image-layout-supplies-ranks
                 (:instance assembly-layout-witness-requires-natural-sizes
                            (ranks (assembly-key-ranks (assembly-keys (assembly-labels items 0)))))
                 (:instance assembly-resolved-items-fit-small-image (image items) (pc 0)))
           :in-theory (disable assembly-image-layout-supplies-ranks assembly-layout-input-p
                               assembly-image-layout-p assembly-layout-sizes-p assembly-key-ranks
                               assembly-labels assembly-size assembly-items-executable-p
                               assembly-fixed-item-list-p assembly-resolved-item-addresses-p)))
  :rule-classes nil)
