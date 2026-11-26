(in-package "BOYMOO-PROOFS")

(include-book "label-ranks")
(include-book "item-decoding")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-image-layout-p (items)
  (let ((keys (assembly-keys (assembly-labels items 0))))
    (and (true-listp items)
         (assembly-data-list-p items)
         (assembly-label-key-list-p keys)
         (no-duplicatesp-equal keys))))

(local
 (defthm assembly-data-supplies-layout-sizes
   (implies (assembly-data-list-p items)
            (assembly-layout-sizes-p items))
   :hints (("Goal" :induct (assembly-data-list-p items)
                   :in-theory (disable assembly-data-p boymoo-compiler::a64-image-item-size
                                       assembly-item-characters assembly-item-character-count))
           ("Subgoal *1/2"
            :use ((:instance assembly-item-character-count (item (car items)) (pc 0) (labels nil)))))))

(defthm assembly-image-layout-supplies-ranks
  (implies (assembly-image-layout-p items)
           (assembly-layout-input-p items 0 nil
                                    (assembly-key-ranks (assembly-keys (assembly-labels items 0)))))
  :hints (("Goal"
           :use ((:instance assembly-layout-input-for-distinct-labels (pc 0)))
           :in-theory (disable assembly-layout-input-for-distinct-labels assembly-layout-input-p
                               assembly-key-ranks assembly-layout-sizes-p
                               assembly-labels assembly-data-list-p))))

(local
 (defthm assembly-item-label-agrees-with-assembly-layout
   (let ((offsets (assembly-labels items 0)))
     (implies (and (assembly-layout-input-p items 0 nil ranks)
                   (assembly-executable-item-p item pc offsets))
              (assembly-item-label-agreement-p
               item (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)) offsets)))
   :hints (("Goal"
            :use ((:instance assembly-executable-item-target-defined (offsets (assembly-labels items 0)))
                  (:instance assembly-layout-entry-offset (entry (assembly-item-target-label item))))
            :in-theory (disable assembly-layout-entry-offset assembly-item-target-label
                                assembly-item-refers-to-label-p assembly-executable-item-p
                                assembly-layout-input-p assembly-labels
                                boymoo-compiler::a64-layout boymoo-compiler::a64-offset)))
   :rule-classes nil))

(defthm assembly-assemble-image-for-distinct-labels
  (implies (and (assembly-image-layout-p items)
                (assoc-equal entry (assembly-labels items 0)))
           (mv-let (image offset)
             (boymoo-compiler::a64-assemble-image items entry)
             (and (proof-image-p image)
                  (equal (car image) (assembly-size items))
                  (equal offset (assembly-label-offset entry (assembly-labels items 0)))
                  (equal (assembly-fragment-characters (cdr image))
                         (assembly-items-characters
                          items 0 (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))))))
  :hints (("Goal"
           :use ((:instance assembly-flattened-image
                            (ranks (assembly-key-ranks (assembly-keys (assembly-labels items 0)))))
                 (:instance assembly-image-well-formed
                            (ranks (assembly-key-ranks (assembly-keys (assembly-labels items 0)))))
                 assembly-image-layout-supplies-ranks)
           :in-theory (disable assembly-flattened-image assembly-image-well-formed
                               assembly-image-layout-supplies-ranks assembly-layout-input-p
                               assembly-key-ranks assembly-size assembly-data-list-p
                               assembly-label-key-list-p assembly-labels assembly-items-characters
                               proof-image-p boymoo-compiler::a64-layout
                               boymoo-compiler::a64-assemble-image)))
  :rule-classes nil)

(defthm assembly-linked-executable-item-instructions
  (let* ((items (append prefix (cons item suffix)))
         (pc (assembly-size prefix))
         (offsets (assembly-labels items 0)))
    (implies (and (assembly-image-layout-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base world)
                  (assembly-executable-item-p item pc offsets))
             (proof-instructions-at-p
              (assembly-specified-instructions item pc offsets) (+ base pc) world)))
  :hints (("Goal"
           :use ((:instance assembly-image-layout-supplies-ranks (items (append prefix (cons item suffix))))
                 (:instance assembly-item-label-agrees-with-assembly-layout
                            (items (append prefix (cons item suffix)))
                            (pc (assembly-size prefix))
                            (ranks (assembly-key-ranks
                                    (assembly-keys (assembly-labels (append prefix (cons item suffix)) 0)))))
                 (:instance assembly-executable-item-position
                            (pc (assembly-size prefix))
                            (offsets (assembly-labels (append prefix (cons item suffix)) 0)))
                 (:instance assembly-specified-instruction-shape
                            (pc (assembly-size prefix))
                            (offsets (assembly-labels (append prefix (cons item suffix)) 0)))
                 (:instance assembly-executable-item-decodes
                            (pc (assembly-size prefix))
                            (offsets (assembly-labels (append prefix (cons item suffix)) 0))
                            (labels (mv-nth 1 (boymoo-compiler::a64-layout
                                              (append prefix (cons item suffix)) 0 nil nil))))
                 (:instance assembly-linked-specified-instructions
                            (ranks (assembly-key-ranks
                                    (assembly-keys (assembly-labels (append prefix (cons item suffix)) 0))))
                            (instructions
                             (assembly-specified-instructions
                              item (assembly-size prefix)
                              (assembly-labels (append prefix (cons item suffix)) 0)))))
           :in-theory (disable assembly-image-layout-supplies-ranks assembly-layout-input-p
                               assembly-linked-specified-instructions proof-linked-image-p
                               proof-instructions-at-p assembly-executable-item-p
                               assembly-specified-instructions assembly-single-instruction
                               assembly-item-label-agreement-p assembly-item-words
                               assembly-decode-words assembly-decoded-list-p
                               assembly-register-instruction-p assembly-code-item-p
                               assembly-data-list-p assembly-key-ranks assembly-layout-sizes-p
                               assembly-labels assembly-labels-after-prefix
                               assembly-label-key-list-p assembly-size boymoo-compiler::a64-layout)))
  :rule-classes nil)

(defun assembly-items-executable-p (items pc offsets)
  (if (atom items)
      t
    (and (or (not (assembly-code-item-p (car items)))
             (assembly-executable-item-p (car items) pc offsets))
         (assembly-items-executable-p
          (cdr items) (+ pc (boymoo-compiler::a64-image-item-size (car items))) offsets))))

(defun assembly-image-program-p (items)
  (and (assembly-image-layout-p items)
       (assembly-items-executable-p items 0 (assembly-labels items 0))))

(defthm assembly-items-executable-after-prefix
  (implies (acl2-numberp pc)
           (equal (assembly-items-executable-p (append prefix suffix) pc offsets)
                  (and (assembly-items-executable-p prefix pc offsets)
                       (assembly-items-executable-p suffix (+ pc (assembly-size prefix)) offsets))))
  :hints (("Goal" :induct (assembly-items-executable-p prefix pc offsets)
                  :in-theory (disable assembly-code-item-p assembly-executable-item-p
                                      boymoo-compiler::a64-image-item-size))))

(defthm assembly-linked-program-item-instructions
  (let* ((items (append prefix (cons item suffix)))
         (pc (assembly-size prefix))
         (offsets (assembly-labels items 0)))
    (implies (and (assembly-image-program-p items)
                  (assoc-equal entry offsets)
                  (proof-linked-image-p items entry base world)
                  (assembly-code-item-p item))
             (proof-instructions-at-p
              (assembly-specified-instructions item pc offsets) (+ base pc) world)))
  :hints (("Goal"
           :use (assembly-linked-executable-item-instructions)
           :in-theory (disable assembly-image-layout-p proof-linked-image-p
                               proof-instructions-at-p assembly-executable-item-p
                               assembly-specified-instructions assembly-code-item-p
                               boymoo-compiler::a64-image-item-size
                               assembly-labels assembly-labels-after-prefix assembly-size)))
  :rule-classes nil)
