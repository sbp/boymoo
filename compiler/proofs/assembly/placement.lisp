(in-package "BOYMOO-PROOFS")

(include-book "bytes")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-model::a64-load boymoo-compiler::a64-layout
                           boymoo-compiler::a64-assemble-image
                           boymoo-compiler::a64-image-item-size
                           assembly-item-characters assembly-layout-input-p)))

(defun assembly-characters-at-p (chars address machine)
  (if (atom chars)
      (null chars)
    (and (equal (car chars) (code-char (boymoo-model::a64-load 1 address machine)))
         (assembly-characters-at-p (cdr chars) (1+ (ifix address)) machine))))

(local
 (defthm assembly-byte-characters-list
   (character-listp (proof-byte-characters bytes))))

(local
 (defthm assembly-placement-of-read-characters
   (assembly-characters-at-p
    (proof-byte-characters (proof-byte-list count address machine)) address machine)
   :hints (("Goal" :induct (proof-byte-list count address machine)))))

(defthm assembly-load-string-placement
  (assembly-characters-at-p
   (coerce (proof-load-string count address machine) 'list) address machine)
  :hints (("Goal" :in-theory (disable proof-byte-characters proof-byte-list))))

(defthm assembly-character-placement-of-append
  (implies (and (integerp address) (true-listp chars))
           (equal (assembly-characters-at-p (append chars rest) address machine)
                  (and (assembly-characters-at-p chars address machine)
                       (assembly-characters-at-p rest (+ address (len chars)) machine))))
  :hints (("Goal" :induct (assembly-characters-at-p chars address machine))))

(defthm assembly-fragments-place-characters
  (implies (and (integerp address)
                (proof-fragments-p fragments)
                (proof-fragments-at-p fragments address machine))
           (assembly-characters-at-p
            (assembly-fragment-characters fragments) address machine))
  :hints (("Goal" :induct (proof-fragments-at-p fragments address machine)
                  :in-theory (disable proof-load-string))
          ("Subgoal *1/2"
           :use ((:instance assembly-load-string-placement
                            (count (length (car fragments)))))
           :in-theory (disable assembly-load-string-placement))))

(defthm assembly-linked-image-places-characters
  (implies (and (assembly-layout-input-p items 0 nil ranks)
                (assembly-data-list-p items)
                (assoc-equal entry (assembly-labels items 0))
                (proof-linked-image-p items entry base world))
           (assembly-characters-at-p
            (assembly-items-characters
             items 0 (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))
            base (proof-world-machine world)))
  :hints (("Goal"
           :use (assembly-flattened-image
                 (:instance assembly-fragments-place-characters
                            (fragments (cdr (mv-nth 0
                                                    (boymoo-compiler::a64-assemble-image items entry))))
                            (address base) (machine (proof-world-machine world))))
           :in-theory (disable assembly-flattened-image assembly-fragments-place-characters
                               proof-fragments-at-p proof-world-machine
                               assembly-fragment-characters proof-fragments-p))))

(local
 (defthm assembly-item-characters-is-true-list
   (true-listp (assembly-item-characters item pc labels))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (assembly-item-characters)
                                  (assembly-item-words assembly-byte-character))))))

(local
 (defthm assembly-items-characters-is-true-list
   (true-listp (assembly-items-characters items pc labels))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (assembly-items-characters items pc labels)))))

(local
 (defthm assembly-first-item-placed
   (implies (and (integerp address)
                 (assembly-characters-at-p
                  (assembly-items-characters (cons item suffix) pc labels) address machine))
            (assembly-characters-at-p (assembly-item-characters item pc labels) address machine))
   :hints (("Goal" :expand ((assembly-items-characters (cons item suffix) pc labels))))
   :rule-classes nil))

(defthm assembly-item-placed-by-character-stream
  (implies (and (integerp base)
                (integerp pc)
                (assembly-data-list-p prefix)
                (assembly-data-p item)
                (assembly-characters-at-p
                 (assembly-items-characters (append prefix (cons item suffix)) pc labels)
                 base machine))
           (assembly-characters-at-p
            (assembly-item-characters item (+ pc (assembly-size prefix)) labels)
            (+ base (assembly-size prefix)) machine))
  :hints (("Goal"
           :use ((:instance assembly-first-item-placed
                            (address (+ base (assembly-size prefix)))
                            (pc (+ pc (assembly-size prefix))))
                 (:instance assembly-items-characters-of-append
                            (first prefix) (rest (cons item suffix)))
                 (:instance assembly-items-character-count (items prefix))
                 (:instance assembly-character-placement-of-append
                            (chars (assembly-items-characters prefix pc labels))
                            (rest (assembly-items-characters (cons item suffix)
                                                             (+ pc (assembly-size prefix)) labels))
                            (address base)))
           :in-theory (disable assembly-items-characters-of-append assembly-data-p
                               assembly-items-characters assembly-items-character-count
                               assembly-character-placement-of-append))))

(local
 (defthm assembly-data-list-p-of-append
   (equal (assembly-data-list-p (append prefix suffix))
          (and (assembly-data-list-p prefix) (assembly-data-list-p suffix)))))

(defthm assembly-linked-image-places-item
  (let* ((items (append prefix (cons item suffix)))
         (labels (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))
         (pc (assembly-size prefix)))
    (implies (and (assembly-layout-input-p items 0 nil ranks)
                  (assembly-data-list-p items)
                  (assoc-equal entry (assembly-labels items 0))
                  (proof-linked-image-p items entry base world))
             (assembly-characters-at-p
              (assembly-item-characters item pc labels)
              (+ base pc) (proof-world-machine world))))
  :hints (("Goal"
           :use ((:instance assembly-linked-image-places-characters
                            (items (append prefix (cons item suffix))))
                 (:instance assembly-item-placed-by-character-stream
                            (pc 0) (machine (proof-world-machine world))
                            (labels (mv-nth 1
                                            (boymoo-compiler::a64-layout
                                             (append prefix (cons item suffix)) 0 nil nil)))))
           :in-theory (disable assembly-linked-image-places-characters
                               assembly-item-placed-by-character-stream
                               assembly-items-characters))))
