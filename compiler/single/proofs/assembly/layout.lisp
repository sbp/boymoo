(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defthm assembly-append-associative
  (equal (append (append xs ys) zs)
         (append xs (append ys zs))))

(defthm assembly-append-to-nil
  (implies (true-listp xs)
           (equal (append xs nil) xs)))

(defun assembly-size (items)
  (if (atom items)
      0
    (+ (boymoo-compiler::a64-image-item-size (car items))
       (assembly-size (cdr items)))))

(defun assembly-labels (items pc)
  (if (atom items)
      nil
    (if (eq (caar items) :label)
        (acons (cadar items) pc (assembly-labels (cdr items) pc))
      (assembly-labels (cdr items)
                       (+ pc (boymoo-compiler::a64-image-item-size (car items)))))))

(defun assembly-code-items (items)
  (if (atom items)
      nil
    (if (eq (caar items) :label)
        (assembly-code-items (cdr items))
      (cons (car items) (assembly-code-items (cdr items))))))

(defun assembly-keys (entries)
  (if (atom entries)
      nil
    (cons (caar entries) (assembly-keys (cdr entries)))))

(defthm assembly-size-of-label
  (implies (equal (car item) :label)
           (equal (boymoo-compiler::a64-image-item-size item) 0)))

(defthm assembly-keys-of-labels
  (implies (syntaxp (not (equal pc ''0)))
           (equal (assembly-keys (assembly-labels items pc))
                  (assembly-keys (assembly-labels items 0))))
  :hints (("Goal" :induct (assembly-labels items pc)
                  :in-theory (disable boymoo-compiler::a64-image-item-size))))

(defthm assembly-labels-after-prefix
  (implies (acl2-numberp pc)
           (equal (assembly-labels (append prefix items) pc)
                  (append (assembly-labels prefix pc)
                          (assembly-labels items (+ pc (assembly-size prefix))))))
  :hints (("Goal" :induct (assembly-labels prefix pc)
                  :in-theory (disable boymoo-compiler::a64-image-item-size))))

(defthm assembly-size-of-append
  (equal (assembly-size (append first rest))
         (+ (assembly-size first) (assembly-size rest)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::a64-image-item-size))))

(defthm assembly-size-of-revappend
  (equal (assembly-size (revappend first rest))
         (+ (assembly-size first) (assembly-size rest)))
  :hints (("Goal" :induct (revappend first rest)
                  :in-theory (disable boymoo-compiler::a64-image-item-size))))

(defthm assembly-size-of-code-items
  (equal (assembly-size (assembly-code-items items)) (assembly-size items))
  :hints (("Goal" :in-theory (disable boymoo-compiler::a64-image-item-size))))
