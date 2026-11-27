(in-package "BOYMOO-PROOFS")

(include-book "static-terms")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable length ash char boymoo-compiler::index-get boymoo-compiler::index-set
                           boymoo-compiler::decode-part boymoo-compiler::declaration-list
                           boymoo-compiler::data-imports boymoo-compiler::data-text
                           boymoo-compiler::data-intern boymoo-compiler::data-vector
                           boymoo-compiler::data-with-block boymoo-compiler::data-word
                           boymoo-compiler::data-block
                           boymoo-compiler::data-bucket-vector
                           boymoo-compiler::data-program-symbols boymoo-compiler::data-initial
                           boymoo-compiler::data-package-numbers
                           (:executable-counterpart boymoo-compiler::compiler-error)
                           assembly-static-block-p assembly-static-data-state-p
                           assembly-static-program-input-p assembly-generator-index-p
                           assembly-static-bucket-tree-p assembly-constant-index-p)))

(local
 (defthm assembly-first-static-data-result
   (equal (mv-nth 0 values) (car values))))

(local
 (defthm assembly-second-static-data-result
   (equal (mv-nth 1 values) (cadr values))))

(local
 (defthm assembly-third-static-data-result
   (equal (mv-nth 2 values) (caddr values))))

(defun assembly-static-package-lines-p (lines)
  (if (atom lines)
      t
    (and (stringp (boymoo-compiler::decode-part (cadar lines) 0 (length (cadar lines))))
         (assembly-static-symbol-list-p (boymoo-compiler::declaration-list (caddar lines)))
         (assembly-static-package-lines-p (cdr lines)))))

(local
 (defthm assembly-static-reversed-package-names
   (implies (and (string-listp names) (string-listp tail))
            (string-listp (boymoo-compiler::reverse-onto names tail)))))

(local
 (defthm assembly-static-reversed-words
   (implies (and (assembly-static-words-p words) (assembly-static-words-p tail))
            (assembly-static-words-p (boymoo-compiler::reverse-onto words tail)))))

(local (in-theory (disable boymoo-compiler::reverse-onto assembly-static-symbol-list-p)))

(local
 (defthm assembly-static-size-and-type-of-package-declarations
   (let ((out (boymoo-compiler::data-package-declarations lines packages declared
                                                         declarations state-data names)))
     (implies (and (assembly-static-data-state-p state-data)
                   (assembly-static-package-lines-p lines)
                   (assembly-generator-index-p declarations 12 :static-declaration)
                   (string-listp names))
              (and (assembly-generator-index-p (car out) 12 :static-declaration)
                   (assembly-static-data-state-p (cadr out))
                   (string-listp (caddr out)))))
   :hints (("Goal"
            :induct (boymoo-compiler::data-package-declarations lines packages declared
                                                               declarations state-data names)))))

(local
 (defthm assembly-static-package-vectors-are-sized
   (let ((out (boymoo-compiler::data-package-vectors names packages declarations state-data reversed)))
     (implies (and (assembly-static-data-state-p state-data)
                   (string-listp names)
                   (assembly-generator-index-p declarations 12 :static-declaration)
                   (assembly-static-words-p reversed))
              (and (integerp (car out))
                   (assembly-static-data-state-p (cadr out)))))
   :hints (("Goal"
            :induct (boymoo-compiler::data-package-vectors names packages declarations
                                                            state-data reversed)))))

(local (in-theory (disable boymoo-compiler::data-package-declarations
                           boymoo-compiler::data-package-vectors)))

(defthm assembly-static-package-state-is-sized
  (let ((out (boymoo-compiler::data-packages lines number packages state-data reversed)))
    (implies (and (assembly-static-data-state-p state-data)
                  (assembly-static-package-lines-p lines)
                  (assembly-static-words-p reversed))
             (and (integerp (car out))
                  (assembly-static-data-state-p (cadr out))))))

(defun assembly-static-build-input-p (lines package-lines)
  (and (assembly-static-package-lines-p package-lines)
       (assembly-static-program-input-p lines)
       (boymoo-compiler::index-get "COMMON-LISP"
                                   (boymoo-compiler::data-package-numbers package-lines 0 nil))))

(local
 (defthm assembly-static-image-with-runtime-header
   (let ((prefix (list (car block) package-ref bucket-ref 34
                       4098 nil-name tagged-package 4098 t-name tagged-package)))
     (implies (and (assembly-static-block-p block)
                   (integerp nil-name) (integerp t-name) (integerp package-ref)
                   (not (stringp bucket-ref)) (not (stringp tagged-package)))
              (proof-image-p
               (cons (car block)
                     (boymoo-compiler::data-write
                      (boymoo-compiler::reverse-onto prefix nil)
                      (boymoo-compiler::data-write (cdr block) nil))))))
   :hints (("Goal"
            :use ((:instance assembly-static-image-from-sized-block
                             (prefix (list (car block) package-ref bucket-ref 34
                                           4098 nil-name tagged-package 4098 t-name tagged-package))))
            :in-theory (disable boymoo-compiler::data-write assembly-static-image-from-sized-block
                                proof-image-p)))))

(local (in-theory (disable boymoo-compiler::data-packages
                           boymoo-compiler::data-write assembly-static-package-lines-p proof-image-p)))

(defthm assembly-data-build-produces-sized-image-and-typed-index
  (let ((out (boymoo-compiler::data-build lines package-lines)))
    (implies (assembly-static-build-input-p lines package-lines)
             (and (proof-image-p (car out))
                  (assembly-constant-index-p (cadr out) 12)))))
