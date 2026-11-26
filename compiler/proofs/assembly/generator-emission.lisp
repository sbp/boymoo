(in-package "BOYMOO-PROOFS")

(include-book "image-bounds")
(include-book "generator-induction")

(logic)
(set-verify-guards-eagerness 0)

(defthm assembly-projections-of-append
  (and (equal (assembly-label-names (append items code))
              (append (assembly-label-names items) (assembly-label-names code)))
       (equal (assembly-references (append items code))
              (append (assembly-references items) (assembly-references code)))
       (equal (assembly-no-image-items-p (append items code))
              (and (assembly-no-image-items-p items) (assembly-no-image-items-p code))))
  :hints (("Goal" :induct (append items code)
                  :in-theory (disable assembly-item-refers-to-label-p
                                      assembly-item-target-label))))

(defthm assembly-projections-of-revappend
  (and (equal (assembly-label-names (revappend items code))
              (revappend (assembly-label-names items) (assembly-label-names code)))
       (equal (assembly-references (revappend items code))
              (revappend (assembly-references items) (assembly-references code)))
       (equal (assembly-no-image-items-p (revappend items code))
              (and (assembly-no-image-items-p items) (assembly-no-image-items-p code))))
  :hints (("Goal" :induct (revappend items code)
                  :in-theory (disable assembly-item-refers-to-label-p
                                      assembly-item-target-label))))

(defthm assembly-reverse-onto-as-revappend
  (equal (boymoo-compiler::reverse-onto items code) (revappend items code)))

(defmacro assembly-projections-preserved (name expression &rest hints)
   `(defthm ,name
      (and (equal (assembly-label-names ,expression) (assembly-label-names code))
           (equal (assembly-references ,expression) (assembly-references code))
           (equal (assembly-no-image-items-p ,expression) (assembly-no-image-items-p code)))
      ,@(if hints (list :hints hints) nil)))

(assembly-projections-preserved assembly-projections-of-gen-load-high
 (boymoo-compiler::gen-load-high rd n shift code)
 ("Goal" :induct (boymoo-compiler::gen-load-high rd n shift code)
         :in-theory (disable boymoo-compiler::low-bits ash)))

(local (in-theory (disable boymoo-compiler::gen-load-high boymoo-compiler::low-bits ash)))

(assembly-projections-preserved assembly-projections-of-gen-load-word
 (boymoo-compiler::gen-load-word rd n code))

(assembly-projections-preserved assembly-projections-of-gen-load-datum
 (boymoo-compiler::gen-load-datum rd datum code))

(local (in-theory (disable boymoo-compiler::gen-load-word boymoo-compiler::gen-load-datum)))

(assembly-projections-preserved assembly-projections-of-gen-address
 (boymoo-compiler::gen-address rd rn bytes subtract code))

(assembly-projections-preserved assembly-projections-of-gen-frame-word
 (boymoo-compiler::gen-frame-word rd slot code))

(local (in-theory (disable boymoo-compiler::gen-address boymoo-compiler::gen-frame-word)))

(assembly-projections-preserved assembly-projections-of-gen-push
 (boymoo-compiler::gen-push code))

(assembly-projections-preserved assembly-projections-of-gen-drop
 (boymoo-compiler::gen-drop count code))

(assembly-projections-preserved assembly-projections-of-gen-finish
 (boymoo-compiler::gen-finish tail code))

(assembly-projections-preserved assembly-projections-of-gen-argument-registers
 (boymoo-compiler::gen-argument-registers remaining slot reg code)
 ("Goal" :induct (boymoo-compiler::gen-argument-registers remaining slot reg code)))

(assembly-projections-preserved assembly-projections-of-gen-copy-arguments
 (boymoo-compiler::gen-copy-arguments remaining offset code)
 ("Goal" :induct (boymoo-compiler::gen-copy-arguments remaining offset code)))

(defthm assembly-projections-of-gen-defined-call
  (let ((result (boymoo-compiler::gen-defined-call name arity tail code)))
    (and (equal (assembly-label-names result) (assembly-label-names code))
         (equal (assembly-references result) (cons (list :fn name) (assembly-references code)))
         (equal (assembly-no-image-items-p result) (assembly-no-image-items-p code))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-copy-arguments))))

(defun assembly-simple-form-p (term)
  (or (atom term) (and (stringp (cadr term)) (not (cddr term)))))

(defun assembly-simple-forms-p (terms)
  (if (atom terms)
      t
    (and (assembly-simple-form-p (car terms))
         (assembly-simple-forms-p (cdr terms)))))

(defthm assembly-projections-of-gen-simple
  (let ((result (boymoo-compiler::gen-simple term rd scope constants code))
        (rest (if (assembly-simple-form-p term) code nil)))
    (and (equal (assembly-label-names result) (assembly-label-names rest))
         (equal (assembly-references result) (assembly-references rest))
         (equal (assembly-no-image-items-p result) (assembly-no-image-items-p rest))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-slot boymoo-compiler::gen-datum))))

(defthm assembly-projections-of-gen-simple-args
  (let ((result (boymoo-compiler::gen-simple-args terms reg scope constants code))
        (rest (if (assembly-simple-forms-p terms) code nil)))
    (and (equal (assembly-label-names result) (assembly-label-names rest))
         (equal (assembly-references result) (assembly-references rest))
         (equal (assembly-no-image-items-p result) (assembly-no-image-items-p rest))))
  :hints (("Goal" :induct (boymoo-compiler::gen-simple-args terms reg scope constants code)
                  :in-theory (disable assembly-simple-form-p boymoo-compiler::gen-simple))))

(defun assembly-routine-labels (name serial)
  (cond ((member-equal name '("COMMON-LISP::CAR" "COMMON-LISP::CDR"))
         (list (boymoo-compiler::gen-local serial)))
        ((equal name "COMMON-LISP::EQUAL")
         (list (boymoo-compiler::gen-local (+ serial 2))
               (boymoo-compiler::gen-local (+ serial 1))
               (boymoo-compiler::gen-local serial)))
        ((member-equal name '("ACL2::BINARY-+" "ACL2::UNARY--" "COMMON-LISP::<"))
         (list (boymoo-compiler::gen-local (+ serial 1))
               (boymoo-compiler::gen-local serial)))
        (t nil)))

(defun assembly-routine-references (name label serial)
  (cond ((member-equal name '("COMMON-LISP::CAR" "COMMON-LISP::CDR"))
         (list (boymoo-compiler::gen-local serial)))
        ((equal name "COMMON-LISP::CONSP") nil)
        ((equal name "COMMON-LISP::EQUAL")
         (let ((done (boymoo-compiler::gen-local (+ serial 2)))
               (no (boymoo-compiler::gen-local (+ serial 1)))
               (yes (boymoo-compiler::gen-local serial)))
           (list done done "prim:COMMON-LISP::EQUAL" no no no yes)))
        ((member-equal name '("ACL2::BINARY-+" "ACL2::UNARY--" "COMMON-LISP::<"))
         (let ((done (boymoo-compiler::gen-local (+ serial 1)))
               (slow (boymoo-compiler::gen-local serial)))
           (if (equal name "COMMON-LISP::<")
               (list label done slow)
             (list label done slow slow))))
        (t (list label))))

(local
 (defthm assembly-mv-nth-zero-is-car
   (equal (mv-nth 0 value) (car value))))

(defthm assembly-projections-of-gen-routine
  (let ((result (mv-nth 0 (boymoo-compiler::gen-routine name label serial code))))
    (and (equal (assembly-label-names result)
                (append (assembly-routine-labels name serial) (assembly-label-names code)))
         (equal (assembly-references result)
                (append (assembly-routine-references name label serial) (assembly-references code)))
         (equal (assembly-no-image-items-p result) (assembly-no-image-items-p code)))))

(defthm assembly-projections-of-gen-prologue
  (let ((result (boymoo-compiler::gen-prologue arity high serial code)))
    (and (equal (assembly-label-names result)
                (if (< arity high)
                    (list* (boymoo-compiler::gen-local (+ serial 1))
                           (boymoo-compiler::gen-local serial)
                           (assembly-label-names code))
                  (cons (boymoo-compiler::gen-local serial) (assembly-label-names code))))
         (equal (assembly-references result)
                (if (< arity high)
                    (list* "rt:grow" (boymoo-compiler::gen-local (+ serial 1))
                           "rt:deep" (boymoo-compiler::gen-local serial) (assembly-references code))
                  (list* "rt:deep" (boymoo-compiler::gen-local serial) (assembly-references code))))
         (equal (assembly-no-image-items-p result) (assembly-no-image-items-p code)))))
