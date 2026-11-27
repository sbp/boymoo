(in-package "BOYMOO-PROOFS")

(include-book "generator-emission")

(logic)
(set-verify-guards-eagerness 0)

; A source tree counts one unit per cons and atom, plus the characters
; of its strings. A dotted string tail can contribute to LENGTH.
(defun assembly-source-tree-weight (tree)
  (if (consp tree)
      (+ 1 (assembly-source-tree-weight (car tree))
           (assembly-source-tree-weight (cdr tree)))
    (+ 1 (if (stringp tree) (length tree) 0))))

(local (in-theory (disable length ash boymoo-compiler::low-bits)))

(local
 (defthm assembly-source-tree-positive-weight
   (posp (assembly-source-tree-weight tree))
   :rule-classes :type-prescription))

(local
 (defthm assembly-source-tree-weight-covers-length
   (< (length tree) (assembly-source-tree-weight tree))
   :hints (("Goal" :induct (assembly-source-tree-weight tree)
                   :in-theory (enable length)))
   :rule-classes :linear))

(local
 (defthm assembly-length-of-cons-upper-bound
   (<= (length (cons first rest)) (+ 1 (length rest)))
   :hints (("Goal" :in-theory (enable length)))
   :rule-classes :linear))

(local
 (defthm assembly-length-is-natural
   (natp (length value))
   :hints (("Goal" :in-theory (enable length)))
   :rule-classes :type-prescription))

(local
 (defthm assembly-size-of-ordinary-code-is-natural
   (implies (assembly-no-image-items-p code)
            (and (integerp (assembly-size code))
                 (<= 0 (assembly-size code))))
   :hints (("Goal" :use ((:instance assembly-word-offset-of-image-free-size (items code)))
                   :in-theory (disable assembly-size assembly-no-image-items-p
                                       assembly-word-offset-of-image-free-size
                                       assembly-word-offset-of-ordinary-item-size)))
   :rule-classes ((:type-prescription
                   :corollary (implies (assembly-no-image-items-p code)
                                       (natp (assembly-size code))))
                  (:linear
                   :corollary (implies (assembly-no-image-items-p code)
                                       (<= 0 (assembly-size code)))))))

(local
 (defthm assembly-generator-emit-size
   (equal (assembly-size (boymoo-compiler::gen-emit prefix code))
          (+ (assembly-size prefix) (assembly-size code)))))

(local
 (defthm assembly-generator-emit-no-images
   (equal (assembly-no-image-items-p (boymoo-compiler::gen-emit prefix code))
          (and (assembly-no-image-items-p prefix) (assembly-no-image-items-p code)))))

(local (in-theory (disable boymoo-compiler::gen-emit boymoo-compiler::reverse-onto)))

(local
 (defthm assembly-generator-load-high-size
   (implies (member-equal shift '(16 32 48 64))
            (<= (assembly-size (boymoo-compiler::gen-load-high rd n shift code))
                (+ (assembly-size code) (* 1/4 (- 64 shift)))))
   :hints (("Goal" :induct (boymoo-compiler::gen-load-high rd n shift code)))
   :rule-classes :linear))

(local (in-theory (disable boymoo-compiler::gen-load-high)))

(local
 (defthm assembly-generator-load-word-size
   (<= (assembly-size (boymoo-compiler::gen-load-word rd word code))
       (+ (assembly-size code) 16))
   :rule-classes :linear))

(local
 (defthm assembly-generator-load-datum-size
   (<= (assembly-size (boymoo-compiler::gen-load-datum rd datum code))
       (+ (assembly-size code) 16))
   :rule-classes :linear))

(local (in-theory (disable boymoo-compiler::gen-load-word boymoo-compiler::gen-load-datum)))

(local
 (defthm assembly-generator-address-size
   (<= (assembly-size (boymoo-compiler::gen-address rd rn bytes subtract code))
       (+ (assembly-size code) 20))
   :rule-classes :linear))

(local
 (defthm assembly-generator-frame-word-size
   (<= (assembly-size (boymoo-compiler::gen-frame-word rd slot code))
       (+ (assembly-size code) 20))
   :rule-classes :linear))

(local (in-theory (disable boymoo-compiler::gen-address boymoo-compiler::gen-frame-word)))

(local
 (defthm assembly-generator-drop-size
   (<= (assembly-size (boymoo-compiler::gen-drop count code))
       (+ (assembly-size code) 20))
   :rule-classes :linear))

(local
 (defthm assembly-generator-finish-size
   (equal (assembly-size (boymoo-compiler::gen-finish tail code))
          (+ (assembly-size code) (if tail 12 0)))))

(local
 (defthm assembly-generator-push-size
   (equal (assembly-size (boymoo-compiler::gen-push code))
          (+ (assembly-size code) 8))))

(local
 (defthm assembly-generator-simple-size
   (implies (assembly-no-image-items-p code)
            (<= (assembly-size (boymoo-compiler::gen-simple term rd scope constants code))
                (+ (assembly-size code) 20)))
   :hints (("Goal" :in-theory (disable boymoo-compiler::gen-datum boymoo-compiler::gen-slot)))
   :rule-classes :linear))

(local (in-theory (disable boymoo-compiler::gen-simple)))

(local
 (defthm assembly-generator-simple-args-size
   (implies (assembly-no-image-items-p code)
            (<= (assembly-size (boymoo-compiler::gen-simple-args terms reg scope constants code))
                (+ (assembly-size code) (* 20 (len terms)))))
   :hints (("Goal" :induct (boymoo-compiler::gen-simple-args terms reg scope constants code)
                   :in-theory (disable assembly-simple-form-p)))
   :rule-classes :linear))

(local
 (defthm assembly-generator-argument-registers-size
   (<= (assembly-size (boymoo-compiler::gen-argument-registers remaining slot reg code))
       (+ (assembly-size code) (* 20 (nfix remaining))))
   :hints (("Goal" :induct (boymoo-compiler::gen-argument-registers remaining slot reg code)))
   :rule-classes :linear))

(local
 (defthm assembly-generator-copy-arguments-size
   (<= (assembly-size (boymoo-compiler::gen-copy-arguments remaining offset code))
       (+ (assembly-size code) (* 24 (nfix remaining))))
   :hints (("Goal" :induct (boymoo-compiler::gen-copy-arguments remaining offset code)))
   :rule-classes :linear))

(local (in-theory (disable boymoo-compiler::gen-copy-arguments)))

(local
 (defthm assembly-generator-defined-call-size
   (<= (assembly-size (boymoo-compiler::gen-defined-call name arity tail code))
       (+ (assembly-size code) 48 (* 24 (nfix arity))))
   :rule-classes :linear))

(local
 (defthm assembly-generator-routine-size
   (<= (assembly-size (mv-nth 0 (boymoo-compiler::gen-routine name label serial code)))
       (+ (assembly-size code) 64))
   :rule-classes :linear))

(defthm assembly-generator-prologue-size
  (<= (assembly-size (boymoo-compiler::gen-prologue arity high serial code))
      (+ (assembly-size code) 72))
  :rule-classes :linear)

(local
 (defthm assembly-non-simple-source-term-is-cons
   (implies (not (boymoo-compiler::gen-simple-p term))
            (consp term))
   :rule-classes :forward-chaining))

(local
 (defthm assembly-gen-args-of-atom-returns-code
   (implies (atom args)
            (equal (mv-nth 0 (boymoo-compiler::gen-args args scope depth context code high serial))
                   code))))

(local (in-theory (disable boymoo-compiler::gen-term boymoo-compiler::gen-args
                           boymoo-compiler::gen-lambda-args boymoo-compiler::gen-simple-p
                           boymoo-compiler::gen-simple-args boymoo-compiler::gen-simple-args-p
                           boymoo-compiler::gen-mbe-p boymoo-compiler::gen-slot
                           boymoo-compiler::gen-datum boymoo-compiler::gen-argument-registers
                           boymoo-compiler::gen-defined-call boymoo-compiler::gen-call-info
                           boymoo-compiler::gen-routine boymoo-compiler::gen-prologue
                           boymoo-compiler::gen-car-cdr boymoo-compiler::gen-equal
                           boymoo-compiler::gen-arithmetic boymoo-compiler::gen-boolean
                           boymoo-compiler::gen-finish boymoo-compiler::gen-push
                           boymoo-compiler::gen-drop boymoo-compiler::bind-formal
                           boymoo-compiler::bind-formals boymoo-compiler::declaration-list
                           boymoo-compiler::index-get mv-nth assembly-simple-forms-p)))

(local
 (defthm assembly-generator-result-code
   (equal (mv-nth 0 (cons code rest)) code)))

(local
 (defthm assembly-len-bounded-by-length
   (<= (len xs) (length xs))
   :hints (("Goal" :in-theory (enable length)))
   :rule-classes :linear))

(local
 (defthm assembly-generator-result-size
   (let* ((result (assembly-generator-result kind term formals scope body-scope depth
                                              tail context code high serial))
          (out (mv-nth 0 result))
          (units (assembly-source-tree-weight term))
          (reserve (if (eq kind :term) 0 (* 32 (length term)))))
     (implies (assembly-no-image-items-p code)
              (and (assembly-no-image-items-p out)
                   (<= (assembly-size out)
                       (+ (assembly-size code) (* 128 units) (- reserve))))))
   :hints (("Goal"
            :induct (assembly-generator-induction kind term formals scope body-scope depth
                                                  tail context code high serial)
            :expand ((:free (scope depth tail context code high serial)
                            (boymoo-compiler::gen-term term scope depth tail context code high serial))
                     (:free (scope depth context code high serial)
                            (boymoo-compiler::gen-args term scope depth context code high serial))
                     (:free (formals scope body-scope depth context code high serial)
                            (boymoo-compiler::gen-lambda-args term formals scope body-scope depth
                                                             context code high serial)))))
   :rule-classes nil))

(defthm assembly-generation-size-from-source-tree
  (let ((out (mv-nth 0 (boymoo-compiler::gen-term term scope depth tail context code high serial))))
    (implies (assembly-no-image-items-p code)
             (and (assembly-no-image-items-p out)
                  (<= (assembly-size out)
                      (+ (assembly-size code) (* 128 (assembly-source-tree-weight term)))))))
  :hints (("Goal" :use ((:instance assembly-generator-result-size
                                   (kind :term) (formals nil) (body-scope nil)))))
  :rule-classes nil)
