(in-package "BOYMOO-PROOFS")

(include-book "generator-induction")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::gen-term boymoo-compiler::gen-args
                           boymoo-compiler::gen-lambda-args boymoo-compiler::gen-simple
                           boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple-args
                           boymoo-compiler::gen-simple-args-p boymoo-compiler::gen-frame-word
                           boymoo-compiler::gen-mbe-p boymoo-compiler::gen-slot
                           boymoo-compiler::gen-datum boymoo-compiler::gen-argument-registers
                           boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-defined-call
                           boymoo-compiler::gen-address boymoo-compiler::gen-load-high
                           boymoo-compiler::gen-load-word boymoo-compiler::gen-load-datum
                           boymoo-compiler::gen-car-cdr boymoo-compiler::gen-equal
                           boymoo-compiler::gen-arithmetic boymoo-compiler::gen-boolean
                           boymoo-compiler::gen-routine boymoo-compiler::gen-call-info
                           boymoo-compiler::gen-emit boymoo-compiler::gen-prologue
                           boymoo-compiler::bind-formal boymoo-compiler::bind-formals
                           boymoo-compiler::declaration-list boymoo-compiler::index-get
                           boymoo-compiler::a64-image-item-size
                           assembly-generator-tree-p assembly-constant-index-p
                           assembly-generator-value-p)))

(local
 (defthm assembly-fixed-fields-cons
   (equal (assembly-fixed-item-list-p (cons item code))
          (and (assembly-fixed-item-p item) (assembly-fixed-item-list-p code)))))

(local (in-theory (disable assembly-fixed-item-list-p)))

(local
 (defthm assembly-nil-datum-is-zero-in-logic
   (equal (boymoo-compiler::gen-load-datum rd nil code)
          (boymoo-compiler::gen-load-datum rd 0 code))
   :hints (("Goal" :in-theory (enable boymoo-compiler::gen-load-datum
                                     boymoo-compiler::gen-load-word
                                     boymoo-compiler::low-bits ash)))))

(local
 (defthm assembly-fixed-fields-of-load-looked-up-datum
   (implies (and (assembly-constant-index-p constants 12)
                 (assembly-fixed-item-list-p code))
            (assembly-fixed-item-list-p
             (boymoo-compiler::gen-load-datum 0 (boymoo-compiler::gen-datum text constants) code)))
   :hints (("Goal"
            :use (assembly-generator-value-of-gen-datum)
            :in-theory (e/d (assembly-generator-value-p)
                            (assembly-generator-value-of-gen-datum))))))

(local
 (defthm assembly-natural-generator-slot-value
   (implies (natp depth)
            (assembly-generator-value-p depth :slot))
   :hints (("Goal" :in-theory (enable assembly-generator-value-p)))))

(local
 (defthm assembly-natural-length
   (natp (length x))
   :rule-classes :type-prescription))

(local
 (defthm assembly-len-bounded-by-length
   (<= (len x) (length x))
   :rule-classes :linear))

(local
 (defthm assembly-result-component-of-cons
   (equal (mv-nth n (cons first rest))
          (if (zp n) first (mv-nth (1- n) rest)))))

(local (in-theory (disable mv-nth length boymoo-compiler::gen-finish
                           boymoo-compiler::gen-push boymoo-compiler::gen-drop)))

(local
 (defthm assembly-gen-routine-keeps-natural-serial
   (implies (natp serial)
            (natp (mv-nth 1 (boymoo-compiler::gen-routine name label serial code))))
   :hints (("Goal" :use (assembly-gen-routine-serial)))))

(local
 (defthm assembly-gen-routine-does-not-decrease-serial
   (implies (natp serial)
            (<= serial (mv-nth 1 (boymoo-compiler::gen-routine name label serial code))))
   :hints (("Goal" :use (assembly-gen-routine-serial)))
   :rule-classes :linear))

(local
 (defthm assembly-generator-invariants
   (let ((result (assembly-generator-result kind term formals scope body-scope depth
                                            tail context code high serial)))
     (implies (and (natp depth) (natp high) (natp serial)
                   (assembly-fixed-item-list-p code)
                   (assembly-generator-tree-p scope :slot)
                   (assembly-constant-index-p (caddr context) 12)
                   (implies (and (not (eq kind :term)) (not (eq kind :args)))
                            (assembly-generator-tree-p body-scope :slot)))
              (and (assembly-fixed-item-list-p (mv-nth 0 result))
                   (natp (mv-nth 1 result))
                   (natp (mv-nth 2 result))
                   (<= serial (mv-nth 2 result))
                   (implies (and (not (eq kind :term)) (not (eq kind :args)))
                            (and (natp (mv-nth 4 result))
                                 (<= depth (mv-nth 4 result))
                                 (assembly-generator-tree-p (mv-nth 3 result) :slot))))))
   :hints (("Goal"
            :induct (assembly-generator-induction kind term formals scope body-scope depth
                                                  tail context code high serial)
            :expand ((:free (scope depth tail context code high serial)
                            (boymoo-compiler::gen-term term scope depth tail context code high serial))
                     (:free (scope depth context code high serial)
                            (boymoo-compiler::gen-args term scope depth context code high serial))
                     (:free (formals scope body-scope depth context code high serial)
                            (boymoo-compiler::gen-lambda-args term formals scope body-scope depth
                                                             context code high serial))))
           ("Subgoal *1/8"
            :use ((:instance assembly-arity-of-gen-call-info-for-routine (head (car term)))))
           ("Subgoal *1/7"
            :use ((:instance assembly-arity-of-gen-call-info-for-routine (head (car term))))))
   :rule-classes nil))

(defthm assembly-fixed-fields-of-gen-term
  (mv-let (out out-high out-serial)
    (boymoo-compiler::gen-term term scope depth tail context code high serial)
    (implies (and (natp depth) (natp high) (natp serial)
                  (assembly-fixed-item-list-p code)
                  (assembly-generator-tree-p scope :slot)
                  (assembly-constant-index-p (caddr context) 12))
             (and (assembly-fixed-item-list-p out)
                  (natp out-high) (natp out-serial) (<= serial out-serial))))
  :hints (("Goal" :use ((:instance assembly-generator-invariants
                                   (kind :term) (formals nil) (body-scope nil)))))
  :rule-classes nil)

(defthm assembly-fixed-fields-of-gen-args
  (mv-let (out out-high out-serial)
    (boymoo-compiler::gen-args args scope depth context code high serial)
    (implies (and (natp depth) (natp high) (natp serial)
                  (assembly-fixed-item-list-p code)
                  (assembly-generator-tree-p scope :slot)
                  (assembly-constant-index-p (caddr context) 12))
             (and (assembly-fixed-item-list-p out)
                  (natp out-high) (natp out-serial) (<= serial out-serial))))
  :hints (("Goal" :use ((:instance assembly-generator-invariants
                                   (kind :args) (term args)
                                   (formals nil) (body-scope nil) (tail nil)))))
  :rule-classes nil)

(defthm assembly-fixed-fields-of-gen-lambda-args
  (mv-let (out out-high out-serial out-scope out-depth)
    (boymoo-compiler::gen-lambda-args args formals scope body-scope depth context code high serial)
    (implies (and (natp depth) (natp high) (natp serial)
                  (assembly-fixed-item-list-p code)
                  (assembly-generator-tree-p scope :slot)
                  (assembly-generator-tree-p body-scope :slot)
                  (assembly-constant-index-p (caddr context) 12))
             (and (assembly-fixed-item-list-p out)
                  (natp out-high) (natp out-serial) (<= serial out-serial)
                  (assembly-generator-tree-p out-scope :slot)
                  (natp out-depth) (<= depth out-depth))))
  :hints (("Goal" :use ((:instance assembly-generator-invariants
                                   (kind :lambda-args) (term args) (tail nil)))))
  :rule-classes nil)

(local
 (defthm assembly-empty-generator-scope
   (assembly-generator-tree-p nil :slot)))

(local
 (defthm assembly-fixed-fields-of-definition-body
   (let* ((formals (boymoo-compiler::declaration-list (cadr definition)))
          (arity (length formals))
          (scope (boymoo-compiler::bind-formals formals 0 nil)))
     (mv-let (out out-high out-serial)
       (boymoo-compiler::gen-term (caddr definition) scope arity t context nil arity (+ serial 2))
       (implies (and (natp serial) (assembly-constant-index-p (caddr context) 12))
                (and (assembly-fixed-item-list-p out)
                     (natp out-high) (natp out-serial)))))
   :hints (("Goal"
            :use ((:instance assembly-fixed-fields-of-gen-term
                             (term (caddr definition))
                             (scope (boymoo-compiler::bind-formals
                                     (boymoo-compiler::declaration-list (cadr definition)) 0 nil))
                             (depth (length (boymoo-compiler::declaration-list (cadr definition))))
                             (tail t) (code nil)
                             (high (length (boymoo-compiler::declaration-list (cadr definition))))
                             (serial (+ serial 2))))))
   :rule-classes nil))

(defthm assembly-generated-bodies-for-typed-constants
  (implies (and (natp serial) (true-listp defs) (string-listp (strip-cars defs))
                (assembly-constant-index-p (caddr context) 12))
           (assembly-generated-bodies-p defs context serial))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code))
           ("Subgoal *1/2" :use ((:instance assembly-fixed-fields-of-definition-body
                                           (definition (car defs))))))
  :rule-classes nil)

(defthm assembly-compile-items-fixed-fields-from-inputs
  (implies (and (true-listp defs) (string-listp (strip-cars defs))
                (assembly-constant-index-p (caddr context) 12)
                (proof-image-p data))
           (and (assembly-fixed-item-list-p
                 (boymoo-compiler::compile-items entry defs context data
                                                (boymoo-compiler::linux-system-code)))
                (assembly-fixed-item-list-p
                 (boymoo-compiler::compile-items entry defs context data
                                                (boymoo-compiler::system-code)))))
  :hints (("Goal"
           :use (assembly-fixed-fields-of-system-and-runtime
                 (:instance assembly-generated-bodies-for-typed-constants (serial 0)))
           :in-theory (disable boymoo-compiler::compile-items boymoo-compiler::linux-system-code
                               boymoo-compiler::system-code assembly-generated-bodies-p
                               (:executable-counterpart boymoo-compiler::linux-system-code)
                               (:executable-counterpart boymoo-compiler::system-code))))
  :rule-classes nil)
