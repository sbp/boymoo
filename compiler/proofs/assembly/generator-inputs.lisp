(in-package "BOYMOO-PROOFS")

(include-book "generated-fields")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-generator-value-p (value kind)
  (case kind
    (:slot (or (null value) (natp value)))
    (:static-name
     (and (not (stringp value))
          (not (stringp (cdr value)))
          (or (eq (car value) :import)
              (null (car value))
              (integerp (car value)))))
    (:static-declaration (not (stringp (cadr value))))
    (otherwise
     (or (null value) (integerp (if (consp value) (cdr value) value))))))

(defun assembly-generator-tree-p (tree kind)
  (if (atom tree)
      t
    (and (assembly-generator-value-p (cddar tree) kind)
         (assembly-generator-tree-p (cadr tree) kind)
         (assembly-generator-tree-p (cddr tree) kind))))

(defun assembly-generator-index-p (index bits kind)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom index) t)
        ((zp bits) (assembly-generator-tree-p index kind))
        (t (and (assembly-generator-index-p (car index) (1- bits) kind)
                (assembly-generator-index-p (cdr index) (1- bits) kind)))))

(defun assembly-constant-index-p (index bits)
  (assembly-generator-index-p index bits :datum))

(local (in-theory (disable boymoo-compiler::table-key-less
                           boymoo-compiler::table-height
                           boymoo-compiler::variable-name-p
                           boymoo-compiler::text-hash
                           boymoo-compiler::low-bits ash)))

(defthm assembly-generator-value-of-tree-get
  (implies (assembly-generator-tree-p tree kind)
           (assembly-generator-value-p (boymoo-compiler::table-tree-get key tree) kind))
  :hints (("Goal" :induct (boymoo-compiler::table-tree-get key tree)))
  :rule-classes nil)

(defthm assembly-generator-value-of-index-get
  (implies (assembly-generator-index-p index bits kind)
           (assembly-generator-value-p (boymoo-compiler::table-get key hash bits index) kind))
  :hints (("Goal" :induct (boymoo-compiler::table-get key hash bits index)
                  :in-theory (disable boymoo-compiler::table-tree-get))
          ("Subgoal *1/2"
           :use ((:instance assembly-generator-value-of-tree-get (tree index)))))
  :rule-classes nil)

(defthm assembly-generator-value-of-gen-slot
  (implies (assembly-generator-tree-p scope :slot)
           (assembly-generator-value-p (boymoo-compiler::gen-slot name scope) :slot))
  :hints (("Goal" :use ((:instance assembly-generator-value-of-tree-get
                                   (tree scope) (kind :slot) (key name)))
                  :in-theory (disable boymoo-compiler::table-tree-get
                                      assembly-generator-value-p))))

(defthm assembly-generator-value-of-gen-datum
  (implies (assembly-constant-index-p constants 12)
           (assembly-generator-value-p (boymoo-compiler::gen-datum text constants) :datum))
  :hints (("Goal" :use ((:instance assembly-generator-value-of-index-get
                                   (index constants) (bits 12) (key text) (kind :datum)
                                   (hash (boymoo-compiler::text-hash text))))
                  :in-theory (disable boymoo-compiler::table-get assembly-generator-value-p))))

(local
 (defthm assembly-generator-children-and-entry
   (implies (assembly-generator-tree-p tree kind)
            (and (assembly-generator-value-p (cddar tree) kind)
                 (assembly-generator-tree-p (cadr tree) kind)
                 (assembly-generator-tree-p (cddr tree) kind)))))

(local
 (defthm assembly-generator-tree-node
   (implies (and (assembly-generator-value-p (cdr entry) kind)
                 (assembly-generator-tree-p left kind)
                 (assembly-generator-tree-p right kind))
            (assembly-generator-tree-p (boymoo-compiler::table-node entry left right) kind))))

(local
 (defthm assembly-generator-tree-of-atom
   (implies (atom tree)
            (assembly-generator-tree-p tree kind))))

(local (in-theory (disable boymoo-compiler::table-node
                           assembly-generator-tree-p
                           assembly-generator-value-p)))

(local
 (defthm assembly-generator-tree-rotate-left
   (implies (and (assembly-generator-value-p (cdr entry) kind)
                 (assembly-generator-tree-p left kind)
                 (assembly-generator-tree-p right kind))
            (assembly-generator-tree-p (boymoo-compiler::table-rotate-left entry left right) kind))))

(local
 (defthm assembly-generator-tree-rotate-right
   (implies (and (assembly-generator-value-p (cdr entry) kind)
                 (assembly-generator-tree-p left kind)
                 (assembly-generator-tree-p right kind))
            (assembly-generator-tree-p (boymoo-compiler::table-rotate-right entry left right) kind))))

(local
 (defthm assembly-generator-tree-balance
   (implies (and (assembly-generator-value-p (cdr entry) kind)
                 (assembly-generator-tree-p left kind)
                 (assembly-generator-tree-p right kind))
            (assembly-generator-tree-p (boymoo-compiler::table-balance entry left right) kind))
   :hints (("Goal" :in-theory (disable boymoo-compiler::table-rotate-left
                                       boymoo-compiler::table-rotate-right)))))

(local
 (defthm assembly-generator-tree-put
   (implies (and (assembly-generator-value-p value kind)
                 (assembly-generator-tree-p tree kind))
            (assembly-generator-tree-p (boymoo-compiler::table-tree-put key value tree) kind))
   :hints (("Goal" :induct (boymoo-compiler::table-tree-put key value tree)
                   :in-theory (disable boymoo-compiler::table-balance)))))

(defthm assembly-generator-index-of-table-put
  (implies (and (assembly-generator-value-p value kind)
                (assembly-generator-index-p index bits kind))
           (assembly-generator-index-p (boymoo-compiler::table-put key value hash bits index) bits kind))
  :hints (("Goal" :induct (boymoo-compiler::table-put key value hash bits index)
                  :in-theory (disable boymoo-compiler::table-tree-put))))

(defthm assembly-generator-slots-of-bind-formal
  (implies (and (assembly-generator-value-p slot :slot)
                (assembly-generator-tree-p scope :slot))
           (assembly-generator-tree-p (boymoo-compiler::bind-formal name slot scope) :slot))
  :hints (("Goal" :in-theory (disable boymoo-compiler::table-tree-get
                                      boymoo-compiler::table-tree-put))))

(defthm assembly-generator-slots-of-bind-formals
  (implies (and (natp slot) (assembly-generator-tree-p scope :slot))
           (assembly-generator-tree-p (boymoo-compiler::bind-formals formals slot scope) :slot))
  :hints (("Goal" :induct (boymoo-compiler::bind-formals formals slot scope)
                  :in-theory (e/d (assembly-generator-value-p) (boymoo-compiler::bind-formal)))))

(local
 (defthm assembly-nil-slot-is-zero-in-logic
   (equal (boymoo-compiler::gen-frame-word rd nil code)
          (boymoo-compiler::gen-frame-word rd 0 code))))

(local
 (defthm assembly-nil-datum-is-zero-in-logic
   (equal (boymoo-compiler::gen-load-datum rd nil code)
          (boymoo-compiler::gen-load-datum rd 0 code))
   :hints (("Goal" :in-theory (enable boymoo-compiler::low-bits ash)))))

(defthm assembly-fixed-fields-of-gen-simple-with-typed-lookups
  (implies (and (unsigned-byte-p 5 rd)
                (assembly-generator-tree-p scope :slot)
                (assembly-constant-index-p constants 12)
                (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p
            (boymoo-compiler::gen-simple term rd scope constants code)))
  :hints (("Goal"
           :use ((:instance assembly-generator-value-of-gen-slot (name term))
                 (:instance assembly-generator-value-of-gen-datum (text (cadr term))))
           :in-theory (e/d (assembly-generator-value-p)
                           (boymoo-compiler::gen-frame-word boymoo-compiler::gen-load-datum
                            boymoo-compiler::gen-slot boymoo-compiler::gen-datum
                            assembly-fixed-fields-of-gen-simple
                            assembly-generator-value-of-gen-slot assembly-generator-value-of-gen-datum)))))

(defthm assembly-fixed-fields-of-gen-simple-args
  (implies (and (natp reg) (<= (+ reg (len terms)) 32)
                (assembly-generator-tree-p scope :slot)
                (assembly-constant-index-p constants 12)
                (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p
            (boymoo-compiler::gen-simple-args terms reg scope constants code)))
  :hints (("Goal" :induct (boymoo-compiler::gen-simple-args terms reg scope constants code)
                  :in-theory (disable boymoo-compiler::gen-simple assembly-fixed-item-list-p))))

(local
 (defun assembly-routine-arities-p (entries)
   (if (atom entries)
       t
     (and (natp (cadar entries))
          (<= (cadar entries) 32)
          (assembly-routine-arities-p (cdr entries))))))

(local
 (defthm assembly-arity-of-lookup
   (implies (and (assembly-routine-arities-p entries)
                 (assoc-equal key entries))
            (and (natp (cadr (assoc-equal key entries)))
                 (<= (cadr (assoc-equal key entries)) 32)))))

(defthm assembly-arity-of-gen-call-info-for-routine
  (implies (mv-nth 2 (boymoo-compiler::gen-call-info head context))
           (let ((arity (mv-nth 1 (boymoo-compiler::gen-call-info head context))))
             (and (natp arity) (<= arity 32))))
  :hints (("Goal" :in-theory (disable assoc-equal boymoo-compiler::index-get
                                      assembly-routine-arities-p)))
  :rule-classes nil)

(defthm assembly-gen-routine-serial
  (implies (natp serial)
           (and (natp (mv-nth 1 (boymoo-compiler::gen-routine name label serial code)))
                (<= serial (mv-nth 1 (boymoo-compiler::gen-routine name label serial code)))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-car-cdr
                                      boymoo-compiler::gen-equal
                                      boymoo-compiler::gen-arithmetic
                                      boymoo-compiler::gen-boolean)))
  :rule-classes nil)
