(in-package "BOYMOO-PROOFS")

(include-book "views")
(include-book "lists")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-pointer-address proof-word-tag proof-load-word proof-span-p
                     proof-value-p proof-view proof-view-step proof-header-type proof-header-size
                     data-word-visible-at-rank-p evenp ash floor mod)))

(defun data-slot-views-p (views address depth base objects packages machine)
  (if (atom views)
      (null views)
    (let ((word (proof-load-word address machine)))
      (and (car views) (data-word-visible-at-rank-p word depth base objects)
           (equal (proof-view word base objects packages machine) (car views))
           (data-slot-views-p (cdr views) (+ address 8) depth base objects packages machine)))))

(local
 (defun slot-view-induction (views address)
   (if (atom views) address (slot-view-induction (cdr views) (+ 8 address)))))

(defthmd data-view-slots-have-the-stated-views
  (implies (data-slot-views-p views address depth base objects packages machine)
           (equal (proof-view-step :slots address (len views) depth base objects packages machine)
                  (cons :slots views)))
  :hints (("Goal" :induct (slot-view-induction views address)
                  :in-theory (enable data-view-at-greater-rank)
                  :expand ((:free (count)
                                  (proof-view-step :slots address count depth base objects packages machine))))))

(local
 (defthm vector-payload-has-whole-words
   (implies (natp count)
            (and (equal (mod (* 8 count) 8) 0)
                 (equal (ash (* 8 count) -3) count)))
   :hints (("Goal" :use ((:instance data-floor-unique (x (* 8 count)) (d 8) (q count)))
                   :in-theory (enable data-ash-right mod)))))

(defthmd data-view-of-static-vector-fields
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (rank (proof-object-rank object))
         (size (* 8 (len fields))))
    (implies (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                  object (natp rank) (eq (proof-object-kind object) :header)
                  (proof-span-p address (+ 8 size))
                  (equal (proof-load-word address machine) (+ 6 (* 256 size)))
                  (data-slot-views-p fields (+ address 8) rank base objects packages machine))
             (equal (proof-view word base objects packages machine) (cons :vector fields))))
  :hints (("Goal" :use ((:instance data-header-type-and-size (type 6) (size (* 8 (len fields))))
                       (:instance data-view-slots-have-the-stated-views
                                  (views fields) (address (+ 8 (proof-pointer-address word base)))
                                  (depth (proof-object-rank (assoc-equal (proof-pointer-address word base)
                                                                          objects)))))
                  :in-theory (disable data-slot-views-p proof-symbol-value proof-rational-value
                                      proof-complex-value proof-integer-view proof-load-string)
                  :expand ((proof-view word base objects packages machine)
                           (:free (depth)
                                  (proof-view-step :word word 0 depth base objects packages machine))))))

; Values and words are in allocation order, from the last car of the
; source list to the first. Each allocation points to the preceding tail.
(defun data-list-cell-view-layout-p (words values tail offset base objects packages machine)
  (if (atom words)
      (and (null words) (null values))
    (let* ((address (proof-pointer-address offset base))
           (object (assoc-equal address objects))
           (rank (proof-object-rank object)))
      (and (consp values) (unsigned-byte-p 64 offset) (not (oddp offset))
           (equal (proof-word-tag offset) 0)
           object (posp rank) (eq (proof-object-kind object) :cons) (proof-span-p address 16)
           (equal (proof-load-word address machine) (proof-constant-word (car words)))
           (equal (proof-load-word (+ address 8) machine) (proof-constant-word tail))
           (data-child-value-p (proof-load-word address machine) (car values) rank
                               base objects packages machine)
           (data-word-visible-at-rank-p (proof-load-word (+ address 8) machine) rank base objects)
           (data-list-cell-view-layout-p (cdr words) (cdr values) offset (+ 16 offset)
                                         base objects packages machine)))))

(local
 (defun list-cell-view-induction (words values tail tail-value block)
   (if (atom words)
       (list values tail tail-value block)
     (mv-let (cell next) (boymoo-compiler::data-cell (car words) tail block)
       (list-cell-view-induction (cdr words) (cdr values) cell (cons (car values) tail-value) next)))))

(local
 (defthm word-of-unsigned-reference
   (implies (unsigned-byte-p 64 word) (equal (proof-constant-word word) word))))

(local
 (defthm empty-cell-allocation-returns-tail
   (implies (atom words)
            (equal (car (boymoo-compiler::data-list-cells words tail block)) tail))))

(defthmd data-view-of-static-list-cell-block
  (implies (and (integerp (car block))
                (data-list-cell-view-layout-p words values tail (car block) base objects packages machine)
                (proof-value-p (proof-constant-word tail) tail-value base objects packages machine))
           (proof-value-p (proof-constant-word (mv-nth 0 (boymoo-compiler::data-list-cells words tail block)))
                          (boymoo-compiler::reverse-onto values tail-value) base objects packages machine))
  :hints (("Goal" :induct (list-cell-view-induction words values tail tail-value block)
                  :in-theory (disable proof-constant-word data-list-cell-view-layout-p
                                      boymoo-compiler::data-list-cells)
                  :expand ((data-list-cell-view-layout-p words values tail (car block)
                                                         base objects packages machine)
                           (boymoo-compiler::data-list-cells words tail block)))
          ("Subgoal *1/2" :use ((:instance data-view-of-static-cons-fields
                                           (word (car block)) (first (car values)) (second tail-value))))))
