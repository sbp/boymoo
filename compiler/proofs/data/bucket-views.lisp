(in-package "BOYMOO-PROOFS")

(include-book "encoded-chunks")
(include-book "static-bounds")
(include-book "chunk-retention")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-view proof-view-step proof-load-word proof-word-tag proof-pointer-address
                     boymoo-compiler::data-bucket-add boymoo-compiler::bucket-get
                     boymoo-compiler::low-bits evenp)))

(defthmd data-view-of-aligned-static-cons
  (let ((offset (* 8 slot)) (address (+ base (* 8 slot))))
    (implies (and (proof-span-p base size) (< size *proof-space-size*)
                  (posp slot) (<= (+ 16 offset) size)
                  (equal (assoc-equal address objects) (proof-object address :static :cons slot))
                  (data-child-value-p (proof-load-word address machine) first slot base objects packages machine)
                  (data-child-value-p (proof-load-word (+ 8 address) machine) rest slot base objects packages machine))
             (proof-value-p offset (cons first rest) base objects packages machine)))
  :hints (("Goal" :use ((:instance data-static-reference-fits-and-points-at-offset (tag 0))
                        (:instance data-view-of-static-cons-fields (word (* 8 slot)) (second rest)))
                  :in-theory (disable data-child-value-p proof-value-p))))

(defthmd data-aligned-static-cons-is-visible-at-larger-rank
  (let* ((word (* 8 slot)) (address (+ base word)))
    (implies (and (proof-span-p base size) (< size *proof-space-size*) (natp slot) (< word size)
                  (posp parent) (< slot parent)
                  (equal (assoc-equal address objects) (proof-object address :static :cons slot)))
             (data-word-visible-at-rank-p word parent base objects)))
  :hints (("Goal" :use ((:instance data-static-reference-fits-and-points-at-offset (tag 0))))))

(defun data-bucket-cell-records-p (slot base objects)
  (let* ((key (+ base (* 8 slot))) (entry (+ 16 key)) (head (+ 32 key)))
    (and (equal (assoc-equal key objects) (proof-object key :static :cons slot))
         (equal (assoc-equal entry objects) (proof-object entry :static :cons (+ 2 slot)))
         (equal (assoc-equal head objects) (proof-object head :static :cons (+ 4 slot))))))

(defun data-bucket-cell-words (slot number name-word symbol-word old-head)
  (let ((key (* 8 slot)))
    (list (+ 1 (* 2 number)) name-word key symbol-word (+ 16 key) old-head)))

(local
 (defthm nonnegative-immediate-is-a-visible-child
   (implies (and (natp number) (proof-immediate-integer-p number) (posp rank))
            (data-child-value-p (+ 1 (* 2 number)) number rank base objects packages machine))
   :hints (("Goal" :use ((:instance data-immediate-integer-twos-complement (integer number))
                         (:instance data-immediate-integer-word-is-odd (integer number))
                         (:instance data-view-of-immediate-integer (integer number)))
                   :in-theory (disable data-immediate-integer-word-is-odd proof-immediate-integer-p
                                       proof-integer-word)))))

(local
 (defthm static-span-start-is-an-integer
   (implies (proof-span-p base size) (integerp base))
   :rule-classes :forward-chaining))

(local
 (in-theory (disable data-child-value-p data-word-visible-at-rank-p proof-value-p
                     proof-span-p proof-immediate-integer-p)))

(local
 (defthm placed-key-cell-has-key-view
   (let ((address (+ base (* 8 slot))))
     (implies (and (proof-span-p base size) (< size *proof-space-size*) (posp slot)
                   (<= (+ 16 (* 8 slot)) size) (natp number) (proof-immediate-integer-p number)
                   (equal (assoc-equal address objects) (proof-object address :static :cons slot))
                   (equal (proof-load-word address machine) (+ 1 (* 2 number)))
                   (data-child-value-p (proof-load-word (+ 8 address) machine) name slot
                                       base objects packages machine))
              (proof-value-p (* 8 slot) (cons number name) base objects packages machine)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-view-of-aligned-static-cons (first number) (rest name)))))))

(local
 (defthm placed-cons-with-earlier-cons-has-value
   (let ((address (+ base (* 8 slot))) (earlier-address (+ base (* 8 earlier))))
     (implies (and (proof-span-p base size) (< size *proof-space-size*) (natp earlier) (posp slot)
                   (< earlier slot) (<= (+ 16 (* 8 slot)) size)
                   (equal (assoc-equal address objects) (proof-object address :static :cons slot))
                   (equal (assoc-equal earlier-address objects) (proof-object earlier-address :static :cons earlier))
                   (equal (proof-load-word address machine) (* 8 earlier))
                   (proof-value-p (* 8 earlier) first base objects packages machine)
                   (data-child-value-p (proof-load-word (+ 8 address) machine) rest slot
                                       base objects packages machine))
              (proof-value-p (* 8 slot) (cons first rest) base objects packages machine)))
   :rule-classes nil
   :hints (("Goal" :use (data-view-of-aligned-static-cons
                         (:instance data-aligned-static-cons-is-visible-at-larger-rank
                                    (slot earlier) (parent slot)))
                   :in-theory (enable data-child-value-p)))))

(defthmd data-view-of-placed-bucket-cells
  (let ((words (data-bucket-cell-words slot number name-word symbol-word old-head)))
    (implies (and (proof-span-p base size) (< size *proof-space-size*) (posp slot)
                  (<= (+ 48 (* 8 slot)) size) (natp number) (proof-immediate-integer-p number)
                  (data-u64-word-list-p words)
                  (data-placed-characters-p (data-forward-chunk-characters words) (+ base (* 8 slot)) machine)
                  (data-bucket-cell-records-p slot base objects)
                  (data-child-value-p name-word name slot base objects packages machine)
                  (data-child-value-p symbol-word symbol (+ 2 slot) base objects packages machine)
                  (data-child-value-p old-head entries (+ 4 slot) base objects packages machine))
             (proof-value-p (+ 32 (* 8 slot)) (cons (cons (cons number name) symbol) entries)
                            base objects packages machine)))
  :hints (("Goal" :use ((:instance data-placed-u64-chunks-load-their-words
                                   (words (data-bucket-cell-words slot number name-word symbol-word old-head))
                                   (address (+ base (* 8 slot))))
                        placed-key-cell-has-key-view
                        (:instance placed-cons-with-earlier-cons-has-value
                                   (slot (+ 2 slot)) (earlier slot) (first (cons number name)) (rest symbol))
                        (:instance placed-cons-with-earlier-cons-has-value
                                   (slot (+ 4 slot)) (earlier (+ 2 slot))
                                   (first (cons (cons number name) symbol)) (rest entries)))
                  :in-theory (disable data-placed-characters-p
                                      data-forward-chunk-characters data-u64-word-list-p))))

(local
 (defthm bucket-lookup-path-matches-itself
   (data-bucket-same-path-p bucket bucket bits)))

(defthmd data-bucket-add-selects-new-head
  (let* ((bucket (data-bucket-for-name number name))
         (offset (car (boymoo-compiler::data-block state-data)))
         (next (boymoo-compiler::data-bucket-add number name name-word symbol-word state-data)))
    (implies (natp offset)
             (equal (boymoo-compiler::bucket-get bucket 12 (caddr next)) (+ 32 offset))))
  :hints (("Goal" :in-theory (e/d (data-bucket-add-publishes-three-cells)
                                 (data-bucket-same-path-p data-bucket-for-name boymoo-compiler::bucket-set)))))

(defthmd data-bucket-add-placed-head-view
  (let* ((block (boymoo-compiler::data-block state-data))
         (bucket (data-bucket-for-name number name))
         (old-head (boymoo-compiler::bucket-get bucket 12 (caddr state-data)))
         (next (boymoo-compiler::data-bucket-add number name name-word symbol-word state-data))
         (head (boymoo-compiler::bucket-get bucket 12 (caddr next))))
    (implies (and (proof-span-p base size) (< size *proof-space-size*) (posp slot)
                  (equal (car block) (* 8 slot)) (<= (+ 48 (* 8 slot)) size) (data-block-sized-p block 80)
                  (natp number) (proof-immediate-integer-p number)
                  (data-u64-word-list-p (data-bucket-cell-words slot number name-word symbol-word old-head))
                  (data-state-retains-chunks-p (cdr (boymoo-compiler::data-block next)) final-state)
                  (data-placed-characters-p (data-chunks-characters (cdr (boymoo-compiler::data-block final-state)))
                                            (+ base 80) machine)
                  (data-bucket-cell-records-p slot base objects)
                  (data-child-value-p name-word name slot base objects packages machine)
                  (data-child-value-p symbol-word symbol (+ 2 slot) base objects packages machine)
                  (data-child-value-p old-head entries (+ 4 slot) base objects packages machine))
             (proof-value-p head (cons (cons (cons number name) symbol) entries) base objects packages machine)))
  :hints (("Goal" :use ((:instance data-bucket-add-publishes-three-cells (package number))
                        (:instance data-view-of-placed-bucket-cells
                                   (old-head (boymoo-compiler::bucket-get
                                              (data-bucket-for-name number name) 12 (caddr state-data))))
                        (:instance data-placed-retained-builder-allocation
                                   (before (boymoo-compiler::data-block state-data))
                                   (body (cdr (boymoo-compiler::data-block final-state)))
                                   (allocated (data-bucket-cell-words
                                               slot number name-word symbol-word
                                               (boymoo-compiler::bucket-get
                                                (data-bucket-for-name number name) 12 (caddr state-data))))))
                  :in-theory (e/d (data-bucket-add-selects-new-head)
                                 (data-bucket-add-publishes-three-cells data-bucket-for-name data-retained-chunks-p
                                  data-placed-characters-p data-chunks-characters data-forward-chunk-characters
                                  data-block-sized-p data-child-value-p data-bucket-cell-records-p
                                  proof-value-p proof-span-p proof-immediate-integer-p data-u64-word-list-p)))))

(defthmd data-inserting-a-fresh-static-bucket-binding
  (let ((key (cons number name)))
    (implies (and (natp number) (< number (len packages)) (stringp name) (symbolp symbol)
                  (equal (proof-symbol-hash number name 12) bucket)
                  (equal symbol (intern-in-package-of-symbol name (proof-package-witness (nth number packages))))
                  (not (assoc-equal key entries)) (proof-static-bucket-p entries bucket packages))
             (let ((next (cons (cons key symbol) entries)))
               (and (proof-static-bucket-p next bucket packages)
                    (equal (assoc-equal query next)
                           (if (equal query key) (cons key symbol) (assoc-equal query entries)))))))
  :hints (("Goal" :in-theory (disable proof-symbol-hash))))
