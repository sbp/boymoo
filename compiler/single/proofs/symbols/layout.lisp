(in-package "BOYMOO-PROOFS")

(include-book "package-model")
(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm symbols-limb-magnitude-is-integer
   (integerp (proof-limb-magnitude count address machine))
   :rule-classes :type-prescription))

(local
 (defthm symbols-integer-view-is-integer
   (implies (proof-integer-view address machine)
            (integerp (proof-view-value (proof-integer-view address machine))))
   :hints (("Goal" :in-theory (disable proof-load-word proof-limbs-p
                                       proof-limb-magnitude proof-header-type
                                       proof-header-size ash)))))

(local
 (defthm symbols-integer-view-equality-implies-integer
   (implies (equal (proof-integer-view address machine) (proof-value-view datum))
            (integerp datum))
   :hints (("Goal"
            :use symbols-integer-view-is-integer
            :in-theory (disable proof-integer-view symbols-integer-view-is-integer)))))

(local
 (defthm symbols-symbol-tag-is-even
   (implies (and (integerp word) (equal (proof-word-tag word) 2))
            (evenp word))
   :hints (("Goal"
            :use ((:instance symbols-mod-of-nested-mod (x word) (factor 4) (divisor 2))
                  (:instance symbols-unsigned-as-mod (width 3) (x word)))
            :cases ((equal (* 1/2 word) (floor word 2)))
            :in-theory (disable boymoo-model::a64-unsigned floor
                                symbols-mod-of-nested-mod)))))

(defthm symbols-symbol-value-gives-name-and-home
  (let* ((name (proof-view-value name-view))
         (number (proof-view-value number-view))
         (package (nth number packages))
         (view (proof-symbol-value name-view number-view packages))
         (symbol (proof-view-value view)))
    (implies view
             (and (proof-value-view-p view)
                  (symbolp symbol)
                  (natp number) (< number (len packages))
                  (proof-immediate-integer-p number)
                  (equal (symbol-name symbol) name)
                  (equal (acl2::symbol-package-name symbol) (proof-package-name package))
                  (equal name-view (proof-value-view (symbol-name symbol)))
                  (equal number-view (proof-value-view number)))))
  :rule-classes nil)

(defthmd symbols-view-word-sufficient-rank
   (implies (proof-view-step :word word 0 depth base objects packages machine)
            (equal (proof-view-step :word word 0 depth base objects packages machine)
                   (proof-view word base objects packages machine)))
   :hints (("Goal"
            :expand ((:free (rank)
                            (proof-view-step :word word 0 rank base objects packages machine)))
            :in-theory (disable proof-view-step proof-symbol-value
                                proof-integer-view proof-load-word proof-limb-magnitude
                                proof-header-size proof-header-type proof-pointer-address
                                proof-word-tag proof-cons-value proof-rational-value
                                proof-complex-value proof-load-string ash mod
                                boymoo-model::a64-signed boymoo-model::a64-unsigned))))

(defthm symbols-only-symbols-have-symbol-headers
  (implies (proof-value-p word datum base objects packages machine)
           (iff (symbolp datum)
                (and (equal (proof-word-tag word) 2)
                     (equal (proof-header-type
                             (proof-load-word (proof-pointer-address word base) machine))
                            2))))
  :hints (("Goal"
           :expand ((:free (rank)
                           (proof-view-step :word word 0 rank base objects packages machine)))
           :use ((:instance symbols-symbol-tag-is-even)
                 (:instance symbols-integer-view-equality-implies-integer
                            (address (proof-pointer-address word base))))
           :in-theory (disable proof-view-step proof-integer-view proof-load-word
                               symbols-view-word-sufficient-rank
                               symbols-symbol-tag-is-even
                               symbols-integer-view-equality-implies-integer
                               proof-header-size proof-header-type proof-pointer-address
                               proof-word-tag proof-load-string ash mod
                               boymoo-model::a64-signed boymoo-model::a64-unsigned))))

(local
 (defthm symbols-unreadable-fields-have-no-symbol-view
   (and (equal (proof-symbol-value nil number packages) nil)
        (equal (proof-symbol-value name nil packages) nil))))

(local
 (defthm symbols-symbol-view-reads-two-fields
   (let* ((address (proof-pointer-address word base))
          (name-word (proof-load-word (+ address 8) machine))
          (package-word (proof-load-word (+ address 16) machine))
          (view (proof-view word base objects packages machine)))
     (implies (and (equal (proof-word-tag word) 2)
                   (equal (proof-header-type (proof-load-word address machine)) 2)
                   view)
              (equal view
                     (proof-symbol-value (proof-view name-word base objects packages machine)
                                         (proof-view package-word base objects packages machine)
                                         packages))))
   :hints (("Goal"
            :expand ((proof-view word base objects packages machine)
                     (:free (rank)
                            (proof-view-step :word word 0 rank base objects packages machine)))
            :use ((:instance symbols-symbol-tag-is-even)
                  (:instance symbols-view-word-sufficient-rank
                             (word (proof-load-word (+ (proof-pointer-address word base) 8)
                                                    machine))
                             (depth (proof-object-rank
                                     (assoc-equal (proof-pointer-address word base) objects))))
                  (:instance symbols-view-word-sufficient-rank
                             (word (proof-load-word (+ (proof-pointer-address word base) 16)
                                                    machine))
                             (depth (proof-object-rank
                                     (assoc-equal (proof-pointer-address word base) objects)))))
            :in-theory (disable proof-view proof-view-step proof-symbol-value
                                symbols-view-word-sufficient-rank
                                symbols-symbol-tag-is-even proof-load-word proof-pointer-address
                                proof-header-type proof-header-size proof-word-tag
                                ash mod floor boymoo-model::a64-unsigned)))
   :rule-classes nil))

(defthm symbols-published-symbol-fields
  (let* ((address (proof-pointer-address word base))
         (name-word (proof-load-word (+ address 8) machine))
         (package-word (proof-load-word (+ address 16) machine))
         (number (proof-view-value (proof-view package-word base objects packages machine))))
    (implies (and (proof-value-p word symbol base objects packages machine)
                  (symbolp symbol))
             (and (proof-value-p name-word (symbol-name symbol) base objects packages machine)
                  (proof-value-p package-word number base objects packages machine)
                  (natp number)
                  (proof-immediate-integer-p number)
                  (< number (len packages))
                  (equal (proof-package-name (nth number packages))
                         (acl2::symbol-package-name symbol)))))
  :hints (("Goal"
           :use ((:instance symbols-only-symbols-have-symbol-headers (datum symbol))
                 (:instance symbols-symbol-view-reads-two-fields)
                 (:instance symbols-symbol-value-gives-name-and-home
                            (name-view (proof-view
                                        (proof-load-word (+ (proof-pointer-address word base) 8)
                                                         machine)
                                        base objects packages machine))
                            (number-view (proof-view
                                          (proof-load-word (+ (proof-pointer-address word base) 16)
                                                           machine)
                                          base objects packages machine))))
           :in-theory (disable symbols-only-symbols-have-symbol-headers
                               proof-view proof-view-step proof-symbol-value
                               symbols-view-word-sufficient-rank
                               proof-pointer-address proof-header-type proof-load-word
                               proof-word-tag length)))
  :rule-classes nil)

(defthm symbols-represented-string-layout
  (let* ((address (proof-pointer-address word base))
         (header (proof-load-word address machine))
         (size (proof-header-size header)))
    (implies (proof-value-p word datum base objects packages machine)
             (and (iff (stringp datum)
                       (and (equal (proof-word-tag word) 2)
                            (equal (proof-header-type header) 1)))
                  (implies (stringp datum)
                           (and (proof-span-p address (+ 8 size))
                                (equal datum (proof-load-string size (+ address 8) machine)))))))
  :hints (("Goal"
           :expand ((:free (rank)
                           (proof-view-step :word word 0 rank base objects packages machine)))
           :use ((:instance symbols-symbol-tag-is-even)
                 (:instance symbols-integer-view-equality-implies-integer
                            (address (proof-pointer-address word base))))
           :in-theory (disable proof-view-step proof-integer-view proof-load-word
                               symbols-view-word-sufficient-rank
                               symbols-symbol-tag-is-even
                               symbols-integer-view-equality-implies-integer
                               proof-header-size proof-header-type proof-pointer-address
                               proof-word-tag proof-load-string proof-span-p ash mod
                               boymoo-model::a64-signed boymoo-model::a64-unsigned)))
  :rule-classes nil)

(local
 (defthm symbols-slot-view-starts-with-slots
   (let ((view (proof-view-step :slots address count depth base objects packages machine)))
     (implies view (equal (car view) :slots)))
   :hints (("Goal"
            :expand ((proof-view-step :slots address count depth base objects packages machine))
            :in-theory (disable proof-view-step)))))

(local
 (defthm symbols-integer-view-is-value
   (implies (proof-integer-view address machine)
            (equal (car (proof-integer-view address machine)) :value))
   :hints (("Goal" :in-theory (disable proof-load-word proof-limbs-p proof-limb-magnitude
                                       proof-header-type proof-header-size ash)))))

(defthm symbols-vector-view-shape
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects))
         (header (proof-load-word address machine))
         (size (proof-header-size header)))
    (implies (equal (proof-view word base objects packages machine) (cons :vector entries))
             (and (equal (proof-word-tag word) 2)
                  (eq (proof-object-kind object) :header)
                  (equal (proof-header-type header) 6)
                  (equal (mod size 8) 0)
                  (proof-span-p address (+ 8 size))
                  (equal (proof-view-step :slots (+ address 8) (ash size -3)
                                          (proof-object-rank object) base objects packages machine)
                         (cons :slots entries)))))
  :hints (("Goal"
           :expand ((proof-view word base objects packages machine)
                    (:free (depth)
                           (proof-view-step :word word 0 depth base objects packages machine)))
           :use ((:instance symbols-symbol-tag-is-even)
                 (:instance symbols-integer-view-is-value
                            (address (proof-pointer-address word base)))
                 (:instance symbols-slot-view-starts-with-slots
                            (address (+ 8 (proof-pointer-address word base)))
                            (count (ash (proof-header-size
                                         (proof-load-word (proof-pointer-address word base) machine)) -3))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))
           :in-theory (disable proof-view proof-view-step proof-integer-view proof-load-word
                               symbols-view-word-sufficient-rank symbols-symbol-tag-is-even
                               symbols-integer-view-is-value proof-load-string proof-span-p
                               proof-header-type proof-header-size proof-pointer-address proof-word-tag
                               ash mod boymoo-model::a64-signed boymoo-model::a64-unsigned)))
  :rule-classes nil)

(local
 (defun symbols-slot-offset-induction (address count index)
   (declare (xargs :measure (nfix count)))
   (if (or (zp count) (zp index))
       (cons address index)
     (symbols-slot-offset-induction (+ address 8) (1- count) (1- index)))))

(local
 (defthm symbols-slot-view-length
   (let ((view (proof-view-step :slots address count depth base objects packages machine)))
     (implies view (equal (len (cdr view)) (nfix count))))
   :hints (("Goal" :induct (symbols-slot-offset-induction address count count)
                   :expand ((proof-view-step :slots address count depth base objects packages machine))
                   :in-theory (disable proof-view-step proof-load-word symbols-view-word-sufficient-rank)))))

(local
 (defthm symbols-slot-index-gives-depth-view
   (let ((views (proof-view-step :slots address count depth base objects packages machine)))
     (implies (and views (natp count) (natp index) (< index count) (integerp address))
              (equal (nth index (cdr views))
                     (proof-view-step :word (proof-load-word (+ address (* 8 index)) machine)
                                      0 depth base objects packages machine))))
   :hints (("Goal" :induct (symbols-slot-offset-induction address count index)
                   :expand ((proof-view-step :slots address count depth base objects packages machine))
                   :in-theory (disable proof-view-step proof-load-word
                                       symbols-view-word-sufficient-rank)))
   :rule-classes nil))

(local
 (defthm symbols-slot-index-is-readable
   (let ((views (proof-view-step :slots address count depth base objects packages machine)))
     (implies (and views (natp count) (natp index) (< index count) (integerp address))
              (proof-view-step :word (proof-load-word (+ address (* 8 index)) machine)
                               0 depth base objects packages machine)))
   :hints (("Goal" :induct (symbols-slot-offset-induction address count index)
                   :expand ((proof-view-step :slots address count depth base objects packages machine))
                   :in-theory (disable proof-view-step proof-load-word
                                       symbols-view-word-sufficient-rank)))
   :rule-classes nil))

(local
 (defthm symbols-header-shifts-as-floors
   (and (equal (ash word -1) (floor (ifix word) 2))
        (equal (ash word -8) (floor (ifix word) 256))
        (equal (ash word -3) (floor (ifix word) 8)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm symbols-vector-length-matches-header
   (let* ((header (proof-load-word address machine))
          (size (proof-header-size header)))
     (implies (equal (mod size 8) 0)
              (and (natp (ash size -3)) (equal size (* 8 (ash size -3))))))
   :hints (("Goal"
            :use ((:instance symbols-load-width (count 8))
                  (:instance symbols-floor-bounds (x (proof-load-word address machine))
                             (divisor 256))
                  (:instance symbols-floor-bounds (x (proof-header-size (proof-load-word address machine)))
                             (divisor 8)))
            :in-theory (e/d (mod)
                            (boymoo-model::a64-load ash floor boymoo-model::a64-unsigned))))))

(defthm symbols-vector-view-reads-slot
  (let* ((address (proof-pointer-address word base))
         (header (proof-load-word address machine))
         (size (proof-header-size header))
         (slot (+ address 8 (* 8 index))))
    (implies (and (equal (proof-view word base objects packages machine) (cons :vector entries))
                  (natp index) (< index (len entries)))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type header) 6)
                  (equal size (* 8 (len entries)))
                  (equal (proof-view (proof-load-word slot machine) base objects packages machine)
                         (nth index entries)))))
  :hints (("Goal"
           :use ((:instance symbols-vector-view-shape)
                 (:instance symbols-vector-length-matches-header
                            (address (proof-pointer-address word base)))
                 (:instance symbols-slot-view-length
                            (address (+ 8 (proof-pointer-address word base)))
                            (count (ash (proof-header-size
                                         (proof-load-word (proof-pointer-address word base) machine)) -3))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance symbols-slot-index-gives-depth-view
                            (address (+ 8 (proof-pointer-address word base)))
                            (count (ash (proof-header-size
                                         (proof-load-word (proof-pointer-address word base) machine)) -3))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance symbols-slot-index-is-readable
                            (address (+ 8 (proof-pointer-address word base)))
                            (count (ash (proof-header-size
                                         (proof-load-word (proof-pointer-address word base) machine)) -3))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance symbols-view-word-sufficient-rank
                            (word (proof-load-word (+ (proof-pointer-address word base) 8 (* 8 index)) machine))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))
           :in-theory (disable proof-view proof-view-step proof-load-word proof-span-p
                               symbols-slot-view-length symbols-vector-length-matches-header
                               proof-header-type proof-header-size proof-pointer-address proof-word-tag
                               ash mod boymoo-model::a64-unsigned)))
  :rule-classes nil)

(local
 (defthm symbols-package-row-views-length
   (equal (len (proof-package-row-views packages)) (len packages))))

(local
 (defthm symbols-package-row-view-at-index
   (let ((row (nth number packages)))
     (implies (and (natp number) (< number (len packages)))
              (equal (nth number (proof-package-row-views packages))
                     (list :vector
                           (proof-value-view (proof-package-name row))
                           (proof-value-view (proof-package-imports row))
                           (proof-value-view (if (proof-package-visible row)
                                                 (proof-package-witness row) nil))))))))

(defun symbols-static-package-row-word (number base machine)
  (let* ((table-word (proof-load-word (+ base 8) machine))
         (address (proof-pointer-address table-word base)))
    (proof-load-word (+ address 8 (* 8 (nfix number))) machine)))

(defthm symbols-static-package-row-view
  (implies (and (proof-static-p base objects packages machine)
                (natp number) (< number (len packages)))
           (equal (proof-view (symbols-static-package-row-word number base machine)
                              base (proof-static-objects objects) packages machine)
                  (nth number (proof-package-row-views packages))))
  :hints (("Goal"
           :use ((:instance symbols-vector-view-reads-slot
                            (word (proof-load-word (+ base 8) machine))
                            (entries (proof-package-row-views packages))
                            (objects (proof-static-objects objects)) (index number)))
           :in-theory (disable proof-view proof-load-word proof-pointer-address proof-static-objects
                               proof-object-map-p proof-static-spans-p proof-home-bindings-p
                               proof-static-buckets-p proof-package-bindings-p proof-packages-p
                               proof-package-row-views proof-value-p)))
  :rule-classes nil)

(defthm symbols-static-package-row-fields
  (let* ((word (symbols-static-package-row-word number base machine))
         (address (proof-pointer-address word base))
         (statics (proof-static-objects objects))
         (row (nth number packages)))
    (implies (and (proof-static-p base objects packages machine)
                  (natp number) (< number (len packages)))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type (proof-load-word address machine)) 6)
                  (equal (proof-header-size (proof-load-word address machine)) 24)
                  (proof-value-p (proof-load-word (+ address 8) machine)
                                 (proof-package-name row) base statics packages machine)
                  (proof-value-p (proof-load-word (+ address 16) machine)
                                 (proof-package-imports row) base statics packages machine)
                  (proof-value-p (proof-load-word (+ address 24) machine)
                                 (if (proof-package-visible row) (proof-package-witness row) nil)
                                 base statics packages machine))))
  :hints (("Goal"
           :use ((:instance symbols-static-package-row-view)
                 (:instance symbols-vector-view-reads-slot
                            (word (symbols-static-package-row-word number base machine))
                            (entries (cdr (nth number (proof-package-row-views packages))))
                            (objects (proof-static-objects objects)) (index 0))
                 (:instance symbols-vector-view-reads-slot
                            (word (symbols-static-package-row-word number base machine))
                            (entries (cdr (nth number (proof-package-row-views packages))))
                            (objects (proof-static-objects objects)) (index 1))
                 (:instance symbols-vector-view-reads-slot
                            (word (symbols-static-package-row-word number base machine))
                            (entries (cdr (nth number (proof-package-row-views packages))))
                            (objects (proof-static-objects objects)) (index 2)))
           :in-theory (disable proof-view proof-load-word proof-pointer-address proof-static-objects
                               proof-static-p proof-header-size proof-header-type proof-word-tag
                               proof-package-row-views symbols-static-package-row-word)))
  :rule-classes nil)

(local
 (defthm symbols-assoc-object-has-address
   (implies (assoc-equal address objects)
            (and (equal (proof-object-address (assoc-equal address objects)) address)
                 (member-equal (assoc-equal address objects) objects)))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm symbols-box-pointer-round-trip
   (implies (and (integerp base) (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2))
            (equal (boymoo-model::a64-unsigned
                    64 (+ 2 (- (proof-pointer-address word base) base)))
                   word))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-sum-right
                             (width 64) (x (+ base (- word 2))) (y (+ 2 (- base)))))
            :in-theory (disable boymoo-model::a64-unsigned proof-word-tag)))))

(local
 (defthm symbols-boxed-view-has-header-record
   (let ((object (assoc-equal (proof-pointer-address word base) objects)))
     (implies (and (equal (proof-word-tag word) 2)
                   (proof-view word base objects packages machine))
              (and (unsigned-byte-p 64 word)
                   object
                   (eq (proof-object-kind object) :header))))
   :hints (("Goal"
            :use ((:instance symbols-symbol-tag-is-even))
            :expand ((proof-view word base objects packages machine)
                     (:free (depth) (proof-view-step :word word 0 depth base objects packages machine)))
            :in-theory (disable proof-view proof-view-step proof-load-word proof-object-kind
                                symbols-symbol-tag-is-even proof-symbol-value proof-pointer-address
                                proof-header-type proof-header-size proof-word-tag
                                proof-integer-view proof-cons-value proof-rational-value proof-complex-value
                                proof-span-p proof-load-string assoc-equal member-equal ash mod floor
                                boymoo-model::a64-signed boymoo-model::a64-unsigned)))
   :rule-classes nil))

(local
 (defthm symbols-represented-symbol-has-object
   (let* ((address (proof-pointer-address word base))
          (object (assoc-equal address objects)))
     (implies (and (integerp base) (symbolp symbol)
                   (proof-value-p word symbol base objects packages machine))
              (and (member-equal object objects)
                   (proof-symbol-object-p object machine)
                   (equal (proof-object-word object base) word)
                   (equal (proof-object-view object base objects packages machine)
                          (proof-value-view symbol)))))
   :hints (("Goal"
            :use ((:instance symbols-only-symbols-have-symbol-headers (datum symbol))
                  (:instance symbols-boxed-view-has-header-record)
                  (:instance symbols-box-pointer-round-trip)
                  (:instance symbols-assoc-object-has-address (address (proof-pointer-address word base))))
            :in-theory (disable proof-view proof-load-word proof-object-kind
                                symbols-only-symbols-have-symbol-headers
                                symbols-assoc-object-has-address symbols-box-pointer-round-trip
                                proof-pointer-address proof-header-type proof-header-size
                                proof-word-tag assoc-equal member-equal boymoo-model::a64-unsigned)))
   :rule-classes nil))

(local
 (defthm symbols-map-excludes-a-seen-symbol
   (implies (and (symbolp symbol)
                 (member-equal symbol seen)
                 (proof-object-map-p pending objects seen base packages machine)
                 (member-equal object pending)
                 (proof-symbol-object-p object machine)
                 (equal (proof-object-view object base objects packages machine)
                        (proof-value-view symbol)))
            nil)
   :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine)
                   :in-theory (disable proof-symbol-object-p proof-object-view proof-object-record-p
                                       proof-object-size proof-object-disjoint-p proof-span-p)))
   :rule-classes nil))

(local
 (defthm symbols-symbol-objects-in-map-are-unique
   (implies (and (symbolp symbol)
                 (proof-object-map-p pending objects seen base packages machine)
                 (member-equal first pending) (member-equal second pending)
                 (proof-symbol-object-p first machine) (proof-symbol-object-p second machine)
                 (equal (proof-object-view first base objects packages machine) (proof-value-view symbol))
                 (equal (proof-object-view second base objects packages machine) (proof-value-view symbol)))
            (equal first second))
   :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine)
                   :in-theory (disable proof-symbol-object-p proof-object-view proof-object-record-p
                                       proof-object-size proof-object-disjoint-p proof-span-p))
           ("Subgoal *1/2"
            :use ((:instance symbols-map-excludes-a-seen-symbol
                             (object first) (pending (cdr pending)) (seen (cons symbol seen)))
                  (:instance symbols-map-excludes-a-seen-symbol
                             (object second) (pending (cdr pending)) (seen (cons symbol seen))))
            :in-theory (disable proof-symbol-object-p proof-object-view proof-object-record-p
                                proof-object-size proof-object-disjoint-p proof-span-p)))
   :rule-classes nil))

(defthm symbols-canonical-symbol-word
  (implies (and (integerp base) (symbolp symbol)
                (proof-object-map-p objects objects nil base packages machine)
                (proof-value-p first symbol base objects packages machine)
                (proof-value-p second symbol base objects packages machine))
           (equal first second))
  :hints (("Goal"
           :use ((:instance symbols-represented-symbol-has-object (word first))
                 (:instance symbols-represented-symbol-has-object (word second))
                 (:instance symbols-symbol-objects-in-map-are-unique
                            (pending objects) (seen nil)
                            (first (assoc-equal (proof-pointer-address first base) objects))
                            (second (assoc-equal (proof-pointer-address second base) objects))))
           :in-theory (disable proof-object-view proof-object-word proof-pointer-address
                               proof-value-p proof-object-map-p proof-symbol-object-p
                               assoc-equal member-equal)))
  :rule-classes nil)

(local
 (defthm symbols-witness-of-numbered-row-is-non-nil
   (implies (and (proof-packages-p packages) (natp number) (< number (len packages)))
            (proof-package-witness (nth number packages)))
   :hints (("Goal" :induct (nth number packages) :in-theory (disable acl2::pkg-imports)))))

(defthm symbols-static-package-row-witness-tests-visibility
  (let* ((row-word (symbols-static-package-row-word number base machine))
         (row-address (proof-pointer-address row-word base))
         (witness-word (proof-load-word (+ row-address 24) machine))
         (row (nth number packages)))
    (implies (and (proof-static-p base objects packages machine)
                  (natp number) (< number (len packages)))
             (iff (equal witness-word *proof-nil*) (not (proof-package-visible row)))))
  :hints (("Goal"
           :use ((:instance symbols-static-package-row-fields)
                 (:instance symbols-witness-of-numbered-row-is-non-nil)
                 (:instance symbols-canonical-symbol-word
                            (symbol nil) (objects (proof-static-objects objects)) (second *proof-nil*)
                            (first (proof-load-word
                                    (+ (proof-pointer-address
                                        (symbols-static-package-row-word number base machine) base)
                                       24)
                                    machine))))
           :in-theory (disable proof-view proof-load-word proof-pointer-address proof-static-objects
                               proof-object-map-p proof-static-spans-p proof-home-bindings-p
                               proof-static-buckets-p proof-package-bindings-p proof-packages-p
                               proof-package-row-views symbols-static-package-row-word
                               symbols-witness-of-numbered-row-is-non-nil)))
  :rule-classes nil)

(local
 (defthm symbols-byte-characters-are-characters
   (character-listp (proof-byte-characters bytes))))

(local
 (defthm symbols-code-of-loaded-byte
   (equal (char-code (code-char (boymoo-model::a64-load 1 address machine)))
          (boymoo-model::a64-load 1 address machine))
   :hints (("Goal"
            :use ((:instance symbols-load-width (count 1)))
            :in-theory (disable boymoo-model::a64-load)))))

(local
 (defthm symbols-character-codes-of-loaded-bytes
   (equal (proof-string-bytes (proof-byte-characters (proof-byte-list count address machine)))
          (proof-byte-list count address machine))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (disable boymoo-model::a64-load)))))

(defthm symbols-loaded-string-has-span-bytes
  (equal (proof-string-bytes (coerce (proof-load-string count address machine) 'list))
         (proof-byte-list count address machine))
  :hints (("Goal"
           :use ((:instance acl2::coerce-inverse-1
                            (acl2::x (proof-byte-characters (proof-byte-list count address machine)))))
           :in-theory (disable proof-string-bytes proof-byte-characters proof-byte-list))))

(defthm symbols-byte-list-length
  (equal (len (proof-byte-list count address machine)) (nfix count))
  :hints (("Goal" :induct (proof-byte-list count address machine)
                  :in-theory (disable boymoo-model::a64-load))))

(local
 (defthm symbols-half-of-double
   (implies (rationalp half) (equal (* (* 2 half) 1/2) half))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm symbols-double-is-even
   (implies (integerp half) (not (oddp (* 2 half))))
   :hints (("Goal" :in-theory (disable commutativity-of-* associativity-of-*)))
   :rule-classes nil))

(local
 (defthm symbols-layout-integer-gap
   (implies (and (integerp x) (integerp y) (< x y))
            (<= (1+ x) y))
   :rule-classes nil))

(local
 (defthm symbols-odd-is-one-plus-double-half
   (implies (and (integerp word) (oddp word))
            (equal (+ 1 (* 2 (floor word 2))) word))
   :hints (("Goal"
            :cases ((equal word (* 2 (floor word 2))))
            :use ((:instance symbols-floor-bounds (x word) (divisor 2))
                  (:instance symbols-double-is-even (half (floor word 2)))
                  (:instance symbols-layout-integer-gap (x (* 2 (floor word 2))) (y word))
                  (:instance symbols-layout-integer-gap (x word) (y (+ 2 (* 2 (floor word 2))))))
            :in-theory (disable floor evenp oddp)))
   :rule-classes nil))

(local
 (defthm symbols-odd-signed-word-round-trip
   (implies (and (unsigned-byte-p 64 word) (oddp word))
            (equal (proof-integer-word (ash (boymoo-model::a64-signed 64 word) -1)) word))
   :hints (("Goal"
            :use ((:instance symbols-odd-is-one-plus-double-half)
                  (:instance symbols-floor-of-decomposition
                             (q (- (floor word 2) (expt 2 63))) (r 1) (divisor 2))
                  (:instance symbols-unsigned-translate-by-wider-modulus
                             (wide 64) (narrow 64) (x word) (multiple -1)))
            :in-theory (e/d (boymoo-model::a64-signed)
                            (boymoo-model::a64-unsigned floor ash oddp logbitp
                             symbols-floor-of-decomposition symbols-unsigned-translate-by-wider-modulus))))
   :rule-classes nil))

(local
 (defthm symbols-rational-view-has-nonintegral-value
   (implies (integerp number)
            (not (equal (proof-rational-value first second) (cons :value number))))))

(local
 (defthm symbols-complex-view-has-nonintegral-value
   (implies (integerp number)
            (not (equal (proof-complex-value first second) (cons :value number))))))

(defthm symbols-canonical-immediate-integer-word
  (implies (and (proof-immediate-integer-p number)
                (proof-value-p word number base objects packages machine))
           (equal word (proof-integer-word number)))
  :hints (("Goal"
           :expand ((:free (rank) (proof-view-step :word word 0 rank base objects packages machine)))
           :use ((:instance symbols-odd-signed-word-round-trip))
           :in-theory (disable proof-view-step proof-load-word proof-integer-view proof-integer-word
                               proof-word-tag proof-header-type proof-header-size proof-pointer-address
                               proof-span-p proof-load-string boymoo-model::a64-signed boymoo-model::a64-unsigned
                               proof-rational-value proof-complex-value floor ash mod)))
  :rule-classes nil)
