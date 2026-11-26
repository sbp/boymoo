(in-package "BOYMOO-PROOFS")

(include-book "intern")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-view proof-view-step proof-load-word proof-heap-base
                     proof-pointer-address proof-word-tag proof-object-map-p
                     boymoo-model::a64-unsigned symbols-load-register-word)))

(local
 (defthm symbols-chain-load-is-word
   (equal (symbols-load-register-word address world)
          (proof-load-word address (proof-world-machine world)))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word symbols-word-load-fits proof-load-word)
                                   (boymoo-model::a64-load))))))

(local
 (defthm symbols-chain-box-tag-is-integer
   (implies (equal (proof-word-tag word) 2) (integerp word))
   :hints (("Goal" :in-theory (enable proof-word-tag boymoo-model::a64-unsigned)))))

(defthm symbols-chain-payload-after-header
  (implies (and (integerp base) (equal (proof-word-tag word) 2)
                (< (+ 8 (proof-pointer-address word base)) (expt 2 64)))
           (equal (symbols-address-plus-word base (boymoo-model::a64-unsigned 64 (+ 6 word)))
                  (+ 8 (proof-pointer-address word base))))
  :hints (("Goal"
           :use ((:instance symbols-chain-box-tag-is-integer)
                 (:instance symbols-unsigned-sum-right (width 64) (x (+ 6 word)) (y base))
                 (:instance symbols-unsigned-sum-right (width 64) (x (+ base word -2)) (y 8)))
           :in-theory (e/d (proof-pointer-address)
                           (symbols-chain-box-tag-is-integer symbols-unsigned-sum-right)))))

(local
 (defthm symbols-chain-base-is-natural
   (natp (proof-heap-base world))
   :hints (("Goal" :in-theory (enable proof-heap-base)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-nonempty-dynamic-bucket-view-is-entry
   (implies (and (proof-dynamic-bucket view index count packages)
                 (not (equal view (proof-value-view nil))))
            (and (equal view (cons :vector (cdr view)))
                 (true-listp view) (equal (len (cdr view)) 3)))
   :hints (("Goal"
            :cases ((consp view))
            :expand ((proof-dynamic-bucket view index count packages))
            :in-theory (disable proof-dynamic-bucket proof-symbol-hash proof-package-number
                                acl2::binary-logand boymoo-model::a64-signed)))
   :rule-classes nil))

(defthm symbols-dynamic-entry-fields-agree
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (view (proof-view word base objects packages machine))
         (fields (symbols-intern-fields-at t word world)))
    (implies (and (proof-dynamic-bucket view index count packages)
                  (not (equal view (proof-value-view nil))))
             (and (equal (proof-view (car fields) base objects packages machine) (cadddr view))
                  (equal (proof-view (cadr fields) base objects packages machine) (cadr view))
                  (equal (proof-view (caddr fields) base objects packages machine) (caddr view)))))
  :hints (("Goal"
           :use ((:instance symbols-nonempty-dynamic-bucket-view-is-entry
                            (view (proof-view word (proof-heap-base world) objects packages (proof-world-machine world))))
                 (:instance symbols-vector-view-shape (base (proof-heap-base world))
                            (machine (proof-world-machine world))
                            (entries (cdr (proof-view word (proof-heap-base world) objects packages
                                                       (proof-world-machine world)))))
                 (:instance symbols-vector-view-reads-slot (base (proof-heap-base world))
                            (machine (proof-world-machine world)) (index 0)
                            (entries (cdr (proof-view word (proof-heap-base world) objects packages
                                                       (proof-world-machine world)))))
                 (:instance symbols-vector-view-reads-slot (base (proof-heap-base world))
                            (machine (proof-world-machine world)) (index 1)
                            (entries (cdr (proof-view word (proof-heap-base world) objects packages
                                                       (proof-world-machine world)))))
                 (:instance symbols-vector-view-reads-slot (base (proof-heap-base world))
                            (machine (proof-world-machine world)) (index 2)
                            (entries (cdr (proof-view word (proof-heap-base world) objects packages
                                                       (proof-world-machine world))))))
           :in-theory (disable proof-dynamic-bucket proof-symbol-hash proof-package-number
                               proof-world-machine proof-header-size proof-header-type
                               acl2::binary-logand boymoo-model::a64-signed symbols-address-plus-word ash floor)))
  :rule-classes nil)

(local
 (defun symbols-dynamic-view-and-link-induction (view word world)
   (if (consp (cdddr view))
       (symbols-dynamic-view-and-link-induction (cadddr view)
                                               (car (symbols-intern-fields-at t word world)) world)
     word)))

(local
 (defthm symbols-nil-bucket-has-length-zero
   (and (equal (proof-dynamic-bucket '(:value) index count packages) (list :entries))
        (symbols-intern-chain-length-p 0 t *proof-nil* world))))

(defthm symbols-nonempty-bucket-has-tail
  (let* ((bindings (proof-dynamic-bucket view index count packages))
         (tail (proof-dynamic-bucket (cadddr view) index count packages)))
    (implies (and bindings (not (equal view (proof-value-view nil))))
             (and tail (consp (cdddr view))
                  (equal (len (cdr bindings)) (+ 1 (len (cdr tail)))))))
  :hints (("Goal"
           :expand ((proof-dynamic-bucket view index count packages))
           :in-theory (disable proof-dynamic-bucket proof-symbol-hash proof-package-number
                               acl2::binary-logand boymoo-model::a64-signed)))
  :rule-classes nil)

(local
 (defthm symbols-positive-chain-length-follows-link
   (implies (posp length)
            (equal (symbols-intern-chain-length-p length t word world)
                   (and (not (equal word *proof-nil*))
                        (symbols-intern-chain-length-p
                         (1- length) t (car (symbols-intern-fields-at t word world)) world))))
   :hints (("Goal" :in-theory (disable symbols-intern-fields-at)))))

(defthm symbols-physical-dynamic-chain-terminates
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (bindings (proof-dynamic-bucket view index count packages)))
    (implies (and (proof-object-map-p objects objects nil base packages machine)
                  (proof-value-p *proof-nil* nil base objects packages machine)
                  (equal (proof-view word base objects packages machine) view)
                  bindings)
             (symbols-intern-chain-length-p (len (cdr bindings)) t word world)))
  :hints (("Goal"
           :induct (symbols-dynamic-view-and-link-induction view word world)
           :in-theory (disable proof-dynamic-bucket symbols-intern-fields-at proof-world-machine
                               symbols-intern-chain-length-p symbols-positive-chain-length-follows-link))
          ("Subgoal *1/1"
           :use ((:instance symbols-dynamic-entry-fields-agree)
                 (:instance symbols-nonempty-bucket-has-tail)
                 (:instance symbols-canonical-symbol-word (base (proof-heap-base world)) (symbol nil)
                            (first word) (second *proof-nil*) (machine (proof-world-machine world)))
                 (:instance symbols-positive-chain-length-follows-link
                            (length (len (cdr (proof-dynamic-bucket view index count packages))))))
           :in-theory (disable proof-world-machine proof-dynamic-bucket symbols-intern-fields-at
                               symbols-positive-chain-length-follows-link symbols-intern-chain-length-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-nonempty-bucket-has-tail)
                 (:instance symbols-canonical-symbol-word (base (proof-heap-base world)) (symbol nil)
                            (first word) (second *proof-nil*) (machine (proof-world-machine world))))
           :in-theory (disable proof-world-machine proof-dynamic-bucket symbols-intern-fields-at
                               symbols-positive-chain-length-follows-link symbols-intern-chain-length-p)))
  :rule-classes nil)

(local
 (defthm symbols-chain-load-word-is-natural
   (natp (proof-load-word address machine))
   :hints (("Goal" :use ((:instance symbols-load-width (count 8)))
                   :in-theory (e/d (proof-load-word) (boymoo-model::a64-load))))
   :rule-classes :type-prescription))

(local
 (defthm symbols-nonempty-dynamic-table-view-is-vector
   (implies (and (proof-dynamic-entries view packages)
                 (not (equal view (proof-value-view nil))))
            (and (equal view (cons :vector (cdr view)))
                 (consp (cdr view))))
   :hints (("Goal" :cases ((consp view))
                   :expand ((proof-dynamic-entries view packages))
                   :in-theory (disable proof-dynamic-entries proof-dynamic-buckets acl2::binary-logand)))
   :rule-classes nil))

(local
 (defthm symbols-chain-value-view-reconstructs
   (implies (proof-value-view-p view)
            (equal view (proof-value-view (proof-view-value view))))
   :hints (("Goal" :cases ((consp view))))
   :rule-classes nil))

(local
 (defthm symbols-chain-header-fields-reconstruct-word
   (implies (integerp word)
            (equal (+ (proof-header-type word) (* 256 (proof-header-size word))) word))
   :hints (("Goal" :in-theory (enable proof-header-size symbols-unsigned-as-mod ash floor mod)))))

(local
 (defthm symbols-chain-word-address-is-natural
   (natp (proof-pointer-address word base))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))
   :rule-classes :type-prescription))

(defthm symbols-dynamic-table-word-encodes-size-and-count
  (let* ((address (proof-pointer-address word base))
         (view (proof-view word base objects packages machine))
         (bindings (proof-dynamic-entries view packages))
         (count (len (cdr bindings)))
         (size (len (cddr view))))
    (implies (and bindings (not (equal view (proof-value-view nil))))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-load-word address machine) (+ 6 (* 2048 (+ 1 size))))
                  (equal (proof-load-word (+ address 8) machine) (+ 1 (* 2 count))))))
  :hints (("Goal"
           :use ((:instance symbols-nonempty-dynamic-table-view-is-vector
                            (view (proof-view word base objects packages machine)))
                 (:instance symbols-vector-view-shape
                            (entries (cdr (proof-view word base objects packages machine))))
                 (:instance symbols-vector-view-reads-slot (index 0)
                            (entries (cdr (proof-view word base objects packages machine))))
                 (:instance symbols-chain-value-view-reconstructs
                            (view (cadr (proof-view word base objects packages machine))))
                 (:instance symbols-canonical-immediate-integer-word
                            (word (proof-load-word (+ 8 (proof-pointer-address word base)) machine))
                            (number (len (cdr (proof-dynamic-entries (proof-view word base objects packages machine)
                                                                     packages)))))
                 (:instance symbols-chain-header-fields-reconstruct-word
                            (word (proof-load-word (proof-pointer-address word base) machine))))
           :expand ((proof-dynamic-entries (proof-view word base objects packages machine) packages))
           :in-theory (disable proof-dynamic-entries proof-dynamic-buckets proof-header-type proof-header-size
                               symbols-chain-header-fields-reconstruct-word boymoo-model::a64-load
                               proof-load-word proof-symbol-hash acl2::binary-logand ash floor mod)))
  :rule-classes nil)

(defthm symbols-dynamic-table-bucket-word-has-bucket-view
  (let* ((address (proof-pointer-address word base))
         (view (proof-view word base objects packages machine)))
    (implies (and (proof-dynamic-entries view packages)
                  (not (equal view (proof-value-view nil)))
                  (natp index) (< index (len (cddr view))))
             (equal (proof-view (proof-load-word (+ address 16 (* 8 index)) machine)
                                base objects packages machine)
                    (nth index (cddr view)))))
  :hints (("Goal"
           :use ((:instance symbols-nonempty-dynamic-table-view-is-vector
                            (view (proof-view word base objects packages machine)))
                 (:instance symbols-vector-view-reads-slot (index (1+ index))
                            (entries (cdr (proof-view word base objects packages machine)))))
           :expand ((proof-dynamic-entries (proof-view word base objects packages machine) packages))
           :in-theory (disable proof-dynamic-entries proof-dynamic-buckets
                               proof-symbol-hash acl2::binary-logand)))
  :rule-classes nil)

(local
 (defthm symbols-cons-view-has-two-value-fields
   (implies (and (consp value) (equal (proof-cons-value first second) (proof-value-view value)))
            (and (equal first (proof-value-view (car value)))
                 (equal second (proof-value-view (cdr value)))))
   :rule-classes nil))

(local
 (defthm symbols-noncons-value-views-do-not-represent-conses
   (implies (consp value)
            (and (not (equal (proof-integer-view address machine) (cons :value value)))
                 (not (equal (proof-rational-value first second) (cons :value value)))
                 (not (equal (proof-complex-value first second) (cons :value value)))
                 (not (equal (proof-symbol-value first second packages) (cons :value value)))))
   :hints (("Goal" :in-theory (disable proof-load-word proof-header-type proof-header-size
                                      proof-limbs-p proof-limb-magnitude ash mod)))))

(defthm symbols-represented-cons-fields
  (let* ((address (proof-pointer-address word base))
         (entry (assoc-equal address objects)))
    (implies (and (consp value) (proof-value-p word value base objects packages machine))
             (and (equal (proof-word-tag word) 0)
                  (eq (proof-object-kind entry) :cons)
                  (proof-span-p address 16)
                  (proof-value-p (proof-load-word address machine) (car value) base objects packages machine)
                  (proof-value-p (proof-load-word (+ address 8) machine) (cdr value)
                                 base objects packages machine))))
  :hints (("Goal"
           :use ((:instance symbols-view-word-sufficient-rank
                            (word (proof-load-word (proof-pointer-address word base) machine))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance symbols-view-word-sufficient-rank
                            (word (proof-load-word (+ 8 (proof-pointer-address word base)) machine))
                            (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
                 (:instance symbols-cons-view-has-two-value-fields
                            (first (proof-view-step :word (proof-load-word (proof-pointer-address word base) machine)
                                                    0 (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))
                                                    base objects packages machine))
                            (second (proof-view-step :word (proof-load-word (+ 8 (proof-pointer-address word base)) machine)
                                                     0 (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))
                                                     base objects packages machine))))
           :expand ((proof-view word base objects packages machine)
                    (:free (depth) (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (disable symbols-view-word-sufficient-rank
                               proof-cons-value proof-symbol-value proof-rational-value proof-complex-value
                               proof-integer-view proof-load-string proof-span-p proof-object-rank
                               proof-object-kind assoc-equal ash floor mod)))
  :rule-classes nil)

(local
 (defthm symbols-cons-tag-gives-runtime-address
   (implies (equal (proof-word-tag word) 0)
            (equal (symbols-address-plus-word base word) (proof-pointer-address word base)))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))))

(defthm symbols-static-chain-next-word-represents-tail
  (implies (and (consp entries) (proof-machine-value-p word entries world objects packages))
           (proof-machine-value-p (car (symbols-intern-fields-at nil word world))
                                  (cdr entries) world objects packages))
  :hints (("Goal"
           :use ((:instance symbols-represented-cons-fields (value entries)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (disable symbols-address-plus-word proof-world-machine)))
  :rule-classes nil)

(local
 (defun symbols-static-view-and-link-induction (entries word world)
   (if (atom entries)
       word
     (symbols-static-view-and-link-induction (cdr entries)
                                             (car (symbols-intern-fields-at nil word world)) world))))

(local
 (defthm symbols-empty-static-chain-has-canonical-link
   (symbols-intern-chain-length-p 0 nil *proof-nil* world)))

(local
 (defthm symbols-positive-static-chain-length-follows-link
   (implies (posp length)
            (equal (symbols-intern-chain-length-p length nil word world)
                   (and (not (equal word *proof-nil*))
                        (symbols-intern-chain-length-p
                         (1- length) nil (car (symbols-intern-fields-at nil word world)) world))))
   :hints (("Goal" :in-theory (disable symbols-intern-fields-at)))))

(defthm symbols-physical-static-chain-terminates
  (let ((base (proof-heap-base world))
        (machine (proof-world-machine world)))
    (implies (and (proof-static-bucket-p entries index packages)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-machine-value-p *proof-nil* nil world objects packages)
                  (proof-machine-value-p word entries world objects packages))
             (symbols-intern-chain-length-p (len entries) nil word world)))
  :hints (("Goal"
           :induct (symbols-static-view-and-link-induction entries word world)
           :in-theory (disable symbols-positive-static-chain-length-follows-link symbols-intern-chain-length-p
                               symbols-intern-fields-at proof-world-machine proof-symbol-hash proof-package-number))
          ("Subgoal *1/2"
           :use ((:instance symbols-static-chain-next-word-represents-tail)
                 (:instance symbols-positive-static-chain-length-follows-link (length (len entries))))
           :in-theory (disable symbols-positive-static-chain-length-follows-link symbols-intern-chain-length-p
                               symbols-intern-fields-at proof-world-machine proof-symbol-hash proof-package-number))
          ("Subgoal *1/1"
           :use ((:instance symbols-canonical-symbol-word (symbol nil) (first word) (second *proof-nil*)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (disable symbols-positive-static-chain-length-follows-link symbols-intern-chain-length-p
                               symbols-intern-fields-at proof-world-machine proof-symbol-hash proof-package-number)))
  :rule-classes nil)

(local
 (defun symbols-chain-cons-head (word world)
   (proof-load-word (proof-pointer-address word (proof-heap-base world)) (proof-world-machine world))))

(defthm symbols-physical-static-entry-gives-binding-fields
  (let ((fields (symbols-intern-fields-at nil word world)))
    (implies (and (consp entries) (consp (car entries)) (consp (caar entries))
                  (proof-machine-value-p word entries world objects packages))
             (and (proof-machine-value-p (cadr fields) (cdar entries) world objects packages)
                  (proof-machine-value-p (cadddr fields) (caaar entries) world objects packages)
                  (proof-machine-value-p (car (cddddr fields)) (cdaar entries) world objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-represented-cons-fields (value entries)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance symbols-represented-cons-fields (value (car entries))
                            (word (symbols-chain-cons-head word world))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance symbols-represented-cons-fields (value (caar entries))
                            (word (symbols-chain-cons-head (symbols-chain-cons-head word world) world))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (disable symbols-address-plus-word proof-world-machine proof-value-p)))
  :rule-classes nil)

(local
 (defthm symbols-dynamic-bucket-member-has-symbol-and-hash-view
   (implies (and (proof-dynamic-bucket view index count packages)
                 (not (equal view (proof-value-view nil))))
            (and (proof-value-view-p (cadr view))
                 (symbolp (proof-view-value (cadr view)))
                 (equal (cadr view) (proof-value-view (proof-view-value (cadr view))))
                 (proof-value-view-p (caddr view))
                 (equal (caddr view) (proof-value-view (proof-view-value (caddr view))))))
   :hints (("Goal"
            :use ((:instance symbols-chain-value-view-reconstructs (view (cadr view)))
                  (:instance symbols-chain-value-view-reconstructs (view (caddr view))))
            :expand ((proof-dynamic-bucket view index count packages))
            :in-theory (disable proof-dynamic-bucket proof-symbol-hash proof-package-number
                                acl2::binary-logand boymoo-model::a64-signed)))
   :rule-classes nil))

(defthm symbols-physical-dynamic-entry-gives-binding-fields
  (let* ((view (proof-view word (proof-heap-base world) objects packages (proof-world-machine world)))
         (fields (symbols-intern-fields-at t word world)))
    (implies (and (proof-dynamic-bucket view index count packages)
                  (not (equal view (proof-value-view nil))))
             (and (proof-machine-value-p (cadr fields) (proof-view-value (cadr view)) world objects packages)
                  (proof-machine-value-p (caddr fields) (proof-view-value (caddr view)) world objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-dynamic-entry-fields-agree)
                 (:instance symbols-dynamic-bucket-member-has-symbol-and-hash-view
                            (view (proof-view word (proof-heap-base world) objects packages (proof-world-machine world)))))
           :in-theory (disable symbols-intern-fields-at proof-dynamic-bucket proof-world-machine)))
  :rule-classes nil)

(defun symbols-physical-dynamic-chain-tail (links word world)
  (declare (xargs :measure (nfix links)))
  (if (zp links)
      word
    (symbols-physical-dynamic-chain-tail
     (1- links) (car (symbols-intern-fields-at t word world)) world)))

(local
 (defun symbols-follow-dynamic-views-induction (links word view world)
   (declare (xargs :measure (nfix links)))
   (if (zp links)
       (cons word view)
     (symbols-follow-dynamic-views-induction
      (1- links) (car (symbols-intern-fields-at t word world)) (cadddr view) world))))

(defthm symbols-physical-chain-tail-has-decoded-view
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (bindings (proof-dynamic-bucket view index size packages)))
    (implies (and bindings (natp links) (<= links (len (cdr bindings)))
                  (equal (proof-view word base objects packages machine) view))
             (equal (proof-view (symbols-physical-dynamic-chain-tail links word world) base objects packages machine)
                    (symbols-chain-tail links view))))
  :hints (("Goal" :induct (symbols-follow-dynamic-views-induction links word view world)
                  :in-theory (disable proof-dynamic-bucket symbols-intern-fields-at proof-world-machine))
          ("Subgoal *1/2"
           :use ((:instance symbols-nonempty-bucket-has-tail (count size))
                 (:instance symbols-dynamic-entry-fields-agree (count size)))
           :expand ((symbols-chain-tail links view) (symbols-physical-dynamic-chain-tail links word world))
           :in-theory (disable proof-dynamic-bucket symbols-intern-fields-at proof-world-machine)))
  :rule-classes nil)

(local
 (defthm symbols-decoded-chain-tail-is-valid
   (let ((bindings (proof-dynamic-bucket view index size packages)))
     (implies (and bindings (natp links) (<= links (len (cdr bindings))))
              (proof-dynamic-bucket (symbols-chain-tail links view) index size packages)))
   :hints (("Goal" :induct (symbols-chain-tail links view) :in-theory (disable proof-dynamic-bucket))
           ("Subgoal *1/2"
            :use ((:instance symbols-nonempty-bucket-has-tail (count size)))
            :in-theory (disable proof-dynamic-bucket)))
   :rule-classes nil))

(defthm symbols-physical-chain-symbol-word-is-canonical
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (tail (symbols-physical-dynamic-chain-tail links word world))
         (bindings (proof-dynamic-bucket view index size packages)))
    (implies (and bindings (natp links) (< links (len (cdr bindings)))
                  (equal (proof-view word base objects packages machine) view)
                  (symbolp symbol)
                  (equal (cadr (symbols-chain-tail links view)) (proof-value-view symbol))
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-value-p represented symbol base objects packages machine))
             (equal (cadr (symbols-intern-fields-at t tail world)) represented)))
  :hints (("Goal"
           :use ((:instance symbols-physical-chain-tail-has-decoded-view)
                 (:instance symbols-decoded-chain-tail-is-valid)
                 (:instance symbols-dynamic-chain-terminates (bucket view))
                 (:instance symbols-physical-dynamic-entry-gives-binding-fields
                            (word (symbols-physical-dynamic-chain-tail links word world)) (count size))
                 (:instance symbols-canonical-symbol-word (base (proof-heap-base world))
                            (first (cadr (symbols-intern-fields-at t (symbols-physical-dynamic-chain-tail links word world)
                                                                 world)))
                            (second represented) (machine (proof-world-machine world))))
           :in-theory (disable proof-dynamic-bucket symbols-chain-tail symbols-intern-fields-at
                               proof-world-machine symbols-dynamic-chain-terminates)))
  :rule-classes nil)

(defun symbols-physical-dynamic-root-bucket (index world)
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (table (proof-pointer-address (proof-dynamic-root base machine) base)))
    (proof-load-word (+ table 16 (* 8 (nfix index))) machine)))

(local
 (defthm symbols-valid-dynamic-table-has-bucket-views
   (let* ((bindings (proof-dynamic-entries root packages))
          (buckets (cddr root)))
     (implies (and bindings (member-equal symbol (cdr bindings)))
              (and (not (equal root (proof-value-view nil)))
                   (equal bindings (proof-dynamic-buckets buckets 0 (len buckets) packages)))))
   :hints (("Goal" :expand ((proof-dynamic-entries root packages))
                   :in-theory (disable proof-dynamic-entries proof-dynamic-buckets acl2::binary-logand)))
   :rule-classes nil))

(local
 (defthm symbols-physical-dynamic-root-word-has-selected-view
   (let* ((base (proof-heap-base world))
          (machine (proof-world-machine world))
          (root (proof-dynamic-view world objects packages)))
     (implies (and (proof-dynamic-entries root packages)
                   (not (equal root (proof-value-view nil)))
                   (natp index) (< index (len (cddr root))))
              (equal (proof-view (symbols-physical-dynamic-root-bucket index world) base objects packages machine)
                     (nth index (cddr root)))))
   :hints (("Goal"
            :use ((:instance symbols-dynamic-table-bucket-word-has-bucket-view
                             (word (proof-dynamic-root (proof-heap-base world) (proof-world-machine world)))
                             (base (proof-heap-base world)) (machine (proof-world-machine world))))
            :in-theory (disable proof-dynamic-entries proof-dynamic-root proof-world-machine)))
   :rule-classes nil))

(defthm symbols-published-root-reaches-canonical-word
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (root (proof-dynamic-view world objects packages))
         (bindings (proof-dynamic-entries root packages))
         (buckets (cddr root))
         (size (len buckets))
         (index (symbols-bucket-index symbol size packages))
         (bucket (nth index buckets))
         (head (symbols-physical-dynamic-root-bucket index world))
         (links (symbols-chain-distance symbol bucket))
         (entry (symbols-physical-dynamic-chain-tail links head world)))
    (implies (and bindings (member-equal symbol (cdr bindings)) (symbolp symbol)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-value-p represented symbol base objects packages machine))
             (and (natp index) (< index size) (natp links)
                  (equal (cadr (symbols-intern-fields-at t entry world)) represented))))
  :hints (("Goal"
           :use ((:instance symbols-root-reaches-listed-symbol (root (proof-dynamic-view world objects packages)))
                 (:instance symbols-valid-dynamic-table-has-bucket-views (root (proof-dynamic-view world objects packages)))
                 (:instance symbols-nth-dynamic-bucket-valid (first 0)
                            (buckets (cddr (proof-dynamic-view world objects packages)))
                            (size (len (cddr (proof-dynamic-view world objects packages))))
                            (offset (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages)))
                                                          packages)))
                 (:instance symbols-dynamic-member-in-selected-bucket (first 0)
                            (buckets (cddr (proof-dynamic-view world objects packages)))
                            (size (len (cddr (proof-dynamic-view world objects packages))))
                            (offset (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages)))
                                                          packages)))
                 (:instance symbols-physical-dynamic-root-word-has-selected-view
                            (index (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages)))
                                                         packages)))
                 (:instance symbols-binding-has-finite-chain-distance
                            (size (len (cddr (proof-dynamic-view world objects packages))))
                            (index (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages))) packages))
                            (bucket (nth (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages)))
                                                               packages)
                                         (cddr (proof-dynamic-view world objects packages)))))
                 (:instance symbols-physical-chain-symbol-word-is-canonical
                            (size (len (cddr (proof-dynamic-view world objects packages))))
                            (index (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages))) packages))
                            (view (nth (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages))) packages)
                                       (cddr (proof-dynamic-view world objects packages))))
                            (links (symbols-chain-distance
                                    symbol (nth (symbols-bucket-index
                                                 symbol (len (cddr (proof-dynamic-view world objects packages))) packages)
                                                (cddr (proof-dynamic-view world objects packages)))))
                            (word (symbols-physical-dynamic-root-bucket
                                   (symbols-bucket-index symbol (len (cddr (proof-dynamic-view world objects packages))) packages)
                                   world))))
           :in-theory (disable proof-dynamic-view proof-dynamic-entries proof-dynamic-buckets proof-dynamic-bucket
                               symbols-root-reaches-listed-symbol symbols-nth-dynamic-bucket-valid
                               symbols-dynamic-member-in-selected-bucket symbols-binding-has-finite-chain-distance
                               symbols-physical-dynamic-root-bucket symbols-physical-dynamic-chain-tail
                               symbols-bucket-index symbols-chain-distance symbols-chain-tail symbols-intern-fields-at
                               proof-value-p proof-world-machine)))
  :rule-classes nil)
