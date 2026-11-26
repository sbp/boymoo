(in-package "BOYMOO-PROOFS")

(include-book "package-model")
(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(defun symbols-cached-hash (symbol packages)
  (boymoo-model::a64-signed
   63 (proof-symbol-hash
       (proof-package-number (acl2::symbol-package-name symbol) packages 0)
       (symbol-name symbol) 63)))

(defun symbols-bucket-index (symbol size packages)
  (logand (1- size) (symbols-cached-hash symbol packages)))

(defthm symbols-bucket-index-bounds
  (implies (posp size)
           (and (natp (symbols-bucket-index symbol size packages))
                (< (symbols-bucket-index symbol size packages) size)))
  :hints (("Goal"
           :use ((:instance symbols-and-mask-bounds
                            (mask (1- size)) (x (symbols-cached-hash symbol packages))))
           :in-theory (disable symbols-and-mask-bounds symbols-cached-hash
                               acl2::binary-logand))))

(defun symbols-home-symbol-p (symbol packages)
  (and (symbolp symbol)
       (natp (proof-package-number (acl2::symbol-package-name symbol) packages 0))))

(defun symbols-prepend-entry (symbol bucket packages)
  (list :vector (proof-value-view symbol)
        (proof-value-view (symbols-cached-hash symbol packages))
        bucket))

(defthm symbols-prepend-entry-yields-binding
  (implies (and (symbols-home-symbol-p symbol packages)
                (equal index (symbols-bucket-index symbol size packages))
                (proof-dynamic-bucket bucket index size packages))
           (equal (proof-dynamic-bucket
                   (symbols-prepend-entry symbol bucket packages)
                   index size packages)
                  (list* :entries symbol
                         (cdr (proof-dynamic-bucket bucket index size packages)))))
  :hints (("Goal" :in-theory (disable proof-symbol-hash proof-package-number
                                      boymoo-model::a64-signed acl2::binary-logand))))

(defun symbols-push-bucket (offset symbol buckets packages)
  (update-nth offset
              (symbols-prepend-entry symbol (nth offset buckets) packages)
              buckets))

(defthm symbols-push-bucket-length
  (implies (and (natp offset) (< offset (len buckets)))
           (equal (len (symbols-push-bucket offset symbol buckets packages))
                  (len buckets)))
  :hints (("Goal" :induct (update-nth offset item buckets)
                  :in-theory (disable symbols-prepend-entry))))

; Flattening concatenates buckets in increasing index order. Inserting
; a new head inserts a single symbol at the boundary of its bucket.
(defun symbols-entries-before (offset buckets first size packages)
  (declare (xargs :measure (nfix offset)))
  (if (or (zp offset) (atom buckets))
      0
    (+ (len (cdr (proof-dynamic-bucket (car buckets) first size packages)))
       (symbols-entries-before (1- offset) (cdr buckets) (1+ first) size packages))))

(defthm symbols-entries-before-is-natural
  (natp (symbols-entries-before offset buckets first size packages))
  :rule-classes :type-prescription)

(defun symbols-insert-at (offset symbol entries)
  (declare (xargs :measure (nfix offset)))
  (if (or (zp offset) (atom entries))
      (cons symbol entries)
    (cons (car entries)
          (symbols-insert-at (1- offset) symbol (cdr entries)))))

(local
 (defthm symbols-insert-after-prefix
   (implies (natp offset)
            (equal (symbols-insert-at (+ (len prefix) offset)
                                      symbol (append prefix entries))
                   (append prefix (symbols-insert-at offset symbol entries))))))

(local
 (defthm symbols-dynamic-bucket-marker
   (implies (proof-dynamic-bucket bucket index size packages)
            (equal (car (proof-dynamic-bucket bucket index size packages)) :entries))
   :hints (("Goal" :in-theory (disable proof-symbol-hash proof-package-number
                                       boymoo-model::a64-signed acl2::binary-logand)))))

(local
 (defthm symbols-dynamic-buckets-marker
   (implies (proof-dynamic-buckets buckets first size packages)
            (equal (car (proof-dynamic-buckets buckets first size packages))
                   :entries))
   :hints (("Goal" :in-theory (disable proof-dynamic-bucket)))))

(defthm symbols-push-bucket-yields-insertion
  (implies
   (and (natp offset) (< offset (len buckets))
        (natp first)
        (symbols-home-symbol-p symbol packages)
        (equal (+ first offset) (symbols-bucket-index symbol size packages))
        (proof-dynamic-buckets buckets first size packages))
   (equal
    (proof-dynamic-buckets (symbols-push-bucket offset symbol buckets packages)
                           first size packages)
    (cons :entries
          (symbols-insert-at (symbols-entries-before offset buckets first size packages)
                             symbol
                             (cdr (proof-dynamic-buckets
                                   buckets first size packages))))))
  :hints (("Goal"
           :induct (symbols-entries-before offset buckets first size packages)
           :in-theory (disable proof-dynamic-bucket symbols-prepend-entry
                               symbols-home-symbol-p symbols-bucket-index
                               proof-package-number boymoo-model::a64-signed
                               acl2::binary-logand))))

(defthm symbols-insert-at-length
  (equal (len (symbols-insert-at offset symbol entries)) (1+ (len entries))))

(defthm symbols-insert-at-membership
  (iff (member-equal value (symbols-insert-at offset symbol entries))
       (or (equal value symbol) (member-equal value entries))))

(defthm symbols-insert-at-uniqueness
  (iff (no-duplicatesp-equal (symbols-insert-at offset symbol entries))
       (and (no-duplicatesp-equal entries)
            (not (member-equal symbol entries)))))

(defun symbols-empty-buckets (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-value-view nil) (symbols-empty-buckets (1- count)))))

(defthm symbols-empty-bucket-length
  (equal (len (symbols-empty-buckets count)) (nfix count)))

(local
 (defun symbols-empty-buckets-induction (count first)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       first
     (symbols-empty-buckets-induction (1- count) (1+ first)))))

(defthm symbols-empty-buckets-have-no-bindings
  (equal (proof-dynamic-buckets (symbols-empty-buckets count) first size packages)
         (list :entries))
  :hints (("Goal" :induct (symbols-empty-buckets-induction count first))))

(local
 (defthm symbols-valid-dynamic-root-fields
   (implies (and (proof-dynamic-entries root packages)
                 (not (equal root (proof-value-view nil))))
            (let* ((buckets (cddr root))
                   (size (len buckets))
                   (count (proof-view-value (cadr root))))
              (and (eq (car root) :vector)
                   (<= 16 size)
                   (equal (logand size (1- size)) 0)
                   (natp count)
                   (<= count size)
                   (equal count (len (cdr (proof-dynamic-entries root packages))))
                   (equal (proof-dynamic-entries root packages)
                          (proof-dynamic-buckets buckets 0 size packages))
                   (no-duplicatesp-equal (cdr (proof-dynamic-entries root packages))))))
   :hints (("Goal" :in-theory (disable proof-dynamic-buckets acl2::binary-logand)))
   :rule-classes nil))

(defun symbols-insert-binding (symbol root packages)
  (let* ((buckets (cddr root))
         (index (symbols-bucket-index symbol (len buckets) packages))
         (count (proof-view-value (cadr root))))
    (list* :vector (proof-value-view (1+ count))
           (symbols-push-bucket index symbol buckets packages))))

(defthm symbols-insert-binding-preserves-invariant
  (let* ((size (len (cddr root)))
         (index (symbols-bucket-index symbol size packages))
         (old (proof-dynamic-entries root packages))
         (new (proof-dynamic-entries (symbols-insert-binding symbol root packages)
                                    packages)))
    (implies (and old (not (equal root (proof-value-view nil)))
                  (symbols-home-symbol-p symbol packages)
                  (natp index) (< index size)
                  (< (proof-view-value (cadr root)) size)
                  (not (member-equal symbol (cdr old))))
             (and new
                  (equal (len (cdr new)) (1+ (len (cdr old))))
                  (iff (member-equal value (cdr new))
                       (or (equal value symbol) (member-equal value (cdr old)))))))
  :hints (("Goal"
           :use ((:instance symbols-valid-dynamic-root-fields)
                 (:instance symbols-push-bucket-yields-insertion
                            (first 0) (buckets (cddr root))
                            (size (len (cddr root)))
                            (offset (symbols-bucket-index symbol (len (cddr root)) packages))))
           :in-theory (disable proof-dynamic-buckets symbols-push-bucket
                               symbols-insert-at symbols-home-symbol-p
                               symbols-bucket-index acl2::binary-logand)
           :expand ((proof-dynamic-entries (symbols-insert-binding symbol root packages)
                                            packages)))))

(defthm symbols-fresh-binding-preserves-dynamic-table
  (let* ((old (proof-dynamic-entries root packages))
         (new (proof-dynamic-entries (symbols-insert-binding symbol root packages) packages)))
    (implies (and old (not (equal root (proof-value-view nil)))
                  (symbols-home-symbol-p symbol packages)
                  (< (proof-view-value (cadr root)) (len (cddr root)))
                  (not (member-equal symbol (cdr old))))
             (and new
                  (equal (len (cdr new)) (1+ (len (cdr old))))
                  (iff (member-equal value (cdr new))
                       (or (equal value symbol) (member-equal value (cdr old)))))))
  :hints (("Goal"
           :use ((:instance symbols-valid-dynamic-root-fields)
                 (:instance symbols-bucket-index-bounds (size (len (cddr root))))
                 (:instance symbols-insert-binding-preserves-invariant))
           :in-theory (disable proof-dynamic-entries symbols-home-symbol-p
                               symbols-bucket-index symbols-insert-binding
                               symbols-bucket-index-bounds
                               symbols-insert-binding-preserves-invariant))))

(defun symbols-routable-entries-p (entries size packages)
  (if (atom entries)
      (null entries)
    (let ((symbol (car entries)))
      (and (symbols-home-symbol-p symbol packages)
           (natp (symbols-bucket-index symbol size packages))
           (< (symbols-bucket-index symbol size packages) size)
           (symbols-routable-entries-p (cdr entries) size packages)))))

; Growth visits the old buckets in index order and the entries of each
; bucket in link order. A visit prepends the entry to its new bucket.
(defun symbols-rehash-bindings (entries buckets size packages)
  (if (atom entries)
      buckets
    (let* ((symbol (car entries))
           (index (symbols-bucket-index symbol size packages)))
      (symbols-rehash-bindings
       (cdr entries) (symbols-push-bucket index symbol buckets packages)
       size packages))))

(defthm symbols-rehash-empty-input
  (equal (symbols-rehash-bindings nil buckets size packages) buckets))

(defthm symbols-rehash-keeps-bucket-count
  (implies (and (symbols-routable-entries-p entries size packages)
                (equal (len buckets) size))
           (equal (len (symbols-rehash-bindings entries buckets size packages))
                  size))
  :hints (("Goal" :induct (symbols-rehash-bindings entries buckets size packages)
                  :in-theory (disable symbols-push-bucket symbols-home-symbol-p
                                      symbols-bucket-index))))

(local
 (defthm symbols-member-of-append
   (iff (member-equal value (append x y))
        (or (member-equal value x) (member-equal value y)))))

(defthm symbols-rehash-keeps-bindings
  (let ((old (proof-dynamic-buckets buckets 0 size packages))
        (new (proof-dynamic-buckets
              (symbols-rehash-bindings entries buckets size packages)
              0 size packages)))
    (implies (and (symbols-routable-entries-p entries size packages)
                  (<= size (len buckets))
                  old)
             (and new
                  (equal (len (cdr new)) (+ (len entries) (len (cdr old))))
                  (iff (member-equal value (cdr new))
                       (member-equal value (append entries (cdr old)))))))
  :hints (("Goal" :induct (symbols-rehash-bindings entries buckets size packages)
                  :in-theory (disable proof-dynamic-buckets symbols-push-bucket
                                      symbols-insert-at symbols-home-symbol-p
                                      symbols-bucket-index))))

(local
 (defun symbols-disjoint-entries-p (left right)
   (if (atom left)
       t
     (and (not (member-equal (car left) right))
          (symbols-disjoint-entries-p (cdr left) right)))))

(local
 (defthm symbols-no-entries-are-disjoint
   (symbols-disjoint-entries-p entries nil)))

(local
 (defthm symbols-disjoint-entries-after-insertion
   (iff (symbols-disjoint-entries-p entries (symbols-insert-at offset symbol old))
        (and (not (member-equal symbol entries))
             (symbols-disjoint-entries-p entries old)))
   :hints (("Goal" :induct (symbols-disjoint-entries-p entries old)
                   :in-theory (disable symbols-insert-at)))))

(local
 (defthm symbols-rehash-keeps-unique-bindings
   (let ((old (proof-dynamic-buckets buckets 0 size packages)))
     (implies (and (symbols-routable-entries-p entries size packages)
                   (<= size (len buckets))
                   old
                   (no-duplicatesp-equal (cdr old))
                   (no-duplicatesp-equal entries)
                   (symbols-disjoint-entries-p entries (cdr old)))
              (no-duplicatesp-equal
               (cdr (proof-dynamic-buckets
                     (symbols-rehash-bindings entries buckets size packages)
                     0 size packages)))))
   :hints (("Goal" :induct (symbols-rehash-bindings entries buckets size packages)
                   :in-theory (disable proof-dynamic-buckets symbols-push-bucket
                                       symbols-insert-at symbols-home-symbol-p
                                       symbols-bucket-index)))))

(defun symbols-grown-size (root)
  (if (equal root (proof-value-view nil)) 16 (* 2 (len (cddr root)))))

(defun symbols-grow-view (root packages)
  (let* ((size (symbols-grown-size root))
         (entries (proof-dynamic-entries root packages))
         (count (if (equal root (proof-value-view nil))
                    (proof-value-view 0)
                  (cadr root))))
    (list* :vector count
           (symbols-rehash-bindings (cdr entries) (symbols-empty-buckets size)
                                    size packages))))

(defthm symbols-grow-view-preserves-invariant
  (let* ((size (symbols-grown-size root))
         (old (proof-dynamic-entries root packages))
         (rebuilt (symbols-grow-view root packages))
         (new (proof-dynamic-entries rebuilt packages)))
    (implies (and old
                  (symbols-routable-entries-p (cdr old) size packages)
                  (equal (logand size (1- size)) 0))
             (and new
                  (equal (len (cddr rebuilt)) size)
                  (equal (len (cdr new)) (len (cdr old)))
                  (iff (member-equal value (cdr new))
                       (member-equal value (cdr old))))))
  :hints (("Goal"
           :in-theory (disable proof-dynamic-buckets symbols-empty-buckets
                               (:executable-counterpart symbols-empty-buckets)
                               symbols-rehash-bindings symbols-routable-entries-p
                               acl2::binary-logand)
           :use ((:instance symbols-rehash-keeps-unique-bindings
                            (entries (cdr (proof-dynamic-entries root packages)))
                            (size (symbols-grown-size root))
                            (buckets (symbols-empty-buckets (symbols-grown-size root))))))))

(local
 (defthm symbols-routability-of-append
   (implies (and (symbols-routable-entries-p left size packages)
                 (symbols-routable-entries-p right size packages))
            (symbols-routable-entries-p (append left right) size packages))
   :hints (("Goal" :in-theory (disable symbols-bucket-index symbols-home-symbol-p)))))

(local
 (defthm symbols-valid-bucket-entries-are-routable
   (let ((entries (proof-dynamic-bucket bucket index count packages)))
     (implies (and entries (posp size))
              (symbols-routable-entries-p (cdr entries) size packages)))
   :hints (("Goal" :induct (proof-dynamic-bucket bucket index count packages)
                   :in-theory (disable proof-symbol-hash proof-package-number
                                       symbols-bucket-index boymoo-model::a64-signed
                                       acl2::binary-logand))
           ("Subgoal *1/2"
            :use ((:instance symbols-bucket-index-bounds
                             (symbol (proof-view-value (cadr bucket)))))))))

(local
 (defthm symbols-valid-buckets-entries-are-routable
   (let ((entries (proof-dynamic-buckets buckets first count packages)))
     (implies (and entries (posp size))
              (symbols-routable-entries-p (cdr entries) size packages)))
   :hints (("Goal" :induct (proof-dynamic-buckets buckets first count packages)
                   :in-theory (disable proof-dynamic-bucket)))))

(defthm symbols-doubling-preserves-dynamic-table
  (let* ((old (proof-dynamic-entries root packages))
         (rebuilt (symbols-grow-view root packages))
         (new (proof-dynamic-entries rebuilt packages)))
    (implies old
             (and new
                  (equal (len (cddr rebuilt)) (symbols-grown-size root))
                  (equal (len (cdr new)) (len (cdr old)))
                  (iff (member-equal value (cdr new))
                       (member-equal value (cdr old)))))))

(defun symbols-chain-tail (links bucket)
  (declare (xargs :measure (nfix links)))
  (if (zp links)
      bucket
    (symbols-chain-tail (1- links) (cadddr bucket))))

(defthm symbols-dynamic-chain-terminates
  (let* ((entries (proof-dynamic-bucket bucket index size packages))
         (count (len (cdr entries))))
    (implies (and entries (natp links) (<= links count))
             (iff (equal (symbols-chain-tail links bucket) (proof-value-view nil))
                  (equal links count))))
  :hints (("Goal" :induct (symbols-chain-tail links bucket)
                  :expand ((proof-dynamic-bucket bucket index size packages))
                  :in-theory (disable proof-package-number proof-symbol-hash
                                      boymoo-model::a64-signed acl2::binary-logand))))

(defthm symbols-dynamic-member-bucket-index
  (let ((entries (proof-dynamic-bucket bucket index size packages)))
    (implies (and entries (member-equal symbol (cdr entries)))
             (and (symbols-home-symbol-p symbol packages)
                  (equal (symbols-bucket-index symbol size packages) index))))
  :hints (("Goal" :induct (proof-dynamic-bucket bucket index size packages)
                  :in-theory (disable proof-package-number proof-symbol-hash
                                      boymoo-model::a64-signed acl2::binary-logand))))

(local
 (defthm symbols-dynamic-bucket-absence-before-first
   (implies (and (natp first)
                 (< (symbols-bucket-index symbol size packages) first))
            (not (member-equal symbol
                               (cdr (proof-dynamic-buckets buckets first size packages)))))
   :hints (("Goal" :induct (proof-dynamic-buckets buckets first size packages)
                   :in-theory (disable proof-dynamic-bucket symbols-bucket-index
                                       symbols-home-symbol-p)))))

(local
 (defun symbols-scan-buckets-induction (buckets first offset)
   (if (atom buckets)
       (cons first offset)
     (symbols-scan-buckets-induction (cdr buckets) (1+ first) (1- offset)))))

(local
 (defthm symbols-absent-bucket-has-no-view
   (equal (proof-dynamic-bucket nil index size packages) nil)))

(defthm symbols-dynamic-member-in-selected-bucket
  (let ((entries (proof-dynamic-buckets buckets first size packages))
        (index (+ first offset)))
    (implies (and entries (natp first) (natp offset)
                  (equal index (symbols-bucket-index symbol size packages)))
             (iff (member-equal symbol (cdr entries))
                  (member-equal symbol
                                (cdr (proof-dynamic-bucket
                                      (nth offset buckets) index size packages))))))
  :hints (("Goal" :induct (symbols-scan-buckets-induction buckets first offset)
                  :in-theory (disable proof-dynamic-bucket symbols-bucket-index
                                      symbols-home-symbol-p))))

(defthm symbols-nth-dynamic-bucket-valid
  (implies (and (proof-dynamic-buckets buckets first size packages)
                (natp first) (natp offset) (< offset (len buckets)))
           (proof-dynamic-bucket (nth offset buckets) (+ first offset) size packages))
  :hints (("Goal" :induct (symbols-scan-buckets-induction buckets first offset)
                  :in-theory (disable proof-dynamic-bucket))))

(defun symbols-dynamic-scan (name number hash bucket packages)
  (declare (xargs :measure (acl2-count bucket)))
  (if (equal bucket (proof-value-view nil))
      nil
    (let ((symbol (proof-view-value (cadr bucket))))
      (cond ((atom (cdddr bucket)) nil)
            ((and (equal hash (proof-view-value (caddr bucket)))
                  (equal number (proof-package-number
                                 (acl2::symbol-package-name symbol) packages 0))
                  (equal name (symbol-name symbol)))
             (proof-value-view symbol))
            (t (symbols-dynamic-scan name number hash (cadddr bucket) packages))))))

(local
 (defthm symbols-associated-row-name
   (implies (assoc-equal name packages)
            (equal (proof-package-name (assoc-equal name packages)) name))))

(defthm symbols-package-number-injective
  (implies (and (natp (proof-package-number left packages 0))
                (natp (proof-package-number right packages 0))
                (equal (proof-package-number left packages 0)
                       (proof-package-number right packages 0))
                (alistp packages))
           (equal left right))
  :hints (("Goal"
           :use ((:instance symbols-package-number-selects-row (first 0) (name left))
                 (:instance symbols-package-number-selects-row (first 0) (name right))
                 (:instance symbols-package-number-present (first 0) (name left))
                 (:instance symbols-package-number-present (first 0) (name right))
                 (:instance symbols-associated-row-name (name left))
                 (:instance symbols-associated-row-name (name right)))
           :in-theory (disable proof-package-number proof-package-name assoc-equal
                               symbols-package-number-present
                               symbols-associated-row-name)))
  :rule-classes nil)

(local
 (defthm symbols-dynamic-key-identifies-symbol
   (implies (and (symbols-home-symbol-p left packages)
                 (symbols-home-symbol-p right packages)
                 (equal (proof-package-number (acl2::symbol-package-name left)
                                              packages 0)
                        (proof-package-number (acl2::symbol-package-name right)
                                              packages 0))
                 (equal (symbol-name left) (symbol-name right))
                 (alistp packages))
            (equal left right))
   :hints (("Goal"
            :use ((:instance symbols-package-number-injective
                             (left (acl2::symbol-package-name left))
                             (right (acl2::symbol-package-name right)))
                  (:instance symbols-equal-when-spellings-agree (x left) (y right)))
            :in-theory (disable proof-package-number)))
   :rule-classes nil))

(defthm symbols-dynamic-scan-finds-binding
  (let ((entries (proof-dynamic-bucket bucket index size packages)))
    (implies (and entries (symbols-home-symbol-p symbol packages) (alistp packages))
             (equal (symbols-dynamic-scan
                     (symbol-name symbol)
                     (proof-package-number (acl2::symbol-package-name symbol) packages 0)
                     (symbols-cached-hash symbol packages)
                     bucket packages)
                    (and (member-equal symbol (cdr entries))
                         (proof-value-view symbol)))))
  :hints (("Goal"
           :induct (proof-dynamic-bucket bucket index size packages)
           :in-theory (disable proof-package-number proof-symbol-hash
                               boymoo-model::a64-signed acl2::binary-logand))
          ("Subgoal *1/2"
           :use ((:instance symbols-dynamic-key-identifies-symbol
                            (left symbol) (right (proof-view-value (cadr bucket))))))))

(defun symbols-lookup-binding (symbol root packages)
  (if (equal root (proof-value-view nil))
      nil
    (let* ((buckets (cddr root))
           (index (symbols-bucket-index symbol (len buckets) packages)))
      (symbols-dynamic-scan
       (symbol-name symbol)
       (proof-package-number (acl2::symbol-package-name symbol) packages 0)
       (symbols-cached-hash symbol packages)
       (nth index buckets) packages))))

(defthm symbols-lookup-binding-implements-membership
  (let* ((index (symbols-bucket-index symbol (len (cddr root)) packages))
         (entries (proof-dynamic-entries root packages)))
    (implies (and entries (symbols-home-symbol-p symbol packages)
                  (natp index) (< index (len (cddr root))) (alistp packages))
             (equal (symbols-lookup-binding symbol root packages)
                    (and (member-equal symbol (cdr entries))
                         (proof-value-view symbol)))))
  :hints (("Goal"
           :use ((:instance symbols-valid-dynamic-root-fields)
                 (:instance symbols-nth-dynamic-bucket-valid
                            (buckets (cddr root)) (first 0)
                            (size (len (cddr root)))
                            (offset (symbols-bucket-index symbol (len (cddr root)) packages)))
                 (:instance symbols-dynamic-member-in-selected-bucket
                            (buckets (cddr root)) (first 0)
                            (size (len (cddr root)))
                            (offset (symbols-bucket-index symbol (len (cddr root)) packages)))
                 (:instance symbols-dynamic-scan-finds-binding
                            (bucket (nth (symbols-bucket-index symbol (len (cddr root)) packages)
                                         (cddr root)))
                            (index (symbols-bucket-index symbol (len (cddr root)) packages))
                            (size (len (cddr root)))))
           :in-theory (disable proof-dynamic-buckets proof-dynamic-bucket
                               symbols-bucket-index symbols-dynamic-scan
                               symbols-cached-hash proof-package-number
                               symbols-dynamic-scan-finds-binding
                               symbols-dynamic-member-in-selected-bucket
                               symbols-nth-dynamic-bucket-valid))))

(defun symbols-chain-distance (symbol bucket)
  (declare (xargs :measure (acl2-count bucket)))
  (cond ((atom (cdddr bucket)) nil)
        ((equal (proof-view-value (cadr bucket)) symbol) 0)
        (t (let ((distance (symbols-chain-distance symbol (cadddr bucket))))
             (and distance (1+ distance))))))

(defthm symbols-binding-has-finite-chain-distance
  (let* ((entries (proof-dynamic-bucket bucket index size packages))
         (distance (symbols-chain-distance symbol bucket)))
    (implies (and entries (member-equal symbol (cdr entries)))
             (and (natp distance)
                  (< distance (len (cdr entries)))
                  (equal (cadr (symbols-chain-tail distance bucket))
                         (proof-value-view symbol)))))
  :hints (("Goal" :induct (proof-dynamic-bucket bucket index size packages)
                  :in-theory (disable proof-symbol-hash proof-package-number
                                      boymoo-model::a64-signed acl2::binary-logand))))

(defthm symbols-root-reaches-listed-symbol
  (let* ((entries (proof-dynamic-entries root packages))
         (buckets (cddr root))
         (size (len buckets))
         (index (symbols-bucket-index symbol size packages))
         (bucket (nth index buckets))
         (distance (symbols-chain-distance symbol bucket)))
    (implies (and entries (member-equal symbol (cdr entries)))
             (and (natp index) (< index size)
                  (natp distance)
                  (equal (cadr (symbols-chain-tail distance bucket))
                         (proof-value-view symbol)))))
  :hints (("Goal"
           :use ((:instance symbols-valid-dynamic-root-fields)
                 (:instance symbols-bucket-index-bounds (size (len (cddr root))))
                 (:instance symbols-dynamic-member-in-selected-bucket
                            (buckets (cddr root)) (first 0) (size (len (cddr root)))
                            (offset (symbols-bucket-index symbol (len (cddr root)) packages)))
                 (:instance symbols-nth-dynamic-bucket-valid
                            (buckets (cddr root)) (first 0) (size (len (cddr root)))
                            (offset (symbols-bucket-index symbol (len (cddr root)) packages)))
                 (:instance symbols-binding-has-finite-chain-distance
                            (bucket (nth (symbols-bucket-index symbol (len (cddr root)) packages)
                                         (cddr root)))
                            (size (len (cddr root)))
                            (index (symbols-bucket-index symbol (len (cddr root)) packages))))
           :in-theory (disable symbols-bucket-index symbols-chain-distance
                               symbols-chain-tail proof-dynamic-bucket proof-dynamic-buckets
                               symbols-bucket-index-bounds symbols-nth-dynamic-bucket-valid
                               symbols-dynamic-member-in-selected-bucket
                               symbols-binding-has-finite-chain-distance))))

(defthm symbols-dynamic-object-is-listed
  (let ((symbol (proof-view-value (proof-object-view object base objects packages machine))))
    (implies (and (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
                  (member-equal object pending)
                  (not (eq (proof-object-zone object) :static))
                  (proof-symbol-object-p object machine))
             (member-equal symbol entries)))
  :hints (("Goal"
           :induct (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
           :in-theory (disable proof-object-view proof-symbol-object-p))))

(defthm symbols-static-object-is-not-dynamic
  (let ((symbol (proof-view-value (proof-object-view object base objects packages machine))))
    (implies (and (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
                  (member-equal object pending)
                  (eq (proof-object-zone object) :static)
                  (proof-symbol-object-p object machine))
             (not (member-equal symbol entries))))
  :hints (("Goal"
           :induct (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
           :in-theory (disable proof-object-view proof-symbol-object-p))))

(defthm symbols-published-root-reaches-dynamic-symbol
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (root (proof-dynamic-view world objects packages))
         (buckets (cddr root))
         (symbol (proof-view-value (proof-object-view object base objects packages machine)))
         (index (symbols-bucket-index symbol (len buckets) packages))
         (bucket (nth index buckets))
         (distance (symbols-chain-distance symbol bucket)))
    (implies (and (proof-heap-p world objects packages)
                  (member-equal object objects)
                  (proof-symbol-object-p object machine)
                  (not (eq (proof-object-zone object) :static)))
             (and (natp index) (< index (len buckets))
                  (natp distance)
                  (equal (cadr (symbols-chain-tail distance bucket))
                         (proof-value-view symbol)))))
  :hints (("Goal"
           :use ((:instance symbols-dynamic-object-is-listed
                            (pending objects) (base (proof-heap-base world))
                            (machine (proof-world-machine world))
                            (entries (cdr (proof-dynamic-entries
                                           (proof-dynamic-view world objects packages)
                                           packages))))
                 (:instance symbols-root-reaches-listed-symbol
                            (root (proof-dynamic-view world objects packages))
                            (symbol (proof-view-value
                                     (proof-object-view object (proof-heap-base world) objects
                                                        packages (proof-world-machine world))))))
           :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p
                               proof-external-objects proof-heap-object-spans-p
                               proof-string-accounting-p proof-stack-prefix
                               proof-dynamic-entries proof-dynamic-view
                               proof-dynamic-symbol-objects-p proof-object-view
                               proof-symbol-object-p symbols-bucket-index
                               symbols-chain-tail symbols-chain-distance
                               symbols-dynamic-object-is-listed
                               symbols-root-reaches-listed-symbol))))

(defthm symbols-collector-return-preserves-bindings
  (implies (proof-collector-return-p kind bytes before after old-objects new-objects packages)
           (equal (proof-dynamic-entries (proof-dynamic-view after new-objects packages)
                                         packages)
                  (proof-dynamic-entries (proof-dynamic-view before old-objects packages)
                                         packages)))
  :hints (("Goal"
           :in-theory (disable proof-dynamic-entries proof-dynamic-view
                               proof-heap-p proof-prefix-preserved-p proof-heap-frame-p
                               proof-frame-return-p proof-reserved-span-p)))
  :rule-classes nil)
