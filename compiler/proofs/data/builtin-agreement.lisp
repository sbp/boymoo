(in-package "BOYMOO-PROOFS")

(include-book "builtin-symbols")
(include-book "trace-agreement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::data-build boymoo-compiler::index-get
                     boymoo-compiler::data-package-numbers boymoo-compiler::data-initial
                     boymoo-compiler::data-program-symbols boymoo-compiler::data-packages
                     boymoo-compiler::bucket-get boymoo-compiler::bucket-set
                     data-program-allocation-trace data-packages-allocation-trace
                     data-before-buckets data-ascending-bucket-words data-bucket-for-name
                     proof-image-at-p proof-span-p data-static-image-map
                     data-static-word-present-p data-static-records-children-present-p data-static-known-records-p
                     data-build-allocation-check-p data-program-storage-input-p data-package-lines-storage-input-p
                     data-program-constant-keys-p proof-value-p proof-view mod)))

(defthmd data-build-allocation-records-include-fixed-symbols-and-names
  (implies (and (mv-nth 0 (data-before-buckets lines package-lines)) (integerp base))
           (data-builtin-symbol-records-p truth base (data-build-allocation-records lines package-lines base)))
  :hints (("Goal" :use data-build-common-lisp-number-agrees-with-index
                  :in-theory (enable data-chunk-size))))

(local
 (defthm a-placed-builder-image-includes-the-fixed-objects
   (implies (and (proof-image-at-p (car (boymoo-compiler::data-build lines package-lines)) base machine)
                 (mv-nth 0 (data-before-buckets lines package-lines))
                 (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines))
            (proof-span-p base 112))
   :rule-classes nil
   :hints (("Goal" :use (data-build-body-is-sized-for-storage-input data-build-size-includes-the-bucket-vector)
                   :in-theory (e/d (proof-image-at-p proof-span-p)
                                  (data-block-sized-p proof-image-p proof-fragments-at-p))))))

(local
 (in-theory (disable data-build-allocation-records data-builtin-symbol-records-p
                     data-build-allocation-trace data-allocation-trace-map)))

(defthmd data-placed-builder-records-give-fixed-symbol-values
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (number (mv-nth 0 (data-before-buckets lines package-lines)))
         (package (nth number packages))
         (witness (proof-package-witness package))
         (objects (data-build-allocation-records lines package-lines base)))
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (proof-image-at-p image base machine)
                  number (natp number) (proof-immediate-integer-p number) (< number (len packages))
                  (equal (proof-package-name package) "COMMON-LISP")
                  (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP"))
             (proof-value-p (data-builtin-symbol-word truth) (if truth t nil) base objects packages machine)))
  :hints (("Goal" :use (data-build-allocation-records-include-fixed-symbols-and-names
                        a-placed-builder-image-includes-the-fixed-objects
                        (:instance data-build-view-of-builtin-symbol
                                   (objects (data-build-allocation-records lines package-lines base))))
                  :in-theory (e/d (proof-span-p)
                                 (proof-immediate-integer-p proof-package-name proof-package-witness nth)))))

(defthmd data-checked-builder-allocations-give-fixed-symbol-values
  (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
    (let* ((number (mv-nth 0 (data-before-buckets lines package-lines)))
           (package (nth number packages))
           (witness (proof-package-witness package)))
      (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                    (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                    (equal (mod base 8) 0) (data-build-allocation-check-p lines package-lines base)
                    number (natp number) (proof-immediate-integer-p number) (< number (len packages))
                    (equal (proof-package-name package) "COMMON-LISP")
                    (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP"))
               (mv-let (ok objects) (data-static-image-map base image constants machine)
                 (and ok (proof-value-p (data-builtin-symbol-word truth) (if truth t nil)
                                        base objects packages machine))))))
  :hints (("Goal"
           :use (data-checked-builder-allocations-scan-successfully
                 data-placed-builder-records-give-fixed-symbol-values
                 (:instance data-static-map-on-success-covers-roots
                            (image (car (boymoo-compiler::data-build lines package-lines)))
                            (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines))))
                 (:instance data-static-image-map-on-success-closes-object-children
                            (image (car (boymoo-compiler::data-build lines package-lines)))
                            (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines))))
                 (:instance data-view-agrees-with-witness-map
                            (word (data-builtin-symbol-word truth))
                            (witness (data-build-allocation-records lines package-lines base))
                            (objects (mv-nth 1 (data-static-image-map
                                                base (car (boymoo-compiler::data-build lines package-lines))
                                                (mv-nth 1 (boymoo-compiler::data-build lines package-lines)) machine)))))
           :in-theory (e/d (proof-value-p)
                           (proof-immediate-integer-p proof-package-name proof-package-witness nth)))))

(defthmd data-checked-builder-allocations-agree-on-fixed-constants
  (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
    (let* ((number (mv-nth 0 (data-before-buckets lines package-lines)))
           (package (nth number packages))
           (witness (proof-package-witness package)))
      (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                    (data-program-constant-keys-p lines)
                    (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                    (equal (mod base 8) 0) (data-build-allocation-check-p lines package-lines base)
                    number (natp number) (proof-immediate-integer-p number) (< number (len packages))
                    (equal (proof-package-name package) "COMMON-LISP")
                    (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP"))
               (mv-let (ok objects) (data-static-image-map base image constants machine)
                 (and ok (proof-constant-map-p '(("COMMON-LISP::NIL" . nil) ("COMMON-LISP::T" . t))
                                               constants base objects packages machine))))))
  :hints (("Goal" :use ((:instance data-checked-builder-allocations-give-fixed-symbol-values (truth nil))
                        (:instance data-checked-builder-allocations-give-fixed-symbol-values (truth t))
                        data-build-retains-nil-and-t-index-entries data-build-common-lisp-number-agrees-with-index)
                  :in-theory (disable proof-immediate-integer-p data-table-p
                                      proof-package-name proof-package-witness nth))))

(defun data-static-table-and-object-views-p (base objects packages machine)
  (let* ((package-word (proof-load-word (+ base 8) machine))
         (bucket-word (proof-load-word (+ base 16) machine))
         (buckets (proof-view bucket-word base objects packages machine)))
    (and (proof-packages-p packages)
         (proof-object-map-p objects objects nil base packages machine)
         (equal (proof-view package-word base objects packages machine)
                (cons :vector (proof-package-row-views packages)))
         (eq (car buckets) :vector)
         (proof-static-buckets-p (cdr buckets) 0 packages)
         (proof-home-bindings-p objects base objects packages machine (cdr buckets))
         (proof-package-bindings-p packages 0 (cdr buckets)))))

(defthmd data-placed-builder-table-and-object-views-supply-static-views
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (number (mv-nth 0 (data-before-buckets lines package-lines)))
         (package (nth number packages))
         (witness (proof-package-witness package))
         (objects (data-build-allocation-records lines package-lines base)))
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (proof-image-at-p image base machine)
                  number (natp number) (proof-immediate-integer-p number) (< number (len packages))
                  (equal (proof-package-name package) "COMMON-LISP")
                  (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP")
                  (data-static-table-and-object-views-p base objects packages machine))
             (data-static-views-p base objects packages machine)))
  :hints (("Goal" :use ((:instance data-placed-builder-records-give-fixed-symbol-values (truth nil))
                        (:instance data-placed-builder-records-give-fixed-symbol-values (truth t)))
                  :in-theory (disable proof-immediate-integer-p proof-package-name proof-package-witness
                                      proof-object-map-p proof-static-buckets-p proof-packages-p
                                      proof-home-bindings-p proof-package-bindings-p proof-package-row-views
                                      proof-load-word nth))))
