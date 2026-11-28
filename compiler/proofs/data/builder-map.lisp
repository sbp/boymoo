(in-package "BOYMOO-PROOFS")

(include-book "build-allocation-trace")
(include-book "static-agreement")

(logic)
(set-verify-guards-eagerness 0)

(defun data-build-allocation-records (lines package-lines base)
  (data-allocation-trace-map (data-build-allocation-trace lines package-lines) 32 base))

(defun data-build-root-words-are-ranked-p (lines package-lines base records)
  (mv-let (header chunks constants) (data-image-parts lines package-lines)
    (declare (ignore chunks))
    (let* ((rank (1+ (nfix (ash (car header) -3))))
           (roots (list *proof-nil* *proof-t* (cadr header) (caddr header)))
           (entries (strip-cdrs (data-table-bindings constants 12))))
      (and header
           (data-ranked-allocation-words-p roots rank base records)
           (data-ranked-allocation-words-p (data-encoded-words entries) rank base records)))))

(defun data-build-allocation-check-p (lines package-lines base)
  (let* ((trace (data-build-allocation-trace lines package-lines))
         (records (data-build-allocation-records lines package-lines base)))
    (and (data-allocation-trace-shapes-p trace)
         (data-trace-references-are-ranked-p trace 32 base records)
         (data-build-root-words-are-ranked-p lines package-lines base records))))

(local
 (in-theory (disable data-image-parts boymoo-compiler::data-build data-build-allocation-trace
                     data-allocation-trace-map data-ranked-word-p proof-load-word ash)))

(local
 (defthm initial-index-tasks-match-their-encoded-entries
   (equal (data-ranked-tasks-p (data-static-constant-work bindings depth) base records machine)
          (data-ranked-allocation-words-p (data-encoded-words (strip-cdrs bindings)) depth base records))))

(local
 (defthm ranked-word-fits-in-64-bits
   (implies (data-ranked-word-p word rank base records) (unsigned-byte-p 64 word))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable data-ranked-word-p)))))

(local
 (defthm one-field-checks-its-loaded-word
   (equal (data-ranked-field-words-p address 1 rank base records machine)
          (data-ranked-word-p (proof-load-word address machine) rank base records))
   :hints (("Goal" :expand ((:free (where) (data-ranked-field-words-p where 0 rank base records machine))
                            (data-ranked-field-words-p address 1 rank base records machine))))))

(local
 (defthm two-fields-check-their-loaded-words
   (equal (data-ranked-field-words-p start 2 rank base records machine)
          (and (data-ranked-word-p (proof-load-word start machine) rank base records)
               (data-ranked-word-p (proof-load-word (+ start 8) machine) rank base records)))
   :hints (("Goal" :expand ((:free (address) (data-ranked-field-words-p address 2 rank base records machine))
                            (:free (address) (data-ranked-field-words-p address 1 rank base records machine))
                            (:free (address) (data-ranked-field-words-p address 0 rank base records machine)))))))

(local
 (defthm root-word-check-agrees-with-initial-worklist
   (let ((image (car (boymoo-compiler::data-build lines package-lines)))
         (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines))))
     (implies (and (data-build-root-words-are-ranked-p lines package-lines base records)
                   (proof-image-at-p image base machine))
              (data-ranked-tasks-p
               (data-static-image-work base (car image) (data-table-bindings constants 12)) base records machine)))
   :hints (("Goal" :use (data-build-image-and-index data-build-fragment-count-agreement
                         (:instance data-build-loads-header-field (field 1))
                         (:instance data-build-loads-header-field (field 2))
                         (:instance ranked-word-fits-in-64-bits
                                    (word (cadr (car (data-image-parts lines package-lines))))
                                    (rank (1+ (nfix (ash (car (car (data-image-parts lines package-lines))) -3)))))
                         (:instance ranked-word-fits-in-64-bits
                                    (word (caddr (car (data-image-parts lines package-lines))))
                                    (rank (1+ (nfix (ash (car (car (data-image-parts lines package-lines))) -3))))))
                   :in-theory (disable data-static-constant-work data-table-bindings data-encoded-words
                                       proof-image-at-p proof-fragments-p proof-fragments-size unsigned-byte-p
                                       data-write-short-word-chunks data-forward-chunk-characters
                                       boymoo-compiler::data-write boymoo-compiler::reverse-onto)))))

(local
 (defthm an-exact-byte-word-multiple-has-an-integer-quotient
   (implies (and (integerp count) (equal bytes (* 8 count))) (integerp (* 1/8 bytes)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 1/8) (acl2::y 8) (acl2::z count)))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm aligned-base-has-an-integer-word-count
   (implies (and (integerp base) (equal (mod base 8) 0)) (integerp (* 1/8 base)))
   :hints (("Goal" :use ((:instance an-exact-byte-word-multiple-has-an-integer-quotient
                                    (bytes base) (count (floor base 8))))
                   :in-theory (e/d (mod) (floor))))))

(local
 (in-theory (disable data-build-root-words-are-ranked-p data-static-image-work data-ranked-tasks-p
                     data-static-image-witness-p data-table-bindings proof-span-p mod)))

(defthmd data-checked-builder-allocations-construct-the-static-witness
  (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (mv-nth 0 (data-before-buckets lines package-lines))
                  (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                  (equal (mod base 8) 0) (data-build-allocation-check-p lines package-lines base))
             (data-static-image-witness-p base image constants machine
                                          (data-build-allocation-records lines package-lines base))))
  :hints (("Goal" :use (data-build-places-allocation-trace-at-offset-32
                        (:instance root-word-check-agrees-with-initial-worklist
                                   (records (data-build-allocation-records lines package-lines base)))
                        (:instance data-placed-allocation-trace-constructs-ranked-image-witness
                                   (trace (data-build-allocation-trace lines package-lines))
                                   (image (car (boymoo-compiler::data-build lines package-lines)))
                                   (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))))
                  :in-theory (e/d (proof-span-p)
                                 (data-allocation-trace-shapes-p data-trace-references-are-ranked-p
                                  data-before-buckets data-placed-characters-p data-program-storage-input-p
                                  data-package-lines-storage-input-p proof-image-p proof-fragments-at-p)))))

(local
 (in-theory (disable data-build-allocation-check-p data-build-allocation-records data-static-image-map)))

(defthmd data-checked-builder-allocations-scan-successfully
  (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
    (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                  (mv-nth 0 (data-before-buckets lines package-lines))
                  (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                  (equal (mod base 8) 0) (data-build-allocation-check-p lines package-lines base))
             (mv-let (ok objects) (data-static-image-map base image constants machine)
               (and ok (data-static-known-records-p objects (data-build-allocation-records lines package-lines base))))))
  :hints (("Goal" :use (data-checked-builder-allocations-construct-the-static-witness
                        (:instance data-static-image-map-succeeds-for-ranked-graph
                                   (image (car (boymoo-compiler::data-build lines package-lines)))
                                   (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))
                                   (witness (data-build-allocation-records lines package-lines base))))
                  :in-theory (disable data-before-buckets proof-image-at-p data-static-known-records-p
                                      data-program-storage-input-p data-package-lines-storage-input-p))))

(defthmd data-checked-builder-allocations-and-views-give-initial-static-heap
  (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
    (let ((records (data-build-allocation-records lines package-lines base)))
      (implies (and (data-program-storage-input-p lines) (data-package-lines-storage-input-p package-lines)
                    (mv-nth 0 (data-before-buckets lines package-lines))
                    (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                    (equal (mod base 8) 0) (data-build-allocation-check-p lines package-lines base)
                    (data-static-views-p base records packages machine))
               (mv-let (ok objects) (data-static-image-map base image constants machine)
                 (and ok (proof-static-initial-p base objects packages machine))))))
  :hints (("Goal" :use (data-checked-builder-allocations-construct-the-static-witness
                        (:instance data-build-initial-static-from-placed-witness
                                   (witness (data-build-allocation-records lines package-lines base))))
                  :in-theory (disable data-before-buckets proof-image-at-p data-static-views-p proof-static-initial-p
                                      data-program-storage-input-p data-package-lines-storage-input-p))))
