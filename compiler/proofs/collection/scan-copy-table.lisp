(in-package "BOYMOO-PROOFS")

(include-book "scan-memory")
(include-book "relocated-views")

(logic)
(set-verify-guards-eagerness 0)

; The input is a list of original words. A table entry includes the
; full tag because the view relation also checks the kind of pointer.
(defun collection-table-from-assigned-words (words base objects work)
  (if (endp words)
      nil
    (let* ((word (car words))
           (rest (collection-table-from-assigned-words (cdr words) base objects work)))
      (if (and (member-equal (proof-word-tag word) '(0 2))
               (collection-datum-assigned-p word base objects work))
          (acons word (collection-relocate-datum word base objects work) rest)
        rest))))

(local
 (in-theory (disable collection-datum-assigned-p collection-relocate-datum
                     collection-copy-table-p collection-local-copy-p
                     collection-rewritten-word-p collection-read-word proof-load-word
                     proof-world-machine proof-heap-base proof-stack-base proof-stack-top
                     proof-dynamic-root proof-view proof-view-step proof-dynamic-view
                     proof-stack-prefix proof-prefix-preserved-p proof-dynamic-table-preserved-p
                     proof-word-tag boymoo-model::a64-unsigned (:definition ash))))

(defthm collection-assigned-word-table-reuses-one-relocation
  (implies (and (member-equal word words)
                (member-equal (proof-word-tag word) '(0 2))
                (collection-datum-assigned-p word base objects work))
           (equal (assoc-equal word (collection-table-from-assigned-words words base objects work))
                  (cons word (collection-relocate-datum word base objects work))))
  :hints (("Goal" :induct (len words))))

(local
 (defthm collection-original-read-is-load-for-copy-table
   (equal (proof-load-word address (proof-world-machine world))
          (collection-read-word address world))
   :hints (("Goal" :in-theory (enable collection-read-word)))))

(local
 (defthm collection-relocation-keeps-nonpointer-word
   (implies (not (member-equal (proof-word-tag word) '(0 2)))
            (equal (collection-relocate-datum word base objects work) word))
   :hints (("Goal"
            :in-theory (enable collection-relocate-datum collection-movable-reference)))))

(local
 (in-theory (disable collection-table-from-assigned-words)))

(defthm collection-committed-slots-supply-copy-table-edges
  (let ((table (collection-table-from-assigned-words words base objects work)))
    (implies (and (collection-scanned-fields-p count source target base objects original current work)
                  (subsetp-equal (collection-slot-words count source original) words))
             (collection-rewritten-fields-p count source target table
                                           (proof-world-machine original)
                                           (proof-world-machine current))))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-scanned-fields-p count source target base objects original current work)
           :in-theory (enable collection-rewritten-word-p))))

(local
 (defthm collection-one-slot-supplies-its-only-word
   (equal (collection-slot-words 1 address world)
          (list (collection-read-word address world)))
   :hints (("Goal"
            :expand ((collection-slot-words 1 address world)
                     (collection-slot-words 0 (+ address 8) world))))))

(defthm collection-committed-roots-supply-stack-and-table-contracts
  (let* ((base (proof-heap-base original))
         (bottom (proof-stack-base original))
         (top (proof-stack-top original))
         (count (ash (- top bottom) -3))
         (table (collection-table-from-assigned-words words base objects work)))
    (implies (and (equal (proof-heap-base current) base)
                  (equal (proof-stack-base current) bottom)
                  (<= top (proof-stack-top current))
                  (proof-stack-prefix top original objects packages)
                  (proof-dynamic-view original objects packages)
                  (collection-copy-table-p table table base objects new-objects
                                           (proof-world-machine original) (proof-world-machine current))
                  (collection-scanned-fields-p count bottom bottom base objects original current work)
                  (collection-scanned-fields-p 1 (+ base 24) (+ base 24)
                                               base objects original current work)
                  (subsetp-equal (collection-slot-words count bottom original) words)
                  (member-equal (proof-dynamic-root base (proof-world-machine original)) words))
             (and (proof-prefix-preserved-p top original current objects new-objects packages)
                  (proof-dynamic-table-preserved-p nil original current objects new-objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-committed-slots-supply-copy-table-edges
                            (count (ash (- (proof-stack-top original) (proof-stack-base original)) -3))
                            (source (proof-stack-base original)) (target (proof-stack-base original))
                            (base (proof-heap-base original)))
                 (:instance collection-committed-slots-supply-copy-table-edges
                            (count 1) (source (+ (proof-heap-base original) 24))
                            (target (+ (proof-heap-base original) 24)) (base (proof-heap-base original)))
                 (:instance collection-local-copies-establish-stack-and-table-contracts
                            (before original) (after current) (top (proof-stack-top original))
                            (old-objects objects)
                            (table (collection-table-from-assigned-words words (proof-heap-base original)
                                                                         objects work))))
           :in-theory (enable proof-dynamic-root))))

(local
 (in-theory (disable collection-finish-scan collection-source-pending-p
                     collection-cell-queue collection-header-queue collection-forwarding
                     collection-copy-field-offset collection-copy-field-count collection-copy-is-raw-p
                     collection-copy-payload-observed-p collection-scanned-fields-p
                     proof-pointer-address proof-header-type proof-header-size)))

(local
 (defthm collection-completed-scan-has-no-pending-source
   (not (collection-source-pending-p source (collection-finish-scan work)))
   :hints (("Goal" :in-theory (enable collection-source-pending-p)))))

(defthm collection-completed-copy-observation-supplies-rewritten-fields
  (let* ((done (collection-finish-scan work))
         (entry (assoc-equal source (collection-forwarding done)))
         (header (collection-read-word source original))
         (offset (collection-copy-field-offset kind))
         (count (collection-copy-field-count kind header))
         (table (collection-table-from-assigned-words words base objects done)))
    (implies (and entry (not (collection-copy-is-raw-p kind header))
                  (collection-copy-payload-observed-p source kind base objects original current done)
                  (subsetp-equal (collection-slot-words count (+ source offset) original) words))
             (collection-rewritten-fields-p count (+ source offset) (+ (cdr entry) offset) table
                                           (proof-world-machine original) (proof-world-machine current))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-committed-slots-supply-copy-table-edges
                            (work (collection-finish-scan work))
                            (count (collection-copy-field-count kind (collection-read-word source original)))
                            (source (+ source (collection-copy-field-offset kind)))
                            (target (+ (cdr (assoc-equal source (collection-forwarding (collection-finish-scan work))))
                                       (collection-copy-field-offset kind)))))
           :in-theory (e/d (collection-copy-payload-observed-p)
                            (collection-rewritten-fields-p collection-slot-words)))))

(defthm collection-completed-cons-observation-validates-local-copy
  (let* ((source (proof-pointer-address word base))
         (target (proof-pointer-address copy base))
         (old (assoc-equal source objects))
         (new (assoc-equal target new-objects))
         (done (collection-finish-scan work))
         (table (collection-table-from-assigned-words words base objects done)))
    (implies (and (unsigned-byte-p 64 word) (unsigned-byte-p 64 copy)
                  (not (oddp word)) (not (oddp copy))
                  (equal (proof-word-tag word) 0) (equal (proof-word-tag copy) 0)
                  old new (natp (proof-object-rank old))
                  (equal (proof-object-rank new) (proof-object-rank old))
                  (eq (proof-object-kind old) :cons) (eq (proof-object-kind new) :cons)
                  (proof-span-p source 16) (proof-span-p target 16)
                  (equal (assoc-equal source (collection-forwarding done)) (cons source target))
                  (collection-copy-payload-observed-p source :cons base objects original current done)
                  (subsetp-equal (collection-slot-words 2 source original) words))
             (collection-local-copy-p word copy table base objects new-objects
                                      (proof-world-machine original) (proof-world-machine current))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-completed-copy-observation-supplies-rewritten-fields
                            (kind :cons) (source (proof-pointer-address word base))))
           :in-theory (e/d (collection-local-copy-p collection-copy-field-count
                                                     collection-copy-field-offset collection-copy-is-raw-p)
                            (collection-rewritten-fields-p collection-slot-words oddp)))))

(defthm collection-completed-reference-header-observation-validates-local-copy
  (let* ((source (proof-pointer-address word base))
         (target (proof-pointer-address copy base))
         (old (assoc-equal source objects))
         (new (assoc-equal target new-objects))
         (done (collection-finish-scan work))
         (header (collection-read-word source original))
         (type (proof-header-type header))
         (size (proof-header-size header))
         (count (collection-copy-field-count :header header))
         (table (collection-table-from-assigned-words words base objects done)))
    (implies (and (unsigned-byte-p 64 word) (unsigned-byte-p 64 copy)
                  (not (oddp word)) (not (oddp copy))
                  (equal (proof-word-tag word) 2) (equal (proof-word-tag copy) 2)
                  old new (natp (proof-object-rank old))
                  (equal (proof-object-rank new) (proof-object-rank old))
                  (eq (proof-object-kind old) :header) (eq (proof-object-kind new) :header)
                  (proof-span-p source (+ 8 size)) (proof-span-p target (+ 8 size))
                  (member-equal type '(2 4 5 6))
                  (if (equal type 6)
                      (and (equal (mod size 8) 0) (equal count (ash size -3)))
                    (and (equal size 16) (equal count 2)))
                  (equal (assoc-equal source (collection-forwarding done)) (cons source target))
                  (collection-copy-payload-observed-p source :header base objects original current done)
                  (subsetp-equal (collection-slot-words count (+ source 8) original) words))
             (collection-local-copy-p word copy table base objects new-objects
                                      (proof-world-machine original) (proof-world-machine current))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-completed-copy-observation-supplies-rewritten-fields
                            (kind :header) (source (proof-pointer-address word base))))
           :in-theory (e/d (collection-local-copy-p collection-copy-field-offset collection-copy-is-raw-p
                                                     collection-copy-payload-observed-p)
                            (collection-rewritten-fields-p collection-slot-words oddp mod)))))
