(in-package "BOYMOO-PROOFS")

(include-book "package-layout")
(include-book "image")

(logic)
(set-verify-guards-eagerness 0)

; Allocation chunks are stored in reverse order. A retained suffix is
; an unchanged initial segment of the serialized allocation bytes.
(defun data-retained-chunks-p (earlier later)
  (or (equal earlier later)
      (and (consp later) (data-retained-chunks-p earlier (cdr later)))))

(defthm data-retaining-the-same-chunks
  (data-retained-chunks-p chunks chunks))

(defthm data-prepending-a-chunk-retains-older-chunks
  (implies (data-retained-chunks-p earlier later)
           (data-retained-chunks-p earlier (cons chunk later))))

(local
 (in-theory (disable data-retained-chunks-p data-state-sized-p data-block-sized-p
                     boymoo-compiler::index-get boymoo-compiler::index-set
                     boymoo-compiler::table-get boymoo-compiler::table-put
                     boymoo-compiler::decode-part boymoo-compiler::decode-symbol-part
                     boymoo-compiler::data-integer-value boymoo-compiler::data-integer-limbs
                     boymoo-compiler::symbol-separator boymoo-compiler::find-char
                     boymoo-compiler::read-lines boymoo-compiler::aligned-size
                     boymoo-compiler::hex-byte char length ash subseq)))

(defthm data-word-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (boymoo-compiler::data-word word block)))))

(defthm data-text-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-text type text block))))))

(defthm data-fields-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-fields type first second block))))))

(defthm data-cell-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-cell first second block))))))

(local
 (in-theory (disable boymoo-compiler::data-word boymoo-compiler::data-text
                     boymoo-compiler::data-fields boymoo-compiler::data-cell)))

(defthm data-words-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (boymoo-compiler::data-words words block)))))

(defthm data-list-cells-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-list-cells words last block))))))

(defthm data-vector-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-vector words block))))))

(defthm data-bucket-vector-allocation-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (boymoo-compiler::data-bucket-vector tree bits block)))))

(local
 (in-theory (disable boymoo-compiler::data-words boymoo-compiler::data-list-cells
                     boymoo-compiler::data-vector boymoo-compiler::data-bucket-vector)))

(defthm data-write-integer-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier
                                   (cdr (mv-nth 1 (boymoo-compiler::data-write-integer value text-length block))))))

(local (in-theory (disable boymoo-compiler::data-write-integer)))

(defthm data-rational-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-rational text block))))))

(local (in-theory (disable boymoo-compiler::data-rational)))

(defthm data-number-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-retained-chunks-p earlier (cdr (mv-nth 1 (boymoo-compiler::data-number text block))))))

(local (in-theory (disable boymoo-compiler::data-number)))

(defun data-state-retains-chunks-p (earlier state-data)
  (data-retained-chunks-p earlier (cdr (boymoo-compiler::data-block state-data))))

(defthm data-block-replacement-retains-chunks
  (implies (data-retained-chunks-p earlier (cdr block))
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-with-block block state-data))))

(defthm data-remember-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-remember text entry state-data))))

(defthm data-bucket-add-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-bucket-add number name name-word symbol-word
                                                                               state-data))))

(local
 (defthm composite-state-retains-its-block-chunks
   (equal (data-state-retains-chunks-p earlier (list* names constants buckets block))
          (data-retained-chunks-p earlier (cdr block)))))

(local
 (defthm retained-state-has-retained-block-chunks
   (implies (data-state-retains-chunks-p earlier state-data)
            (data-retained-chunks-p earlier (cddddr state-data)))))

(local
 (defthm replacing-only-the-name-table-retains-the-same-chunks
   (equal (data-state-retains-chunks-p earlier (cons names (cdr state-data)))
          (data-state-retains-chunks-p earlier state-data))))

(local (in-theory (disable data-state-retains-chunks-p)))

(defthm data-intern-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (mv-nth 2 (boymoo-compiler::data-intern number name state-data))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-bucket-add))))

(local
 (in-theory (disable boymoo-compiler::data-bucket-add boymoo-compiler::data-intern
                     boymoo-compiler::data-remember)))

(defthm data-symbol-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (mv-nth 1 (boymoo-compiler::data-symbol text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-symbol)))

(defthm data-atom-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (mv-nth 1 (boymoo-compiler::data-atom text packages state-data)))))

(local (in-theory (disable boymoo-compiler::data-atom)))

(local
 (defthm datum-pass-retains-chunks
   (implies (data-state-retains-chunks-p earlier state-data)
            (data-state-retains-chunks-p
             earlier (mv-nth 1 (if (eq kind :datum) (boymoo-compiler::data-datum parsed packages state-data)
                                 (boymoo-compiler::data-list-datum parsed packages state-data reversed)))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed)))))

(defthm data-datum-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data))))
  :hints (("Goal" :use ((:instance datum-pass-retains-chunks (kind :datum) (reversed nil)))
                  :in-theory (disable boymoo-compiler::data-datum))))

(local (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum)))

(defthm data-constant-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-constant text packages state-data))))

(defthm data-note-symbol-retains-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-note-symbol text packages state-data))))

(local (in-theory (disable boymoo-compiler::data-note-symbol boymoo-compiler::data-constant)))

(defthm data-formals-retain-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-formals formals packages state-data))))

(local (in-theory (disable boymoo-compiler::data-formals boymoo-compiler::declaration-list)))

(local
 (defthm term-pass-retains-chunks
   (implies (and (data-state-retains-chunks-p earlier state-data) (data-term-storage-input-p kind parsed depth))
            (data-state-retains-chunks-p
             earlier (if (eq kind :term) (boymoo-compiler::data-term parsed packages state-data depth)
                       (boymoo-compiler::data-terms parsed packages state-data depth))))
   :rule-classes nil
   :hints (("Goal" :induct (data-term-state-induction kind parsed packages state-data depth)
                   :in-theory (disable data-formals-storage-input-p data-symbol-storage-input-p
                                       data-constant-storage-input-p)))))

(defthm data-term-retains-chunks
  (implies (and (data-state-retains-chunks-p earlier state-data) (data-term-storage-input-p :term parsed depth))
           (data-state-retains-chunks-p earlier (boymoo-compiler::data-term parsed packages state-data depth)))
  :hints (("Goal" :use ((:instance term-pass-retains-chunks (kind :term)))
                  :in-theory (disable boymoo-compiler::data-term data-term-storage-input-p))))

(local
 (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-storage-input-p)))

(defthm data-definitions-retain-chunks
  (implies (and (data-state-retains-chunks-p earlier state-data) (data-definitions-storage-input-p definitions))
           (data-state-retains-chunks-p earlier
                                       (boymoo-compiler::data-definitions definitions packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-definitions definitions packages state-data)
                  :in-theory (disable data-formals-storage-input-p data-symbol-storage-input-p))))

(defthm data-program-symbols-retain-chunks
  (implies (and (data-state-retains-chunks-p earlier state-data) (data-program-storage-input-p lines))
           (data-state-retains-chunks-p earlier
                                       (boymoo-compiler::data-program-symbols lines packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-program-symbols lines packages state-data)
                  :in-theory (disable boymoo-compiler::data-definitions data-definitions-storage-input-p
                                      data-datum-storage-input-p data-formals-storage-input-p))))

(defthm data-imports-retain-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p
            earlier (mv-nth 1 (boymoo-compiler::data-imports imports number packages common-lisp state-data reversed)))))

(local (in-theory (disable boymoo-compiler::data-imports)))

(defthm data-package-vectors-retain-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p
            earlier (mv-nth 1 (boymoo-compiler::data-package-vectors names packages declarations state-data reversed)))))

(local (in-theory (disable boymoo-compiler::data-package-vectors)))

(defthm data-package-declarations-retain-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p
            earlier (mv-nth 1 (boymoo-compiler::data-package-declarations
                               lines packages declared declarations state-data names)))))

(defthm data-packages-retain-chunks
  (implies (data-state-retains-chunks-p earlier state-data)
           (data-state-retains-chunks-p
            earlier (mv-nth 1 (boymoo-compiler::data-packages lines number packages state-data reversed))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-package-declarations))))

(defthm data-initial-name-chunks-are-retained
  (data-state-retains-chunks-p '("T" 257 "NIL" 769) (mv-nth 2 (boymoo-compiler::data-initial package)))
  :hints (("Goal" :in-theory (e/d (boymoo-compiler::data-text boymoo-compiler::data-word)
                                 (boymoo-compiler::data-bucket-add)))))

(defthmd data-build-retains-initial-name-chunks
  (implies (and (data-program-storage-input-p lines)
                (boymoo-compiler::index-get
                 "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
           (data-retained-chunks-p '("T" 257 "NIL" 769) (mv-nth 1 (data-image-parts lines package-lines))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-initial boymoo-compiler::data-package-numbers
                                      boymoo-compiler::data-packages boymoo-compiler::data-program-symbols
                                      data-program-storage-input-p))))

(local
 (defthm chunks-serialize-to-a-true-list
   (true-listp (data-chunks-characters reversed))
   :hints (("Goal" :use data-chunks-characters-are-characters
                   :in-theory (disable data-chunks-characters)))))

(defthmd data-placed-retained-chunks
  (implies (and (data-retained-chunks-p earlier later) (integerp address)
                (data-placed-characters-p (data-chunks-characters later) address machine))
           (data-placed-characters-p (data-chunks-characters earlier) address machine))
  :hints (("Goal" :induct (data-retained-chunks-p earlier later)
                  :in-theory (e/d (data-retained-chunks-p)
                                 (data-placed-characters-p data-chunk-characters)))))

(defthmd data-placed-retained-builder-allocation
  (implies (and (integerp base) (data-block-sized-p before 80)
                (data-retained-chunks-p (boymoo-compiler::reverse-onto allocated (cdr before)) body)
                (data-placed-characters-p (data-chunks-characters body) (+ base 80) machine))
           (data-placed-characters-p (data-forward-chunk-characters allocated) (+ base (car before)) machine))
  :hints (("Goal" :use ((:instance data-placed-retained-chunks
                                   (earlier (boymoo-compiler::reverse-onto allocated (cdr before)))
                                   (later body) (address (+ base 80)))
                        (:instance data-placed-allocation-chunks
                                   (earlier (cdr before)) (later nil) (address (+ base 80))))
                  :in-theory (e/d (data-block-sized-p)
                                 (data-placed-characters-p data-chunks-characters data-chunks-size
                                  data-forward-chunk-characters boymoo-compiler::reverse-onto)))))

(defthmd data-build-places-initial-name-chunks
  (let ((image (car (boymoo-compiler::data-build lines package-lines))))
    (implies (and (proof-image-at-p image base machine) (data-program-storage-input-p lines)
                  (boymoo-compiler::index-get
                   "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
             (data-placed-characters-p (data-chunks-characters '("T" 257 "NIL" 769)) (+ base 80) machine)))
  :hints (("Goal" :use (data-build-places-body-chunks data-build-retains-initial-name-chunks
                        (:instance data-placed-retained-chunks (earlier '("T" 257 "NIL" 769))
                                   (later (mv-nth 1 (data-image-parts lines package-lines)))
                                   (address (+ base 80))))
                  :in-theory (disable boymoo-compiler::data-build data-image-parts
                                      data-chunks-characters data-placed-characters-p
                                      data-program-storage-input-p boymoo-compiler::data-package-numbers
                                      proof-fragments-at-p proof-fragments-size proof-fragments-p))))
