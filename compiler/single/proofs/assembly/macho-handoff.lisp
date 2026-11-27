(in-package "BOYMOO-PROOFS")

(include-book "macho-signature")
(include-book "machine-invariant")

(logic)
(set-verify-guards-eagerness 0)

; Use the read view only for data accesses. Instruction fetch continues
; to use the original regions, including the read-only mode for linkedit.
(defun assembly-macho-data-regions (regions)
  (if (atom regions)
      nil
    (cons (if (eq (caddar regions) :r)
              (proof-region (caar regions) (cadar regions) :rx)
            (car regions))
          (assembly-macho-data-regions (cdr regions)))))

(defthm assembly-macho-data-regions-preserve-write-permission
  (equal (proof-covered-p address count :write (assembly-macho-data-regions regions))
         (proof-covered-p address count :write regions))
  :hints (("Goal" :induct (assembly-macho-data-regions regions)
                  :in-theory (disable proof-subspan-p))))

(defthm assembly-macho-data-regions-keep-standard-mappings
  (implies (proof-regions-p regions)
           (equal (assembly-macho-data-regions regions) regions))
  :hints (("Goal" :induct (proof-regions-p regions)
                  :in-theory (disable proof-region-disjoint-p))))

(defun assembly-macho-linkedit-span (file)
  (proof-file-le 8 208 file))

(defun assembly-macho-handoff-input-p (file base machine regions input)
  (let* ((text-size (assembly-macho-text-size file))
         (linkedit-size (assembly-macho-linkedit-span file))
         (size (+ text-size linkedit-size)))
    (and (assembly-macho-file-p file)
         (assembly-macho-loader-input-p text-size base machine regions input)
         (assembly-register-file-p machine)
         (posp linkedit-size)
         (proof-span-p base size)
         (<= (length file) size)
         (proof-region-disjoint-p base (+ base size) regions))))

(defun assembly-load-macho-handoff (file base machine regions input replies)
  (if (assembly-macho-handoff-input-p file base machine regions input)
      (let* ((text-end (+ base (assembly-macho-text-size file)))
             (end (+ text-end (assembly-macho-linkedit-span file))))
        (proof-world
         (boymoo-model::a64-set-pc
          (+ base (assembly-macho-entry-offset file))
          (assembly-load-cleared-file file base end machine))
         (list* (proof-region base text-end :rx) (proof-region text-end end :r) regions)
         *assembly-macho-page-size*
         (proof-string-bytes (coerce input 'list)) nil nil replies nil))
    nil))

(local (in-theory (disable proof-image-p proof-file-le ash floor mod length
                           assembly-macho-text-size assembly-macho-file-p
                           assembly-macho-entry-offset assembly-macho-linkedit-span
                           assembly-load-cleared-file assembly-register-file-p
                           boymoo-model::a64-load boymoo-model::a64-unsigned
                           proof-clear-memory proof-overlay-bytes proof-string-bytes)))

(local
 (defthm assembly-macho-handoff-entry-fits-in-address
   (implies (and (assembly-macho-file-p file)
                 (proof-span-p base (assembly-macho-text-size file)))
            (unsigned-byte-p 64 (+ base (assembly-macho-entry-offset file))))
   :hints (("Goal" :in-theory (enable assembly-macho-file-p)))))

(local
 (defthm assembly-macho-file-is-string
   (implies (assembly-macho-file-p file) (stringp file))
   :hints (("Goal" :in-theory (enable assembly-macho-file-p)))))

(local
 (defthm assembly-handoff-byte-after-pc-change
   (equal (boymoo-model::a64-load width address (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-load width address machine))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                   (boymoo-model::a64-read-bytes))))))

(local
 (defthm assembly-handoff-characters-at-after-pc-change
   (equal (assembly-characters-at-p chars address (boymoo-model::a64-set-pc pc machine))
          (assembly-characters-at-p chars address machine))
   :hints (("Goal" :induct (assembly-characters-at-p chars address machine)
                   :in-theory (disable boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-handoff-pc-after-pc-change
   (implies (unsigned-byte-p 64 pc)
            (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine)) pc))))

(local
 (defthm assembly-handoff-registers-after-pc-change
   (and (equal (boymoo-model::a64-registers (boymoo-model::a64-set-pc pc machine))
               (boymoo-model::a64-registers machine))
        (equal (boymoo-model::a64-sp (boymoo-model::a64-set-pc pc machine))
               (boymoo-model::a64-sp machine))
        (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-pc pc machine))
               (boymoo-model::a64-nzcv machine)))))

(local
 (defthm assembly-handoff-registers-after-loading
   (and (equal (boymoo-model::a64-registers (assembly-load-cleared-file file base end machine))
               (boymoo-model::a64-registers machine))
        (equal (boymoo-model::a64-sp (assembly-load-cleared-file file base end machine))
               (boymoo-model::a64-sp machine))
        (equal (boymoo-model::a64-nzcv (assembly-load-cleared-file file base end machine))
               (boymoo-model::a64-nzcv machine)))
   :hints (("Goal" :in-theory (enable assembly-load-cleared-file)))))

(local (in-theory (disable assembly-characters-at-p
                           boymoo-model::a64-set-pc boymoo-model::a64-pc
                           boymoo-model::a64-registers boymoo-model::a64-sp boymoo-model::a64-nzcv
                           assembly-macho-loader-input-p)))

(defthm assembly-macho-handoff-loads-complete-file
  (let* ((world (assembly-load-macho-handoff file base machine regions input replies))
         (loaded (proof-world-machine world))
         (entry (+ base (assembly-macho-entry-offset file)))
         (text-end (+ base (assembly-macho-text-size file)))
         (end (+ text-end (assembly-macho-linkedit-span file))))
    (implies (assembly-macho-handoff-input-p file base machine regions input)
             (and (assembly-characters-at-p (coerce file 'list) base loaded)
                  (equal (proof-world-pc world) entry)
                  (equal (proof-world-regions world)
                         (list* (proof-region base text-end :rx) (proof-region text-end end :r)
                                regions))
                  (equal (boymoo-model::a64-registers loaded) (boymoo-model::a64-registers machine))
                  (equal (boymoo-model::a64-sp loaded) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-nzcv loaded) (boymoo-model::a64-nzcv machine))
                  (equal (proof-world-replies world) replies)
                  (not (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance assembly-loaded-file-places-characters
                            (clear-end (+ base (assembly-macho-text-size file)
                                          (assembly-macho-linkedit-span file)))))
           :in-theory (enable assembly-macho-loader-input-p)))
  :rule-classes nil)

(defthm assembly-macho-handoff-zeroes-linkedit-tail
  (let* ((world (assembly-load-macho-handoff file base machine regions input replies))
         (end (+ base (assembly-macho-text-size file) (assembly-macho-linkedit-span file))))
    (implies (and (assembly-macho-handoff-input-p file base machine regions input)
                  (unsigned-byte-p 64 address)
                  (<= (+ base (length file)) address)
                  (< address end))
             (equal (boymoo-model::a64-load 1 address (proof-world-machine world)) 0)))
  :hints (("Goal" :in-theory (enable assembly-macho-loader-input-p))))

(local
 (defthm assembly-uncovered-disjoint-span
   (implies (and (posp size) (proof-region-disjoint-p base (+ base size) regions))
            (not (proof-covered-p base size access regions)))
   :hints (("Goal" :induct (proof-covered-p base size access regions)))))

(local
 (defthm assembly-macho-disjoint-subspan
   (implies (and (<= base address) (<= (+ address count) end)
                 (proof-region-disjoint-p base end regions))
            (proof-region-disjoint-p address (+ address count) regions))
   :hints (("Goal" :induct (proof-region-disjoint-p base end regions)))
   :rule-classes nil))

(defthm assembly-macho-linkedit-is-read-only
  (let* ((world (assembly-load-macho-handoff file base machine regions input replies))
         (loaded-regions (proof-world-regions world))
         (start (+ base (assembly-macho-text-size file)))
         (end (+ start (assembly-macho-linkedit-span file))))
    (implies (and (assembly-macho-handoff-input-p file base machine regions input)
                  (posp count) (proof-subspan-p address count start end))
             (and (proof-covered-p address count :read (assembly-macho-data-regions loaded-regions))
                  (not (proof-covered-p address count :write (assembly-macho-data-regions loaded-regions)))
                  (not (proof-covered-p address count :execute loaded-regions)))))
  :hints (("Goal"
           :use ((:instance assembly-macho-disjoint-subspan
                            (end (+ base (assembly-macho-text-size file)
                                      (assembly-macho-linkedit-span file)))))
           :in-theory (enable assembly-macho-loader-input-p)))
  :rule-classes nil)

(local
 (defun assembly-macho-placed-prefix-induction (count chars address)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       nil
     (cons (cons (car chars) address)
           (assembly-macho-placed-prefix-induction (1- count) (cdr chars) (+ 1 (ifix address)))))))

(local
 (defthm assembly-macho-placed-characters-prefix
   (implies (and (assembly-characters-at-p chars address machine) (natp count) (<= count (len chars)))
            (assembly-characters-at-p (take count chars) address machine))
   :hints (("Goal" :induct (assembly-macho-placed-prefix-induction count chars address)
                   :in-theory (enable assembly-characters-at-p)))))

(local
 (defthm assembly-handoff-file-length
   (implies (stringp file)
            (equal (len (coerce file 'list)) (length file)))
   :hints (("Goal" :in-theory (enable length)))))

(local
 (defthm assembly-macho-handoff-file-geometry
   (implies (assembly-macho-handoff-input-p file base machine regions input)
            (and (natp base)
                 (integerp (* 1/16384 base))
                 (proof-span-p base (assembly-macho-text-size file))
                 (<= (assembly-macho-text-size file) (length file))))
   :hints (("Goal"
            :in-theory (e/d (assembly-macho-file-p assembly-macho-loader-input-p)
                            (assembly-macho-header-p boymoo-compiler::macho-signature-size))))))

(local
 (defthm assembly-macho-text-size-covers-image
   (implies (proof-image-p image)
            (<= (+ *assembly-macho-code-offset* (car image))
                (assembly-macho-image-text-size image)))
   :hints (("Goal"
            :use ((:instance assembly-macho-segment-rounding
                             (bytes (+ *assembly-macho-code-offset* (car image)))))
            :in-theory (enable proof-image-p)))))

(local
 (defthm assembly-macho-sized-image-components
   (implies (proof-image-p image)
            (and (natp (car image))
                 (proof-fragments-p (cdr image))))
   :hints (("Goal" :in-theory (enable proof-image-p)))
   :rule-classes (:forward-chaining)))

(local (in-theory (disable assembly-load-macho-handoff
                           boymoo-compiler::macho-image-executable
                           assembly-macho-image-text-size
                           assembly-macho-slot-count
                           assembly-macho-image-entry-p)))

(local
 (defthm assembly-macho-handoff-covers-code-subspan
   (implies (and (assembly-macho-handoff-input-p file base machine regions input)
                 (proof-subspan-p address count base (+ base (assembly-macho-text-size file))))
            (proof-covered-p address count :execute
                             (proof-world-regions
                              (assembly-load-macho-handoff file base machine regions input replies))))
   :hints (("Goal" :in-theory (enable assembly-load-macho-handoff)))))

(defthm assembly-macho-handoff-places-signature
  (let* ((world (assembly-load-macho-handoff file base machine regions input replies))
         (size (assembly-macho-text-size file)))
    (implies (assembly-macho-handoff-input-p file base machine regions input)
             (assembly-characters-at-p (nthcdr size (coerce file 'list)) (+ base size)
                                       (proof-world-machine world))))
  :hints (("Goal"
           :use (assembly-macho-handoff-loads-complete-file
                 (:instance assembly-placed-characters-after-prefix
                            (chars (coerce file 'list)) (count (assembly-macho-text-size file))
                            (address base)
                            (machine (proof-world-machine
                                      (assembly-load-macho-handoff file base machine regions input replies)))))
           :in-theory (enable assembly-macho-file-p assembly-macho-loader-input-p)))
  :rule-classes nil)

(defthm assembly-macho-handoff-places-assembly-image
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (world (assembly-load-macho-handoff file base machine regions input replies))
         (loaded (proof-world-machine world))
         (address (+ base *assembly-macho-code-offset*)))
    (implies (and (assembly-macho-image-entry-p image entry)
                  (assembly-macho-handoff-input-p file base machine regions input))
             (and (proof-image-at-p image address loaded)
                  (proof-covered-p address (car image) :execute (proof-world-regions world)))))
  :hints (("Goal"
           :use (assembly-macho-text-file-contents
                 assembly-macho-emitted-file-p
                 assembly-macho-text-size-covers-image
                 (:instance assembly-macho-handoff-file-geometry
                            (file (boymoo-compiler::macho-image-executable image entry)))
                 (:instance assembly-macho-handoff-covers-code-subspan
                            (file (boymoo-compiler::macho-image-executable image entry))
                            (address (+ base *assembly-macho-code-offset*)) (count (car image)))
                 (:instance assembly-macho-handoff-loads-complete-file
                            (file (boymoo-compiler::macho-image-executable image entry)))
                 (:instance assembly-macho-placed-characters-prefix
                            (chars (coerce (boymoo-compiler::macho-image-executable image entry) 'list))
                            (count (assembly-macho-image-text-size image)) (address base)
                            (machine (proof-world-machine
                                      (assembly-load-macho-handoff
                                       (boymoo-compiler::macho-image-executable image entry)
                                       base machine regions input replies))))
                 (:instance assembly-placed-characters-after-prefix
                            (chars (take (assembly-macho-image-text-size image)
                                         (coerce (boymoo-compiler::macho-image-executable image entry) 'list)))
                            (count *assembly-macho-code-offset*) (address base)
                            (machine (proof-world-machine
                                      (assembly-load-macho-handoff
                                       (boymoo-compiler::macho-image-executable image entry)
                                       base machine regions input replies))))
                 (:instance assembly-fragments-from-placed-characters
                            (fragments (cdr image)) (address (+ base *assembly-macho-code-offset*))
                            (machine (proof-world-machine
                                      (assembly-load-macho-handoff
                                       (boymoo-compiler::macho-image-executable image entry)
                                       base machine regions input replies)))))
           :in-theory (e/d (assembly-macho-image-entry-p)
                           (assembly-macho-handoff-input-p assembly-macho-header-p
                            assembly-macho-text-size-covers-image assembly-macho-handoff-file-geometry
                            assembly-macho-handoff-covers-code-subspan
                            proof-fragments-at-p assembly-fragment-characters assembly-zero-characters
                            assembly-macho-placed-characters-prefix take nthcdr))))
  :rule-classes nil)

(defthm assembly-macho-handoff-links-assembled-image
  (mv-let (image offset)
    (boymoo-compiler::a64-assemble-image items entry)
    (let* ((file (boymoo-compiler::macho-image-executable image offset))
           (world (assembly-load-macho-handoff file base machine regions input replies))
           (address (+ base *assembly-macho-code-offset*)))
      (implies (and (assembly-macho-image-entry-p image offset)
                    (assembly-macho-handoff-input-p file base machine regions input))
               (and (proof-linked-image-p items entry address world)
                    (equal (proof-world-pc world) (+ address offset))
                    (not (proof-world-stop world))))))
  :hints (("Goal"
           :use ((:instance assembly-macho-handoff-places-assembly-image
                            (image (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry)))
                            (entry (mv-nth 1 (boymoo-compiler::a64-assemble-image items entry))))
                 (:instance assembly-macho-emitted-file-p
                            (image (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry)))
                            (entry (mv-nth 1 (boymoo-compiler::a64-assemble-image items entry))))
                 (:instance assembly-macho-handoff-loads-complete-file
                            (file (boymoo-compiler::macho-image-executable
                                   (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))
                                   (mv-nth 1 (boymoo-compiler::a64-assemble-image items entry)))))
                 (:instance assembly-macho-handoff-file-geometry
                            (file (boymoo-compiler::macho-image-executable
                                   (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))
                                   (mv-nth 1 (boymoo-compiler::a64-assemble-image items entry)))))
                 assembly-macho-code-base-alignment)
           :in-theory (e/d (assembly-macho-image-entry-p)
                           (boymoo-compiler::a64-assemble-image proof-image-at-p proof-covered-p
                            assembly-macho-handoff-input-p assembly-macho-handoff-file-geometry
                            assembly-macho-code-base-alignment))))
  :rule-classes nil)
