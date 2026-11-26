(in-package "BOYMOO-PROOFS")

(include-book "macho-image")
(include-book "image-loading")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-macho-file-p (file)
  (let* ((size (assembly-macho-text-size file))
         (entry (assembly-macho-entry-offset file))
         (signature-size (assembly-macho-signature-size file)))
    (and (assembly-macho-header-p file size (- entry *assembly-macho-code-offset*) signature-size)
         (natp size) (< size (expt 2 32))
         (integerp (* 1/16384 size))
         (proof-subspan-p entry 4 *assembly-macho-code-offset* size)
         (equal (mod entry 4) 0)
         (equal signature-size
                (boymoo-compiler::macho-signature-size (assembly-macho-slot-count size)))
         (equal (length file) (+ size signature-size)))))

(defun assembly-macho-file-text (file)
  (coerce (take (assembly-macho-text-size file) (coerce file 'list)) 'string))

(defun assembly-macho-loader-input-p (size base machine regions input)
  (let ((sp (boymoo-model::a64-sp machine)))
    (and (proof-span-p base size)
         (<= *assembly-macho-preferred-base* base)
         (integerp (* 1/16384 base))
         (stringp input)
         (proof-regions-p regions)
         (proof-region-disjoint-p 0 *assembly-macho-preferred-base* regions)
         (proof-region-disjoint-p base (+ base size) regions)
         (<= 16 sp)
         (equal (mod sp 16) 0)
         (proof-covered-p (- sp 16) 16 :write regions))))

; The handoff supplies the initial registers, stack and other mappings.
; The model installs the executable __TEXT segment at the supplied base.
(defun assembly-load-macho-text (file base machine regions input)
  (let* ((size (assembly-macho-text-size file))
         (end (+ base size)))
    (if (and (assembly-macho-file-p file)
             (assembly-macho-loader-input-p size base machine regions input))
        (proof-world
         (boymoo-model::a64-set-pc
          (+ base (assembly-macho-entry-offset file))
          (assembly-load-cleared-file (assembly-macho-file-text file) base end machine))
         (cons (proof-region base end :rx) regions)
         *assembly-macho-page-size*
         (proof-string-bytes (coerce input 'list)) nil nil nil nil)
      nil)))

(local (in-theory (disable ash floor mod assembly-power-of-two proof-file-le
                           boymoo-compiler::macho-header
                           boymoo-compiler::macho-image-executable
                           boymoo-compiler::macho-segment-size
                           boymoo-compiler::macho-signature-size
                           assembly-macho-signature-size-formula
                           assembly-macho-entry-offset assembly-macho-text-size
                           assembly-macho-signature-size)))

(local
 (defthm assembly-macho-read-header-values
   (implies (assembly-macho-header-p file size entry signature-size)
            (and (stringp file)
                 (equal (assembly-macho-text-size file) size)
                 (equal (assembly-macho-entry-offset file) (+ *assembly-macho-code-offset* entry))
                 (equal (assembly-macho-signature-size file) signature-size)))))

(local (in-theory (disable assembly-macho-header-p)))

(local
 (defthm assembly-macho-entry-alignment-from-image
   (implies (and (natp entry) (equal (mod entry 4) 0))
            (equal (mod (+ *assembly-macho-code-offset* entry) 4) 0))
   :hints (("Goal"
            :use ((:instance assembly-floor-bounds (x entry) (d 4))
                  (:instance assembly-floor-unique
                             (x (+ *assembly-macho-code-offset* entry)) (d 4)
                             (q (+ 1024 (floor entry 4)))))
            :in-theory (enable mod)))))

(defthm assembly-macho-emitted-file-p
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (size (assembly-macho-image-text-size image)))
    (implies (assembly-macho-image-entry-p image entry)
             (and (assembly-macho-file-p file)
                  (equal (assembly-macho-text-size file) size)
                  (equal (assembly-macho-entry-offset file) (+ *assembly-macho-code-offset* entry)))))
  :hints (("Goal"
           :use (assembly-macho-file-length-and-header
                 (:instance assembly-macho-segment-rounding
                            (bytes (+ *assembly-macho-code-offset* (car image)))))
           :in-theory (disable assembly-fragment-characters)))
  :rule-classes nil)

(local
 (defthm assembly-macho-text-file-string-length
   (let* ((file (boymoo-compiler::macho-image-executable image entry))
          (text (assembly-macho-file-text file)))
     (implies (assembly-macho-image-entry-p image entry)
              (and (stringp text)
                   (equal (length text) (assembly-macho-image-text-size image))
                   (equal (nthcdr *assembly-macho-code-offset* (coerce text 'list))
                          (append
                           (assembly-fragment-characters (cdr image))
                           (assembly-zero-characters
                            (- (assembly-macho-image-text-size image)
                               (+ *assembly-macho-code-offset* (car image)))))))))
   :hints (("Goal"
            :use (assembly-macho-text-file-contents assembly-macho-emitted-file-p)
            :in-theory (disable assembly-macho-file-p assembly-macho-image-entry-p
                                assembly-macho-image-text-size assembly-macho-text-characters
                                assembly-fragment-characters assembly-zero-characters)))
   :rule-classes nil))

(local
 (defthm assembly-macho-load-byte-after-setting-pc
   (equal (boymoo-model::a64-load 1 address (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-load 1 address machine))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes)))))

(local
 (defthm assembly-macho-byte-list-after-setting-pc
   (equal (proof-byte-list count address (boymoo-model::a64-set-pc pc machine))
          (proof-byte-list count address machine))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (disable boymoo-model::a64-load boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-macho-pc-after-setting-pc
   (implies (unsigned-byte-p 64 pc)
            (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc pc machine)) pc))))

(local (in-theory (disable boymoo-model::a64-set-pc boymoo-model::a64-pc
                           assembly-macho-file-p assembly-macho-file-text
                           boymoo-model::a64-load assembly-load-cleared-file)))

(local
 (defthm assembly-macho-loaded-file-text-places-code
   (let* ((file (boymoo-compiler::macho-image-executable image entry))
          (text (assembly-macho-file-text file))
          (size (assembly-macho-image-text-size image))
          (loaded (assembly-load-cleared-file text base (+ base size) machine)))
     (implies (and (assembly-macho-image-entry-p image entry)
                   (proof-span-p base size))
              (proof-fragments-at-p (cdr image) (+ base *assembly-macho-code-offset*) loaded)))
   :hints (("Goal"
            :use (assembly-macho-text-file-string-length
                  (:instance assembly-macho-segment-rounding
                             (bytes (+ *assembly-macho-code-offset* (car image))))
                  (:instance assembly-loaded-file-places-characters
                             (file (assembly-macho-file-text (boymoo-compiler::macho-image-executable image entry)))
                             (clear-end (+ base (assembly-macho-image-text-size image))))
                  (:instance assembly-placed-characters-after-prefix
                             (chars (coerce (assembly-macho-file-text
                                             (boymoo-compiler::macho-image-executable image entry)) 'list))
                             (count *assembly-macho-code-offset*) (address base)
                             (machine (assembly-load-cleared-file
                                       (assembly-macho-file-text
                                        (boymoo-compiler::macho-image-executable image entry))
                                       base (+ base (assembly-macho-image-text-size image)) machine)))
                  (:instance assembly-fragments-from-placed-characters
                             (fragments (cdr image)) (address (+ base *assembly-macho-code-offset*))
                             (machine (assembly-load-cleared-file
                                       (assembly-macho-file-text
                                        (boymoo-compiler::macho-image-executable image entry))
                                       base (+ base (assembly-macho-image-text-size image)) machine))))
            :in-theory (disable proof-fragments-at-p assembly-fragments-from-placed-characters
                                assembly-characters-at-p assembly-fragment-characters
                                assembly-zero-characters)))
   :rule-classes nil))

(local
 (defthm assembly-macho-fragments-after-setting-pc
   (equal (proof-fragments-at-p fragments address (boymoo-model::a64-set-pc pc machine))
          (proof-fragments-at-p fragments address machine))
   :hints (("Goal" :induct (proof-fragments-at-p fragments address machine)
                   :in-theory (disable proof-byte-list proof-byte-characters)))))

(defthm assembly-macho-loader-maps-text
  (let* ((file (boymoo-compiler::macho-image-executable image entry))
         (world (assembly-load-macho-text file base machine regions input))
         (code-base (+ base *assembly-macho-code-offset*)))
    (implies (and (assembly-macho-image-entry-p image entry)
                  (assembly-macho-loader-input-p (assembly-macho-image-text-size image)
                                                 base machine regions input))
             (and (consp world)
                  (not (proof-world-stop world))
                  (equal (proof-world-pc world) (+ code-base entry))
                  (equal (proof-world-page-size world) *assembly-macho-page-size*)
                  (proof-covered-p code-base (car image) :execute (proof-world-regions world))
                  (proof-image-at-p image code-base (proof-world-machine world)))))
  :hints (("Goal"
           :use (assembly-macho-emitted-file-p assembly-macho-loaded-file-text-places-code
                 (:instance assembly-macho-segment-rounding
                            (bytes (+ *assembly-macho-code-offset* (car image)))))
           :in-theory (disable proof-fragments-at-p proof-regions-p proof-region-disjoint-p
                               proof-load-cleared-string proof-string-bytes)))
  :rule-classes nil)

(local
 (defthm assembly-macho-page-base-is-adrp-aligned
   (implies (integerp (* 1/16384 base))
            (integerp (* 1/4096 base)))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 4) (acl2::y 1/16384) (acl2::z base)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm assembly-macho-page-quotient-times-4096
   (equal (* 4096 (* 1/4096 base)) (fix base))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 4096) (acl2::y 1/4096) (acl2::z base)))
            :in-theory (disable acl2::associativity-of-*)))))

(defthm assembly-macho-code-base-alignment
  (implies (and (natp base) (integerp (* 1/16384 base)))
           (equal (mod (+ base *assembly-macho-code-offset*) 4096) 0))
  :hints (("Goal"
           :use ((:instance assembly-floor-unique
                            (x (+ base *assembly-macho-code-offset*)) (d 4096)
                            (q (+ 1 (* 1/4096 base)))))
           :in-theory (enable mod))))

(defthm assembly-load-linked-macho-image
  (mv-let (image offset)
    (boymoo-compiler::a64-assemble-image items entry)
    (let* ((file (boymoo-compiler::macho-image-executable image offset))
           (world (assembly-load-macho-text file base machine regions input))
           (location (assembly-label-offset entry (assembly-labels items 0)))
           (size (boymoo-compiler::macho-segment-size
                  (+ *assembly-macho-code-offset* (assembly-size items))))
           (code-base (+ base *assembly-macho-code-offset*)))
      (implies (and (assembly-image-layout-p items)
                    (assoc-equal entry (assembly-labels items 0))
                    (natp location) (equal (mod location 4) 0)
                    (<= (+ location 4) (assembly-size items))
                    (< size (expt 2 32))
                    (assembly-macho-loader-input-p size base machine regions input))
               (and (proof-linked-image-p items entry code-base world)
                    (equal (proof-world-pc world) (+ code-base location))
                    (not (proof-world-stop world))))))
  :hints (("Goal"
           :use (assembly-assemble-image-for-distinct-labels assembly-macho-code-base-alignment
                 (:instance assembly-macho-loader-maps-text
                            (image (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry)))
                            (entry (mv-nth 1 (boymoo-compiler::a64-assemble-image items entry)))))
           :in-theory (disable assembly-load-macho-text assembly-size assembly-image-layout-p
                               assembly-labels assembly-label-offset assembly-items-characters
                               boymoo-compiler::a64-assemble-image proof-image-at-p proof-image-p
                               proof-covered-p proof-world-machine proof-world-regions
                               proof-world-stop proof-world-pc assembly-macho-code-base-alignment)))
  :rule-classes nil)
