(in-package "BOYMOO-PROOFS")

(include-book "elf-image")
(include-book "image-loading")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash assembly-low assembly-power-of-two
                           boymoo-model::a64-unsigned
                           boymoo-compiler::elf-image-executable proof-elf-p proof-elf-entry
                           assembly-fragment-characters)))

(local
 (defthm assembly-nonnegative-rational-has-nonnegative-numerator
   (implies (and (rationalp value) (<= 0 value))
            (<= 0 (numerator value)))
   :hints (("Goal"
            :use ((:instance acl2::rational-implies1 (acl2::x value))
                  (:instance acl2::rational-implies2 (acl2::x value))
                  (:instance assembly-scale-order
                             (d (/ (denominator value))) (a (numerator value)) (b 0)))
            :in-theory (disable acl2::rational-implies2)))
   :rule-classes nil))

(local
 (defthm assembly-exact-rounding-quotient
   (implies (and (natp address) (posp alignment)
                 (equal (denominator (* address (/ alignment))) 1))
            (equal (* alignment (numerator (* address (/ alignment)))) address))
   :hints (("Goal"
            :use ((:instance acl2::rational-implies2 (acl2::x (* address (/ alignment))))
                  (:instance acl2::associativity-of-*
                             (acl2::x alignment) (acl2::y (/ alignment)) (acl2::z address))
                  (:instance acl2::inverse-of-* (acl2::x alignment)))
            :in-theory (disable acl2::rational-implies2 acl2::associativity-of-* acl2::inverse-of-*)))
   :rule-classes nil))

(defthm assembly-align-up-covers-address
  (implies (and (natp address) (posp alignment))
           (and (natp (proof-align-up address alignment))
                (<= address (proof-align-up address alignment))))
  :hints (("Goal"
           :use ((:instance assembly-floor-bounds (x address) (d alignment))
                 (:instance assembly-nonnegative-rational-has-nonnegative-numerator
                            (value (* address (/ alignment))))
                 assembly-exact-rounding-quotient)
           :in-theory (enable floor ceiling)))
  :rule-classes nil)

(local
 (defthm assembly-load-after-setting-pc
   (equal (boymoo-model::a64-load count address (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-load count address machine))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes)))))

(local
 (defthm assembly-read-byte-list-after-setting-pc
   (equal (proof-byte-list count address (boymoo-model::a64-set-pc pc machine))
          (proof-byte-list count address machine))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (disable boymoo-model::a64-load boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-read-fragments-after-setting-pc
   (equal (proof-fragments-at-p fragments address (boymoo-model::a64-set-pc pc machine))
          (proof-fragments-at-p fragments address machine))
   :hints (("Goal" :induct (proof-fragments-at-p fragments address machine)
                   :in-theory (disable proof-byte-list proof-byte-characters
                                       boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-loader-pc-value
   (implies (unsigned-byte-p 64 address)
            (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc address machine))
                   address))))

(local
 (defthm assembly-file-code-placed
   (let* ((file (boymoo-compiler::elf-image-executable image offset))
          (base *proof-linux-file-base*)
          (loaded (assembly-load-cleared-file file base clear-end machine)))
     (implies (and (assembly-elf-image-entry-p image offset)
                   (<= (+ *proof-linux-code-base* (car image)) clear-end))
              (proof-fragments-at-p (cdr image) *proof-linux-code-base* loaded)))
   :hints (("Goal"
            :use (assembly-elf-image-file
                  (:instance assembly-loaded-file-places-characters
                             (file (boymoo-compiler::elf-image-executable image offset))
                             (base *proof-linux-file-base*))
                  (:instance assembly-placed-characters-after-prefix
                             (chars (coerce (boymoo-compiler::elf-image-executable image offset) 'list))
                             (count *proof-linux-code-offset*) (address *proof-linux-file-base*)
                             (machine (assembly-load-cleared-file
                                       (boymoo-compiler::elf-image-executable image offset)
                                       *proof-linux-file-base* clear-end machine)))
                  (:instance assembly-fragments-from-placed-characters
                             (fragments (cdr image)) (address *proof-linux-code-base*)
                             (machine (assembly-load-cleared-file
                                       (boymoo-compiler::elf-image-executable image offset)
                                       *proof-linux-file-base* clear-end machine))))
            :in-theory (disable assembly-elf-image-file assembly-fragments-from-placed-characters
                                assembly-load-cleared-file assembly-characters-at-p
                                proof-fragments-at-p proof-fragments-p proof-byte-list)))
   :rule-classes nil))

(defun assembly-linux-loader-input-p (size machine regions page input)
  (let ((end (proof-align-up (+ *proof-linux-code-base* size) page))
        (sp (boymoo-model::a64-sp machine)))
    (and (stringp input)
         (proof-page-size-p page)
         (proof-regions-p regions)
         (proof-region-disjoint-p *proof-linux-file-base* end regions)
         (<= 16 sp)
         (equal (mod sp 16) 0)
         (proof-covered-p (- sp 16) 16 :write regions))))

(local
 (defthm assembly-linux-loader-world
   (let* ((size (car image))
          (file (boymoo-compiler::elf-image-executable image offset))
          (end (proof-align-up (+ *proof-linux-code-base* size) page)))
     (implies (and (assembly-elf-image-entry-p image offset)
                   (assembly-linux-loader-input-p size machine regions page input))
              (equal (proof-load-linux file machine regions page input replies)
                     (proof-world
                      (boymoo-model::a64-set-pc
                       (+ *proof-linux-code-base* offset)
                       (assembly-load-cleared-file file *proof-linux-file-base* end machine))
                      (cons (proof-region *proof-linux-file-base* end :rx) regions)
                      page
                      (proof-string-bytes (coerce input 'list))
                      nil nil replies nil))))
   :hints (("Goal"
            :use (assembly-elf-image-file)
            :in-theory (disable assembly-elf-image-file assembly-elf-image-entry-p
                                proof-align-up proof-covered-p proof-page-size-p proof-regions-p
                                proof-clear-memory proof-region-disjoint-p
                                boymoo-model::a64-set-pc proof-world
                                proof-load-cleared-string proof-string-bytes length)))))

(defthm assembly-linux-loader-maps-elf-image
  (let* ((file (boymoo-compiler::elf-image-executable image offset))
         (world (proof-load-linux file machine regions page input replies)))
    (implies (and (assembly-elf-image-entry-p image offset)
                  (assembly-linux-loader-input-p (car image) machine regions page input))
             (and (consp world)
                  (not (proof-world-stop world))
                  (equal (proof-world-pc world) (+ *proof-linux-code-base* offset))
                  (proof-image-at-p image *proof-linux-code-base* (proof-world-machine world))
                  (proof-covered-p *proof-linux-code-base* (car image) :execute
                                   (proof-world-regions world)))))
  :hints (("Goal"
           :use ((:instance assembly-file-code-placed
                            (clear-end (proof-align-up (+ *proof-linux-code-base* (car image)) page)))
                 (:instance assembly-align-up-covers-address
                            (address (+ *proof-linux-code-base* (car image))) (alignment page)))
           :in-theory (disable proof-load-linux assembly-load-cleared-file proof-align-up
                               proof-clear-memory proof-fragments-at-p proof-fragments-p
                               proof-region-disjoint-p proof-regions-p
                               proof-string-bytes boymoo-model::a64-sp boymoo-model::a64-set-pc
                               boymoo-model::a64-pc)))
  :rule-classes nil)

(defthm assembly-linux-loader-zero-page-tail
  (let* ((size (car image))
         (file (boymoo-compiler::elf-image-executable image offset))
         (world (proof-load-linux file machine regions page input replies))
         (end (+ *proof-linux-code-base* size)))
    (implies (and (assembly-elf-image-entry-p image offset)
                  (assembly-linux-loader-input-p size machine regions page input)
                  (unsigned-byte-p 64 address)
                  (<= end address) (< address (proof-align-up end page)))
             (equal (boymoo-model::a64-load 1 address (proof-world-machine world)) 0)))
  :hints (("Goal"
           :use (assembly-elf-image-file)
           :in-theory (disable assembly-elf-image-file proof-load-linux
                               assembly-load-cleared-file proof-align-up length
                               assembly-elf-image-entry-p assembly-linux-loader-input-p
                               boymoo-model::a64-load boymoo-model::a64-set-pc)))
  :rule-classes nil)

(defthm assembly-load-linked-linux-image
  (mv-let (image offset)
    (boymoo-compiler::a64-assemble-image items entry)
    (let* ((file (boymoo-compiler::elf-image-executable image offset))
           (world (proof-load-linux file machine regions page input replies))
           (location (assembly-label-offset entry (assembly-labels items 0))))
      (implies (and (assembly-image-layout-p items)
                    (assoc-equal entry (assembly-labels items 0))
                    (natp location) (equal (mod location 4) 0)
                    (<= (+ location 4) (assembly-size items))
                    (<= (+ *proof-linux-code-base* (assembly-size items)) (expt 2 63))
                    (assembly-linux-loader-input-p (assembly-size items) machine regions page input))
               (and (proof-linked-image-p items entry *proof-linux-code-base* world)
                    (equal (proof-world-pc world) (+ *proof-linux-code-base* location))
                    (not (proof-world-stop world))))))
  :hints (("Goal"
           :use (assembly-assemble-image-for-distinct-labels
                 (:instance assembly-linux-loader-maps-elf-image
                            (image (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry)))
                            (offset (mv-nth 1 (boymoo-compiler::a64-assemble-image items entry)))))
           :in-theory (disable assembly-linux-loader-input-p
                               proof-load-linux assembly-linux-loader-world
                               assembly-layout-input-p assembly-image-layout-p assembly-labels
                               assembly-size assembly-label-offset assembly-items-characters
                               boymoo-compiler::a64-assemble-image proof-image-at-p proof-image-p
                               proof-covered-p proof-world-machine proof-world-regions
                               proof-world-stop proof-world-pc)))
  :rule-classes nil)
