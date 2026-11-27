(in-package "BOYMOO-PROOFS")

(include-book "rehash-table")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-advance proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-register-frame-p proof-advance-append
                     symbols-path-ready-p symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p symbols-load-register-word
                     boymoo-model::a64-unsigned)))

(defun symbols-grow-clearing-entry (before)
  (proof-advance (len *symbols-grow-header-path*) before))

(defun symbols-grow-cleared-state (count before)
  (proof-advance (* 4 count) (symbols-grow-clearing-entry before)))

(defun symbols-grow-after-old-root-check (count before)
  (let ((cleared (symbols-grow-cleared-state count before)))
    (proof-advance (len (symbols-grow-after-clear-path cleared)) cleared)))

(defun symbols-grow-rehash-required-p (count before)
  (not (equal (symbols-grow-old-table-word (symbols-grow-cleared-state count before))
              *proof-nil*)))

(defun symbols-grow-publication-entry (count chains before)
  (let ((checked (symbols-grow-after-old-root-check count before)))
    (if (symbols-grow-rehash-required-p count before)
        (proof-advance (symbols-rehash-table-fuel chains) checked)
      checked)))

(defun symbols-grow-tail-finish (count chains before)
  (proof-advance (len *symbols-grown-root-path*) (symbols-grow-publication-entry count chains before)))

(defun symbols-grow-tail-ready-p (count chains code-base before)
  (let* ((clear (symbols-grow-clearing-entry before))
         (cleared (symbols-grow-cleared-state count before))
         (check (symbols-grow-after-old-root-check count before))
         (publish (symbols-grow-publication-entry count chains before)))
    (and (posp count)
         (equal (symbols-stack-word 0 before) (* 8 count))
         (< (+ 16 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))
         (symbols-grow-header-pre-p code-base before)
         (symbols-path-ready-p *symbols-grow-header-path* code-base
                               (symbols-runtime-address "rt:intern-clear-buckets" code-base) before)
         (symbols-clear-buckets-ready-p count code-base clear)
         (symbols-path-ready-p (symbols-grow-after-clear-path cleared) code-base
                               (symbols-grow-after-clear-target code-base cleared) cleared)
         (implies (symbols-grow-rehash-required-p count before)
                  (and (symbols-rehash-table-input-p chains code-base check)
                       (symbols-rehash-table-ready-p chains code-base check)))
         (symbols-path-ready-p *symbols-grown-root-path* code-base
                               (symbols-stack-word 8 (symbols-grown-root-world publish)) publish))))

(local
 (defthm symbols-grow-initialized-header-enters-clearing
   (implies (and (posp count)
                 (symbols-grow-header-pre-p code-base before)
                 (equal (symbols-stack-word 0 before) (* 8 count))
                 (symbols-grow-header-frame-p code-base before clear))
            (symbols-clear-buckets-input-p count code-base clear))
   :hints (("Goal" :in-theory (disable symbols-grow-header-world symbols-stack-word)))
   :rule-classes nil))

(local
 (defthm symbols-cleared-buckets-enter-root-check
   (implies (and (symbols-runtime-base-p code-base)
                 (symbols-clear-buckets-frame-p count code-base clear cleared))
            (symbols-grow-after-clear-pre-p code-base cleared))
   :hints (("Goal" :in-theory (disable symbols-clear-buckets-writes symbols-write-words)))
   :rule-classes nil))

(local
 (defthm symbols-grown-root-entry-follows-rehash
   (implies (and (symbols-runtime-base-p code-base)
                 (< (+ 16 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))
                 (symbols-grow-header-frame-p code-base before clear)
                 (symbols-clear-buckets-frame-p count code-base clear cleared)
                 (symbols-grow-after-clear-frame-p code-base cleared checked)
                 (if (equal (symbols-grow-old-table-word cleared) *proof-nil*)
                     (equal publish checked)
                   (symbols-rehash-table-frame-p chains code-base checked publish)))
            (symbols-grown-root-pre-p code-base publish))
   :hints (("Goal"
            :in-theory (disable symbols-grow-header-world symbols-grow-old-table-word
                                symbols-grow-old-table-address symbols-rehash-table-memory
                                symbols-clear-buckets-writes symbols-write-words
                                symbols-stack-word symbols-box-address)))
   :rule-classes nil))

(defthm symbols-run-grow-table-tail
  (let* ((clear (symbols-grow-clearing-entry before))
         (cleared (symbols-grow-cleared-state count before))
         (checked (symbols-grow-after-old-root-check count before))
         (publish (symbols-grow-publication-entry count chains before))
         (after (symbols-grow-tail-finish count chains before)))
    (implies (symbols-grow-tail-ready-p count chains code-base before)
             (and (symbols-grow-header-frame-p code-base before clear)
                  (symbols-clear-buckets-frame-p count code-base clear cleared)
                  (symbols-grow-after-clear-frame-p code-base cleared checked)
                  (implies (symbols-grow-rehash-required-p count before)
                           (symbols-rehash-table-frame-p chains code-base checked publish))
                  (symbols-grown-root-frame-p publish after))))
  :hints (("Goal"
           :use ((:instance symbols-run-grow-header (base code-base))
                 (:instance symbols-grow-initialized-header-enters-clearing
                            (clear (symbols-grow-clearing-entry before)))
                 (:instance symbols-run-clear-buckets (before (symbols-grow-clearing-entry before)))
                 (:instance symbols-cleared-buckets-enter-root-check
                            (clear (symbols-grow-clearing-entry before))
                            (cleared (symbols-grow-cleared-state count before)))
                 (:instance symbols-run-grow-after-clear (base code-base)
                            (before (symbols-grow-cleared-state count before)))
                 (:instance symbols-run-rehash-all-buckets (before (symbols-grow-after-old-root-check count before)))
                 (:instance symbols-grown-root-entry-follows-rehash
                            (clear (symbols-grow-clearing-entry before))
                            (cleared (symbols-grow-cleared-state count before))
                            (checked (symbols-grow-after-old-root-check count before))
                            (publish (symbols-grow-publication-entry count chains before)))
                 (:instance symbols-run-publish-grown-root (before (symbols-grow-publication-entry count chains before))))
           :in-theory (disable symbols-grow-header-frame-p symbols-grow-after-clear-frame-p
                               symbols-grown-root-frame-p symbols-rehash-table-frame-p
                               symbols-grow-header-world symbols-grow-old-table-word symbols-grow-old-table-address
                               symbols-grow-after-clear-path symbols-grow-after-clear-target
                               symbols-grown-root-world symbols-grow-allocation-saves symbols-stack-word symbols-box-address
                               symbols-rehash-table-input-p symbols-rehash-table-ready-p symbols-rehash-table-fuel
                               symbols-clear-buckets-input-p symbols-clear-buckets-frame-p
                               symbols-clear-buckets-ready-p)))
  :rule-classes nil)

(defun symbols-grow-allocation-entry (before)
  (proof-advance (len *symbols-grow-allocation-path*) before))

(defun symbols-grow-allocated-state (fuel before)
  (proof-advance fuel (symbols-grow-allocation-entry before)))

(local
 (defthm symbols-growth-register-is-natural
   (natp (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-growth-register-fits-word
   (< (proof-world-reg register world) (expt 2 64))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :linear))

(local
 (defthm symbols-growth-stack-pointer-is-natural
   (natp (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-growth-stack-pointer-fits-word
   (< (boymoo-model::a64-sp machine) (expt 2 64))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :linear))

(local
 (defthm symbols-grow-link-register-is-word
   (equal (boymoo-model::a64-unsigned 64 (proof-world-reg register world))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-grow-save-writes-give-size-and-link
   (let ((bytes (* 8 (symbols-grow-bucket-count (proof-world-reg 0 before))))
         (sp (boymoo-model::a64-sp (proof-world-machine before)))
         (saved (symbols-grow-allocation-saves before)))
     (implies (and (<= 16 sp) (< (+ 16 bytes) (expt 2 64)))
              (and (equal (symbols-load-register-word (- sp 16) saved) bytes)
                   (equal (symbols-load-register-word (- sp 8) saved) (proof-world-reg 30 before)))))
   :hints (("Goal"
            :in-theory (e/d (symbols-load-register-word
                             proof-load-word boymoo-model::a64-load
                             symbols-world-machine-of-update symbols-memory-of-store)
                            (boymoo-model::a64-store boymoo-model::a64-read-bytes update-nth))))
   :rule-classes nil))

(local
 (defthm symbols-grow-word-depends-on-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (equal (symbols-load-register-word address first) (symbols-load-register-word address last)))
   :hints (("Goal" :in-theory (enable symbols-no-memory-or-kernel-change-p symbols-load-register-word
                                     boymoo-model::a64-load proof-load-word)))
   :rule-classes nil))

(local
 (defthm symbols-grow-allocation-frame-saves-size-and-link
   (let ((bytes (* 8 (symbols-grow-bucket-count (proof-world-reg 0 before))))
         (sp (boymoo-model::a64-sp (proof-world-machine before))))
     (implies (and (<= 16 sp) (< (+ 16 bytes) (expt 2 64))
                   (symbols-grow-allocation-frame-p code-base before call))
              (and (equal (symbols-stack-word 0 call) bytes)
                   (equal (symbols-stack-word 8 call) (proof-world-reg 30 before)))))
   :hints (("Goal"
            :use ((:instance symbols-grow-save-writes-give-size-and-link)
                  (:instance symbols-grow-word-depends-on-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                             (first (symbols-grow-allocation-saves before)) (last call))
                  (:instance symbols-grow-word-depends-on-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))
                             (first (symbols-grow-allocation-saves before)) (last call)))
            :in-theory (disable symbols-grow-allocation-saves symbols-grow-bucket-count)))
   :rule-classes nil))

(local
 (defthm symbols-grow-alloc-contract-keeps-save-slots
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine call)))
          (end (+ (- (proof-machine-limit call) *proof-machine-margin*) *proof-machine-reservation*)))
     (implies (and (<= (+ 16 sp) end) (<= end (expt 2 64))
                   (proof-allocator-return-p :header bytes call after old-objects new-objects packages))
              (and (equal (symbols-stack-word 0 call) (symbols-stack-word 0 after))
                   (equal (symbols-stack-word 8 call) (symbols-stack-word 8 after)))))
   :hints (("Goal"
            :use ((:instance symbols-agreeing-memory-span-gives-word
                             (start (boymoo-model::a64-sp (proof-world-machine call)))
                             (end (+ (- (proof-machine-limit call) *proof-machine-margin*) *proof-machine-reservation*))
                             (address (boymoo-model::a64-sp (proof-world-machine call))) (before call))
                  (:instance symbols-agreeing-memory-span-gives-word
                             (start (boymoo-model::a64-sp (proof-world-machine call)))
                             (end (+ (- (proof-machine-limit call) *proof-machine-margin*) *proof-machine-reservation*))
                             (address (+ 8 (boymoo-model::a64-sp (proof-world-machine call)))) (before call)))
            :in-theory (e/d (symbols-load-register-word)
                            (proof-heap-p proof-reserved-span-p proof-prefix-preserved-p
                             proof-dynamic-table-preserved-p proof-memory-span-agrees-p
                             proof-machine-limit proof-stack-base proof-spaces-end proof-stack-end
                             proof-fixed-heap-p proof-static-size))))
   :rule-classes nil))

(defun symbols-grow-allocation-return-ready-p (fuel code-base before old-objects new-objects packages)
  (let* ((call (symbols-grow-allocation-entry before))
         (reserved (symbols-grow-allocated-state fuel before))
         (bucket-bytes (* 8 (symbols-grow-bucket-count (proof-world-reg 0 before))))
         (sp (boymoo-model::a64-sp (proof-world-machine call)))
         (end (+ (- (proof-machine-limit call) *proof-machine-margin*) *proof-machine-reservation*)))
    (and (symbols-grow-allocation-pre-p code-base before)
         (symbols-path-ready-p *symbols-grow-allocation-path* code-base
                               (symbols-runtime-address "rt:alloc" code-base) before)
         (<= (+ 16 sp) end) (<= end (expt 2 64))
         (< (+ 8 bucket-bytes) (expt 2 56))
         (proof-allocator-return-p :header (+ 16 bucket-bytes) call reserved old-objects new-objects packages)
         (not (eq (car (proof-world-machine reserved)) :svc)))))

(defthm symbols-run-grow-allocation-return
  (let* ((call (symbols-grow-allocation-entry before))
         (after (symbols-grow-allocated-state fuel before))
         (count (symbols-grow-bucket-count (proof-world-reg 0 before)))
         (bytes (+ 16 (* 8 count))))
    (implies (symbols-grow-allocation-return-ready-p fuel code-base before old-objects new-objects packages)
             (and (equal (proof-world-reg 0 call) bytes)
                  (symbols-grow-header-pre-p code-base after)
                  (equal (symbols-stack-word 0 after) (* 8 count))
                  (equal (symbols-stack-word 8 after) (proof-world-reg 30 before))
                  (proof-reserved-span-p :header (proof-world-reg 0 after) bytes after new-objects))))
  :hints (("Goal"
           :use ((:instance symbols-run-grow-allocation-call (base code-base))
                 (:instance symbols-grow-allocation-frame-saves-size-and-link
                            (call (symbols-grow-allocation-entry before)))
                 (:instance symbols-grow-alloc-contract-keeps-save-slots
                            (bytes (+ 16 (* 8 (symbols-grow-bucket-count (proof-world-reg 0 before)))))
                            (call (symbols-grow-allocation-entry before)) (after (symbols-grow-allocated-state fuel before))))
           :in-theory (disable symbols-grow-allocation-saves symbols-stack-word symbols-no-memory-or-kernel-change-p
                               proof-preserved-heap-p proof-machine-limit proof-object-disjoint-p
                               proof-active-floor proof-heap-layout-p proof-world-stop)))
  :rule-classes nil)

(local
 (defthm symbols-grow-publication-keeps-allocated-stack-pointer
   (let ((publish (symbols-grow-publication-entry count chains before)))
     (implies (symbols-grow-tail-ready-p count chains code-base before)
              (equal (boymoo-model::a64-sp (proof-world-machine publish))
                     (boymoo-model::a64-sp (proof-world-machine before)))))
   :hints (("Goal"
            :use ((:instance symbols-run-grow-table-tail))
            :in-theory (disable symbols-grow-clearing-entry symbols-grow-cleared-state symbols-grow-after-old-root-check
                                symbols-grow-tail-ready-p symbols-grown-root-frame-p
                                symbols-grow-rehash-required-p symbols-rehash-table-fuel
                                symbols-grow-old-table-word symbols-grow-old-table-address symbols-grow-header-world
                                symbols-rehash-table-memory symbols-clear-buckets-writes symbols-write-words
                                symbols-stack-word)))
   :rule-classes nil))

(local
 (defthm symbols-grow-publication-stack-link-is-the-saved-word
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine reserved)))
          (memory (symbols-grown-root-world publish)))
     (implies (and (< (+ sp 16) (expt 2 64))
                   (equal (boymoo-model::a64-sp (proof-world-machine publish)) sp)
                   (proof-memory-span-agrees-p sp (+ sp 16) reserved memory))
              (equal (symbols-stack-word 8 memory) (symbols-stack-word 8 reserved))))
   :hints (("Goal"
            :use ((:instance symbols-agreeing-memory-span-gives-word
                             (start (boymoo-model::a64-sp (proof-world-machine reserved)))
                             (end (+ 16 (boymoo-model::a64-sp (proof-world-machine reserved))))
                             (address (+ 8 (boymoo-model::a64-sp (proof-world-machine reserved))))
                             (before reserved) (after (symbols-grown-root-world publish))))
            :in-theory (e/d (symbols-world-machine-of-update symbols-sp-of-store symbols-load-register-word)
                            (symbols-box-word proof-memory-span-agrees-p boymoo-model::a64-store))))
   :rule-classes nil))

(defun symbols-intern-grow-entry (before)
  (proof-advance (len *symbols-intern-grow-call-path*) before))

(defun symbols-intern-grown-state (fuel chains before)
  (let* ((entry (symbols-intern-grow-entry before))
         (count (symbols-grow-bucket-count (proof-world-reg 0 entry)))
         (reserved (symbols-grow-allocated-state fuel entry)))
    (symbols-grow-tail-finish count chains reserved)))

(defun symbols-intern-growth-continuation-ready-p (fuel chains code-base before old-objects new-objects packages)
  (let* ((entry (symbols-intern-grow-entry before))
         (count (symbols-grow-bucket-count (proof-world-reg 0 entry)))
         (reserved (symbols-grow-allocated-state fuel entry))
         (publish (symbols-grow-publication-entry count chains reserved))
         (sp (boymoo-model::a64-sp (proof-world-machine reserved))))
    (and (symbols-grow-call-pre-p code-base before)
         (symbols-path-ready-p *symbols-intern-grow-call-path* code-base
                               (symbols-runtime-address "rt:intern-grow-table" code-base) before)
         (symbols-grow-allocation-return-ready-p fuel code-base entry old-objects new-objects packages)
         (symbols-grow-tail-ready-p count chains code-base reserved)
         (< (+ sp 16) (expt 2 64))
         (proof-memory-span-agrees-p sp (+ sp 16) reserved (symbols-grown-root-world publish)))))

(defthm symbols-run-grow-table-returns-to-interner-allocation
  (let* ((entry (symbols-intern-grow-entry before))
         (count (symbols-grow-bucket-count (proof-world-reg 0 entry)))
         (reserved (symbols-grow-allocated-state fuel entry))
         (publish (symbols-grow-publication-entry count chains reserved))
         (after (symbols-intern-grown-state fuel chains before)))
    (implies (symbols-intern-growth-continuation-ready-p fuel chains code-base before
                                                         old-objects new-objects packages)
             (and (symbols-grown-root-frame-p publish after)
                  (not (proof-world-stop after))
                  (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-allocate" code-base)))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-grow-call (base code-base))
                 (:instance symbols-run-grow-allocation-return (before (symbols-intern-grow-entry before)))
                 (:instance symbols-run-grow-table-tail
                            (count (symbols-grow-bucket-count (proof-world-reg 0 (symbols-intern-grow-entry before))))
                            (before (symbols-grow-allocated-state fuel (symbols-intern-grow-entry before))))
                 (:instance symbols-grow-publication-keeps-allocated-stack-pointer
                            (count (symbols-grow-bucket-count (proof-world-reg 0 (symbols-intern-grow-entry before))))
                            (before (symbols-grow-allocated-state fuel (symbols-intern-grow-entry before))))
                 (:instance symbols-grow-publication-stack-link-is-the-saved-word
                            (reserved (symbols-grow-allocated-state fuel (symbols-intern-grow-entry before)))
                            (publish (symbols-grow-publication-entry
                                      (symbols-grow-bucket-count (proof-world-reg 0 (symbols-intern-grow-entry before)))
                                      chains (symbols-grow-allocated-state fuel (symbols-intern-grow-entry before))))))
           :in-theory (disable symbols-grow-allocated-state symbols-grow-publication-entry symbols-grow-tail-finish
                               symbols-grow-bucket-count symbols-grow-allocation-return-ready-p
                               symbols-grow-tail-ready-p symbols-grow-header-frame-p symbols-clear-buckets-frame-p
                               symbols-grow-after-clear-frame-p symbols-rehash-table-frame-p
                               symbols-grow-rehash-required-p symbols-grown-root-world symbols-stack-word
                               symbols-no-memory-or-kernel-change-p proof-memory-span-agrees-p proof-reserved-span-p)))
  :rule-classes nil)
