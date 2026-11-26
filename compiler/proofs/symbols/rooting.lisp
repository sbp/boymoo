(in-package "BOYMOO-PROOFS")

(include-book "loops")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-register-frame-p proof-view proof-view-step proof-load-word
                     boymoo-model::a64-unsigned symbols-runtime-offset symbols-path-ready-p
                     symbols-no-memory-or-kernel-change-p symbols-intern-rooted-name-world)))

(local
 (defthm symbols-rooting-register-is-natural
   (natp (proof-world-reg index world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-rooting-word-register-fits
   (equal (boymoo-model::a64-unsigned 64 (proof-world-reg index world))
          (proof-world-reg index world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-rooted-name-world-saves-name-word
   (implies (< (+ 8 (proof-stack-top before)) (expt 2 64))
            (equal (symbols-load-register-word (proof-stack-top before) (symbols-intern-rooted-name-world before))
                   (proof-world-reg 19 before)))
   :hints (("Goal"
            :in-theory (e/d (symbols-intern-rooted-name-world proof-load-word boymoo-model::a64-load
                             symbols-world-machine-of-update symbols-memory-of-store)
                            (boymoo-model::a64-read-bytes boymoo-model::a64-store update-nth))))))

(local
 (defthm symbols-rooting-read-of-same-memory
   (implies (symbols-no-memory-or-kernel-change-p before after)
            (equal (symbols-load-register-word address before) (symbols-load-register-word address after)))
   :hints (("Goal" :in-theory (enable symbols-no-memory-or-kernel-change-p symbols-load-register-word
                                     proof-load-word boymoo-model::a64-load)))
   :rule-classes nil))

(defthm symbols-run-intern-roots-name-word
  (let ((after (proof-advance (len (symbols-intern-root-name-path before)) before))
        (slot (proof-stack-top before)))
    (implies (and (symbols-intern-root-name-pre-p code-base before)
                  (symbols-path-ready-p (symbols-intern-root-name-path before) code-base
                                        (symbols-intern-root-name-target code-base before) before))
             (and (equal (proof-stack-top after) (+ 8 slot))
                  (equal (symbols-load-register-word slot after) (proof-world-reg 19 before)))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-root-name)
                 (:instance symbols-rooted-name-world-saves-name-word)
                 (:instance symbols-rooting-read-of-same-memory
                            (address (proof-stack-top before)) (before (symbols-intern-rooted-name-world before))
                            (after (proof-advance (len (symbols-intern-root-name-path before)) before))))
           :in-theory (disable symbols-intern-root-name-path symbols-intern-root-name-target
                               symbols-intern-name-root-table-word symbols-intern-name-root-capacity
                               symbols-intern-name-root-count symbols-load-register-word
                               symbols-rooted-name-world-saves-name-word)))
  :rule-classes nil)

(defun symbols-intern-ensure-stack-entry (before)
  (proof-advance (len *symbols-intern-ensure-stack-path*) before))

(defun symbols-intern-ensured-stack (fuel before)
  (proof-advance fuel (symbols-intern-ensure-stack-entry before)))

(defun symbols-intern-rooted-state (fuel before)
  (let ((ensured (symbols-intern-ensured-stack fuel before)))
    (proof-advance (len (symbols-intern-root-name-path ensured)) ensured)))

(local
 (defthm symbols-interner-stack-return-keeps-root-inputs
   (let ((required (+ 8 (proof-stack-top before))))
     (implies (and (symbols-intern-ensure-stack-pre-p code-base before)
                   (symbols-intern-ensure-stack-frame-p code-base before call)
                   (proof-grow-return-p "rt:ensure-stack" required call ensured objects grown-objects packages)
                   (not (eq (car (proof-world-machine ensured)) :svc)))
              (and (symbols-intern-root-name-pre-p code-base ensured)
                   (equal (proof-stack-top ensured) (proof-stack-top before))
                   (equal (proof-world-reg 19 ensured) (proof-world-reg 19 before))
                   (equal (proof-world-reg 20 ensured) (proof-world-reg 20 before))
                   (equal (proof-world-reg 22 ensured) (proof-world-reg 9 before)))))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 19) (clobbers '(8 22 30)) (after call))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 20) (clobbers '(8 22 30)) (after call))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 25) (clobbers '(8 22 30)) (after call))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 19) (clobbers '(9 10 11 12 24)) (before call) (after ensured))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 20) (clobbers '(9 10 11 12 24)) (before call) (after ensured))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 22) (clobbers '(9 10 11 12 24)) (before call) (after ensured))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 25) (clobbers '(9 10 11 12 24)) (before call) (after ensured)))
            :in-theory (e/d (proof-stack-top)
                            (proof-preserved-heap-p proof-fixed-heap-p proof-grow-limit proof-stack-limit))))
   :rule-classes nil))

(defthm symbols-run-intern-ensure-stack-and-root-name
  (let* ((call (symbols-intern-ensure-stack-entry before))
         (ensured (symbols-intern-ensured-stack fuel before))
         (after (symbols-intern-rooted-state fuel before))
         (required (+ 8 (proof-stack-top before))))
    (implies (and (symbols-intern-ensure-stack-pre-p code-base before)
                  (symbols-path-ready-p *symbols-intern-ensure-stack-path* code-base
                                        (symbols-runtime-address "rt:ensure-stack" code-base) before)
                  (proof-grow-return-p "rt:ensure-stack" required call ensured objects grown-objects packages)
                  (not (eq (car (proof-world-machine ensured)) :svc))
                  (symbols-path-ready-p (symbols-intern-root-name-path ensured) code-base
                                        (symbols-intern-root-name-target code-base ensured) ensured))
             (and (symbols-intern-root-name-frame-p code-base ensured after)
                  (equal (proof-stack-top after) required)
                  (equal (symbols-load-register-word (proof-stack-top before) after) (proof-world-reg 19 before))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                  (equal (proof-world-reg 22 after) (proof-world-reg 9 before)))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-ensure-stack-call)
                 (:instance symbols-interner-stack-return-keeps-root-inputs
                            (call (symbols-intern-ensure-stack-entry before))
                            (ensured (symbols-intern-ensured-stack fuel before)))
                 (:instance symbols-run-intern-root-name (before (symbols-intern-ensured-stack fuel before)))
                 (:instance symbols-run-intern-roots-name-word (before (symbols-intern-ensured-stack fuel before)))
                 (:instance symbols-frame-gives-register
                            (highest 30) (register 20) (clobbers '(0 1 2 25))
                            (before (symbols-intern-ensured-stack fuel before))
                            (after (symbols-intern-rooted-state fuel before)))
                 (:instance symbols-frame-gives-register
                            (highest 30) (register 22) (clobbers '(0 1 2 25))
                            (before (symbols-intern-ensured-stack fuel before))
                            (after (symbols-intern-rooted-state fuel before))))
           :in-theory (disable symbols-intern-ensure-stack-frame-p symbols-intern-root-name-target
                               symbols-intern-root-name-path symbols-intern-name-root-table-word
                               symbols-intern-name-root-capacity symbols-intern-name-root-count
                               symbols-intern-root-name-pre-p proof-grow-return-p
                               symbols-load-register-word)))
  :rule-classes nil)

(local
 (defun symbols-stack-index-induction (count index address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count address)
     (symbols-stack-index-induction (1- count) (1- index) (+ 8 address)))))

(local
 (defthm symbols-nth-after-replacing-first-slot
   (implies (posp index)
            (equal (nth index (cons value (cdr rest))) (nth index rest)))
   :hints (("Goal" :expand ((nth index (cons value (cdr rest))) (nth index rest))))))

(defthm symbols-stack-view-at-index
  (let ((view (proof-stack-views count address base objects packages machine)))
    (implies (and view (natp address) (natp index) (natp count) (< index count))
             (equal (nth (+ 1 index) view)
                    (proof-view (proof-load-word (+ address (* 8 index)) machine)
                                base objects packages machine))))
  :hints (("Goal"
           :induct (symbols-stack-index-induction count index address)
           :in-theory (disable proof-stack-views))
          ("Subgoal *1/2"
           :expand ((proof-stack-views count address base objects packages machine))
           :in-theory (disable proof-stack-views))
          ("Subgoal *1/1"
           :expand ((proof-stack-views count address base objects packages machine))
           :in-theory (disable proof-stack-views)))
  :rule-classes nil)

(local
 (defthm symbols-value-stack-base-is-natural
   (natp (proof-stack-base world))
   :hints (("Goal"
            :use ((:instance symbols-load-width (count 8) (address (+ -88 (proof-heap-base world)))
                             (machine (proof-world-machine world))))
            :in-theory (e/d (proof-load-word) (boymoo-model::a64-load))))
   :rule-classes :type-prescription))

(defthm symbols-allocator-preserves-rooted-slot-value
  (let* ((base (proof-stack-base before))
         (top (proof-stack-top before))
         (slot (+ base (* 8 index))))
    (implies (and (proof-allocator-return-p kind bytes before after old-objects new-objects packages)
                  (natp index) (< index (ash (- top base) -3))
                  (proof-machine-value-p (symbols-load-register-word slot before) value before old-objects packages))
             (proof-machine-value-p (symbols-load-register-word slot after) value after new-objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-stack-view-at-index (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (objects old-objects) (machine (proof-world-machine before)))
                 (:instance symbols-stack-view-at-index (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base after))
                            (objects new-objects) (machine (proof-world-machine after))))
           :in-theory (e/d (symbols-load-register-word proof-load-word symbols-word-load-fits)
                           (proof-stack-views ash mod proof-stack-top proof-stack-base proof-heap-p
                            proof-dynamic-table-preserved-p proof-frame-return-p proof-reserved-span-p
                            proof-memory-span-agrees-p proof-stack-end proof-spaces-end boymoo-model::a64-load))))
  :rule-classes nil)

(defthm symbols-run-intern-allocation-return
  (let* ((call (proof-advance (len *symbols-intern-allocate-call-path*) before))
         (after (proof-advance fuel call)))
    (implies (and (symbols-intern-allocate-call-pre-p code-base before)
                  (symbols-path-ready-p *symbols-intern-allocate-call-path* code-base
                                        (symbols-runtime-address "rt:alloc" code-base) before)
                  (proof-allocator-return-p :header 56 call after old-objects new-objects packages)
                  (not (eq (car (proof-world-machine after)) :svc)))
             (and (equal (proof-world-reg 0 call) 56)
                  (symbols-intern-initialize-pre-p code-base after)
                  (proof-reserved-span-p :header (proof-world-reg 0 after) 56 after new-objects))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-allocate-call))
           :in-theory (disable proof-preserved-heap-p proof-reserved-span-p)))
  :rule-classes nil)
