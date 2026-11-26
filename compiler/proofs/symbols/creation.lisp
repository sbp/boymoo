(in-package "BOYMOO-PROOFS")

(include-book "intern-call")
(include-book "rooting")
(include-book "publication")
(include-book "grow-call")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-advance proof-world-reg proof-world-pc proof-reg proof-register-frame-p
                     proof-grow-return-p proof-allocator-return-p proof-reserved-span-p proof-heap-p
                     symbols-runtime-offset symbols-path-ready-p
                     symbols-intern-lookup-state symbols-intern-lookup-binding
                     symbols-intern-ensure-stack-entry symbols-intern-ensured-stack symbols-intern-rooted-state)))

(defun symbols-intern-allocation-entry (before)
  (proof-advance (len *symbols-intern-allocate-call-path*) before))

(defun symbols-intern-reserved-state (stack-fuel allocation-fuel before)
  (proof-advance allocation-fuel
                 (symbols-intern-allocation-entry (symbols-intern-rooted-state stack-fuel before))))

(defun symbols-intern-rooting-branch-ready-p (stack-fuel code-base before target objects grown-objects packages)
  (let ((stack-call (symbols-intern-ensure-stack-entry before))
        (ensured (symbols-intern-ensured-stack stack-fuel before)))
    (and (symbols-path-ready-p *symbols-intern-ensure-stack-path* code-base
                               (symbols-runtime-address "rt:ensure-stack" code-base) before)
         (proof-grow-return-p "rt:ensure-stack" (+ 8 (proof-stack-top before))
                              stack-call ensured objects grown-objects packages)
         (not (eq (car (proof-world-machine ensured)) :svc))
         (equal (symbols-intern-root-name-target code-base ensured) target)
         (symbols-path-ready-p (symbols-intern-root-name-path ensured) code-base target ensured))))

(defun symbols-intern-symbol-allocation-ready-p (fuel code-base before old-objects new-objects packages)
  (let* ((allocator (symbols-intern-allocation-entry before))
         (reserved (proof-advance fuel allocator)))
    (and (symbols-path-ready-p *symbols-intern-allocate-call-path* code-base
                               (symbols-runtime-address "rt:alloc" code-base) before)
         (proof-allocator-return-p :header 56 allocator reserved old-objects new-objects packages)
         (not (eq (car (proof-world-machine reserved)) :svc)))))

(defun symbols-intern-reservation-with-room-ready-p (stack-fuel allocation-fuel code-base before
                                                              objects grown-objects new-objects packages)
  (and (symbols-intern-rooting-branch-ready-p stack-fuel code-base before
                                             (symbols-runtime-address "rt:intern-allocate" code-base)
                                             objects grown-objects packages)
       (symbols-intern-symbol-allocation-ready-p allocation-fuel code-base
                                                (symbols-intern-rooted-state stack-fuel before)
                                                grown-objects new-objects packages)))

(local
 (defthm symbols-missed-intern-lookup-admits-stack-call
   (implies (and (symbols-runtime-base-p code-base)
                 (symbols-intern-saved-frame-p caller before)
                 (< (+ 8 (proof-stack-top caller)) (expt 2 64))
                 (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-create" code-base)))
            (and (symbols-intern-ensure-stack-pre-p code-base before)
                 (equal (proof-stack-top before) (proof-stack-top caller))))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 25)
                             (clobbers *symbols-intern-temporary-clobbers*) (before caller) (after before)))
            :in-theory (disable symbols-intern-saved-world symbols-no-memory-or-kernel-change-p)))
   :rule-classes nil))

(local
 (defthm symbols-name-save-with-room-enters-allocation
   (implies (and (symbols-runtime-base-p code-base)
                 (symbols-intern-root-name-frame-p code-base ensured rooted)
                 (equal (symbols-intern-root-name-target code-base ensured)
                        (symbols-runtime-address "rt:intern-allocate" code-base)))
            (symbols-intern-allocate-call-pre-p code-base rooted))
   :hints (("Goal" :in-theory (disable symbols-intern-root-name-target symbols-intern-name-root-table-word
                                      symbols-intern-name-root-capacity symbols-intern-name-root-count
                                      symbols-no-memory-or-kernel-change-p)))
   :rule-classes nil))

(defun symbols-intern-lookup-miss-ready-p (name designator static-count static-fuels dynamic-count dynamic-fuels
                                              code-base caller objects packages)
  (and (symbols-intern-at-p 0 code-base caller)
       (<= 48 (boymoo-model::a64-sp (proof-world-machine caller)))
       (< (+ 8 (proof-stack-top caller)) (expt 2 64))
       (stringp name) (symbolp designator) (proof-packages-p packages)
       (symbols-intern-saved-input-p name designator caller objects packages)
       (symbols-intern-lookup-ready-p name static-count static-fuels dynamic-count dynamic-fuels code-base caller)
       (not (symbols-intern-lookup-binding name static-count static-fuels dynamic-count caller))))

(defthm symbols-run-intern-miss-with-room-to-reserved-span
  (let* ((create (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller))
         (rooted (symbols-intern-rooted-state stack-fuel create))
         (reserved (symbols-intern-reserved-state stack-fuel allocation-fuel create)))
    (implies (and (symbols-intern-lookup-miss-ready-p name designator static-count static-fuels
                                                     dynamic-count dynamic-fuels code-base caller objects packages)
                  (symbols-intern-reservation-with-room-ready-p stack-fuel allocation-fuel code-base create
                                                                objects grown-objects new-objects packages))
             (and (equal (proof-stack-top rooted) (+ 8 (proof-stack-top caller)))
                  (symbols-intern-initialize-pre-p code-base reserved)
                  (proof-reserved-span-p :header (proof-world-reg 0 reserved) 56 reserved new-objects))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-lookup (before caller))
                 (:instance symbols-missed-intern-lookup-admits-stack-call
                            (before (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller)))
                 (:instance symbols-run-intern-ensure-stack-and-root-name (fuel stack-fuel)
                            (before (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller)))
                 (:instance symbols-name-save-with-room-enters-allocation
                            (ensured (symbols-intern-ensured-stack
                                      stack-fuel (symbols-intern-lookup-state
                                                  name static-count static-fuels dynamic-count dynamic-fuels caller)))
                            (rooted (symbols-intern-rooted-state
                                     stack-fuel (symbols-intern-lookup-state
                                                 name static-count static-fuels dynamic-count dynamic-fuels caller))))
                 (:instance symbols-run-intern-allocation-return (fuel allocation-fuel) (old-objects grown-objects)
                            (before (symbols-intern-rooted-state
                                     stack-fuel (symbols-intern-lookup-state
                                                 name static-count static-fuels dynamic-count dynamic-fuels caller)))))
           :in-theory (disable symbols-intern-saved-frame-p symbols-intern-ensure-stack-pre-p
                               symbols-intern-allocate-call-pre-p symbols-intern-initialize-pre-p
                               symbols-intern-root-name-frame-p symbols-intern-root-name-target
                               symbols-intern-root-name-path symbols-intern-lookup-ready-p
                               symbols-intern-saved-input-p proof-packages-p symbols-load-register-word)))
  :rule-classes nil)

(defthm symbols-intern-with-room-runtime-contract
  (let* ((primitive 'acl2::intern-in-package-of-symbol)
         (args (list name designator))
         (create (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller))
         (reserved (symbols-intern-reserved-state stack-fuel allocation-fuel create))
         (entry (symbols-intern-publication-entry reserved))
         (after (symbols-intern-fresh-finish reserved))
         (address (proof-world-reg 0 reserved)))
    (implies (and (proof-runtime-pre-p primitive args program *symbols-runtime-labels*
                                       code-base caller objects packages)
                  (symbols-intern-lookup-miss-ready-p name designator static-count static-fuels
                                                     dynamic-count dynamic-fuels code-base caller objects packages)
                  (symbols-intern-reservation-with-room-ready-p stack-fuel allocation-fuel code-base create
                                                                objects grown-objects reserved-objects packages)
                  (symbols-intern-fresh-return-ready-p code-base caller reserved)
                  (symbols-intern-link-writes-disjoint-p address (+ address 48) entry)
                  (symbols-intern-fresh-representation-p name designator buckets packages reserved after new-objects)
                  (proof-preserved-heap-p t caller after objects new-objects packages))
             (proof-runtime-return-p primitive args program caller after objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-miss-with-room-to-reserved-span (new-objects reserved-objects))
                 (:instance symbols-intern-reserved-fresh-runtime-contract (caller-objects objects)
                            (reserved (symbols-intern-reserved-state
                                       stack-fuel allocation-fuel
                                       (symbols-intern-lookup-state name static-count static-fuels
                                                                    dynamic-count dynamic-fuels caller)))))
           :in-theory (disable proof-runtime-pre-p proof-runtime-return-p proof-preserved-heap-p
                               symbols-intern-lookup-miss-ready-p symbols-intern-reservation-with-room-ready-p
                               symbols-intern-reserved-state symbols-intern-fresh-return-ready-p
                               symbols-intern-initialize-pre-p symbols-intern-fresh-representation-p
                               symbols-intern-link-writes-disjoint-p symbols-intern-fresh-finish
                               symbols-intern-publication-entry)))
  :rule-classes nil)

(defun symbols-intern-reserved-state-after-growth (stack-fuel growth-fuel allocation-fuel chains before)
  (let* ((rooted (symbols-intern-rooted-state stack-fuel before))
         (grown (symbols-intern-grown-state growth-fuel chains rooted)))
    (proof-advance allocation-fuel (symbols-intern-allocation-entry grown))))

(defun symbols-intern-reservation-after-growth-ready-p (stack-fuel growth-fuel allocation-fuel chains code-base before
                                                                 objects stack-objects table-objects new-objects packages)
  (let* ((rooted (symbols-intern-rooted-state stack-fuel before))
         (grown (symbols-intern-grown-state growth-fuel chains rooted)))
    (and (symbols-intern-rooting-branch-ready-p stack-fuel code-base before
                                               (symbols-runtime-address "rt:intern-grow" code-base)
                                               objects stack-objects packages)
         (symbols-intern-growth-continuation-ready-p growth-fuel chains code-base rooted
                                                     stack-objects table-objects packages)
         (not (eq (car (proof-world-machine grown)) :svc))
         (symbols-intern-symbol-allocation-ready-p allocation-fuel code-base grown table-objects new-objects packages))))

(defthm symbols-run-intern-miss-with-growth-to-reserved-span
  (let* ((create (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller))
         (rooted (symbols-intern-rooted-state stack-fuel create))
         (reserved (symbols-intern-reserved-state-after-growth stack-fuel growth-fuel allocation-fuel chains create)))
    (implies (and (symbols-intern-lookup-miss-ready-p name designator static-count static-fuels
                                                     dynamic-count dynamic-fuels code-base caller objects packages)
                  (symbols-intern-reservation-after-growth-ready-p stack-fuel growth-fuel allocation-fuel chains
                                                                   code-base create objects stack-objects
                                                                   table-objects new-objects packages))
             (and (equal (proof-stack-top rooted) (+ 8 (proof-stack-top caller)))
                  (symbols-intern-initialize-pre-p code-base reserved)
                  (proof-reserved-span-p :header (proof-world-reg 0 reserved) 56 reserved new-objects))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-lookup (before caller))
                 (:instance symbols-missed-intern-lookup-admits-stack-call
                            (before (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller)))
                 (:instance symbols-run-intern-ensure-stack-and-root-name (fuel stack-fuel) (grown-objects stack-objects)
                            (before (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller)))
                 (:instance symbols-run-grow-table-returns-to-interner-allocation
                            (fuel growth-fuel) (old-objects stack-objects) (new-objects table-objects)
                            (before (symbols-intern-rooted-state
                                     stack-fuel (symbols-intern-lookup-state
                                                 name static-count static-fuels dynamic-count dynamic-fuels caller))))
                 (:instance symbols-run-intern-allocation-return (fuel allocation-fuel) (old-objects table-objects)
                            (before (symbols-intern-grown-state
                                     growth-fuel chains (symbols-intern-rooted-state
                                                         stack-fuel (symbols-intern-lookup-state
                                                                     name static-count static-fuels dynamic-count dynamic-fuels caller))))))
           :in-theory (disable symbols-intern-saved-frame-p symbols-intern-ensure-stack-pre-p
                               symbols-intern-initialize-pre-p
                               symbols-intern-root-name-frame-p symbols-intern-root-name-target
                               symbols-intern-root-name-path symbols-intern-lookup-ready-p
                               symbols-intern-saved-input-p symbols-intern-growth-continuation-ready-p
                               symbols-intern-grown-state symbols-intern-grow-entry symbols-grow-bucket-count
                               symbols-grow-allocated-state symbols-grow-publication-entry
                               symbols-grown-root-frame-p proof-packages-p symbols-load-register-word)))
  :rule-classes nil)

(defthm symbols-intern-with-growth-runtime-contract
  (let* ((primitive 'acl2::intern-in-package-of-symbol)
         (args (list name designator))
         (create (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels caller))
         (reserved (symbols-intern-reserved-state-after-growth stack-fuel growth-fuel allocation-fuel chains create))
         (entry (symbols-intern-publication-entry reserved))
         (after (symbols-intern-fresh-finish reserved))
         (address (proof-world-reg 0 reserved)))
    (implies (and (proof-runtime-pre-p primitive args program *symbols-runtime-labels*
                                       code-base caller objects packages)
                  (symbols-intern-lookup-miss-ready-p name designator static-count static-fuels
                                                     dynamic-count dynamic-fuels code-base caller objects packages)
                  (symbols-intern-reservation-after-growth-ready-p stack-fuel growth-fuel allocation-fuel chains
                                                                   code-base create objects stack-objects
                                                                   table-objects reserved-objects packages)
                  (symbols-intern-fresh-return-ready-p code-base caller reserved)
                  (symbols-intern-link-writes-disjoint-p address (+ address 48) entry)
                  (symbols-intern-fresh-representation-p name designator buckets packages reserved after new-objects)
                  (proof-preserved-heap-p t caller after objects new-objects packages))
             (proof-runtime-return-p primitive args program caller after objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-miss-with-growth-to-reserved-span (new-objects reserved-objects))
                 (:instance symbols-intern-reserved-fresh-runtime-contract (caller-objects objects)
                            (reserved (symbols-intern-reserved-state-after-growth
                                       stack-fuel growth-fuel allocation-fuel chains
                                       (symbols-intern-lookup-state name static-count static-fuels
                                                                    dynamic-count dynamic-fuels caller)))))
           :in-theory (disable proof-runtime-pre-p proof-runtime-return-p proof-preserved-heap-p
                               symbols-intern-lookup-miss-ready-p symbols-intern-reservation-after-growth-ready-p
                               symbols-intern-reserved-state-after-growth symbols-intern-fresh-return-ready-p
                               symbols-intern-initialize-pre-p symbols-intern-fresh-representation-p
                               symbols-intern-link-writes-disjoint-p symbols-intern-fresh-finish
                               symbols-intern-publication-entry)))
  :rule-classes nil)
