(in-package "BOYMOO-PROOFS")

(include-book "cell-contract")
(include-book "cons-publication")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-cons-reserve-path* (take 8 *allocation-cons-fast-path*))

; This world represents the cell reservation before CONS initializes its fields.
; Set the result register and PC to those of an allocator return.
(defun allocation-cons-reservation-world (before)
  (let ((cut (allocation-path-end *allocation-cons-reserve-path* before)))
    (allocation-set-pc (proof-world-reg 30 before)
                       (allocation-write-reg 0 (proof-world-reg 2 cut) cut))))

(defthm allocation-cons-inline-reservation
  (implies (and (allocation-cons-machine-entry-p origin before)
                (proof-allocation-fits-p :cons 16 before))
           (allocation-fast-machine-return-p :cons 16 before (allocation-cons-reservation-world before)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-cons-inline-reservation-keeps-operand-views
  (let* ((reserved (allocation-cons-reservation-world before))
         (machine (proof-world-machine before))
         (base (proof-heap-base before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-fast-machine-return-p :cons 16 before reserved))
             (and (equal (proof-heap-base reserved) base)
                  (equal (proof-view word base objects packages (proof-world-machine reserved))
                         (proof-view word base objects packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-cell-frontier-outside-published-objects)
                 (:instance allocation-fast-cells-store-describes-return-memory (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-unchanged-register (bytes 16) (register 28) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-view-after-disjoint-write
                  (start (allocation-cell-frontier-address before)) (bytes 8)
                  (value (allocation-reservation-address :cons 16 before))
                  (machine (proof-world-machine before)) (base (proof-heap-base before))))
           :in-theory (disable allocation-cons-reservation-world proof-heap-p proof-object-map-p proof-view
                               proof-span-p allocation-objects-outside-write-p allocation-fast-machine-return-p
                               allocation-fast-cells-unchanged-register boymoo-model::a64-store))))

(defthm allocation-cons-fast-initializes-reserved-cell
  (let* ((reserved (allocation-cons-reservation-world before))
         (address (allocation-reservation-address :cons 16 before))
         (first (proof-world-reg 0 before))
         (second (proof-world-reg 1 before))
         (cell (proof-object address :active :cons rank)))
    (implies (and (allocation-fast-machine-return-p :cons 16 before reserved)
                  (allocation-cons-fast-return-p before after))
             (and (equal (proof-heap-base after) (proof-heap-base before))
                  (equal (proof-world-reg 0 after) (proof-object-word cell (proof-heap-base before)))
                  (allocation-same-memory-p (proof-world-machine after)
                                            (allocation-store-cell address first second (proof-world-machine reserved))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-member (register 28) (upper 30) (clobbers '(0 2 9 26))))
           :in-theory (e/d (allocation-same-memory-p)
                           (allocation-cons-reservation-world proof-register-frame-p proof-span-p
                            allocation-cons-fields-p proof-streams-preserved-p proof-cons-floor
                            boymoo-model::a64-write-bytes boymoo-model::a64-unsigned)))))

(defthm allocation-cons-fast-publishes-cell
  (let* ((address (allocation-reservation-address :cons 16 before))
         (record (proof-object address :active :cons rank))
         (published (cons record objects))
         (base (proof-heap-base before))
         (left-word (proof-world-reg 0 before))
         (right-word (proof-world-reg 1 before)))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (proof-allocation-fits-p :cons 16 before)
                  (proof-heap-p before objects packages)
                  (allocation-cons-fast-return-p before after)
                  (proof-reg-value-p 0 left before objects packages)
                  (proof-reg-value-p 1 right before objects packages)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth left-word base objects) rank)
                  (<= (allocation-word-depth right-word base objects) rank))
             (and (proof-object-map-p published published nil base packages (proof-world-machine after))
                  (proof-reg-value-p 0 (cons left right) after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-inline-reservation allocation-cons-fast-initializes-reserved-cell
                 (:instance allocation-cons-inline-reservation-keeps-operand-views (word (proof-world-reg 0 before)))
                 (:instance allocation-cons-inline-reservation-keeps-operand-views (word (proof-world-reg 1 before)))
                 (:instance allocation-fast-cells-preserves-heap (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-reserved-span (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-heap-published-map (world (allocation-cons-reservation-world before)))
                 (:instance allocation-object-map-with-disjoint-spans
                  (pending objects) (symbols nil) (base (proof-heap-base before))
                  (machine (proof-world-machine (allocation-cons-reservation-world before)))
                  (start (allocation-reservation-address :cons 16 before))
                  (end (+ 16 (allocation-reservation-address :cons 16 before))))
                 (:instance allocation-initialize-and-publish-cell
                  (start (allocation-reservation-address :cons 16 before)) (base (proof-heap-base before))
                  (machine (proof-world-machine (allocation-cons-reservation-world before)))
                  (first (proof-world-reg 0 before)) (second (proof-world-reg 1 before))))
           :in-theory (disable allocation-cons-reservation-world allocation-cons-fast-return-p
                               proof-heap-p proof-object-map-p proof-span-p proof-object-disjoint-p
                               allocation-objects-outside-write-p proof-view proof-object-word
                               allocation-word-depth allocation-store-cell allocation-cons-machine-entry-p
                               proof-allocation-fits-p proof-cons-floor proof-active-end mod))))

(defthm allocation-cons-fast-checked-publication
  (let* ((address (allocation-reservation-address :cons 16 before))
         (base (proof-heap-base before))
         (published (cons (proof-object address :active :cons rank) objects))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (proof-allocation-fits-p :cons 16 before)
                  (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 left before objects packages)
                  (proof-reg-value-p 1 right before objects packages)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth (proof-world-reg 0 before) base objects) rank)
                  (<= (allocation-word-depth (proof-world-reg 1 before) base objects) rank)
                  (allocation-path-ready-p *allocation-cons-fast-path* cuts before)
                  (equal after (allocation-path-end *allocation-cons-fast-path* before)))
             (and (proof-segment-p (len *allocation-cons-fast-path*) cuts before :cut after)
                  (proof-object-map-p published published nil base packages (proof-world-machine after))
                  (proof-reg-value-p 0 (cons left right) after published packages))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-cons-fast-checked-return allocation-cons-fast-publishes-cell)
           :in-theory (disable allocation-cons-machine-entry-p allocation-cons-fast-return-p
                               allocation-path-ready-p allocation-path-end proof-segment-p
                               proof-heap-p proof-object-map-p proof-reg-value-p proof-allocation-fits-p
                               allocation-word-depth proof-heap-base mod))))
