(in-package "BOYMOO-PROOFS")

(include-book "cons")
(include-book "segments")
(include-book "publication")
(include-book "alignment")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-cons-checked-to-growth
  (let ((cuts (list (allocation-code-address "rt:ensure-stack" origin))))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (not (proof-allocation-fits-p :cons 16 before))
                  (<= 16 (allocation-sp before))
                  (< (+ 16 (proof-stack-top before)) *allocation-word-modulus*)
                  (allocation-path-ready-p *allocation-cons-growth-path* cuts before)
                  (equal cut (allocation-path-end *allocation-cons-growth-path* before)))
             (and (allocation-cons-growth-edge-p origin before cut)
                  (proof-segment-p (len *allocation-cons-growth-path*) cuts before :cut cut))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-cons-machine-to-growth
                        (:instance allocation-checked-cut
                         (instructions *allocation-cons-growth-path*) (world before) (after cut)
                         (cuts (list (allocation-code-address "rt:ensure-stack" origin)))))
           :in-theory (disable allocation-cons-machine-entry-p allocation-checked-cut
                               allocation-path-end allocation-path-ready-p proof-segment-p
                               allocation-cons-fields-p proof-allocation-fits-p))))

(defthm allocation-cons-checked-to-allocator
  (let ((cuts (list (allocation-code-address "rt:alloc-cells" origin))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-cons-address origin 14))
                  (< (+ 16 (proof-stack-top before)) *allocation-word-modulus*)
                  (allocation-path-ready-p *allocation-cons-root-path* cuts before)
                  (equal cut (allocation-path-end *allocation-cons-root-path* before)))
             (and (allocation-cons-root-edge-p origin before cut)
                  (proof-segment-p (len *allocation-cons-root-path*) cuts before :cut cut))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-cons-machine-to-allocator
                        (:instance allocation-checked-cut
                         (instructions *allocation-cons-root-path*) (world before) (after cut)
                         (cuts (list (allocation-code-address "rt:alloc-cells" origin)))))
           :in-theory (disable allocation-checked-cut allocation-path-end allocation-path-ready-p
                               allocation-cons-fields-p proof-segment-p))))

(defthm allocation-cons-checked-resumed-return
  (let* ((cell (proof-world-reg 0 before))
         (save (allocation-sp before))
         (cuts (list (allocation-load-word (+ save 8) before))))
    (implies (and (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (<= 16 (proof-stack-top before))
                  (proof-span-p cell 16)
                  (< (+ save 16) *allocation-word-modulus*)
                  (proof-disjoint-p cell (+ cell 16) save (+ save 16))
                  (allocation-path-ready-p *allocation-cons-return-path* cuts before)
                  (equal after (allocation-path-end *allocation-cons-return-path* before)))
             (and (allocation-cons-resumed-return-p before after)
                  (proof-segment-p (len *allocation-cons-return-path*) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-cons-resumed-machine-return
                        (:instance allocation-checked-cut
                         (instructions *allocation-cons-return-path*) (world before)
                         (cuts (list (allocation-load-word (+ (allocation-sp before) 8) before)))))
           :in-theory (disable allocation-checked-cut allocation-path-end allocation-path-ready-p
                               allocation-cons-fields-p proof-segment-p))))

(local
 (defun allocation-stack-slot-induct (index count address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count address)
     (allocation-stack-slot-induct (1- index) (1- count) (+ 8 address)))))

(defthm allocation-stack-slot-view
  (let ((views (proof-stack-views count address base objects packages machine)))
    (implies (and (natp index) (natp count) (< index count) (natp address) views)
             (equal (nth index (cdr views))
                    (proof-view (proof-load-word (+ address (* 8 index)) machine)
                                base objects packages machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-stack-slot-induct index count address)
           :expand ((proof-stack-views count address base objects packages machine))
           :in-theory (disable proof-view proof-load-word))))

(local
 (defthm allocation-stack-base-natural
   (natp (proof-stack-base world))
   :rule-classes :type-prescription))

(defthm allocation-root-view-in-prefix
  (let ((top (+ (proof-stack-base world) (* 8 count)))
        (address (+ (proof-stack-base world) (* 8 index))))
    (implies (and (natp index) (natp count) (< index count)
                  (proof-stack-prefix top world objects packages))
             (equal (nth index (cdr (proof-stack-prefix top world objects packages)))
                    (proof-view (allocation-load-word address world) (proof-heap-base world)
                                objects packages (proof-world-machine world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-stack-slot-view
                  (address (proof-stack-base world)) (base (proof-heap-base world))
                  (machine (proof-world-machine world)))
                 allocation-stack-slot-count)
           :in-theory (e/d (allocation-load-word)
                           (proof-load-word proof-view proof-stack-views proof-stack-base proof-runtime-word
                            allocation-runtime-word-as-load mod allocation-stack-slot-count)))))

(defthm allocation-last-two-root-views
  (let* ((prefix (proof-stack-prefix top world objects packages))
         (base (proof-heap-base world))
         (machine (proof-world-machine world)))
    (implies (and (natp index) (equal top (+ (proof-stack-base world) (* 8 index) 16)) prefix)
             (and (equal (nth index (cdr prefix))
                         (proof-view (allocation-load-word (- top 16) world) base objects packages machine))
                  (equal (nth (1+ index) (cdr prefix))
                         (proof-view (allocation-load-word (- top 8) world) base objects packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-root-view-in-prefix (count (+ 2 index)))
                 (:instance allocation-root-view-in-prefix (count (+ 2 index)) (index (1+ index))))
           :in-theory (disable proof-stack-prefix proof-stack-base proof-view nth))))

(defthm allocation-allocator-stack-prefix
  (implies (proof-allocator-return-p kind bytes before after old-objects new-objects packages)
           (and (equal (proof-stack-base after) (proof-stack-base before))
                (equal (proof-stack-top after) (proof-stack-top before))
                (proof-prefix-preserved-p (proof-stack-top before)
                                          before after old-objects new-objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-member
                   (register 25) (upper 30) (clobbers (append *proof-volatile-registers* '(26 27)))))
           :in-theory (disable proof-heap-p proof-stack-prefix proof-reserved-span-p
                               proof-memory-span-agrees-p proof-dynamic-table-preserved-p
                               proof-stack-base proof-stack-end proof-spaces-end
                               proof-static-size proof-heap-base proof-view))))

(defthm allocation-cons-two-roots-after-allocator
  (let* ((top (proof-stack-top before))
         (slot (- top 16)))
    (implies (and (natp index)
                  (equal top (+ (proof-stack-base before) (* 8 index) 16))
                  (proof-allocator-return-p :cons 16 before after old-objects new-objects packages)
                  (proof-machine-value-p (allocation-load-word slot before) left
                                         before old-objects packages)
                  (proof-machine-value-p (allocation-load-word (+ slot 8) before) right
                                         before old-objects packages))
             (and (equal (allocation-cons-reload-address after) slot)
                  (proof-machine-value-p (allocation-load-word slot after) left
                                         after new-objects packages)
                  (proof-machine-value-p (allocation-load-word (+ slot 8) after) right
                                         after new-objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-allocator-stack-prefix (kind :cons) (bytes 16))
                 (:instance allocation-last-two-root-views
                   (world before) (objects old-objects) (top (proof-stack-top before)))
                 (:instance allocation-last-two-root-views
                   (world after) (objects new-objects) (top (proof-stack-top before))))
           :in-theory (disable proof-allocator-return-p proof-stack-prefix proof-stack-base
                               proof-stack-top proof-heap-base proof-view nth))))
