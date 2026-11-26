(in-package "BOYMOO-PROOFS")

(include-book "unpublished-write")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-stack-base-is-natural
  (natp (proof-stack-base world))
  :rule-classes :type-prescription)

(defthm allocation-stack-index-is-word-aligned
  (implies (integerp index)
           (equal (mod (* 8 index) 8) 0)))

(defthm allocation-stack-pointer-after-popping-pair-is-aligned
  (implies (and (integerp sp) (equal (mod sp 16) 0))
           (equal (mod (+ 16 sp) 16) 0)))

(local
 (defun allocation-stack-prefix-induct (shorter count address)
   (declare (xargs :measure (nfix shorter)))
   (if (zp shorter)
       (list count address)
     (allocation-stack-prefix-induct (1- shorter) (1- count) (+ 8 address)))))

(defthm allocation-stack-views-for-shorter-prefix
  (let ((views (proof-stack-views count address base objects packages machine)))
    (implies (and (natp shorter) (natp count) (<= shorter count) views)
             (equal (proof-stack-views shorter address base objects packages machine)
                    (cons :slots (take shorter (cdr views))))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-stack-prefix-induct shorter count address)
           :expand ((:free (number) (proof-stack-views number address base objects packages machine)))
           :in-theory (disable (:definition proof-stack-views) proof-view proof-load-word))))

(defthm allocation-stack-prefix-without-two-roots
  (let* ((base (proof-stack-base world))
         (shorter (+ base (* 8 index)))
         (full (proof-stack-prefix (proof-stack-top world) world objects packages)))
    (implies (and (natp index) (equal (proof-stack-top world) (+ shorter 16)) full)
             (equal (proof-stack-prefix shorter world objects packages)
                    (cons :slots (take index (cdr full))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-stack-views-for-shorter-prefix
                  (shorter index) (count (+ index 2)) (address (proof-stack-base world))
                  (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance allocation-stack-slot-count (count (+ index 2)))
                 (:instance allocation-stack-slot-count (count index)))
           :in-theory (disable proof-stack-views proof-view ash proof-load-word
                               proof-stack-base proof-runtime-word allocation-runtime-word-as-load mod))))

(defun allocation-world-with-stack-pointers (top sp world)
  (allocation-write-sp sp (allocation-write-reg 25 top world)))

(defthm allocation-stack-pointer-update-keeps-memory
  (allocation-same-memory-p (proof-world-machine (allocation-world-with-stack-pointers top sp world))
                            (proof-world-machine world)))

(local
 (defthm allocation-stack-register-writes-keep-model-memory
   (and (allocation-same-memory-p (proof-world-machine (allocation-write-sp sp world))
                                 (proof-world-machine world))
        (allocation-same-memory-p (proof-world-machine (allocation-write-reg register value world))
                                 (proof-world-machine world)))))

(local (in-theory (disable allocation-equal-memory-is-model-equivalence)))

(local
 (defthm allocation-external-list-ends-at-zero
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(defthm allocation-stack-pointer-update-keeps-external-objects
  (equal (proof-external-objects head fuel (allocation-world-with-stack-pointers top sp world) objects)
         (proof-external-objects head fuel world objects))
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :expand ((:free (next) (proof-external-objects head fuel next objects)))
           :in-theory (disable (:definition proof-external-objects) proof-load-word proof-align-up
                               proof-header-size proof-header-type proof-disjoint-p))))

(defthm allocation-stack-pointer-update-keeps-object-spans
  (equal (proof-heap-object-spans-p objects headers (allocation-world-with-stack-pointers top sp world))
         (proof-heap-object-spans-p objects headers world))
  :hints (("Goal" :induct (proof-heap-object-spans-p objects headers world)
           :expand ((:free (next) (proof-heap-object-spans-p objects headers next)))
           :in-theory (disable (:definition proof-heap-object-spans-p) proof-object-size proof-subspan-p mod))))

(defthm allocation-stack-pointer-update-keeps-prefix
  (implies (and (unsigned-byte-p 64 top) (<= top (proof-stack-top world)))
           (equal (proof-stack-prefix top (allocation-world-with-stack-pointers top sp world) objects packages)
                  (proof-stack-prefix top world objects packages)))
  :hints (("Goal" :in-theory (disable proof-stack-views proof-view proof-load-word mod ash))))

(defthm allocation-stack-pointer-update-keeps-dynamic-view
  (equal (proof-dynamic-view (allocation-world-with-stack-pointers top sp world) objects packages)
         (proof-dynamic-view world objects packages))
  :hints (("Goal" :in-theory (disable proof-view proof-load-word))))

(defthm allocation-stack-pointer-update-keeps-string-accounting
  (equal (proof-string-accounting-p headers (allocation-world-with-stack-pointers top sp world))
         (proof-string-accounting-p headers world))
  :hints (("Goal" :in-theory (disable proof-external-bytes mod))))

(defthm allocation-stack-pointer-update-reg-and-load
  (let ((changed (allocation-world-with-stack-pointers top sp world)))
    (and (equal (proof-world-reg register changed)
                (if (equal register 25) (boymoo-model::a64-unsigned 64 top)
                  (proof-world-reg register world)))
         (equal (allocation-load-word address changed) (allocation-load-word address world)))))

(defthm allocation-heap-layout-after-stack-pointer-update
  (let* ((machine-base (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-base *proof-machine-reservation*)))
    (implies (and (proof-heap-layout-p world)
                  (unsigned-byte-p 64 top) (equal (mod top 8) 0)
                  (<= (proof-stack-base world) top) (<= top (proof-stack-top world))
                  (unsigned-byte-p 64 sp) (equal (mod sp 16) 0)
                  (<= machine-base sp) (<= sp machine-end))
             (proof-heap-layout-p (allocation-world-with-stack-pointers top sp world))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                               proof-load-word proof-page-size-p mod))))

(defthm allocation-heap-after-stack-pointer-update
  (let* ((machine-base (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-base *proof-machine-reservation*))
         (after (allocation-world-with-stack-pointers top sp world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-stack-prefix top world objects packages)
                  (unsigned-byte-p 64 top) (equal (mod top 8) 0)
                  (<= (proof-stack-base world) top) (<= top (proof-stack-top world))
                  (unsigned-byte-p 64 sp) (equal (mod sp 16) 0)
                  (<= machine-base sp) (<= sp machine-end))
             (and (proof-heap-p after objects packages)
                  (equal (proof-stack-prefix top after objects packages)
                         (proof-stack-prefix top world objects packages))
                  (equal (proof-dynamic-view after objects packages)
                         (proof-dynamic-view world objects packages)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-heap-layout-after-stack-pointer-update)
           :in-theory (disable allocation-world-with-stack-pointers
                               proof-heap-layout-p proof-static-p proof-object-map-p
                               proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                               proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                               proof-stack-prefix proof-load-word mod))))
