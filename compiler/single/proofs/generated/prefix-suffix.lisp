(in-package "BOYMOO-PROOFS")

(include-book "stack-prefix")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-stack-prefix proof-prefix-preserved-p proof-stack-views proof-stack-base
                    proof-stack-top proof-heap-p proof-heap-base proof-world-machine proof-world-pc
                    proof-compiled-entry-p generated-stack-views-are-word-views proof-load-word proof-view
                    nthcdr mod ash expt))

(local
 (defun generated-stack-suffix-induction (left address)
   (declare (xargs :measure (nfix left)))
   (if (zp left)
       address
     (generated-stack-suffix-induction (1- left) (+ address 8)))))

(defthm generated-stack-views-suffix-from-whole
  (let ((views (proof-stack-views (+ left count) address base objects packages machine)))
    (implies (and (natp left) (natp count) (integerp address) views)
             (equal (proof-stack-views count (+ address (* 8 left)) base objects packages machine)
                    (cons :slots (nthcdr left (cdr views))))))
  :hints (("Goal" :induct (generated-stack-suffix-induction left address)
                  :in-theory (enable nthcdr))
          ("Subgoal *1/2"
           :expand ((proof-stack-views (+ count left) address base objects packages machine)
                    (proof-stack-views (+ left count) address base objects packages machine))))
  :rule-classes nil)

(defthm generated-stack-prefix-has-aligned-slot-count
  (let* ((base (proof-stack-base world)) (count (ash (- top base) -3)))
    (implies (proof-stack-prefix top world objects packages)
             (and (natp count) (equal top (+ base (* 8 count))) (<= top (proof-stack-top world))
                  (<= base top))))
  :hints (("Goal"
           :use (:instance generated-byte-count-of-aligned-slots (size (- top (proof-stack-base world))))
           :in-theory (e/d (proof-stack-prefix generated-ash-down-by-three)
                           (generated-byte-count-of-aligned-slots))))
  :rule-classes nil)

(defthm generated-preserved-prefix-preserves-aligned-suffix
  (let ((lower (proof-stack-base before)))
    (implies (and (equal (proof-stack-base after) lower)
                  (natp left) (natp count) (equal start (+ lower (* 8 left)))
                  (equal top (+ lower (* 8 (+ left count))))
                  (proof-prefix-preserved-p top before after old-objects new-objects packages))
             (equal (proof-stack-views count start (proof-heap-base after) new-objects packages
                                      (proof-world-machine after))
                    (proof-stack-views count start (proof-heap-base before) old-objects packages
                                      (proof-world-machine before)))))
  :hints (("Goal"
           :use ((:instance generated-stack-prefix-has-aligned-slot-count (world before) (objects old-objects))
                 (:instance generated-stack-prefix-has-aligned-slot-count (world after) (objects new-objects))
                 (:instance generated-stack-prefix-at-slot-count (world before) (objects old-objects)
                            (count (+ left count)))
                 (:instance generated-stack-prefix-at-slot-count (world after) (objects new-objects)
                            (count (+ left count)))
                 (:instance generated-stack-views-suffix-from-whole
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (objects old-objects) (machine (proof-world-machine before)))
                 (:instance generated-stack-views-suffix-from-whole
                            (address (proof-stack-base after)) (base (proof-heap-base after))
                            (objects new-objects) (machine (proof-world-machine after))))
           :in-theory (e/d (proof-prefix-preserved-p) (generated-stack-prefix-at-slot-count))))
  :rule-classes nil)

(defthm generated-compiled-arguments-survive-prefix-preservation
  (let* ((top (proof-stack-top before))
         (base (proof-stack-base before)))
    (implies (and (equal (proof-stack-base after) base) (equal (proof-stack-top after) top)
                  (proof-compiled-entry-p (proof-world-pc before) args before old-objects packages)
                  (proof-prefix-preserved-p top before after old-objects new-objects packages)
                  (proof-heap-p after new-objects packages))
             (proof-compiled-entry-p (proof-world-pc after) args after new-objects packages)))
  :hints (("Goal"
           :use ((:instance generated-stack-prefix-has-aligned-slot-count (world before) (objects old-objects)
                            (top (proof-stack-top before)))
                 (:instance generated-preserved-prefix-preserves-aligned-suffix
                            (top (proof-stack-top before)) (count (len args))
                            (left (- (ash (- (proof-stack-top before) (proof-stack-base before)) -3) (len args)))
                            (start (- (proof-stack-top before) (* 8 (len args))))))
           :in-theory (enable proof-compiled-entry-p proof-prefix-preserved-p generated-ash-down-by-three)))
  :rule-classes nil)
