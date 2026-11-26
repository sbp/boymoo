(in-package "BOYMOO-PROOFS")

(include-book "stack-pop")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-stack-prefix proof-prefix-preserved-p proof-stack-views
                    proof-environment-p proof-machine-value-p proof-heap-p
                    proof-world-machine proof-load-word proof-view
                    proof-stack-base proof-stack-top proof-heap-base proof-subspan-p
                    generated-stack-views-are-word-views generated-stack-views-have-valid-prefix
                    generated-load-word ash mod floor expt))

(defthm generated-stack-base-natp
  (natp (proof-stack-base world))
  :hints (("Goal"
           :use (:instance generated-word-load-bounds (address (- (proof-heap-base world) 88)))
           :in-theory (enable proof-stack-base proof-runtime-word generated-load-word)))
  :rule-classes :type-prescription)

(defthm generated-stack-top-natp
  (natp (proof-stack-top world))
  :hints (("Goal" :in-theory (enable proof-stack-top)))
  :rule-classes :type-prescription)

(defthm generated-length-of-appended-lists
  (equal (len (append first second)) (+ (len first) (len second)))
  :hints (("Goal" :induct (len first))))

(local
 (defun generated-stack-slot-induction (index count address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (cons count address)
     (generated-stack-slot-induction (1- index) (1- count) (+ 8 address)))))

(defthm generated-stack-views-at-slot
  (let ((views (proof-stack-views count address base objects packages machine)))
    (implies (and (natp slot) (natp count) (< slot count) (integerp address) views)
             (equal (nth slot (cdr views))
                    (proof-view (proof-load-word (+ address (* 8 slot)) machine)
                                base objects packages machine))))
  :hints (("Goal" :induct (generated-stack-slot-induction slot count address)
                  :in-theory (enable nth))
          ("Subgoal *1/2" :expand (proof-stack-views count address base objects packages machine))
          ("Subgoal *1/1" :expand (proof-stack-views count address base objects packages machine))))

(local
 (defun generated-stack-split-induction (first rest address)
   (declare (xargs :measure (nfix first)))
   (if (zp first)
       (cons rest address)
     (generated-stack-split-induction (1- first) rest (+ 8 address)))))

(defthm generated-stack-views-have-slot-tag
  (let ((views (proof-stack-views count address base objects packages machine)))
    (implies views (equal (cons :slots (cdr views)) views)))
  :hints (("Goal" :expand (proof-stack-views count address base objects packages machine))))

(defthm generated-stack-views-split
  (let* ((prefix (proof-stack-views first address base objects packages machine))
         (suffix (proof-stack-views rest (+ address (* 8 first)) base objects packages machine)))
    (implies (and (natp first) (natp rest) (integerp address))
             (equal (proof-stack-views (+ first rest) address base objects packages machine)
                    (and prefix suffix (cons :slots (append (cdr prefix) (cdr suffix)))))))
  :hints (("Goal" :induct (generated-stack-split-induction first rest address)
                  :in-theory (enable proof-stack-views)))
  :rule-classes nil)

(local
 (defthm generated-count-of-eight-byte-slots
   (implies (natp count)
            (and (equal (mod (* 8 count) 8) 0)
                 (equal (ash (* 8 count) -3) count)))
   :hints (("Goal"
            :use (:instance generated-floor-of-multiple-and-remainder (divisor 8) (q count) (r 0))
            :in-theory (enable mod)))))

(local
 (defthm generated-slot-top-minus-stack-base
   (implies (and (integerp base) (integerp count))
            (equal (+ base (- base) (* 8 count)) (* 8 count)))
   :hints (("Goal" :use (:instance associativity-of-*
                                   (acl2::x 1) (acl2::y 8) (acl2::z count))))))

(defthm generated-stack-prefix-at-slot-count
  (let ((address (proof-stack-base world)))
    (implies (and (natp count) (equal top (+ address (* 8 count)))
                  (<= top (proof-stack-top world)))
             (equal (proof-stack-prefix top world objects packages)
                    (proof-stack-views count address (proof-heap-base world)
                                       objects packages (proof-world-machine world)))))
  :hints (("Goal" :in-theory (enable proof-stack-prefix))))

(defthm generated-prefix-preserved-transitive
  (implies (and (proof-prefix-preserved-p top first middle first-objects middle-objects packages)
                (proof-prefix-preserved-p top middle last middle-objects last-objects packages))
           (proof-prefix-preserved-p top first last first-objects last-objects packages))
  :hints (("Goal" :in-theory (enable proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-prefix-preserved-at-smaller-top
  (let ((base (proof-stack-base before)))
    (implies (and (equal (proof-stack-base after) base)
                  (natp count) (equal top (+ base (* 8 count)))
                  (<= top retained)
                  (proof-prefix-preserved-p retained before after old-objects new-objects packages))
             (proof-prefix-preserved-p top before after old-objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance generated-stack-views-have-valid-prefix
                            (small count) (large (ash (- retained (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (objects old-objects) (machine (proof-world-machine before)))
                 (:instance generated-stack-views-have-valid-prefix
                            (small count) (large (ash (- retained (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base after))
                            (objects new-objects) (machine (proof-world-machine after)))
                 (:instance generated-byte-count-of-aligned-slots
                            (size (- retained (proof-stack-base before)))))
           :in-theory (e/d (proof-prefix-preserved-p proof-stack-prefix)
                           (generated-stack-views-have-valid-prefix generated-stack-prefix-at-slot-count
                            generated-byte-count-of-aligned-slots))))
  :rule-classes nil)

(defthm generated-prefix-preserved-preserves-slot-view
  (let ((base (proof-stack-base before)))
    (implies (and (equal (proof-stack-base after) base)
                  (proof-subspan-p address 8 base retained)
                  (natp slot) (equal address (+ base (* 8 slot)))
                  (proof-prefix-preserved-p retained before after old-objects new-objects packages))
             (equal (proof-view (proof-load-word address (proof-world-machine after))
                                (proof-heap-base after) new-objects packages (proof-world-machine after))
                    (proof-view (proof-load-word address (proof-world-machine before))
                                (proof-heap-base before) old-objects packages (proof-world-machine before)))))
  :hints (("Goal"
           :use ((:instance generated-stack-views-at-slot
                            (count (ash (- retained (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base before))
                            (objects old-objects) (machine (proof-world-machine before)))
                 (:instance generated-stack-views-at-slot
                            (count (ash (- retained (proof-stack-base before)) -3))
                            (address (proof-stack-base before)) (base (proof-heap-base after))
                            (objects new-objects) (machine (proof-world-machine after)))
                 (:instance generated-byte-count-of-aligned-slots
                            (size (- retained (proof-stack-base before)))))
           :in-theory (e/d (proof-prefix-preserved-p proof-stack-prefix proof-subspan-p)
                           (generated-stack-views-at-slot generated-byte-count-of-aligned-slots))))
  :rule-classes nil)

(local
 (defthm generated-retained-top-fits-after
   (implies (proof-prefix-preserved-p top before after old-objects new-objects packages)
            (<= top (proof-stack-top after)))
   :hints (("Goal" :in-theory (enable proof-prefix-preserved-p proof-stack-prefix)))
   :rule-classes nil))

(defthm generated-prefix-preserves-aligned-environment
  (let ((base (proof-stack-base before)))
    (implies (and (natp offset) (equal frame (+ base (* 8 offset)))
                  (equal (proof-stack-base after) base)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after old-objects new-objects packages)
                  (proof-environment-p bindings env frame before old-objects packages))
             (proof-environment-p bindings env frame after new-objects packages)))
  :hints (("Goal" :induct (len bindings))
          ("Subgoal *1/1"
           :use ((:instance generated-prefix-preserved-preserves-slot-view
                            (retained (proof-stack-top before)) (slot (+ offset (cdar bindings)))
                            (address (+ frame (* 8 (cdar bindings)))))
                 (:instance generated-retained-top-fits-after (top (proof-stack-top before))))
           :in-theory (enable proof-environment-p proof-subspan-p proof-machine-value-p proof-value-p))
          ("Subgoal *1/2" :in-theory (enable proof-environment-p))))
