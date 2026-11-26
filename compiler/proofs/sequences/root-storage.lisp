(in-package "BOYMOO-PROOFS")

(include-book "heap-objects")
(include-book "root-prefix")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defun sequence-root-slot-induction (count total address)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons total address)
     (sequence-root-slot-induction (1- count) (1- total) (+ 8 address)))))

(local
 (defthm sequence-nonempty-stack-view-has-slot-marker
   (implies (proof-stack-views count address base objects packages machine)
            (equal (car (proof-stack-views count address base objects packages machine)) :slots))
   :hints (("Goal" :expand ((proof-stack-views count address base objects packages machine))))))

(defthm sequence-stack-views-of-adjacent-slots
  (let ((prefix (proof-stack-views count address base objects packages machine))
        (suffix (proof-stack-views more (+ address (* 8 count)) base objects packages machine)))
    (implies (and (natp count) (natp more) (integerp address) prefix suffix)
             (equal (proof-stack-views (+ count more) address base objects packages machine)
                    (cons :slots (append (cdr prefix) (cdr suffix))))))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-load-word (:definition proof-stack-views))
    :induct (sequence-root-slot-induction count (+ count more) address)
    :expand ((proof-stack-views count address base objects packages machine)
             (proof-stack-views (+ count more) address base objects packages machine)))
   ("Subgoal *1/1"
    :expand ((proof-stack-views 0 address base objects packages machine))
    :use ((:instance sequence-nonempty-stack-view-has-slot-marker (count more)))))
  :rule-classes nil)

(defthm sequence-stack-views-take-prefix
  (let ((full (proof-stack-views total address base objects packages machine)))
    (implies (and (natp count) (natp total) (<= count total) full)
             (equal (proof-stack-views count address base objects packages machine)
                    (cons :slots (take count (cdr full))))))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-load-word (:definition proof-stack-views))
    :induct (sequence-root-slot-induction count total address)
    :expand ((proof-stack-views count address base objects packages machine)
             (proof-stack-views total address base objects packages machine)
             (take count (cdr (proof-stack-views total address base objects packages machine)))))
   ("Subgoal *1/1"
    :expand ((proof-stack-views 0 address base objects packages machine))))
  :rule-classes nil)

(local
 (defthm sequence-aligned-root-count-times-eight
   (implies (and (natp distance) (equal (mod distance 8) 0))
            (equal (* 8 (floor distance 8)) distance))
   :hints (("Goal" :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm sequence-aligned-root-prefix-length
   (implies (and (natp lower) (natp top) (<= lower top)
                 (equal (mod (- top lower) 8) 0) (natp more))
            (let ((count (ash (- top lower) -3))
                  (extended (+ top (* 8 more))))
              (and (natp count)
                   (equal (+ lower (* 8 count)) top)
                   (equal (ash (- extended lower) -3) (+ count more))
                   (equal (mod (- extended lower) 8) 0))))
   :hints
   (("Goal"
     :in-theory (disable sequence-floor-add-multiple sequence-mod-add-multiple)
     :use ((:instance sequence-floor-bounds (value (- top lower)) (divisor 8))
           (:instance sequence-aligned-root-count-times-eight (distance (- top lower)))
           (:instance sequence-floor-add-multiple (value (- top lower)) (divisor 8) (multiple more))
           (:instance sequence-mod-add-multiple (value (- top lower)) (divisor 8) (multiple more)))))
   :rule-classes nil))

(defthm sequence-pushed-root-views
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before))
         (lower (proof-stack-base before))
         (top (proof-stack-top before))
         (next (+ top (* 8 more)))
         (prefix (proof-stack-prefix top before objects packages))
         (suffix (proof-stack-views more top base objects packages last)))
    (implies
     (and (proof-span-p lower (- top lower))
          prefix suffix
          (natp more)
          (equal (proof-heap-base after) base)
          (equal (proof-stack-base after) lower)
          (equal (proof-stack-top after) next)
          (sequence-object-storage-agrees-p objects first last)
          (sequence-machine-span-agrees-p lower top first last))
     (and (proof-prefix-preserved-p top before after objects objects packages)
          (equal (proof-stack-prefix next after objects packages)
                 (cons :slots (append (cdr prefix) (cdr suffix)))))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-stack-prefix proof-prefix-preserved-p)
                    (proof-stack-views proof-load-word proof-view sequence-object-storage-agrees-p
                     sequence-machine-span-agrees-p proof-heap-base proof-stack-top proof-stack-base))
    :use ((:instance sequence-aligned-root-prefix-length
                     (lower (proof-stack-base before)) (top (proof-stack-top before)))
          (:instance sequence-stack-views-on-agreed-storage
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (address (proof-stack-base before)) (lower (proof-stack-base before))
                     (upper (proof-stack-top before)) (base (proof-heap-base before))
                     (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3)))
          (:instance sequence-stack-views-of-adjacent-slots
                     (machine (proof-world-machine after)) (address (proof-stack-base before))
                     (base (proof-heap-base before))
                     (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))))))
  :rule-classes nil)

(local
 (defthm sequence-stack-views-of-equal-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-stack-views count address base objects packages last)
                   (proof-stack-views count address base objects packages first)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-load-word)
                     (proof-view (:definition proof-stack-views)))
     :induct (sequence-root-slot-induction count count address)
     :expand ((:free (machine) (proof-stack-views count address base objects packages machine))))
    ("Subgoal *1/2"
     :use ((:instance sequence-view-of-equal-memory (word (proof-load-word address first))))))
   :rule-classes nil))

(defthm sequence-popped-root-views
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before))
         (lower (proof-stack-base before))
         (top (proof-stack-top before))
         (next (proof-stack-top after)))
    (implies
     (and (proof-stack-prefix top before objects packages)
          (natp lower) (natp next) (<= lower next) (<= next top)
          (equal (mod (- next lower) 8) 0)
          (equal (proof-heap-base after) base)
          (equal (proof-stack-base after) lower)
          (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first)))
     (proof-prefix-preserved-p next before after objects objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-stack-prefix proof-prefix-preserved-p)
                    (proof-stack-views proof-load-word proof-view proof-world-machine
                     proof-heap-base proof-stack-top proof-stack-base))
    :use ((:instance sequence-aligned-root-prefix-length (more 0)
                     (lower (proof-stack-base before)) (top (proof-stack-top before)))
          (:instance sequence-aligned-root-prefix-length (more 0)
                     (lower (proof-stack-base before)) (top (proof-stack-top after)))
          (:instance sequence-stack-views-take-prefix
                     (address (proof-stack-base before)) (base (proof-heap-base before))
                     (machine (proof-world-machine before))
                     (count (ash (- (proof-stack-top after) (proof-stack-base before)) -3))
                     (total (ash (- (proof-stack-top before) (proof-stack-base before)) -3)))
          (:instance sequence-stack-views-of-equal-memory
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (address (proof-stack-base before)) (base (proof-heap-base before))
                     (count (ash (- (proof-stack-top after) (proof-stack-base before)) -3))))))
  :rule-classes nil)
