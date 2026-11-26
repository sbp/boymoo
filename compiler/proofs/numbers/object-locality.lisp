(in-package "BOYMOO-PROOFS")

(include-book "fresh-views")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-view proof-pointer-address
                     proof-object-address proof-object-size proof-header-size
                     proof-header-type proof-word-tag proof-number-slot-ash-is-floor
                     proof-number-integer-parity boymoo-model::a64-unsigned
                     boymoo-model::a64-memory boymoo-model::a64-byte
                     acl2::binary-logand mod floor ash)))

(local
 (defthm byte-check-narrows
   (implies (and (proof-byte-entries-agree-p entries lower upper first last)
                 (<= lower start) (<= end upper))
            (proof-byte-entries-agree-p entries start end first last))
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper first last)))))

(defthm proof-number-subspan-agrees
  (implies (and (proof-number-machine-span-agrees-p lower upper first last)
                (<= lower start) (<= end upper))
           (proof-number-machine-span-agrees-p start end first last))
  :hints (("Goal" :in-theory (e/d (proof-number-machine-span-agrees-p)
                                 (proof-byte-entries-agree-p))))
  :rule-classes nil)

(local
 (defthm byte-check-when-memories-match
   (proof-byte-entries-agree-p entries lower upper memory memory)
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper memory memory)))))

(defthm proof-number-span-agreement-with-same-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (proof-number-machine-span-agrees-p start end first last))
  :hints (("Goal" :in-theory (e/d (proof-number-machine-span-agrees-p)
                                 (proof-byte-entries-agree-p))))
  :rule-classes nil)

(local
 (defthm check-byte-at-present-key
   (implies (and (assoc-equal address entries) (<= start address) (< address end)
                 (proof-byte-entries-agree-p entries start end first last))
            (equal (boymoo-model::a64-byte address last)
                   (boymoo-model::a64-byte address first)))
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries start end first last)))
   :rule-classes nil))

(defthm proof-number-byte-agrees-in-machine-span
   (let ((a (boymoo-model::a64-memory first))
         (b (boymoo-model::a64-memory last)))
     (implies (and (unsigned-byte-p 64 address)
                   (<= start address) (< address end)
                   (proof-number-machine-span-agrees-p start end first last))
              (equal (boymoo-model::a64-byte address b)
                     (boymoo-model::a64-byte address a))))
   :hints (("Goal"
            :use ((:instance check-byte-at-present-key
                             (entries (boymoo-model::a64-memory first))
                             (first (boymoo-model::a64-memory first))
                             (last (boymoo-model::a64-memory last)))
                  (:instance check-byte-at-present-key
                             (entries (boymoo-model::a64-memory last))
                             (first (boymoo-model::a64-memory first))
                             (last (boymoo-model::a64-memory last))))
            :in-theory (e/d (proof-number-machine-span-agrees-p boymoo-model::a64-byte)
                           (proof-byte-entries-agree-p))
            :cases ((assoc-equal address (boymoo-model::a64-memory first))
                    (assoc-equal address (boymoo-model::a64-memory last)))))
   :rule-classes nil)

(local
 (defthm byte-list-kept-in-span
   (implies (and (natp address) (<= lower address) (natp count)
                 (<= (+ address count) upper) (<= upper (expt 2 64))
                 (proof-number-machine-span-agrees-p lower upper first last))
            (equal (proof-byte-list count address last)
                   (proof-byte-list count address first)))
   :hints (("Goal" :induct (proof-byte-list count address first))
           ("Subgoal *1/2"
            :use ((:instance proof-number-byte-agrees-in-machine-span (start lower) (end upper)))))
   :rule-classes nil))

(local
 (defthm string-kept-in-span
   (implies (and (natp address) (<= lower address) (natp count)
                 (<= (+ address count) upper) (<= upper (expt 2 64))
                 (proof-number-machine-span-agrees-p lower upper first last))
            (equal (proof-load-string count address last)
                   (proof-load-string count address first)))
   :hints (("Goal" :use byte-list-kept-in-span :in-theory (disable proof-byte-list)))
   :rule-classes nil))

(local
 (defthm object-read-fits-size
   (implies (natp payload)
            (<= (+ 8 payload) (+ 8 (proof-align-up payload 8))))
   :hints (("Goal" :in-theory (disable proof-align-up)))
   :rule-classes :linear))

(defund proof-number-object-memory-p (object objects first last)
  (let* ((start (proof-object-address object))
         (size (proof-object-size object first)))
    (and (equal (assoc-equal start objects) object)
         (proof-span-p start size)
         (proof-number-machine-span-agrees-p start (+ start size) first last))))

(defun proof-number-objects-memory-p (pending objects first last)
  (if (atom pending)
      t
    (and (proof-number-object-memory-p (car pending) objects first last)
         (proof-number-objects-memory-p (cdr pending) objects first last))))

(defthm proof-number-object-memory-at-lookup
  (implies (and (assoc-equal address pending)
                (proof-number-objects-memory-p pending objects first last))
           (proof-number-object-memory-p (assoc-equal address pending) objects first last))
  :hints (("Goal" :induct (assoc-equal address pending)
                  :in-theory (disable proof-number-object-memory-p))))

(local
 (defthm key-of-associated-object
   (implies (assoc-equal address objects)
            (equal (proof-object-address (assoc-equal address objects)) address))
   :hints (("Goal" :induct (assoc-equal address objects)
                   :in-theory (enable proof-object-address)))))

(local
 (defthm header-size-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds
                             (a (proof-load-word address machine)) (b 256)))
            :in-theory (enable proof-header-size)))
   :rule-classes :type-prescription))

(defthm proof-number-object-memory-keeps-header
  (let ((address (proof-object-address object)))
    (implies (proof-number-object-memory-p object objects first last)
             (equal (proof-load-word address last) (proof-load-word address first))))
  :hints (("Goal"
           :use ((:instance proof-number-word-agrees-in-machine-span
                            (address (proof-object-address object))
                            (lower (proof-object-address object))
                            (upper (+ (proof-object-address object)
                                      (proof-object-size object first)))))
           :in-theory (e/d (proof-number-object-memory-p proof-object-size)
                           (proof-align-up))))
  :rule-classes nil)

(defthm proof-number-object-memory-keeps-size
  (implies (proof-number-object-memory-p object objects first last)
           (equal (proof-object-size object last) (proof-object-size object first)))
  :hints (("Goal"
           :use proof-number-object-memory-keeps-header
           :in-theory (e/d (proof-object-size) (proof-align-up))))
  :rule-classes nil)

(local
 (defthm lookup-retained
   (implies (and (assoc-equal address old-objects)
                 (proof-number-objects-memory-p old-objects objects first last))
            (equal (assoc-equal address objects) (assoc-equal address old-objects)))
   :hints (("Goal"
            :use ((:instance proof-number-object-memory-at-lookup (pending old-objects)))
            :in-theory (e/d (proof-number-object-memory-p)
                            (proof-number-objects-memory-p proof-number-object-memory-at-lookup))))
   :rule-classes nil))

(local
 (defthm read-agreement-in-object
   (let ((start (proof-object-address object))
         (size (proof-object-size object first)))
     (implies (and (proof-number-object-memory-p object objects first last)
                   (natp (+ start offset))
                   (<= 0 offset) (<= (+ offset 8) size))
              (equal (proof-load-word (+ start offset) last)
                     (proof-load-word (+ start offset) first))))
   :hints (("Goal"
            :use ((:instance proof-number-word-agrees-in-machine-span
                             (address (+ (proof-object-address object) offset))
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object)
                                       (proof-object-size object first)))))
            :in-theory (enable proof-number-object-memory-p)))
   :rule-classes nil))

(local
 (defthm header-object-subspan-agrees
   (let* ((start (proof-object-address object))
          (payload (proof-header-size (proof-load-word start first))))
     (implies (and (proof-number-object-memory-p object objects first last)
                   (not (eq (proof-object-kind object) :cons))
                   (<= start lower) (<= upper (+ start 8 payload)))
              (proof-number-machine-span-agrees-p lower upper first last)))
   :hints (("Goal"
            :use ((:instance proof-number-subspan-agrees (start lower) (end upper)
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object)
                                       (proof-object-size object first)))))
            :in-theory (e/d (proof-number-object-memory-p proof-object-size)
                            (proof-align-up))))
   :rule-classes nil))

(local
 (defthm slot-count-fits
   (implies (natp size)
            (and (natp (ash size -3))
                 (<= (* 8 (ash size -3)) size)))
   :hints (("Goal" :use ((:instance proof-number-positive-divisor-floor-bounds
                                    (a size) (b 8)))
                   :in-theory (enable proof-number-slot-ash-is-floor)))
   :rule-classes ((:type-prescription :corollary
                   (implies (natp size) (natp (ash size -3))))
                  (:linear :corollary
                   (implies (natp size) (<= (* 8 (ash size -3)) size))))))

(local
 (defund view-slot-memory-p (kind input count first last)
   (if (and (eq kind :slots) (posp count))
       (and (proof-span-p input (* 8 count))
            (proof-number-machine-span-agrees-p input (+ input (* 8 count)) first last))
     t)))

(local
 (defthm slots-have-preserved-inputs
   (implies (and (posp count) (view-slot-memory-p :slots input count first last))
            (and (equal (proof-load-word input last) (proof-load-word input first))
                 (view-slot-memory-p :slots (+ 8 input) (1- count) first last)))
   :hints (("Goal"
            :use ((:instance proof-number-word-agrees-in-machine-span
                             (lower input) (address input) (upper (+ input (* 8 count))))
                  (:instance proof-number-subspan-agrees
                             (start (+ 8 input)) (end (+ input (* 8 count)))
                             (lower input) (upper (+ input (* 8 count)))))
            :in-theory (enable view-slot-memory-p)))
   :rule-classes nil))

(local
 (defthm object-view-inputs-kept
   (let* ((address (proof-object-address object))
          (payload (proof-header-size (proof-load-word address first)))
          (cells (eq (proof-object-kind object) :cons)))
     (implies (proof-number-object-memory-p object objects first last)
              (and (equal (proof-load-word address last)
                          (proof-load-word address first))
                   (implies (or cells (<= 8 payload))
                            (equal (proof-load-word (+ 8 address) last)
                                   (proof-load-word (+ 8 address) first)))
                   (implies (and (not cells) (<= 16 payload))
                            (equal (proof-load-word (+ 16 address) last)
                                   (proof-load-word (+ 16 address) first)))
                   (implies (not cells)
                            (and (equal (proof-load-string payload (+ 8 address) last)
                                        (proof-load-string payload (+ 8 address) first))
                                 (implies (proof-integer-view address first)
                                          (equal (proof-integer-view address last)
                                                 (proof-integer-view address first)))
                                 (view-slot-memory-p :slots (+ 8 address)
                                                     (ash payload -3) first last))))))
   :hints (("Goal"
            :use (proof-number-object-memory-keeps-header
                  (:instance read-agreement-in-object (offset 8))
                  (:instance read-agreement-in-object (offset 16))
                  (:instance header-object-subspan-agrees
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object) 8
                                       (proof-header-size (proof-load-word
                                                           (proof-object-address object) first)))))
                  (:instance proof-number-integer-scratch-view-kept
                             (address (proof-object-address object)))
                  (:instance string-kept-in-span
                             (address (+ 8 (proof-object-address object)))
                             (count (proof-header-size (proof-load-word
                                                        (proof-object-address object) first)))
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object)
                                       (proof-object-size object first))))
                  (:instance header-object-subspan-agrees
                             (lower (+ 8 (proof-object-address object)))
                             (upper (+ 8 (proof-object-address object)
                                       (* 8 (ash (proof-header-size
                                                  (proof-load-word
                                                   (proof-object-address object) first)) -3))))))
            :in-theory (e/d (proof-number-object-memory-p proof-object-size view-slot-memory-p)
                            (proof-integer-view proof-load-string proof-align-up))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm pointer-view-inputs-kept
   (let* ((object (assoc-equal address old-objects))
          (payload (proof-header-size (proof-load-word address first)))
          (cells (eq (proof-object-kind object) :cons)))
     (implies (and object (proof-number-objects-memory-p old-objects objects first last))
              (and (equal (assoc-equal address objects) object)
                   (equal (proof-load-word address last) (proof-load-word address first))
                   (implies (or cells (<= 8 payload))
                            (equal (proof-load-word (+ 8 address) last)
                                   (proof-load-word (+ 8 address) first)))
                   (implies (and (not cells) (<= 16 payload))
                            (equal (proof-load-word (+ 16 address) last)
                                   (proof-load-word (+ 16 address) first)))
                   (implies (not cells)
                            (and (equal (proof-load-string payload (+ 8 address) last)
                                        (proof-load-string payload (+ 8 address) first))
                                 (implies (proof-integer-view address first)
                                          (equal (proof-integer-view address last)
                                                 (proof-integer-view address first)))
                                 (view-slot-memory-p :slots (+ 8 address)
                                                     (ash payload -3) first last))))))
   :hints (("Goal"
            :use ((:instance object-view-inputs-kept (object (assoc-equal address old-objects)))
                  lookup-retained)
            :in-theory (disable proof-number-object-memory-at-lookup proof-load-string
                                proof-integer-view)
            :do-not-induct t)
           ("Goal'" :use ((:instance proof-number-object-memory-at-lookup
                                    (pending old-objects)))))
   :rule-classes nil))

(local
 (defthm no-datum-from-missing-fields
   (and (not (proof-rational-value nil second))
        (not (proof-rational-value first nil))
        (not (proof-complex-value nil second))
        (not (proof-complex-value first nil))
        (not (proof-symbol-value nil second packages))
        (not (proof-symbol-value first nil packages))
        (not (proof-cons-value nil second))
        (not (proof-cons-value first nil)))
   :hints (("Goal" :in-theory (enable proof-rational-value proof-complex-value
                                     proof-symbol-value proof-cons-value)))))

(local
 (defthm successful-view-step-kept
   (implies (and (proof-view-step kind input count depth base old-objects packages first)
                 (proof-number-objects-memory-p old-objects objects first last)
                 (view-slot-memory-p kind input count first last))
            (equal (proof-view-step kind input count depth base objects packages last)
                   (proof-view-step kind input count depth base old-objects packages first)))
   :hints (("Goal"
            :induct (proof-view-step kind input count depth base old-objects packages first)
            :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (disable (:definition proof-view-step)
                                proof-load-string proof-integer-view proof-symbol-value
                                proof-rational-value proof-complex-value proof-cons-value
                                proof-number-objects-memory-p)
            :expand ((:free (kind)
                             (proof-view-step kind input count depth base old-objects packages first))
                     (:free (kind)
                             (proof-view-step kind input count depth base objects packages last))))
           ("Subgoal *1/2" :use slots-have-preserved-inputs)
           (and (member-equal '(not (assoc-equal (proof-pointer-address input base) old-objects))
                              clause)
                '(:use ((:instance pointer-view-inputs-kept
                                   (address (proof-pointer-address input base)))))))
   :rule-classes nil))

(defthm proof-number-view-kept-with-object-memory
  (implies (and (proof-view word base old-objects packages first)
                (proof-number-objects-memory-p old-objects objects first last))
           (equal (proof-view word base objects packages last)
                  (proof-view word base old-objects packages first)))
  :hints (("Goal"
           :use ((:instance successful-view-step-kept
                            (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                             (assoc-equal (proof-pointer-address word base)
                                                          old-objects))))))
                 (:instance lookup-retained (address (proof-pointer-address word base))))
           :cases ((assoc-equal (proof-pointer-address word base) old-objects))
           :in-theory (e/d (proof-view view-slot-memory-p)
                           (proof-view-step proof-object-rank proof-number-objects-memory-p)))
          ("Subgoal 2"
           :expand ((proof-view-step :word word 0 1 base old-objects packages first)
                    (:free (depth)
                           (proof-view-step :word word 0 depth base objects packages last)))))
  :rule-classes nil)

(defthm proof-number-stack-views-kept-with-object-memory
  (implies (and (proof-stack-views count address base old-objects packages first)
                (proof-number-objects-memory-p old-objects objects first last)
                (natp count) (natp address)
                (<= (+ address (* 8 count)) (expt 2 64))
                (proof-number-machine-span-agrees-p
                 address (+ address (* 8 count)) first last))
           (equal (proof-stack-views count address base objects packages last)
                  (proof-stack-views count address base old-objects packages first)))
  :hints (("Goal"
           :induct (proof-stack-views count address base old-objects packages first))
          ("Subgoal *1/2"
           :use ((:instance proof-number-word-agrees-in-machine-span
                            (lower address) (upper (+ address (* 8 count))))
                 (:instance proof-number-subspan-agrees
                            (lower address) (upper (+ address (* 8 count)))
                            (start (+ 8 address)) (end (+ address (* 8 count))))
                 (:instance proof-number-view-kept-with-object-memory
                            (word (proof-load-word address first))))))
  :rule-classes nil)

(defthm proof-number-stack-base-range
  (unsigned-byte-p 64 (proof-stack-base world))
  :hints (("Goal" :in-theory (e/d (proof-stack-base proof-runtime-word)
                                 (unsigned-byte-p proof-heap-base proof-world-machine))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (proof-stack-base world)))
                 (:linear :corollary (< (proof-stack-base world) (expt 2 64)))))

(defthm proof-number-stack-top-range
  (unsigned-byte-p 64 (proof-stack-top world))
  :hints (("Goal" :in-theory (e/d (proof-stack-top proof-world-reg) (unsigned-byte-p proof-reg))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (proof-stack-top world)))
                 (:linear :corollary (< (proof-stack-top world) (expt 2 64)))))

(defthm proof-number-prefix-kept-with-object-memory
  (let* ((lower (proof-stack-base before))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and (proof-stack-prefix top before old-objects packages)
                  (equal (proof-stack-base after) lower)
                  (equal (proof-heap-base after) (proof-heap-base before))
                  (<= top (proof-stack-top after))
                  (proof-number-objects-memory-p old-objects objects first last)
                  (proof-number-machine-span-agrees-p lower top first last))
             (proof-prefix-preserved-p top before after old-objects objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-stack-views-kept-with-object-memory
                            (count (ash (- top (proof-stack-base before)) -3))
                            (address (proof-stack-base before))
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-subspan-agrees
                            (lower (proof-stack-base before)) (upper top)
                            (start (proof-stack-base before))
                            (end (+ (proof-stack-base before)
                                    (* 8 (ash (- top (proof-stack-base before)) -3))))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance slot-count-fits (size (- top (proof-stack-base before)))))
           :in-theory (disable proof-stack-base proof-stack-top proof-heap-base
                               proof-world-machine proof-stack-views proof-world-reg
                               proof-number-objects-memory-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-value-kept-with-object-memory
  (implies (and (proof-machine-value-p word value before old-objects packages)
                (equal (proof-heap-base after) (proof-heap-base before))
                (proof-number-objects-memory-p old-objects objects
                                               (proof-world-machine before)
                                               (proof-world-machine after)))
           (proof-machine-value-p word value after objects packages))
  :hints (("Goal"
           :use ((:instance proof-number-view-kept-with-object-memory
                            (base (proof-heap-base before))
                            (first (proof-world-machine before))
                            (last (proof-world-machine after))))
           :in-theory (disable proof-heap-base proof-world-machine proof-number-objects-memory-p)))
  :rule-classes nil)
