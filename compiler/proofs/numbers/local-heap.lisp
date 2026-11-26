(in-package "BOYMOO-PROOFS")

(include-book "static-preservation")
(include-book "external-preservation")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-stop proof-world-regions
                     proof-load-word proof-heap-base proof-stack-base proof-stack-top
                     proof-machine-limit proof-static-size proof-view proof-object-map-p
                     proof-object-record-p proof-object-view proof-object-size proof-heap-p
                     proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                     proof-stack-prefix proof-prefix-preserved-p proof-external-objects
                     proof-external-bytes proof-heap-layout-p proof-heap-object-spans-p proof-static-p
                     proof-number-machine-span-agrees-p proof-memory-span-agrees-p
                     proof-number-objects-memory-p proof-number-object-memory-p
                     proof-number-memory-change-p
                     boymoo-model::a64-memory boymoo-model::a64-sp
                     boymoo-model::a64-unsigned mod floor ash)))

(defund proof-number-machine-stack-end (world)
  (+ (- (proof-machine-limit world) *proof-machine-margin*) *proof-machine-reservation*))

(defund proof-number-local-write-p (start end world)
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (static-end (+ base (proof-static-size base machine))))
    (and (posp start)
         (proof-number-in-runtime-reservation-p start end world)
         (proof-disjoint-p base static-end start end)
         (proof-disjoint-p (proof-stack-base world) (proof-stack-top world) start end)
         (proof-disjoint-p (boymoo-model::a64-sp machine)
                           (proof-number-machine-stack-end world) start end))))

(defthm proof-number-heap-layout-covers-static-and-machine-stack
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (static (proof-static-size base machine)))
    (implies (proof-heap-layout-p world)
             (and (<= 80 static)
                  (proof-span-p base (+ static 24))
                  (<= (proof-number-machine-stack-end world) (expt 2 64)))))
  :hints (("Goal"
           :use (proof-number-heap-layout-range-bounds
                 (:instance proof-number-alignment-does-not-shrink
                            (size (+ (proof-heap-base world)
                                     (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                            (alignment *proof-runtime-page*))
                 (:instance proof-number-reg-range (register 28) (machine (proof-world-machine world)))
                 (:instance proof-number-load-word-range
                            (address (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-heap-layout-p proof-number-machine-stack-end proof-heap-base proof-static-size)
                           (proof-heap-limit proof-box-top proof-stack-limit proof-stack-end
                            proof-spaces-end proof-number-reg-range proof-reg
                            proof-active-floor proof-active-end proof-cons-floor proof-inactive-floor
                            proof-inactive-end proof-align-up proof-disjoint-p proof-covered-p
                            proof-regions-p proof-runtime-word))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm open-heap-has-layout
   (implies (proof-heap-p world objects packages)
            (and (proof-heap-layout-p world)
                 (proof-stack-prefix (proof-stack-top world) world objects packages)))
   :hints (("Goal" :in-theory (enable proof-heap-p)))
   :rule-classes nil))

(defthm proof-number-local-write-preserves-prefix
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after)))
    (implies (and (proof-heap-p before old-objects packages)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (<= (proof-stack-top before) (proof-stack-top after))
                  (proof-number-local-write-p start end before)
                  (proof-number-memory-change-p start end first last)
                  (proof-number-objects-memory-p old-objects objects first last))
             (proof-prefix-preserved-p (proof-stack-top before) before after old-objects objects packages)))
  :hints (("Goal"
           :use ((:instance open-heap-has-layout (world before) (objects old-objects))
                 proof-number-equal-heap-coordinates-preserve-fields
                 (:instance proof-number-disjoint-footprint-keeps-prefix (top (proof-stack-top before))))
           :in-theory (e/d (proof-number-local-write-p)
                           (proof-disjoint-p proof-stack-end proof-spaces-end
                            proof-active-floor proof-active-end proof-cons-floor
                            proof-inactive-floor proof-inactive-end proof-runtime-word))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-local-write-preserves-heap-frame
  (let* ((base (proof-heap-base before))
         (first (proof-world-machine before))
         (last (proof-world-machine after))
         (static-end (+ base (proof-static-size base first))))
    (implies (and (proof-heap-layout-p before)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (proof-streams-preserved-p before after)
                  (proof-number-local-write-p start end before)
                  (proof-number-memory-change-p start end first last))
             (and (proof-heap-frame-p before after)
                  (proof-number-machine-span-agrees-p base static-end first last))))
  :hints (("Goal"
           :use ((:instance proof-number-heap-layout-covers-static-and-machine-stack (world before))
                 proof-number-equal-heap-coordinates-preserve-fields
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (lower (proof-heap-base before))
                            (upper (+ (proof-heap-base before)
                                      (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (lower (boymoo-model::a64-sp (proof-world-machine before)))
                            (upper (proof-number-machine-stack-end before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-subspan-agrees
                            (lower (proof-heap-base before))
                            (upper (+ (proof-heap-base before)
                                      (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                            (start (proof-heap-base before)) (end (+ (proof-heap-base before) 24))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-subspan-agrees
                            (lower (proof-heap-base before))
                            (upper (+ (proof-heap-base before)
                                      (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                            (start (+ (proof-heap-base before) 32))
                            (end (+ (proof-heap-base before)
                                    (proof-static-size (proof-heap-base before) (proof-world-machine before))))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (e/d (proof-number-local-write-p proof-heap-frame-p proof-number-machine-stack-end
                            proof-number-machine-span-agrees-p proof-memory-span-agrees-p proof-world-machine)
                           (proof-disjoint-p proof-stack-end proof-spaces-end proof-byte-entries-agree-p
                            proof-active-floor proof-active-end proof-cons-floor proof-runtime-word
                            proof-inactive-floor proof-inactive-end))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm old-object-spans-remain
   (implies (and (proof-heap-object-spans-p pending external before)
                 (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                 (proof-number-objects-memory-p pending objects
                                                (proof-world-machine before) (proof-world-machine after)))
            (proof-heap-object-spans-p pending external after))
   :hints (("Goal"
            :induct (proof-heap-object-spans-p pending external before)
            :in-theory (e/d (proof-number-objects-memory-p proof-heap-object-spans-p)
                            (proof-subspan-p proof-active-floor proof-active-end
                             proof-cons-floor proof-box-top)))
           (and (member-equal '(not (consp pending)) clause)
                '(:use (proof-number-equal-heap-coordinates-preserve-fields
                        (:instance proof-number-object-memory-keeps-size
                                   (object (car pending))
                                   (first (proof-world-machine before))
                                   (last (proof-world-machine after)))))))
   :rule-classes nil))

(local
 (defthm old-dynamic-symbols-remain
   (implies (and (proof-dynamic-symbol-objects-p pending old-objects entries base packages first)
                 (proof-object-map-p pending old-objects symbols base packages first)
                 (proof-number-objects-memory-p old-objects objects first last)
                 (proof-number-objects-memory-p pending objects first last))
            (proof-dynamic-symbol-objects-p pending objects entries base packages last))
   :hints (("Goal"
            :induct (proof-object-map-p pending old-objects symbols base packages first)
            :expand ((proof-object-map-p pending old-objects symbols base packages first))
            :in-theory (enable (:induction proof-object-map-p)
                               proof-number-objects-memory-p proof-dynamic-symbol-objects-p))
           (and (member-equal '(not (consp pending)) clause)
                '(:use ((:instance proof-number-object-memory-keeps-symbol-test (object (car pending)))
                        (:instance proof-number-object-view-kept (object (car pending)))))))
   :rule-classes nil))

(local
 (defthm valid-dynamic-entries-have-view
   (implies (proof-dynamic-entries root packages) root)
   :hints (("Goal" :cases ((null root))
                   :in-theory (enable proof-dynamic-entries)))
   :rule-classes nil))

(local
 (defthm same-root-word-keeps-dynamic-view
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages)
                   (proof-number-objects-memory-p old-objects objects first last))
              (equal (proof-dynamic-view after objects packages)
                     (proof-dynamic-view before old-objects packages))))
   :hints (("Goal"
            :use (proof-number-equal-heap-coordinates-preserve-fields
                  (:instance valid-dynamic-entries-have-view
                             (root (proof-dynamic-view before old-objects packages)))
                  (:instance proof-number-view-kept-with-object-memory
                             (word (proof-dynamic-root (proof-heap-base before) (proof-world-machine before)))
                             (base (proof-heap-base before))
                             (first (proof-world-machine before)) (last (proof-world-machine after))))
            :in-theory (e/d (proof-dynamic-view)
                            (proof-dynamic-root proof-runtime-word))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm saved-prefix-keeps-top
   (implies (and (proof-prefix-preserved-p (proof-stack-top before)
                                           before after old-objects objects packages)
                 (equal (proof-stack-top before) (proof-stack-top after)))
            (proof-stack-prefix (proof-stack-top after) after objects packages))
   :hints (("Goal" :in-theory (enable proof-prefix-preserved-p)))))

(defund proof-number-extra-active-record-p (extra world)
  (and (eq (proof-object-zone extra) :active)
       (not (proof-symbol-object-p extra (proof-world-machine world)))
       (proof-heap-object-spans-p (list extra) nil world)))

(local
 (defthm layout-has-regions
   (implies (proof-heap-layout-p world)
            (proof-regions-p (proof-world-regions world)))
   :hints (("Goal"
            :expand ((proof-heap-layout-p world))
            :in-theory (disable proof-regions-p proof-covered-p proof-disjoint-p
                                proof-runtime-word proof-align-up)))
   :rule-classes nil))

(local
 (defthm accounting-and-layout-region-facts
   (implies (and (proof-heap-layout-p before)
                 (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                 (equal (proof-external-bytes external (proof-world-machine before))
                        (proof-external-bytes external (proof-world-machine after))))
            (equal (proof-string-accounting-p external before)
                   (proof-string-accounting-p external after)))
   :hints (("Goal"
            :use proof-number-equal-heap-coordinates-preserve-fields
            :in-theory (e/d (proof-heap-layout-p)
                            (proof-string-bytes-since-collection proof-string-budget proof-runtime-word
                             proof-align-up proof-regions-p proof-covered-p proof-disjoint-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm static-records-with-active-addition
   (implies (implies extra (proof-number-extra-active-record-p extra world))
            (equal (proof-static-objects (if extra (cons extra old-objects) old-objects))
                   (proof-static-objects old-objects)))
   :hints (("Goal" :in-theory (enable proof-number-extra-active-record-p)))))

(local
 (defthm local-write-keeps-static-block
   (let ((objects (if extra (cons extra old-objects) old-objects))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-heap-p before old-objects packages)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (proof-streams-preserved-p before after)
                   (proof-number-local-write-p start end before)
                   (proof-number-memory-change-p start end first last)
                   (implies extra (proof-number-extra-active-record-p extra after)))
              (proof-static-p (proof-heap-base after) objects packages last)))
   :hints (("Goal"
            :use ((:instance open-heap-has-layout (world before) (objects old-objects))
                  (:instance proof-number-heap-layout-covers-static-and-machine-stack (world before))
                  proof-number-local-write-preserves-heap-frame
                  proof-number-equal-heap-coordinates-preserve-fields
                  (:instance static-records-with-active-addition (world after))
                  (:instance proof-number-static-block-kept
                             (base (proof-heap-base before))
                             (first (proof-world-machine before)) (last (proof-world-machine after))
                             (objects (if extra (cons extra old-objects) old-objects))))
            :in-theory (e/d (proof-heap-p)
                            (proof-heap-frame-p proof-static-objects static-records-with-active-addition))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm external-objects-kept-by-local-write
   (let* ((objects (if extra (cons extra old-objects) old-objects))
          (external (proof-external-objects (proof-external-head before) (len old-objects) before old-objects))
          (first (proof-world-machine before))
          (last (proof-world-machine after)))
     (implies (and (proof-heap-p before old-objects packages)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (proof-number-local-write-p start end before)
                   (proof-number-memory-change-p start end first last)
                   (proof-number-objects-memory-p old-objects objects first last))
              (and external
                   (equal (proof-external-objects (proof-external-head after) (len objects) after objects) external)
                   (proof-string-accounting-p (cdr external) after))))
   :hints (("Goal"
            :use (proof-number-equal-heap-coordinates-preserve-fields
                  (:instance layout-has-regions (world before))
                  (:instance accounting-and-layout-region-facts
                             (external (cdr (proof-external-objects
                                             (proof-external-head before) (len old-objects) before old-objects))))
                  (:instance proof-number-external-chain-and-accounting-kept
                             (fuel (len old-objects)) (additional-fuel (if extra 1 0))
                             (head (proof-external-head before))
                             (objects (if extra (cons extra old-objects) old-objects))))
            :in-theory (e/d (proof-heap-p proof-number-local-write-p)
                            (proof-external-head proof-runtime-word proof-string-accounting-p proof-regions-p
                             proof-disjoint-p proof-spaces-end proof-stack-end))
            :cases ((not extra))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm object-spans-kept-by-local-write
   (let* ((objects (if extra (cons extra old-objects) old-objects))
          (external (proof-external-objects (proof-external-head before) (len old-objects) before old-objects)))
     (implies (and (proof-heap-p before old-objects packages)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (proof-number-objects-memory-p old-objects objects
                                                  (proof-world-machine before) (proof-world-machine after))
                   (implies extra (proof-number-extra-active-record-p extra after)))
              (proof-heap-object-spans-p objects (cdr external) after)))
   :hints (("Goal"
            :use ((:instance old-object-spans-remain
                             (pending old-objects) (objects (if extra (cons extra old-objects) old-objects))
                             (external (cdr (proof-external-objects
                                             (proof-external-head before) (len old-objects) before old-objects)))))
            :expand ((proof-heap-object-spans-p (cons extra old-objects)
                                                (cdr (proof-external-objects
                                                      (proof-external-head before) (len old-objects)
                                                      before old-objects))
                                                after)
                     (proof-heap-object-spans-p (list extra) nil after))
            :in-theory (e/d (proof-heap-p proof-number-extra-active-record-p)
                            (proof-external-head proof-runtime-word proof-string-accounting-p
                             proof-symbol-object-p proof-subspan-p))
            :cases ((not extra))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm dynamic-root-kept-by-local-write
   (let* ((objects (if extra (cons extra old-objects) old-objects))
          (dynamic (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages))
          (base (proof-heap-base before))
          (last (proof-world-machine after)))
     (implies (and (proof-heap-p before old-objects packages)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (proof-number-objects-memory-p old-objects objects (proof-world-machine before) last)
                   (implies extra (proof-number-extra-active-record-p extra after)))
              (and (proof-dynamic-table-preserved-p nil before after old-objects objects packages)
                   dynamic
                   (equal (proof-dynamic-entries (proof-dynamic-view after objects packages) packages) dynamic)
                   (proof-dynamic-symbol-objects-p objects objects (cdr dynamic) base packages last))))
   :hints (("Goal"
            :use ((:instance same-root-word-keeps-dynamic-view
                             (objects (if extra (cons extra old-objects) old-objects)))
                  (:instance old-dynamic-symbols-remain
                             (pending old-objects) (symbols nil)
                             (first (proof-world-machine before)) (last (proof-world-machine after))
                             (base (proof-heap-base before))
                             (entries (cdr (proof-dynamic-entries (proof-dynamic-view before old-objects packages)
                                                                   packages)))
                             (objects (if extra (cons extra old-objects) old-objects))))
            :expand ((proof-dynamic-symbol-objects-p
                      (cons extra old-objects) (cons extra old-objects)
                      (cdr (proof-dynamic-entries (proof-dynamic-view before old-objects packages) packages))
                      (proof-heap-base before) packages (proof-world-machine after)))
            :in-theory (e/d (proof-heap-p proof-number-extra-active-record-p)
                            (proof-symbol-object-p proof-external-head proof-string-accounting-p))
            :cases ((not extra))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-same-top-local-write-preserves-heap
  (let* ((objects (if extra (cons extra old-objects) old-objects))
         (first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before)))
    (implies (and (proof-heap-p before old-objects packages)
                  (proof-heap-layout-p after)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (proof-streams-preserved-p before after)
                  (proof-number-local-write-p start end before)
                  (proof-number-memory-change-p start end first last)
                  (proof-number-objects-memory-p old-objects objects first last)
                  (proof-object-map-p objects objects nil base packages last)
                  (implies extra (proof-number-extra-active-record-p extra after)))
             (proof-preserved-heap-p nil before after old-objects objects packages)))
  :hints (("Goal"
           :use (proof-number-equal-heap-coordinates-preserve-fields
                 (:instance open-heap-has-layout (world before) (objects old-objects))
                 (:instance proof-number-local-write-preserves-prefix
                            (objects (if extra (cons extra old-objects) old-objects)))
                 proof-number-local-write-preserves-heap-frame
                 (:instance saved-prefix-keeps-top
                            (objects (if extra (cons extra old-objects) old-objects)))
                 local-write-keeps-static-block external-objects-kept-by-local-write
                 object-spans-kept-by-local-write dynamic-root-kept-by-local-write)
           :expand ((:free (items) (proof-heap-p after items packages)))
           :in-theory (disable proof-heap-frame-p proof-external-head proof-string-accounting-p
                               proof-runtime-word proof-dynamic-table-preserved-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-local-write-keeps-heap-with-initialized-stack
  (let* ((objects (if extra (cons extra old-objects) old-objects))
         (first (proof-world-machine before))
         (last (proof-world-machine after))
         (base (proof-heap-base before)))
    (implies (and (proof-heap-p before old-objects packages)
                  (proof-heap-layout-p after)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (proof-stack-prefix (proof-stack-top after) after objects packages)
                  (proof-streams-preserved-p before after)
                  (proof-number-local-write-p start end before)
                  (proof-number-memory-change-p start end first last)
                  (proof-number-objects-memory-p old-objects objects first last)
                  (proof-object-map-p objects objects nil base packages last)
                  (implies extra (proof-number-extra-active-record-p extra after)))
             (and (proof-heap-p after objects packages)
                  (proof-heap-frame-p before after)
                  (proof-dynamic-table-preserved-p nil before after old-objects objects packages))))
  :hints (("Goal"
           :use (proof-number-equal-heap-coordinates-preserve-fields
                 (:instance open-heap-has-layout (world before) (objects old-objects))
                 proof-number-local-write-preserves-heap-frame
                 local-write-keeps-static-block external-objects-kept-by-local-write
                 object-spans-kept-by-local-write dynamic-root-kept-by-local-write)
           :expand ((:free (items) (proof-heap-p after items packages)))
           :in-theory (disable proof-heap-frame-p proof-external-head proof-string-accounting-p
                               proof-runtime-word proof-dynamic-table-preserved-p)
           :do-not-induct t))
  :rule-classes nil)
