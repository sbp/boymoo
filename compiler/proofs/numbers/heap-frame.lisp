(in-package "BOYMOO-PROOFS")

(include-book "object-publication")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-stop
                     proof-world-regions proof-world-page-size
                     proof-step proof-run proof-view proof-value-p
                     proof-object-map-p proof-static-p proof-object-size
                     proof-external-objects proof-heap-object-spans-p
                     proof-number-machine-span-agrees-p proof-memory-span-agrees-p
                     proof-covered-p proof-align-up proof-regions-p proof-page-size-p
                     proof-stack-views proof-dynamic-entries proof-dynamic-symbol-objects-p
                     boymoo-model::a64-sp boymoo-model::a64-load
                     boymoo-model::a64-memory boymoo-model::a64-read-bytes
                     boymoo-model::a64-unsigned
                     mod floor ash acl2::binary-logand)))

(defund proof-number-same-heap-state-p (before after)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after)))
    (and (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
         (equal (boymoo-model::a64-sp first) (boymoo-model::a64-sp last))
         (equal (proof-world-reg 23 before) (proof-world-reg 23 after))
         (equal (proof-world-reg 24 before) (proof-world-reg 24 after))
         (equal (proof-world-reg 25 before) (proof-world-reg 25 after))
         (equal (proof-world-reg 26 before) (proof-world-reg 26 after))
         (equal (proof-world-reg 27 before) (proof-world-reg 27 after))
         (equal (proof-world-reg 28 before) (proof-world-reg 28 after))
         (equal (proof-world-page-size before) (proof-world-page-size after))
         (equal (proof-world-regions before) (proof-world-regions after))
         (equal (proof-world-stop before) (proof-world-stop after)))))

(local
 (defthm same-state-keeps-layout
   (implies (proof-number-same-heap-state-p before after)
            (equal (proof-heap-layout-p after) (proof-heap-layout-p before)))
   :hints (("Goal"
            :in-theory (e/d (proof-number-same-heap-state-p boymoo-model::a64-load)
                            (proof-span-p proof-subspan-p proof-disjoint-p))))))

(local
 (defthm same-state-keeps-external-chain
   (implies (proof-number-same-heap-state-p before after)
            (equal (proof-external-objects head fuel after objects)
                   (proof-external-objects head fuel before objects)))
   :hints (("Goal"
            :induct (proof-external-objects head fuel before objects)
            :expand ((:free (head)
                             (proof-external-objects head fuel before objects))
                     (:free (head)
                             (proof-external-objects head fuel after objects)))
            :in-theory (e/d ((:induction proof-external-objects)
                             proof-number-same-heap-state-p boymoo-model::a64-load)
                            (proof-disjoint-p proof-header-type proof-header-size))))))

(local
 (defthmd object-size-with-same-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-object-size object last) (proof-object-size object first)))
   :hints (("Goal" :in-theory (enable proof-object-size boymoo-model::a64-load)))))

(local
 (defthm same-state-keeps-object-spans
   (implies (proof-number-same-heap-state-p before after)
            (equal (proof-heap-object-spans-p objects external after)
                   (proof-heap-object-spans-p objects external before)))
   :hints (("Goal"
            :induct (proof-heap-object-spans-p objects external before)
            :in-theory (e/d (proof-heap-object-spans-p proof-number-same-heap-state-p
                             boymoo-model::a64-load)
                            (proof-subspan-p)))
           ("Subgoal *1/3" :use ((:instance object-size-with-same-memory
                                            (object (car objects))
                                            (first (proof-world-machine before))
                                            (last (proof-world-machine after)))))
           ("Subgoal *1/2" :use ((:instance object-size-with-same-memory
                                            (object (car objects))
                                            (first (proof-world-machine before))
                                            (last (proof-world-machine after))))))))

(local
 (defund memory-image (machine)
   (boymoo-model::a64-state nil 0 0 0 (boymoo-model::a64-memory machine))))

(local
 (defthm image-memory
   (equal (boymoo-model::a64-memory (memory-image machine)) (boymoo-model::a64-memory machine))
   :hints (("Goal" :in-theory (enable memory-image boymoo-model::a64-memory)))))

(local
 (defthm view-in-memory-image
   (equal (proof-view word base objects packages (memory-image machine))
          (proof-view word base objects packages machine))
   :hints (("Goal" :use ((:instance proof-number-view-kept-with-memory
                                     (first machine) (last (memory-image machine))))))))

(local
 (defthm symbol-test-in-memory-image
   (equal (proof-symbol-object-p object (memory-image machine))
          (proof-symbol-object-p object machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load)))))

(local
 (defthm object-view-in-memory-image
   (equal (proof-object-view object base objects packages (memory-image machine))
          (proof-object-view object base objects packages machine))))

(local
 (defthm size-in-memory-image
   (equal (proof-object-size object (memory-image machine)) (proof-object-size object machine))
   :hints (("Goal" :use ((:instance object-size-with-same-memory
                                     (first machine) (last (memory-image machine))))))))

(local
 (defthm object-disjointness-in-memory-image
   (equal (proof-object-disjoint-p address end objects (memory-image machine))
          (proof-object-disjoint-p address end objects machine))
   :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine)))))

(local
 (defthm object-map-in-memory-image
   (equal (proof-object-map-p pending objects symbols base packages (memory-image machine))
          (proof-object-map-p pending objects symbols base packages machine))
   :hints (("Goal"
            :induct (proof-object-map-p pending objects symbols base packages machine)
            :in-theory (enable proof-object-map-p)))))

(local
 (defthm static-spans-in-memory-image
   (equal (proof-static-spans-p objects base size (memory-image machine))
          (proof-static-spans-p objects base size machine))
   :hints (("Goal" :induct (proof-static-spans-p objects base size machine)))))

(local
 (defthm home-bindings-in-memory-image
   (equal (proof-home-bindings-p pending base objects packages (memory-image machine) buckets)
          (proof-home-bindings-p pending base objects packages machine buckets))
   :hints (("Goal" :induct (proof-home-bindings-p pending base objects packages machine buckets)
                   :in-theory (enable boymoo-model::a64-load)))))

(local
 (defthm static-block-in-memory-image
   (equal (proof-static-p base objects packages (memory-image machine))
          (proof-static-p base objects packages machine))
   :hints (("Goal" :in-theory (e/d (proof-static-p proof-value-p boymoo-model::a64-load)
                                  (proof-static-spans-p proof-home-bindings-p
                                   proof-static-buckets-p proof-packages-p
                                   proof-package-bindings-p))))))

(local
 (defthm stack-views-in-memory-image
   (equal (proof-stack-views count address base objects packages (memory-image machine))
          (proof-stack-views count address base objects packages machine))
   :hints (("Goal" :induct (proof-stack-views count address base objects packages machine)
                   :in-theory (enable proof-stack-views boymoo-model::a64-load)))))

(local
 (defthm dynamic-symbols-in-memory-image
   (equal (proof-dynamic-symbol-objects-p pending objects entries base packages (memory-image machine))
          (proof-dynamic-symbol-objects-p pending objects entries base packages machine))
   :hints (("Goal" :induct (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
                   :in-theory (enable proof-dynamic-symbol-objects-p)))))

(local
 (defthm symbols-and-value-stack-with-same-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (and (equal (proof-static-p base objects packages last)
                        (proof-static-p base objects packages first))
                 (equal (proof-object-map-p pending objects symbols base packages last)
                        (proof-object-map-p pending objects symbols base packages first))
                 (equal (proof-dynamic-symbol-objects-p pending objects entries base packages last)
                        (proof-dynamic-symbol-objects-p pending objects entries base packages first))
                 (equal (proof-stack-views count address base objects packages last)
                        (proof-stack-views count address base objects packages first))))
   :hints (("Goal"
            :use ((:instance static-block-in-memory-image (machine first))
                  (:instance static-block-in-memory-image (machine last))
                  (:instance object-map-in-memory-image (machine first))
                  (:instance object-map-in-memory-image (machine last))
                  (:instance dynamic-symbols-in-memory-image (machine first))
                  (:instance dynamic-symbols-in-memory-image (machine last))
                  (:instance stack-views-in-memory-image (machine first))
                  (:instance stack-views-in-memory-image (machine last)))
            :in-theory (e/d (memory-image)
                            (static-block-in-memory-image object-map-in-memory-image
                             dynamic-symbols-in-memory-image stack-views-in-memory-image))))))

(local
 (defthmd external-bytes-with-same-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-external-bytes headers last)
                   (proof-external-bytes headers first)))
   :hints (("Goal" :induct (proof-external-bytes headers first)
                   :in-theory (enable boymoo-model::a64-load)))))

(defthm proof-number-same-state-keeps-heap
  (implies (proof-number-same-heap-state-p before after)
           (equal (proof-heap-p after objects packages) (proof-heap-p before objects packages)))
  :hints (("Goal"
           :use (same-state-keeps-layout
                 (:instance same-state-keeps-external-chain
                            (head (proof-external-head before)) (fuel (len objects)))
                 (:instance same-state-keeps-object-spans
                            (external (cdr (proof-external-objects (proof-external-head before)
                                                                   (len objects) before objects))))
                 (:instance external-bytes-with-same-memory
                            (headers (cdr (proof-external-objects (proof-external-head before)
                                                                  (len objects) before objects)))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance symbols-and-value-stack-with-same-memory
                            (base (proof-heap-base before)) (pending objects) (symbols nil)
                            (first (proof-world-machine before)) (last (proof-world-machine after))
                            (entries (cdr (proof-dynamic-entries
                                          (proof-dynamic-view before objects packages) packages)))
                            (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))
                            (address (proof-stack-base before)))
                 (:instance proof-number-view-kept-with-memory
                            (word (proof-dynamic-root (proof-heap-base before)
                                                      (proof-world-machine before)))
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (e/d (proof-number-same-heap-state-p boymoo-model::a64-load)
                           (proof-heap-layout-p same-state-keeps-layout
                            same-state-keeps-external-chain same-state-keeps-object-spans
                            proof-external-bytes symbols-and-value-stack-with-same-memory))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-same-state-keeps-prefix
  (implies (proof-number-same-heap-state-p before after)
           (equal (proof-stack-prefix top after objects packages)
                  (proof-stack-prefix top before objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-and-value-stack-with-same-memory
                            (base (proof-heap-base before)) (pending nil) (symbols nil) (entries nil)
                            (first (proof-world-machine before)) (last (proof-world-machine after))
                            (count (ash (- top (proof-stack-base before)) -3))
                            (address (proof-stack-base before))))
           :in-theory (e/d (proof-number-same-heap-state-p boymoo-model::a64-load)
                           (symbols-and-value-stack-with-same-memory))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-world-span-agrees-with-same-memory
  (implies (equal (boymoo-model::a64-memory (proof-world-machine before))
                  (boymoo-model::a64-memory (proof-world-machine after)))
           (proof-memory-span-agrees-p low high before after))
  :hints (("Goal"
           :use ((:instance proof-number-span-agreement-with-same-memory
                            (first (proof-world-machine before)) (last (proof-world-machine after))
                            (start low) (end high)))
           :in-theory (enable proof-memory-span-agrees-p proof-number-machine-span-agrees-p
                              proof-world-machine)))
  :rule-classes nil)

(defthm proof-number-same-state-preserves-heap
  (implies (and (proof-number-same-heap-state-p before after)
                (proof-streams-preserved-p before after)
                (proof-heap-p before objects packages))
           (proof-preserved-heap-p nil before after objects objects packages))
  :hints (("Goal"
           :use (proof-number-same-state-keeps-heap
                 (:instance proof-number-same-state-keeps-prefix (top (proof-stack-top before)))
                 (:instance proof-number-view-kept-with-memory
                            (word (proof-dynamic-root (proof-heap-base before)
                                                      (proof-world-machine before)))
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-world-span-agrees-with-same-memory
                            (low (proof-heap-base before)) (high (+ 24 (proof-heap-base before))))
                 (:instance proof-number-world-span-agrees-with-same-memory
                            (low (+ 32 (proof-heap-base before)))
                            (high (+ (proof-heap-base before)
                                     (proof-static-size (proof-heap-base before)
                                                        (proof-world-machine before)))))
                 (:instance proof-number-world-span-agrees-with-same-memory
                            (low (boymoo-model::a64-sp (proof-world-machine before)))
                            (high (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                     *proof-machine-reservation*))))
           :in-theory (e/d (proof-number-same-heap-state-p boymoo-model::a64-load)
                           (proof-heap-layout-p proof-string-accounting-p same-state-keeps-layout
                            same-state-keeps-external-chain same-state-keeps-object-spans
                            symbols-and-value-stack-with-same-memory proof-external-bytes
                            proof-streams-preserved-p proof-stack-views))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm subset-kept-on-cons
   (implies (subsetp-equal left right)
            (subsetp-equal left (cons entry right)))
   :hints (("Goal" :induct (subsetp-equal left right)))))

(defthm proof-number-static-objects-are-subset
  (subsetp-equal (proof-static-objects objects) objects)
  :hints (("Goal" :induct (proof-static-objects objects))))

(defthm proof-number-boolean-words-have-views
  (implies (proof-heap-p world objects packages)
           (and (proof-machine-value-p *proof-t* t world objects packages)
                (proof-machine-value-p *proof-nil* nil world objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-map-spans-with-unchanged-memory
                            (pending (proof-static-objects objects)) (old-objects objects)
                            (extra nil) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-view-kept-with-object-memory
                            (word *proof-t*) (base (proof-heap-base world))
                            (old-objects (proof-static-objects objects))
                            (first (proof-world-machine world)) (last (proof-world-machine world)))
                 (:instance proof-number-view-kept-with-object-memory
                            (word *proof-nil*) (base (proof-heap-base world))
                            (old-objects (proof-static-objects objects))
                            (first (proof-world-machine world)) (last (proof-world-machine world))))
           :in-theory (e/d (proof-static-p proof-value-p)
                           (proof-static-spans-p proof-home-bindings-p proof-package-bindings-p
                            proof-packages-p proof-static-buckets-p proof-heap-layout-p
                            proof-stack-prefix proof-string-accounting-p))
           :do-not-induct t))
  :rule-classes nil)
