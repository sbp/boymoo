(in-package "BOYMOO-PROOFS")

(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                    proof-world-regions proof-world-page-size proof-load-word
                    proof-heap-p proof-heap-layout-p proof-covered-p proof-regions-p
                    proof-object-size proof-object-map-p proof-object-disjoint-p
                    proof-object-view proof-symbol-object-p proof-static-spans-p
                    proof-home-bindings-p proof-static-p proof-static-buckets-p
                    proof-dynamic-symbol-objects-p proof-external-objects proof-external-bytes
                    proof-heap-object-spans-p proof-stack-prefix proof-runtime-word
                    proof-stack-views proof-dynamic-view proof-string-accounting-p
                    proof-stack-base proof-stack-limit proof-stack-top proof-machine-limit
                    proof-stack-end proof-spaces-end proof-heap-base proof-box-top proof-heap-limit
                    proof-align-up proof-argument-views proof-machine-value-p generated-sp
                    boymoo-model::a64-sp proof-disjoint-p proof-span-p proof-subspan-p))

(defcong generated-memory-equiv equal (proof-object-size object machine) 2
  :hints (("Goal" :in-theory (enable proof-object-size))))

(defcong generated-memory-equiv equal (proof-object-view object base objects packages machine) 5
  :hints (("Goal" :in-theory (enable proof-object-view))))

(defcong generated-memory-equiv equal (proof-symbol-object-p object machine) 2
  :hints (("Goal" :in-theory (enable proof-symbol-object-p))))

(defcong generated-memory-equiv equal (proof-object-disjoint-p start end objects machine) 4
  :hints (("Goal" :induct (proof-object-disjoint-p start end objects machine)
                  :in-theory (enable proof-object-disjoint-p))))

(defcong generated-memory-equiv equal (proof-object-map-p pending objects symbols base packages machine) 6
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                  :in-theory (enable proof-object-map-p))))

(defcong generated-memory-equiv equal (proof-static-spans-p objects base size machine) 4
  :hints (("Goal" :induct (proof-static-spans-p objects base size machine)
                  :in-theory (enable proof-static-spans-p))))

(defcong generated-memory-equiv equal (proof-home-bindings-p pending base objects packages machine buckets) 5
  :hints (("Goal" :induct (proof-home-bindings-p pending base objects packages machine buckets)
                  :in-theory (enable proof-home-bindings-p))))

(defcong generated-memory-equiv equal (proof-static-p base objects packages machine) 4
  :hints (("Goal" :in-theory (enable proof-static-p))))

(defcong generated-memory-equiv equal
  (proof-dynamic-symbol-objects-p pending objects entries base packages machine) 6
  :hints (("Goal"
           :induct (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
           :in-theory (enable proof-dynamic-symbol-objects-p))))

(defcong generated-memory-equiv equal (proof-external-bytes headers machine) 2
  :hints (("Goal" :induct (proof-external-bytes headers machine)
                  :in-theory (enable proof-external-bytes))))

(defund generated-heap-world-equiv (left right)
  (and (generated-memory-equiv (proof-world-machine left) (proof-world-machine right))
       (equal (generated-sp left) (generated-sp right))
       (equal (proof-world-stop left) (proof-world-stop right))
       (equal (proof-world-regions left) (proof-world-regions right))
       (equal (proof-world-page-size left) (proof-world-page-size right))
       (equal (proof-machine-limit left) (proof-machine-limit right))
       (equal (proof-stack-limit left) (proof-stack-limit right))
       (equal (proof-stack-top left) (proof-stack-top right))
       (equal (proof-heap-limit left) (proof-heap-limit right))
       (equal (proof-box-top left) (proof-box-top right))
       (equal (proof-heap-base left) (proof-heap-base right))))

(defequiv generated-heap-world-equiv
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv generated-memory-equiv (proof-world-machine world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-heap-base world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-stack-top world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-machine-limit world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-stack-limit world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-heap-limit world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-box-top world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-world-regions world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-world-stop world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (proof-world-page-size world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defcong generated-heap-world-equiv equal (generated-sp world) 1
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv))))

(defthmd generated-heap-machine-sp
  (equal (boymoo-model::a64-sp (proof-world-machine world)) (generated-sp world))
  :hints (("Goal" :in-theory (enable generated-sp))))

(defcong generated-heap-world-equiv equal (proof-runtime-word offset world) 2
  :hints (("Goal" :in-theory (enable proof-runtime-word))))

(defcong generated-heap-world-equiv equal (proof-stack-base world) 1
  :hints (("Goal" :in-theory (enable proof-stack-base))))

(defcong generated-heap-world-equiv equal (proof-stack-end world) 1
  :hints (("Goal" :in-theory (enable proof-stack-end))))

(defcong generated-heap-world-equiv equal (proof-spaces-end world) 1
  :hints (("Goal" :in-theory (enable proof-spaces-end))))

(defcong generated-heap-world-equiv equal (proof-heap-layout-p world) 1
  :hints (("Goal" :in-theory (enable proof-heap-layout-p generated-heap-machine-sp))))

(defcong generated-heap-world-equiv equal (proof-external-objects head fuel world objects) 3
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                  :expand ((proof-external-objects head fuel world objects)
                           (proof-external-objects head fuel world-equiv objects))
                  :in-theory (enable proof-external-objects))))

(defcong generated-heap-world-equiv equal (proof-heap-object-spans-p objects external world) 3
  :hints (("Goal" :induct (proof-heap-object-spans-p objects external world)
                  :in-theory (enable proof-heap-object-spans-p))))

(defcong generated-heap-world-equiv equal (proof-string-accounting-p headers world) 2
  :hints (("Goal" :in-theory (enable proof-string-accounting-p))))

(defcong generated-heap-world-equiv equal (proof-stack-prefix top world objects packages) 2
  :hints (("Goal" :in-theory (enable proof-stack-prefix proof-stack-base))))

(defcong generated-heap-world-equiv equal (proof-dynamic-view world objects packages) 1
  :hints (("Goal" :in-theory (enable proof-dynamic-view))))

(defcong generated-heap-world-equiv equal (proof-heap-p world objects packages) 1
  :hints (("Goal" :in-theory (enable proof-heap-p))))

(defcong generated-heap-world-equiv equal (proof-machine-value-p word value world objects packages) 3
  :hints (("Goal" :in-theory (enable proof-machine-value-p))))

(defcong generated-heap-world-equiv equal (proof-environment-p bindings env frame world objects packages) 4
  :hints (("Goal" :induct (proof-environment-p bindings env frame world objects packages)
                  :in-theory (enable proof-stack-base))))

(defthm generated-page-size-of-updates
  (and (equal (proof-world-page-size (generated-set-pc pc world)) (proof-world-page-size world))
       (equal (proof-world-page-size (generated-set-reg register value world))
              (proof-world-page-size world))
       (equal (proof-world-page-size (generated-set-flags flags world)) (proof-world-page-size world))
       (equal (proof-world-page-size (generated-store-word address value world))
              (proof-world-page-size world)))
  :hints (("Goal" :in-theory (enable generated-set-pc generated-set-reg generated-set-flags
                                    generated-store-word))))

(defthm generated-heap-equiv-of-register-updates
  (and (generated-heap-world-equiv (generated-set-pc pc world) world)
       (generated-heap-world-equiv (generated-set-flags flags world) world)
       (implies (and (natp register) (< register 31)
                     (not (member-equal register '(23 24 25 26 27 28))))
                (generated-heap-world-equiv (generated-set-reg register value world) world)))
  :hints (("Goal" :in-theory (enable generated-heap-world-equiv proof-machine-limit proof-stack-limit
                                    proof-stack-top proof-heap-limit proof-box-top proof-heap-base))))

(defthm generated-compiled-entry-ignores-other-registers
  (implies (generated-heap-world-equiv before after)
           (equal (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (proof-compiled-entry-p (proof-world-pc after) args after objects packages)))
  :hints (("Goal" :in-theory (enable proof-stack-base)))
  :rule-classes nil)
