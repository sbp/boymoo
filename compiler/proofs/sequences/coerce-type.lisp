(in-package "BOYMOO-PROOFS")

(include-book "symbol-fields")
(include-book "byte-words")
(include-book "static-roots")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-word-view-depth (word base objects)
  (1+ (nfix (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))

(defun sequence-symbol-package-index (word base objects packages machine)
  (let* ((address (proof-pointer-address word base))
         (rank (proof-object-rank (assoc-equal address objects))))
    (proof-view-value (sequence-symbol-field-view 16 address rank base objects packages machine))))

(local
 (defthm sequence-nonnegative-immediate-word
   (implies (and (natp index) (proof-immediate-integer-p index))
            (equal (proof-integer-word index) (+ 1 (* 2 index))))))

(local
 (defthm sequence-represented-symbol-storage
   (let* ((address (proof-pointer-address word base))
          (index (sequence-symbol-package-index word base objects packages machine))
          (name (proof-load-word (+ address 8) machine)))
     (implies
      (proof-value-p word datum base objects packages machine)
      (and (equal (symbolp datum)
                  (and (equal (proof-word-tag word) 2)
                       (equal (proof-header-type (proof-load-word address machine)) 2)))
           (implies (symbolp datum)
                    (and (proof-span-p address 24)
                         (proof-value-p name (symbol-name datum) base objects packages machine)
                         (natp index) (< index (len packages))
                         (proof-immediate-integer-p index)
                         (equal (proof-load-word (+ address 16) machine) (+ 1 (* 2 index)))
                         (equal (proof-package-name (nth index packages))
                                (acl2::symbol-package-name datum)))))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-value-p proof-view)
                     (proof-view-step proof-load-word proof-pointer-address
                      proof-header-type proof-header-size proof-word-tag
                      sequence-even-tags-mark-even-words sequence-unsigned-word-of-value
                      oddp evenp))
     :use ((:instance sequence-symbol-view-identifies-fields
                      (depth (sequence-word-view-depth word base objects)))
           (:instance sequence-unsigned-word-of-value
                      (depth (sequence-word-view-depth word base objects)))
           sequence-even-tags-mark-even-words
           (:instance sequence-value-view-at-its-own-rank
                      (word (proof-load-word (+ 8 (proof-pointer-address word base)) machine))
                      (datum (symbol-name datum))
                      (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))
           (:instance sequence-immediate-value-has-canonical-word
                      (word (proof-load-word (+ 16 (proof-pointer-address word base)) machine))
                      (datum (sequence-symbol-package-index word base objects packages machine))
                      (depth (proof-object-rank (assoc-equal (proof-pointer-address word base) objects)))))))
   :rule-classes nil))

(local
 (defthm sequence-header-type-and-size-determine-word
   (implies (unsigned-byte-p 64 header)
            (equal (+ (proof-header-type header) (* 256 (proof-header-size header))) header))
   :hints (("Goal" :in-theory (enable sequence-a64-unsigned-as-mod
                                     proof-header-type proof-header-size mod)))
   :rule-classes nil))

(local
 (defthm sequence-list-name-has-four-bytes
   (implies (and (natp count) (equal (proof-load-string count address machine) "LIST"))
            (equal count 4))
   :hints (("Goal" :in-theory (disable proof-load-string sequence-load-string-length
                                      sequence-load-string-characters)
            :use sequence-load-string-length))
   :rule-classes nil))

(local
 (defthm sequence-string-header-name-test
   (implies
    (and (proof-span-p address (+ 8 (proof-header-size header)))
         (natp (proof-header-size header))
         (equal (+ 1 (* 256 (proof-header-size header))) header))
    (and (equal (and (equal header 1025)
                     (equal (boymoo-model::a64-unsigned
                             32 (proof-load-word (+ address 8) machine))
                            #x5453494c))
                (equal (proof-load-string (proof-header-size header) (+ address 8) machine)
                       "LIST"))
         (implies (equal header 1025) (unsigned-byte-p 64 (+ address 8)))))
   :hints
   (("Goal"
     :in-theory (disable proof-load-string proof-load-word proof-header-size
                         sequence-low-four-bytes-of-word-load)
     :use ((:instance sequence-packed-list-name-test (address (+ address 8)))
           (:instance sequence-list-name-has-four-bytes
                      (count (proof-header-size header)) (address (+ address 8))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-name-test
   (let* ((address (sequence-coerce-name-address symbol-address base machine))
          (header (proof-load-word address machine)))
     (implies (and (stringp name)
                   (proof-value-p (proof-load-word (+ symbol-address 8) machine)
                                  name base objects packages machine))
              (and (equal (and (equal header 1025)
                               (equal (boymoo-model::a64-unsigned
                                       32 (proof-load-word (+ address 8) machine))
                                      #x5453494c))
                          (equal name "LIST"))
                   (implies (equal header 1025) (unsigned-byte-p 64 (+ address 8))))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-pointer-address proof-load-word proof-value-p proof-view)
                     (proof-view-step proof-load-string proof-header-type proof-header-size
                      sequence-low-four-bytes-of-word-load sequence-load-string-length
                      sequence-read-bytes-bits))
     :use ((:instance sequence-string-view-of-represented-value
                      (word (proof-load-word (+ 8 symbol-address) machine))
                      (datum name)
                      (depth (sequence-word-view-depth
                              (proof-load-word (+ 8 symbol-address) machine) base objects)))
           (:instance sequence-string-header-name-test
                      (address (sequence-coerce-name-address symbol-address base machine))
                      (header (proof-load-word (sequence-coerce-name-address symbol-address base machine)
                                              machine)))
           (:instance sequence-header-type-and-size-determine-word
                      (header (proof-load-word (sequence-coerce-name-address symbol-address base machine)
                                              machine)))
           (:instance sequence-read-bytes-bits
                      (count 8) (address (sequence-coerce-name-address symbol-address base machine))
                      (memory (boymoo-model::a64-memory machine)))
           (:instance sequence-floor-of-unsigned
                      (dropped 8) (kept 56)
                      (value (proof-load-word (sequence-coerce-name-address symbol-address base machine)
                                             machine))))
     :expand ((proof-header-size
               (proof-load-word (sequence-coerce-name-address symbol-address base machine)
                                machine)))))
   :rule-classes nil))

(local
 (defthm sequence-null-symbol-storage
   (implies (and (unsigned-byte-p 64 base) (unsigned-byte-p 64 (+ base 48)))
            (equal (proof-pointer-address *proof-nil* base) (+ base 32)))
   :hints (("Goal" :in-theory (enable proof-pointer-address proof-word-tag)))))

(defthm sequence-coerce-type-test-agrees-with-source
  (implies (and (proof-value-p word result-type base objects packages machine)
                (proof-value-p *proof-nil* nil base objects packages machine)
                (proof-packages-p packages)
                (unsigned-byte-p 64 base) (unsigned-byte-p 64 (+ base 48)))
           (and (equal (eq (sequence-coerce-type-test word base machine) :list)
                       (eq result-type 'list))
                (sequence-coerce-test-readable-p word base machine)))
  :hints
  (("Goal"
    :in-theory (disable proof-value-p proof-view proof-packages-p proof-word-tag
                        proof-pointer-address proof-header-type proof-load-word
                        sequence-coerce-name-address sequence-symbol-package-index
                        sequence-low-four-bytes-of-word-load)
    :cases ((symbolp result-type))
    :use ((:instance sequence-represented-symbol-storage (datum result-type))))
   ("Subgoal 1"
    :use ((:instance sequence-represented-symbol-storage (word *proof-nil*) (datum nil))
          (:instance sequence-coerce-name-test
                     (symbol-address (proof-pointer-address word base))
                     (name (symbol-name result-type)))
          (:instance sequence-package-numbers-agree-exactly-for-equal-names
                     (left (sequence-symbol-package-index word base objects packages machine))
                     (right (sequence-symbol-package-index *proof-nil* base objects packages machine)))
          (:instance sequence-equal-symbol-names-and-packages (left result-type) (right 'list)))))
  :rule-classes nil)

(local
 (defthm sequence-coerce-heap-base-is-word
   (unsigned-byte-p 64 (proof-heap-base world))
   :hints (("Goal" :in-theory (enable proof-heap-base proof-world-reg)))
   :rule-classes nil))

(local
 (defthm sequence-coerce-heap-supplies-packages-and-running-world
   (implies (proof-heap-p world objects packages)
            (and (not (proof-world-stop world)) (proof-packages-p packages)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-static-p)
                     (proof-heap-p proof-heap-layout-p proof-packages-p proof-heap-base
                      proof-world-machine proof-object-map-p proof-heap-object-spans-p
                      proof-string-accounting-p proof-dynamic-view proof-dynamic-entries
                      proof-dynamic-symbol-objects-p proof-stack-prefix proof-external-objects
                      proof-static-objects proof-static-buckets-p proof-home-bindings-p
                      proof-package-bindings-p proof-static-spans-p proof-value-p proof-view
                      proof-regions-p proof-align-up proof-disjoint-p))
     :expand ((proof-heap-p world objects packages)
              (proof-heap-layout-p world))))
   :rule-classes nil))

(defthm sequence-coerce-dispatch-for-represented-type
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (path (sequence-coerce-dispatch-path before))
         (target (+ image-base (if (eq result-type 'list)
                                   *sequence-coerce-list-offset*
                                 *sequence-coerce-string-offset*)))
         (after (sequence-execute path before))
         (last (proof-world-machine after)))
    (implies
     (and (proof-heap-p before objects packages)
          (proof-reg-value-p 1 result-type before objects packages)
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset*))
          (unsigned-byte-p 64 (+ base 48))
          (sequence-instruction-path path (list target) before))
     (and (proof-segment-p (len path) (list target) before :cut after)
          (equal (proof-world-pc after) target)
          (proof-register-frame-p 30 '(1 2 3) before after)
          (consp (boymoo-model::a64-registers last))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                    (proof-value-p proof-view proof-heap-p proof-static-p proof-packages-p
                     proof-register-frame-p proof-segment-p sequence-instruction-path
                     sequence-coerce-dispatch-path sequence-coerce-type-test
                     sequence-coerce-test-readable-p proof-world-machine proof-world-reg
                     proof-world-pc proof-heap-base proof-world-stop sequence-execute))
    :use ((:instance sequence-coerce-heap-base-is-word (world before))
          (:instance sequence-coerce-heap-supplies-packages-and-running-world (world before))
          (:instance sequence-static-truth-values-in-heap (world before))
          sequence-coerce-type-test-cutpoint sequence-coerce-type-test-effects
          (:instance sequence-coerce-type-test-agrees-with-source
                     (word (proof-world-reg 1 before)) (base (proof-heap-base before))
                     (machine (proof-world-machine before))))))
  :rule-classes nil)
