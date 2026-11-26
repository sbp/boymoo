(in-package "BOYMOO-PROOFS")

(include-book "find")
(include-book "object-map")
(include-book "query")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-view proof-view-step proof-load-word proof-pointer-address proof-word-tag
                     proof-heap-base proof-world-reg proof-reg proof-world-machine
                     boymoo-model::a64-unsigned symbols-logical-right-shift-bits
                     proof-header-size proof-header-type)))

(local
 (defthm symbols-row-views-have-package-count
   (equal (len (proof-package-row-views packages)) (len packages))))

(defthm symbols-static-package-vector-layout
  (let* ((word (proof-load-word (+ base 8) machine))
         (address (proof-pointer-address word base))
         (header (proof-load-word address machine)))
    (implies (and (proof-static-p base objects packages machine) (consp packages))
             (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type header) 6)
                  (equal (proof-header-size header) (* 8 (len packages)))
                  (proof-span-p address (+ 8 (* 8 (len packages)))))))
  :hints (("Goal"
           :use ((:instance symbols-vector-view-shape (word (proof-load-word (+ base 8) machine))
                            (objects (proof-static-objects objects)) (entries (proof-package-row-views packages)))
                 (:instance symbols-vector-view-reads-slot (word (proof-load-word (+ base 8) machine))
                            (objects (proof-static-objects objects)) (entries (proof-package-row-views packages))
                            (index 0)))
           :expand ((len packages))
           :in-theory (disable proof-static-objects proof-static-spans-p proof-object-map-p
                               proof-package-row-views proof-home-bindings-p proof-static-buckets-p
                               proof-package-bindings-p proof-packages-p proof-value-p proof-span-p)))
  :rule-classes nil)

(local
 (defthm symbols-static-row-base-is-natural
   (natp (proof-heap-base world))
   :hints (("Goal" :in-theory (enable proof-heap-base proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-static-row-pointer-is-natural
   (natp (proof-pointer-address word base))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-static-row-loaded-word-is-natural
   (natp (proof-load-word address machine))
   :hints (("Goal" :use ((:instance symbols-load-width (count 8)))
                   :in-theory (e/d (proof-load-word) (boymoo-model::a64-load))))
   :rule-classes :type-prescription))

(local
 (defthm symbols-static-row-loaded-word-fits
   (equal (boymoo-model::a64-unsigned 64 (proof-load-word address machine))
          (proof-load-word address machine))
   :hints (("Goal" :in-theory (e/d (proof-load-word symbols-word-load-fits) (boymoo-model::a64-load))))))

(local
 (defthm symbols-static-row-boxed-address
   (implies (and (integerp base) (integerp word) (equal (proof-word-tag word) 2))
            (equal (symbols-box-address word base) (proof-pointer-address word base)))
   :hints (("Goal" :in-theory (enable proof-pointer-address)))))

(local
 (defthm symbols-static-row-first-slot-at-vector-payload
   (let ((address (proof-pointer-address word base)))
     (implies (and (integerp base) (integerp word) (equal (proof-word-tag word) 2)
                   (< (+ 8 address) (expt 2 64)))
              (equal (boymoo-model::a64-unsigned 64 (+ base (boymoo-model::a64-unsigned 64 (+ word 6))))
                     (+ 8 address))))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-sum-right (width 64) (x (+ 6 word)) (y base))
                  (:instance symbols-unsigned-sum-right (width 64) (x (+ base word -2)) (y 8)))
            :in-theory (e/d (proof-pointer-address) (symbols-unsigned-sum-right))))))

(defthm symbols-package-row-slot-agrees-with-static-vector
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (table (proof-load-word (+ base 8) machine))
         (address (proof-pointer-address table base)))
    (implies (and (proof-static-p base objects packages machine) (natp number) (< number (len packages))
                  (< number (expt 2 63)) (equal (proof-world-reg 0 world) (+ 1 (* 2 number))))
             (and (equal (symbols-package-row-slot world) (+ address 8 (* 8 number)))
                  (equal (symbols-package-row-address world)
                         (proof-pointer-address (symbols-static-package-row-word number base machine) base)))))
  :hints (("Goal"
           :use ((:instance symbols-static-package-vector-layout
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance symbols-static-package-row-fields
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance symbols-static-row-first-slot-at-vector-payload
                            (base (proof-heap-base world))
                            (word (proof-load-word (+ 8 (proof-heap-base world)) (proof-world-machine world))))
                 (:instance symbols-logical-right-shift-correct (word (proof-world-reg 0 world)) (amount 1))
                 (:instance symbols-floor-of-decomposition (q number) (r 1) (divisor 2)))
           :cases ((consp packages))
           :in-theory (disable proof-static-p proof-value-p symbols-floor-of-decomposition floor
                               symbols-unsigned-sum-left symbols-unsigned-sum-right symbols-box-address
                               symbols-static-row-first-slot-at-vector-payload)))
  :rule-classes nil)

(local
 (defthm symbols-static-named-package-has-nonempty-name
   (implies (and (proof-packages-p packages) (natp number) (< number (len packages)))
            (let ((name (proof-package-name (nth number packages))))
              (and (stringp name) (posp (len (coerce name 'list))))))
   :hints (("Goal" :induct (nth number packages)
                   :in-theory (disable acl2::pkg-imports)))))

(local
 (defthm symbols-string-bytes-count-characters
   (equal (len (proof-string-bytes characters)) (len characters))))

(local
 (defthm symbols-static-row-loaded-header-size-is-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal" :use ((:instance symbols-load-width (count 8)))
                   :in-theory (e/d (proof-header-size proof-load-word ash) (boymoo-model::a64-load))))
   :rule-classes :type-prescription))

(local
 (defthm symbols-static-row-loaded-size-agrees-with-shift
   (let ((header (proof-load-word address machine)))
     (equal (symbols-logical-right-shift-bits header 8) (proof-header-size header)))
   :hints (("Goal"
            :use ((:instance symbols-logical-right-shift-correct
                             (word (proof-load-word address machine)) (amount 8))
                  (:instance symbols-load-width (count 8)))
            :in-theory (e/d (proof-load-word proof-header-size ash)
                            (boymoo-model::a64-load symbols-logical-right-shift-bits))))))

(local
 (defthm symbols-static-name-is-exact-byte-span
   (let* ((address (proof-pointer-address word base))
          (header (proof-load-word address machine))
          (size (len (coerce name 'list))))
     (implies (and (stringp name) (posp size) (proof-value-p word name base objects packages machine))
              (and (equal (proof-word-tag word) 2)
                   (equal (proof-header-size header) size)
                   (< (+ 8 address) (expt 2 64))
                   (equal (proof-byte-list size (+ address 8) machine)
                          (proof-string-bytes (coerce name 'list))))))
   :hints (("Goal"
            :use ((:instance symbols-represented-string-layout (datum name))
                  (:instance symbols-loaded-string-has-span-bytes
                             (count (proof-header-size (proof-load-word (proof-pointer-address word base) machine)))
                             (address (+ 8 (proof-pointer-address word base))))
                  (:instance symbols-byte-list-length
                             (count (proof-header-size (proof-load-word (proof-pointer-address word base) machine)))
                             (address (+ 8 (proof-pointer-address word base)))))
            :in-theory (disable proof-value-p proof-load-string proof-byte-list proof-string-bytes
                                symbols-byte-list-length symbols-loaded-string-has-span-bytes)))
   :rule-classes nil))

(defun symbols-static-row-slot-address (number world)
  (let* ((base (proof-heap-base world))
         (table (proof-load-word (+ base 8) (proof-world-machine world))))
    (+ (proof-pointer-address table base) 8 (* 8 (nfix number)))))

(defun symbols-static-addressed-row (number packages world)
  (let* ((base (proof-heap-base world))
         (word (symbols-static-package-row-word number base (proof-world-machine world)))
         (name (proof-package-name (nth number packages))))
    (cons (proof-string-bytes (coerce name 'list)) (proof-pointer-address word base))))

(local
 (defthm symbols-static-object-address-after-prefix
   (implies (and (proof-static-spans-p records base size machine)
                 (assoc-equal address records))
            (<= (+ base 32) address))
   :hints (("Goal" :induct (assoc-equal address records)
                   :in-theory (disable proof-object-size proof-span-p)))))

(local
 (defthm symbols-indexed-package-view-is-vector
   (let ((view (nth number (proof-package-row-views packages))))
     (implies (and (natp number) (< number (len packages)))
              (equal view (cons :vector (cdr view)))))
   :hints (("Goal" :induct (nth number packages)
                   :expand ((proof-package-row-views packages))))
   :rule-classes nil))

(local
 (defthm symbols-numbered-static-row-is-nonzero
   (let* ((word (symbols-static-package-row-word number base machine))
          (address (proof-pointer-address word base)))
     (implies (and (proof-static-p base objects packages machine)
                   (natp number) (< number (len packages)))
              (not (equal address 0))))
   :hints (("Goal"
            :use ((:instance symbols-static-package-row-view)
                  (:instance symbols-indexed-package-view-is-vector)
                  (:instance symbols-vector-view-shape
                             (word (symbols-static-package-row-word number base machine))
                             (objects (proof-static-objects objects))
                             (entries (cdr (nth number (proof-package-row-views packages)))))
                  (:instance symbols-static-object-address-after-prefix
                             (records (proof-static-objects objects))
                             (size (proof-static-size base machine))
                             (address (proof-pointer-address (symbols-static-package-row-word number base machine) base))))
            :in-theory (disable proof-package-row-views proof-load-word proof-static-objects
                                proof-static-spans-p proof-object-map-p proof-value-p proof-home-bindings-p
                                proof-static-buckets-p proof-package-bindings-p proof-packages-p
                                symbols-static-package-row-word assoc-equal)))
   :rule-classes nil))

(defthm symbols-static-row-provides-finder-bytes
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world)))
    (implies (and (proof-static-p base objects packages machine)
                  (natp number) (< number (len packages)))
             (symbols-find-rows-p (list (symbols-static-addressed-row number packages world))
                                  (symbols-static-row-slot-address number world) world)))
  :hints (("Goal"
           :use ((:instance symbols-static-package-row-fields (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance symbols-numbered-static-row-is-nonzero (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance symbols-static-named-package-has-nonempty-name)
                 (:instance symbols-static-name-is-exact-byte-span
                            (word (proof-load-word
                                   (+ 8 (proof-pointer-address
                                         (symbols-static-package-row-word number (proof-heap-base world)
                                                                         (proof-world-machine world))
                                         (proof-heap-base world)))
                                   (proof-world-machine world)))
                            (name (proof-package-name (nth number packages)))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (objects (proof-static-objects objects))))
           :in-theory (disable proof-view proof-value-p proof-byte-list proof-string-bytes
                               proof-static-objects proof-static-spans-p proof-object-map-p
                               proof-static-buckets-p proof-home-bindings-p proof-package-bindings-p proof-packages-p
                               symbols-box-address)))
  :rule-classes nil)

(defun symbols-static-addressed-rows (pending number world)
  (if (atom pending)
      nil
    (let* ((base (proof-heap-base world))
           (word (symbols-static-package-row-word number base (proof-world-machine world)))
           (bytes (proof-string-bytes (coerce (proof-package-name (car pending)) 'list))))
      (cons (cons bytes (proof-pointer-address word base))
            (symbols-static-addressed-rows (cdr pending) (+ 1 number) world)))))

(local
 (defthm symbols-finder-rows-admit-first-row
   (implies (and (symbols-find-rows-p (list row) slot world)
                 (symbols-find-rows-p rest (+ slot 8) world))
            (symbols-find-rows-p (cons row rest) slot world))
   :hints (("Goal" :in-theory (disable symbols-box-at-slot symbols-load-register-word
                                      proof-byte-list boymoo-model::a64-unsigned)))))

(local
 (defthm symbols-nthcdr-package-tail
   (implies (natp number)
            (and (equal (car (nthcdr number packages)) (nth number packages))
                 (equal (cdr (nthcdr number packages)) (nthcdr (1+ number) packages))
                 (equal (len (nthcdr number packages)) (nfix (- (len packages) number)))))
   :hints (("Goal" :induct (nth number packages)))))

(local
 (defthm symbols-nonempty-package-tail-has-in-range-index
   (implies (and (natp number) (consp (nthcdr number packages)))
            (< number (len packages)))
   :hints (("Goal"
            :use ((:instance symbols-nthcdr-package-tail))
            :expand ((len (nthcdr number packages)))
            :in-theory (disable nthcdr symbols-nthcdr-package-tail)))
   :rule-classes nil))

(defthm symbols-static-addressed-rows-agree-with-finder
  (implies (and (proof-static-p (proof-heap-base world) objects packages (proof-world-machine world))
                (natp number) (equal pending (nthcdr number packages)))
           (symbols-find-rows-p (symbols-static-addressed-rows pending number world)
                                (symbols-static-row-slot-address number world) world))
  :hints (("Goal"
           :induct (symbols-static-addressed-rows pending number world)
           :in-theory (disable proof-static-p symbols-find-rows-p symbols-static-package-row-word
                               symbols-static-row-slot-address proof-string-bytes))
          ("Subgoal *1/2"
           :use ((:instance symbols-static-row-provides-finder-bytes)
                 (:instance symbols-nonempty-package-tail-has-in-range-index)
                 (:instance symbols-finder-rows-admit-first-row
                            (row (symbols-static-addressed-row number packages world))
                            (slot (symbols-static-row-slot-address number world))
                            (rest (symbols-static-addressed-rows (cdr pending) (1+ number) world))))
           :in-theory (disable proof-static-p symbols-find-rows-p symbols-finder-rows-admit-first-row
                               symbols-static-package-row-word proof-string-bytes nthcdr nth))
          ("Subgoal *1/1" :in-theory (enable symbols-find-rows-p)))
  :rule-classes nil)

(local
 (defthm symbols-reading-character-codes-recovers-original-characters
   (implies (character-listp characters)
            (equal (proof-byte-characters (proof-string-bytes characters)) characters))))

(defthmd symbols-name-bytes-are-injective
  (implies (and (stringp first) (stringp second))
           (iff (equal (proof-string-bytes (coerce first 'list))
                       (proof-string-bytes (coerce second 'list)))
                (equal first second)))
  :hints (("Goal"
           :use ((:instance symbols-reading-character-codes-recovers-original-characters
                            (characters (coerce first 'list)))
                 (:instance symbols-reading-character-codes-recovers-original-characters
                            (characters (coerce second 'list)))
                 (:instance acl2::coerce-inverse-2 (acl2::x first))
                 (:instance acl2::coerce-inverse-2 (acl2::x second)))
           :in-theory (disable proof-string-bytes proof-byte-characters
                               symbols-reading-character-codes-recovers-original-characters acl2::coerce-inverse-2))))

(defthm symbols-static-addressed-rows-select-source-package
  (let* ((bytes (proof-string-bytes (coerce name 'list)))
         (selected (proof-package-number name pending number))
         (base (proof-heap-base world))
         (slot (symbols-static-package-row-word selected base (proof-world-machine world))))
    (implies (and (proof-packages-p pending) (stringp name) (natp number))
             (equal (assoc-equal bytes (symbols-static-addressed-rows pending number world))
                    (and selected (cons bytes (proof-pointer-address slot base))))))
  :hints (("Goal"
           :induct (symbols-static-addressed-rows pending number world)
           :in-theory (e/d (symbols-name-bytes-are-injective)
                           (proof-string-bytes symbols-static-package-row-word acl2::pkg-imports))))
  :rule-classes nil)

(local
 (defthm symbols-addressed-rows-count
   (equal (len (symbols-static-addressed-rows pending number world)) (len pending))))

(defthm symbols-static-package-vector-provides-finder-rows
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (rows (symbols-static-addressed-rows packages 0 world))
         (slot (symbols-find-first-slot base world))
         (table (proof-pointer-address (proof-load-word (+ base 8) machine) base)))
    (implies (and (consp packages) (proof-static-p base objects packages machine)
                  (< (+ table 8 (* 8 (len packages))) (expt 2 64)))
             (and (equal (symbols-find-vector-size base world) (* 8 (len rows)))
                  (< (+ slot (* 8 (len rows))) (expt 2 64))
                  (symbols-find-rows-p rows slot world))))
  :hints (("Goal"
           :use ((:instance symbols-static-package-vector-layout (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance symbols-static-addressed-rows-agree-with-finder (pending packages) (number 0)))
           :in-theory (disable proof-static-p symbols-find-rows-p symbols-static-addressed-rows
                               symbols-unsigned-sum-left symbols-unsigned-sum-right symbols-box-address)))
  :rule-classes nil)

(defun symbols-query-datum-bytes (datum)
  (if (stringp datum) (proof-string-bytes (coerce datum 'list)) nil))

(local
 (defthm symbols-query-lookup-bytes-from-value
   (implies (iff (symbols-query-string-argument-p before) (stringp datum))
            (equal (symbols-query-lookup-bytes (symbols-query-datum-bytes datum) before)
                   (proof-string-bytes (coerce (if (stringp datum) datum "ACL2") 'list))))
   :hints (("Goal" :in-theory (disable symbols-query-string-argument-p)))))

(local
 (defthm symbols-visible-package-has-row
   (implies (proof-package-visible row)
            (consp row))
   :hints (("Goal" :in-theory (enable proof-package-visible)))))

(local
 (defthm symbols-program-has-visible-acl2-package
   (implies (proof-program-packages-p program packages)
            (and (assoc-equal "ACL2" packages)
                 (proof-package-visible (assoc-equal "ACL2" packages))))
   :hints (("Goal" :use ((:instance symbols-acl2-row-visible)
                       (:instance symbols-visible-package-has-row
                                  (row (assoc-equal "ACL2" packages))))
                   :in-theory (disable symbols-acl2-row-visible proof-program-packages-p
                                       assoc-equal proof-package-visible)))))

(local
 (defthm symbols-query-selected-static-row-address
   (let* ((name (if (stringp datum) datum "ACL2"))
          (number (proof-package-number name packages 0))
          (rows (symbols-static-addressed-rows packages 0 memory)))
     (implies (and (proof-packages-p packages)
                   (iff (symbols-query-string-argument-p before) (stringp datum)))
              (equal (symbols-query-row rows (symbols-query-datum-bytes datum) before)
                     (if number (cdr (symbols-static-addressed-row number packages memory)) 0))))
   :hints (("Goal"
            :use ((:instance symbols-static-addressed-rows-select-source-package
                             (name (if (stringp datum) datum "ACL2")) (pending packages) (number 0) (world memory)))
            :in-theory (disable symbols-query-lookup-bytes symbols-query-string-argument-p symbols-query-datum-bytes
                                symbols-static-addressed-rows proof-package-number proof-string-bytes assoc-equal
                                symbols-static-package-row-word proof-packages-p)))
   :rule-classes nil))

(defthm symbols-query-data-agreement-from-static-map
  (let* ((memory (symbols-query-stack-effects before entry))
         (base (proof-heap-base memory))
         (machine (proof-world-machine memory))
         (rows (symbols-static-addressed-rows packages 0 memory))
         (name (symbols-query-datum-bytes datum)))
    (implies (and (member-eq primitive '(acl2::pkg-imports acl2::pkg-witness))
                  (equal (proof-world-reg 6 before) (symbols-query-field primitive))
                  (iff (symbols-query-string-argument-p before) (stringp datum))
                  (equal base (proof-heap-base before))
                  (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-program-packages-p program packages))
             (symbols-query-data-agreement-p primitive datum packages rows name before entry objects)))
  :hints (("Goal"
           :use ((:instance symbols-program-has-visible-acl2-package)
                 (:instance symbols-query-selected-static-row-address
                            (memory (symbols-query-stack-effects before entry)))
                 (:instance symbols-package-number-selects-row (first 0) (name (if (stringp datum) datum "ACL2")))
                 (:instance symbols-package-number-present (first 0) (name (if (stringp datum) datum "ACL2")))
                 (:instance symbols-package-number-range (first 0) (name (if (stringp datum) datum "ACL2")))
                 (:instance symbols-static-nil-in-live-objects
                            (base (proof-heap-base (symbols-query-stack-effects before entry)))
                            (machine (proof-world-machine (symbols-query-stack-effects before entry))))
                 (:instance symbols-static-package-row-fields-in-live-objects
                            (number (proof-package-number (if (stringp datum) datum "ACL2") packages 0))
                            (base (proof-heap-base (symbols-query-stack-effects before entry)))
                            (machine (proof-world-machine (symbols-query-stack-effects before entry))))
                 (:instance symbols-numbered-static-row-is-nonzero
                            (number (proof-package-number (if (stringp datum) datum "ACL2") packages 0))
                            (base (proof-heap-base (symbols-query-stack-effects before entry)))
                            (machine (proof-world-machine (symbols-query-stack-effects before entry))))
                 (:instance symbols-static-package-row-witness-tests-visibility
                            (number (proof-package-number (if (stringp datum) datum "ACL2") packages 0))
                            (base (proof-heap-base (symbols-query-stack-effects before entry)))
                            (machine (proof-world-machine (symbols-query-stack-effects before entry)))))
           :in-theory (disable symbols-query-stack-effects symbols-query-string-argument-p symbols-query-row
                               symbols-static-addressed-rows proof-static-p proof-value-p proof-object-map-p
                               proof-package-number proof-packages-p symbols-static-package-row-word assoc-equal
                               symbols-row-imports proof-package-imports proof-package-witness
                               proof-package-name proof-package-visible
                               symbols-program-has-visible-acl2-package symbols-package-number-selects-row
                               symbols-package-number-present proof-hidden-package-witnesses proof-public-package-names)))
  :rule-classes nil)

(local
 (defthm symbols-query-saved-world-keeps-heap-base
   (and (equal (proof-heap-base (symbols-query-saved-world world))
               (proof-heap-base world))
        (equal (proof-heap-base (symbols-saved-link-world world))
               (proof-heap-base world)))
   :hints (("Goal" :in-theory (enable proof-heap-base proof-world-reg proof-reg proof-world-machine)))))

(local
 (defthm symbols-query-dispatched-world-keeps-heap-base
   (implies (symbols-query-dispatched-frame-p base before entry)
            (equal (proof-heap-base (symbols-query-stack-effects before entry))
                   (proof-heap-base before)))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 28) (clobbers '(1 2 3 30)) (after entry))
                  (:instance symbols-query-saved-world-keeps-heap-base (world before))
                  (:instance symbols-query-saved-world-keeps-heap-base (world entry)))
            :in-theory (e/d (proof-heap-base)
                            (symbols-query-saved-world symbols-saved-link-world symbols-string-hit-p
                             symbols-string-payload symbols-string-header-word
                             symbols-query-saved-world-keeps-heap-base))))
   :rule-classes nil))

(defthm symbols-public-package-query-with-static-map
  (let* ((primitive (if witness 'acl2::pkg-witness 'acl2::pkg-imports))
         (path (symbols-query-wrapper-path witness))
         (body (symbols-public-query-body witness before))
         (entry (symbols-query-dispatched body))
         (memory (symbols-query-stack-effects body entry))
         (rows (symbols-static-addressed-rows packages 0 memory))
         (name (symbols-query-datum-bytes datum))
         (after (symbols-package-query-finish rows byte-fuels body))
         (base (proof-heap-base memory))
         (machine (proof-world-machine memory))
         (result (boymoo-model::core-primitive primitive (list datum) program)))
    (implies (and (symbols-query-wrapper-pre-p witness code-base before)
                  (<= 32 (boymoo-model::a64-sp (proof-world-machine before)))
                  (symbols-path-ready-p path code-base (symbols-runtime-address "rt:package-query" code-base) before)
                  (symbols-package-query-ready-p rows name byte-fuels code-base body)
                  (proof-runtime-pre-p primitive (list datum) program *symbols-runtime-labels*
                                       code-base before objects packages)
                  (iff (symbols-query-string-argument-p body) (stringp datum))
                  (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (boymoo-model::core-value-p result)
                  (proof-preserved-heap-p nil before after objects objects packages)
                  (proof-fixed-heap-p before after objects))
             (proof-runtime-return-p primitive (list datum) program before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-query-wrapper)
                 (:instance symbols-run-query-prefix (before (symbols-public-query-body witness before)))
                 (:instance symbols-query-dispatched-world-keeps-heap-base (base code-base)
                            (before (symbols-public-query-body witness before))
                            (entry (symbols-query-dispatched (symbols-public-query-body witness before))))
                 (:instance symbols-query-data-agreement-from-static-map
                            (primitive (if witness 'acl2::pkg-witness 'acl2::pkg-imports))
                            (before (symbols-public-query-body witness before))
                            (entry (symbols-query-dispatched (symbols-public-query-body witness before))))
                 (:instance symbols-public-package-query-contract
                            (rows (symbols-static-addressed-rows
                                   packages 0 (symbols-query-stack-effects
                                               (symbols-public-query-body witness before)
                                               (symbols-query-dispatched (symbols-public-query-body witness before)))))
                            (name (symbols-query-datum-bytes datum))))
           :in-theory (disable proof-advance proof-register-frame-p proof-segment-p symbols-run-query-wrapper
                               symbols-query-wrapper-path symbols-query-dispatched
                               symbols-query-stack-effects symbols-static-addressed-rows symbols-query-datum-bytes
                               symbols-package-query-finish symbols-path-ready-p symbols-query-setup-ready-p
                               symbols-query-search-ready-p symbols-query-data-agreement-p
                               symbols-query-dispatched-frame-p symbols-query-string-argument-p
                               proof-static-p proof-object-map-p proof-program-packages-p proof-register-arguments-p
                               proof-heap-p proof-preserved-heap-p proof-fixed-heap-p proof-runtime-return-p
                               boymoo-model::core-primitive)))
  :rule-classes nil)
