(in-package "BOYMOO-PROOFS")

(include-book "chain-layout")
(include-book "row-data")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-view proof-view-step proof-load-word proof-heap-base proof-world-reg proof-world-machine
                     boymoo-model::a64-unsigned symbols-logical-right-shift-bits
                     proof-pointer-address proof-word-tag proof-header-size
                     proof-string-bytes proof-byte-list)))

(local
 (defthm symbols-key-loaded-word-is-heap-word
   (equal (symbols-load-register-word address world)
          (proof-load-word address (proof-world-machine world)))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits proof-load-word)
                                   (boymoo-model::a64-load))))))

(local
 (defthm symbols-key-unsigned-length-is-header-size
   (let ((header (proof-load-word address (proof-world-machine world))))
     (and (equal (symbols-logical-right-shift-bits header 8) (proof-header-size header))
          (natp (proof-header-size header))))
   :hints (("Goal"
            :use ((:instance symbols-logical-right-shift-correct
                             (word (proof-load-word address (proof-world-machine world))) (amount 8))
                  (:instance symbols-load-width (count 8) (machine (proof-world-machine world))))
            :in-theory (e/d (ash proof-header-size proof-load-word)
                            (boymoo-model::a64-load symbols-logical-right-shift-bits))))))

(local
 (defthm symbols-key-heap-base-is-natural
   (natp (proof-heap-base world))
   :hints (("Goal" :in-theory (enable proof-heap-base proof-world-reg proof-reg
                                    boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-key-box-tag-requires-word
   (implies (equal (proof-word-tag word) 2) (integerp word))
   :hints (("Goal" :in-theory (enable proof-word-tag boymoo-model::a64-unsigned)))))

(local
 (defthm symbols-key-box-address-agrees-with-view
   (implies (and (integerp base) (equal (proof-word-tag word) 2))
            (equal (symbols-box-address word base) (proof-pointer-address word base)))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-sum-right
                             (width 64) (x (- word 2)) (y base))
                  (:instance symbols-key-box-tag-requires-word))
            :in-theory (e/d (proof-pointer-address)
                            (symbols-unsigned-sum-right))))))

(local
 (defthm symbols-key-character-count-agrees-with-byte-count
   (equal (len (proof-string-bytes characters)) (len characters))
   :hints (("Goal" :induct (proof-string-bytes characters) :in-theory (enable proof-string-bytes)))))

(local
 (defthm symbols-key-empty-byte-list-is-nil
   (equal (proof-byte-list 0 address machine) nil)
   :hints (("Goal" :in-theory (enable proof-byte-list)))))

(local
 (defthm symbols-key-unsigned-payload-keeps-bytes
   (implies (and (natp size) (proof-span-p address (+ 8 size)))
            (equal (proof-byte-list size (boymoo-model::a64-unsigned 64 (+ address 8)) machine)
                   (proof-byte-list size (+ address 8) machine)))
   :hints (("Goal" :cases ((zp size))))))

(defthm symbols-intern-represented-name-compares-bytes
  (let ((machine (proof-world-machine world)))
    (implies (and (stringp candidate) (stringp name)
                  (equal size (len (coerce name 'list)))
                  (equal (proof-byte-list size address machine)
                         (proof-string-bytes (coerce name 'list)))
                  (proof-machine-value-p word candidate world objects packages))
             (iff (symbols-intern-name-key-matches-p word address size world)
                  (equal candidate name))))
  :hints (("Goal"
           :use ((:instance symbols-represented-string-layout (datum candidate)
                            (machine (proof-world-machine world)) (base (proof-heap-base world)))
                 (:instance symbols-loaded-string-has-span-bytes
                            (count (proof-header-size
                                    (proof-load-word (proof-pointer-address word (proof-heap-base world))
                                                     (proof-world-machine world))))
                            (address (+ 8 (proof-pointer-address word (proof-heap-base world))))
                            (machine (proof-world-machine world)))
                 (:instance symbols-byte-list-length
                            (count (proof-header-size
                                    (proof-load-word (proof-pointer-address word (proof-heap-base world))
                                                     (proof-world-machine world))))
                            (address (+ 8 (proof-pointer-address word (proof-heap-base world))))
                            (machine (proof-world-machine world)))
                 (:instance symbols-key-unsigned-length-is-header-size
                            (address (proof-pointer-address word (proof-heap-base world))))
                 (:instance symbols-key-unsigned-payload-keeps-bytes
                            (size (proof-header-size
                                   (proof-load-word (proof-pointer-address word (proof-heap-base world))
                                                    (proof-world-machine world))))
                            (address (proof-pointer-address word (proof-heap-base world)))
                            (machine (proof-world-machine world)))
                 (:instance symbols-name-bytes-are-injective (first candidate) (second name)))
           :in-theory (disable symbols-box-address proof-load-string symbols-byte-list-length
                               symbols-loaded-string-has-span-bytes proof-span-p proof-value-p
                               symbols-key-unsigned-length-is-header-size symbols-key-unsigned-payload-keeps-bytes)))
  :rule-classes nil)

(local
 (defthm symbols-key-tagged-number-is-small-word
   (implies (and (natp number) (< number (expt 2 62)))
            (and (unsigned-byte-p 63 (+ 1 (* 2 number)))
                 (equal (proof-integer-word number) (+ 1 (* 2 number)))))
   :hints (("Goal" :in-theory (enable proof-integer-word)))))

(local
 (defthm symbols-key-small-word-keeps-signed-value
   (implies (unsigned-byte-p 63 word)
            (equal (boymoo-model::a64-signed 64 word) word))
   :hints (("Goal"
            :use ((:instance symbols-floor-of-decomposition (q 0) (r word) (divisor (expt 2 63))))
            :in-theory (e/d (boymoo-model::a64-signed logbitp) (floor symbols-floor-of-decomposition))))))

(local
 (defthm symbols-key-half-of-double
   (implies (rationalp number) (equal (* 1/2 (* 2 number)) number))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm symbols-key-tagged-number-is-odd
   (implies (integerp number) (oddp (+ 1 (* 2 number))))
   :hints (("Goal"
            :use ((:instance symbols-floor-of-decomposition (q number) (r 1/2) (divisor 1))
                  (:instance symbols-floor-of-decomposition (q (+ 1/2 number)) (r 0) (divisor 1)))
            :in-theory (e/d (oddp evenp) (floor symbols-floor-of-decomposition))))))

(local
 (defthm symbols-key-tagged-number-shifts-back
   (implies (integerp number)
            (equal (ash (+ 1 (* 2 number)) -1) number))
   :hints (("Goal" :use ((:instance symbols-floor-of-decomposition (q number) (r 1/2) (divisor 1)))
                   :in-theory (e/d (ash) (floor symbols-floor-of-decomposition))))))

(defthm symbols-nonnegative-package-word-represents-number
  (implies (and (natp number) (< number (expt 2 62)))
           (proof-value-p (proof-integer-word number) number base objects packages machine))
  :hints (("Goal"
           :expand ((proof-view (+ 1 (* 2 number)) base objects packages machine)
                    (:free (depth) (proof-view-step :word (+ 1 (* 2 number)) 0 depth
                                                    base objects packages machine)))
           :in-theory (disable proof-integer-word oddp evenp)))
  :rule-classes nil)

(local
 (defthm symbols-intern-package-word-equality
   (implies (and (natp number) (< number (expt 2 62))
                 (proof-machine-value-p word candidate world objects packages))
            (iff (equal word (proof-integer-word number))
                 (equal candidate number)))
   :hints (("Goal"
            :use ((:instance symbols-canonical-immediate-integer-word
                             (base (proof-heap-base world)) (machine (proof-world-machine world)))
                  (:instance symbols-nonnegative-package-word-represents-number
                             (base (proof-heap-base world)) (machine (proof-world-machine world))))
            :in-theory (disable symbols-key-tagged-number-is-small-word proof-integer-word)))
   :rule-classes nil))

(defun symbols-intern-key-input-p (number name world)
  (and (natp number) (< number (expt 2 62)) (stringp name)
       (equal (proof-world-reg 20 world) (proof-integer-word number))
       (equal (proof-world-reg 21 world) (len (coerce name 'list)))
       (equal (proof-byte-list (proof-world-reg 21 world) (proof-world-reg 8 world)
                               (proof-world-machine world))
              (proof-string-bytes (coerce name 'list)))))

(local
 (defthm symbols-static-entry-match-tests-key
   (let* ((fields (symbols-intern-fields-at nil word world))
          (key (caar entries)))
     (implies (and (consp entries) (consp (car entries)) (consp key) (stringp (cdr key))
                   (symbols-intern-key-input-p number name world)
                   (proof-machine-value-p word entries world objects packages))
              (iff (symbols-intern-key-matches-fields-p nil fields world)
                   (equal key (cons number name)))))
   :hints (("Goal"
            :use ((:instance symbols-physical-static-entry-gives-binding-fields)
                  (:instance symbols-intern-package-word-equality (candidate (caaar entries))
                             (word (cadddr (symbols-intern-fields-at nil word world))))
                  (:instance symbols-intern-represented-name-compares-bytes
                             (candidate (cdaar entries))
                             (word (car (cddddr (symbols-intern-fields-at nil word world))))
                             (address (proof-world-reg 8 world)) (size (proof-world-reg 21 world))))
            :in-theory (disable symbols-intern-name-key-matches-p symbols-intern-fields-at
                                symbols-key-tagged-number-is-small-word proof-integer-word
                                proof-machine-value-p)))
   :rule-classes nil))

(local
 (defthm symbols-nonempty-chain-lookup-tests-head
   (implies (natp rest-length)
            (equal (symbols-intern-chain-binding (+ 1 rest-length) dynamic word world)
                   (if (equal word *proof-nil*)
                       nil
                     (let ((fields (symbols-intern-fields-at dynamic word world)))
                       (if (symbols-intern-key-matches-fields-p dynamic fields world)
                           (cons :binding (cadr fields))
                         (symbols-intern-chain-binding rest-length dynamic (car fields) world))))))
   :hints (("Goal"
            :expand ((symbols-intern-chain-binding (+ 1 rest-length) dynamic word world))
            :in-theory (disable symbols-intern-chain-binding symbols-intern-fields-at
                                symbols-intern-key-matches-fields-p)))))

(local
 (defthm symbols-cons-word-differs-from-live-nil
   (implies (and (consp value) (proof-machine-value-p word value world objects packages)
                 (proof-machine-value-p *proof-nil* nil world objects packages))
            (not (equal word *proof-nil*)))
   :rule-classes nil))

(local
 (defun symbols-key-lookup-static-induction (entries word world)
   (if (atom entries)
       word
     (symbols-key-lookup-static-induction (cdr entries)
                                          (car (symbols-intern-fields-at nil word world))
                                          world))))

(defthm symbols-physical-static-chain-finds-source-binding
  (let* ((physical (symbols-intern-chain-binding (len entries) nil word world))
         (source (assoc-equal (cons number name) entries)))
    (implies (and (proof-static-bucket-p entries index packages)
                  (symbols-intern-key-input-p number name world)
                  (proof-machine-value-p word entries world objects packages)
                  (proof-machine-value-p *proof-nil* nil world objects packages))
             (and (iff physical source)
                  (implies source
                           (proof-machine-value-p (cdr physical) (cdr source) world objects packages)))))
  :hints (("Goal"
           :induct (symbols-key-lookup-static-induction entries word world)
           :in-theory (disable symbols-intern-chain-binding symbols-intern-fields-at
                               symbols-intern-key-matches-fields-p symbols-intern-key-input-p
                               assoc-equal proof-static-bucket-p proof-machine-value-p))
          ("Subgoal *1/2"
           :expand ((:free (key) (assoc-equal key entries))
                    (proof-static-bucket-p entries index packages))
           :use ((:instance symbols-static-entry-match-tests-key)
                 (:instance symbols-static-chain-next-word-represents-tail)
                 (:instance symbols-cons-word-differs-from-live-nil (value entries))
                 (:instance symbols-physical-static-entry-gives-binding-fields))
           :in-theory (disable symbols-intern-chain-binding symbols-intern-fields-at
                               symbols-intern-key-matches-fields-p symbols-intern-key-input-p
                               assoc-equal proof-static-bucket-p proof-machine-value-p proof-value-p
                               proof-symbol-hash proof-package-number acl2::intern-in-package-of-symbol))
          ("Subgoal *1/1"
           :in-theory (enable symbols-intern-chain-binding assoc-equal)))
  :rule-classes nil)

(local
 (defthm symbols-key-symbol-header-has-span
   (let ((address (proof-pointer-address word base)))
     (implies (and (symbolp symbol) (proof-value-p word symbol base objects packages machine))
              (and (equal (proof-word-tag word) 2)
                   (proof-span-p address 24))))
   :hints (("Goal"
            :use ((:instance symbols-only-symbols-have-symbol-headers (datum symbol)))
            :expand ((proof-view word base objects packages machine)
                     (:free (rank) (proof-view-step :word word 0 rank base objects packages machine)))
            :in-theory (disable proof-view-step proof-span-p proof-integer-view proof-symbol-value
                                proof-cons-value proof-rational-value proof-complex-value proof-load-string
                                proof-header-type proof-object-kind assoc-equal ash mod floor)))
   :rule-classes nil))

(local
 (defthm symbols-dynamic-entry-fields-read-from-symbol-payload
   (let* ((fields (symbols-intern-fields-at t word world))
          (symbol-word (cadr fields))
          (base (proof-heap-base world))
          (payload (symbols-address-plus-word base (boymoo-model::a64-unsigned 64 (+ symbol-word 6))))
          (machine (proof-world-machine world)))
     (and (equal (cadddr fields) (proof-load-word (+ payload 8) machine))
          (equal (car (cddddr fields)) (proof-load-word payload machine))))
   :hints (("Goal"
            :in-theory (disable symbols-address-plus-word symbols-load-register-word)))))

(local
 (defthm symbols-dynamic-raw-symbol-fields-have-home-key
   (let* ((fields (symbols-intern-fields-at t word world))
          (symbol-word (cadr fields))
          (base (proof-heap-base world))
          (machine (proof-world-machine world))
          (number (proof-view-value
                   (proof-view (proof-load-word (+ 16 (proof-pointer-address symbol-word base)) machine)
                               base objects packages machine))))
     (implies (and (proof-packages-p packages) (symbolp symbol)
                   (proof-machine-value-p symbol-word symbol world objects packages))
              (and (equal (proof-package-number (acl2::symbol-package-name symbol) packages 0) number)
                   (proof-machine-value-p (cadddr fields) number world objects packages)
                   (proof-machine-value-p (car (cddddr fields)) (symbol-name symbol) world objects packages))))
   :hints (("Goal"
            :use ((:instance symbols-key-symbol-header-has-span
                             (word (cadr (symbols-intern-fields-at t word world)))
                             (base (proof-heap-base world)) (machine (proof-world-machine world)))
                  (:instance symbols-published-symbol-fields
                             (word (cadr (symbols-intern-fields-at t word world)))
                             (base (proof-heap-base world)) (machine (proof-world-machine world)))
                  (:instance symbols-package-number-of-indexed-row (first 0)
                             (number (proof-view-value
                                      (proof-view
                                       (proof-load-word (+ 16 (proof-pointer-address
                                                              (cadr (symbols-intern-fields-at t word world))
                                                              (proof-heap-base world)))
                                                        (proof-world-machine world))
                                       (proof-heap-base world) objects packages (proof-world-machine world))))))
            :in-theory (disable symbols-intern-fields-at symbols-address-plus-word
                                proof-value-p proof-packages-p proof-package-number
                                proof-package-name proof-view-value)))
   :rule-classes nil))

(local
 (defthm symbols-dynamic-head-symbol-and-hash
   (let ((symbol (proof-view-value (cadr view))))
     (implies (and (proof-dynamic-bucket view index count packages)
                   (not (equal view (proof-value-view nil))))
              (and (consp (cdddr view))
                   (symbolp symbol)
                   (equal (cadr view) (proof-value-view symbol))
                   (equal (proof-view-value (caddr view)) (symbols-cached-hash symbol packages)))))
   :hints (("Goal"
            :expand ((proof-dynamic-bucket view index count packages))
            :in-theory (disable proof-dynamic-bucket proof-package-number proof-symbol-hash
                                boymoo-model::a64-signed acl2::binary-logand)))
   :rule-classes nil))

(defthm symbols-physical-dynamic-entry-represents-home-key
  (let* ((view (proof-view word (proof-heap-base world) objects packages (proof-world-machine world)))
         (symbol (proof-view-value (cadr view)))
         (number (proof-package-number (acl2::symbol-package-name symbol) packages 0))
         (fields (symbols-intern-fields-at t word world)))
    (implies (and (proof-dynamic-bucket view index count packages)
                  (not (equal view (proof-value-view nil)))
                  (proof-packages-p packages))
             (and (symbolp symbol)
                  (proof-machine-value-p (cadr fields) symbol world objects packages)
                  (proof-machine-value-p (caddr fields) (symbols-cached-hash symbol packages) world objects packages)
                  (proof-machine-value-p (cadddr fields) number world objects packages)
                  (proof-machine-value-p (car (cddddr fields)) (symbol-name symbol) world objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-physical-dynamic-entry-gives-binding-fields)
                 (:instance symbols-dynamic-raw-symbol-fields-have-home-key
                            (symbol (proof-view-value (cadr (proof-view word (proof-heap-base world)
                                                       objects packages (proof-world-machine world))))))
                 (:instance symbols-dynamic-head-symbol-and-hash
                            (view (proof-view word (proof-heap-base world) objects packages (proof-world-machine world)))))
           :in-theory (disable proof-dynamic-bucket proof-view-value proof-machine-value-p proof-value-p
                               symbols-intern-fields-at proof-packages-p proof-package-number
                               symbols-cached-hash)))
  :rule-classes nil)

(defun symbols-intern-key-cached-hash (number name)
  (boymoo-model::a64-signed 63 (proof-symbol-hash number name 63)))

(local
 (defthm symbols-signed-hash-fits-immediate-integer
   (proof-immediate-integer-p (boymoo-model::a64-signed 63 word))
   :hints (("Goal"
            :cases ((< (boymoo-model::a64-unsigned 63 word) (expt 2 62)))
            :use ((:instance symbols-floor-of-decomposition (q 0) (divisor (expt 2 62))
                             (r (boymoo-model::a64-unsigned 63 word)))
                  (:instance symbols-floor-of-decomposition (q 1) (divisor (expt 2 62))
                             (r (- (boymoo-model::a64-unsigned 63 word) (expt 2 62)))))
            :in-theory (e/d (boymoo-model::a64-signed logbitp)
                            (floor symbols-floor-of-decomposition))))))

(local
 (defthm symbols-dynamic-entry-match-tests-home-key
   (let* ((view (proof-view word (proof-heap-base world) objects packages (proof-world-machine world)))
          (symbol (proof-view-value (cadr view)))
          (fields (symbols-intern-fields-at t word world)))
     (implies (and (proof-dynamic-bucket view index count packages)
                   (not (equal view (proof-value-view nil)))
                   (proof-packages-p packages)
                   (symbols-intern-key-input-p number name world)
                   (equal (proof-world-reg 9 world)
                          (proof-integer-word (symbols-intern-key-cached-hash number name))))
              (iff (symbols-intern-key-matches-fields-p t fields world)
                   (and (equal (proof-package-number (acl2::symbol-package-name symbol) packages 0) number)
                        (equal (symbol-name symbol) name)))))
   :hints (("Goal"
            :use ((:instance symbols-physical-dynamic-entry-represents-home-key)
                  (:instance symbols-intern-package-word-equality
                             (candidate (proof-package-number
                                         (acl2::symbol-package-name
                                          (proof-view-value
                                           (cadr (proof-view word (proof-heap-base world) objects packages
                                                             (proof-world-machine world)))))
                                         packages 0))
                             (word (cadddr (symbols-intern-fields-at t word world))))
                  (:instance symbols-intern-represented-name-compares-bytes
                             (candidate (symbol-name
                                         (proof-view-value
                                          (cadr (proof-view word (proof-heap-base world) objects packages
                                                            (proof-world-machine world))))))
                             (word (car (cddddr (symbols-intern-fields-at t word world))))
                             (address (proof-world-reg 8 world)) (size (proof-world-reg 21 world)))
                  (:instance symbols-canonical-immediate-integer-word
                             (number (symbols-cached-hash
                                      (proof-view-value
                                       (cadr (proof-view word (proof-heap-base world) objects packages
                                                         (proof-world-machine world))))
                                      packages))
                             (word (caddr (symbols-intern-fields-at t word world)))
                             (base (proof-heap-base world)) (machine (proof-world-machine world))))
            :in-theory (disable proof-dynamic-bucket proof-view-value proof-packages-p
                                proof-package-number proof-symbol-hash proof-integer-word
                                symbols-key-tagged-number-is-small-word symbols-intern-fields-at
                                symbols-intern-name-key-matches-p boymoo-model::a64-signed)))
   :rule-classes nil))

(local
 (defthm symbols-decoded-dynamic-scan-tests-home-key
   (let ((symbol (proof-view-value (cadr view)))
         (hash (symbols-intern-key-cached-hash number name)))
     (implies (and (proof-dynamic-bucket view index count packages)
                   (not (equal view (proof-value-view nil))))
              (equal (symbols-dynamic-scan name number hash view packages)
                     (if (and (equal (proof-package-number (acl2::symbol-package-name symbol) packages 0) number)
                              (equal (symbol-name symbol) name))
                         (proof-value-view symbol)
                       (symbols-dynamic-scan name number hash (cadddr view) packages)))))
   :hints (("Goal"
            :use ((:instance symbols-dynamic-head-symbol-and-hash))
            :expand ((:free (hash) (symbols-dynamic-scan name number hash view packages)))
            :in-theory (disable symbols-dynamic-scan proof-dynamic-bucket proof-view-value
                                proof-package-number proof-symbol-hash boymoo-model::a64-signed)))))

(local
 (defthm symbols-nonnil-view-word-differs-from-live-nil
   (implies (and (equal (proof-view word (proof-heap-base world) objects packages (proof-world-machine world)) view)
                 (not (equal view (proof-value-view nil)))
                 (proof-machine-value-p *proof-nil* nil world objects packages))
            (not (equal word *proof-nil*)))
   :rule-classes nil))

(local
 (defun symbols-key-lookup-dynamic-induction (view word world)
   (if (atom (cdddr view))
       word
     (symbols-key-lookup-dynamic-induction (cadddr view)
                                           (car (symbols-intern-fields-at t word world))
                                           world))))

(defthm symbols-physical-dynamic-chain-finds-decoded-binding
  (let* ((bindings (proof-dynamic-bucket view index count packages))
         (physical (symbols-intern-chain-binding (len (cdr bindings)) t word world))
         (decoded (symbols-dynamic-scan name number (symbols-intern-key-cached-hash number name) view packages))
         (base (proof-heap-base world))
         (machine (proof-world-machine world)))
    (implies (and bindings
                  (equal (proof-view word base objects packages machine) view)
                  (proof-machine-value-p *proof-nil* nil world objects packages)
                  (proof-packages-p packages)
                  (symbols-intern-key-input-p number name world)
                  (equal (proof-world-reg 9 world)
                         (proof-integer-word (symbols-intern-key-cached-hash number name))))
             (and (iff physical decoded)
                  (implies decoded
                           (equal (proof-view (cdr physical) base objects packages machine) decoded)))))
  :hints (("Goal"
           :induct (symbols-key-lookup-dynamic-induction view word world)
           :in-theory (disable proof-dynamic-bucket symbols-dynamic-scan symbols-intern-chain-binding
                               symbols-intern-key-cached-hash symbols-intern-key-input-p
                               symbols-intern-fields-at proof-machine-value-p proof-integer-word proof-packages-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-nonempty-bucket-has-tail)
                 (:instance symbols-dynamic-entry-fields-agree)
                 (:instance symbols-dynamic-entry-match-tests-home-key)
                 (:instance symbols-decoded-dynamic-scan-tests-home-key)
                 (:instance symbols-nonnil-view-word-differs-from-live-nil)
                 (:instance symbols-nonempty-chain-lookup-tests-head (dynamic t)
                            (rest-length (len (cdr (proof-dynamic-bucket (cadddr view) index count packages)))))
                 (:instance symbols-dynamic-head-symbol-and-hash))
           :in-theory (disable proof-dynamic-bucket symbols-dynamic-scan symbols-intern-chain-binding
                               symbols-nonempty-chain-lookup-tests-head symbols-decoded-dynamic-scan-tests-home-key
                               symbols-intern-key-cached-hash
                               symbols-intern-key-input-p symbols-intern-fields-at proof-machine-value-p
                               proof-integer-word proof-packages-p symbols-intern-key-matches-fields-p
                               proof-symbol-hash proof-package-number boymoo-model::a64-signed))
          ("Subgoal *1/1"
           :use ((:instance symbols-nonempty-bucket-has-tail))
           :in-theory (enable proof-dynamic-bucket symbols-dynamic-scan symbols-intern-chain-binding)))
  :rule-classes nil)

(defun symbols-static-bucket-views (world objects packages)
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (word (proof-load-word (+ base 16) machine)))
    (cdr (proof-view word base (proof-static-objects objects) packages machine))))

(defun symbols-static-bucket-slot (index world)
  (let* ((base (proof-heap-base world))
         (word (proof-load-word (+ base 16) (proof-world-machine world))))
    (+ 8 (proof-pointer-address word base) (* 8 index))))

(local
 (defthm symbols-static-bucket-vector-has-4096-slots
   (implies (and (natp first) (proof-static-buckets-p buckets first packages))
            (equal (+ first (len buckets)) 4096))
   :hints (("Goal" :induct (proof-static-buckets-p buckets first packages)
                   :in-theory (disable proof-static-bucket-p)))
   :rule-classes nil))

(local
 (defun symbols-static-bucket-index-induction (buckets first index)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list buckets first)
     (symbols-static-bucket-index-induction (cdr buckets) (1+ first) (1- index)))))

(local
 (defthm symbols-static-bucket-view-at-index
   (implies (and (proof-static-buckets-p buckets first packages)
                 (natp first) (natp index) (< index (len buckets)))
            (and (equal (nth index buckets) (proof-value-view (proof-view-value (nth index buckets))))
                 (proof-static-bucket-p (proof-view-value (nth index buckets)) (+ first index) packages)))
   :hints (("Goal" :induct (symbols-static-bucket-index-induction buckets first index)
                   :in-theory (disable proof-static-bucket-p)))
   :rule-classes nil))

(defthm symbols-static-bucket-slot-agrees-with-object-map
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (table (proof-load-word (+ base 16) machine))
         (address (proof-pointer-address table base))
         (entries (symbols-static-bucket-views world objects packages))
         (word (proof-load-word (symbols-static-bucket-slot index world) machine))
         (bucket (proof-view-value (nth index entries))))
    (implies (and (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (natp index) (< index 4096))
             (and (equal (len entries) 4096)
                  (equal (proof-word-tag table) 2)
                  (proof-span-p address 32776)
                  (proof-static-bucket-p bucket index packages)
                  (proof-machine-value-p word bucket world objects packages))))
  :hints (("Goal"
           :cases ((consp (proof-view (proof-load-word (+ 16 (proof-heap-base world)) (proof-world-machine world))
                                     (proof-heap-base world) (proof-static-objects objects) packages
                                     (proof-world-machine world))))
           :use ((:instance symbols-static-bucket-vector-has-4096-slots (first 0)
                            (buckets (symbols-static-bucket-views world objects packages)))
                 (:instance symbols-static-bucket-view-at-index (first 0)
                            (buckets (symbols-static-bucket-views world objects packages)))
                 (:instance symbols-vector-view-shape
                            (word (proof-load-word (+ 16 (proof-heap-base world)) (proof-world-machine world)))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (objects (proof-static-objects objects))
                            (entries (symbols-static-bucket-views world objects packages)))
                 (:instance symbols-vector-view-reads-slot
                            (word (proof-load-word (+ 16 (proof-heap-base world)) (proof-world-machine world)))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (objects (proof-static-objects objects))
                            (entries (symbols-static-bucket-views world objects packages)))
                 (:instance symbols-static-view-in-live-objects
                            (word (proof-load-word (symbols-static-bucket-slot index world) (proof-world-machine world)))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (disable proof-static-buckets-p proof-object-map-p proof-static-spans-p proof-home-bindings-p
                               proof-package-bindings-p proof-packages-p proof-static-objects proof-static-bucket-p
                               proof-span-p proof-view-value ash mod)))
  :rule-classes nil)

(defthm symbols-intern-static-slot-address-agrees-with-vector
  (let ((base (proof-heap-base world))
        (machine (proof-world-machine world)))
    (implies (and (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (natp index) (< index 4096)
                  (equal (symbols-intern-static-index world) index))
             (equal (symbols-intern-static-slot world) (symbols-static-bucket-slot index world))))
  :hints (("Goal"
           :use ((:instance symbols-static-bucket-slot-agrees-with-object-map)
                 (:instance symbols-chain-payload-after-header
                            (base (proof-heap-base world))
                            (word (proof-load-word (+ 16 (proof-heap-base world)) (proof-world-machine world)))))
           :in-theory (disable proof-static-p proof-object-map-p proof-static-bucket-p
                               symbols-static-bucket-views proof-machine-value-p
                               symbols-intern-static-index symbols-unsigned-sum-left symbols-unsigned-sum-right
                               symbols-chain-payload-after-header)))
  :rule-classes nil)

(local
 (defthm symbols-static-key-hash-is-index
   (and (natp (proof-symbol-hash number name 12))
        (< (proof-symbol-hash number name 12) 4096))
   :hints (("Goal" :in-theory (enable proof-symbol-hash)))
   :rule-classes nil))

(defthm symbols-static-probe-from-static-map
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (buckets (symbols-static-bucket-views world objects packages))
         (index (proof-symbol-hash number name 12))
         (entries (proof-view-value (nth index buckets)))
         (head (proof-world-reg 22 world))
         (physical (symbols-intern-chain-binding (len entries) nil head world))
         (source (proof-static-binding number name buckets)))
    (implies (and (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (symbols-intern-key-input-p number name world)
                  (equal head (proof-load-word (symbols-static-bucket-slot index world) machine)))
             (and (symbols-intern-chain-length-p (len entries) nil head world)
                  (iff physical source)
                  (implies physical
                           (proof-machine-value-p (cdr physical) (cdr source) world objects packages)))))
  :hints (("Goal"
           :use ((:instance symbols-static-key-hash-is-index)
                 (:instance symbols-static-bucket-slot-agrees-with-object-map
                            (index (proof-symbol-hash number name 12)))
                 (:instance symbols-static-nil-in-live-objects (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance symbols-physical-static-chain-terminates
                            (index (proof-symbol-hash number name 12))
                            (entries (proof-view-value
                                      (nth (proof-symbol-hash number name 12)
                                           (symbols-static-bucket-views world objects packages))))
                            (word (proof-world-reg 22 world)))
                 (:instance symbols-physical-static-chain-finds-source-binding
                            (index (proof-symbol-hash number name 12))
                            (entries (proof-view-value
                                      (nth (proof-symbol-hash number name 12)
                                           (symbols-static-bucket-views world objects packages))))
                            (word (proof-world-reg 22 world))))
           :in-theory (disable proof-static-p proof-object-map-p proof-static-bucket-p proof-symbol-hash
                               symbols-static-bucket-slot symbols-static-bucket-views symbols-intern-key-input-p
                               symbols-intern-chain-binding symbols-intern-chain-length-p proof-value-p
                               assoc-equal proof-view-value symbols-static-bucket-hit)))
  :rule-classes nil)

(local
 (defthm symbols-key-known-dynamic-heap-supplies-views
   (implies (proof-heap-p world objects packages)
            (and (proof-dynamic-entries (proof-dynamic-view world objects packages) packages)
                 (proof-machine-value-p *proof-nil* nil world objects packages)
                 (proof-object-map-p objects objects nil (proof-heap-base world) packages (proof-world-machine world))
                 (proof-packages-p packages)))
   :hints (("Goal"
            :use ((:instance symbols-static-nil-in-live-objects (base (proof-heap-base world))
                             (machine (proof-world-machine world))))
            :in-theory (disable proof-dynamic-entries proof-dynamic-view proof-object-map-p
                                proof-static-objects proof-static-spans-p proof-static-bucket-p
                                proof-static-buckets-p proof-home-bindings-p proof-package-bindings-p
                                proof-packages-p proof-value-p proof-heap-layout-p proof-stack-prefix
                                proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                                proof-dynamic-symbol-objects-p)))
   :rule-classes nil))

(local
 (defthm symbols-key-initialized-table-gives-bucket-views
   (let ((buckets (cddr root)))
     (implies (and (proof-dynamic-entries root packages)
                   (not (equal root (proof-value-view nil))))
              (and (posp (len buckets))
                   (proof-dynamic-buckets buckets 0 (len buckets) packages))))
   :hints (("Goal"
            :expand ((proof-dynamic-entries root packages))
            :in-theory (disable proof-dynamic-entries proof-dynamic-buckets acl2::binary-logand)))
   :rule-classes nil))

(defun symbols-dynamic-key-index (number name size)
  (logand (1- size) (symbols-intern-key-cached-hash number name)))

(local
 (defthm symbols-dynamic-key-index-in-range
   (implies (posp size)
            (and (natp (symbols-dynamic-key-index number name size))
                 (< (symbols-dynamic-key-index number name size) size)))
   :hints (("Goal"
            :use ((:instance symbols-and-mask-bounds (mask (1- size))
                             (x (symbols-intern-key-cached-hash number name))))
            :in-theory (disable acl2::binary-logand symbols-and-mask-bounds)))
   :rule-classes nil))

(defthm symbols-dynamic-probe-from-live-table
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (root (proof-dynamic-view world objects packages))
         (buckets (cddr root))
         (size (len buckets))
         (index (symbols-dynamic-key-index number name size))
         (view (nth index buckets))
         (entries (cdr (proof-dynamic-bucket view index size packages)))
         (head (proof-world-reg 22 world))
         (hash (symbols-intern-key-cached-hash number name))
         (physical (symbols-intern-chain-binding (len entries) t head world))
         (decoded (symbols-dynamic-scan name number hash view packages)))
    (implies (and (proof-heap-p world objects packages)
                  (not (equal root (proof-value-view nil)))
                  (symbols-intern-key-input-p number name world)
                  (equal (proof-world-reg 9 world) (proof-integer-word hash))
                  (equal head (symbols-physical-dynamic-root-bucket index world)))
             (and (symbols-intern-chain-length-p (len entries) t head world)
                  (iff physical decoded)
                  (implies physical
                           (equal (proof-view (cdr physical) base objects packages machine) decoded)))))
  :hints (("Goal"
           :use ((:instance symbols-key-known-dynamic-heap-supplies-views)
                 (:instance symbols-key-initialized-table-gives-bucket-views
                            (root (proof-dynamic-view world objects packages)))
                 (:instance symbols-dynamic-key-index-in-range
                            (size (len (cddr (proof-dynamic-view world objects packages)))))
                 (:instance symbols-nth-dynamic-bucket-valid (first 0)
                            (buckets (cddr (proof-dynamic-view world objects packages)))
                            (size (len (cddr (proof-dynamic-view world objects packages))))
                            (offset (symbols-dynamic-key-index number name
                                      (len (cddr (proof-dynamic-view world objects packages))))))
                 (:instance symbols-dynamic-table-bucket-word-has-bucket-view
                            (word (proof-dynamic-root (proof-heap-base world) (proof-world-machine world)))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (index (symbols-dynamic-key-index number name
                                     (len (cddr (proof-dynamic-view world objects packages))))))
                 (:instance symbols-physical-dynamic-chain-terminates
                            (word (proof-world-reg 22 world))
                            (count (len (cddr (proof-dynamic-view world objects packages))))
                            (index (symbols-dynamic-key-index number name
                                     (len (cddr (proof-dynamic-view world objects packages)))))
                            (view (nth (symbols-dynamic-key-index number name
                                         (len (cddr (proof-dynamic-view world objects packages))))
                                       (cddr (proof-dynamic-view world objects packages)))))
                 (:instance symbols-physical-dynamic-chain-finds-decoded-binding
                            (word (proof-world-reg 22 world))
                            (count (len (cddr (proof-dynamic-view world objects packages))))
                            (index (symbols-dynamic-key-index number name
                                     (len (cddr (proof-dynamic-view world objects packages)))))
                            (view (nth (symbols-dynamic-key-index number name
                                         (len (cddr (proof-dynamic-view world objects packages))))
                                       (cddr (proof-dynamic-view world objects packages))))))
           :in-theory (disable proof-heap-p proof-object-map-p proof-dynamic-entries proof-dynamic-bucket proof-dynamic-buckets
                               proof-dynamic-root proof-value-p proof-packages-p proof-integer-word
                               symbols-intern-chain-length-p symbols-intern-chain-binding symbols-dynamic-scan
                               symbols-intern-key-input-p symbols-intern-key-cached-hash symbols-dynamic-key-index)))
  :rule-classes nil)

(local
 (defthm symbols-dynamic-header-gives-mask-at-address
   (let ((header (proof-load-word table (proof-world-machine world))))
     (implies (and (posp size) (< (+ 1 size) (expt 2 53))
                   (equal header (+ 6 (* 2048 (+ 1 size)))))
              (equal (symbols-dynamic-mask-at table world) (1- size))))
   :hints (("Goal"
            :use ((:instance symbols-logical-right-shift-correct
                             (word (proof-load-word table (proof-world-machine world))) (amount 11))
                  (:instance symbols-floor-of-decomposition (q (+ 1 size)) (r 6) (divisor 2048)))
            :in-theory (disable symbols-floor-of-decomposition)))
   :rule-classes nil))

(local
 (defthm symbols-key-arithmetic-right-shift-one
   (equal (ash word -1) (floor (ifix word) 2))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm symbols-key-tagged-hash-fits-word
   (unsigned-byte-p 64 (proof-integer-word value))
   :hints (("Goal" :in-theory (enable proof-integer-word)))
   :rule-classes nil))

(defthm symbols-dynamic-slot-address-agrees-with-key
  (let* ((size (expt 2 bits))
         (index (symbols-dynamic-key-index number name size))
         (hash (symbols-intern-key-cached-hash number name)))
    (implies (and (natp number) (natp bits) (<= bits 63)
                  (< (+ 1 size) (expt 2 53))
                  (proof-span-p table (+ 16 (* 8 size)))
                  (equal (proof-load-word table (proof-world-machine world)) (+ 6 (* 2048 (+ 1 size))))
                  (equal tagged (proof-integer-word hash)))
             (equal (symbols-dynamic-bucket-at table tagged world)
                    (+ table 16 (* 8 index)))))
  :hints (("Goal"
           :use ((:instance symbols-dynamic-key-index-in-range (size (expt 2 bits)))
                 (:instance symbols-dynamic-header-gives-mask-at-address (size (expt 2 bits)))
                 (:instance symbols-logical-right-shift-correct (word tagged) (amount 1))
                 (:instance symbols-key-tagged-hash-fits-word (value (symbols-intern-key-cached-hash number name)))
                 (:instance symbols-machine-tagged-hash)
                 (:instance symbols-machine-dynamic-hash))
           :in-theory (disable symbols-machine-tagged-hash symbols-machine-dynamic-hash
                               symbols-dynamic-mask-at proof-symbol-hash proof-integer-word
                               symbols-machine-key-hash acl2::binary-logand floor boymoo-model::a64-signed)))
  :rule-classes nil)
