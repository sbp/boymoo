(in-package "BOYMOO-PROOFS")

(include-book "bits")
(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned mod floor ash
                     acl2::binary-logior acl2::binary-logand)))

(local
 (defthm symbols-memory-assoc-of-put
   (implies (and (natp key) (natp target))
            (equal (assoc-equal key (put-assoc-equal target value memory))
                   (if (equal key target)
                       (cons target value)
                     (assoc-equal key memory))))))

(local
 (defthm symbols-byte-at-written-address
   (implies (and (natp address) (< address (expt 2 64)))
            (equal (boymoo-model::a64-byte
                    address (put-assoc-equal address (boymoo-model::a64-unsigned 8 value) memory))
                   (boymoo-model::a64-unsigned 8 value)))))

(local
 (defthm symbols-byte-at-other-address
   (implies (and (natp address) (natp target)
                 (< address (expt 2 64)) (< target (expt 2 64)) (not (equal address target)))
            (equal (boymoo-model::a64-byte address
                                          (put-assoc-equal target value memory))
                   (boymoo-model::a64-byte address memory)))))

(defthm symbols-disjoint-byte-write
  (implies (and (natp address) (< address (expt 2 64))
                (natp target) (natp count) (<= (+ target count) (expt 2 64))
                (or (< address target) (<= (+ target count) address)))
           (equal (boymoo-model::a64-byte
                   address (boymoo-model::a64-write-bytes count target value memory))
                  (boymoo-model::a64-byte address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count target value memory)
                  :in-theory (disable boymoo-model::a64-byte put-assoc-equal assoc-equal))))

(defthm symbols-disjoint-read-and-write
  (implies (and (natp address) (natp size) (<= (+ address size) (expt 2 64))
                (natp target) (natp count) (<= (+ target count) (expt 2 64))
                (proof-disjoint-p address (+ address size) target (+ target count)))
           (equal (boymoo-model::a64-read-bytes
                   size address (boymoo-model::a64-write-bytes count target value memory))
                  (boymoo-model::a64-read-bytes size address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes size address memory)
                  :in-theory (disable boymoo-model::a64-byte boymoo-model::a64-write-bytes))))

(local
 (defthm symbols-right-shift-byte-is-floor
   (implies (integerp word)
            (equal (ash word -8) (floor word 256)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm symbols-low-byte-and-tail-decompose-word
   (implies (integerp word)
            (equal (+ (boymoo-model::a64-unsigned 8 word) (* 256 (ash word -8)))
                   word))
   :hints (("Goal" :in-theory (enable symbols-unsigned-as-mod mod)))))

(local
 (defthm symbols-expt-plus-eight
   (implies (natp width)
            (equal (expt 2 (+ 8 width)) (* 256 (expt 2 width))))
   :hints (("Goal" :expand ((expt 2 (+ 8 width)) (expt 2 (+ 7 width))
                            (expt 2 (+ 6 width)) (expt 2 (+ 5 width))
                            (expt 2 (+ 4 width)) (expt 2 (+ 3 width))
                            (expt 2 (+ 2 width)) (expt 2 (+ 1 width)))))))

(local
 (defthm symbols-base-256-decomposition
   (implies (and (integerp upper) (posp divisor) (natp low) (< low 256))
            (equal (+ (* 256 divisor (floor upper divisor))
                      (+ low (* 256 (mod upper divisor))))
                   (+ low (* 256 upper))))
   :hints (("Goal" :in-theory (enable mod) :nonlinearp t))
   :rule-classes nil))

(local
 (defthm symbols-base-256-modulus
   (implies (and (integerp upper) (posp divisor) (natp low) (< low 256))
            (equal (mod (+ low (* 256 upper)) (* 256 divisor))
                   (+ low (* 256 (mod upper divisor)))))
   :hints (("Goal"
            :use ((:instance symbols-base-256-decomposition)
                  (:instance symbols-mod-of-decomposition
                             (q (floor upper divisor))
                             (r (+ low (* 256 (mod upper divisor))))
                             (divisor (* 256 divisor))))
            :in-theory (disable symbols-mod-of-decomposition)))
   :rule-classes nil))

(local
 (defthm symbols-byte-and-tail-recombine
   (let* ((tail (ash word -8))
          (head (boymoo-model::a64-unsigned 8 word))
          (rest (boymoo-model::a64-unsigned width tail)))
     (implies (and (natp width) (integerp word))
              (equal (logior head (ash rest 8))
                     (boymoo-model::a64-unsigned (+ width 8) word))))
   :hints (("Goal"
            :use ((:instance symbols-low-byte-and-tail-decompose-word)
                  (:instance symbols-or-of-low-and-aligned-fields
                             (width 8) (low (boymoo-model::a64-unsigned 8 word))
                             (high (boymoo-model::a64-unsigned width (ash word -8))))
                  (:instance symbols-base-256-modulus
                             (upper (ash word -8)) (divisor (expt 2 width))
                             (low (boymoo-model::a64-unsigned 8 word))))
            :in-theory (enable symbols-unsigned-as-mod)))
   :rule-classes nil))

(defthm symbols-read-written-bytes
  (implies (and (natp address) (natp count) (<= (+ address count) (expt 2 64))
                (integerp value))
           (equal (boymoo-model::a64-read-bytes
                   count address (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-unsigned (* 8 count) value)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (disable boymoo-model::a64-byte put-assoc-equal))
          ("Subgoal *1/2"
           :use ((:instance symbols-byte-and-tail-recombine
                            (word value) (width (* 8 (1- count)))))
           :in-theory (disable boymoo-model::a64-byte put-assoc-equal))))

(defthm symbols-load-word-after-store
  (implies (and (natp address) (<= (+ address 8) (expt 2 64))
                (integerp value))
           (equal (proof-load-word address (boymoo-model::a64-store 8 address value machine))
                  (boymoo-model::a64-unsigned 64 value)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes))))

(defthm symbols-load-word-after-disjoint-store
  (implies (and (natp address) (<= (+ address 8) (expt 2 64))
                (natp target) (<= (+ target 8) (expt 2 64))
                (proof-disjoint-p address (+ address 8) target (+ target 8)))
           (equal (proof-load-word address (boymoo-model::a64-store 8 target value machine))
                  (proof-load-word address machine)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes))))

(defthm symbols-byte-list-after-disjoint-store
  (implies (and (natp address) (natp size) (<= (+ address size) (expt 2 64))
                (natp target) (natp count) (<= (+ target count) (expt 2 64))
                (proof-disjoint-p address (+ address size) target (+ target count)))
           (equal (proof-byte-list size address (boymoo-model::a64-store count target value machine))
                  (proof-byte-list size address machine)))
  :hints (("Goal" :induct (proof-byte-list size address machine)
                  :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes))))

(defun symbols-memory-addresses-p (entries)
  (if (atom entries)
      (null entries)
    (and (natp (caar entries)) (symbols-memory-addresses-p (cdr entries)))))

(local
 (defthm symbols-put-keeps-memory-addresses
   (implies (and (natp address) (symbols-memory-addresses-p memory))
            (symbols-memory-addresses-p (put-assoc-equal address value memory)))))

(local
 (defthm symbols-write-keeps-memory-addresses
   (implies (symbols-memory-addresses-p memory)
            (symbols-memory-addresses-p (boymoo-model::a64-write-bytes count target value memory)))
   :hints (("Goal" :induct (boymoo-model::a64-write-bytes count target value memory)
                   :in-theory (disable put-assoc-equal)))))

(local
 (defthm symbols-span-entries-unchanged-by-disjoint-store
   (implies (and (natp start) (natp end) (<= end (expt 2 64))
                 (natp target) (natp count) (<= (+ target count) (expt 2 64))
                 (symbols-memory-addresses-p entries)
                 (proof-disjoint-p start end target (+ target count)))
            (proof-byte-entries-agree-p entries start end memory
                                        (boymoo-model::a64-write-bytes count target value memory)))
   :hints (("Goal"
            :induct (proof-byte-entries-agree-p entries start end memory
                                                 (boymoo-model::a64-write-bytes count target value memory))
            :in-theory (disable boymoo-model::a64-byte boymoo-model::a64-write-bytes)))))

(defthm symbols-disjoint-store-preserves-memory-span
  (let ((after (update-nth 0 (boymoo-model::a64-store count target value
                                                   (proof-world-machine before)) before)))
    (implies (and (natp start) (natp end) (<= end (expt 2 64))
                  (natp target) (natp count) (<= (+ target count) (expt 2 64))
                  (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine before)))
                  (proof-disjoint-p start end target (+ target count)))
             (proof-memory-span-agrees-p start end before after)))
  :hints (("Goal" :in-theory (disable proof-byte-entries-agree-p boymoo-model::a64-write-bytes)))
  :rule-classes nil)

(local
 (defthm symbols-matching-entry-implies-matching-byte
   (implies (and (assoc-equal address entries) (natp address)
                 (<= start address) (< address end)
                 (proof-byte-entries-agree-p entries start end first last))
            (equal (boymoo-model::a64-byte address first)
                   (boymoo-model::a64-byte address last)))
   :hints (("Goal" :induct (assoc-equal address entries)
                   :in-theory (disable boymoo-model::a64-byte)))
   :rule-classes nil))

(local
 (defthm symbols-absent-address-reads-zero
   (implies (and (natp address) (< address (expt 2 64))
                 (not (assoc-equal address memory)))
            (equal (boymoo-model::a64-byte address memory) 0))))

(defthm symbols-memory-span-agreement-gives-byte
  (implies (and (proof-memory-span-agrees-p start end first last)
                (natp address) (<= start address) (< address end)
                (< address (expt 2 64)))
           (equal (boymoo-model::a64-byte address (boymoo-model::a64-memory (proof-world-machine first)))
                  (boymoo-model::a64-byte address (boymoo-model::a64-memory (proof-world-machine last)))))
  :hints (("Goal"
           :use ((:instance symbols-matching-entry-implies-matching-byte
                            (entries (boymoo-model::a64-memory (proof-world-machine first)))
                            (first (boymoo-model::a64-memory (proof-world-machine first)))
                            (last (boymoo-model::a64-memory (proof-world-machine last))))
                 (:instance symbols-matching-entry-implies-matching-byte
                            (entries (boymoo-model::a64-memory (proof-world-machine last)))
                            (first (boymoo-model::a64-memory (proof-world-machine first)))
                            (last (boymoo-model::a64-memory (proof-world-machine last)))))
           :in-theory (disable proof-byte-entries-agree-p boymoo-model::a64-byte
                               boymoo-model::a64-memory proof-world-machine)))
  :rule-classes nil)

(local
 (defthm symbols-agreeing-memory-spans-give-agreeing-entries
   (implies (and (proof-memory-span-agrees-p start end first middle)
                 (proof-memory-span-agrees-p start end middle last)
                 (symbols-memory-addresses-p entries)
                 (<= end (expt 2 64)))
            (proof-byte-entries-agree-p entries start end
                                        (boymoo-model::a64-memory (proof-world-machine first))
                                        (boymoo-model::a64-memory (proof-world-machine last))))
   :hints (("Goal"
            :induct (len entries)
            :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-byte
                                boymoo-model::a64-memory proof-world-machine))
           ("Subgoal *1/1"
            :use ((:instance symbols-memory-span-agreement-gives-byte (address (caar entries)) (last middle))
                  (:instance symbols-memory-span-agreement-gives-byte (address (caar entries)) (first middle)))
            :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-byte
                                boymoo-model::a64-memory proof-world-machine)))
   :rule-classes nil))

(defthm symbols-memory-span-agreement-is-transitive
  (implies (and (proof-memory-span-agrees-p start end first middle)
                (proof-memory-span-agrees-p start end middle last)
                (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine first)))
                (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine last)))
                (<= end (expt 2 64)))
           (proof-memory-span-agrees-p start end first last))
  :hints (("Goal"
           :use ((:instance symbols-agreeing-memory-spans-give-agreeing-entries
                            (entries (boymoo-model::a64-memory (proof-world-machine first))))
                 (:instance symbols-agreeing-memory-spans-give-agreeing-entries
                            (entries (boymoo-model::a64-memory (proof-world-machine last)))))
           :in-theory (disable proof-byte-entries-agree-p boymoo-model::a64-memory proof-world-machine)))
  :rule-classes nil)

(local
 (defthm symbols-read-agreeing-byte-span
   (implies (and (proof-memory-span-agrees-p start end before after)
                 (natp count) (natp address) (<= start address)
                 (<= (+ address count) end) (<= end (expt 2 64)))
            (equal (boymoo-model::a64-read-bytes
                    count address (boymoo-model::a64-memory (proof-world-machine before)))
                   (boymoo-model::a64-read-bytes
                    count address (boymoo-model::a64-memory (proof-world-machine after)))))
   :hints (("Goal"
            :induct (boymoo-model::a64-read-bytes count address
                                                 (boymoo-model::a64-memory (proof-world-machine before)))
            :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-byte
                                boymoo-model::a64-memory proof-world-machine))
           ("Subgoal *1/2"
            :use ((:instance symbols-memory-span-agreement-gives-byte (first before) (last after)))
            :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-byte
                                boymoo-model::a64-memory proof-world-machine)))
   :rule-classes nil))

(defthm symbols-agreeing-memory-span-gives-word
  (implies (and (proof-memory-span-agrees-p start end before after)
                (natp address) (<= start address)
                (<= (+ address 8) end) (<= end (expt 2 64)))
           (equal (proof-load-word address (proof-world-machine before))
                  (proof-load-word address (proof-world-machine after))))
  :hints (("Goal" :use ((:instance symbols-read-agreeing-byte-span (count 8)))
                  :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-read-bytes
                                      boymoo-model::a64-memory proof-world-machine)))
  :rule-classes nil)

(local
 (defun symbols-memory-image (machine)
   (list nil 0 0 0 (boymoo-model::a64-memory machine))))

(local
 (defthm symbols-memory-of-memory-image
   (equal (boymoo-model::a64-memory (symbols-memory-image machine))
          (boymoo-model::a64-memory machine))))

(local
 (in-theory (disable symbols-memory-image boymoo-model::a64-memory
                     boymoo-model::a64-read-bytes proof-load-string)))

(local
 (defthm symbols-read-word-of-memory-image
   (equal (proof-load-word address (symbols-memory-image machine))
          (proof-load-word address machine))))

(local
 (defthm symbols-byte-list-of-memory-image
   (equal (proof-byte-list size address (symbols-memory-image machine))
          (proof-byte-list size address machine))))

(local
 (defthm symbols-load-string-of-memory-image
   (equal (proof-load-string size address (symbols-memory-image machine))
          (proof-load-string size address machine))
   :hints (("Goal" :in-theory (enable proof-load-string)))))

(local
 (defthm symbols-limbs-of-memory-image
   (equal (proof-limbs-p count address (symbols-memory-image machine))
          (proof-limbs-p count address machine))))

(local
 (defthm symbols-magnitude-of-memory-image
   (equal (proof-limb-magnitude count address (symbols-memory-image machine))
          (proof-limb-magnitude count address machine))))

(local
 (defthm symbols-integer-view-of-memory-image
   (equal (proof-integer-view address (symbols-memory-image machine))
          (proof-integer-view address machine))
   :hints (("Goal" :in-theory (disable proof-load-word proof-limbs-p proof-limb-magnitude)))))

(local
 (defthm symbols-view-step-of-memory-image
   (equal (proof-view-step kind word count depth base objects packages (symbols-memory-image machine))
          (proof-view-step kind word count depth base objects packages machine))
   :hints (("Goal" :induct (proof-view-step kind word count depth base objects packages machine)
                   :in-theory (disable proof-load-word proof-integer-view proof-symbol-value
                                       proof-word-tag proof-pointer-address
                                       proof-header-type proof-header-size proof-span-p
                                       proof-rational-value proof-complex-value proof-cons-value)))))

(local
 (defthm symbols-view-of-memory-image
   (equal (proof-view word base objects packages (symbols-memory-image machine))
          (proof-view word base objects packages machine))
   :hints (("Goal" :in-theory (disable proof-view-step proof-pointer-address)))))

(defthm symbols-view-depends-on-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-view word base objects packages first)
                  (proof-view word base objects packages last)))
  :hints (("Goal"
           :use ((:instance symbols-view-of-memory-image (machine first))
                 (:instance symbols-view-of-memory-image (machine last)))
           :in-theory (e/d (symbols-memory-image)
                           (proof-view symbols-view-of-memory-image proof-view-step))))
  :rule-classes nil)

; Each write is a pair of the destination address and the word.
(defun symbols-write-words (writes world)
  (if (atom writes)
      world
    (symbols-write-words
     (cdr writes)
     (update-nth 0 (boymoo-model::a64-store 8 (caar writes) (cdar writes)
                                          (proof-world-machine world)) world))))

(defun symbols-word-writes-in-span-p (writes start end)
  (if (atom writes)
      (null writes)
    (and (natp (caar writes)) (<= start (caar writes)) (<= (+ 8 (caar writes)) end)
         (symbols-word-writes-in-span-p (cdr writes) start end))))

(local
 (defthm symbols-write-words-preserve-memory-addresses
   (implies (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine world)))
            (symbols-memory-addresses-p
             (boymoo-model::a64-memory (proof-world-machine (symbols-write-words writes world)))))
   :hints (("Goal" :induct (symbols-write-words writes world)
                   :in-theory (e/d (boymoo-model::a64-memory)
                                   (boymoo-model::a64-write-bytes))))))

(local
 (defthm symbols-one-word-write-preserves-memory-addresses
   (implies (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine world)))
            (symbols-memory-addresses-p
             (boymoo-model::a64-memory
              (proof-world-machine
               (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine world)) world)))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-memory proof-world-machine)
                                   (boymoo-model::a64-write-bytes update-nth))))))

(local
 (defthm symbols-byte-entries-agree-with-themselves
   (proof-byte-entries-agree-p entries start end memory memory)
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries start end memory memory)))))

(local
 (defthm symbols-identical-memory-agrees-on-span
   (implies (equal (boymoo-model::a64-memory (proof-world-machine before))
                   (boymoo-model::a64-memory (proof-world-machine after)))
            (proof-memory-span-agrees-p start end before after))
   :hints (("Goal" :in-theory (disable proof-world-machine proof-byte-entries-agree-p)))))

(defthm symbols-word-writes-preserve-disjoint-span
  (implies (and (natp start) (natp end) (<= end (expt 2 64))
                (<= upper (expt 2 64))
                (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine before)))
                (symbols-word-writes-in-span-p writes lower upper)
                (proof-disjoint-p start end lower upper))
           (proof-memory-span-agrees-p start end before (symbols-write-words writes before)))
  :hints (("Goal" :induct (symbols-write-words writes before)
                  :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-store
                                      proof-world-machine update-nth))
          ("Subgoal *1/2"
           :use ((:instance symbols-disjoint-store-preserves-memory-span
                            (target (caar writes)) (value (cdar writes)) (count 8))
                 (:instance symbols-memory-span-agreement-is-transitive
                            (first before) (last (symbols-write-words writes before))
                            (middle (update-nth 0 (boymoo-model::a64-store 8 (caar writes) (cdar writes)
                                                                         (proof-world-machine before))
                                                before))))
           :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-store
                               proof-world-machine update-nth)))
  :rule-classes nil)

(local
 (defthm symbols-update-memory-preserves-first-field
   (equal (car (update-nth 4 value machine)) (car machine))
   :hints (("Goal" :expand ((update-nth 4 value machine))))))

(local
 (defthm symbols-one-word-write-preserves-registers-and-mappings
   (let ((after (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine before)) before)))
     (and (equal (proof-world-reg register after) (proof-world-reg register before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (proof-world-replies after) (proof-world-replies before))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-registers boymoo-model::a64-sp)
                                   (boymoo-model::a64-write-bytes update-nth))))))

(defthm symbols-write-words-preserve-registers-and-mappings
  (let ((after (symbols-write-words writes before)))
    (and (equal (proof-world-reg register after) (proof-world-reg register before))
         (equal (proof-world-regions after) (proof-world-regions before))
         (equal (proof-world-replies after) (proof-world-replies before))))
  :hints (("Goal" :induct (symbols-write-words writes before)
                  :in-theory (disable boymoo-model::a64-store update-nth proof-world-reg
                                      proof-world-regions proof-world-replies proof-world-machine))))

(local
 (defthm symbols-member-of-valid-regions
   (implies (and (proof-regions-p regions) (member-equal region regions))
            (proof-region-p region))
   :hints (("Goal" :induct (proof-regions-p regions)
                   :in-theory (disable proof-region-p proof-region-disjoint-p)))))

(local
 (defthm symbols-covered-span-is-well-formed
   (implies (proof-covered-p address size access regions)
            (proof-span-p address size))
   :hints (("Goal" :induct (proof-covered-p address size access regions)
                   :in-theory (disable proof-span-p proof-region-allows-p)))))

(local
 (defthm symbols-machine-stack-writes-preserve-external-mappings
   (let* ((floor (- (proof-machine-limit before) *proof-machine-margin*))
          (ceiling (+ floor *proof-machine-reservation*))
          (mappings (proof-external-objects head fuel before objects)))
     (implies (and mappings (proof-regions-p (proof-world-regions before))
                   (<= ceiling (expt 2 64))
                   (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine before)))
                   (symbols-word-writes-in-span-p writes floor ceiling))
              (proof-fixed-external-p (cdr mappings) before (symbols-write-words writes before))))
   :hints (("Goal"
            :induct (proof-external-objects head fuel before objects)
            :in-theory (disable symbols-write-words proof-load-word proof-heap-base
                                proof-machine-limit proof-stack-base proof-stack-end proof-spaces-end
                                proof-world-machine proof-world-regions proof-regions-p
                                proof-object-zone proof-object-kind proof-header-size proof-header-type
                                proof-align-up proof-disjoint-p proof-memory-span-agrees-p))
           ("Subgoal *1/2"
            :use ((:instance symbols-member-of-valid-regions
                             (region (proof-region
                                      head (+ head (proof-load-word (+ head 8) (proof-world-machine before))) :rw))
                             (regions (proof-world-regions before)))
                  (:instance symbols-word-writes-preserve-disjoint-span
                             (start head) (end (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                             (lower (- (proof-machine-limit before) *proof-machine-margin*))
                             (upper (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                       *proof-machine-reservation*))))
            :in-theory (disable symbols-write-words proof-load-word proof-heap-base
                                proof-machine-limit proof-stack-base proof-stack-end proof-spaces-end
                                proof-world-machine proof-world-regions proof-regions-p
                                proof-object-zone proof-object-kind proof-header-size proof-header-type
                                proof-align-up proof-disjoint-p proof-memory-span-agrees-p)))
   :rule-classes nil))

(defthm symbols-machine-stack-writes-preserve-fixed-heap
  (let* ((floor (- (proof-machine-limit before) *proof-machine-margin*))
         (ceiling (+ floor *proof-machine-reservation*)))
    (implies (and (proof-heap-layout-p before)
                  (proof-external-objects (proof-external-head before) (len objects) before objects)
                  (symbols-memory-addresses-p (boymoo-model::a64-memory (proof-world-machine before)))
                  (symbols-word-writes-in-span-p writes floor ceiling))
             (proof-fixed-heap-p before (symbols-write-words writes before) objects)))
  :hints (("Goal"
           :use ((:instance symbols-machine-stack-writes-preserve-external-mappings
                            (head (proof-external-head before)) (fuel (len objects)))
                 (:instance symbols-word-writes-preserve-disjoint-span
                            (start (- (proof-heap-base before) *proof-heap-prefix*))
                            (end (proof-spaces-end before))
                            (lower (- (proof-machine-limit before) *proof-machine-margin*))
                            (upper (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                      *proof-machine-reservation*)))
                 (:instance symbols-covered-span-is-well-formed
                            (address (- (proof-machine-limit before) *proof-machine-margin*))
                            (size *proof-machine-reservation*) (access :write)
                            (regions (proof-world-regions before)))
                 (:instance symbols-covered-span-is-well-formed
                            (address (- (proof-heap-base before) *proof-heap-prefix*))
                            (size (+ *proof-heap-prefix* (- (proof-spaces-end before) (proof-heap-base before))))
                            (access :write) (regions (proof-world-regions before))))
           :in-theory (disable symbols-write-words proof-load-word proof-runtime-word
                               proof-heap-base proof-machine-limit proof-active-floor proof-active-end
                               proof-inactive-floor proof-inactive-end proof-cons-floor
                               proof-stack-base proof-stack-end proof-spaces-end proof-external-head
                               proof-world-machine proof-world-regions proof-world-replies
                               proof-regions-p proof-region-p proof-external-objects proof-covered-p
                               proof-disjoint-p proof-memory-span-agrees-p proof-fixed-external-p)))
  :rule-classes nil)
