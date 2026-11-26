(in-package "BOYMOO-PROOFS")

(include-book "publication-heap")
(include-book "string-results")
(include-book "constructor-calls")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-publication-address-fields-are-natural
   (and (natp (proof-active-floor world)) (natp (proof-box-top world))
        (natp (proof-heap-base world)) (natp (proof-world-reg 0 world)))
   :hints (("Goal" :in-theory (enable proof-active-floor proof-runtime-word proof-load-word
                                    proof-box-top proof-heap-base proof-world-reg proof-reg)))
   :rule-classes nil))

(local
 (defthm sequence-single-string-record-keeps-old-keys
   (implies (and (proof-object-map-p pending objects seen base packages machine)
                 (not (assoc-equal address pending)))
            (sequence-new-records-miss-existing-keys-p
             pending (list (proof-object address :active :header 0))))
   :hints
   (("Goal"
     :in-theory (e/d ((:induction proof-object-map-p) proof-object-record-p)
                     (proof-object-size proof-object-view proof-object-disjoint-p
                      proof-symbol-object-p proof-view-value proof-span-p))
     :induct (proof-object-map-p pending objects seen base packages machine)
     :expand ((proof-object-map-p pending objects seen base packages machine))))
   :rule-classes nil))

(local
 (defthm sequence-string-header-fields-at-publication
   (let ((header (proof-load-word address machine)))
     (implies (and (natp length) (equal header (+ 1 (* 256 length))))
              (and (equal (proof-header-size header) length)
                   (equal (proof-header-type header) 1))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-header-size proof-header-type sequence-a64-unsigned-as-mod)
                     (proof-load-word sequence-floor-add-multiple sequence-mod-add-multiple))
     :use ((:instance sequence-floor-add-multiple (value 1) (multiple length) (divisor 256))
           (:instance sequence-mod-add-multiple (value 1) (multiple length) (divisor 256)))))
   :rule-classes nil))

(local
 (defthm sequence-string-record-is-in-reserved-span
   (let* ((base (proof-heap-base before))
          (machine (proof-world-machine after))
          (record (proof-object address :active :header 0))
          (bytes (+ 8 (proof-align-up length 8)))
          (records (list record))
          (extended (cons record objects)))
     (implies
      (and (natp length)
           (sequence-initialized-string-p (proof-object-word record base) base address length extended machine)
           (equal (mod address 8) 0)
           (proof-span-p address bytes)
           (proof-object-disjoint-p address (+ address bytes) objects machine)
           (natp (proof-active-floor after))
           (natp (proof-box-top after))
           (<= (proof-active-floor after) address)
           (equal (+ address bytes) (proof-box-top after)))
      (and (sequence-added-object-records-p records objects extended base packages machine)
           (proof-heap-object-spans-p records external after))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-added-object-records-p proof-object-view proof-object-record-p
                      proof-object-size proof-heap-object-spans-p proof-symbol-object-p proof-subspan-p
                      sequence-initialized-string-p)
                     (proof-object-word proof-object-disjoint-p proof-align-up proof-load-word proof-load-string
                      proof-view proof-header-type proof-header-size proof-world-machine proof-heap-base
                      proof-active-floor proof-box-top proof-word-tag proof-pointer-address))
     :use ((:instance sequence-string-header-fields-at-publication (machine (proof-world-machine after)))
           (:instance sequence-initialized-string-views-its-bytes
                      (word (proof-object-word (proof-object address :active :header 0) (proof-heap-base before)))
                      (base (proof-heap-base before)) (header address)
                      (objects (cons (proof-object address :active :header 0) objects))
                      (machine (proof-world-machine after))))))
   :rule-classes nil))

(defthm sequence-publish-initialized-string-in-reservation
  (let* ((last (proof-world-machine after))
         (base (proof-heap-base before))
         (record (proof-object address :active :header 0))
         (extended (cons record objects))
         (bytes (+ 8 (proof-align-up length 8))))
    (implies
     (and (proof-heap-p before objects packages)
          (proof-reserved-span-p :header address bytes before objects)
          (sequence-publication-preserves-storage-p before after objects packages)
          (natp length)
          (equal (mod address 8) 0)
          (sequence-initialized-string-p (proof-object-word record base) base address length extended last))
     (proof-preserved-heap-p nil before after objects extended packages)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (proof-reserved-span-p sequence-heap-registers-agree-p sequence-heap-metadata-agrees-p)
                    (proof-preserved-heap-p proof-heap-p proof-object-map-p proof-world-machine
                     proof-span-p proof-object-disjoint-p proof-object-size proof-object-word
                     proof-active-floor proof-box-top proof-align-up proof-header-size proof-header-type
                     proof-heap-base proof-stack-top proof-stack-limit proof-machine-limit proof-heap-limit
                     sequence-initialized-string-p sequence-added-object-records-p
                     sequence-new-records-miss-existing-keys-p sequence-object-storage-agrees-p))
    :expand ((proof-heap-p before objects packages))
    :use ((:instance sequence-reservation-contains-no-published-address
                     (pending objects) (seen nil) (base (proof-heap-base before)) (start address)
                     (end (+ address 8 (proof-align-up length 8))) (machine (proof-world-machine before)))
          (:instance sequence-single-string-record-keeps-old-keys
                     (pending objects) (seen nil) (base (proof-heap-base before))
                     (machine (proof-world-machine before)))
          (:instance sequence-disjoint-objects-on-agreed-storage
                     (start address) (end (+ address 8 (proof-align-up length 8)))
                     (pending objects) (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-align-up-covers-address (address length) (alignment 8))
          (:instance sequence-publication-address-fields-are-natural (world after))
          (:instance sequence-string-record-is-in-reserved-span
                     (external (cdr (proof-external-objects (proof-external-head before)
                                                             (len objects) before objects))))
          (:instance sequence-publish-active-nonsymbol-objects
                     (records (list (proof-object address :active :header 0)))))))
  :rule-classes nil)

(local
 (defthm sequence-header-integer-in-lowest-terms
   (implies (integerp value)
            (and (equal (denominator value) 1)
                 (equal (numerator value) value)))
   :hints
   (("Goal"
     :in-theory (disable acl2::rational-implies2 associativity-of-*)
     :use ((:instance acl2::rational-implies1 (acl2::x value))
           (:instance acl2::rational-implies2 (acl2::x value))
           (:instance associativity-of-*
                      (acl2::x (denominator value)) (acl2::y (/ (denominator value)))
                      (acl2::z (numerator value)))
           (:instance acl2::lowest-terms
                      (acl2::x value) (acl2::n (denominator value)) (acl2::r value) (acl2::q 1)))))))

(local
 (defthm sequence-header-aligned-payload-size
   (implies (natp blocks)
            (equal (proof-align-up (* 8 blocks) 8) (* 8 blocks)))
   :hints (("Goal"
            :in-theory (e/d (proof-align-up ceiling) (associativity-of-* acl2::rational-implies2))
            :use ((:instance associativity-of-*
                             (acl2::x 1/8) (acl2::y 8) (acl2::z blocks))
                  (:instance acl2::rational-implies2 (acl2::x blocks)))))
   :rule-classes nil))

(local
 (defthm sequence-header-integer-upper-end
   (implies (and (integerp lower) (integerp upper) (< upper (1+ lower)))
            (<= upper lower))
   :hints (("Goal"
            :use ((:instance sequence-floor-unique
                             (value (- upper lower)) (divisor 1) (quotient 0))
                  (:instance sequence-floor-unique
                             (value (- upper lower)) (divisor 1) (quotient (- upper lower))))))
   :rule-classes nil))

(local
 (defthm sequence-string-allocation-matches-object-size
   (implies (natp length)
            (equal (sequence-small-string-allocation length) (+ 8 (proof-align-up length 8))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-small-string-allocation proof-align-up)
                     (floor ceiling sequence-floor-add-multiple))
     :cases ((equal (proof-align-up length 8) (+ length 8)))
     :use ((:instance sequence-align-up-covers-address (address length) (alignment 8))
           (:instance sequence-align-up-upper-bound (address length) (alignment 8))
           (:instance sequence-header-aligned-payload-size (blocks (1- (ceiling length 8))))
           (:instance sequence-header-integer-upper-end (lower (+ length 7)) (upper (proof-align-up length 8)))
           (:instance sequence-floor-unique (value (+ length 15)) (divisor 8)
                      (quotient (1+ (ceiling length 8)))))))
   :rule-classes nil))

(local
 (defthm sequence-string-word-after-constructor-initialization
   (let* ((first (proof-world-machine before))
          (stack (boymoo-model::a64-sp first))
          (address (proof-world-reg 0 before))
          (base (proof-heap-base before))
          (length (proof-load-word stack first))
          (bytes (sequence-small-string-allocation length))
          (path (sequence-small-string-finish-path length))
          (after (sequence-execute path before))
          (record (proof-object address :active :header 0)))
     (implies
      (and (proof-reserved-span-p :header address bytes before objects)
           (proof-heap-layout-p before)
           (consp (boymoo-model::a64-registers first))
           (unsigned-byte-p 18 length) (unsigned-byte-p 64 (+ stack 16)))
      (and (equal (mod address 8) 0)
           (sequence-initialized-string-p
            (proof-object-word record base) base address length (cons record objects)
            (proof-world-machine after)))))
   :hints
   (("Goal"
     :do-not-induct t
     :in-theory (e/d (sequence-initialized-string-p proof-object-word proof-span-p proof-subspan-p)
                     (proof-reserved-span-p proof-heap-layout-p proof-world-machine proof-world-reg
                      proof-world-regions proof-heap-base proof-load-word proof-covered-p
                      proof-pointer-address proof-word-tag boymoo-model::a64-unsigned
                      sequence-execute sequence-small-string-allocation sequence-small-string-finish-path))
     :use (sequence-small-string-initialized-storage
           (:instance sequence-publication-address-fields-are-natural (world before))
           (:instance sequence-reserved-header-in-mapped-heap (world before) (address (proof-world-reg 0 before))
                      (bytes (sequence-small-string-allocation
                              (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                               (proof-world-machine before)))))
           (:instance sequence-string-pointer-fields (address (proof-world-reg 0 before))
                      (base (proof-heap-base before)))
           (:instance sequence-small-string-write-extents (address (proof-world-reg 0 before))
                      (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                               (proof-world-machine before)))))))
   :rule-classes nil))

(defthm sequence-small-string-finishes-and-publishes
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 0 before))
         (length (proof-load-word stack machine))
         (bytes (sequence-small-string-allocation length))
         (path (sequence-small-string-finish-path length))
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (after (sequence-execute path before))
         (published (cons (proof-object address :active :header 0) objects)))
    (implies
     (and (proof-heap-p before objects packages)
          (proof-reserved-span-p :header address bytes before objects)
          (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 18 length)
          (unsigned-byte-p 64 (+ stack 16))
          (sequence-instruction-path path cuts before)
          (sequence-publication-preserves-storage-p before after objects packages))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-string-result-p length after published packages)
          (proof-preserved-heap-p nil before after objects published packages))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable proof-heap-p proof-heap-layout-p proof-reserved-span-p proof-world-machine proof-world-reg
                        proof-world-stop proof-world-regions proof-heap-base proof-load-word
                        proof-covered-p proof-string-result-p proof-preserved-heap-p proof-segment-p
                        sequence-initialized-string-p sequence-publication-preserves-storage-p
                        sequence-execute sequence-small-string-allocation sequence-small-string-finish-path
                        sequence-instruction-path proof-align-up)
    :use (sequence-small-string-finish-contract sequence-string-word-after-constructor-initialization
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-string-allocation-matches-object-size
                     (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before))))
          (:instance sequence-reserved-header-in-mapped-heap (world before) (address (proof-world-reg 0 before))
                     (bytes (sequence-small-string-allocation
                             (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before)))))
          (:instance sequence-publish-initialized-string-in-reservation
                     (after (sequence-execute
                             (sequence-small-string-finish-path
                              (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                               (proof-world-machine before)))
                             before))
                     (address (proof-world-reg 0 before))
                     (length (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                              (proof-world-machine before)))))))
  :rule-classes nil)
