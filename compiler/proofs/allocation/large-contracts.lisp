(in-package "BOYMOO-PROOFS")

(include-book "large-return")
(include-book "mapping")
(include-book "external-list")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-large-budget-sum-fits
  (implies (and (natp length) (< length *proof-space-size*)
                (proof-string-accounting-p headers world))
           (< (+ (proof-string-bytes-since-collection world) (allocation-large-mapping-size length))
              *allocation-word-modulus*))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-align-up-bounds
                         (size (+ 32 length)) (alignment *proof-runtime-page*)))
           :in-theory (disable proof-external-bytes proof-align-up proof-runtime-word mod))))

(defthm allocation-map-success-regions-well-formed
  (implies (and (proof-regions-p (proof-world-regions before))
                (posp size) (allocation-map-admissible-success-p mapping size before))
           (proof-regions-p (proof-world-regions (allocation-map-success-world mapping size before))))
  :hints (("Goal" :in-theory (disable allocation-map-success-world proof-region-disjoint-p mod))))

(local
 (defthm allocation-byte-character-list
   (and (character-listp (proof-byte-characters bytes))
        (equal (len (proof-byte-characters bytes)) (len bytes)))))

(local
 (defthm allocation-length-of-byte-list
   (implies (natp count)
            (equal (len (proof-byte-list count address machine)) count))
   :hints (("Goal" :induct (proof-byte-list count address machine)))))

(defthm allocation-length-of-loaded-string
  (implies (natp count)
           (and (stringp (proof-load-string count address machine))
                (equal (length (proof-load-string count address machine)) count)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-byte-characters proof-byte-list))))

(defthm allocation-region-member-covers-subspan
  (implies (and (member-equal (proof-region start end :rw) regions)
                (proof-subspan-p address count start end))
           (proof-covered-p address count :write regions))
  :rule-classes nil
  :hints (("Goal" :induct (proof-covered-p address count :write regions)
           :in-theory (disable proof-subspan-p))))

(defthm allocation-large-payload-in-mapping
  (implies (and (proof-span-p mapping size) (natp length)
                (< (+ 32 mapping) *allocation-word-modulus*)
                (<= (+ 32 length) size)
                (member-equal (proof-region mapping (+ mapping size) :rw) regions))
           (proof-covered-p (+ 32 mapping) length :write regions))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-region-member-covers-subspan
                         (start mapping) (end (+ mapping size)) (address (+ 32 mapping)) (count length)))
           :in-theory (disable proof-covered-p))))

(defthm allocation-large-result-after-publication
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base after))
         (header (+ mapping 24))
         (machine (proof-world-machine after))
         (object (proof-object header :external :header 0))
         (extent (+ 8 (proof-align-up length 8)))
         (published (cons object objects)))
    (implies (and (allocation-large-postmap-result-p before after)
                  (equal (mod mapping 8) 0) (equal (mod base 8) 0)
                  (proof-span-p mapping size) (<= (+ 32 length) size)
                  (< (+ 32 mapping) *allocation-word-modulus*)
                  (member-equal (proof-region mapping (+ mapping size) :rw) (proof-world-regions after))
                  (proof-span-p header extent)
                  (not (assoc-equal header objects))
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-object-disjoint-p header (+ header extent) objects machine))
             (and (proof-object-map-p published published nil base packages machine)
                  (proof-string-result-p length after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-publish-initialized-external-string
                   (address (+ 24 (proof-world-reg 0 before)))
                   (length (proof-world-reg 19 before)) (base (proof-heap-base after))
                   (machine (proof-world-machine after)))
                 (:instance allocation-tagged-offset-round-trip
                   (address (+ 24 (proof-world-reg 0 before))) (base (proof-heap-base after)) (tag 2))
                 (:instance allocation-aligned-eight-sum (first (proof-world-reg 0 before)) (second 24))
                 (:instance allocation-length-of-loaded-string
                   (count (proof-world-reg 19 before)) (address (+ 32 (proof-world-reg 0 before)))
                   (machine (proof-world-machine after)))
                 (:instance allocation-large-payload-in-mapping
                   (mapping (proof-world-reg 0 before)) (size (proof-world-reg 20 before))
                   (length (proof-world-reg 19 before)) (regions (proof-world-regions after))))
           :in-theory (e/d (allocation-load-word)
                           (proof-object-map-p proof-object-disjoint-p proof-view proof-pointer-address
                            proof-load-string proof-load-word proof-covered-p proof-align-up
                            proof-streams-preserved-p allocation-string-header boymoo-model::a64-unsigned
                            allocation-unsigned-64-of-difference mod)))))

(defthm allocation-large-mark-is-zero-on-cleared-mapping
  (let ((mapping (proof-world-reg 0 before))
        (size (proof-world-reg 20 before)))
    (implies (and (proof-span-p mapping size) (<= 24 size)
                  (equal (allocation-memory before) (proof-clear-memory mapping (+ mapping size) memory)))
             (equal (allocation-load-word (+ mapping 16) before) 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-read-within-cleared-span
                  (address (+ 16 (proof-world-reg 0 before))) (bytes 8)
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))))
           :in-theory (e/d (allocation-load-word proof-load-word)
                           (proof-clear-memory boymoo-model::a64-read-bytes)))))

(defthm allocation-large-initialized-payload-stays-zero
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (end (+ mapping size)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (equal (allocation-memory before) (proof-clear-memory mapping end memory))
                  (unsigned-byte-p 64 address) (<= (+ mapping 32) address) (< address end))
             (equal (boymoo-model::a64-byte address (allocation-memory after)) 0)))
  :rule-classes nil
  :hints (("Goal" :use allocation-large-postmap-preserves-payload
           :in-theory (disable allocation-large-mapped-entry-p allocation-large-insertion-p allocation-large-header-p
                               boymoo-model::a64-byte proof-clear-memory))))

(defthm allocation-large-publishes-external-list
  (let* ((head (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (length (proof-world-reg 19 before))
         (end (+ head size))
         (machine-start (- (proof-machine-limit after) *proof-machine-margin*))
         (old-list (proof-external-objects (proof-external-head before) (len objects) after objects))
         (published (cons (proof-object (+ head 24) :external :header 0) objects)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (allocation-large-postmap-result-p before after)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (equal size (allocation-large-mapping-size length))
                  (not (assoc-equal (+ head 24) objects))
                  (equal (allocation-load-word (+ head 16) before) 0)
                  (proof-disjoint-p head end (- (proof-heap-base after) *proof-heap-prefix*) (proof-spaces-end after))
                  (proof-disjoint-p head end (proof-stack-base after) (proof-stack-end after))
                  (proof-disjoint-p head end machine-start (+ machine-start *proof-machine-reservation*))
                  (member-equal (proof-region head end :rw) (proof-world-regions after))
                  old-list)
             (equal (proof-external-objects (proof-external-head after) (len published) after published)
                    (list* :mappings (+ head 24) (cdr old-list)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialization-preserves-bookkeeping
                 (:instance allocation-external-list-with-new-head (head (proof-world-reg 0 before)) (world after))
                 (:instance allocation-string-header-fields (length (proof-world-reg 19 before))))
           :in-theory (e/d (allocation-load-word)
                           (proof-load-word proof-external-objects proof-external-head proof-disjoint-p
                            proof-world-machine proof-heap-base proof-machine-limit proof-spaces-end
                            proof-stack-base proof-stack-end proof-align-up proof-string-bytes-since-collection
                            proof-string-budget proof-streams-preserved-p proof-object-word
                            allocation-large-insertion-p allocation-large-header-p
                            allocation-string-header proof-header-type proof-header-size)))))
