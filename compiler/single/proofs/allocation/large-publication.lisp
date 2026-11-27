(in-package "BOYMOO-PROOFS")

(include-book "large-flow")
(include-book "word-writes")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-large-initialization-writes (world)
  (let* ((mapping (proof-world-reg 0 world))
         (size (proof-world-reg 20 world))
         (metadata (proof-world-reg 21 world)))
    (list (cons (+ metadata 72) (+ (allocation-load-word (+ metadata 72) world) size))
          (cons mapping (allocation-load-word (+ metadata 56) world))
          (cons (+ mapping 8) size)
          (cons (+ metadata 56) mapping)
          (cons (+ mapping 24) (allocation-string-header (proof-world-reg 19 world))))))

(defthm allocation-large-initialization-write-footprint
  (implies (and (allocation-large-mapped-entry-p origin before)
                (allocation-large-insertion-p before inserted)
                (allocation-large-header-p inserted initialized))
           (equal (allocation-memory initialized)
                  (allocation-memory (allocation-write-words (allocation-large-initialization-writes before) before))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable allocation-code-origin-p allocation-large-string-address
                               allocation-string-header proof-object-word proof-streams-preserved-p
                               boymoo-model::a64-write-bytes))))

(defthm allocation-large-extents-within-request
  (let* ((header (+ 24 mapping))
         (extent (+ 8 (proof-align-up length 8))))
    (implies (and (natp length)
                  (equal size (allocation-large-mapping-size length))
                  (proof-span-p mapping size)
                  (< (+ mapping 32) *allocation-word-modulus*))
             (and (<= (+ 32 length) size)
                  (proof-span-p header extent)
                  (<= (+ header extent) (+ mapping size))
                  (<= (+ header 16) (+ mapping size)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-external-record-fits-mapping
                 (:instance allocation-align-up-bounds (size (+ 32 length)) (alignment *proof-runtime-page*))
                 (:instance allocation-align-up-bounds (size length) (alignment 8)))
           :in-theory (disable proof-align-up mod))))

(defthm allocation-large-initialization-writes-outside-objects
  (let* ((mapping (proof-world-reg 0 before))
         (end (+ mapping (proof-world-reg 20 before)))
         (base (proof-heap-base before))
         (machine (proof-world-machine before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-objects-outside-write-p mapping end objects machine)
                  (allocation-objects-outside-write-p (- base 128) base objects machine))
             (allocation-word-writes-outside-objects-p (allocation-large-initialization-writes before) objects machine)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-objects-outside-subspan
                  (start (- (proof-heap-base before) 128)) (end (proof-heap-base before))
                  (lower (+ 72 (proof-world-reg 21 before))) (upper (+ 80 (proof-world-reg 21 before)))
                  (machine (proof-world-machine before)))
                 (:instance allocation-objects-outside-subspan
                  (start (- (proof-heap-base before) 128)) (end (proof-heap-base before))
                  (lower (+ 56 (proof-world-reg 21 before))) (upper (+ 64 (proof-world-reg 21 before)))
                  (machine (proof-world-machine before)))
                 (:instance allocation-objects-outside-subspan
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower (proof-world-reg 0 before)) (upper (+ (proof-world-reg 0 before) 8))
                  (machine (proof-world-machine before)))
                 (:instance allocation-objects-outside-subspan
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower (+ (proof-world-reg 0 before) 8)) (upper (+ (proof-world-reg 0 before) 16))
                  (machine (proof-world-machine before)))
                 (:instance allocation-objects-outside-subspan
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower (+ (proof-world-reg 0 before) 24)) (upper (+ (proof-world-reg 0 before) 32))
                  (machine (proof-world-machine before))))
           :in-theory (disable allocation-objects-outside-write-p allocation-string-header
                               allocation-code-origin-p allocation-large-string-address))))

(defthm allocation-large-write-preserves-published-objects
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (writes (allocation-large-initialization-writes before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (equal (proof-heap-base after) base)
                  (allocation-word-writes-outside-objects-p writes objects machine)
                  (proof-object-map-p objects objects nil base packages machine))
             (and (proof-object-map-p objects objects nil base packages (proof-world-machine after))
                  (equal (proof-object-disjoint-p lower upper objects (proof-world-machine after))
                         (proof-object-disjoint-p lower upper objects machine))
                  (equal (proof-view word base objects packages (proof-world-machine after))
                         (proof-view word base objects packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialization-write-footprint
                 (:instance allocation-word-writes-keep-published-map
                  (writes (allocation-large-initialization-writes before)) (world before) (base (proof-heap-base before)))
                 (:instance allocation-word-writes-keep-views
                  (writes (allocation-large-initialization-writes before)) (world before) (base (proof-heap-base before)))
                 (:instance allocation-word-writes-keep-inspected-span-disjoint
                  (writes (allocation-large-initialization-writes before)) (world before))
                 (:instance allocation-equal-memory-is-model-equivalence
                  (first after) (last (allocation-write-words (allocation-large-initialization-writes before) before))))
           :in-theory (disable allocation-large-initialization-writes allocation-large-mapped-entry-p
                               allocation-large-insertion-p allocation-large-header-p allocation-write-words
                               allocation-equal-memory-is-model-equivalence
                               allocation-word-writes-outside-objects-p proof-object-map-p proof-object-disjoint-p
                               proof-view proof-heap-base))))

(local
 (defthm allocation-large-publication-entry-facts
   (let ((mapping (proof-world-reg 0 before)))
     (implies (and (allocation-large-mapped-entry-p origin before)
                   (allocation-large-postmap-result-p before after))
              (and (proof-span-p mapping (proof-world-reg 20 before))
                   (< (+ mapping 32) *allocation-word-modulus*)
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (equal (proof-world-regions after) (proof-world-regions before)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable allocation-code-origin-p allocation-large-string-address
                                      proof-span-p proof-heap-base proof-object-word allocation-string-header
                                      proof-streams-preserved-p)))))

(defthm allocation-large-initialization-and-publication
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before))
         (header (+ mapping 24))
         (machine (proof-world-machine before))
         (published (cons (proof-object header :external :header 0) objects)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (allocation-large-postmap-result-p before after)
                  (equal size (allocation-large-mapping-size length))
                  (equal (mod mapping 8) 0) (equal (mod base 8) 0)
                  (member-equal (proof-region mapping (+ mapping size) :rw) (proof-world-regions before))
                  (proof-object-map-p objects objects nil base packages machine)
                  (allocation-objects-outside-write-p mapping (+ mapping size) objects machine)
                  (allocation-objects-outside-write-p (- base 128) base objects machine))
             (and (proof-object-map-p published published nil base packages (proof-world-machine after))
                  (proof-string-result-p length after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-publication-entry-facts allocation-large-initialization-writes-outside-objects
                 allocation-large-result-after-publication
                 (:instance allocation-large-extents-within-request
                  (mapping (proof-world-reg 0 before)) (length (proof-world-reg 19 before)) (size (proof-world-reg 20 before)))
                 (:instance allocation-large-write-preserves-published-objects
                  (lower (+ 24 (proof-world-reg 0 before)))
                  (upper (+ 32 (proof-world-reg 0 before) (proof-align-up (proof-world-reg 19 before) 8))) (word 0))
                 (:instance allocation-objects-outside-subspan
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower (+ 24 (proof-world-reg 0 before)))
                  (upper (+ 32 (proof-world-reg 0 before) (proof-align-up (proof-world-reg 19 before) 8)))
                  (machine (proof-world-machine before)))
                 (:instance allocation-objects-outside-subspan
                  (start (proof-world-reg 0 before)) (end (+ (proof-world-reg 0 before) (proof-world-reg 20 before)))
                  (lower (+ 24 (proof-world-reg 0 before))) (upper (+ 40 (proof-world-reg 0 before)))
                  (machine (proof-world-machine before)))
                 (:instance allocation-cell-span-excludes-existing-address
                  (address (+ 24 (proof-world-reg 0 before))) (machine (proof-world-machine before))))
           :in-theory (disable allocation-large-initialization-writes allocation-large-insertion-p allocation-large-header-p
                               allocation-large-mapped-entry-p allocation-large-postmap-result-p
                               proof-span-p proof-heap-base
                               allocation-word-writes-outside-objects-p allocation-objects-outside-write-p
                               proof-object-map-p proof-object-disjoint-p proof-string-result-p
                               proof-load-word allocation-string-header proof-object-word
                               proof-align-up proof-streams-preserved-p allocation-large-mapping-size mod))))

(defthm allocation-large-postmap-restore-keeps-initialization
  (implies (and (allocation-large-mapped-entry-p origin before)
                (allocation-large-insertion-p before inserted)
                (allocation-large-header-p inserted initialized)
                (allocation-machine-state-p initialized)
                (not (proof-world-stop initialized))
                (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
           (equal (allocation-memory after) (allocation-memory initialized)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-large-restore-machine-return (before initialized)))
           :in-theory (disable allocation-path-end allocation-code-origin-p allocation-large-string-address
                               allocation-large-insertion-memory allocation-string-header proof-object-word
                               proof-streams-preserved-p))))

(defthm allocation-large-checked-initialization-and-publication
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before))
         (machine (proof-world-machine before))
         (path (allocation-large-postmap-path))
         (cuts (list (allocation-load-word (+ (allocation-sp before) 8) before)))
         (published (cons (proof-object (+ mapping 24) :external :header 0) objects)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized))
                  (equal size (allocation-large-mapping-size length))
                  (equal (mod mapping 8) 0) (equal (mod base 8) 0)
                  (member-equal (proof-region mapping (+ mapping size) :rw) (proof-world-regions before))
                  (proof-object-map-p objects objects nil base packages machine)
                  (allocation-objects-outside-write-p mapping (+ mapping size) objects machine)
                  (allocation-objects-outside-write-p (- base 128) base objects machine)
                  (allocation-path-ready-p path cuts before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (proof-object-map-p published published nil base packages (proof-world-machine after))
                  (proof-string-result-p length after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialized-machine-stages allocation-large-postmap-restore-keeps-initialization
                 allocation-large-postmap-checked-return allocation-large-initialization-and-publication)
           :in-theory (disable allocation-large-mapped-entry-p allocation-large-insertion-p allocation-large-header-p
                               allocation-path-end allocation-path-ready-p proof-segment-p allocation-large-postmap-result-p
                               proof-object-map-p allocation-objects-outside-write-p proof-heap-base
                               proof-string-result-p allocation-large-mapping-size mod))))
