(in-package "BOYMOO-PROOFS")

(include-book "large-strings")
(include-book "segments")
(include-book "publication")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-load-word-from-memory
   (equal (allocation-load-word address world)
          (boymoo-model::a64-read-bytes 8 address (allocation-memory world)))
   :hints (("Goal" :in-theory (enable allocation-load-word proof-load-word)))))

(defthm allocation-large-insertion-preserves-disjoint-word
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before)))
    (implies (and (allocation-large-insertion-p before after)
                  (<= 32 size) (proof-span-p mapping size)
                  (<= 128 base) (equal (proof-world-reg 21 before) (- base 128))
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ 8 address) mapping (+ mapping size))
                  (proof-disjoint-p address (+ 8 address) (- base 128) base))
             (equal (allocation-load-word address after) (allocation-load-word address before))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-streams-preserved-p proof-runtime-word))))

(defthm allocation-large-header-preserves-disjoint-word
  (let ((header (+ (proof-world-reg 0 before) 24)))
    (implies (and (allocation-large-header-p before after)
                  (proof-span-p header 8) (proof-span-p address 8)
                  (proof-disjoint-p address (+ 8 address) header (+ 8 header)))
             (equal (allocation-load-word address after) (allocation-load-word address before))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-streams-preserved-p proof-object-word
                                     allocation-string-header))))

(defthm allocation-large-insertion-preserves-payload-byte
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before)))
    (implies (and (allocation-large-insertion-p before after)
                  (<= 32 size) (proof-span-p mapping size)
                  (<= 128 base) (equal (proof-world-reg 21 before) (- base 128))
                  (proof-disjoint-p mapping (+ mapping size) (- base 128) base)
                  (unsigned-byte-p 64 address) (<= (+ mapping 32) address) (< address (+ mapping size)))
             (equal (boymoo-model::a64-byte address (allocation-memory after))
                    (boymoo-model::a64-byte address (allocation-memory before)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-streams-preserved-p boymoo-model::a64-byte))))

(defthm allocation-large-header-preserves-payload-byte
  (let ((header (+ (proof-world-reg 0 before) 24)))
    (implies (and (allocation-large-header-p before after)
                  (proof-span-p header 8) (unsigned-byte-p 64 address) (<= (+ 8 header) address))
             (equal (boymoo-model::a64-byte address (allocation-memory after))
                    (boymoo-model::a64-byte address (allocation-memory before)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-streams-preserved-p proof-object-word
                                     allocation-string-header boymoo-model::a64-byte))))

(defun allocation-large-postmap-path ()
  (append *allocation-large-insertion-path* *allocation-large-header-path* *allocation-large-restore-path*))

(defun allocation-large-mapped-entry-p (origin before)
  (let ((mapping (proof-world-reg 0 before))
        (size (proof-world-reg 20 before))
        (length (proof-world-reg 19 before))
        (base (proof-heap-base before))
        (save (allocation-sp before)))
    (and (allocation-code-origin-p origin)
         (allocation-machine-state-p before)
         (not (proof-world-stop before))
         (equal (proof-world-pc before) (allocation-large-string-address origin 21))
         (posp mapping) (<= 32 size) (proof-span-p mapping size)
         (< (+ mapping 32) *allocation-word-modulus*)
         (< length *proof-space-size*)
         (<= 128 base) (equal (proof-world-reg 21 before) (- base 128))
         (< (+ (proof-string-bytes-since-collection before) size) *allocation-word-modulus*)
         (natp save) (< (+ save 32) *allocation-word-modulus*)
         (proof-disjoint-p mapping (+ mapping size) (- base 128) base)
         (proof-disjoint-p save (+ save 32) mapping (+ mapping size))
         (proof-disjoint-p save (+ save 32) (- base 128) base))))

(defun allocation-large-postmap-result-p (before after)
  (let* ((mapping (proof-world-reg 0 before))
         (length (proof-world-reg 19 before))
         (save (allocation-sp before)))
    (and (not (proof-world-stop after))
         (equal (proof-world-pc after) (allocation-load-word (+ save 8) before))
         (equal (allocation-sp after) (+ save 32))
         (equal (proof-world-reg 30 after) (allocation-load-word (+ save 8) before))
         (equal (proof-world-reg 21 after) (allocation-load-word save before))
         (equal (proof-world-reg 19 after) (allocation-load-word (+ save 16) before))
         (equal (proof-world-reg 20 after) (allocation-load-word (+ save 24) before))
         (equal (proof-world-reg 0 after)
                (proof-object-word (proof-object (+ mapping 24) :external :header 0) (proof-heap-base before)))
         (equal (proof-world-reg 1 after) (+ mapping 32))
         (equal (proof-world-reg 2 after) length)
         (equal (proof-heap-base after) (proof-heap-base before))
         (equal (allocation-load-word (+ mapping 24) after) (allocation-string-header length))
         (equal (proof-world-regions after) (proof-world-regions before))
         (equal (proof-world-replies after) (proof-world-replies before))
         (proof-streams-preserved-p before after))))

(defthm allocation-large-initialization-preserves-save-word
  (let ((address (+ offset (allocation-sp before))))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (member-equal offset '(0 8 16 24)))
             (equal (allocation-load-word address initialized) (allocation-load-word address before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-insertion-preserves-disjoint-word
                  (after inserted) (address (+ offset (allocation-sp before))))
                 (:instance allocation-large-header-preserves-disjoint-word
                  (before inserted) (after initialized) (address (+ offset (allocation-sp before)))))
           :in-theory (disable allocation-load-word-from-memory proof-world-pc
                               allocation-code-origin-p allocation-large-string-address
                               allocation-large-insertion-memory proof-streams-preserved-p
                               proof-object-word allocation-string-header))))

(defthm allocation-large-initialized-machine-stages
  (implies (and (allocation-large-mapped-entry-p origin before)
                (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                (equal initialized (allocation-path-end *allocation-large-header-path* inserted)))
           (and (allocation-large-insertion-p before inserted)
                (allocation-large-header-p inserted initialized)
                (allocation-machine-state-p initialized)
                (not (proof-world-stop initialized))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-insert-mapping-machine-edge (after inserted))
                 (:instance allocation-large-header-machine-edge (before inserted) (after initialized)))
           :in-theory (disable allocation-path-end allocation-load-word-from-memory
                               allocation-code-origin-p allocation-large-string-address
                               allocation-large-insertion-memory proof-streams-preserved-p
                               proof-object-word allocation-string-header))))

(defthm allocation-large-postmap-finish
  (implies (and (allocation-large-mapped-entry-p origin before)
                (allocation-large-insertion-p before inserted)
                (allocation-large-header-p inserted initialized)
                (allocation-machine-state-p initialized)
                (not (proof-world-stop initialized))
                (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
           (allocation-large-postmap-result-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-restore-machine-return (before initialized))
                 (:instance allocation-large-initialization-preserves-save-word (offset 0))
                 (:instance allocation-large-initialization-preserves-save-word (offset 8))
                 (:instance allocation-large-initialization-preserves-save-word (offset 16))
                 (:instance allocation-large-initialization-preserves-save-word (offset 24)))
           :in-theory (disable allocation-path-end allocation-code-origin-p allocation-large-string-address
                               allocation-large-insertion-memory proof-object-word allocation-string-header))))

(defthm allocation-large-postmap-checked-return
  (let* ((cuts (list (allocation-load-word (+ (allocation-sp before) 8) before)))
         (path (allocation-large-postmap-path)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* before))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized))
                  (allocation-path-ready-p path cuts before))
             (and (allocation-large-postmap-result-p before after)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-initialized-machine-stages allocation-large-postmap-finish
                 (:instance allocation-path-end-of-append
                  (first *allocation-large-insertion-path*)
                  (last (append *allocation-large-header-path* *allocation-large-restore-path*))
                  (world before))
                 (:instance allocation-path-end-of-append
                  (first *allocation-large-header-path*) (last *allocation-large-restore-path*)
                  (world inserted))
                 (:instance allocation-checked-cut
                  (instructions (allocation-large-postmap-path)) (world before)
                  (cuts (list (allocation-load-word (+ (allocation-sp before) 8) before)))))
           :in-theory (disable allocation-large-mapped-entry-p allocation-path-ready-p
                               allocation-large-insertion-p allocation-large-header-p
                               allocation-checked-cut allocation-path-end allocation-path-end-of-append proof-segment-p
                               allocation-load-word-from-memory proof-object-word
                               allocation-string-header proof-streams-preserved-p))))

(defthm allocation-large-postmap-preserves-payload
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (unsigned-byte-p 64 address) (<= (+ mapping 32) address) (< address (+ mapping size)))
             (equal (boymoo-model::a64-byte address (allocation-memory after))
                    (boymoo-model::a64-byte address (allocation-memory before)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-insertion-preserves-payload-byte (after inserted))
                 (:instance allocation-large-header-preserves-payload-byte (before inserted) (after initialized)))
           :in-theory (disable allocation-code-origin-p allocation-large-string-address
                               allocation-large-insertion-memory proof-streams-preserved-p
                               proof-object-word allocation-string-header boymoo-model::a64-byte))))

(defthm allocation-large-header-keeps-mapping-bookkeeping-word
  (let* ((mapping (proof-world-reg 0 before))
         (base (proof-heap-base before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (member-equal address
                                (list mapping (+ mapping 8) (+ mapping 16)
                                      (- base 72) (- base 56) (- base 48))))
             (equal (allocation-load-word address initialized) (allocation-load-word address inserted))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-header-preserves-disjoint-word (before inserted) (after initialized)))
           :in-theory (disable allocation-load-word-from-memory allocation-code-origin-p
                               allocation-large-string-address allocation-large-insertion-memory
                               proof-streams-preserved-p proof-object-word allocation-string-header))))

(defthm allocation-large-initialization-preserves-bookkeeping
  (let* ((mapping (proof-world-reg 0 before))
         (size (proof-world-reg 20 before))
         (base (proof-heap-base before)))
    (implies (and (allocation-large-mapped-entry-p origin before)
                  (allocation-large-insertion-p before inserted)
                  (allocation-large-header-p inserted initialized)
                  (equal (allocation-memory after) (allocation-memory initialized))
                  (equal (proof-heap-base after) base))
             (and (equal (proof-external-head after) mapping)
                  (equal (proof-string-bytes-since-collection after)
                         (+ (proof-string-bytes-since-collection before) size))
                  (equal (proof-string-budget after) (proof-string-budget before))
                  (equal (allocation-load-word mapping after) (proof-external-head before))
                  (equal (allocation-load-word (+ mapping 8) after) size)
                  (equal (allocation-load-word (+ mapping 16) after)
                         (allocation-load-word (+ mapping 16) before)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-header-keeps-mapping-bookkeeping-word (address (proof-world-reg 0 before)))
                 (:instance allocation-large-header-keeps-mapping-bookkeeping-word (address (+ 8 (proof-world-reg 0 before))))
                 (:instance allocation-large-header-keeps-mapping-bookkeeping-word (address (+ 16 (proof-world-reg 0 before))))
                 (:instance allocation-large-header-keeps-mapping-bookkeeping-word (address (- (proof-heap-base before) 72)))
                 (:instance allocation-large-header-keeps-mapping-bookkeeping-word (address (- (proof-heap-base before) 56)))
                 (:instance allocation-large-header-keeps-mapping-bookkeeping-word (address (- (proof-heap-base before) 48))))
           :in-theory (disable allocation-large-mapped-entry-p allocation-large-insertion-memory
                               allocation-large-header-p proof-streams-preserved-p))))
