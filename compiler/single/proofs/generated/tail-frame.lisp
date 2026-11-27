(in-package "BOYMOO-PROOFS")

(include-book "stack-write")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-compiled-entry-p proof-compiled-return-p
                    proof-world-machine proof-world-reg proof-world-stop proof-world-pc proof-world-regions
                    proof-world-page-size proof-stack-top proof-stack-base proof-stack-limit proof-stack-end
                    proof-machine-limit proof-heap-base proof-heap-limit proof-box-top proof-stack-views
                    proof-stack-prefix proof-prefix-preserved-p proof-object-disjoint-p proof-object-map-p
                    proof-segment-p proof-span-p proof-subspan-p proof-disjoint-p proof-instruction-effect
                    generated-stack-views-are-word-views generated-address-path generated-indexed-copy-path
                    generated-indexed-tail-path generated-indexed-tail-prefix generated-path-p generated-path-after
                    generated-copy-words generated-read-words generated-word-views generated-sp generated-load-word
                    boymoo-model::a64-unsigned expt mod))

(local
 (defthm generated-stack-pointer-update-preserves-page-size
   (equal (proof-world-page-size (generated-set-sp sp world)) (proof-world-page-size world))
   :hints (("Goal" :in-theory (enable generated-set-sp)))))

(local
 (defthm generated-copy-preserves-page-size
   (equal (proof-world-page-size (generated-copy-words count source destination world))
          (proof-world-page-size world))
   :hints (("Goal" :induct (generated-copy-words count source destination world)
                   :in-theory (enable generated-copy-words)))))

(local
 (defthm generated-address-path-keeps-untouched-controls
   (let ((after (generated-path-after (generated-address-path rd rn bytes subtract) before)))
     (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31) (unsigned-byte-p 64 bytes)
                   (generated-ordinary-machine-p before))
              (and (implies (and (not (equal rd other)) (not (equal other 17)))
                            (equal (proof-world-reg other after) (proof-world-reg other before)))
                   (equal (proof-world-regions after) (proof-world-regions before))
                   (equal (proof-world-page-size after) (proof-world-page-size before))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (generated-ordinary-machine-p after) (generated-ordinary-machine-p before)))))
   :hints (("Goal" :in-theory (enable generated-address-path generated-path-after)))))

(local
 (defthm generated-indexed-copy-keeps-untouched-controls
   (let ((after (generated-path-after (generated-indexed-copy-path arity 0) before)))
     (implies (and (natp arity) (unsigned-byte-p 64 (* 8 arity))
                   (generated-ordinary-machine-p before))
              (and (implies (not (member-equal register '(9 17)))
                            (equal (proof-world-reg register after) (proof-world-reg register before)))
                   (generated-ordinary-machine-p after)
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (proof-world-regions after) (proof-world-regions before))
                   (equal (proof-world-page-size after) (proof-world-page-size before)))))
   :hints (("Goal" :use (:instance generated-indexed-copy-path-observations (count arity) (offset 0))
                   :in-theory (e/d (generated-heap-world-equiv)
                                   (generated-indexed-copy-path-observations))))))

(defthm generated-tail-transfer-keeps-untouched-controls
  (let* ((path (generated-indexed-tail-path arity target before))
         (after (generated-path-after path before)))
    (implies (and (natp arity) (unsigned-byte-p 64 (* 8 arity))
                  (generated-ordinary-machine-p before))
             (and (implies (not (member-equal register '(9 10 17 19 25 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register before)))
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (equal (proof-world-regions after) (proof-world-regions before))
                  (equal (proof-world-page-size after) (proof-world-page-size before))
                  (generated-ordinary-machine-p after))))
  :hints (("Goal"
           :in-theory (e/d (generated-indexed-tail-path generated-indexed-tail-prefix generated-path-after)
                           (generated-indexed-copy-path-observations generated-address-path-observations)))))

(local
 (defthm generated-runtime-stack-reservations-are-disjoint
   (implies (proof-heap-layout-p world)
            (proof-disjoint-p (proof-stack-base world) (proof-stack-end world)
                              (generated-machine-stack-base world) (generated-machine-stack-end world)))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p generated-machine-stack-base generated-machine-stack-end)))
   :rule-classes nil))

(local
 (defthm generated-tail-copy-fits-stack
   (let* ((frame (proof-world-reg 19 before)) (sp (generated-sp before))
          (start (proof-stack-base before)) (top (proof-stack-top before))
          (bytes (* 8 arity)) (new-top (+ frame bytes)))
     (implies (and (proof-heap-layout-p before) (natp arity) (<= start frame) (<= new-top top)
                   (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before)))
              (and (unsigned-byte-p 64 bytes)
                   (generated-runtime-stack-span-p frame new-top before)
                   (generated-word-block-span-p frame arity)
                   (proof-disjoint-p frame new-top sp (+ sp 16))
                   (<= new-top (proof-stack-limit before)))))
   :hints (("Goal"
            :use ((:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-runtime-stack-reservations-are-disjoint (world before)))
            :in-theory (enable generated-runtime-stack-span-p proof-subspan-p proof-disjoint-p proof-span-p proof-stack-top)))
   :rule-classes nil))

(local
 (defthm generated-tail-pop-keeps-machine-stack-alignment
   (implies (integerp sp) (equal (mod (+ 16 sp) 16) (mod sp 16)))
   :hints (("Goal" :use (:instance generated-floor-add-multiple (x sp) (divisor 16) (q 1))
                   :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm generated-tail-frame-span-fits-popped-stack
   (let ((sp (generated-sp before))
         (lower (generated-machine-stack-base before)) (upper (generated-machine-stack-end before)))
     (implies (and (proof-heap-layout-p before) (proof-subspan-p sp 16 lower upper))
              (and (<= lower (+ sp 16)) (<= (+ sp 16) upper) (equal (mod (+ sp 16) 16) 0))))
   :hints (("Goal"
            :use ((:instance generated-heap-layout-machine-stack-bounds (world before))
                  (:instance generated-tail-pop-keeps-machine-stack-alignment (sp (generated-sp before))))
            :in-theory (enable proof-subspan-p)))
   :rule-classes nil))

(local
 (defthm generated-tail-path-length
   (equal (len (generated-indexed-tail-path arity target before))
          (+ 2 (len (generated-indexed-tail-prefix arity))))
   :hints (("Goal" :in-theory (enable generated-indexed-tail-path)))))

(local
 (defthm generated-tail-is-stack-update
   (let* ((frame (proof-world-reg 19 before)) (sp (generated-sp before))
          (bytes (* 8 arity)) (source (- (proof-stack-top before) bytes))
          (new-top (+ frame bytes))
          (path (generated-indexed-tail-path arity target before))
          (after (generated-path-after path before)))
     (implies (and (proof-heap-layout-p before) (natp arity) (natp keep)
                   (equal frame (+ (proof-stack-base before) (* 8 keep))) (<= frame source)
                   (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                   (< (+ sp 16) (expt 2 64)) (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                   (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                   (generated-path-p path (list target) before))
              (and (generated-stack-update-p frame new-top before after)
                   (proof-segment-p (len path) (list target) before :cut after)
                   (equal (proof-world-pc after) target)
                   (equal (proof-stack-top after) new-top)
                   (equal (proof-world-reg 19 after) (generated-load-word sp before))
                   (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                   (equal (generated-sp after) (+ sp 16)))))
   :hints (("Goal"
            :use (generated-tail-copy-fits-stack generated-indexed-tail-call-transfer
                  generated-indexed-tail-observes-copied-memory generated-tail-frame-span-fits-popped-stack
                  (:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-add-slots-keeps-stack-alignment
                             (base (proof-stack-base before)) (count (+ keep arity)))
                  (:instance generated-word-copy-writes-only-inside-span
                             (count arity) (world before)
                             (start (proof-world-reg 19 before)) (destination (proof-world-reg 19 before))
                             (end (+ (proof-world-reg 19 before) (* 8 arity)))
                             (source (- (proof-stack-top before) (* 8 arity)))))
            :in-theory (e/d (generated-stack-update-p proof-stack-top proof-stack-limit proof-machine-limit
                                               proof-box-top proof-heap-limit proof-heap-base)
                            (generated-word-copy-writes-only-inside-span generated-word-block-span-p
                             generated-cut-is-segment))))
   :rule-classes nil))

(local
 (defthm generated-relocated-arguments-keep-source-views
   (let* ((arity (len args)) (bytes (* 8 arity))
          (frame (proof-world-reg 19 before))
          (source (- (proof-stack-top before) bytes))
          (path (generated-indexed-tail-path arity target before))
          (after (generated-path-after path before)))
     (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                   (unsigned-byte-p 64 bytes) (<= frame source)
                   (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                   (< (+ (generated-sp before) 16) (expt 2 64))
                   (proof-disjoint-p frame (+ frame bytes) (generated-sp before) (+ (generated-sp before) 16))
                   (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                   (generated-path-p path (list target) before)
                   (not (proof-world-stop before))
                   (proof-object-disjoint-p frame (+ frame bytes) objects (proof-world-machine before)))
              (equal (proof-stack-views arity frame (proof-heap-base after) objects packages (proof-world-machine after))
                     (cons :slots (proof-argument-views args)))))
   :hints (("Goal"
            :use ((:instance generated-indexed-tail-preserves-published-word-views
                             (arity (len args))
                             (words (generated-read-words (len args) (- (proof-stack-top before) (* 8 (len args))) before)))
                  (:instance generated-indexed-tail-call-transfer (arity (len args)))
                  (:instance generated-heap-has-layout-and-roots (world before)))
            :in-theory (e/d (proof-compiled-entry-p proof-stack-top generated-stack-views-are-word-views)
                            (generated-indexed-tail-preserves-published-word-views))))
   :rule-classes nil))

(defthm generated-indexed-tail-establishes-entry-and-preserves-heap
  (let* ((arity (len args)) (bytes (* 8 arity))
         (frame (proof-world-reg 19 before)) (sp (generated-sp before))
         (path (generated-indexed-tail-path arity target before))
         (after (generated-path-after path before)))
    (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (natp keep) (equal frame (+ (proof-stack-base before) (* 8 keep)))
                  (<= (+ frame bytes) (proof-stack-top before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                  (< (+ sp 16) (expt 2 64)) (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (generated-path-p path (list target) before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (proof-compiled-entry-p target args after objects packages)
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-stack-top after) (+ frame bytes))
                  (proof-prefix-preserved-p frame before after objects objects packages)
                  (equal (proof-world-reg 19 after) (generated-load-word sp before))
                  (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                  (equal (generated-sp after) (+ sp 16)))))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-layout-value-stack-bounds (world before))
                 (:instance generated-tail-copy-fits-stack (arity (len args)))
                 (:instance generated-tail-is-stack-update (arity (len args)))
                 generated-relocated-arguments-keep-source-views
                 (:instance generated-stack-update-preserves-runtime-fields
                            (start (proof-world-reg 19 before)) (end (+ (proof-world-reg 19 before) (* 8 (len args))))
                            (after (generated-path-after (generated-indexed-tail-path (len args) target before) before)))
                 (:instance generated-stack-update-is-disjoint-from-published-objects
                            (start (proof-world-reg 19 before)) (end (+ (proof-world-reg 19 before) (* 8 (len args))))
                            (after (generated-path-after (generated-indexed-tail-path (len args) target before) before)))
                 (:instance generated-stack-update-preserves-untouched-prefix
                            (start (proof-world-reg 19 before)) (end (+ (proof-world-reg 19 before) (* 8 (len args))))
                            (after (generated-path-after (generated-indexed-tail-path (len args) target before) before)))
                 (:instance generated-stack-prefix-with-argument-suffix
                            (after (generated-path-after (generated-indexed-tail-path (len args) target before) before)))
                 (:instance generated-stack-update-preserves-heap-with-valid-roots
                            (start (proof-world-reg 19 before)) (end (+ (proof-world-reg 19 before) (* 8 (len args))))
                            (after (generated-path-after (generated-indexed-tail-path (len args) target before) before))))
           :in-theory (e/d (proof-compiled-entry-p proof-prefix-preserved-p proof-disjoint-p)
                           (generated-tail-transfer-keeps-untouched-controls))))
  :rule-classes nil)
