(in-package "BOYMOO-PROOFS")

(include-book "root-transfer")
(include-book "published-writes")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine proof-world-pc proof-world-reg proof-world-stop
                    proof-instruction-effect proof-segment-p proof-view proof-heap-p proof-heap-base
                    proof-load-word generated-load-word generated-store-word generated-copy-words
                    generated-indexed-tail-prefix generated-indexed-tail-path generated-address-path
                    generated-indexed-copy-path generated-wide-word-items generated-move-instructions
                    boymoo-model::a64-unsigned expt))

(local
 (defthm generated-loads-agree-when-memory-agrees
   (implies (generated-memory-equiv (proof-world-machine first) (proof-world-machine second))
            (equal (generated-load-word address first) (generated-load-word address second)))
   :hints (("Goal" :in-theory (enable generated-load-word)))
   :rule-classes nil))

(local
 (defthm generated-equal-stores-preserve-memory-agreement
   (implies (generated-memory-equiv (proof-world-machine first) (proof-world-machine second))
            (generated-memory-equiv (proof-world-machine (generated-store-word address word first))
                                     (proof-world-machine (generated-store-word address word second))))
   :hints (("Goal" :in-theory (enable generated-memory-equiv generated-store-word
                                     boymoo-model::a64-store boymoo-model::a64-memory)))))

(local
 (defun generated-copy-memory-induction (count source destination first second)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons first second)
     (generated-copy-memory-induction
      (1- count) (+ 8 source) (+ 8 destination)
      (generated-store-word destination (generated-load-word source first) first)
      (generated-store-word destination (generated-load-word source second) second)))))

(defthm generated-copy-keeps-memory-agreement
  (implies (generated-memory-equiv (proof-world-machine first) (proof-world-machine second))
           (generated-memory-equiv
            (proof-world-machine (generated-copy-words count source destination first))
            (proof-world-machine (generated-copy-words count source destination second))))
  :hints (("Goal" :induct (generated-copy-memory-induction count source destination first second)
                  :in-theory (enable generated-copy-words))
          ("Subgoal *1/2" :use (:instance generated-loads-agree-when-memory-agrees (address source))))
  :rule-classes nil)

(defthm generated-address-path-preserves-memory
  (let* ((path (generated-address-path rd rn bytes subtract))
         (after (generated-path-after path before)))
    (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31) (unsigned-byte-p 64 bytes))
             (generated-memory-equiv (proof-world-machine after) (proof-world-machine before))))
  :hints (("Goal" :in-theory (enable generated-address-path generated-path-after))))

(local
 (defthm generated-tail-memory-length-of-append
   (equal (len (append first second)) (+ (len first) (len second)))))

(local
 (defthm generated-tail-memory-copy-zero-is-empty
   (equal (generated-indexed-copy-path 0 offset) nil)
   :hints (("Goal" :in-theory (enable generated-indexed-copy-path)))))

(local
 (defthm generated-tail-memory-copy-zero-words
   (equal (generated-copy-words 0 source destination world) world)
   :hints (("Goal" :in-theory (enable generated-copy-words)))))

(defthm generated-indexed-tail-prefix-observes-copied-memory
  (let* ((frame (proof-world-reg 19 before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (prefix (generated-indexed-tail-prefix arity))
         (after (generated-path-after prefix before)))
    (implies (and (natp arity) (unsigned-byte-p 64 bytes) (<= frame source)
                  (< (+ (proof-world-pc before) (* 4 (len prefix))) (expt 2 64))
                  (generated-ordinary-machine-p before))
             (and (generated-memory-equiv
                   (proof-world-machine after)
                   (proof-world-machine (generated-copy-words arity source frame before)))
                  (equal (proof-world-reg 28 after) (proof-world-reg 28 before)))))
  :hints (("Goal"
           :use (:instance generated-copy-keeps-memory-agreement
                           (count arity) (source (- (proof-world-reg 25 before) (* 8 arity)))
                           (destination (proof-world-reg 19 before))
                           (first (generated-path-after (generated-address-path 10 25 (* 8 arity) t) before))
                           (second before))
           :in-theory (enable generated-indexed-tail-prefix generated-path-after)))
  :rule-classes nil)

(defthm generated-indexed-tail-observes-copied-memory
  (let* ((frame (proof-world-reg 19 before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (prefix (generated-indexed-tail-prefix arity))
         (pc (+ (proof-world-pc before) (* 4 (len prefix))))
         (after (generated-path-after (generated-indexed-tail-path arity target before) before)))
    (implies (and (natp arity) (unsigned-byte-p 64 bytes) (<= frame source)
                  (< pc (expt 2 64)) (generated-ordinary-machine-p before))
             (and (generated-memory-equiv
                   (proof-world-machine after)
                   (proof-world-machine (generated-copy-words arity source frame before)))
                  (equal (proof-heap-base after) (proof-heap-base before)))))
  :hints (("Goal"
           :use (generated-indexed-tail-prefix-observes-copied-memory
                 (:instance generated-indexed-tail-prefix-effect (address 0)))
           :in-theory (e/d (generated-indexed-tail-path generated-path-after proof-heap-base)
                           (generated-indexed-tail-prefix-effect)))))

(defthm generated-copy-preserves-published-word-views
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine (generated-copy-words count source destination before)))
         (views (generated-word-views words base objects packages first)))
    (implies (and (generated-word-block-span-p destination count)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p destination (+ destination (* 8 count)) objects first)
                  views)
             (equal (generated-word-views words base objects packages last) views)))
  :hints (("Goal" :induct (generated-word-views words base objects packages (proof-world-machine before)))
          ("Subgoal *1/2"
           :use (:instance generated-published-view-outside-copied-destination
                           (word (car words)) (copies count)))))

(defthm generated-indexed-tail-preserves-published-word-views
  (let* ((frame (proof-world-reg 19 before))
         (base (proof-heap-base before))
         (bytes (* 8 arity))
         (source (- (proof-world-reg 25 before) bytes))
         (prefix (generated-indexed-tail-prefix arity))
         (after (generated-path-after (generated-indexed-tail-path arity target before) before))
         (first (proof-world-machine before))
         (views (generated-word-views words base objects packages first)))
    (implies (and (natp arity) (unsigned-byte-p 64 bytes) (<= frame source)
                  (< (+ (proof-world-pc before) (* 4 (len prefix))) (expt 2 64))
                  (generated-ordinary-machine-p before)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p frame (+ frame bytes) objects first)
                  views)
             (equal (generated-word-views words (proof-heap-base after) objects packages
                                          (proof-world-machine after)) views)))
  :hints (("Goal"
           :use (generated-indexed-tail-observes-copied-memory
                 (:instance generated-copy-preserves-published-word-views
                            (base (proof-heap-base before)) (count arity)
                            (source (- (proof-world-reg 25 before) (* 8 arity)))
                            (destination (proof-world-reg 19 before))))
           :in-theory (disable generated-indexed-tail-observes-copied-memory
                               generated-copy-preserves-published-word-views generated-word-views))))

(local
 (defthm generated-indexed-tail-prefix-fits-in-path
   (<= (len (generated-indexed-tail-prefix arity))
       (len (generated-indexed-tail-path arity target before)))
   :hints (("Goal" :in-theory (enable generated-indexed-tail-path)))
   :rule-classes :linear))

(local
 (defthm generated-compiled-arguments-have-published-views
   (let* ((arity (len args))
          (source (- (proof-stack-top before) (* 8 arity)))
          (base (proof-heap-base before))
          (machine (proof-world-machine before)))
     (implies (proof-compiled-entry-p address args before objects packages)
              (and (proof-object-map-p objects objects nil base packages machine)
                   (generated-word-views (generated-read-words arity source before)
                                          base objects packages machine))))
   :hints (("Goal" :in-theory (e/d (proof-compiled-entry-p proof-heap-p)
                                   (proof-heap-layout-p proof-static-p proof-object-map-p
                                    proof-external-objects proof-stack-prefix
                                    proof-stack-views generated-word-views))))))

(defthm generated-indexed-tail-establishes-entry-with-disjoint-objects
  (let* ((arity (len args))
         (bytes (* 8 arity))
         (frame (proof-world-reg 19 before))
         (source (- (proof-stack-top before) bytes))
         (sp (generated-sp before))
         (path (generated-indexed-tail-path arity target before))
         (after (generated-path-after path before)))
    (implies (and (unsigned-byte-p 64 bytes) (<= frame source)
                  (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                  (< (+ sp 16) (expt 2 64))
                  (proof-disjoint-p frame (+ frame bytes) sp (+ sp 16))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (generated-path-p path (list target) before)
                  (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (proof-object-disjoint-p frame (+ frame bytes) objects (proof-world-machine before))
                  (proof-heap-p after objects packages) (<= (proof-stack-base after) frame))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (proof-compiled-entry-p target args after objects packages)
                  (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                  (equal (generated-sp after) (+ sp 16)))))
  :hints (("Goal"
           :use (generated-indexed-tail-enters-with-argument-views
                 (:instance generated-compiled-arguments-have-published-views
                            (address (proof-world-pc before)))
                 (:instance generated-indexed-tail-preserves-published-word-views
                            (arity (len args))
                            (words (generated-read-words (len args)
                                                          (- (proof-stack-top before) (* 8 (len args)))
                                                          before))))
           :in-theory (e/d (proof-stack-top)
                           (generated-indexed-tail-preserves-published-word-views
                            generated-compiled-arguments-have-published-views
                            generated-word-views)))))
