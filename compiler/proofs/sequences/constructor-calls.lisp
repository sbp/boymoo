(in-package "BOYMOO-PROOFS")

(include-book "constructors")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-saved-link-fits-word
   (unsigned-byte-p 64 (proof-world-reg 30 world))))

(local
 (defthm sequence-saved-constructor-words
   (let* ((memory (boymoo-model::a64-memory machine))
          (stored (boymoo-model::a64-write-bytes
                   8 (+ stack 8) link
                   (boymoo-model::a64-write-bytes 8 stack length memory))))
     (implies (and (proof-span-p stack 16)
                   (unsigned-byte-p 64 length)
                   (unsigned-byte-p 64 link))
              (and (equal (boymoo-model::a64-read-bytes 8 stack stored) length)
                   (equal (boymoo-model::a64-read-bytes 8 (+ stack 8) stored) link))))
   :hints (("Goal" :use ((:instance sequence-read-outside-write
                                    (count 8) (address stack) (start (+ stack 8)) (size 8)
                                    (value link)
                                    (memory (boymoo-model::a64-write-bytes
                                             8 stack length (boymoo-model::a64-memory machine)))))))
   :rule-classes nil))

(defthm sequence-small-string-call-to-allocator
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (length (proof-world-reg 0 before))
         (link (proof-world-reg 30 before))
         (continuation (+ image-base *sequence-new-string-offset* 32))
         (cuts (list (+ image-base *sequence-header-allocator-offset*)))
         (path *sequence-small-string-request*)
         (after (sequence-execute path before))
         (returned (proof-world-machine after)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-new-string-offset*))
          (unsigned-byte-p 64 continuation)
          (unsigned-byte-p 18 length)
          (<= 16 stack)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 0 after) (sequence-small-string-allocation length))
          (equal (proof-world-reg 30 after) continuation)
          (equal (boymoo-model::a64-sp returned) (- stack 16))
          (equal (proof-load-word (- stack 16) returned) length)
          (equal (proof-load-word (- stack 8) returned) link))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-world-machine proof-world-pc proof-world-reg
                        sequence-small-string-allocation)
    :use
    (sequence-small-string-allocation-request
     (:instance sequence-saved-constructor-words
                (stack (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                (length (proof-world-reg 0 before)) (link (proof-world-reg 30 before))
                (machine (proof-world-machine before)))
     (:instance sequence-segment-of-instruction-path
                (instructions *sequence-small-string-request*)
                (cuts (list (+ image-base *sequence-header-allocator-offset*)))
                (after (sequence-execute *sequence-small-string-request* before))))))
  :rule-classes nil)

(defthm sequence-empty-string-call-to-constructor
  (let* ((cuts (list (+ image-base *sequence-new-string-offset*)))
         (path *sequence-empty-string-dispatch*)
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-empty-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-empty-string-offset* 8))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 0 after) 0)
          (equal (proof-world-reg 30 after) (proof-world-reg 30 before)))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-world-machine proof-world-stop
                        proof-world-pc proof-world-reg)
    :use
    (sequence-empty-string-tail-call
     (:instance sequence-segment-of-instruction-path
                (instructions *sequence-empty-string-dispatch*)
                (cuts (list (+ image-base *sequence-new-string-offset*)))
                (after (sequence-execute *sequence-empty-string-dispatch* before))))))
  :rule-classes nil)

(local
 (defthm sequence-aligned-word-multiple-of-eight
   (implies (and (natp value) (equal (mod value 8) 0))
            (equal (* 8 (floor value 8)) value))
   :hints (("Goal" :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm sequence-aligned-reservation-offset
   (implies (and (natp address) (natp base) (natp bytes)
                 (equal (mod (+ address bytes) 8) 0)
                 (equal (mod base 8) 0) (equal (mod bytes 8) 0))
            (equal (mod (- address base) 8) 0))
   :hints (("Goal"
            :use ((:instance sequence-aligned-word-multiple-of-eight (value base))
                  (:instance sequence-aligned-word-multiple-of-eight (value bytes))
                  (:instance sequence-mod-add-multiple
                             (value (- address base)) (divisor 8)
                             (multiple (+ (floor base 8) (floor bytes 8)))))
            :in-theory (disable sequence-mod-add-multiple)))
   :rule-classes nil))

(local
 (defthm sequence-space-end-fits-word
   (unsigned-byte-p 64 (proof-spaces-end world))
   :hints (("Goal" :use ((:instance sequence-read-bytes-bits
                                    (count 8) (address (- (proof-heap-base world) 64))
                                    (memory (boymoo-model::a64-memory
                                             (proof-world-machine world)))))))))

(local
 (defthm sequence-box-top-fits-word
   (unsigned-byte-p 64 (proof-box-top world))))

(defthm sequence-reserved-header-in-mapped-heap
  (let ((base (proof-heap-base world)))
    (implies (and (proof-heap-layout-p world)
                  (proof-reserved-span-p :header address bytes world objects))
             (and (unsigned-byte-p 64 (+ address bytes))
                  (<= base address)
                  (equal (mod address 8) 0)
                  (equal (mod (- address base) 8) 0)
                  (proof-covered-p address bytes :write (proof-world-regions world)))))
  :hints
  (("Goal"
    :in-theory (disable proof-align-up proof-covered-p proof-object-disjoint-p
                        proof-regions-p proof-load-word proof-disjoint-p
                        proof-active-floor proof-inactive-floor proof-active-end proof-inactive-end
                        proof-cons-floor proof-box-top proof-spaces-end proof-heap-base proof-static-size)
    :use
    ((:instance sequence-aligned-reservation-offset (base (proof-heap-base world)))
     (:instance sequence-aligned-reservation-offset (base 0))
     (:instance sequence-align-up-covers-address
                (address (+ (proof-heap-base world)
                            (proof-static-size (proof-heap-base world)
                                               (proof-world-machine world))))
                (alignment *proof-runtime-page*))
     (:instance sequence-covered-subspan
                (start (- (proof-heap-base world) *proof-heap-prefix*))
                (count (+ *proof-heap-prefix* (- (proof-spaces-end world)
                                                 (proof-heap-base world))))
                (size bytes) (access :write) (regions (proof-world-regions world))))))
  :rule-classes nil)

(defthm sequence-small-string-after-allocator
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (length (proof-load-word stack machine))
         (link (proof-load-word (+ stack 8) machine))
         (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                 *proof-machine-reservation*))
         (address (proof-world-reg 0 returned))
         (bytes (sequence-small-string-allocation length))
         (path (sequence-small-string-finish-path length))
         (cuts (list link))
         (after (sequence-execute path returned))
         (published (cons (proof-object address :active :header 0) new-objects)))
    (implies
     (and (proof-allocator-return-p :header bytes before returned
                                    old-objects new-objects packages)
          (proof-subspan-p stack 16 stack end)
          (unsigned-byte-p 64 (+ stack 16))
          (unsigned-byte-p 18 length)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path path cuts returned))
     (and (proof-segment-p (len path) cuts returned :cut after)
          (proof-string-result-p length after published packages)
          (proof-register-frame-p 29 '(0 1 2 3) returned after)
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-pc after) link)
          (not (proof-world-stop after))
          (equal (cdr after) (cdr returned))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16)))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-layout-p proof-object-map-p proof-heap-object-spans-p
                        proof-external-objects proof-static-p proof-string-accounting-p
                        proof-dynamic-entries proof-dynamic-view proof-dynamic-symbol-objects-p
                        proof-stack-prefix proof-prefix-preserved-p proof-heap-frame-p
                        proof-dynamic-table-preserved-p proof-reserved-span-p proof-register-frame-p
                        proof-string-result-p proof-covered-p proof-segment-p proof-load-word
                        proof-world-machine proof-world-reg proof-heap-base
                        sequence-small-string-allocation sequence-small-string-finish-path)
    :use
    ((:instance sequence-allocator-keeps-small-string-saves
                (bytes (sequence-small-string-allocation
                        (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before)))))
     (:instance sequence-reserved-header-in-mapped-heap
                (world returned) (objects new-objects) (address (proof-world-reg 0 returned))
                (bytes (sequence-small-string-allocation
                        (proof-load-word (boymoo-model::a64-sp (proof-world-machine before))
                                         (proof-world-machine before)))))
     (:instance sequence-small-string-finish-contract (before returned) (objects new-objects))
     (:instance sequence-small-string-finish-effects (before returned)))))
  :rule-classes nil)
