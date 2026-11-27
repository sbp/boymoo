(in-package "BOYMOO-PROOFS")

(include-book "linked-loads")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-machine proof-world-stop proof-world-regions
                    proof-regions-p proof-region-p proof-region-disjoint-p proof-region-allows-p proof-covered-p
                    proof-subspan-p proof-span-p proof-disjoint-p proof-heap-layout-p proof-heap-p proof-stack-top
                    proof-stack-base proof-stack-end proof-stack-limit proof-decode proof-decode-at proof-fetchable-p
                    proof-instruction-at-p proof-instructions-at-p proof-instruction-effect proof-instruction-access-p
                    generated-store-word generated-path-p boymoo-model::a64-unsigned expt))

(local
 (defthm generated-covered-span-is-disjoint-from-excluded-region
   (implies (and (proof-region-disjoint-p start end regions) (proof-covered-p address size access regions))
            (proof-disjoint-p start end address (+ address size)))
   :hints (("Goal" :induct (proof-covered-p address size access regions)
                   :in-theory (enable proof-covered-p proof-region-disjoint-p proof-subspan-p proof-disjoint-p)))
   :rule-classes nil))

(defthm generated-mapped-writable-and-executable-spans-are-disjoint
  (implies (and (proof-regions-p regions)
                (proof-covered-p write-address write-size :write regions)
                (proof-covered-p code-address code-size :execute regions))
           (proof-disjoint-p write-address (+ write-address write-size) code-address (+ code-address code-size)))
  :hints (("Goal" :induct (len regions)
                  :in-theory (enable proof-regions-p proof-covered-p proof-region-allows-p proof-subspan-p proof-disjoint-p))
          ("Subgoal *1/1"
           :use ((:instance generated-covered-span-is-disjoint-from-excluded-region
                            (regions (cdr regions)) (start (caar regions)) (end (cadar regions))
                            (address write-address) (size write-size) (access :write))
                 (:instance generated-covered-span-is-disjoint-from-excluded-region
                            (regions (cdr regions)) (start (caar regions)) (end (cadar regions))
                            (address code-address) (size code-size) (access :execute)))))
  :rule-classes nil)

(local
 (defthm generated-word-store-outside-instruction-bytes-keeps-decoding
   (implies (and (proof-span-p address 8) (proof-span-p pc 4) (proof-disjoint-p address (+ address 8) pc (+ pc 4)))
            (equal (proof-decode-at pc (proof-world-machine (generated-store-word address value world)))
                   (proof-decode-at pc (proof-world-machine world))))
   :hints (("Goal"
            :use (:instance generated-read-after-writing-disjoint
                            (count 8) (length 4) (query pc) (memory (boymoo-model::a64-memory (proof-world-machine world))))
            :in-theory (enable proof-decode-at generated-store-word boymoo-model::a64-load boymoo-model::a64-store
                               boymoo-model::a64-memory proof-world-machine generated-set-machine proof-span-p)))
   :rule-classes nil))

(defthm generated-linked-instruction-survives-mapped-word-store
  (let ((regions (proof-world-regions world)))
    (implies (and (proof-regions-p regions) (proof-covered-p address 8 :write regions)
                  (proof-instruction-at-p instruction pc world))
             (proof-instruction-at-p instruction pc (generated-store-word address value world))))
  :hints (("Goal"
           :use ((:instance generated-mapped-writable-and-executable-spans-are-disjoint
                            (regions (proof-world-regions world)) (write-address address) (write-size 8)
                            (code-address pc) (code-size 4))
                 (:instance generated-covered-memory-has-bounded-span (size 8) (access :write) (regions (proof-world-regions world)))
                 (:instance generated-covered-memory-has-bounded-span (address pc) (size 4) (access :execute)
                            (regions (proof-world-regions world)))
                 generated-word-store-outside-instruction-bytes-keeps-decoding)
           :in-theory (enable proof-instruction-at-p proof-fetchable-p)))
  :rule-classes nil)

(local
 (defthm generated-size-checked-value-push-has-writable-slot
   (let ((top (proof-stack-top before)) (regions (proof-world-regions before)))
     (implies (and (proof-heap-layout-p before) (<= (+ top 8) (proof-stack-limit before)))
              (and (proof-covered-p top 8 :write regions) (proof-regions-p regions) (not (proof-world-stop before)))))
   :hints (("Goal"
            :use ((:instance generated-heap-layout-value-stack-bounds (world before))
                  (:instance generated-value-stack-reservation-covers-contained-read-or-write
                             (world before) (address (proof-stack-top before)) (width 8) (access :write)))
            :in-theory (enable proof-heap-layout-p proof-stack-top proof-subspan-p proof-span-p)))
   :rule-classes nil))

(local
 (defthm generated-mapped-value-push-slot-allows-store
   (implies (proof-covered-p (proof-world-reg 25 world) 8 :write (proof-world-regions world))
            (proof-instruction-access-p '(:single 0 8 25 0 :offset 0) world))
   :hints (("Goal" :in-theory (enable proof-instruction-access-p proof-access-p proof-world-reg proof-reg)))))

(defthm generated-push-has-checked-path-from-linked-bytes
  (let* ((pc (proof-world-pc before)) (end (+ pc 8)))
    (implies (and (proof-heap-p before objects packages)
                  (<= (+ (proof-stack-top before) 8) (proof-stack-limit before))
                  (< end (expt 2 64)) (generated-ordinary-machine-p before)
                  (proof-instructions-at-p *generated-push-path* pc before))
             (generated-path-p *generated-push-path* (list end) before)))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 generated-size-checked-value-push-has-writable-slot
                 (:instance generated-linked-instruction-survives-mapped-word-store
                            (instruction '(:arithmetic-imm 0 64 25 25 8)) (pc (+ 4 (proof-world-pc before)))
                            (address (proof-world-reg 25 before)) (value (proof-world-reg 0 before))
                            (world (generated-set-pc (+ 4 (proof-world-pc before)) before))))
           :in-theory (enable proof-instructions-at-p generated-path-p generated-instruction-p proof-stack-top)))
  :rule-classes nil)
