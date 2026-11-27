(in-package "BOYMOO-PROOFS")

(include-book "prologue")
(include-book "heap-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-reg proof-world-machine proof-world-pc proof-world-stop
                    proof-frame-return-p proof-heap-frame-p proof-register-frame-p
                    proof-grow-return-p proof-preserved-heap-p proof-fixed-heap-p
                    proof-heap-p proof-memory-span-agrees-p proof-byte-entries-agree-p
                    boymoo-model::a64-unsigned boymoo-model::a64-byte
                    boymoo-model::a64-read-bytes generated-load-word generated-sp expt))

(defthm generated-register-in-preserved-frame
  (implies (and (natp register) (natp last) (<= register last)
                (not (member-equal register clobbers))
                (proof-register-frame-p last clobbers before after))
           (equal (proof-world-reg register after) (proof-world-reg register before)))
  :hints (("Goal" :induct (proof-register-frame-p last clobbers before after)
                  :in-theory (enable proof-register-frame-p)))
  :rule-classes nil)

(local
 (defthm generated-present-byte-agrees-in-span
   (implies (and (proof-byte-entries-agree-p entries start end first second)
                 (<= start address) (< address end) (assoc-equal address entries))
            (equal (boymoo-model::a64-byte address first)
                   (boymoo-model::a64-byte address second)))
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries start end first second)
                   :in-theory (enable proof-byte-entries-agree-p)))
   :rule-classes nil))

(local
 (defthm generated-byte-in-agreeing-span
   (let ((first (boymoo-model::a64-memory (proof-world-machine before)))
         (second (boymoo-model::a64-memory (proof-world-machine after))))
     (implies (and (proof-memory-span-agrees-p start end before after)
                   (unsigned-byte-p 64 address) (<= start address) (< address end))
              (equal (boymoo-model::a64-byte address first)
                     (boymoo-model::a64-byte address second))))
   :hints (("Goal"
            :use ((:instance generated-present-byte-agrees-in-span
                             (entries (boymoo-model::a64-memory (proof-world-machine before)))
                             (first (boymoo-model::a64-memory (proof-world-machine before)))
                             (second (boymoo-model::a64-memory (proof-world-machine after))))
                  (:instance generated-present-byte-agrees-in-span
                             (entries (boymoo-model::a64-memory (proof-world-machine after)))
                             (first (boymoo-model::a64-memory (proof-world-machine before)))
                             (second (boymoo-model::a64-memory (proof-world-machine after)))))
            :in-theory (enable proof-memory-span-agrees-p boymoo-model::a64-byte)))
   :rule-classes nil))

(local
 (defun generated-span-induction (count address)
   (declare (xargs :measure (nfix count)))
   (if (zp count) address
     (generated-span-induction (1- count) (1+ address)))))

(defthm generated-read-in-agreeing-span
  (implies (and (natp count) (natp address) (<= (+ address count) (expt 2 64))
                (<= start address) (<= (+ address count) end)
                (proof-memory-span-agrees-p start end before after))
           (equal (boymoo-model::a64-read-bytes
                   count address (boymoo-model::a64-memory (proof-world-machine after)))
                  (boymoo-model::a64-read-bytes
                   count address (boymoo-model::a64-memory (proof-world-machine before)))))
  :hints (("Goal" :induct (generated-span-induction count address)
                  :in-theory (enable boymoo-model::a64-read-bytes))
          ("Subgoal *1/2" :use generated-byte-in-agreeing-span))
  :rule-classes nil)

(local
 (defthm generated-word-in-agreeing-span
   (implies (and (proof-span-p address 8) (<= start address) (<= (+ address 8) end)
                 (proof-memory-span-agrees-p start end before after))
            (equal (generated-load-word address after) (generated-load-word address before)))
   :hints (("Goal" :use (:instance generated-read-in-agreeing-span (count 8))
                   :in-theory (enable generated-load-word proof-load-word boymoo-model::a64-load
                                      proof-span-p)))
   :rule-classes nil))

(defthm generated-grow-return-preserves-prologue-frame
  (let* ((sp (generated-sp before))
         (end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (natp required) (<= required (proof-stack-end before))
                  (<= (+ sp 16) end) (<= (+ sp 16) (expt 2 64))
                  (proof-grow-return-p "rt:grow" required before after old-objects new-objects packages))
             (and (<= required (proof-stack-limit after))
                  (equal (generated-sp after) sp)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (equal (proof-world-pc after) (proof-world-reg 30 before))
                  (equal (generated-load-word sp after) (generated-load-word sp before))
                  (equal (generated-load-word (+ sp 8) after) (generated-load-word (+ sp 8) before)))))
  :hints (("Goal"
           :use ((:instance generated-register-in-preserved-frame (register 19) (last 30)
                            (clobbers '(8 9 10 11 12 24)))
                 (:instance generated-register-in-preserved-frame (register 25) (last 30)
                            (clobbers '(8 9 10 11 12 24)))
                 (:instance generated-word-in-agreeing-span (address (generated-sp before))
                            (start (generated-sp before))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*)))
                 (:instance generated-word-in-agreeing-span (address (+ (generated-sp before) 8))
                            (start (generated-sp before))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*))))
           :in-theory (enable proof-grow-return-p proof-frame-return-p proof-heap-frame-p
                              proof-preserved-heap-p generated-heap-machine-sp proof-span-p)))
  :rule-classes nil)
