(in-package "BOYMOO-PROOFS")

(include-book "saved-words")
(include-book "segments")
(include-book "heap-locality")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-prefix-after-prefix
  (implies (and (natp first-steps) (natp last-steps)
                (allocation-prefix-p first-steps cuts before middle)
                (allocation-prefix-p last-steps cuts middle after))
           (allocation-prefix-p (+ first-steps last-steps) cuts before after))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-prefix-p first-steps cuts before middle)
           :expand ((allocation-prefix-p (+ first-steps last-steps) cuts before after))
           :in-theory (disable proof-step))))

(defun allocation-memory-addresses-are-words-p (entries)
  (if (atom entries)
      t
    (and (unsigned-byte-p 64 (caar entries))
         (allocation-memory-addresses-are-words-p (cdr entries)))))

(defthm allocation-span-agreement-on-word-addresses
  (implies (and (proof-memory-span-agrees-p lower upper before after)
                (allocation-memory-addresses-are-words-p entries))
           (and (proof-byte-entries-agree-p entries lower upper (allocation-memory before) (allocation-memory after))
                (proof-byte-entries-agree-p entries lower upper (allocation-memory after) (allocation-memory before))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-memory-addresses-are-words-p entries)
           :in-theory (disable proof-memory-span-agrees-p boymoo-model::a64-byte))
          ("Subgoal *1/2"
           :use ((:instance allocation-byte-agreement-in-span (address (caar entries)))))))

(defthm allocation-byte-entries-agree-in-contained-span
  (implies (and (proof-byte-entries-agree-p entries lower upper first last)
                (<= lower start) (<= end upper))
           (proof-byte-entries-agree-p entries start end first last))
  :rule-classes nil
  :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper first last)
           :in-theory (disable boymoo-model::a64-byte))))

(defthm allocation-memory-span-agreement-in-contained-span
  (implies (and (proof-memory-span-agrees-p lower upper before after)
                (<= lower start) (<= end upper))
           (proof-memory-span-agrees-p start end before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-byte-entries-agree-in-contained-span
                  (entries (allocation-memory before)) (first (allocation-memory before)) (last (allocation-memory after)))
                 (:instance allocation-byte-entries-agree-in-contained-span
                  (entries (allocation-memory after)) (first (allocation-memory before)) (last (allocation-memory after))))
           :in-theory (disable proof-byte-entries-agree-p))))

(local
 (defthm allocation-frame-byte-entry-agreement-transitive
   (implies (and (proof-byte-entries-agree-p entries lower upper first middle)
                 (proof-byte-entries-agree-p entries lower upper middle last))
            (proof-byte-entries-agree-p entries lower upper first last))
   :rule-classes nil
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper first middle)
            :in-theory (disable boymoo-model::a64-byte)))))

(defthm allocation-memory-span-agreement-transitive
  (implies (and (proof-memory-span-agrees-p lower upper before middle)
                (proof-memory-span-agrees-p lower upper middle after)
                (allocation-memory-addresses-are-words-p (allocation-memory before))
                (allocation-memory-addresses-are-words-p (allocation-memory after)))
           (proof-memory-span-agrees-p lower upper before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-span-agreement-on-word-addresses
                  (entries (allocation-memory before)) (before middle))
                 (:instance allocation-span-agreement-on-word-addresses
                  (entries (allocation-memory after)) (after middle))
                 (:instance allocation-frame-byte-entry-agreement-transitive
                  (entries (allocation-memory before)) (first (allocation-memory before))
                  (middle (allocation-memory middle)) (last (allocation-memory after)))
                 (:instance allocation-frame-byte-entry-agreement-transitive
                  (entries (allocation-memory after)) (first (allocation-memory before))
                  (middle (allocation-memory middle)) (last (allocation-memory after))))
           :in-theory (disable proof-byte-entries-agree-p allocation-memory-addresses-are-words-p))))

(defun allocation-restored-registers-p (registers before after)
  (if (atom registers)
      t
    (and (equal (proof-world-reg (car registers) after) (proof-world-reg (car registers) before))
         (allocation-restored-registers-p (cdr registers) before after))))

(local
 (defthm allocation-restored-register-has-old-value
   (implies (and (allocation-restored-registers-p registers before after)
                 (member-equal register registers))
            (equal (proof-world-reg register after) (proof-world-reg register before)))
   :rule-classes nil))

(local
 (defthm allocation-member-of-appended-clobbers
   (iff (member-equal register (append first second))
        (or (member-equal register first) (member-equal register second)))
   :hints (("Goal" :induct (append first second)))))

(local
 (defun allocation-register-count-induct (upper)
   (declare (xargs :measure (nfix upper)))
   (if (zp upper)
       upper
     (allocation-register-count-induct (1- upper)))))

(defthm allocation-register-frame-after-restoration
  (implies (and (proof-register-frame-p upper (append restored clobbers) before after)
                (allocation-restored-registers-p restored before after))
           (proof-register-frame-p upper clobbers before after))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-register-count-induct upper)
           :expand ((:free (frame) (proof-register-frame-p upper frame before after)))
           :in-theory (disable proof-register-frame-p allocation-restored-registers-p))
          ("Subgoal *1/1"
           :use ((:instance allocation-restored-register-has-old-value (register upper) (registers restored))))
          ("Subgoal *1/2"
           :use ((:instance allocation-restored-register-has-old-value (register upper) (registers restored))))))

(defthm allocation-frame-keeps-static-size
  (let ((base (proof-heap-base before)))
    (implies (and (proof-heap-frame-p before after) (proof-span-p base 8))
             (equal (proof-static-size base (proof-world-machine after))
                    (proof-static-size base (proof-world-machine before)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-in-agreeing-span
                  (address (proof-heap-base before)) (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before)))))
           :in-theory (e/d (allocation-load-word)
                           (proof-load-word proof-memory-span-agrees-p proof-heap-base
                            proof-stack-base proof-stack-end proof-spaces-end
                            proof-machine-limit proof-streams-preserved-p)))))

(defthm allocation-heap-frame-compose
  (implies (and (proof-heap-frame-p before middle)
                (proof-heap-frame-p middle after)
                (proof-span-p (proof-heap-base before) 8)
                (equal (proof-machine-limit middle) (proof-machine-limit before))
                (<= (allocation-sp middle) (allocation-sp before))
                (allocation-memory-addresses-are-words-p (allocation-memory before))
                (allocation-memory-addresses-are-words-p (allocation-memory after)))
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-frame-keeps-static-size (after middle))
                 (:instance allocation-memory-span-agreement-in-contained-span
                  (before middle) (lower (allocation-sp middle))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
                  (start (allocation-sp before))
                  (end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
                 (:instance allocation-memory-span-agreement-transitive
                  (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before))))
                 (:instance allocation-memory-span-agreement-transitive
                  (lower (+ 32 (proof-heap-base before)))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-memory-span-agreement-transitive
                  (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (disable proof-heap-base proof-static-size proof-load-word proof-stack-base proof-stack-end
                               proof-spaces-end proof-machine-limit proof-memory-span-agrees-p proof-span-p
                               allocation-memory-addresses-are-words-p))))

(defthm allocation-heap-preservation-compose-at-same-stack-top
  (implies (and (proof-preserved-heap-p nil before middle old-objects middle-objects packages)
                (proof-preserved-heap-p nil middle after middle-objects new-objects packages)
                (equal (proof-stack-top middle) (proof-stack-top before))
                (proof-span-p (proof-heap-base before) 8)
                (equal (proof-machine-limit middle) (proof-machine-limit before))
                (<= (allocation-sp middle) (allocation-sp before))
                (allocation-memory-addresses-are-words-p (allocation-memory before))
                (allocation-memory-addresses-are-words-p (allocation-memory after)))
           (proof-preserved-heap-p nil before after old-objects new-objects packages))
  :rule-classes nil
  :hints (("Goal" :use (allocation-heap-frame-compose)
           :in-theory (disable proof-heap-p proof-heap-frame-p proof-stack-top proof-stack-prefix
                               proof-heap-base proof-machine-limit proof-dynamic-view proof-span-p))))
