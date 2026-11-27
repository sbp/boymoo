(in-package "BOYMOO-PROOFS")

(include-book "subseq-view")
(include-book "readonly-call")
(include-book "cell-memory")
(include-book "register-only")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-subseq-stack-room-p (world)
  (let ((stack (boymoo-model::a64-sp (proof-world-machine world))))
    (and (< 0 (- stack 32))
         (<= (sequence-machine-stack-base world) (- stack 32)))))

(local
 (defthm sequence-subseq-saves-two-pairs
   (let* ((machine (proof-world-machine before))
          (stack (boymoo-model::a64-sp machine)))
     (equal (sequence-subseq-caller-save-memory before)
            (sequence-write-cell
             (- stack 32) (proof-world-reg 21 before) (proof-world-reg 30 before)
             (sequence-write-cell (- stack 16) (proof-world-reg 19 before) (proof-world-reg 20 before)
                                  (boymoo-model::a64-memory machine)))))
   :hints (("Goal" :in-theory (enable sequence-subseq-caller-save-memory sequence-write-cell)))
   :rule-classes nil))

(local
 (defthm sequence-subseq-noninteger-byte-has-zero-address
   (implies (not (integerp address))
            (equal (boymoo-model::a64-byte address memory) (boymoo-model::a64-byte 0 memory)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte sequence-a64-unsigned-as-mod)))))

(local
 (defthm sequence-subseq-saves-keep-outside-byte
   (let* ((first (proof-world-machine before))
          (stack (boymoo-model::a64-sp first))
          (bottom (- stack 32))
          (initial (boymoo-model::a64-memory first))
          (saved (sequence-subseq-caller-save-memory before)))
     (implies (and (posp bottom) (<= 0 address) (< address (expt 2 64))
                   (or (< address bottom) (<= stack address)))
              (equal (boymoo-model::a64-byte address saved) (boymoo-model::a64-byte address initial))))
   :hints
   (("Goal"
     :in-theory (disable sequence-subseq-caller-save-memory sequence-write-cell
                         proof-world-machine proof-world-reg)
     :cases ((integerp address))
     :use (sequence-subseq-saves-two-pairs
           (:instance sequence-sp-bits (machine (proof-world-machine before)))
           (:instance sequence-cell-write-keeps-other-byte
                      (cell (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (first (proof-world-reg 19 before)) (rest (proof-world-reg 20 before))
                      (memory (boymoo-model::a64-memory (proof-world-machine before))))
           (:instance sequence-cell-write-keeps-other-byte
                      (cell (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                      (first (proof-world-reg 21 before)) (rest (proof-world-reg 30 before))
                      (memory (sequence-write-cell
                               (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                               (proof-world-reg 19 before) (proof-world-reg 20 before)
                               (boymoo-model::a64-memory (proof-world-machine before)))))
           (:instance sequence-cell-write-keeps-other-byte (address 0)
                      (cell (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                      (first (proof-world-reg 19 before)) (rest (proof-world-reg 20 before))
                      (memory (boymoo-model::a64-memory (proof-world-machine before))))
           (:instance sequence-cell-write-keeps-other-byte (address 0)
                      (cell (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                      (first (proof-world-reg 21 before)) (rest (proof-world-reg 30 before))
                      (memory (sequence-write-cell
                               (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                               (proof-world-reg 19 before) (proof-world-reg 20 before)
                               (boymoo-model::a64-memory (proof-world-machine before))))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-saves-keep-outside-entries
   (let* ((first (proof-world-machine before))
          (stack (boymoo-model::a64-sp first))
          (bottom (- stack 32)))
     (implies (and (posp bottom) (<= 0 start) (<= end (expt 2 64))
                   (proof-disjoint-p start end bottom stack))
              (proof-byte-entries-agree-p entries start end (boymoo-model::a64-memory first)
                                          (sequence-subseq-caller-save-memory before))))
   :hints
   (("Goal"
     :induct (len entries)
     :in-theory (e/d (proof-byte-entries-agree-p proof-disjoint-p)
                     (sequence-subseq-caller-save-memory proof-world-machine)))
    ("Subgoal *1/1"
     :use ((:instance sequence-subseq-saves-keep-outside-byte (address (caar entries))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-saves-confine-stores
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (stack (boymoo-model::a64-sp first))
          (bottom (- stack 32)))
     (implies (and (posp bottom)
                   (equal (boymoo-model::a64-memory last) (sequence-subseq-caller-save-memory before)))
              (sequence-machine-write-confined-p bottom stack first last)))
   :hints
   (("Goal"
     :in-theory (enable sequence-machine-write-confined-p sequence-machine-span-agrees-p proof-disjoint-p)
     :use ((:instance sequence-subseq-saves-keep-outside-entries
                      (entries (boymoo-model::a64-memory (proof-world-machine before)))
                      (start 0) (end (- (boymoo-model::a64-sp (proof-world-machine before)) 32)))
           (:instance sequence-subseq-saves-keep-outside-entries
                      (entries (boymoo-model::a64-memory (proof-world-machine after)))
                      (start 0) (end (- (boymoo-model::a64-sp (proof-world-machine before)) 32)))
           (:instance sequence-subseq-saves-keep-outside-entries
                      (entries (boymoo-model::a64-memory (proof-world-machine before)))
                      (start (boymoo-model::a64-sp (proof-world-machine before))) (end (expt 2 64)))
           (:instance sequence-subseq-saves-keep-outside-entries
                      (entries (boymoo-model::a64-memory (proof-world-machine after)))
                      (start (boymoo-model::a64-sp (proof-world-machine before))) (end (expt 2 64))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-saved-stack-in-range
   (let* ((stack (boymoo-model::a64-sp (proof-world-machine before)))
          (bottom (- stack 32))
          (lower (sequence-machine-stack-base before))
          (upper (sequence-machine-stack-end before)))
     (implies (and (proof-heap-layout-p before) (sequence-subseq-stack-room-p before))
              (and (posp bottom)
                   (proof-subspan-p bottom 32 lower upper)
                   (proof-subspan-p bottom 0 lower upper)
                   (equal (mod bottom 16) 0))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-machine-stack-base sequence-machine-stack-end)
                     (proof-disjoint-p proof-regions-p proof-align-up sequence-mod-add-multiple))
     :expand ((proof-heap-layout-p before))
     :use ((:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-mod-add-multiple (divisor 16) (multiple -2)
                      (value (boymoo-model::a64-sp (proof-world-machine before)))))))
   :rule-classes nil))

(defthm sequence-subseq-view-call-keeps-heap
  (let* ((first (proof-world-machine before))
         (stack (boymoo-model::a64-sp first))
         (path *sequence-subseq-view-call*)
         (called (sequence-execute path before))
         (cuts (list (+ image-base *sequence-view-offset*))))
    (implies
     (and (proof-heap-p before objects packages)
          (sequence-subseq-stack-room-p before)
          (consp (boymoo-model::a64-registers first))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-offset* 24))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut called)
          (sequence-stack-write-p (- stack 32) stack before called)
          (proof-heap-p called objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p)
                    (proof-heap-p proof-heap-layout-p proof-world-machine proof-world-reg proof-world-pc
                     proof-world-stop proof-register-frame-p proof-segment-p sequence-execute
                     sequence-machine-write-confined-p proof-subspan-p sequence-instruction-path))
    :use (sequence-subseq-view-call-effects sequence-subseq-saved-stack-in-range
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-register-frame-on-prefix
                     (limit 29) (prefix 28) (clobbers '(5 6 7))
                     (after (sequence-execute *sequence-subseq-view-call* before)))
          (:instance sequence-frame-keeps-heap-registers
                     (clobbers '(5 6 7)) (after (sequence-execute *sequence-subseq-view-call* before)))
          (:instance sequence-subseq-saves-confine-stores (after (sequence-execute *sequence-subseq-view-call* before)))
          (:instance sequence-stack-write-keeps-heap-invariant
                     (start (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                     (end (boymoo-model::a64-sp (proof-world-machine before)))
                     (after (sequence-execute *sequence-subseq-view-call* before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions *sequence-subseq-view-call*) (cuts (list (+ image-base *sequence-view-offset*)))
                     (after (sequence-execute *sequence-subseq-view-call* before))))))
  :rule-classes nil)

(defthm sequence-subseq-retains-its-machine-stack-frame
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (stack (boymoo-model::a64-sp first)))
    (implies
     (and (proof-heap-layout-p before)
          (sequence-subseq-stack-room-p before)
          (sequence-heap-registers-agree-p before after)
          (equal (boymoo-model::a64-sp last) stack)
          (equal (boymoo-model::a64-memory last) (sequence-subseq-caller-save-memory before))
          (equal (cdr after) (cdr before)))
     (sequence-stack-write-p (- stack 32) stack before after)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p) (proof-heap-layout-p sequence-machine-write-confined-p))
    :use (sequence-subseq-saves-confine-stores sequence-subseq-saved-stack-in-range
          (:instance sequence-heap-layout-bounds (world before)))
    :expand ((proof-heap-layout-p before))))
  :rule-classes nil)

(defthm sequence-subseq-saved-registers-read-back
  (let* ((stack (boymoo-model::a64-sp (proof-world-machine before)))
         (bottom (- stack 32))
         (top (- stack 16))
         (last (proof-world-machine after)))
    (implies
     (and (proof-span-p bottom 32)
          (equal (boymoo-model::a64-memory last) (sequence-subseq-caller-save-memory before)))
     (and (equal (proof-load-word bottom last) (proof-world-reg 21 before))
          (equal (proof-load-word (+ bottom 8) last) (proof-world-reg 30 before))
          (equal (proof-load-word top last) (proof-world-reg 19 before))
          (equal (proof-load-word (+ top 8) last) (proof-world-reg 20 before)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-load-word proof-disjoint-p)
                    (sequence-write-cell sequence-subseq-caller-save-memory))
    :use
    (sequence-subseq-saves-two-pairs
     (:instance sequence-cell-write-first-word
                (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                (first (proof-world-reg 19 before)) (rest (proof-world-reg 20 before))
                (memory (boymoo-model::a64-memory (proof-world-machine before))))
     (:instance sequence-cell-write-rest-word
                (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                (first (proof-world-reg 19 before)) (rest (proof-world-reg 20 before))
                (memory (boymoo-model::a64-memory (proof-world-machine before))))
     (:instance sequence-cell-write-first-word
                (address (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                (first (proof-world-reg 21 before)) (rest (proof-world-reg 30 before))
                (memory (sequence-write-cell (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                                             (proof-world-reg 19 before) (proof-world-reg 20 before)
                                             (boymoo-model::a64-memory (proof-world-machine before)))))
     (:instance sequence-cell-write-rest-word
                (address (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                (first (proof-world-reg 21 before)) (rest (proof-world-reg 30 before))
                (memory (sequence-write-cell (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                                             (proof-world-reg 19 before) (proof-world-reg 20 before)
                                             (boymoo-model::a64-memory (proof-world-machine before)))))
     (:instance sequence-cell-write-keeps-other-reads (width 8)
                (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                (cell (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                (first (proof-world-reg 21 before)) (rest (proof-world-reg 30 before))
                (memory (sequence-write-cell (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                                             (proof-world-reg 19 before) (proof-world-reg 20 before)
                                             (boymoo-model::a64-memory (proof-world-machine before)))))
     (:instance sequence-cell-write-keeps-other-reads (width 8)
                (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))
                (cell (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                (first (proof-world-reg 21 before)) (rest (proof-world-reg 30 before))
                (memory (sequence-write-cell (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                                             (proof-world-reg 19 before) (proof-world-reg 20 before)
                                             (boymoo-model::a64-memory (proof-world-machine before))))))))
  :rule-classes nil)

(defun sequence-subseq-called-view (before)
  (sequence-execute *sequence-subseq-view-call* before))

(defun sequence-subseq-view-path (before)
  (let ((called (sequence-subseq-called-view before)))
    (sequence-string-view-path (proof-world-reg 0 called) (proof-heap-base called)
                               (proof-world-machine called))))

(defun sequence-subseq-view-return (before)
  (sequence-execute (sequence-subseq-view-path before) (sequence-subseq-called-view before)))

(local
 (defthm sequence-subseq-view-arguments-at-call
   (let* ((machine (proof-world-machine before))
          (stack (boymoo-model::a64-sp machine))
          (called (sequence-subseq-called-view before))
          (cuts (list (+ image-base *sequence-view-offset*))))
     (implies
      (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base
                               before objects packages)
           (sequence-subseq-stack-room-p before)
           (consp (boymoo-model::a64-registers machine))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-subseq-offset*))
           (unsigned-byte-p 64 (+ image-base *sequence-subseq-offset* 24))
           (sequence-instruction-path *sequence-subseq-view-call* cuts before))
      (and (proof-heap-p called objects packages)
           (consp (boymoo-model::a64-registers (proof-world-machine called)))
           (equal (proof-world-reg 0 called) (proof-world-reg 0 before))
           (equal (proof-world-reg 30 called) (+ image-base *sequence-subseq-offset* 24))
           (proof-register-frame-p 29 '(5 6 7) before called)
           (proof-reg-value-p 0 datum called objects packages)
           (proof-reg-value-p 5 datum called objects packages)
           (proof-reg-value-p 6 start called objects packages)
           (proof-reg-value-p 7 limit called objects packages)
           (equal (proof-heap-base called) (proof-heap-base before))
           (not (proof-world-stop called))
           (equal (boymoo-model::a64-sp (proof-world-machine called)) (- stack 32))
           (equal (boymoo-model::a64-memory (proof-world-machine called)) (sequence-subseq-caller-save-memory before))
           (equal (cdr called) (cdr before)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-runtime-pre-p proof-reg-value-p sequence-stack-write-p
                      sequence-heap-registers-agree-p)
                     (proof-machine-value-p proof-heap-p proof-value-p proof-view proof-world-machine
                      proof-world-stop proof-world-reg proof-world-pc proof-heap-base proof-label-address
                      proof-program-packages-p proof-segment-p proof-register-frame-p proof-subspan-p
                      sequence-machine-write-confined-p sequence-execute sequence-instruction-path))
     :use (sequence-subseq-view-call-keeps-heap sequence-subseq-view-call-effects
           (:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-confined-stack-write-preserves-value
                      (word (proof-world-reg 0 before))
                      (after (sequence-subseq-called-view before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-confined-stack-write-preserves-value
                      (word (proof-world-reg 1 before)) (datum start)
                      (after (sequence-subseq-called-view before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                      (end (boymoo-model::a64-sp (proof-world-machine before))))
           (:instance sequence-confined-stack-write-preserves-value
                      (word (proof-world-reg 2 before)) (datum limit)
                      (after (sequence-subseq-called-view before))
                      (start (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                      (end (boymoo-model::a64-sp (proof-world-machine before)))))))
   :rule-classes nil))

(local
 (defthm sequence-subseq-view-preserves-arguments
   (let* ((first (proof-world-machine before))
          (base (proof-heap-base before))
          (address (proof-pointer-address (proof-world-reg 0 before) base))
          (path (sequence-string-view-path (proof-world-reg 0 before) base first))
          (after (sequence-execute path before))
          (last (proof-world-machine after))
          (link (proof-world-reg 30 before)))
     (implies
      (and (proof-heap-p before objects packages)
           (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers first))
           (proof-reg-value-p 0 datum before objects packages)
           (proof-reg-value-p 5 datum before objects packages)
           (proof-reg-value-p 6 start before objects packages)
           (proof-reg-value-p 7 limit before objects packages)
           (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
           (sequence-instruction-path path (list link) before))
      (and (proof-heap-p after objects packages)
           (equal (proof-world-pc after) link)
           (equal (proof-world-reg 1 after) (if (stringp datum) (+ address 8) 0))
           (equal (proof-world-reg 2 after) (if (stringp datum) (len (coerce datum 'list)) 0))
           (proof-reg-value-p 0 datum after objects packages)
           (proof-reg-value-p 5 datum after objects packages)
           (proof-reg-value-p 6 start after objects packages)
           (proof-reg-value-p 7 limit after objects packages)
           (proof-register-frame-p 29 '(1 2 3) before after)
           (equal (proof-heap-base after) base)
           (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
           (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
           (consp (boymoo-model::a64-registers last))
           (equal (cdr after) (cdr before)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-frame-return-p
                      sequence-register-only-change-p sequence-heap-registers-agree-p proof-value-p)
                     (proof-view proof-heap-p proof-world-machine proof-world-stop
                      proof-world-reg proof-world-pc proof-heap-base proof-register-frame-p
                      proof-segment-p proof-fixed-heap-p proof-preserved-heap-p
                      sequence-instruction-path sequence-execute sequence-string-view-path))
     :use
     (sequence-string-view-field-contract
      (:instance sequence-register-frame-on-prefix (limit 30) (prefix 29) (clobbers '(1 2 3))
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-register-frame-on-prefix (limit 30) (prefix 28) (clobbers '(1 2 3))
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-frame-keeps-heap-registers (clobbers '(1 2 3))
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-register-only-change-keeps-heap
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 0)
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 5)
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 6)
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 7)
                 (after (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                              (proof-heap-base before) (proof-world-machine before)) before)))
      (:instance sequence-view-of-equal-memory
                 (base (proof-heap-base before)) (word (proof-world-reg 0 before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                             (proof-heap-base before) (proof-world-machine before)) before))))
      (:instance sequence-view-of-equal-memory
                 (base (proof-heap-base before)) (word (proof-world-reg 5 before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                             (proof-heap-base before) (proof-world-machine before)) before))))
      (:instance sequence-view-of-equal-memory
                 (base (proof-heap-base before)) (word (proof-world-reg 6 before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                             (proof-heap-base before) (proof-world-machine before)) before))))
      (:instance sequence-view-of-equal-memory
                 (base (proof-heap-base before)) (word (proof-world-reg 7 before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute (sequence-string-view-path (proof-world-reg 0 before)
                                             (proof-heap-base before) (proof-world-machine before)) before)))))))
   :rule-classes nil))

(defthm sequence-subseq-view-ready
  (let* ((first (proof-world-machine before))
         (called (sequence-subseq-called-view before))
         (returned (sequence-subseq-view-return before))
         (last (proof-world-machine returned))
         (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before)))
         (link (+ image-base *sequence-subseq-offset* 24))
         (prefix (append *sequence-subseq-view-call* (sequence-subseq-view-path before))))
    (implies
     (and (proof-runtime-pre-p 'subseq (list datum start limit) program labels image-base before objects packages)
          (sequence-subseq-stack-room-p before)
          (consp (boymoo-model::a64-registers first))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-offset*))
          (unsigned-byte-p 64 link)
          (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
          (sequence-instruction-path *sequence-subseq-view-call* (list (+ image-base *sequence-view-offset*)) before)
          (sequence-instruction-path (sequence-subseq-view-path before) (list link) called)
          (sequence-instruction-path prefix (list link) before))
     (and (proof-segment-p (len prefix) (list link) before :cut returned)
          (proof-heap-p returned objects packages)
          (not (proof-world-stop returned))
          (equal (proof-world-pc returned) link)
          (equal (proof-world-reg 1 returned) (if (stringp datum) (+ address 8) 0))
          (equal (proof-world-reg 2 returned) (if (stringp datum) (len (coerce datum 'list)) 0))
          (proof-reg-value-p 0 datum returned objects packages)
          (proof-reg-value-p 5 datum returned objects packages)
          (proof-reg-value-p 6 start returned objects packages)
          (proof-reg-value-p 7 limit returned objects packages)
          (proof-register-frame-p 29 '(1 2 3 5 6 7) before returned)
          (consp (boymoo-model::a64-registers last))
          (equal (boymoo-model::a64-sp last) (- (boymoo-model::a64-sp first) 32))
          (equal (boymoo-model::a64-memory last) (sequence-subseq-caller-save-memory before))
          (equal (cdr returned) (cdr before)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-world-stop)
                    (proof-runtime-pre-p proof-reg-value-p proof-heap-p proof-segment-p
                     proof-world-machine proof-world-reg proof-world-pc proof-heap-base proof-pointer-address
                     proof-register-frame-p
                     sequence-subseq-view-path sequence-subseq-view-return sequence-subseq-called-view
                     sequence-string-view-path sequence-execute sequence-instruction-path
                     acl2::binary-append sequence-execute-append))
    :use (sequence-subseq-view-arguments-at-call
          (:instance sequence-subseq-view-preserves-arguments (before (sequence-subseq-called-view before)))
          (:instance sequence-register-frame-with-more-clobbers (limit 29)
                     (old '(5 6 7)) (new '(1 2 3 5 6 7)) (after (sequence-subseq-called-view before)))
          (:instance sequence-register-frame-with-more-clobbers (limit 29)
                     (old '(1 2 3)) (new '(1 2 3 5 6 7))
                     (before (sequence-subseq-called-view before)) (after (sequence-subseq-view-return before)))
          (:instance sequence-register-frame-transitive (limit 29) (clobbers '(1 2 3 5 6 7))
                     (middle (sequence-subseq-called-view before)) (after (sequence-subseq-view-return before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions (append *sequence-subseq-view-call* (sequence-subseq-view-path before)))
                     (cuts (list (+ image-base *sequence-subseq-offset* 24)))
                     (after (sequence-subseq-view-return before)))
          (:instance sequence-execute-append (world before)
                     (first *sequence-subseq-view-call*) (second (sequence-subseq-view-path before))))
    :expand ((sequence-subseq-view-return before)
             (sequence-subseq-view-path before)
             (sequence-subseq-called-view before))))
  :rule-classes nil)
