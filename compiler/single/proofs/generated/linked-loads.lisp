(in-package "BOYMOO-PROOFS")

(include-book "term-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-world-machine proof-world-pc proof-world-reg
                    proof-world-stop proof-world-regions proof-stack-base proof-stack-end proof-heap-base
                    proof-instruction-at-p proof-instructions-at-p proof-instruction-access-p proof-instruction-effect
                    proof-fetchable-p proof-decode-at proof-decode proof-covered-p proof-subspan-p proof-span-p
                    generated-heap-world-equiv generated-path-p generated-path-after generated-move-instructions
                    generated-wide-word-items boymoo-model::a64-unsigned expt))

(defcong generated-memory-equiv equal (proof-decode-at address machine) 2
  :hints (("Goal" :in-theory (enable proof-decode-at))))

(defcong generated-heap-world-equiv equal (proof-instruction-at-p instruction address world) 3
  :hints (("Goal" :in-theory (enable proof-instruction-at-p proof-fetchable-p))))

(defcong generated-heap-world-equiv equal (proof-instructions-at-p instructions address world) 3
  :hints (("Goal" :induct (proof-instructions-at-p instructions address world)
                  :in-theory (enable proof-instructions-at-p))))

(defthm generated-linking-preserves-consecutive-blocks
  (implies (and (true-listp first) (integerp address))
           (equal (proof-instructions-at-p (append first rest) address world)
                  (and (proof-instructions-at-p first address world)
                       (proof-instructions-at-p rest (+ address (* 4 (len first))) world))))
  :hints (("Goal" :induct (proof-instructions-at-p first address world)
                  :in-theory (enable proof-instructions-at-p)))
  :rule-classes nil)

(defthm generated-covered-writable-span-covers-contained-read-or-write
  (implies (and (proof-covered-p lower size :write regions)
                (proof-subspan-p address width lower (+ lower size))
                (member-eq access '(:read :write)))
           (proof-covered-p address width access regions))
  :hints (("Goal" :induct (proof-covered-p lower size :write regions)
                  :in-theory (enable proof-covered-p proof-subspan-p proof-region-allows-p)))
  :rule-classes nil)

(defthm generated-value-stack-reservation-covers-contained-read-or-write
  (let* ((lower (proof-stack-base world)) (upper (proof-stack-end world))
         (regions (proof-world-regions world)))
    (implies (and (proof-heap-layout-p world) (proof-subspan-p address width lower upper)
                  (member-eq access '(:read :write)))
             (proof-covered-p address width access regions)))
  :hints (("Goal" :use (:instance generated-covered-writable-span-covers-contained-read-or-write
                                  (lower (proof-stack-base world)) (size *proof-value-reservation*)
                                  (regions (proof-world-regions world)))
                  :in-theory (enable proof-heap-layout-p)))
  :rule-classes nil)

(local
 (defun generated-placed-move-induction (items before)
   (if (atom items)
       before
     (generated-placed-move-induction
      (cdr items) (proof-instruction-effect (car (generated-move-instructions (list (car items)))) before)))))

(defthm generated-linked-move-wide-prefix-is-checked
  (let* ((path (generated-move-instructions items)) (pc (proof-world-pc before))
         (end (+ pc (* 4 (len path)))))
    (implies (and (natp rd) (< rd 31) (not (member-equal rd '(23 24 25 26 27 28)))
                  (generated-move-items-for-p items rd) (not (proof-world-stop before))
                  (< end (expt 2 64)) (<= end continuation)
                  (proof-instructions-at-p path pc before))
             (generated-path-p path (list continuation) before)))
  :hints (("Goal" :induct (generated-placed-move-induction items before)
                  :in-theory (enable generated-path-p generated-move-instructions proof-instructions-at-p
                                     generated-effect-of-movk)))
  :rule-classes nil)

(local
 (defthm generated-register-offset-without-shift-is-word
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-register-offset register 3 0 (proof-world-machine world))
                   (proof-world-reg register world)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-register-offset proof-world-reg proof-reg)))))

(defthm generated-frame-load-instruction-is-readable
  (let* ((offset (if indexed (proof-world-reg 17 world) bytes))
         (address (+ (proof-world-reg 19 world) offset))
         (load (if indexed '(:single 1 8 19 0 :register 17 3 0) (list :single 1 8 19 0 :offset bytes))))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p address 8 (proof-stack-base world) (proof-stack-end world)))
             (proof-instruction-access-p load world)))
  :hints (("Goal" :use (:instance generated-value-stack-reservation-covers-contained-read-or-write
                                  (address (+ (proof-world-reg 19 world) (if indexed (proof-world-reg 17 world) bytes)))
                                  (width 8) (access :read))
                  :in-theory (enable proof-instruction-access-p proof-access-p proof-subspan-p proof-span-p
                                     proof-world-reg proof-reg)))
  :rule-classes nil)

(local
 (defthm generated-move-path-is-a-true-list
   (true-listp (generated-move-instructions items))
   :hints (("Goal" :induct (len items) :in-theory (enable generated-move-instructions)))))

(local
 (defthm generated-wide-indexed-frame-load-is-checked
   (let* ((items (generated-wide-word-items 17 bytes)) (prefix (generated-move-instructions items))
          (load '(:single 1 8 19 0 :register 17 3 0)) (pc (proof-world-pc before))
          (address (+ (proof-world-reg 19 before) bytes)) (path (append prefix (list load)))
          (end (+ pc (* 4 (len path)))))
     (implies (and (proof-heap-layout-p before) (not (proof-world-stop before))
                   (unsigned-byte-p 64 bytes) (< end (expt 2 64))
                   (proof-subspan-p address 8 (proof-stack-base before) (proof-stack-end before))
                   (proof-instructions-at-p path pc before))
              (generated-path-p path (list end) before)))
   :hints (("Goal"
            :use ((:instance generated-linking-preserves-consecutive-blocks
                             (first (generated-move-instructions (generated-wide-word-items 17 bytes)))
                             (rest '((:single 1 8 19 0 :register 17 3 0)))
                             (address (proof-world-pc before)) (world before))
                  (:instance generated-wide-word-loads-value (rd 17) (word bytes))
                  (:instance generated-wide-word-path-preserves-world-fields (rd 17) (word bytes) (other 19))
                  (:instance generated-linked-move-wide-prefix-is-checked (rd 17) (items (generated-wide-word-items 17 bytes))
                             (continuation (+ 4 (proof-world-pc before)
                                              (* 4 (len (generated-move-instructions (generated-wide-word-items 17 bytes)))))))
                  (:instance generated-frame-load-instruction-is-readable (indexed t) (bytes bytes)
                             (world (generated-path-after (generated-move-instructions (generated-wide-word-items 17 bytes)) before))))
            :in-theory (enable generated-path-p proof-instructions-at-p)))
   :rule-classes nil))

(defthm generated-linked-frame-slot-load-has-checked-path
  (let* ((bytes (* 8 slot)) (path (generated-frame-load-path 0 slot))
         (address (+ (proof-world-reg 19 before) bytes)) (pc (proof-world-pc before))
         (end (+ pc (* 4 (len path)))))
    (implies (and (natp slot) (unsigned-byte-p 64 bytes) (< end (expt 2 64))
                  (proof-heap-layout-p before) (not (proof-world-stop before))
                  (proof-subspan-p address 8 (proof-stack-base before) (proof-stack-end before))
                  (proof-instructions-at-p path pc before))
             (generated-path-p path (list end) before)))
  :hints (("Goal"
           :use ((:instance generated-wide-indexed-frame-load-is-checked (bytes (* 8 slot)))
                 (:instance generated-frame-load-instruction-is-readable (indexed nil) (bytes (* 8 slot)) (world before)))
           :in-theory (enable generated-frame-load-path generated-path-p proof-instructions-at-p)))
  :rule-classes nil)

(defthm generated-simple-operand-has-checked-path-from-linked-bytes
  (let* ((path (generated-simple-operand-path term 0 scope constants))
         (pc (proof-world-pc before)) (end (+ pc (* 4 (len path)))))
    (implies (and (generated-simple-operand-agrees-p term source scope slots quoted)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-heap-p before objects packages) (not (proof-world-stop before))
                  (< end (expt 2 64)) (proof-instructions-at-p path pc before))
             (generated-path-p path (list end) before)))
  :hints (("Goal"
           :use ((:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-layout-value-stack-bounds (world before))
                 (:instance generated-linked-frame-slot-load-has-checked-path (slot (boymoo-compiler::gen-slot term scope)))
                 (:instance generated-environment-binding (variable source) (bindings slots)
                            (frame (proof-world-reg 19 before)) (slot (boymoo-compiler::gen-slot term scope)) (world before))
                 (:instance generated-linked-move-wide-prefix-is-checked (rd 0)
                            (items (generated-wide-word-items 0
                                     (proof-constant-word (boymoo-compiler::index-get (cadr term) constants))))
                            (continuation (+ (proof-world-pc before)
                                             (* 4 (len (generated-move-instructions
                                                        (generated-wide-word-items 0
                                                         (proof-constant-word (boymoo-compiler::index-get (cadr term) constants))))))))))
           :in-theory (enable generated-simple-operand-path generated-simple-operand-agrees-p
                              proof-subspan-p proof-span-p)))
  :rule-classes nil)
