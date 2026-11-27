(in-package "BOYMOO-PROOFS")

(include-book "terms")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-reg proof-world-pc proof-world-machine proof-instruction-effect
                    proof-execute proof-step proof-linux-svc proof-reg
                    boymoo-model::a64-execute boymoo-model::a64-unsigned
                    boymoo-compiler::gen-load-high boymoo-compiler::gen-load-word
                    boymoo-compiler::low-bits acl2::binary-logand acl2::binary-logior
                    generated-ash-as-floor lognot ash expt floor))

(defthm generated-shift-down-sixteen
  (implies (integerp word)
           (equal (ash word -16) (floor word 65536)))
  :hints (("Goal" :in-theory (enable ash floor))))

(defthm generated-halfword-bounds
  (implies (integerp word)
           (unsigned-byte-p 16 (boymoo-compiler::low-bits word 16)))
  :hints (("Goal" :use (:instance generated-floor-bounds (x word) (y 65536))
                  :in-theory (enable boymoo-compiler::low-bits)))
  :rule-classes nil)

(defthmd generated-effect-of-movk
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :move-wide 3 64 rd half position) world)
                  (generated-set-reg
                   rd (logior (ash half position)
                              (logand (lognot (ash 65535 position)) (proof-world-reg rd world)))
                   (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute proof-world-machine
                                    proof-world-pc proof-world-reg proof-reg boymoo-model::a64-execute
                                    generated-set-machine generated-set-pc generated-set-reg))))

(local
 (defthm generated-movk-merge-low-and-high
   (implies (and (natp position) (natp low) (< low (expt 2 position)) (integerp half))
            (equal (logior (* half (expt 2 position))
                           (logand (lognot (* 65535 (expt 2 position))) low))
                   (+ low (* (expt 2 position) half))))
   :hints (("Goal"
            :use ((:instance generated-logior-symmetric (x (* (expt 2 position) half)) (y low))
                  (:instance generated-logior-of-disjoint-fields (bits position) (high half))
                  (:instance generated-logand-with-high-field-cleared
                             (bits position) (high 65535)))))))

(defthm generated-effect-of-movk-above-low-word
  (let ((low (proof-world-reg rd world)))
    (implies (and (natp rd) (< rd 31) (natp position) (< low (expt 2 position)) (integerp half))
             (equal (proof-instruction-effect (list :move-wide 3 64 rd half position) world)
                    (generated-set-reg rd (+ low (* (expt 2 position) half))
                                       (generated-set-pc (+ 4 (proof-world-pc world)) world)))))
  :hints (("Goal"
           :use (:instance generated-movk-merge-low-and-high (low (proof-world-reg rd world)))
           :in-theory (e/d (proof-instruction-effect proof-execute
                           proof-world-machine proof-world-pc proof-world-reg proof-reg
                           boymoo-model::a64-execute generated-set-machine
                           generated-set-pc generated-set-reg)
                          (generated-movk-merge-low-and-high)))))

(defund generated-high-halfword-items (rd word position)
  (declare (xargs :measure (nfix (- 64 position))))
  (if (or (not (natp position)) (<= 64 position) (equal word 0))
      nil
    (let* ((half (boymoo-compiler::low-bits word 16))
           (rest (generated-high-halfword-items rd (ash word -16) (+ 16 position))))
      (if (equal half 0) rest (cons (list :movk rd half position) rest)))))

(defun generated-wide-word-items (rd word)
  (cons (list :movz rd (boymoo-compiler::low-bits word 16) 0)
        (generated-high-halfword-items rd (ash word -16) 16)))

(defthm generated-high-halfwords-emission
  (equal (boymoo-compiler::gen-load-high rd word position code)
         (boymoo-compiler::reverse-onto (generated-high-halfword-items rd word position) code))
  :hints (("Goal" :induct (boymoo-compiler::gen-load-high rd word position code)
                  :in-theory (enable boymoo-compiler::gen-load-high
                                     generated-high-halfword-items))))

(defthm generated-wide-word-emission
  (equal (boymoo-compiler::gen-load-word rd word code)
         (boymoo-compiler::reverse-onto (generated-wide-word-items rd word) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-load-word))))

(defun generated-move-instructions (items)
  (if (atom items)
      nil
    (let ((item (car items)))
      (cons (list :move-wide (if (eq (car item) :movz) 2 3) 64
                  (cadr item) (caddr item) (cadddr item))
            (generated-move-instructions (cdr items))))))

(local
 (defun generated-wide-move-induction (rd word position world)
   (declare (xargs :measure (nfix (- 64 position))))
   (if (or (not (natp position)) (<= 64 position) (equal word 0))
       world
     (let ((half (boymoo-compiler::low-bits word 16)))
       (generated-wide-move-induction
        rd (ash word -16) (+ 16 position)
        (if (equal half 0) world
          (proof-instruction-effect (list :move-wide 3 64 rd half position) world)))))))

(local
 (defthm generated-halfword-suffix-arithmetic
   (let* ((half (boymoo-compiler::low-bits word 16))
          (upper (ash word -16))
          (next (+ position 16))
          (merged (+ low (* (expt 2 position) half)))
          (all (+ low (* (expt 2 position) word))))
     (implies (and (member-equal position '(16 32 48))
                   (natp low) (< low (expt 2 position))
                   (natp word) (< word (expt 2 (- 64 position))))
              (and (natp half) (natp upper) (natp merged)
                   (< upper (expt 2 (- 64 next)))
                   (< merged (expt 2 next))
                   (< merged (expt 2 64))
                   (equal (+ merged (* (expt 2 next) upper)) all))))
   :hints (("Goal" :use (generated-halfword-bounds
                         (:instance generated-floor-bounds (x word) (y 65536)))
                   :in-theory (enable boymoo-compiler::low-bits)))
   :rule-classes nil))

(defthm generated-wide-word-suffix-value
  (let ((low (proof-world-reg rd before)))
    (implies (and (natp rd) (< rd 31) (member-equal position '(16 32 48 64))
                  (< low (expt 2 position)) (natp word) (< word (expt 2 (- 64 position))))
             (equal (proof-world-reg rd (generated-path-after
                                         (generated-move-instructions
                                          (generated-high-halfword-items rd word position)) before))
                    (+ low (* (expt 2 position) word)))))
  :hints (("Goal" :induct (generated-wide-move-induction rd word position before)
                  :in-theory (enable generated-high-halfword-items))
          ("Subgoal *1/2" :use (:instance generated-halfword-suffix-arithmetic
                                           (low (proof-world-reg rd before))))))

(defthm generated-wide-word-loads-value
  (implies (and (natp rd) (< rd 31) (unsigned-byte-p 64 word))
           (equal (proof-world-reg rd (generated-path-after
                                       (generated-move-instructions (generated-wide-word-items rd word))
                                       before))
                  word))
  :hints (("Goal" :use (generated-halfword-bounds
                        (:instance generated-floor-bounds (x word) (y 65536)))
                  :in-theory (enable boymoo-compiler::low-bits)))
  :rule-classes nil)

(defun generated-move-items-for-p (items rd)
  (if (atom items)
      (null items)
    (and (member-eq (caar items) '(:movz :movk))
         (equal (cadar items) rd)
         (generated-move-items-for-p (cdr items) rd))))

(defthm generated-high-halfword-items-use-destination
  (generated-move-items-for-p (generated-high-halfword-items rd word position) rd)
  :hints (("Goal" :induct (generated-high-halfword-items rd word position)
                  :in-theory (enable generated-high-halfword-items))))

(defthm generated-wide-word-items-use-destination
  (generated-move-items-for-p (generated-wide-word-items rd word) rd))

(local
 (defun generated-move-items-induction (items before)
   (if (atom items)
       before
     (generated-move-items-induction
      (cdr items)
      (proof-instruction-effect (car (generated-move-instructions (list (car items)))) before)))))

(defthm generated-move-path-preserves-other-registers
  (let* ((path (generated-move-instructions items))
         (after (generated-path-after path before)))
    (implies (and (natp rd) (< rd 31) (generated-move-items-for-p items rd))
             (and (equal (proof-world-stop after) (proof-world-stop before))
                  (implies (generated-ordinary-machine-p before)
                           (generated-ordinary-machine-p after))
                  (implies (not (equal other rd))
                           (equal (proof-world-reg other after) (proof-world-reg other before)))
                  (implies (not (member-equal rd '(23 24 25 26 27 28)))
                           (generated-heap-world-equiv after before))
                  (implies (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                           (equal (proof-world-pc after)
                                  (+ (proof-world-pc before) (* 4 (len path))))))))
  :hints (("Goal" :induct (generated-move-items-induction items before)
                  :in-theory (enable generated-effect-of-movk))))

(defthm generated-wide-word-path-preserves-world-fields
  (let* ((path (generated-move-instructions (generated-wide-word-items rd word)))
         (after (generated-path-after path before)))
    (implies (and (natp rd) (< rd 31))
             (and (equal (proof-world-stop after) (proof-world-stop before))
                  (implies (generated-ordinary-machine-p before)
                           (generated-ordinary-machine-p after))
                  (implies (not (equal other rd))
                           (equal (proof-world-reg other after) (proof-world-reg other before)))
                  (implies (not (member-equal rd '(23 24 25 26 27 28)))
                           (generated-heap-world-equiv after before))
                  (implies (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                           (equal (proof-world-pc after)
                                  (+ (proof-world-pc before) (* 4 (len path))))))))
  :hints (("Goal" :use (:instance generated-move-path-preserves-other-registers
                                  (items (generated-wide-word-items rd word)))
                  :in-theory (disable generated-move-path-preserves-other-registers
                                      generated-wide-word-items generated-move-instructions))))

(defthm generated-wide-word-load-continuation
  (let* ((path (generated-move-instructions (generated-wide-word-items rd word)))
         (continuation (+ (proof-world-pc before) (* 4 (len path))))
         (after (generated-path-after path before)))
    (implies (and (natp rd) (< rd 31) (unsigned-byte-p 64 word)
                  (< continuation (expt 2 64)) (not (proof-world-stop before))
                  (generated-path-p path (list continuation) before))
             (and (proof-segment-p (len path) (list continuation) before :cut after)
                  (equal (proof-world-pc after) continuation)
                  (equal (proof-world-reg rd after) word))))
  :hints (("Goal"
           :use (generated-wide-word-loads-value
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-move-instructions (generated-wide-word-items rd word)))
                            (cuts (list (+ (proof-world-pc before) (* 4 (len
                                          (generated-move-instructions (generated-wide-word-items rd word)))))))))
           :in-theory (disable generated-wide-word-items generated-move-instructions
                               generated-path-after generated-path-p proof-segment-p)))
  :rule-classes nil)
