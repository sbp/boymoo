(in-package "BOYMOO-PROOFS")

(include-book "instructions")
(include-book "memory")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-cons-sp-bound
   (< (allocation-sp world) *allocation-word-modulus*)
   :rule-classes :linear
   :hints (("Goal" :use ((:instance allocation-word-register-range (register 0)))
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                            (allocation-word-register-range))))))

(local
 (defthm allocation-cons-sp-natural
   (natp (allocation-sp world))
   :rule-classes :type-prescription
   :hints (("Goal" :use ((:instance allocation-word-register-range (register 0)))
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                            (allocation-word-register-range))))))

(defconst *allocation-cons-fast-path* (take 11 *allocation-cons-code*))
(defconst *allocation-cons-growth-path*
  (append (take 3 *allocation-cons-code*) (take 3 (nthcdr 11 *allocation-cons-code*))))
(defconst *allocation-cons-root-path* (take 4 (nthcdr 14 *allocation-cons-code*)))
(defconst *allocation-cons-return-path* (nthcdr 18 *allocation-cons-code*))

(defun allocation-cons-address (origin index)
  (+ (allocation-code-address "prim:COMMON-LISP::CONS" origin) (* 4 index)))

(defun allocation-cons-machine-entry-p (origin world)
  (and (allocation-code-origin-p origin)
       (allocation-machine-state-p world)
       (not (proof-world-stop world))
       (equal (proof-world-pc world) (allocation-cons-address origin 0))
       (<= 128 (proof-heap-base world))
       (<= (proof-heap-base world) (proof-box-top world))
       (<= (proof-box-top world) (proof-heap-limit world))
       (<= (proof-heap-limit world) (proof-cons-floor world))))

(defun allocation-cons-fields-p (address first second world)
  (and (equal (allocation-load-word address world) first)
       (equal (allocation-load-word (+ address 8) world) second)))

(defun allocation-cons-fast-return-p (before after)
  (let ((address (- (proof-cons-floor before) 16))
        (metadata (- (proof-heap-base before) 112)))
    (and (proof-frame-return-p '(0 2 9 26) t before after)
         (proof-span-p address 16)
         (equal (proof-cons-floor after) address)
         (equal (proof-box-top after) (proof-box-top before))
         (equal (proof-heap-limit after) (- (proof-heap-limit before) 16))
         (equal (proof-world-reg 0 after) (- address (proof-heap-base before)))
         (allocation-cons-fields-p address (proof-world-reg 0 before) (proof-world-reg 1 before) after)
         (equal (allocation-memory after)
                (allocation-memory
                 (allocation-store-word
                  (+ address 8) (proof-world-reg 1 before)
                  (allocation-store-word address (proof-world-reg 0 before)
                   (allocation-store-word metadata address before)))))
         (equal (proof-world-regions after) (proof-world-regions before))
         (equal (proof-world-replies after) (proof-world-replies before))
         (proof-streams-preserved-p before after))))

(defthm allocation-cons-fast-machine-return
  (implies (and (allocation-cons-machine-entry-p origin before)
                (proof-allocation-fits-p :cons 16 before)
                (equal after (allocation-path-end *allocation-cons-fast-path* before)))
           (allocation-cons-fast-return-p before after))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum
                                     allocation-unsigned-64-of-difference))))

(defthm allocation-cons-fast-checked-return
  (let ((cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (proof-allocation-fits-p :cons 16 before)
                  (allocation-path-ready-p *allocation-cons-fast-path* cuts before)
                  (equal after (allocation-path-end *allocation-cons-fast-path* before)))
             (and (allocation-cons-fast-return-p before after)
                  (proof-segment-p (len *allocation-cons-fast-path*) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-cons-fast-machine-return
                        (:instance allocation-checked-cut
                         (instructions *allocation-cons-fast-path*) (world before)
                         (cuts (list (proof-world-reg 30 before)))))
           :in-theory (disable allocation-cons-machine-entry-p
                               allocation-cons-fields-p
                               allocation-checked-cut allocation-path-ready-p
                               allocation-path-end proof-allocation-fits-p proof-segment-p))))

(defun allocation-cons-growth-edge-p (origin before cut)
  (let ((save (- (allocation-sp before) 16)))
    (and (allocation-machine-state-p cut)
         (not (proof-world-stop cut))
         (equal (proof-world-pc cut) (allocation-code-address "rt:ensure-stack" origin))
         (equal (proof-world-reg 30 cut) (allocation-cons-address origin 14))
         (equal (proof-world-reg 0 cut) (proof-world-reg 0 before))
         (equal (proof-world-reg 1 cut) (proof-world-reg 1 before))
         (equal (proof-world-reg 8 cut) (+ 16 (proof-stack-top before)))
         (equal (proof-stack-top cut) (proof-stack-top before))
         (equal (allocation-sp cut) save)
         (allocation-cons-fields-p save (proof-world-reg 29 before) (proof-world-reg 30 before) cut)
         (equal (proof-world-regions cut) (proof-world-regions before)))))

(defthm allocation-cons-machine-to-growth
  (implies (and (allocation-cons-machine-entry-p origin before)
                (not (proof-allocation-fits-p :cons 16 before))
                (<= 16 (allocation-sp before))
                (< (+ 16 (proof-stack-top before)) *allocation-word-modulus*)
                (equal cut (allocation-path-end *allocation-cons-growth-path* before)))
           (allocation-cons-growth-edge-p origin before cut))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum
                                     allocation-unsigned-64-of-difference))))

(defun allocation-cons-root-edge-p (origin before cut)
  (let ((top (proof-stack-top before)))
    (and (allocation-machine-state-p cut)
         (not (proof-world-stop cut))
         (equal (proof-world-pc cut) (allocation-code-address "rt:alloc-cells" origin))
         (equal (proof-world-reg 30 cut) (allocation-cons-address origin 18))
         (equal (proof-world-reg 0 cut) 16)
         (equal (proof-stack-top cut) (+ top 16))
         (equal (proof-heap-base cut) (proof-heap-base before))
         (equal (allocation-sp cut) (allocation-sp before))
         (allocation-cons-fields-p top (proof-world-reg 0 before) (proof-world-reg 1 before) cut)
         (equal (allocation-memory cut)
                (allocation-memory
                 (allocation-store-word (+ top 8) (proof-world-reg 1 before)
                   (allocation-store-word top (proof-world-reg 0 before) before)))))))

(defthm allocation-cons-machine-to-allocator
  (implies (and (allocation-code-origin-p origin)
                (allocation-machine-state-p before)
                (not (proof-world-stop before))
                (equal (proof-world-pc before) (allocation-cons-address origin 14))
                (< (+ 16 (proof-stack-top before)) *allocation-word-modulus*)
                (equal cut (allocation-path-end *allocation-cons-root-path* before)))
           (allocation-cons-root-edge-p origin before cut))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum
                                     allocation-unsigned-64-of-difference))))

(defun allocation-cons-reload-address (world)
  (- (proof-stack-top world) 16))

(defun allocation-cons-resumed-return-p (before after)
  (let* ((top (allocation-cons-reload-address before))
         (cell (proof-world-reg 0 before))
         (save (allocation-sp before))
         (first (allocation-load-word top before))
         (second (allocation-load-word (+ top 8) before)))
    (and (not (proof-world-stop after))
         (equal (proof-world-pc after) (allocation-load-word (+ save 8) before))
         (equal (proof-world-reg 30 after) (allocation-load-word (+ save 8) before))
         (equal (proof-world-reg 29 after) (allocation-load-word save before))
         (equal (allocation-sp after) (+ save 16))
         (equal (proof-stack-top after) top)
         (equal (proof-heap-base after) (proof-heap-base before))
         (equal (proof-world-reg 0 after)
                (boymoo-model::a64-unsigned 64 (- cell (proof-heap-base before))))
         (allocation-cons-fields-p cell first second after)
         (equal (allocation-memory after)
                (allocation-memory
                 (allocation-store-word (+ cell 8) second
                   (allocation-store-word cell first before))))
         (equal (proof-world-regions after) (proof-world-regions before))
         (equal (proof-world-replies after) (proof-world-replies before))
         (proof-streams-preserved-p before after)
         (proof-register-frame-p 30 '(0 1 2 25 29 30) before after))))

(defthm allocation-cons-resumed-machine-return
  (let ((cell (proof-world-reg 0 before))
        (save (allocation-sp before)))
    (implies (and (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (<= 16 (proof-stack-top before))
                  (proof-span-p cell 16)
                  (< (+ save 16) *allocation-word-modulus*)
                  (proof-disjoint-p cell (+ cell 16) save (+ save 16))
                  (equal after (allocation-path-end *allocation-cons-return-path* before)))
             (allocation-cons-resumed-return-p before after)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum
                                     allocation-unsigned-64-of-difference))))
