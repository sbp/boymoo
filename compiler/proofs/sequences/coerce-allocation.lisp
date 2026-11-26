(in-package "BOYMOO-PROOFS")

(include-book "coerce-dispatch")
(include-book "constructor-calls")
(include-book "register-only")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-coerce-grow-offset* (sequence-offset "rt:ensure-stack"))
(defconst *sequence-coerce-allocate-cells-offset* (sequence-offset "rt:alloc-cells"))

(sequence-defpath *sequence-coerce-list-grow-call*
  ("prim:COMMON-LISP::COERCE" 26 3))

(sequence-defpath *sequence-coerce-string-grow-call*
  ("rt:coerce-to-string" 4 2))

(sequence-defpath *sequence-coerce-reserve-list-call*
  ("prim:COMMON-LISP::COERCE" 29 4))

(sequence-defpath *sequence-coerce-reserve-string-call*
  ("rt:coerce-to-string" 6 4))

(defun sequence-coerce-growth-call-path (list-result)
  (if list-result *sequence-coerce-list-grow-call* *sequence-coerce-string-grow-call*))

(defun sequence-coerce-construction-call-path (list-result)
  (if list-result *sequence-coerce-reserve-list-call* *sequence-coerce-reserve-string-call*))

(defthm sequence-coerce-copy-requests-root-space
  (let* ((machine (proof-world-machine before))
         (path (sequence-coerce-growth-call-path list-result))
         (offset (if list-result *sequence-coerce-offset* *sequence-coerce-string-offset*))
         (pc (+ image-base offset (if list-result 104 16)))
         (link (+ pc (* 4 (len path))))
         (required (+ 8 (proof-stack-top before)))
         (target (+ image-base *sequence-coerce-grow-offset*))
         (after (sequence-execute path before))
         (last (proof-world-machine after)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (posp (proof-world-reg 2 before))
          (natp image-base) (equal (proof-world-pc before) pc)
          (unsigned-byte-p 64 link) (unsigned-byte-p 64 required)
          (sequence-instruction-path path (list target) before))
     (and (proof-segment-p (len path) (list target) before :cut after)
          (equal (proof-world-reg 8 after) required)
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 2 after) (proof-world-reg 2 before))
          (equal (proof-stack-top after) (proof-stack-top before))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine)))))
  :hints
  (("Goal"
    :cases (list-result)
    :in-theory (e/d (sequence-execute proof-world-machine proof-world-reg proof-stack-top)
                    (proof-instruction-effect))
    :use ((:instance sequence-segment-of-instruction-path
                     (instructions (sequence-coerce-growth-call-path list-result))
                     (cuts (list (+ image-base *sequence-coerce-grow-offset*)))
                     (after (sequence-execute (sequence-coerce-growth-call-path list-result) before))))))
  :rule-classes nil)

(local
 (defthm sequence-coerce-construction-call-effects
   (let* ((machine (proof-world-machine before))
          (path (sequence-coerce-construction-call-path list-result))
          (offset (if list-result *sequence-coerce-offset* *sequence-coerce-string-offset*))
          (pc (+ image-base offset (if list-result 116 24)))
          (link (+ pc (* 4 (len path))))
          (top (proof-stack-top before))
          (source (proof-world-reg 0 before))
          (size (proof-world-reg 2 before))
          (target (+ image-base (if list-result *sequence-coerce-allocate-cells-offset*
                                   *sequence-new-string-offset*)))
          (after (sequence-execute path before))
          (last (proof-world-machine after)))
     (implies
      (and (consp (boymoo-model::a64-registers machine))
           (natp image-base) (equal (proof-world-pc before) pc)
           (unsigned-byte-p 64 link) (unsigned-byte-p 64 (+ 8 top))
           (unsigned-byte-p 32 size))
      (and (equal (proof-world-pc after) target)
           (equal (proof-world-reg 30 after) link)
           (equal (proof-world-reg 0 after) (if list-result (* 16 size) size))
           (equal (proof-stack-top after) (+ 8 top))
           (equal (proof-heap-base after) (proof-heap-base before))
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (proof-load-word top last) source)
           (equal (boymoo-model::a64-memory last)
                  (boymoo-model::a64-write-bytes 8 top source (boymoo-model::a64-memory machine))))))
   :hints
   (("Goal"
     :cases (list-result)
     :in-theory (e/d (sequence-execute proof-world-machine proof-world-reg proof-stack-top
                      proof-heap-base proof-load-word)
                     (proof-instruction-effect sequence-signed-word boymoo-model::a64-exec-bitfield))
     :use ((:instance sequence-read-after-own-write (count 8) (address (proof-stack-top before))
                      (value (proof-world-reg 0 before))
                      (memory (boymoo-model::a64-memory (proof-world-machine before)))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-growth-preserves-arguments
   (implies (proof-grow-return-p "rt:ensure-stack" required before returned old-objects new-objects packages)
            (and (not (proof-world-stop returned))
                 (equal (proof-world-pc returned) (proof-world-reg 30 before))
                 (equal (proof-world-reg 0 returned) (proof-world-reg 0 before))
                 (equal (proof-world-reg 2 returned) (proof-world-reg 2 before))
                 (equal (proof-stack-top returned) (proof-stack-top before))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-grow-return-p proof-frame-return-p proof-stack-top)
                     (proof-register-frame-p proof-preserved-heap-p proof-fixed-heap-p
                      proof-grow-limit proof-stack-limit proof-world-reg))
     :use ((:instance sequence-register-in-frame (limit 30) (clobbers '(9 10 11 12 24))
                      (register 0) (after returned))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(9 10 11 12 24))
                      (register 2) (after returned))
           (:instance sequence-register-in-frame (limit 30) (clobbers '(9 10 11 12 24))
                      (register 25) (after returned)))))
   :rule-classes nil))

(defthm sequence-coerce-requests-construction-after-growth
  (let* ((path (sequence-coerce-construction-call-path list-result))
         (offset (if list-result *sequence-coerce-offset* *sequence-coerce-string-offset*))
         (pc (+ image-base offset (if list-result 116 24)))
         (required (+ 8 (proof-stack-top before)))
         (size (proof-world-reg 2 before))
         (target (+ image-base (if list-result *sequence-coerce-allocate-cells-offset*
                                  *sequence-new-string-offset*)))
         (after (sequence-execute path returned)))
    (implies
     (and (proof-grow-return-p "rt:ensure-stack" required before returned old-objects new-objects packages)
          (equal (proof-world-reg 30 before) pc)
          (natp image-base) (unsigned-byte-p 64 (+ pc (* 4 (len path))))
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (unsigned-byte-p 64 required)
          (unsigned-byte-p 32 size)
          (sequence-instruction-path path (list target) returned))
     (and (proof-segment-p (len path) (list target) returned :cut after)
          (equal (proof-world-reg 0 after) (if list-result (* 16 size) size))
          (equal (proof-world-reg 30 after) (+ pc (* 4 (len path))))
          (equal (proof-stack-top after) required)
          (equal (proof-load-word (proof-stack-top before) (proof-world-machine after))
                 (proof-world-reg 0 before)))))
  :hints
  (("Goal"
    :in-theory (disable proof-grow-return-p proof-segment-p proof-world-machine proof-world-pc
                        proof-world-reg proof-world-stop proof-stack-top proof-heap-base proof-load-word
                        sequence-execute sequence-instruction-path sequence-coerce-construction-call-path)
    :use ((:instance sequence-coerce-growth-preserves-arguments (required (+ 8 (proof-stack-top before))))
          (:instance sequence-coerce-construction-call-effects (before returned))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-coerce-construction-call-path list-result)) (before returned)
                     (cuts (list (+ image-base (if list-result *sequence-coerce-allocate-cells-offset*
                                                  *sequence-new-string-offset*))))
                     (after (sequence-execute (sequence-coerce-construction-call-path list-result) returned))))))
  :rule-classes nil)
