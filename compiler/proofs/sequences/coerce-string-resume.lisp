(in-package "BOYMOO-PROOFS")

(include-book "coerce-dispatch")
(include-book "root-prefix")
(include-book "roots")
(include-book "register-only")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-string-constructor-preserves-root-slot
  (let* ((top (proof-stack-top before))
         (slot (+ (proof-stack-base before) (* 8 index))))
    (implies
     (and (proof-string-constructor-return-p length before after old-objects new-objects packages)
          (natp index) (< index (sequence-prefix-length top before))
          (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                 datum before old-objects packages))
     (and (equal (proof-stack-top after) top)
          (not (proof-world-stop after))
          (equal (proof-world-pc after) (proof-world-reg 30 before))
          (proof-machine-value-p (proof-load-word slot (proof-world-machine after))
                                 datum after new-objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-string-constructor-return-p proof-frame-return-p proof-preserved-heap-p
                     proof-heap-frame-p proof-stack-top)
                    (proof-heap-p proof-string-result-p proof-prefix-preserved-p proof-register-frame-p
                     proof-machine-value-p proof-heap-base proof-stack-base proof-world-reg
                     proof-world-machine proof-load-word sequence-prefix-length))
    :use ((:instance sequence-root-view-in-preserved-prefix (top (proof-stack-top before)))
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers (append *proof-volatile-registers* '(26 27))) (register 25)))))
  :rule-classes nil)

(local
 (defthm sequence-coerce-string-reload-keeps-output-registers
   (let ((after (sequence-execute *sequence-coerce-string-reload* before)))
     (implies (consp (boymoo-model::a64-registers (proof-world-machine before)))
              (and (consp (boymoo-model::a64-registers (proof-world-machine after)))
                   (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                   (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                   (equal (proof-world-reg 2 after) (proof-world-reg 2 before)))))
   :hints (("Goal"
            :in-theory (e/d (sequence-execute proof-world-machine proof-load-word)
                            (proof-instruction-effect))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-string-reload-keeps-result
   (let* ((path *sequence-coerce-string-reload*)
          (after (sequence-execute path before)))
     (implies (and (proof-string-result-p length before objects packages)
                   (consp (boymoo-model::a64-registers (proof-world-machine before)))
                   (natp (- (proof-stack-top before) 8))
                   (unsigned-byte-p 64 (+ 8 (proof-world-pc before))))
              (proof-string-result-p length after objects packages)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-string-result-p)
                     (proof-world-machine proof-world-reg proof-world-pc proof-world-regions
                      proof-world-stop proof-stack-top proof-heap-base proof-view proof-load-word
                      proof-pointer-address proof-covered-p sequence-execute))
     :use (sequence-coerce-string-reload-keeps-output-registers
           (:instance sequence-root-reload-effects (operation :coerce-string))
           (:instance sequence-view-of-equal-memory
                      (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                      (first (proof-world-machine before))
                      (last (proof-world-machine (sequence-execute *sequence-coerce-string-reload* before)))))))
   :rule-classes nil))

(defthm sequence-coerce-string-ready-from-constructor
  (let* ((length (len datum))
         (path *sequence-coerce-string-reload*)
         (link (+ image-base *sequence-coerce-string-offset* 40))
         (target (+ image-base *sequence-coerce-string-offset* 48))
         (slot (+ (proof-stack-base before) (* 8 index)))
         (after (sequence-execute path returned)))
    (implies
     (and (consp datum)
          (proof-string-constructor-return-p length before returned old-objects new-objects packages)
          (equal (proof-world-reg 30 before) link)
          (natp index) (< index (sequence-prefix-length (proof-stack-top before) before))
          (natp slot) (equal slot (- (proof-stack-top before) 8))
          (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                 datum before old-objects packages)
          (natp image-base) (unsigned-byte-p 64 target)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path path (list target) returned))
     (and (proof-segment-p (len path) (list target) returned :cut after)
          (equal (proof-stack-top after) slot)
          (proof-string-result-p length after new-objects packages)
          (proof-reg-value-p 4 datum after new-objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-string-constructor-return-p proof-reg-value-p proof-machine-value-p)
                    (proof-string-result-p proof-view proof-value-p proof-preserved-heap-p
                     proof-frame-return-p proof-heap-p proof-segment-p proof-world-machine
                     proof-world-reg proof-world-pc proof-world-stop proof-heap-base proof-stack-top
                     proof-stack-base proof-load-word sequence-prefix-length sequence-execute
                     sequence-instruction-path))
    :use ((:instance sequence-string-constructor-preserves-root-slot (length (len datum)) (after returned))
          (:instance sequence-root-reload-effects (operation :coerce-string) (before returned))
          (:instance sequence-coerce-string-reload-keeps-result (length (len datum))
                     (before returned) (objects new-objects))
          (:instance sequence-representation-on-identical-memory (datum datum)
                     (base (proof-heap-base returned))
                     (objects new-objects)
                     (word (proof-load-word (+ (proof-stack-base before) (* 8 index))
                                            (proof-world-machine returned)))
                     (first (proof-world-machine returned))
                     (last (proof-world-machine (sequence-execute *sequence-coerce-string-reload* returned))))
          (:instance sequence-segment-of-instruction-path (instructions *sequence-coerce-string-reload*)
                     (before returned) (cuts (list (+ image-base *sequence-coerce-string-offset* 48)))
                     (after (sequence-execute *sequence-coerce-string-reload* returned))))))
  :rule-classes nil)
