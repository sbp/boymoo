(in-package "BOYMOO-PROOFS")

(include-book "subseq-view")
(include-book "copy-loops")
(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-subseq-empty-list-path*
  ("rt:subseq-checked" 0 4)
  ("rt:subseq-list" 0 1)
  ("rt:subseq-nil" 0 1)
  ("rt:subseq-return" 0 3))

(defthm sequence-subseq-empty-list-return-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (path *sequence-subseq-empty-list-path*)
         (after (sequence-execute path before))
         (last (proof-world-machine after))
         (link (proof-load-word (+ stack 8) machine)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 19 before) 0)
          (equal (proof-world-reg 21 before) 0)
          (unsigned-byte-p 64 (+ stack 32)))
     (and (equal (proof-world-reg 0 after) *proof-nil*)
          (equal (proof-world-reg 19 after) (proof-load-word (+ stack 16) machine))
          (equal (proof-world-reg 20 after) (proof-load-word (+ stack 24) machine))
          (equal (proof-world-reg 21 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-pc after) link)
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp last) (+ stack 32))
          (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine))
          (proof-register-frame-p 29 '(0 1 19 20 21) before after))))
  :hints (("Goal"
           :in-theory (e/d (sequence-execute proof-load-word proof-world-machine)
                           (proof-instruction-effect sequence-signed-word))
           :expand ((:free (limit clobbers first last)
                           (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(local
 (defthm sequence-subseq-zero-list-size-yields-nil
   (implies (and (not (stringp datum)) (equal (sequence-result-size datum start limit) 0))
            (equal (sequence-slice datum start limit) nil))
   :hints (("Goal" :in-theory (e/d (sequence-slice) (sequence-result-size sequence-drop))))))

(defthm sequence-subseq-zero-list-size-source-result
  (implies (and (not (stringp datum))
                (<= (len (sequence-elements datum)) *proof-space-size*)
                (equal (sequence-result-size datum start limit) 0))
           (equal (proof-runtime-value 'subseq (list datum start limit) program)
                  (boymoo-model::core-value nil)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-value boymoo-model::core-primitive)
                    (boymoo-model::core-prelude sequence-core-subseq sequence-slice sequence-result-size
                     sequence-elements))
    :use ((:instance sequence-core-subseq (end limit)))))
  :rule-classes nil)

(defthm sequence-subseq-empty-list-after-size-check
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (path *sequence-subseq-empty-list-path*)
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 19 before) 0)
          (equal (proof-world-reg 21 before) 0)
          (unsigned-byte-p 64 (+ stack 32))
          (not (stringp datum))
          (<= (len (sequence-elements datum)) *proof-space-size*)
          (equal (sequence-result-size datum start limit) 0)
          (proof-machine-value-p *proof-nil* nil before objects packages)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                             objects packages (proof-world-machine after))
                 (boymoo-model::core-prelude 'subseq (list datum start limit))))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-machine-value-p proof-value-p)
                    (proof-world-stop proof-world-reg proof-world-pc proof-world-machine proof-heap-base
                     proof-view proof-load-word proof-register-frame-p proof-segment-p
                     sequence-result-size sequence-slice sequence-elements sequence-execute sequence-instruction-path
                     sequence-core-subseq boymoo-model::core-prelude))
    :use (sequence-subseq-empty-list-return-effects
          (:instance sequence-core-subseq (end limit))
          (:instance sequence-view-of-equal-memory (word *proof-nil*)
                     (base (proof-heap-base before)) (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute *sequence-subseq-empty-list-path* before))))
          (:instance sequence-segment-of-instruction-path
                     (instructions *sequence-subseq-empty-list-path*)
                     (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                                  (proof-world-machine before))))
                     (after (sequence-execute *sequence-subseq-empty-list-path* before))))))
  :rule-classes nil)
