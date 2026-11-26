(in-package "BOYMOO-PROOFS")

(include-book "register-only")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-coerce-list-return*
  ("rt:coerce-list-loop" 8 2))

(sequence-defpath *sequence-coerce-string-return*
  ("rt:coerce-string-loop" 10 2))

(sequence-defpath *sequence-subseq-return-string*
  ("rt:subseq-string-done" 0 2)
  ("rt:subseq-return" 0 3))

(sequence-defpath *sequence-subseq-return-list*
  ("rt:subseq-list-store" 6 1)
  ("rt:subseq-return" 0 3))

(defthm sequence-coerce-copy-epilogues-use-the-same-instructions
  (equal *sequence-coerce-list-return* *sequence-coerce-string-return*)
  :rule-classes nil)

(local
 (defthm sequence-coerce-copy-return-effects
   (let* ((machine (proof-world-machine before))
          (stack (boymoo-model::a64-sp machine))
          (after (sequence-execute *sequence-coerce-list-return* before))
          (last (proof-world-machine after)))
     (implies (and (consp (boymoo-model::a64-registers machine))
                   (unsigned-byte-p 64 (+ stack 16)))
              (and (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                   (equal (proof-world-reg 29 after) (proof-load-word stack machine))
                   (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
                   (equal (proof-world-pc after) (proof-load-word (+ stack 8) machine))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (equal (boymoo-model::a64-sp last) (+ stack 16))
                   (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine)))))
   :hints (("Goal"
            :in-theory (e/d (sequence-execute proof-world-machine proof-load-word proof-heap-base)
                            (proof-instruction-effect))))
   :rule-classes nil))

(defthm sequence-coerce-copy-returns-represented-result
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (path *sequence-coerce-list-return*)
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 64 (+ stack 16))
          (proof-reg-value-p 0 result before objects packages)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-reg-value-p 0 result after objects packages)
          (equal (proof-world-reg 29 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                    (proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                     proof-view proof-value-p proof-load-word sequence-execute sequence-instruction-path
                     proof-segment-p))
    :use (sequence-coerce-copy-return-effects
          (:instance sequence-representation-on-identical-memory
                     (datum result) (base (proof-heap-base before)) (word (proof-world-reg 0 before))
                     (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute *sequence-coerce-list-return* before))))
          (:instance sequence-segment-of-instruction-path
                     (instructions *sequence-coerce-list-return*)
                     (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                                  (proof-world-machine before))))
                     (after (sequence-execute *sequence-coerce-list-return* before))))))
  :rule-classes nil)

(defun sequence-subseq-copy-return-path (string-result)
  (if string-result *sequence-subseq-return-string* *sequence-subseq-return-list*))

(local
 (defthm sequence-subseq-copy-return-effects
   (let* ((machine (proof-world-machine before))
          (stack (boymoo-model::a64-sp machine))
          (path (sequence-subseq-copy-return-path string-result))
          (after (sequence-execute path before))
          (last (proof-world-machine after)))
     (implies (and (consp (boymoo-model::a64-registers machine))
                   (unsigned-byte-p 64 (+ stack 32)))
              (and (equal (proof-world-reg 0 after) (proof-world-reg (if string-result 6 0) before))
                   (equal (proof-world-reg 19 after) (proof-load-word (+ stack 16) machine))
                   (equal (proof-world-reg 20 after) (proof-load-word (+ stack 24) machine))
                   (equal (proof-world-reg 21 after) (proof-load-word stack machine))
                   (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
                   (equal (proof-world-pc after) (proof-load-word (+ stack 8) machine))
                   (equal (proof-world-stop after) (proof-world-stop before))
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (equal (boymoo-model::a64-sp last) (+ stack 32))
                   (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine)))))
   :hints (("Goal"
            :in-theory (e/d (sequence-execute proof-world-machine proof-load-word proof-heap-base)
                            (proof-instruction-effect))))
   :rule-classes nil))

(defthm sequence-subseq-copy-returns-represented-result
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (path (sequence-subseq-copy-return-path string-result))
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 64 (+ stack 32))
          (proof-reg-value-p (if string-result 6 0) result before objects packages)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-reg-value-p 0 result after objects packages)
          (equal (proof-world-reg 19 after) (proof-load-word (+ stack 16) machine))
          (equal (proof-world-reg 20 after) (proof-load-word (+ stack 24) machine))
          (equal (proof-world-reg 21 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 32)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                    (proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                     proof-view proof-value-p proof-load-word sequence-execute sequence-subseq-copy-return-path
                     sequence-instruction-path proof-segment-p))
    :use (sequence-subseq-copy-return-effects
          (:instance sequence-representation-on-identical-memory
                     (datum result) (base (proof-heap-base before))
                     (word (proof-world-reg (if string-result 6 0) before))
                     (first (proof-world-machine before))
                     (last (proof-world-machine (sequence-execute (sequence-subseq-copy-return-path string-result)
                                                                 before))))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-subseq-copy-return-path string-result))
                     (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                                  (proof-world-machine before))))
                     (after (sequence-execute (sequence-subseq-copy-return-path string-result) before))))))
  :rule-classes nil)
