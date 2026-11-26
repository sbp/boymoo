(in-package "BOYMOO-PROOFS")

(include-book "helpers")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-coerce-list-reload*
  ("rt:coerce-no-list" -14 2))

(sequence-defpath *sequence-coerce-string-reload*
  ("rt:coerce-to-string" 10 2))

(sequence-defpath *sequence-subseq-string-reload*
  ("rt:subseq-checked" 12 2))

(sequence-defpath *sequence-subseq-list-reload*
  ("rt:subseq-list-allocate" 8 2))

(sequence-defpath *sequence-subseq-numeric-reload*
  ("rt:subseq-checked" -2 2))

(defun sequence-reload-path (operation)
  (case operation
    (:coerce-list *sequence-coerce-list-reload*)
    (:coerce-string *sequence-coerce-string-reload*)
    (:subseq-string *sequence-subseq-string-reload*)
    (:subseq-list *sequence-subseq-list-reload*)
    (:subseq-numeric *sequence-subseq-numeric-reload*)
    (otherwise nil)))

(defun sequence-reload-register (operation)
  (case operation
    (:coerce-string 4)
    (:subseq-list 2)
    (otherwise 0)))

(defun sequence-reload-slot (operation world)
  (- (proof-stack-top world) (if (eq operation :subseq-numeric) 16 8)))

(defthm sequence-root-reload-effects
  (let* ((machine (proof-world-machine before))
         (path (sequence-reload-path operation))
         (slot (sequence-reload-slot operation before))
         (after (sequence-execute path before)))
    (implies (and (consp path)
                  (consp (boymoo-model::a64-registers machine))
                  (natp slot)
                  (unsigned-byte-p 64 (+ 8 (proof-world-pc before))))
             (and (equal (proof-world-pc after) (+ 8 (proof-world-pc before)))
                  (equal (proof-stack-top after) slot)
                  (equal (proof-world-reg (sequence-reload-register operation) after)
                         (proof-load-word slot machine))
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (equal (proof-world-regions after) (proof-world-regions before))
                  (equal (proof-heap-base after) (proof-heap-base before))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)))
  :rule-classes nil)

(defthm sequence-reloading-preserved-root
  (let* ((old (proof-world-machine before))
         (new (proof-world-machine returned))
         (base (proof-heap-base before))
         (start (proof-stack-base before))
         (slot (+ start (* 8 index)))
         (path (sequence-reload-path operation))
         (reloaded (sequence-execute path returned))
         (register (sequence-reload-register operation)))
    (implies
     (and (natp index) (natp count) (< index count) (integerp start)
          (natp slot)
          (proof-stack-views count start base old-objects packages old)
          (equal (proof-stack-views count start base old-objects packages old)
                 (proof-stack-views count start base new-objects packages new))
          (equal base (proof-heap-base returned))
          (proof-value-p (proof-load-word slot old) datum base old-objects packages old)
          (consp path)
          (consp (boymoo-model::a64-registers new))
          (unsigned-byte-p 64 (+ 8 (proof-world-pc returned)))
          (equal (sequence-reload-slot operation returned) slot))
     (proof-value-p (proof-world-reg register reloaded) datum
                    base new-objects packages new)))
  :hints
  (("Goal"
    :in-theory (disable sequence-reload-path sequence-reload-register sequence-reload-slot
                        proof-view proof-world-reg proof-heap-base proof-world-machine
                        proof-stack-base proof-stack-views proof-load-word)
    :use ((:instance sequence-selected-root-view-preserved (after returned))
          (:instance sequence-root-reload-effects (before returned)))))
  :rule-classes nil)
