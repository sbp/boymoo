(in-package "BOYMOO-PROOFS")

(include-book "counts")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-byte-iteration-extent
  (implies (and (proof-span-p payload length) (natp index) (< index length))
           (proof-subspan-p (+ payload index) 1 payload (+ payload length))))

(defthm sequence-cons-iteration-extent
  (implies (and (natp count) (natp index) (< index count)
                (proof-span-p first (* 16 count)))
           (proof-subspan-p (+ first (* 16 index)) 16 first (+ first (* 16 count)))))

(defthm sequence-forward-iteration-progress
  (implies (and (natp count) (natp index) (< index count))
           (and (natp (- count (1+ index)))
                (< (- count (1+ index)) (- count index)))))

(defthm sequence-backward-iteration-progress
  (implies (posp count)
           (and (natp (1- count)) (< (1- count) count))))

(sequence-defpath *sequence-subseq-string-read*
  ("rt:subseq-string-loop" 0 7)
  ("rt:subseq-string-store" 0 3))

(sequence-defpath *sequence-subseq-string-pad*
  ("rt:subseq-string-loop" 0 6)
  ("rt:subseq-string-store" 0 3))

(defun sequence-subseq-string-step-path (index start length)
  (if (< (+ start index) length)
      *sequence-subseq-string-read*
    *sequence-subseq-string-pad*))

(defun sequence-subseq-source-byte (index start length source memory)
  (let ((position (+ start index)))
    (if (< position length)
        (boymoo-model::a64-byte (+ source position) memory)
      0)))

(defthm sequence-subseq-string-step-effects
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (index (proof-world-reg 3 before))
         (start (proof-world-reg 20 before))
         (length (proof-world-reg 2 before))
         (count (proof-world-reg 19 before))
         (source (proof-world-reg 1 before))
         (destination (proof-world-reg 7 before))
         (source-index (+ start index))
         (byte (sequence-subseq-source-byte index start length source memory))
         (path (sequence-subseq-string-step-path index start length))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (< index count)
          (unsigned-byte-p 64 source-index)
          (proof-span-p source length)
          (proof-span-p destination count)
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before))))
     (and (equal (proof-world-pc after) (proof-world-pc before))
          (equal (proof-world-reg 3 after) (1+ index))
          (equal (proof-world-reg 1 after) source)
          (equal (proof-world-reg 2 after) length)
          (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
          (equal (proof-world-reg 7 after) destination)
          (equal (proof-world-reg 19 after) count)
          (equal (proof-world-reg 20 after) start)
          (equal (proof-heap-base after) (proof-heap-base before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-write-bytes 1 (+ destination index) byte memory)))))
  :hints (("Goal" :in-theory (e/d (sequence-execute)
                                  (sequence-signed-word sequence-write-one-byte))))
  :rule-classes nil)

(sequence-defpath *sequence-coerce-list-step*
  ("rt:coerce-list-loop" 0 8))

(defthm sequence-coerce-list-step-effects
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (count (proof-world-reg 2 before))
         (source (proof-world-reg 1 before))
         (cell (proof-world-reg 5 before))
         (tail (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (byte (boymoo-model::a64-byte (+ source (1- count)) memory))
         (after (sequence-execute *sequence-coerce-list-step* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (posp count)
          (proof-span-p source count)
          (proof-span-p cell 16)
          (unsigned-byte-p 64 (+ 32 (proof-world-pc before))))
     (and (equal (proof-world-reg 2 after) (1- count))
          (equal (proof-world-reg 0 after) (boymoo-model::a64-unsigned 64 (- cell base)))
          (equal (proof-world-reg 5 after) (boymoo-model::a64-unsigned 64 (+ 16 cell)))
          (equal (proof-world-reg 1 after) source)
          (equal (proof-heap-base after) base)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
          (equal (proof-world-pc after)
                 (if (equal count 1) (+ 32 (proof-world-pc before)) (proof-world-pc before)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-write-bytes
                  8 (+ cell 8) tail
                  (boymoo-model::a64-write-bytes 8 cell (+ 4 (* 8 byte)) memory))))))
  :hints (("Goal" :in-theory (e/d (sequence-execute)
                                  (sequence-signed-word sequence-unsigned-of-difference))
                  :cases ((equal (proof-world-reg 2 before) 1))))
  :rule-classes nil)

(sequence-defpath *sequence-coerce-string-step*
  ("rt:coerce-string-loop" 0 10))

(defun sequence-car-byte (word)
  (if (equal (proof-word-tag word) 4)
      (boymoo-model::a64-unsigned 8
                                 (boymoo-model::a64-unsigned 64 (floor word 8)))
    0))

(defthm sequence-encoded-character-byte
  (implies
   (equal (proof-view-step :word word 0 depth base objects packages machine)
          (proof-value-view datum))
   (equal (sequence-car-byte word) (char-code datum)))
  :hints (("Goal"
           :expand ((proof-view-step :word word 0 depth base objects packages machine))
           :use sequence-even-tags-mark-even-words
           :in-theory (disable sequence-even-tags-mark-even-words
                               proof-symbol-value proof-rational-value
                               proof-complex-value proof-load-string)))
  :rule-classes nil)

(local
 (defthm sequence-character-tag-comparison
   (equal (equal (boymoo-model::a64-unsigned
                  64 (+ -4 (boymoo-model::a64-unsigned 3 word))) 0)
          (equal (boymoo-model::a64-unsigned 3 word) 4))
   :hints (("Goal" :use ((:instance sequence-zero-for-equal-words
                                    (left (boymoo-model::a64-unsigned 3 word)) (right 4)))))))

(defthm sequence-coerce-string-step-effects
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (word (proof-world-reg 4 before))
         (address (proof-pointer-address word (proof-heap-base before)))
         (destination (proof-world-reg 1 before))
         (count (proof-world-reg 2 before))
         (byte (sequence-car-byte (proof-load-word address machine)))
         (after (sequence-execute *sequence-coerce-string-step* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-word-tag word) 0)
          (posp count)
          (proof-span-p address 16)
          (proof-span-p destination count)
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before))))
     (and (equal (proof-world-pc after)
                 (if (equal count 1) (+ 40 (proof-world-pc before)) (proof-world-pc before)))
          (equal (proof-world-reg 2 after) (1- count))
          (equal (proof-world-reg 1 after) (boymoo-model::a64-unsigned 64 (1+ destination)))
          (equal (proof-world-reg 4 after) (proof-load-word (+ address 8) machine))
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-write-bytes 1 destination byte memory)))))
  :hints (("Goal" :in-theory (e/d (sequence-execute)
                                  (sequence-signed-word sequence-write-one-byte))
                  :cases ((equal (proof-world-reg 2 before) 1))))
  :rule-classes nil)

(sequence-defpath *sequence-subseq-list-drop-cell*
  ("rt:subseq-drop" 0 7))

(defthm sequence-subseq-drop-cell-effects
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (word (proof-world-reg 0 before))
         (count (proof-world-reg 20 before))
         (after (sequence-execute *sequence-subseq-list-drop-cell* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-word-tag word) 0)
          (posp count)
          (proof-span-p (+ base word) 16)
          (unsigned-byte-p 64 (+ 28 (proof-world-pc before))))
     (and (equal (proof-world-pc after) (proof-world-pc before))
          (equal (proof-world-reg 20 after) (1- count))
          (equal (proof-world-reg 0 after) (proof-load-word (+ base word 8) machine))
          (equal (proof-heap-base after) base)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)))
  :rule-classes nil)

(sequence-defpath *sequence-subseq-list-copy-cell*
  ("rt:subseq-list-fill" 0 5)
  ("rt:subseq-list-store" 0 6))

(sequence-defpath *sequence-subseq-list-copy-nil*
  ("rt:subseq-list-fill" 0 3)
  ("rt:subseq-list-store" 0 6))

(defthm sequence-subseq-list-step-effects
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (word (proof-world-reg 2 before))
         (cell (proof-world-reg 1 before))
         (base (proof-heap-base before))
         (address (proof-pointer-address word base))
         (count (proof-world-reg 19 before))
         (cons (equal (proof-word-tag word) 0))
         (path (if cons *sequence-subseq-list-copy-cell* *sequence-subseq-list-copy-nil*))
         (after (sequence-execute path before))
         (first (if cons (proof-load-word address machine) *proof-nil*))
         (rest (if (equal count 1) *proof-nil*
                 (boymoo-model::a64-unsigned 64 (- (+ 16 cell) base)))))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 5 before) *proof-nil*)
          (posp count)
          (unsigned-byte-p 64 (+ cell 16))
          (implies cons (proof-span-p address 16))
          (unsigned-byte-p 64 (+ 44 (proof-world-pc before))))
     (and (equal (proof-world-pc after)
                 (if (equal count 1) (+ 44 (proof-world-pc before)) (proof-world-pc before)))
          (equal (proof-world-reg 19 after) (1- count))
          (equal (proof-world-reg 1 after) (+ 16 cell))
          (equal (proof-world-reg 2 after)
                 (if cons (proof-load-word (+ 8 address) machine) word))
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 5 after) *proof-nil*)
          (equal (proof-heap-base after) base)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-write-bytes
                  8 (+ 8 cell) rest
                  (boymoo-model::a64-write-bytes 8 cell first memory))))))
  :hints (("Goal" :in-theory (e/d (sequence-execute)
                                  (sequence-signed-word sequence-unsigned-of-difference))
                  :cases ((equal (proof-world-reg 19 before) 1))))
  :rule-classes nil)

(sequence-defpath *sequence-subseq-size-check*
  ("rt:subseq-checked" 0 3))

(defconst *sequence-subseq-check-offset* (sequence-offset "rt:subseq-checked"))
(defconst *sequence-datum-size-offset* (sequence-offset "rt:datum-size"))

(defthm sequence-subseq-size-branch
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-subseq-size-check* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (<= *proof-space-size* (proof-world-reg 19 before))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-check-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-datum-size-offset*)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-datum-size-offset*))
          (equal (proof-world-stop after) (proof-world-stop before)))))
  :hints (("Goal" :in-theory (e/d (sequence-execute) (sequence-signed-word))))
  :rule-classes nil)

(defthm sequence-subseq-size-cutpoint
  (let* ((machine (proof-world-machine before))
         (limit (sequence-runtime-count (- (sequence-end end datum) start)))
         (size (sequence-result-size datum start end))
         (cuts (list (+ image-base *sequence-datum-size-offset*)))
         (after (sequence-execute *sequence-subseq-size-check* before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 19 before) limit)
          (<= *proof-space-size* limit)
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-check-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-datum-size-offset*))
          (sequence-instruction-path *sequence-subseq-size-check* cuts before))
     (and (proof-segment-p (len *sequence-subseq-size-check*) cuts before :cut after)
          (proof-resource-bound-p (if (stringp datum) :string-size :allocation-size)
                                  (if (stringp datum) size (* 16 size)) after))))
  :hints
  (("Goal"
    :in-theory (disable proof-world-reg proof-world-pc proof-world-machine proof-segment-p
                        proof-resource-bound-p sequence-end sequence-runtime-count
                        sequence-result-size)
    :use
    (sequence-subseq-size-branch
     (:instance sequence-subseq-result-size-limit
                (world (sequence-execute *sequence-subseq-size-check* before)))
     (:instance sequence-segment-of-instruction-path
                (instructions *sequence-subseq-size-check*)
                (cuts (list (+ image-base *sequence-datum-size-offset*)))
                (after (sequence-execute *sequence-subseq-size-check* before))))))
  :rule-classes nil)
