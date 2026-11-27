(in-package "BOYMOO-PROOFS")

(include-book "coerce-list")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-positive-count-is-at-least-one
   (implies (posp count) (<= 1 count))
   :hints (("Goal" :use ((:instance sequence-floor-unique
                                    (value count) (divisor 1) (quotient 0))
                         (:instance sequence-floor-unique
                                    (value count) (divisor 1) (quotient count)))))
   :rule-classes nil))

(defthm sequence-coerce-list-copy-keeps-outside-reads
  (implies (and (natp count)
                (proof-span-p cell (* 16 count))
                (proof-span-p address width)
                (proof-disjoint-p address (+ address width) cell (+ cell (* 16 count))))
           (equal (boymoo-model::a64-read-bytes
                   width address (sequence-coerce-list-copy-memory count source cell tail base memory))
                  (boymoo-model::a64-read-bytes width address memory)))
  :hints
  (("Goal"
    :in-theory (enable (:induction sequence-coerce-list-copy-memory))
    :induct (sequence-coerce-list-copy-memory count source cell tail base memory)
    :expand ((sequence-coerce-list-copy-memory count source cell tail base memory)))
   ("Subgoal *1/2"
    :cases ((equal count 1))
    :expand ((sequence-coerce-list-copy-memory count source cell tail base memory)
             (:free (source cell tail base memory)
                    (sequence-coerce-list-copy-memory 0 source cell tail base memory))
             (:free (source cell tail base memory)
                    (sequence-coerce-list-copy-memory 1 source cell tail base memory)))))
  :rule-classes nil)

(local
 (defthm sequence-coerce-first-cell-after-copy
   (let* ((byte (boymoo-model::a64-byte (+ source (1- count)) memory))
          (finished (sequence-coerce-list-copy-memory count source cell tail base memory)))
     (implies (and (posp count) (integerp source)
                   (proof-span-p cell (* 16 count))
                   (unsigned-byte-p 64 tail))
              (and (equal (boymoo-model::a64-read-bytes 8 cell finished) (+ 4 (* 8 byte)))
                   (equal (boymoo-model::a64-read-bytes 8 (+ cell 8) finished) tail))))
   :hints
   (("Goal"
     :in-theory (disable (:definition sequence-coerce-list-copy-memory))
     :expand ((sequence-coerce-list-copy-memory count source cell tail base memory))
     :cases ((equal count 1))
     :use (sequence-positive-count-is-at-least-one
           (:instance sequence-cell-write-rest-word
                      (address cell) (rest tail)
                      (first (+ 4 (* 8 (boymoo-model::a64-byte (+ source (1- count)) memory)))))
           (:instance sequence-coerce-list-copy-keeps-outside-reads
                      (count (1- count)) (cell (+ cell 16)) (tail (sequence-cell-word cell base))
                      (address cell) (width 8)
                      (memory (sequence-write-cell
                               cell (+ 4 (* 8 (boymoo-model::a64-byte (+ source (1- count)) memory)))
                               tail memory)))
           (:instance sequence-coerce-list-copy-keeps-outside-reads
                      (count (1- count)) (cell (+ cell 16)) (tail (sequence-cell-word cell base))
                      (address (+ cell 8)) (width 8)
                      (memory (sequence-write-cell
                               cell (+ 4 (* 8 (boymoo-model::a64-byte (+ source (1- count)) memory)))
                               tail memory)))))
    ("Subgoal 1"
     :expand ((sequence-coerce-list-copy-memory 1 source cell tail base memory)
              (:free (source cell tail base memory)
                     (sequence-coerce-list-copy-memory 0 source cell tail base memory)))))
   :rule-classes nil))

(defun sequence-reverse-cell-cdr (index cell tail base)
  (if (zp index)
      tail
    (sequence-cell-word (+ cell (* 16 (1- index))) base)))

(local
 (defun sequence-reverse-cell-copy-induction (count index source cell tail base memory)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (cons tail memory)
     (sequence-reverse-cell-copy-induction
      (1- count) (1- index) source (+ cell 16) (sequence-cell-word cell base) base
      (sequence-write-cell
       cell (+ 4 (* 8 (boymoo-model::a64-byte (+ source (1- count)) memory)))
       tail memory)))))

(defthm sequence-coerce-list-cell-contents
  (let* ((finished (sequence-coerce-list-copy-memory count source cell tail base memory))
         (address (+ cell (* 16 index)))
         (byte (boymoo-model::a64-byte (+ source count (- index) -1) memory)))
    (implies (and (natp index) (natp count) (< index count)
                  (proof-span-p source count)
                  (proof-span-p cell (* 16 count))
                  (unsigned-byte-p 64 tail)
                  (proof-disjoint-p source (+ source count) cell (+ cell (* 16 count))))
             (and (equal (boymoo-model::a64-read-bytes 8 address finished) (+ 4 (* 8 byte)))
                  (equal (boymoo-model::a64-read-bytes 8 (+ address 8) finished)
                         (sequence-reverse-cell-cdr index cell tail base)))))
  :hints
  (("Goal"
    :in-theory (disable (:definition sequence-coerce-list-copy-memory))
    :induct (sequence-reverse-cell-copy-induction count index source cell tail base memory))
   ("Subgoal *1/1"
    :use sequence-coerce-first-cell-after-copy)
   ("Subgoal *1/2"
    :expand ((sequence-coerce-list-copy-memory count source cell tail base memory))
    :cases ((equal index 1))
    :use ((:instance sequence-cell-write-keeps-other-byte
                     (address (+ source count (- index) -1))
                     (first (+ 4 (* 8 (boymoo-model::a64-byte (+ source (1- count)) memory))))
                     (rest tail)))))
  :rule-classes nil)
