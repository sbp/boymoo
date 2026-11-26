(in-package "BOYMOO-PROOFS")

(include-book "frame-memory")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-write-cell (address first rest memory)
  (boymoo-model::a64-write-bytes
   8 (+ address 8) rest
   (boymoo-model::a64-write-bytes 8 address first memory)))

(defthm sequence-cell-write-first-word
  (implies (and (proof-span-p address 16) (unsigned-byte-p 64 first))
           (equal (boymoo-model::a64-read-bytes
                   8 address (sequence-write-cell address first rest memory))
                  first))
  :hints
  (("Goal"
    :use ((:instance sequence-read-outside-write
                     (start (+ address 8)) (count 8) (size 8) (value rest)
                     (memory (boymoo-model::a64-write-bytes 8 address first memory)))))))

(defthm sequence-cell-write-rest-word
  (implies (and (proof-span-p address 16) (unsigned-byte-p 64 rest))
           (equal (boymoo-model::a64-read-bytes
                   8 (+ address 8) (sequence-write-cell address first rest memory))
                  rest)))

(defthm sequence-cell-write-keeps-other-reads
  (implies (and (proof-span-p cell 16) (proof-span-p address width)
                (proof-disjoint-p address (+ address width) cell (+ cell 16)))
           (equal (boymoo-model::a64-read-bytes
                   width address (sequence-write-cell cell first rest memory))
                  (boymoo-model::a64-read-bytes width address memory))))

(defthm sequence-cell-write-keeps-other-byte
  (implies (and (proof-span-p cell 16) (unsigned-byte-p 64 address)
                (or (< address cell) (<= (+ cell 16) address)))
           (equal (boymoo-model::a64-byte address (sequence-write-cell cell first rest memory))
                  (boymoo-model::a64-byte address memory))))

(in-theory (disable sequence-write-cell))
