(in-package "BOYMOO-PROOFS")

(include-book "copy-loops")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-subseq-string-end-test*
  ("rt:subseq-string-loop" 0 2))

(defun sequence-subseq-string-copy-path (remaining index start length)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      *sequence-subseq-string-end-test*
    (append (sequence-subseq-string-step-path index start length)
            (sequence-subseq-string-copy-path (1- remaining) (1+ index) start length))))

(defun sequence-subseq-string-copy-memory (remaining index start length source destination memory)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      memory
    (sequence-subseq-string-copy-memory
     (1- remaining) (1+ index) start length source destination
     (boymoo-model::a64-write-bytes
      1 (+ destination index) (sequence-subseq-source-byte index start length source memory)
      memory))))

(defthm sequence-subseq-string-end-effects
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-subseq-string-end-test* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (<= (proof-world-reg 19 before) (proof-world-reg 3 before))
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before))))
     (and (equal (proof-world-pc after) (+ 40 (proof-world-pc before)))
          (equal (proof-world-reg 3 after) (proof-world-reg 3 before))
          (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (e/d (sequence-execute) (sequence-signed-word))))
  :rule-classes nil)

(local
 (defun sequence-string-copy-induction (remaining before)
   (declare (xargs :measure (nfix remaining)))
   (if (zp remaining)
       before
     (sequence-string-copy-induction
      (1- remaining)
      (sequence-execute
       (sequence-subseq-string-step-path (proof-world-reg 3 before)
                                         (proof-world-reg 20 before)
                                         (proof-world-reg 2 before))
       before)))))

(local
 (defthm sequence-string-copy-world-reg-natural
   (natp (proof-world-reg register world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-subseq-copy-path-when-positive
   (implies (posp remaining)
            (equal (sequence-subseq-string-copy-path remaining index start length)
                   (append (sequence-subseq-string-step-path index start length)
                           (sequence-subseq-string-copy-path
                            (1- remaining) (1+ index) start length))))
   :hints (("Goal" :expand ((sequence-subseq-string-copy-path remaining index start length))))))

(local
 (defthm sequence-subseq-copy-memory-when-positive
   (implies (posp remaining)
            (equal (sequence-subseq-string-copy-memory
                    remaining index start length source destination memory)
                   (sequence-subseq-string-copy-memory
                    (1- remaining) (1+ index) start length source destination
                    (boymoo-model::a64-write-bytes
                     1 (+ destination index)
                     (sequence-subseq-source-byte index start length source memory) memory))))
   :hints (("Goal" :expand ((sequence-subseq-string-copy-memory
                             remaining index start length source destination memory))))))

(defthm sequence-subseq-string-copy-effects
  (let* ((machine (proof-world-machine before))
         (index (proof-world-reg 3 before))
         (start (proof-world-reg 20 before))
         (length (proof-world-reg 2 before))
         (count (proof-world-reg 19 before))
         (source (proof-world-reg 1 before))
         (destination (proof-world-reg 7 before))
         (memory (boymoo-model::a64-memory machine))
         (path (sequence-subseq-string-copy-path remaining index start length))
         (after (sequence-execute path before)))
    (implies
     (and (natp remaining)
          (equal (+ index remaining) count)
          (consp (boymoo-model::a64-registers machine))
          (<= (+ start count) (expt 2 64))
          (proof-span-p source length)
          (proof-span-p destination count)
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before))))
     (and (equal (proof-world-pc after) (+ 40 (proof-world-pc before)))
          (equal (proof-world-reg 3 after) count)
          (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (sequence-subseq-string-copy-memory
                  remaining index start length source destination memory)))))
  :hints
  (("Goal"
    :induct (sequence-string-copy-induction remaining before)
    :in-theory (disable acl2::binary-append proof-span-p
                        sequence-subseq-source-byte sequence-subseq-string-step-path
                        (:definition sequence-subseq-string-copy-path)
                        (:definition sequence-subseq-string-copy-memory)
                        proof-world-machine proof-world-reg proof-world-pc))
   ("Subgoal *1/1"
    :use sequence-subseq-string-end-effects
    :expand ((:free (index start length) (sequence-subseq-string-copy-path 0 index start length))
             (:free (index start length source destination memory)
                    (sequence-subseq-string-copy-memory
                     0 index start length source destination memory))))
   ("Subgoal *1/2" :use sequence-subseq-string-step-effects))
  :rule-classes nil)

(defthm sequence-string-copy-keeps-outside-bytes
  (implies (and (natp remaining) (natp index)
                (proof-span-p destination (+ index remaining))
                (unsigned-byte-p 64 address)
                (or (< address (+ destination index))
                    (<= (+ destination index remaining) address)))
           (equal (boymoo-model::a64-byte
                   address (sequence-subseq-string-copy-memory
                            remaining index start length source destination memory))
                  (boymoo-model::a64-byte address memory)))
  :hints (("Goal"
           :induct (sequence-subseq-string-copy-memory
                    remaining index start length source destination memory)
           :in-theory (disable sequence-subseq-source-byte sequence-write-one-byte))))

(local
 (defthm sequence-source-byte-is-a-byte
   (unsigned-byte-p 8 (sequence-subseq-source-byte index start length source memory))))

(local
 (defthm sequence-source-byte-survives-disjoint-store
   (implies
    (and (natp index) (natp start) (proof-span-p source length)
         (proof-span-p address 1)
         (proof-disjoint-p address (1+ address) source (+ source length)))
    (equal (sequence-subseq-source-byte
            index start length source (boymoo-model::a64-write-bytes 1 address byte memory))
           (sequence-subseq-source-byte index start length source memory)))
   :hints (("Goal" :in-theory (disable sequence-write-one-byte)))))

(defthm sequence-string-copy-writes-source-byte-or-zero
  (implies
   (and (natp remaining) (natp index) (natp byte-index) (natp start)
        (<= index byte-index) (< byte-index (+ index remaining))
        (proof-span-p source length)
        (proof-span-p destination (+ index remaining))
        (proof-disjoint-p source (+ source length) (+ destination index)
                          (+ destination index remaining)))
   (equal (boymoo-model::a64-byte
           (+ destination byte-index)
           (sequence-subseq-string-copy-memory
            remaining index start length source destination memory))
          (sequence-subseq-source-byte byte-index start length source memory)))
  :hints
  (("Goal" :induct (sequence-subseq-string-copy-memory
                    remaining index start length source destination memory)
           :in-theory (disable sequence-subseq-source-byte sequence-write-one-byte))
   ("Subgoal *1/2"
    :cases ((equal index byte-index))
    :use ((:instance sequence-source-byte-survives-disjoint-store
                     (index byte-index) (address (+ destination index))
                     (byte (sequence-subseq-source-byte index start length source memory))))))
  :rule-classes nil)

(defthm sequence-subseq-string-copy-segment
  (let* ((machine (proof-world-machine before))
         (index (proof-world-reg 3 before))
         (start (proof-world-reg 20 before))
         (length (proof-world-reg 2 before))
         (count (proof-world-reg 19 before))
         (source (proof-world-reg 1 before))
         (destination (proof-world-reg 7 before))
         (memory (boymoo-model::a64-memory machine))
         (path (sequence-subseq-string-copy-path remaining index start length))
         (cuts (list (+ 40 (proof-world-pc before))))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (natp remaining)
          (equal (+ index remaining) count)
          (consp (boymoo-model::a64-registers machine))
          (<= (+ start count) (expt 2 64))
          (proof-span-p source length)
          (proof-span-p destination count)
          (proof-disjoint-p source (+ source length) (+ destination index)
                            (+ destination count))
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before)))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (implies (and (natp byte-index) (<= index byte-index) (< byte-index count))
                   (equal (boymoo-model::a64-byte
                           (+ destination byte-index)
                           (boymoo-model::a64-memory (proof-world-machine after)))
                          (sequence-subseq-source-byte byte-index start length source memory))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p sequence-subseq-string-copy-path
                        sequence-subseq-string-copy-memory sequence-subseq-source-byte
                        proof-world-pc proof-world-reg proof-world-machine)
    :use (sequence-subseq-string-copy-effects
          (:instance sequence-string-copy-writes-source-byte-or-zero
                     (index (proof-world-reg 3 before)) (start (proof-world-reg 20 before))
                     (length (proof-world-reg 2 before)) (source (proof-world-reg 1 before))
                     (destination (proof-world-reg 7 before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before))))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-subseq-string-copy-path
                                    remaining (proof-world-reg 3 before)
                                    (proof-world-reg 20 before) (proof-world-reg 2 before)))
                     (cuts (list (+ 40 (proof-world-pc before))))
                     (after (sequence-execute
                             (sequence-subseq-string-copy-path
                              remaining (proof-world-reg 3 before)
                              (proof-world-reg 20 before) (proof-world-reg 2 before))
                             before))))))
  :rule-classes nil)

(local
 (defthm sequence-take-length
   (equal (len (take count datum)) (nfix count))
   :hints (("Goal" :induct (take count datum)))))

(local
 (defun sequence-take-index-induction (index count datum)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count datum)
     (sequence-take-index-induction (1- index) (1- count) (cdr datum)))))

(local
 (defthm sequence-nth-of-take
   (implies (and (natp index) (natp count) (< index count))
            (equal (nth index (take count datum)) (nth index datum)))
   :hints (("Goal" :induct (sequence-take-index-induction index count datum)
                   :expand ((take count datum) (nth index datum))))))

(local
 (defthm sequence-nth-of-drop
   (implies (and (natp index) (natp count))
            (equal (nth index (sequence-drop count datum)) (nth (+ index count) datum)))
   :hints (("Goal" :induct (sequence-drop count datum)
                   :expand ((nth (+ index count) datum))))))

(local
 (defthm sequence-nth-code-in-list
   (implies (and (natp index) (< index (len datum)))
            (equal (nth index (sequence-list-bytes datum))
                   (char-code (nth index datum))))
   :hints (("Goal" :induct (nth index datum)))))

(local
 (defthm sequence-source-list-of-coerced-string
   (equal (coerce (coerce datum 'string) 'list)
          (proof-byte-characters (sequence-list-bytes datum)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::core-primitive)
                                   (sequence-core-coerce sequence-byte-characters-of-list-bytes))
                   :use ((:instance sequence-core-coerce (result-type 'string) (program nil)))))))

(defthm sequence-subseq-string-length
  (implies (stringp datum)
           (equal (len (coerce (sequence-slice datum start end) 'list))
                  (sequence-result-size datum start end)))
  :hints (("Goal" :in-theory (disable sequence-result-size sequence-take-after-drop
                                      sequence-byte-characters-of-list-bytes))))

(local
 (defthm sequence-code-char-in-string-slice
   (let* ((datum (proof-load-string length source machine))
          (memory (boymoo-model::a64-memory machine)))
     (implies (and (natp index) (natp length) (integerp source)
                   (< index (sequence-result-size datum start end)))
              (equal (char (sequence-slice datum start end) index)
                     (code-char (sequence-subseq-source-byte
                                 index (sequence-runtime-count start) length source memory)))))
   :hints
   (("Goal"
     :in-theory (e/d (char)
                     (proof-load-string sequence-take-after-drop
                      sequence-byte-characters-of-list-bytes sequence-runtime-count
                      sequence-result-size))
     :use ((:instance sequence-load-string-length (count length) (address source)))))))

(defun sequence-subseq-copy-input-p (before datum start end)
  (let* ((machine (proof-world-machine before))
         (old-length (proof-world-reg 2 before))
         (size (proof-world-reg 19 before))
         (fixed-start (proof-world-reg 20 before))
         (source (proof-world-reg 1 before))
         (destination (proof-world-reg 7 before))
         (path (sequence-subseq-string-copy-path size 0 fixed-start old-length))
         (cuts (list (+ 40 (proof-world-pc before)))))
    (and (not (proof-world-stop before))
         (consp (boymoo-model::a64-registers machine))
         (equal (proof-world-reg 3 before) 0)
         (equal datum (proof-load-string old-length source machine))
         (equal fixed-start (sequence-runtime-count start))
         (equal size (sequence-result-size datum start end))
         (<= old-length *proof-space-size*)
         (<= (+ fixed-start size) (expt 2 64))
         (proof-span-p source old-length)
         (proof-span-p destination size)
         (proof-disjoint-p source (+ source old-length) destination (+ destination size))
         (unsigned-byte-p 64 (+ 40 (proof-world-pc before)))
         (sequence-instruction-path path cuts before))))

(defun sequence-subseq-copied-string (before)
  (let* ((size (proof-world-reg 19 before))
         (path (sequence-subseq-string-copy-path size 0
                                                (proof-world-reg 20 before)
                                                (proof-world-reg 2 before)))
         (after (sequence-execute path before)))
    (proof-load-string size (proof-world-reg 7 before) (proof-world-machine after))))

(local
 (defthm sequence-subseq-copy-character
   (implies (and (sequence-subseq-copy-input-p before datum start end)
                 (natp index) (< index (proof-world-reg 19 before)))
            (equal (char (sequence-subseq-copied-string before) index)
                   (char (sequence-slice datum start end) index)))
   :hints
   (("Goal"
     :in-theory (disable proof-load-string sequence-subseq-string-copy-path
                         sequence-subseq-copy-path-when-positive
                         sequence-runtime-count sequence-result-size sequence-slice
                         proof-segment-p sequence-subseq-source-byte)
     :use ((:instance sequence-subseq-string-copy-segment
                      (remaining (proof-world-reg 19 before)) (byte-index index))
           (:instance sequence-code-char-in-string-slice
                      (length (proof-world-reg 2 before)) (source (proof-world-reg 1 before))
                      (machine (proof-world-machine before))))))))

(local
 (defun sequence-first-list-difference (left right)
   (if (and (consp left) (consp right) (equal (car left) (car right)))
       (1+ (sequence-first-list-difference (cdr left) (cdr right)))
     0)))

(local
 (defthm sequence-list-difference-witness
   (let ((index (sequence-first-list-difference left right)))
     (implies (and (true-listp left) (true-listp right)
                   (equal (len left) (len right))
                   (not (equal left right)))
              (and (natp index) (< index (len left))
                   (not (equal (nth index left) (nth index right))))))
   :hints (("Goal" :induct (sequence-first-list-difference left right)))
   :rule-classes nil))

(local
 (defthm sequence-character-list-is-true-list
   (implies (character-listp chars) (true-listp chars))
   :hints (("Goal" :induct (character-listp chars)))))

(local
 (defthm sequence-subseq-copied-is-string
   (stringp (sequence-subseq-copied-string before))
   :hints (("Goal" :in-theory (disable proof-load-string)))))

(local
 (defthm sequence-subseq-copied-string-length
   (equal (len (coerce (sequence-subseq-copied-string before) 'list))
          (proof-world-reg 19 before))
   :hints (("Goal" :in-theory (disable proof-load-string)))))

(local
 (defthm sequence-string-slice-is-string
   (implies (stringp datum) (stringp (sequence-slice datum start end)))))

(local
 (defthm sequence-string-list-is-injective
   (implies (and (stringp left) (stringp right)
                 (equal (coerce left 'list) (coerce right 'list)))
            (equal left right))
   :hints (("Goal" :in-theory (disable acl2::coerce-inverse-2)
                   :use ((:instance acl2::coerce-inverse-2 (acl2::x left))
                         (:instance acl2::coerce-inverse-2 (acl2::x right)))))
   :rule-classes nil))

(defthm sequence-subseq-string-copy-source-value
  (implies
   (sequence-subseq-copy-input-p before datum start end)
   (equal (boymoo-model::core-value (sequence-subseq-copied-string before))
          (boymoo-model::core-prelude 'subseq (list datum start end))))
  :hints
  (("Goal"
    :in-theory (e/d (char)
                    (sequence-subseq-copied-string sequence-first-list-difference
                     sequence-slice sequence-result-size sequence-runtime-count
                     sequence-subseq-copy-path-when-positive
                     proof-load-string sequence-core-subseq boymoo-model::core-prelude-values))
    :use
    (sequence-core-subseq
     (:instance sequence-list-difference-witness
                (left (coerce (sequence-subseq-copied-string before) 'list))
                (right (coerce (sequence-slice datum start end) 'list)))
     (:instance sequence-subseq-copy-character
                (index (sequence-first-list-difference
                        (coerce (sequence-subseq-copied-string before) 'list)
                        (coerce (sequence-slice datum start end) 'list))))
     (:instance sequence-string-list-is-injective
                (left (sequence-subseq-copied-string before))
                (right (sequence-slice datum start end))))))
  :rule-classes nil)
