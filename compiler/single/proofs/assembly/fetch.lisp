(in-package "BOYMOO-PROOFS")

(include-book "placement")
(include-book "word-transfers")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash floor mod expt assembly-high assembly-low assembly-cat
                           assembly-power-of-two acl2::binary-logand acl2::binary-logior
                           boymoo-compiler::low-bits boymoo-model::a64-unsigned)))

(local
 (defthm assembly-a64-load-one
   (equal (boymoo-model::a64-load 1 address machine)
          (boymoo-model::a64-byte address (boymoo-model::a64-memory machine)))
   :hints (("Goal"
            :expand ((:free (memory) (boymoo-model::a64-read-bytes 1 address memory))
                     (:free (start memory) (boymoo-model::a64-read-bytes 0 start memory)))))))

(local
 (defthm assembly-a64-byte-bound
   (and (<= 0 (boymoo-model::a64-byte address memory))
        (< (boymoo-model::a64-byte address memory) 256))
   :hints (("Goal"
            :use ((:instance assembly-low-bounds
                             (width 8)
                             (value (cdr (assoc-equal
                                          (boymoo-model::a64-unsigned 64 address) memory)))))))
   :rule-classes (:rewrite :linear)))

(local
 (defthm assembly-read-bytes-integer
   (integerp (boymoo-model::a64-read-bytes count address memory))
   :rule-classes :type-prescription))

(local
 (defthm assembly-load-integer
   (integerp (boymoo-model::a64-load count address machine))
   :rule-classes :type-prescription))

(local
 (defthm assembly-load-pairing
   (implies (posp count)
            (equal (boymoo-model::a64-load count address machine)
                   (assembly-cat 8 (boymoo-model::a64-load 1 address machine)
                                 (boymoo-model::a64-load
                                  (1- count) (1+ (ifix address)) machine))))
   :hints (("Goal"
            :use ((:instance assembly-logior-disjoint-fields
                             (width 8)
                             (low (boymoo-model::a64-load 1 address machine))
                             (high (boymoo-model::a64-load
                                    (1- count) (1+ (ifix address)) machine))))
            :expand ((:free (memory) (boymoo-model::a64-read-bytes count address memory)))
            :in-theory (e/d (assembly-cat) (assembly-logior-disjoint-fields))))
   :rule-classes nil))

(local
 (defthm assembly-byte-character-from-fields
   (implies (and (integerp word) (natp index))
            (equal (assembly-byte-character word index)
                   (code-char (assembly-low 8 (assembly-high (* 8 index) word)))))
   :hints (("Goal"
            :use ((:instance assembly-ash-right (value word) (width (* 8 index)))
                  (:instance assembly-product-of-negative (a index) (b 8)))
            :in-theory (disable assembly-ash-right assembly-product-of-negative)))))

(local
 (defthm assembly-byte-character-of-shifted-word
   (implies (and (integerp word) (natp index))
            (equal (assembly-byte-character (assembly-high 8 word) index)
                   (assembly-byte-character word (1+ index))))
   :hints (("Goal" :in-theory (disable assembly-byte-character)))))

(local
 (defthm assembly-word-characters-in-low-order
   (implies (and (posp count) (integerp word))
            (equal (assembly-word-characters word count)
                   (cons (assembly-byte-character word 0)
                         (assembly-word-characters (assembly-high 8 word) (1- count)))))
   :hints (("Goal" :induct (assembly-word-characters word count)
                   :in-theory (disable assembly-byte-character
                                       assembly-byte-character-from-fields))
           ("Subgoal *1/2" :cases ((equal count 1))))))

(local
 (defthm assembly-low-byte-from-character
   (implies (and (integerp word)
                 (equal (code-char (boymoo-model::a64-load 1 address machine))
                        (assembly-byte-character word 0)))
            (equal (boymoo-model::a64-load 1 address machine) (assembly-low 8 word)))
   :hints (("Goal"
            :in-theory (disable assembly-byte-character
                                boymoo-model::a64-byte boymoo-model::a64-load)
            :use ((:instance acl2::char-code-code-char-is-identity
                             (acl2::n (boymoo-model::a64-load 1 address machine)))
                  (:instance acl2::char-code-code-char-is-identity
                             (acl2::n (assembly-low 8 word))))))
   :rule-classes nil))

(local
 (defthm assembly-load-zero
   (equal (boymoo-model::a64-load 0 address machine) 0)
   :hints (("Goal" :expand ((:free (memory) (boymoo-model::a64-read-bytes 0 address memory)))))))

(local
 (defthm assembly-high-fits-remaining-bytes
   (implies (and (posp count) (unsigned-byte-p (* 8 count) word))
            (unsigned-byte-p (* 8 (1- count)) (assembly-high 8 word)))
   :hints (("Goal"
            :use ((:instance assembly-power-of-two-of-sum (a 8) (b (* 8 (1- count))))
                  (:instance assembly-floor-bounds (x word) (d 256)))
            :in-theory (e/d (assembly-high)
                            (unsigned-byte-p assembly-power-of-two-of-sum))))))

(local
 (defun assembly-load-word-induct (count word address)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (cons word address)
     (assembly-load-word-induct (1- count)
                                (assembly-high 8 word)
                                (1+ (ifix address))))))

(defthm assembly-load-serialized-word
  (implies (and (natp count) (unsigned-byte-p (* 8 count) word)
                (assembly-characters-at-p (assembly-word-characters word count) address machine))
           (equal (boymoo-model::a64-load count address machine) word))
  :hints (("Goal" :induct (assembly-load-word-induct count word address)
                  :in-theory (disable unsigned-byte-p
                                      boymoo-model::a64-load assembly-word-characters
                                      assembly-byte-character assembly-byte-character-from-fields))
          ("Subgoal *1/2"
           :use (assembly-load-pairing assembly-low-byte-from-character
                 assembly-high-fits-remaining-bytes
                 (:instance assembly-cat-of-low-and-high (width 8) (x word)))
           :in-theory (disable unsigned-byte-p assembly-cat-of-low-and-high
                               assembly-high-fits-remaining-bytes
                               boymoo-model::a64-load assembly-word-characters
                               assembly-byte-character assembly-byte-character-from-fields))))

(defun assembly-decode-words (words)
  (if (atom words)
      nil
    (cons (proof-decode (car words)) (assembly-decode-words (cdr words)))))

(defun assembly-words-p (words)
  (if (atom words)
      (null words)
    (and (unsigned-byte-p 32 (car words))
         (assembly-words-p (cdr words)))))

(defthm assembly-fetch-serialized-word
  (implies (and (unsigned-byte-p 32 word)
                (proof-fetchable-p address world)
                (assembly-characters-at-p (assembly-word-characters word 4) address
                                          (proof-world-machine world)))
           (proof-instruction-at-p (proof-decode word) address world))
  :hints (("Goal"
           :use ((:instance assembly-load-serialized-word (count 4) (machine (proof-world-machine world))))
           :in-theory (disable assembly-load-serialized-word proof-decode
                               proof-fetchable-p proof-world-machine
                               assembly-word-characters boymoo-model::a64-load))))

(defun assembly-word-fetches-p (words address world)
  (if (atom words)
      (null words)
    (and (proof-fetchable-p address world)
         (assembly-word-fetches-p (cdr words) (+ 4 address) world))))

(defthm assembly-fetch-serialized-words
  (implies (and (assembly-words-p words)
                (integerp address)
                (assembly-word-fetches-p words address world)
                (assembly-characters-at-p
                 (assembly-words-characters words) address (proof-world-machine world)))
           (proof-instructions-at-p (assembly-decode-words words) address world))
  :hints (("Goal" :induct (assembly-word-fetches-p words address world)
                  :in-theory (disable proof-instruction-at-p proof-fetchable-p
                                      proof-decode proof-world-machine
                                      assembly-word-characters))))
