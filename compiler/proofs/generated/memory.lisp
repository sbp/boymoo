(in-package "BOYMOO-PROOFS")

(include-book "bits")
(include-book "registers")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable floor mod ash expt acl2::binary-logior
                    boymoo-model::a64-unsigned boymoo-model::a64-byte
                    boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes
                    generated-load-word generated-store-word proof-load-word))

(defthm generated-memory-byte-bounds
  (and (natp (boymoo-model::a64-byte address memory))
       (< (boymoo-model::a64-byte address memory) 256))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))
  :rule-classes ((:type-prescription
                  :corollary (natp (boymoo-model::a64-byte address memory)))
                 (:linear :corollary (< (boymoo-model::a64-byte address memory) 256))))

(local
 (defthm generated-byte-of-put-at-bounded-address
   (implies (and (unsigned-byte-p 64 address) (unsigned-byte-p 64 query))
            (equal (boymoo-model::a64-byte query
                     (put-assoc-equal address value memory))
                   (if (equal query address)
                       (boymoo-model::a64-unsigned 8 value)
                     (boymoo-model::a64-byte query memory))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))))

(defthm generated-byte-after-writing-outside
  (implies (and (natp address) (natp count) (<= (+ address count) (expt 2 64))
                (unsigned-byte-p 64 query)
                (or (< query address) (<= (+ address count) query)))
           (equal (boymoo-model::a64-byte query
                    (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-byte query memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (enable boymoo-model::a64-write-bytes))))

(defthm generated-read-after-writing-disjoint
  (implies (and (natp address) (natp count) (<= (+ address count) (expt 2 64))
                (natp query) (natp length) (<= (+ query length) (expt 2 64))
                (proof-disjoint-p address (+ address count) query (+ query length)))
           (equal (boymoo-model::a64-read-bytes length query
                    (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-read-bytes length query memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes length query memory)
                  :in-theory (enable boymoo-model::a64-read-bytes))))

(defthm generated-load-after-word-store-disjoint
  (implies (and (proof-span-p query 8) (proof-span-p address 8)
                (proof-disjoint-p query (+ query 8) address (+ address 8)))
           (equal (generated-load-word query (generated-store-word address value world))
                  (generated-load-word query world)))
  :hints (("Goal" :in-theory (enable generated-load-word generated-store-word
                                    proof-load-word boymoo-model::a64-store))))

(local
 (defthm generated-expt-two-after-eight
   (implies (natp n)
            (equal (expt 2 (+ 8 n)) (* 256 (expt 2 n))))
   :hints (("Goal" :expand ((expt 2 (+ 8 n)) (expt 2 (+ 7 n)) (expt 2 (+ 6 n))
                            (expt 2 (+ 5 n)) (expt 2 (+ 4 n)) (expt 2 (+ 3 n))
                            (expt 2 (+ 2 n)) (expt 2 (+ 1 n)))))))

(local
 (defthm generated-ash-by-negative-eight
   (implies (integerp value) (equal (ash value -8) (floor value 256)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm generated-floor-of-floor-for-byte
   (implies (and (integerp value) (posp divisor))
            (equal (floor (floor value 256) divisor)
                   (floor value (* 256 divisor))))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x value) (y 256))
                  (:instance generated-floor-bounds (x (floor value 256)) (y divisor))
                  (:instance generated-floor-unique (x value) (y (* 256 divisor))
                             (q (floor (floor value 256) divisor)))
                  (:instance generated-integer-step (x (floor value 256))
                             (y (+ divisor (* divisor (floor (floor value 256) divisor))))))))))

(local
 (defthm generated-modulo-of-byte-and-higher-bytes
   (implies (and (integerp value) (posp divisor))
            (equal (+ (mod value 256) (* 256 (mod (floor value 256) divisor)))
                   (mod value (* 256 divisor))))
   :hints (("Goal" :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm generated-recombine-written-byte
   (implies (and (integerp value) (natp remaining-bits))
            (equal (+ (boymoo-model::a64-unsigned 8 value)
                      (* 256 (boymoo-model::a64-unsigned remaining-bits (floor value 256))))
                   (boymoo-model::a64-unsigned (+ 8 remaining-bits) value)))
   :hints (("Goal"
            :use ((:instance generated-modulo-of-byte-and-higher-bytes
                             (divisor (expt 2 remaining-bits)))
                  (:instance generated-unsigned-as-mod (n 8) (x value))
                  (:instance generated-unsigned-as-mod (n remaining-bits)
                             (x (floor value 256)))
                  (:instance generated-unsigned-as-mod (n (+ 8 remaining-bits)) (x value)))))))

(local
 (defthm generated-combine-byte-with-higher-bytes
   (implies (and (natp low) (< low 256) (integerp high))
            (equal (logior low (* 256 high)) (+ low (* 256 high))))
   :hints (("Goal" :use (:instance generated-logior-of-disjoint-fields (bits 8))))))

(defthm generated-read-after-writing-same-span
  (implies (and (natp address) (natp count) (<= (+ address count) (expt 2 64))
                (integerp value))
           (equal (boymoo-model::a64-read-bytes count address
                    (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-unsigned (* 8 count) value)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (enable (:induction boymoo-model::a64-write-bytes)))
          ("Subgoal *1/1" :in-theory (enable boymoo-model::a64-unsigned
                                            boymoo-model::a64-write-bytes boymoo-model::a64-read-bytes))
          ("Subgoal *1/2"
           :expand (boymoo-model::a64-write-bytes count address value memory)
           :in-theory (enable boymoo-model::a64-read-bytes))))

(defthm generated-load-after-word-store-same
  (implies (and (proof-span-p address 8) (integerp value))
           (equal (generated-load-word address (generated-store-word address value world))
                  (boymoo-model::a64-unsigned 64 value)))
  :hints (("Goal" :in-theory (enable generated-load-word generated-store-word
                                    proof-load-word boymoo-model::a64-store))))

(local
 (defthm generated-byte-concatenation-bound
   (implies (and (integerp high) (integerp limit) (< high limit)
                 (rationalp low) (< low 256))
            (< (+ low (* 256 high)) (* 256 limit)))
   :hints (("Goal" :use (:instance generated-integer-step (x high) (y limit))))))

(defthm generated-read-bytes-bounds
  (let ((result (boymoo-model::a64-read-bytes count address memory)))
    (and (natp result) (< result (expt 2 (* 8 (nfix count))))))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                  :in-theory (enable boymoo-model::a64-read-bytes))
          ("Subgoal *1/2"
           :use ((:instance generated-expt-two-after-eight (n (* 8 (1- count))))
                 (:instance generated-powers-of-two-integer (n (* 8 (1- count))))
                 (:instance generated-byte-concatenation-bound
                            (low (boymoo-model::a64-byte address memory))
                            (high (boymoo-model::a64-read-bytes
                                   (1- count) (1+ (ifix address)) memory))
                            (limit (expt 2 (* 8 (1- count))))))
           :in-theory (e/d (boymoo-model::a64-read-bytes)
                           (generated-powers-of-two-step generated-byte-concatenation-bound))))
  :rule-classes ((:type-prescription
                  :corollary (natp (boymoo-model::a64-read-bytes count address memory)))
                 (:linear
                  :corollary (< (boymoo-model::a64-read-bytes count address memory)
                                (expt 2 (* 8 (nfix count)))))))

(defthm generated-word-load-bounds
  (and (natp (generated-load-word address world))
       (< (generated-load-word address world) (expt 2 64)))
  :hints (("Goal" :in-theory (enable generated-load-word proof-load-word)))
  :rule-classes ((:type-prescription :corollary (natp (generated-load-word address world)))
                 (:linear :corollary (< (generated-load-word address world) (expt 2 64)))))
