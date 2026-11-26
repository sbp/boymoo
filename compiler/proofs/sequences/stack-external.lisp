(in-package "BOYMOO-PROOFS")

(include-book "stack-mappings")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-layout-p proof-external-objects proof-fixed-external-p
                    proof-external-bytes proof-regions-p proof-align-up proof-disjoint-p))

(local
 (defthm sequence-valid-external-head-is-natural
   (implies (and (proof-heap-layout-p before)
                 (not (equal head 0))
                 (proof-external-objects head fuel before objects))
            (natp head))
   :hints (("Goal"
            :use ((:instance sequence-heap-layout-bounds (world before))
                  (:instance sequence-external-mapping-bounds (world before)))))
   :rule-classes nil))

(local
 (defthm sequence-mapping-words-after-stack-write
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-heap-layout-p before)
                   (sequence-stack-write-p start end before after)
                   (not (equal head 0))
                   (proof-external-objects head fuel before objects)
                   (natp offset) (<= offset 24))
              (equal (proof-load-word (+ head offset) last)
                     (proof-load-word (+ head offset) first))))
   :hints
   (("Goal"
     :in-theory (enable proof-load-word)
     :use ((:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-external-mapping-bounds (world before))
           sequence-mapping-bytes-unchanged-by-stack-write
           (:instance sequence-read-in-agreed-machine-span
                      (start head)
                      (end (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                      (first (proof-world-machine before)) (last (proof-world-machine after))
                      (address (+ head offset)) (count 8)))))
   :rule-classes nil))

(local
 (defun sequence-external-induction (head fuel before)
   (declare (xargs :measure (nfix fuel)))
   (if (or (equal head 0) (zp fuel))
       nil
     (sequence-external-induction
      (proof-load-word head (proof-world-machine before)) (1- fuel) before))))

(local
 (defthm sequence-empty-external-mappings
   (equal (proof-external-objects 0 fuel world objects) (list :mappings))
   :hints (("Goal" :expand ((proof-external-objects 0 fuel world objects))))))

(local
 (defthm sequence-external-fields-after-stack-write
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-heap-layout-p before)
                   (sequence-stack-write-p start end before after)
                   (not (equal head 0))
                   (proof-external-objects head fuel before objects))
              (and (natp head)
                   (equal (proof-heap-base after) (proof-heap-base before))
                   (equal (proof-machine-limit after) (proof-machine-limit before))
                   (equal (proof-spaces-end after) (proof-spaces-end before))
                   (equal (proof-stack-base after) (proof-stack-base before))
                   (equal (proof-stack-end after) (proof-stack-end before))
                   (equal (proof-world-regions after) (proof-world-regions before))
                   (equal (proof-load-word head last) (proof-load-word head first))
                   (equal (proof-load-word (+ head 8) last) (proof-load-word (+ head 8) first))
                   (equal (proof-load-word (+ head 16) last) (proof-load-word (+ head 16) first))
                   (equal (proof-load-word (+ head 24) last) (proof-load-word (+ head 24) first))
                   (sequence-machine-span-agrees-p
                    head (+ head (proof-load-word (+ head 8) first)) first last))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-heap-metadata-agrees-p sequence-heap-registers-agree-p
                      sequence-stack-write-p)
                     (proof-subspan-p proof-span-p proof-streams-preserved-p
                      proof-world-stop proof-world-replies proof-world-page-size))
     :use (sequence-valid-external-head-is-natural
           sequence-stack-write-keeps-heap-metadata sequence-world-tail-fields
           sequence-mapping-bytes-unchanged-by-stack-write
           (:instance sequence-mapping-words-after-stack-write (offset 0))
           (:instance sequence-mapping-words-after-stack-write (offset 8))
           (:instance sequence-mapping-words-after-stack-write (offset 16))
           (:instance sequence-mapping-words-after-stack-write (offset 24)))))
   :rule-classes nil))

(local
 (defthm sequence-external-tail-is-valid
   (let ((next (proof-load-word head (proof-world-machine before))))
     (implies (and (not (equal head 0)) (posp fuel)
                   (proof-external-objects head fuel before objects))
              (proof-external-objects next (1- fuel) before objects)))
   :hints (("Goal" :expand ((proof-external-objects head fuel before objects))))
   :rule-classes nil))

(local
 (defthm sequence-external-preservation-step
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (next (proof-load-word head first))
          (rest (proof-external-objects next (1- fuel) before objects))
          (old (proof-external-objects head fuel before objects))
          (new (proof-external-objects head fuel after objects)))
     (implies (and (proof-heap-layout-p before)
                   (sequence-stack-write-p start end before after)
                   (not (equal head 0)) (posp fuel) old
                   (equal (proof-external-objects next (1- fuel) after objects) rest)
                   (proof-fixed-external-p (cdr rest) before after)
                   (equal (proof-external-bytes (cdr rest) last)
                          (proof-external-bytes (cdr rest) first)))
              (and (equal new old)
                   (proof-fixed-external-p (cdr old) before after)
                   (equal (proof-external-bytes (cdr old) last)
                          (proof-external-bytes (cdr old) first)))))
   :hints
   (("Goal"
     :in-theory (enable proof-fixed-external-p proof-external-bytes)
     :expand ((proof-external-objects head fuel before objects)
              (proof-external-objects head fuel after objects))
     :use sequence-external-fields-after-stack-write))
   :rule-classes nil))

(defthm sequence-stack-write-keeps-external-mappings
  (let* ((old (proof-external-objects head fuel before objects))
         (new (proof-external-objects head fuel after objects))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-stack-write-p start end before after)
                  old)
             (and (equal new old)
                  (proof-fixed-external-p (cdr old) before after)
                  (equal (proof-external-bytes (cdr old) last)
                         (proof-external-bytes (cdr old) first)))))
  :hints
  (("Goal"
    :induct (sequence-external-induction head fuel before))
   ("Subgoal *1/1"
    :in-theory (enable proof-fixed-external-p proof-external-bytes)
    :expand ((proof-external-objects head fuel before objects)
             (proof-external-objects head fuel after objects)))
   ("Subgoal *1/2"
    :use (sequence-external-tail-is-valid sequence-external-preservation-step)))
  :rule-classes nil)

(local
 (defthm sequence-integer-is-in-lowest-terms
   (implies (integerp value)
            (and (equal (denominator value) 1)
                 (equal (numerator value) value)))
   :hints
   (("Goal"
     :in-theory (disable acl2::rational-implies2 associativity-of-*)
     :use ((:instance acl2::rational-implies1 (acl2::x value))
           (:instance acl2::rational-implies2 (acl2::x value))
           (:instance associativity-of-*
                      (acl2::x (denominator value))
                      (acl2::y (/ (denominator value)))
                      (acl2::z (numerator value)))
           (:instance acl2::lowest-terms
                      (acl2::x value) (acl2::n (denominator value))
                      (acl2::r value) (acl2::q 1)))))))

(local
 (defthm sequence-eight-byte-multiple-is-already-aligned
   (implies (natp blocks)
            (equal (proof-align-up (* 8 blocks) 8) (* 8 blocks)))
   :hints (("Goal"
            :in-theory (e/d (proof-align-up ceiling) (associativity-of-* acl2::rational-implies2))
            :use ((:instance associativity-of-*
                             (acl2::x 1/8) (acl2::y 8) (acl2::z blocks))
                  (:instance acl2::rational-implies2 (acl2::x blocks)))))))

(local
 (defthm sequence-integer-limits-are-discrete
   (implies (and (integerp lower) (integerp upper) (< upper (1+ lower)))
            (<= upper lower))
   :hints
   (("Goal"
     :use ((:instance sequence-floor-unique
                      (value (- upper lower)) (divisor 1) (quotient 0))
           (:instance sequence-floor-unique
                      (value (- upper lower)) (divisor 1) (quotient (- upper lower))))))
   :rule-classes nil))

(local
 (defthm sequence-aligned-capacity-includes-rounded-size
   (implies (and (natp size) (natp blocks) (<= size (* 8 blocks)))
            (<= (proof-align-up size 8) (* 8 blocks)))
   :hints (("Goal"
            :in-theory (e/d (proof-align-up (:type-prescription ceiling))
                            ((:definition ceiling) sequence-eight-byte-multiple-is-already-aligned))
            :cases ((equal size (* 8 blocks)))
            :use (sequence-eight-byte-multiple-is-already-aligned
                  (:instance sequence-integer-limits-are-discrete
                             (lower blocks) (upper (ceiling size 8)))
                  (:instance sequence-align-up-upper-bound (address size) (alignment 8)))))
   :rule-classes nil))

(local
 (defthm sequence-external-mapping-covers-rounded-object
   (implies (natp bytes)
            (and (<= (+ 32 (proof-align-up bytes 8))
                     (proof-align-up (+ 32 bytes) *proof-runtime-page*))
                 (<= 40 (proof-align-up (+ 32 bytes) *proof-runtime-page*))))
   :hints
   (("Goal"
     :in-theory (enable proof-align-up)
     :use ((:instance sequence-aligned-capacity-includes-rounded-size
                      (size bytes)
                      (blocks (- (* 8192 (ceiling (+ 32 bytes) *proof-runtime-page*)) 4)))
           (:instance sequence-align-up-covers-address
                      (address (+ 32 bytes)) (alignment *proof-runtime-page*)))))
   :rule-classes nil))

(local
 (defthm sequence-record-fits-external-mapping
   (let* ((first (proof-world-machine before))
          (size (proof-load-word (+ head 8) first))
          (address (proof-object-address object)))
     (implies (and (proof-regions-p (proof-world-regions before))
                   (not (equal head 0))
                   (proof-external-objects head fuel before objects)
                   (equal address (+ head 24)))
              (proof-subspan-p address (proof-object-size object first) head (+ head size))))
   :hints
   (("Goal"
     :in-theory (enable proof-object-size)
     :expand ((proof-external-objects head fuel before objects))
     :use ((:instance sequence-external-mapping-bounds (world before))
           (:instance sequence-align-up-covers-address
                      (address (proof-header-size
                                (proof-load-word (+ head 24) (proof-world-machine before))))
                      (alignment 8))
           (:instance sequence-external-mapping-covers-rounded-object
                      (bytes (proof-header-size
                              (proof-load-word (+ head 24) (proof-world-machine before))))))))
   :rule-classes nil))

(defthm sequence-external-object-agrees-after-stack-write
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (address (proof-object-address object))
         (size (proof-object-size object first)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-stack-write-p start end before after)
                  (member-equal address (cdr (proof-external-objects head fuel before objects))))
             (sequence-machine-span-agrees-p address (+ address size) first last)))
  :hints
  (("Goal"
    :induct (sequence-external-induction head fuel before)
    :expand ((proof-external-objects head fuel before objects)))
   ("Subgoal *1/2"
    :in-theory (disable proof-object-size proof-span-p)
    :use ((:instance sequence-heap-layout-bounds (world before))
          sequence-record-fits-external-mapping
          sequence-mapping-bytes-unchanged-by-stack-write
          (:instance sequence-machine-agreement-on-subinterval
                     (lower head)
                     (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                     (start (proof-object-address object))
                     (end (+ (proof-object-address object)
                             (proof-object-size object (proof-world-machine before))))
                     (first (proof-world-machine before)) (last (proof-world-machine after))))))
  :rule-classes nil)
