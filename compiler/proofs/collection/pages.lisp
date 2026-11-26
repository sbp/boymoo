(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun collection-page-floor (address)
  (* *proof-runtime-page* (floor address *proof-runtime-page*)))

(defun collection-page-ceiling (address)
  (collection-page-floor (+ address (1- *proof-runtime-page*))))

(local (in-theory (disable floor)))

(defthm collection-page-floor-is-two-shifts
  (implies (integerp address)
           (equal (ash (ash address -16) 16) (collection-page-floor address)))
  :hints (("Goal" :in-theory (e/d (ash acl2::floor-normalize-denominator)
                                 (acl2::floor-of-*-of-/-and-1)))))

(local
 (defthm collection-page-floor-bounds
   (implies (integerp address)
            (and (<= (collection-page-floor address) address)
                 (< (- address *proof-runtime-page*) (collection-page-floor address))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance acl2::floor-bounded-by-/
                                    (acl2::x address)
                                    (acl2::y *proof-runtime-page*)))))))

(defthm collection-page-floor-fits-word
  (implies (unsigned-byte-p 64 address)
           (unsigned-byte-p 64 (collection-page-floor address)))
  :hints (("Goal" :use collection-page-floor-bounds)))

(encapsulate
 ()
 (local (include-book "arithmetic/equalities" :dir :system))

 (defthm collection-runtime-page-multiples-are-kernel-aligned
   (implies (and (integerp index) (proof-page-size-p page))
            (equal (mod (* *proof-runtime-page* index) page) 0))
   :hints (("Goal" :in-theory (e/d (acl2::fold-consts-in-*) (mod))))))

(local
 (defthm collection-page-floor-at-aligned-bound
   (implies (and (integerp address) (integerp index)
                 (<= (* *proof-runtime-page* index) address))
            (<= (* *proof-runtime-page* index) (collection-page-floor address)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::floor-weak-monotone
                                    (acl2::i1 (* *proof-runtime-page* index))
                                    (acl2::i2 address)
                                    (acl2::j *proof-runtime-page*)))))))

(local
 (defthm collection-page-floor-below-aligned-bound
   (implies (and (integerp address) (integerp index)
                 (< address (* *proof-runtime-page* (1+ index))))
            (<= (collection-page-floor address) (* *proof-runtime-page* index)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::floor-weak-monotone
                                    (acl2::i1 address)
                                    (acl2::i2 (1- (* *proof-runtime-page* (1+ index))))
                                    (acl2::j *proof-runtime-page*))
                         (:instance acl2::floor-unique
                                    (acl2::i (1- (* *proof-runtime-page* (1+ index))))
                                    (acl2::j *proof-runtime-page*)
                                    (acl2::n index)))))))

(local
 (defthm collection-integer-below-one
   (implies (and (integerp difference) (< difference 1))
            (<= difference 0))
   :rule-classes nil))

(defthm collection-retired-release-ranges
  (let* ((floor (* *proof-runtime-page* first-page))
         (end (* *proof-runtime-page* last-page))
         (header-end (collection-page-ceiling box))
         (cons-start (collection-page-floor cons-floor)))
    (implies (and (natp first-page) (natp last-page) (natp box) (natp cons-floor)
                  (<= floor box) (<= box cons-floor) (<= cons-floor end))
             (and (<= floor box) (<= box header-end) (<= header-end end)
                  (<= floor cons-start) (<= cons-start cons-floor) (<= cons-floor end))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance collection-page-floor-at-aligned-bound
                                   (address cons-floor) (index first-page))
                        (:instance collection-page-floor-below-aligned-bound
                                   (address (+ box (1- *proof-runtime-page*)))
                                   (index last-page))
                        (:instance collection-page-floor-bounds (address cons-floor))
                        (:instance acl2::floor-bounded-by-/
                                   (acl2::x (+ box (1- *proof-runtime-page*)))
                                   (acl2::y *proof-runtime-page*))
                        (:instance collection-integer-below-one
                                   (difference (- box (collection-page-ceiling box))))))))

(defthm collection-clearing-address-range-keeps-other-memory
  (implies (and (alistp memory)
                (not (and (<= start address) (< address end))))
           (equal (assoc-equal address (proof-clear-memory start end memory))
                  (assoc-equal address memory)))
  :hints (("Goal" :induct (proof-clear-memory start end memory))))

(defthm collection-clearing-address-range-removes-its-memory
  (implies (and (alistp memory) (<= start address) (< address end))
           (not (assoc-equal address (proof-clear-memory start end memory))))
  :hints (("Goal" :induct (proof-clear-memory start end memory))))
