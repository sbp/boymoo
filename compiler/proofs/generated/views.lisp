(in-package "BOYMOO-PROOFS")

(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine proof-world-reg proof-load-word
                    boymoo-model::a64-load boymoo-model::a64-memory
                    proof-load-string proof-byte-list proof-limbs-p proof-limb-magnitude
                    proof-integer-view proof-view-step proof-view proof-machine-value-p
                    proof-subspan-p proof-cons-value proof-rational-value proof-complex-value
                    proof-symbol-value generated-load-word))

(defund generated-memory-equiv (first second)
  (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory second)))

(defequiv generated-memory-equiv
  :hints (("Goal" :in-theory (enable generated-memory-equiv))))

(defcong generated-memory-equiv equal (boymoo-model::a64-load count address machine) 3
  :hints (("Goal" :in-theory (enable generated-memory-equiv boymoo-model::a64-load))))

(defcong generated-memory-equiv equal (proof-load-word address machine) 2
  :hints (("Goal" :in-theory (enable proof-load-word))))

(defcong generated-memory-equiv equal (proof-byte-list count address machine) 3
  :hints (("Goal" :induct (proof-byte-list count address machine)
                  :in-theory (enable proof-byte-list))))

(defcong generated-memory-equiv equal (proof-load-string count address machine) 3
  :hints (("Goal" :in-theory (enable proof-load-string))))

(defcong generated-memory-equiv equal (proof-limb-magnitude count address machine) 3
  :hints (("Goal" :induct (proof-limb-magnitude count address machine)
                  :in-theory (enable proof-limb-magnitude))))

(defcong generated-memory-equiv equal (proof-limbs-p count address machine) 3
  :hints (("Goal" :induct (proof-limbs-p count address machine)
                  :in-theory (enable proof-limbs-p))))

(defcong generated-memory-equiv equal (proof-integer-view address machine) 2
  :hints (("Goal" :in-theory (enable proof-integer-view))))

(defcong generated-memory-equiv equal
  (proof-view-step kind input count depth base objects packages machine) 8
  :hints (("Goal" :induct (proof-view-step kind input count depth base objects packages machine)
                  :in-theory (enable proof-view-step))))

(defcong generated-memory-equiv equal (proof-view word base objects packages machine) 5
  :hints (("Goal" :in-theory (enable proof-view))))

(defcong generated-memory-equiv equal (proof-stack-views count address base objects packages machine) 6)

(defthm generated-memory-equiv-of-register-updates
  (and (generated-memory-equiv (proof-world-machine (generated-set-pc pc world))
                               (proof-world-machine world))
       (generated-memory-equiv (proof-world-machine (generated-set-reg register datum world))
                               (proof-world-machine world))
       (generated-memory-equiv (proof-world-machine (generated-set-flags flags world))
                               (proof-world-machine world))
       (generated-memory-equiv (proof-world-machine (generated-set-sp sp world))
                               (proof-world-machine world)))
  :hints (("Goal" :in-theory (enable generated-memory-equiv))))

(defthm generated-environment-binding
  (implies (and (proof-environment-p bindings env frame world objects packages)
                (member-equal (cons variable slot) bindings))
           (let ((address (+ frame (* 8 slot))))
             (and (natp slot) (assoc-eq variable env)
                  (proof-subspan-p address 8 (proof-stack-base world) (proof-stack-top world))
                  (proof-machine-value-p (generated-load-word address world)
                                         (cdr (assoc-eq variable env)) world objects packages))))
  :hints (("Goal" :induct (proof-environment-p bindings env frame world objects packages)
                  :in-theory (enable generated-load-word)))
  :rule-classes nil)

(local
 (defthm generated-immediate-encoding-negative
   (implies (and (proof-immediate-integer-p value) (< value 0))
            (equal (proof-integer-word value)
                   (+ (expt 2 64) (1+ (* 2 value)))))
   :hints (("Goal"
            :use (:instance generated-unsigned-of-remainder
                            (n 64) (q -1) (x (1+ (* 2 value)))
                            (r (+ (expt 2 64) (1+ (* 2 value)))))))))

(local
 (defthm generated-immediate-encoding-nonnegative
   (implies (and (proof-immediate-integer-p value) (<= 0 value))
            (equal (proof-integer-word value) (1+ (* 2 value))))))

(defthm generated-immediate-word-is-odd
  (implies (proof-immediate-integer-p value)
           (not (evenp (proof-integer-word value))))
  :hints (("Goal" :cases ((< value 0))
                  :use ((:instance generated-odd-double-plus-one (q value))
                        (:instance generated-odd-double-plus-one (q (+ (expt 2 63) value))))
                  :in-theory (disable generated-odd-double-plus-one evenp proof-integer-word))))

(defthm generated-signed-of-immediate-word
  (implies (proof-immediate-integer-p value)
           (equal (boymoo-model::a64-signed 64 (proof-integer-word value))
                  (1+ (* 2 value))))
  :hints (("Goal"
           :use (:instance generated-signed-64-of-signed-range (x (1+ (* 2 value))))
           :in-theory (e/d (generated-signed-64-of-word)
                           (generated-signed-64-of-signed-range)))))

(local
 (defthm generated-ash-down-by-one
   (implies (integerp bits) (equal (ash bits -1) (floor bits 2)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(defthm generated-immediate-word-view
  (implies (proof-immediate-integer-p value)
           (equal (proof-view (proof-integer-word value) base objects packages machine)
                  (proof-value-view value)))
  :hints (("Goal"
           :use (generated-immediate-word-is-odd generated-signed-of-immediate-word
                 (:instance generated-unsigned-bounds (n 64) (x (1+ (* 2 value))))
                 (:instance generated-floor-of-multiple-and-remainder
                            (divisor 2) (q value) (r 1)))
           :in-theory (e/d (proof-view proof-view-step oddp)
                           (generated-immediate-word-is-odd generated-signed-of-immediate-word
                            boymoo-model::a64-signed proof-word-tag))))
  :rule-classes nil)
