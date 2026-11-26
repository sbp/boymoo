(in-package "BOYMOO-PROOFS")

(include-book "emission")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-world-stop proof-world-pc proof-instruction-at-p
                     proof-instruction-access-p proof-instruction-effect)))

(defun division-before-cuts-p (count cuts world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (not (proof-world-stop world))
         (not (member-equal (proof-world-pc world) cuts))
         (division-before-cuts-p (1- count) cuts (proof-step world)))))

(defthm division-before-cuts-append
  (equal (division-before-cuts-p (+ (nfix prefix) (nfix suffix)) cuts world)
         (and (division-before-cuts-p prefix cuts world)
              (division-before-cuts-p suffix cuts (proof-advance prefix world))))
  :hints (("Goal" :induct (proof-advance prefix world))))

(defthm division-run-after-cut-free-prefix
  (implies (division-before-cuts-p prefix cuts world)
           (equal (proof-run (+ (nfix prefix) (nfix suffix)) cuts world)
                  (proof-run suffix cuts (proof-advance prefix world))))
  :hints (("Goal" :induct (proof-advance prefix world))))

(defthm division-segment-from-cut-free-prefix
  (let ((after (proof-advance count world)))
    (implies (and (division-before-cuts-p count cuts world)
                  (not (proof-world-stop after))
                  (member-equal (proof-world-pc after) cuts))
             (proof-segment-p count cuts world :cut after)))
  :hints (("Goal" :use (:instance division-run-after-cut-free-prefix (prefix count) (suffix 0))
                  :in-theory (disable division-run-after-cut-free-prefix (:definition proof-advance))))
  :rule-classes nil)

(defun division-instruction-prefix-ready-p (instructions cuts world)
  (if (atom instructions)
      (null instructions)
    (and (not (proof-world-stop world))
         (not (member-equal (proof-world-pc world) cuts))
         (proof-instruction-at-p (car instructions) (proof-world-pc world) world)
         (proof-instruction-access-p (car instructions) world)
         (division-instruction-prefix-ready-p
          (cdr instructions) cuts (proof-instruction-effect (car instructions) world)))))

(defthm division-instruction-prefix-advances
  (implies (division-instruction-prefix-ready-p instructions cuts world)
           (and (division-before-cuts-p (len instructions) cuts world)
                (equal (proof-advance (len instructions) world)
                       (division-instruction-sequence instructions world))))
  :hints (("Goal" :induct (division-instruction-prefix-ready-p instructions cuts world)))
  :rule-classes nil)
