(in-package "BOYMOO-PROOFS")

(include-book "machine-stack")
(include-book "leaf-routines")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable (:definition p6-runtime-offset) (:definition p6-sites))))

(defund p6-field-comparison-case (world)
  (let ((left (proof-world-reg 0 world)) (right (proof-world-reg 1 world)))
    (cond ((equal (p6-world-load 8 left world) (p6-world-load 8 right world)) :second)
          ((equal (p6-world-load 8 (+ 8 left) world) (p6-world-load 8 (+ 8 right) world)) :first)
          (t :defer))))

(defund p6-field-comparison-sites (case)
  (case case
    (:second (p6-sites "rt:equal-fields" 4))
    (:first (p6-sites "rt:equal-fields" 6))
    (otherwise (p6-sites "rt:equal-fields" 8))))

(defund p6-field-comparison-target (case base)
  (+ base (p6-runtime-offset (case case
                                 (:second "rt:equal-second")
                                 (:first "rt:equal-distinct")
                                 (otherwise "rt:ensure-stack")))))

(defund p6-field-comparison-save-link (base)
  (+ base (p6-runtime-offset "rt:equal-fields") 32))

(defund p6-field-comparison-entry-p (base world)
  (let* ((case (p6-field-comparison-case world))
         (target (p6-field-comparison-target case base))
         (regions (proof-world-regions world)))
    (and (p6-path-entry-p (p6-field-comparison-sites case) base world)
         (unsigned-byte-p 64 target) (not (equal target (proof-world-reg 30 world)))
         (proof-covered-p (proof-world-reg 0 world) 16 :read regions)
         (proof-covered-p (proof-world-reg 1 world) 16 :read regions)
         (implies (eq case :defer)
                  (and (unsigned-byte-p 64 (p6-field-comparison-save-link base))
                       (unsigned-byte-p 64 (+ 16 (proof-world-reg 25 world))))))))

(defund p6-field-comparison-post-p (case base world)
  (let* ((sites (p6-field-comparison-sites case)) (after (p6-path-end sites world))
         (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world)))
    (and (equal (proof-world-pc after) (p6-field-comparison-target case base))
         (not (equal (proof-world-pc after) (proof-world-reg 30 world)))
         (not (proof-world-stop after)) (p6-register-file-p after)
         (equal (p6-sp after) (p6-sp world))
         (p6-same-mapped-memory-p world after) (equal (cdr world) (cdr after))
         (p6-read-only-path-p sites base (list (proof-world-reg 30 world)) world)
         (proof-register-frame-p 30 (if (eq case :defer) '(0 1 2 3 8 30) '(0 1 2 3)) world after)
         (equal (proof-world-reg 0 after) (p6-world-load 8 left world))
         (equal (proof-world-reg 1 after) (p6-world-load 8 right world))
         (equal (proof-world-reg 2 after) (p6-world-load 8 (+ 8 left) world))
         (equal (proof-world-reg 3 after) (p6-world-load 8 (+ 8 right) world))
         (implies (eq case :defer)
                  (and (equal (proof-world-reg 8 after) (+ 16 (proof-world-reg 25 world)))
                       (equal (proof-world-reg 30 after) (p6-field-comparison-save-link base)))))))

(defthm p6-equal-fields-selects-comparison
  (implies (p6-field-comparison-entry-p base world)
           (p6-field-comparison-post-p (p6-field-comparison-case world) base world))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-field-comparison-entry-p p6-field-comparison-post-p
                                                       p6-field-comparison-case p6-field-comparison-sites
                                                       p6-field-comparison-target p6-field-comparison-save-link
                                                       p6-path-entry-p p6-path-end p6-same-mapped-memory-p)
                           (p6-sites-placed-p)))))

(defthm p6-equal-fields-dispatch-runs
  (let* ((case (p6-field-comparison-case world)) (sites (p6-field-comparison-sites case)))
    (implies (p6-field-comparison-entry-p base world)
             (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :limit
                              (p6-path-end sites world))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-field-comparison-entry-p p6-field-comparison-post-p
                                                       p6-path-entry-p proof-segment-p)
                           (p6-path-end p6-read-only-path-p proof-register-frame-p p6-sites-placed-p))
           :use (p6-equal-fields-selects-comparison
                 (:instance p6-read-only-path-runs
                            (sites (p6-field-comparison-sites (p6-field-comparison-case world)))
                            (cuts (list (proof-world-reg 30 world))))))))
