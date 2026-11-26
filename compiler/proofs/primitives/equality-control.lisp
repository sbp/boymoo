(in-package "BOYMOO-PROOFS")

(include-book "equality-entry")
(include-book "equality-stack")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable (:definition p6-runtime-offset) (:definition p6-sites))))

(defconst *p6-equal-pair-sites* (p6-sites "rt:equal-pair" 2))

(defund p6-equal-pair-target (same base)
  (+ base (p6-runtime-offset (if same "rt:equal-next" "rt:equal-distinct"))))

(defthm p6-equal-pair-compares-words
  (let* ((sites *p6-equal-pair-sites*) (after (p6-path-end sites world))
         (same (equal (proof-world-reg 0 world) (proof-world-reg 1 world)))
         (target (p6-equal-pair-target same base)))
    (implies (and (p6-path-entry-p sites base world) (unsigned-byte-p 64 target)
                  (not (equal target (proof-world-reg 30 world))))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :limit after)
                  (equal (proof-world-pc after) target)
                  (proof-register-frame-p 30 nil world after)
                  (equal (p6-sp after) (p6-sp world))
                  (p6-same-mapped-memory-p world after) (equal (cdr after) (cdr world)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-pair-target p6-path-entry-p p6-path-end
                                                p6-same-mapped-memory-p proof-segment-p)
                           (p6-sites-placed-p))
           :use ((:instance p6-read-only-path-runs
                            (sites *p6-equal-pair-sites*) (cuts (list (proof-world-reg 30 world))))))))

(defconst *p6-equal-second-sites* (p6-sites "rt:equal-second" 3))

(defthm p6-equal-second-installs-pair
  (let* ((sites *p6-equal-second-sites*) (after (p6-path-end sites world))
         (target (+ base (p6-runtime-offset "rt:equal-pair"))))
    (implies (and (p6-path-entry-p sites base world) (unsigned-byte-p 64 target)
                  (not (equal target (proof-world-reg 30 world))))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :limit after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after) (proof-world-reg 2 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 3 world))
                  (proof-register-frame-p 30 '(0 1) world after)
                  (equal (p6-sp after) (p6-sp world))
                  (p6-same-mapped-memory-p world after) (equal (cdr after) (cdr world)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-path-entry-p p6-path-end p6-same-mapped-memory-p proof-segment-p)
                           (p6-sites-placed-p))
           :use ((:instance p6-read-only-path-runs
                            (sites *p6-equal-second-sites*) (cuts (list (proof-world-reg 30 world))))))))

(defconst *p6-equal-cons-sites* (p6-sites "rt:equal-cons" 2))

(defthm p6-equal-cons-installs-field-addresses
  (let* ((sites *p6-equal-cons-sites*) (after (p6-path-end sites world))
         (target (+ base (p6-runtime-offset "rt:equal-fields")))
         (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world)))
    (implies (and (p6-path-entry-p sites base world) (unsigned-byte-p 64 target)
                  (not (equal target (proof-world-reg 30 world)))
                  (equal (proof-word-tag left) 0) (equal (proof-word-tag right) 0))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :limit after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after) (proof-pointer-address left (proof-heap-base world)))
                  (equal (proof-world-reg 1 after) (proof-pointer-address right (proof-heap-base world)))
                  (proof-register-frame-p 30 '(0 1) world after)
                  (equal (p6-sp after) (p6-sp world))
                  (p6-same-mapped-memory-p world after) (equal (cdr after) (cdr world)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-path-entry-p p6-path-end p6-same-mapped-memory-p
                                          proof-pointer-address proof-segment-p)
                           (p6-sites-placed-p))
           :use ((:instance p6-read-only-path-runs
                            (sites *p6-equal-cons-sites*) (cuts (list (proof-world-reg 30 world))))))))
