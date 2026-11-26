(in-package "BOYMOO-PROOFS")

(include-book "numeric-projections")
(include-book "machine-stack")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-numeric-prologue-sites (name)
  (case name
    (numerator (p6-sites "prim:COMMON-LISP::NUMERATOR" 4))
    (denominator (p6-sites "prim:COMMON-LISP::DENOMINATOR" 4))
    (realpart (p6-sites "prim:COMMON-LISP::REALPART" 4))
    (imagpart (p6-sites "prim:COMMON-LISP::IMAGPART" 4))))

(defund p6-numeric-restore-sites (name)
  (case name
    (numerator (nthcdr 4 (p6-sites "prim:COMMON-LISP::NUMERATOR" 5)))
    (denominator (nthcdr 4 (p6-sites "prim:COMMON-LISP::DENOMINATOR" 5)))
    (realpart (nthcdr 4 (p6-sites "prim:COMMON-LISP::REALPART" 5)))
    (imagpart (nthcdr 4 (p6-sites "prim:COMMON-LISP::IMAGPART" 5)))))

(defund p6-numeric-save-world (before)
  (p6-store-register-pair 29 30 (- (p6-sp before) 16) before))

(defund p6-numeric-type-target (base)
  (+ base (p6-runtime-offset "rt:num-type")))

(defthm p6-numeric-prologue-saves-link-and-calls
  (let* ((sites (p6-numeric-prologue-sites name))
         (after (p6-path-end sites world))
         (target (p6-numeric-type-target base))
         (link (+ base (caar (p6-numeric-restore-sites name)))))
    (implies (and (member-equal name *p6-numeric-projections*)
                  (p6-register-file-p world) (not (oddp (proof-world-reg 0 world)))
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 link)
                  (<= 16 (p6-sp world)))
             (and (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) link)
                  (equal (p6-sp after) (- (p6-sp world) 16))
                  (proof-register-frame-p 30 '(30) world after)
                  (equal (proof-world-stop world) (proof-world-stop after))
                  (p6-register-file-p after)
                  (p6-same-mapped-memory-p (p6-numeric-save-world world) after)
                  (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-numeric-prologue-sites p6-numeric-restore-sites p6-numeric-type-target
                                                     p6-numeric-save-world p6-store-register-pair
                                                     p6-path-end p6-same-mapped-memory-p)
                           (boymoo-model::a64-write-bytes)))))

(defthm p6-numeric-prologue-checked-call
  (let* ((sites (p6-numeric-prologue-sites name))
         (target (p6-numeric-type-target base))
         (link (+ base (caar (p6-numeric-restore-sites name))))
         (cuts (list (proof-world-reg 30 world)))
         (after (p6-path-end sites world)))
    (implies (and (member-equal name *p6-numeric-projections*)
                  (p6-register-file-p world) (not (oddp (proof-world-reg 0 world)))
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 link)
                  (not (equal target (proof-world-reg 30 world)))
                  (<= 16 (p6-sp world)) (not (proof-world-stop world))
                  (p6-checked-path-p sites base cuts world))
             (and (proof-segment-p (len sites) cuts world :limit after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) link)
                  (equal (p6-sp after) (- (p6-sp world) 16))
                  (proof-register-frame-p 30 '(30) world after)
                  (p6-same-mapped-memory-p (p6-numeric-save-world world) after))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-segment-p)
                           (p6-checked-path-p p6-path-end proof-register-frame-p))
           :use (p6-numeric-prologue-saves-link-and-calls
                 (:instance p6-checked-path-runs (sites (p6-numeric-prologue-sites name))
                            (cuts (list (proof-world-reg 30 world))))))))

(defthm p6-numeric-restore-loads-saved-registers
  (let* ((sites (p6-numeric-restore-sites name))
         (after (p6-path-end sites world)))
    (implies (and (member-equal name *p6-numeric-projections*) (p6-register-file-p world)
                  (proof-span-p (p6-sp world) 16) (< (+ 16 (p6-sp world)) (expt 2 64)))
             (and (equal (proof-world-reg 29 after) (p6-world-load 8 (p6-sp world) world))
                  (equal (proof-world-reg 30 after) (p6-world-load 8 (+ 8 (p6-sp world)) world))
                  (equal (p6-sp after) (+ (p6-sp world) 16))
                  (p6-same-mapped-memory-p world after)
                  (proof-register-frame-p 30 '(29 30) world after)
                  (equal (proof-world-stop world) (proof-world-stop after))
                  (p6-register-file-p after)
                  (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-numeric-restore-sites p6-path-end p6-same-mapped-memory-p
                              proof-span-p))))

(defthm p6-numeric-save-and-restore-agree
  (let* ((sites (p6-numeric-restore-sites name))
         (after (p6-path-end sites middle)))
    (implies (and (member-equal name *p6-numeric-projections*) (p6-register-file-p middle)
                  (<= 16 (p6-sp before))
                  (equal (p6-sp middle) (- (p6-sp before) 16))
                  (p6-same-mapped-memory-p (p6-numeric-save-world before) middle))
             (and (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
                  (equal (p6-sp after) (p6-sp before))
                  (proof-register-frame-p 30 '(29 30) middle after)
                  (equal (cdr middle) (cdr after))
                  (p6-same-mapped-memory-p (p6-numeric-save-world before) after))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-numeric-save-world p6-world-load boymoo-model::a64-load
                                                   p6-same-mapped-memory-p proof-span-p)
                           (p6-path-end proof-register-frame-p p6-sp-is-a-word p6-read-bytes-step))
           :use ((:instance p6-numeric-restore-loads-saved-registers (world middle))
                 (:instance p6-load-stored-register-pair
                            (first 29) (second 30) (address (- (p6-sp before) 16)) (world before))
                 (:instance p6-sp-is-a-word (world before))))))
