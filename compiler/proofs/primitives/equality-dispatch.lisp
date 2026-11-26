(in-package "BOYMOO-PROOFS")

(include-book "equality-entry")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable (:definition p6-runtime-offset) (:definition p6-sites))))

(defund p6-equal-operand-address (register world)
  (proof-pointer-address (proof-world-reg register world) (proof-heap-base world)))

(defund p6-equal-operand-header (register world)
  (p6-world-load 8 (p6-equal-operand-address register world) world))

(defund p6-equal-dispatch-case (world)
  (let* ((left-tag (proof-word-tag (proof-world-reg 0 world)))
         (right-tag (proof-word-tag (proof-world-reg 1 world)))
         (header (p6-equal-operand-header 0 world))
         (type (proof-header-type header)))
    (cond ((not (equal left-tag right-tag)) :different-tags)
          ((equal left-tag 0) :cons)
          ((not (equal left-tag 2)) :immediate)
          ((not (equal header (p6-equal-operand-header 1 world))) :different-headers)
          ((equal type 2) :symbol)
          ((< type 4) :bytes)
          ((equal type 6) :vector)
          (t :fields))))

(defund p6-equal-dispatch-sites (case)
  (case case
    (:different-tags (p6-sites "rt:equal-distinct" 3))
    (:cons (p6-sites "rt:equal-distinct" 5))
    (:immediate (p6-sites "rt:equal-distinct" 7))
    (:different-headers (p6-sites "rt:equal-distinct" 15))
    (:symbol (p6-sites "rt:equal-distinct" 18))
    (:bytes (p6-sites "rt:equal-distinct" 22))
    (:vector (p6-sites "rt:equal-distinct" 24))
    (otherwise (p6-sites "rt:equal-distinct" 25))))

(defund p6-equal-dispatch-target (case base)
  (+ base (p6-runtime-offset (case case
                                 (:cons "rt:equal-cons")
                                 (:bytes "rt:equal-byte-span")
                                 (:vector "rt:equal-vector")
                                 (:fields "rt:equal-fields")
                                 (otherwise "rt:equal-no")))))

(defund p6-equal-dispatch-pre-p (base world)
  (let* ((case (p6-equal-dispatch-case world))
         (target (p6-equal-dispatch-target case base))
         (regions (proof-world-regions world)))
    (and (p6-path-entry-p (p6-equal-dispatch-sites case) base world)
         (unsigned-byte-p 64 target) (not (equal target (proof-world-reg 30 world)))
         (or (member-eq case '(:different-tags :cons :immediate))
             (and (proof-covered-p (p6-equal-operand-address 0 world) 8 :read regions)
                  (proof-covered-p (p6-equal-operand-address 1 world) 8 :read regions))))))

(defund p6-equal-dispatch-post-p (case base before)
  (let* ((sites (p6-equal-dispatch-sites case))
         (after (p6-path-end sites before)))
    (and (equal (proof-world-pc after) (p6-equal-dispatch-target case base))
         (not (equal (proof-world-pc after) (proof-world-reg 30 before)))
         (not (proof-world-stop after)) (p6-register-file-p after)
         (p6-same-mapped-memory-p before after) (equal (cdr before) (cdr after))
         (equal (boymoo-model::a64-sp (proof-world-machine before))
                (boymoo-model::a64-sp (proof-world-machine after)))
         (proof-register-frame-p 30 '(0 1 2 3) before after)
         (p6-read-only-path-p sites base (list (proof-world-reg 30 before)) before)
         (implies (eq case :cons)
                  (and (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                       (equal (proof-world-reg 1 after) (proof-world-reg 1 before))))
         (implies (member-eq case '(:bytes :vector :fields))
                  (and (equal (proof-world-reg 0 after)
                              (boymoo-model::a64-unsigned 64 (+ 8 (p6-equal-operand-address 0 before))))
                       (equal (proof-world-reg 1 after)
                              (boymoo-model::a64-unsigned 64 (+ 8 (p6-equal-operand-address 1 before))))
                       (equal (proof-world-reg 2 after) (p6-equal-operand-header 0 before))
                       (equal (proof-world-reg 3 after) (proof-header-type (p6-equal-operand-header 0 before))))))))

(defthm p6-equal-dispatch-classifies-pair
  (implies (p6-equal-dispatch-pre-p base world)
           (p6-equal-dispatch-post-p (p6-equal-dispatch-case world) base world))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-dispatch-pre-p p6-equal-dispatch-post-p p6-equal-dispatch-case
                                                   p6-equal-dispatch-sites p6-equal-dispatch-target
                                                   p6-equal-operand-address p6-equal-operand-header
                                                   p6-path-entry-p p6-path-end p6-same-mapped-memory-p
                                                   proof-pointer-address proof-header-type proof-word-tag)
                           (p6-sites-placed-p p6-loaded-header-fields)))))

(defthm p6-equal-dispatch-runs
  (let* ((case (p6-equal-dispatch-case world)) (sites (p6-equal-dispatch-sites case)))
    (implies (p6-equal-dispatch-pre-p base world)
             (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :limit
                              (p6-path-end sites world))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-dispatch-pre-p p6-equal-dispatch-post-p p6-path-entry-p proof-segment-p)
                           (p6-path-end p6-read-only-path-p proof-register-frame-p p6-sites-placed-p))
           :use (p6-equal-dispatch-classifies-pair
                 (:instance p6-read-only-path-runs
                            (sites (p6-equal-dispatch-sites (p6-equal-dispatch-case world)))
                            (cuts (list (proof-world-reg 30 world))))))))

(defthm p6-equal-symbol-dispatch-uses-published-identity
  (implies (and (eq (p6-equal-dispatch-case world) :symbol)
                (not (equal (proof-world-reg 0 world) (proof-world-reg 1 world)))
                (proof-heap-p world objects packages)
                (proof-reg-value-p 0 first world objects packages)
                (proof-reg-value-p 1 second world objects packages))
           (not (equal first second)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-heap-p proof-reg-value-p p6-equal-dispatch-case p6-equal-operand-address
                                         p6-equal-operand-header p6-world-load proof-load-word
                                         p6-word-class p6-datum-class)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                            proof-heap-object-spans-p proof-string-accounting-p proof-dynamic-symbol-objects-p
                            proof-dynamic-view proof-dynamic-entries proof-stack-prefix p6-loaded-header-fields
                            p6-even-as-mod proof-immediate-integer-p))
           :use ((:instance p6-word-class-of-value
                            (word (proof-world-reg 0 world)) (value first)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-word-class-of-value
                            (word (proof-world-reg 1 world)) (value second)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-even-tag-is-not-an-immediate-integer (word (proof-world-reg 0 world)))
                 (:instance p6-even-tag-is-not-an-immediate-integer (word (proof-world-reg 1 world)))
                 (:instance p6-published-symbols-equal-exactly-by-word
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))))))
