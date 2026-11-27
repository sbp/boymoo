(in-package "BOYMOO-PROOFS")

(include-book "equality-views")
(include-book "machine-stack")
(include-book "state-invariants")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable (:definition p6-runtime-offset) (:definition p6-sites))))

(defconst *p6-equal-pop-sites* (p6-sites "rt:equal-next" 5))

(defund p6-equal-pop-pre-p (base world)
  (let ((top (proof-world-reg 25 world))
        (saved-top (p6-world-load 8 (p6-sp world) world))
        (target (+ base (p6-runtime-offset "rt:equal-pair"))))
    (and (p6-path-entry-p *p6-equal-pop-sites* base world)
         (<= 16 top) (not (equal top saved-top))
         (equal (mod (p6-sp world) 16) 0)
         (proof-covered-p (p6-sp world) 8 :read (proof-world-regions world))
         (proof-covered-p (- top 16) 16 :read (proof-world-regions world))
         (unsigned-byte-p 64 target) (not (equal target (proof-world-reg 30 world))))))

(defthm p6-equal-deferred-pop-block
  (let* ((top (proof-world-reg 25 world))
         (after (p6-path-end *p6-equal-pop-sites* world)))
    (implies (p6-equal-pop-pre-p base world)
             (and (p6-read-only-path-p *p6-equal-pop-sites* base (list (proof-world-reg 30 world)) world)
                  (equal (proof-world-pc after) (+ base (p6-runtime-offset "rt:equal-pair")))
                  (not (equal (proof-world-pc after) (proof-world-reg 30 world)))
                  (not (proof-world-stop after))
                  (equal (proof-world-reg 25 after) (- top 16))
                  (equal (proof-world-reg 0 after) (p6-world-load 8 (- top 16) world))
                  (equal (proof-world-reg 1 after) (p6-world-load 8 (- top 8) world))
                  (equal (p6-sp after) (p6-sp world))
                  (proof-register-frame-p 30 '(0 1 7 25) world after)
                  (p6-same-mapped-memory-p world after)
                  (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-pop-pre-p p6-path-entry-p p6-path-end p6-same-mapped-memory-p)
                           (p6-sites-placed-p)))))

(defthm p6-equal-deferred-pop-runs
  (implies (p6-equal-pop-pre-p base world)
           (proof-segment-p (len *p6-equal-pop-sites*) (list (proof-world-reg 30 world)) world :limit
                            (p6-path-end *p6-equal-pop-sites* world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-pop-pre-p p6-path-entry-p proof-segment-p)
                           (p6-path-end p6-read-only-path-p p6-sites-placed-p proof-register-frame-p))
           :use (p6-equal-deferred-pop-block
                 (:instance p6-read-only-path-runs (sites *p6-equal-pop-sites*)
                            (cuts (list (proof-world-reg 30 world))))))))

(defcong p6-memory-equiv equal (p6-deferred-conjunction count top base objects packages machine) 6
  :hints (("Goal" :induct (p6-deferred-conjunction count top base objects packages machine))))

(local
 (defthm p6-memory-equiv-from-same-mapped-memory
   (implies (p6-same-mapped-memory-p world after)
            (p6-memory-equiv (proof-world-machine world) (proof-world-machine after)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable p6-same-mapped-memory-p p6-memory-equiv)))))

(defthm p6-equal-pop-exposes-next-conjunct
  (let* ((top (proof-world-reg 25 world))
         (machine (proof-world-machine world))
         (after (p6-path-end *p6-equal-pop-sites* world))
         (last (proof-world-machine after)))
    (implies (and (posp count) (p6-equal-pop-pre-p base world))
             (equal (p6-deferred-conjunction count top heap-base objects packages machine)
                    (and (equal (proof-view (proof-world-reg 0 after) heap-base objects packages last)
                                (proof-view (proof-world-reg 1 after) heap-base objects packages last))
                         (p6-deferred-conjunction (1- count) (proof-world-reg 25 after) heap-base objects packages last)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-world-load proof-load-word)
                           (p6-path-end p6-read-only-path-p p6-deferred-conjunction proof-register-frame-p))
           :use ((:instance p6-deferred-conjunction-pop (top (proof-world-reg 25 world))
                            (base heap-base) (machine (proof-world-machine world)))
                 p6-equal-deferred-pop-block))))

(defconst *p6-equal-field-push-sites* (nthcdr 8 (p6-sites "rt:equal-fields" 11)))
(defconst *p6-equal-vector-push-sites* (nthcdr 7 (p6-sites "rt:equal-vector-word" 9)))

(defund p6-equal-push-sites (kind)
  (if (eq kind :fields) *p6-equal-field-push-sites* *p6-equal-vector-push-sites*))

(defund p6-equal-push-target (kind base)
  (+ base (p6-runtime-offset (if (eq kind :fields) "rt:equal-distinct" "rt:equal-vector-loop"))))

(defund p6-equal-pushed-pair-world (kind world)
  (if (eq kind :fields)
      (p6-store-register-pair 2 3 (proof-world-reg 25 world) world)
    (p6-store-register-pair 0 1 (proof-world-reg 25 world) world)))

(defthm p6-equal-deferred-push-block
  (let* ((sites (p6-equal-push-sites kind))
         (after (p6-path-end sites world))
         (top (proof-world-reg 25 world))
         (target (p6-equal-push-target kind base)))
    (implies (and (p6-register-file-p world) (natp base)
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (unsigned-byte-p 64 (+ base (caar (last sites))))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 (+ top 16)))
             (and (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 25 after) (+ 16 top))
                  (equal (p6-sp after) (p6-sp world))
                  (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                         (boymoo-model::a64-nzcv (proof-world-machine world)))
                  (proof-register-frame-p 30 '(25) world after)
                  (p6-same-mapped-memory-p (p6-equal-pushed-pair-world kind world) after)
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-push-sites p6-equal-push-target p6-equal-pushed-pair-world
                                               p6-path-end p6-store-register-pair p6-same-mapped-memory-p)
                           (boymoo-model::a64-write-bytes)))))

(defthm p6-equal-deferred-push-runs
  (let* ((sites (p6-equal-push-sites kind)) (cuts (list return-address))
         (after (p6-path-end sites world))
         (top (proof-world-reg 25 world)) (target (p6-equal-push-target kind base))
         (first (if (eq kind :fields) 2 0)) (second (if (eq kind :fields) 3 1)))
    (implies (and (p6-register-file-p world) (natp base) (not (proof-world-stop world))
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (unsigned-byte-p 64 (+ base (caar (last sites))))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 (+ top 16))
                  (not (equal target return-address))
                  (p6-checked-path-p sites base cuts world))
             (and (proof-segment-p (len sites) cuts world :limit after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 25 after) (+ 16 top))
                  (equal (p6-world-load 8 top after) (proof-world-reg first world))
                  (equal (p6-world-load 8 (+ 8 top) after) (proof-world-reg second world))
                  (p6-same-mapped-memory-p (p6-equal-pushed-pair-world kind world) after)
                  (proof-register-frame-p 30 '(25) world after))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-segment-p p6-equal-pushed-pair-world p6-world-load proof-span-p)
                           (p6-path-end p6-checked-path-p proof-register-frame-p))
           :use (p6-equal-deferred-push-block
                 (:instance p6-checked-path-runs (sites (p6-equal-push-sites kind)) (cuts (list return-address)))
                 (:instance p6-load-stored-register-pair
                            (address (proof-world-reg 25 world))
                            (first (if (eq kind :fields) 2 0)) (second (if (eq kind :fields) 3 1)))))))

(defund p6-equal-return-sites (truth)
  (if truth
      (append (p6-sites "rt:equal-yes" 2) (p6-literal-sites "rt:true"))
    (append (p6-sites "rt:equal-no" 2) (p6-literal-sites "rt:nil"))))

(defthm p6-equal-epilogue-restores-top-and-link
  (let* ((sites (p6-equal-return-sites truth))
         (after (p6-path-end sites world))
         (saved-link (p6-world-load 8 (+ 8 (p6-sp world)) world)))
    (implies (and (p6-register-file-p world) (natp base)
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (p6-site-addresses-p sites base saved-link)
                  (unsigned-byte-p 64 (+ 16 (p6-sp world))))
             (and (equal (proof-world-reg 0 after) (p6-boolean-word truth))
                  (equal (proof-world-reg 25 after) (p6-world-load 8 (p6-sp world) world))
                  (equal (proof-world-reg 30 after) saved-link)
                  (equal (proof-world-pc after) saved-link)
                  (equal (p6-sp after) (+ 16 (p6-sp world)))
                  (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                         (boymoo-model::a64-nzcv (proof-world-machine world)))
                  (proof-register-frame-p 30 '(0 25 30) world after)
                  (p6-same-mapped-memory-p world after)
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable p6-equal-return-sites p6-boolean-word p6-literal-sites
                                     p6-path-end p6-same-mapped-memory-p))))

(defthm p6-equal-epilogue-returns
  (let* ((sites (p6-equal-return-sites truth))
         (after (p6-path-end sites world))
         (saved-link (p6-world-load 8 (+ 8 (p6-sp world)) world))
         (cuts (list saved-link)))
    (implies (and (p6-register-file-p world) (not (proof-world-stop world)) (natp base)
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (p6-site-addresses-p sites base saved-link)
                  (unsigned-byte-p 64 (+ 16 (p6-sp world)))
                  (p6-checked-path-p sites base cuts world))
             (and (proof-segment-p (len sites) cuts world :cut after)
                  (equal (proof-world-reg 0 after) (p6-boolean-word truth))
                  (equal (proof-world-reg 25 after) (p6-world-load 8 (p6-sp world) world))
                  (equal (proof-world-reg 30 after) saved-link)
                  (equal (p6-sp after) (+ 16 (p6-sp world)))
                  (proof-register-frame-p 30 '(0 25 30) world after)
                  (p6-same-mapped-memory-p world after))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-segment-p)
                           (p6-checked-path-p p6-path-end p6-site-addresses-p proof-register-frame-p))
           :use (p6-equal-epilogue-restores-top-and-link
                 (:instance p6-checked-path-runs (sites (p6-equal-return-sites truth))
                            (cuts (list (p6-world-load 8 (+ 8 (p6-sp world)) world))))))))

; The stack supplies the words. The reference heap supplies their views.
; Fixing the reference permits changes to the stack while a comparison runs.
(defun p6-deferred-conjunction-in-reference-heap (count top base objects packages stack-machine reference-machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (equal (proof-view (proof-load-word (- top 16) stack-machine) base objects packages reference-machine)
                (proof-view (proof-load-word (- top 8) stack-machine) base objects packages reference-machine))
         (p6-deferred-conjunction-in-reference-heap (1- count) (- top 16) base objects packages
                                                     stack-machine reference-machine))))

(defthm p6-deferred-conjunction-with-current-heap
  (equal (p6-deferred-conjunction-in-reference-heap count top base objects packages machine machine)
         (p6-deferred-conjunction count top base objects packages machine))
  :rule-classes nil
  :hints (("Goal" :induct (p6-deferred-conjunction count top base objects packages machine))))

(defcong p6-memory-equiv equal
  (p6-deferred-conjunction-in-reference-heap count top base objects packages stack-machine reference-machine) 6
  :hints (("Goal"
           :induct (p6-deferred-conjunction-in-reference-heap count top base objects packages
                                                               stack-machine reference-machine))))

(local
 (defthm p6-storing-pair-preserves-earlier-conjunction
   (let ((saved (p6-store-register-pair first second address world)))
     (implies (and (natp count) (integerp top) (<= (* 16 count) top) (<= top address)
                   (proof-span-p address 16))
              (equal (p6-deferred-conjunction-in-reference-heap count top base objects packages
                                                                  (proof-world-machine saved) reference)
                     (p6-deferred-conjunction-in-reference-heap count top base objects packages
                                                                  (proof-world-machine world) reference))))
   :rule-classes nil
   :hints (("Goal"
            :induct (p6-deferred-conjunction-in-reference-heap count top base objects packages
                                                                (proof-world-machine world) reference)
            :in-theory (e/d (proof-span-p proof-disjoint-p proof-load-word p6-world-load)
                            (p6-load-equality-is-byte-list-equality))
            :expand ((:free (stack-machine)
                            (p6-deferred-conjunction-in-reference-heap count top base objects packages
                                                                        stack-machine reference))))
           ("Subgoal *1/2"
            :use ((:instance p6-load-outside-stored-register-pair (width 8) (source (- top 16)))
                  (:instance p6-load-outside-stored-register-pair (width 8) (source (- top 8)))))
           ("Subgoal *1/3"
            :use ((:instance p6-load-outside-stored-register-pair (width 8) (source (- top 16)))
                  (:instance p6-load-outside-stored-register-pair (width 8) (source (- top 8))))))))

(defthm p6-deferred-pair-store-extends-conjunction
  (let ((saved (p6-store-register-pair first second top world)))
    (implies (and (natp count) (<= (* 16 count) top) (proof-span-p top 16))
             (equal (p6-deferred-conjunction-in-reference-heap (1+ count) (+ top 16) base objects packages
                                                                 (proof-world-machine saved) reference)
                    (and (equal (proof-view (proof-world-reg first world) base objects packages reference)
                                (proof-view (proof-world-reg second world) base objects packages reference))
                         (p6-deferred-conjunction-in-reference-heap count top base objects packages
                                                                     (proof-world-machine world) reference)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-span-p proof-load-word p6-world-load)
                           (p6-deferred-conjunction-in-reference-heap))
           :expand ((p6-deferred-conjunction-in-reference-heap (+ 1 count) (+ 16 top) base objects packages
                                                               (proof-world-machine (p6-store-register-pair first second top world))
                                                               reference))
           :use ((:instance p6-load-stored-register-pair (address top))
                 (:instance p6-storing-pair-preserves-earlier-conjunction (address top))))))

(defconst *p6-equal-empty-stack-sites* (p6-sites "rt:equal-next" 3))

(defthm p6-equal-empty-stack-branches-to-yes
  (let* ((sites *p6-equal-empty-stack-sites*) (target (+ base (p6-runtime-offset "rt:equal-yes")))
         (after (p6-path-end sites world)) (cuts (list (proof-world-reg 30 world))))
    (implies (and (p6-path-entry-p sites base world)
                  (equal (proof-world-reg 25 world) (p6-world-load 8 (p6-sp world) world))
                  (equal (mod (p6-sp world) 16) 0)
                  (proof-covered-p (p6-sp world) 8 :read (proof-world-regions world))
                  (unsigned-byte-p 64 target) (not (equal target (proof-world-reg 30 world))))
             (and (proof-segment-p (len sites) cuts world :limit after)
                  (equal (proof-world-pc after) target)
                  (proof-register-frame-p 30 '(7) world after)
                  (equal (p6-sp after) (p6-sp world))
                  (p6-same-mapped-memory-p world after) (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-path-entry-p p6-path-end proof-segment-p p6-same-mapped-memory-p)
                           (p6-sites-placed-p p6-run-step))
           :use ((:instance p6-read-only-path-runs (sites *p6-equal-empty-stack-sites*)
                            (cuts (list (proof-world-reg 30 world))))))))
