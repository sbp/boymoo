(in-package "BOYMOO-PROOFS")

(include-book "comparison")
(include-book "publication")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-load boymoo-model::a64-store
                     boymoo-model::a64-pc boymoo-model::a64-nzcv
                     boymoo-model::a64-sp boymoo-model::a64-set-pc
                     boymoo-model::a64-set-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory proof-execute proof-instruction-effect
                     proof-reg proof-load-word proof-world-machine proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-view proof-value-p proof-number-checked-block-p
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

(defun proof-number-cut-free-prefix-p (count cuts world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (not (proof-world-stop world))
         (not (member-equal (proof-world-pc world) cuts))
         (proof-number-cut-free-prefix-p (1- count) cuts (proof-step world)))))

(defthm proof-number-run-after-cut-free-prefix
  (implies (and (natp prefix) (natp suffix)
                (proof-number-cut-free-prefix-p prefix cuts world))
           (equal (proof-run (+ prefix suffix) cuts world)
                  (proof-run suffix cuts (proof-advance prefix world))))
  :hints (("Goal"
           :induct (proof-number-cut-free-prefix-p prefix cuts world)
           :in-theory (disable proof-run))
          ("Subgoal *1/2"
           :expand ((proof-run (+ prefix suffix) cuts world)))))

(local
 (defthm cut-membership-in-append
   (iff (member-equal address (append first-cuts last-cuts))
        (or (member-equal address first-cuts) (member-equal address last-cuts)))
   :hints (("Goal" :induct (append first-cuts last-cuts)))))

(local
 (defthm cut-free-for-appended-cuts
   (equal (proof-number-cut-free-prefix-p prefix (append first-cuts last-cuts) world)
          (and (proof-number-cut-free-prefix-p prefix first-cuts world)
               (proof-number-cut-free-prefix-p prefix last-cuts world)))
   :hints (("Goal"
            :induct (proof-number-cut-free-prefix-p prefix first-cuts world)))))

(local
 (defthm run-zero-stays-in-world
   (equal (mv-nth 1 (proof-run 0 cuts world)) world)))

(defthm proof-number-compose-segments
  (implies (and (natp prefix) (natp suffix)
                (proof-number-cut-free-prefix-p prefix (append first-cuts last-cuts) before)
                (proof-segment-p prefix first-cuts before :cut middle)
                (proof-segment-p suffix last-cuts middle reason after))
           (proof-segment-p (+ prefix suffix) last-cuts before reason after))
  :hints (("Goal"
           :use ((:instance proof-number-run-after-cut-free-prefix
                            (world before) (cuts first-cuts) (suffix 0))
                 (:instance proof-number-run-after-cut-free-prefix
                            (world before) (cuts last-cuts)))
           :in-theory (disable proof-run proof-advance
                               proof-number-run-after-cut-free-prefix)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-exact-prefix-p (count cuts before after)
  (and (natp count)
       (proof-number-cut-free-prefix-p count cuts before)
       (equal (proof-advance count before) after)))

(defthm proof-number-checked-block-exact-prefix
  (implies (proof-number-checked-block-p instructions cuts world)
           (proof-number-exact-prefix-p (len instructions) cuts world
                                       (proof-number-execute-block instructions world)))
  :hints (("Goal" :induct (proof-number-checked-block-p instructions cuts world)
           :in-theory (e/d (proof-number-checked-block-p proof-number-exact-prefix-p)
                           (proof-world-pc proof-instruction-access-p)))
          ("Subgoal *1/2" :use ((:instance proof-step-from-instruction
                                           (instruction (car instructions))))))
  :rule-classes nil)

(defthm proof-number-segment-exact-prefix
  (implies (and (natp count)
                (proof-number-cut-free-prefix-p count (append local-cuts cuts) before)
                (proof-segment-p count local-cuts before reason after))
           (proof-number-exact-prefix-p count cuts before after))
  :hints (("Goal"
           :use ((:instance proof-number-run-after-cut-free-prefix
                            (prefix count) (suffix 0) (cuts local-cuts) (world before)))
           :in-theory (e/d (proof-number-exact-prefix-p)
                           (proof-run proof-advance proof-number-run-after-cut-free-prefix))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm cut-free-prefix-of-sum
   (implies (and (natp prefix) (natp suffix))
            (equal (proof-number-cut-free-prefix-p (+ prefix suffix) cuts world)
                   (and (proof-number-cut-free-prefix-p prefix cuts world)
                        (proof-number-cut-free-prefix-p suffix cuts
                                                        (proof-advance prefix world)))))
   :hints (("Goal" :induct (proof-advance prefix world))
           ("Subgoal *1/2" :expand ((proof-number-cut-free-prefix-p (+ prefix suffix)
                                                                     cuts world))))))

(defthm proof-number-exact-prefix-append
  (implies (and (proof-number-exact-prefix-p prefix cuts before middle)
                (proof-number-exact-prefix-p suffix cuts middle after))
           (proof-number-exact-prefix-p (+ prefix suffix) cuts before after))
  :hints (("Goal"
           :use ((:instance proof-advance-append (world before)))
           :in-theory (e/d (proof-number-exact-prefix-p)
                           (proof-advance-append proof-advance proof-number-cut-free-prefix-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-exact-prefix-to-cut
  (implies (and (proof-number-exact-prefix-p count cuts before after)
                (not (proof-world-stop after))
                (member-equal (proof-world-pc after) cuts))
           (proof-segment-p count cuts before :cut after))
  :hints (("Goal"
           :use ((:instance proof-number-run-after-cut-free-prefix
                            (prefix count) (suffix 0) (world before)))
           :in-theory (e/d (proof-number-exact-prefix-p)
                           (proof-advance proof-number-run-after-cut-free-prefix))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-segment-after-exact-prefix
  (implies (and (proof-number-exact-prefix-p prefix cuts before middle)
                (natp suffix)
                (proof-segment-p suffix cuts middle reason after))
           (proof-segment-p (+ prefix suffix) cuts before reason after))
  :hints (("Goal"
           :use ((:instance proof-number-run-after-cut-free-prefix (world before)))
           :in-theory (e/d (proof-number-exact-prefix-p)
                           (proof-run proof-advance proof-number-run-after-cut-free-prefix))
           :do-not-induct t))
  :rule-classes nil)

(defconst *proof-number-leaf-returns*
  '(("rt:zero" (:move-wide 2 64 0 1 0) (:branch-reg 30 nil))
    ("rt:true" (:move-wide 2 64 0 58 0) (:branch-reg 30 nil))
    ("rt:nil" (:move-wide 2 64 0 34 0) (:branch-reg 30 nil))
    ("rt:num-return-second" (:logical-reg 1 64 0 31 1 0 0 nil) (:branch-reg 30 nil))
    ("rt:num-type-return" (:branch-reg 30 nil))))

(defun proof-number-leaf-decoding-p (leaves)
  (if (endp leaves)
      t
    (let* ((name (caar leaves))
           (code (cdar leaves))
           (tail (cdr (proof-number-code-at-label name (boymoo-compiler::runtime-primitive-code)))))
      (and (equal (proof-number-decode-items (take (len code) tail) 0 nil) code)
           (proof-number-leaf-decoding-p (cdr leaves))))))

(defthm proof-number-leaf-return-decoding
  (proof-number-leaf-decoding-p *proof-number-leaf-returns*)
  :rule-classes nil)

(defund proof-number-leaf-result-word (name world)
  (cond ((equal name "rt:zero") 1)
        ((equal name "rt:true") *proof-t*)
        ((equal name "rt:nil") *proof-nil*)
        ((equal name "rt:num-return-second") (proof-world-reg 1 world))
        (t (proof-world-reg 0 world))))

(defthm proof-number-leaf-returns-word
  (let* ((machine (proof-world-machine world))
         (row (assoc-equal name *proof-number-leaf-returns*))
         (code (cdr row))
         (link (proof-world-reg 30 world))
         (after (proof-number-execute-block code world)))
    (implies (and row
                  (proof-number-checked-block-p code (list link) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))
             (and (proof-segment-p (len code) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 0 after) (proof-number-leaf-result-word name world))
                  (implies (not (equal register 0))
                           (equal (proof-world-reg register after) (proof-world-reg register world)))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions (cdr (assoc-equal name *proof-number-leaf-returns*)))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (e/d (proof-number-leaf-result-word) (proof-run proof-advance))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm zero-product
   (implies (rationalp value)
            (and (equal (* 0 value) 0) (equal (* value 0) 0)))
   :hints (("Goal"
            :use ((:instance acl2::distributivity (acl2::x value) (acl2::y 0) (acl2::z 0)))
            :in-theory (disable acl2::distributivity)))))

(defthm proof-number-q-normalize-trivial-return
  (let* ((machine (proof-world-machine world))
         (link (proof-world-reg 30 world))
         (target (if (equal a 0) zero unchanged))
         (name (if (equal a 0) "rt:zero" "rt:num-type-return"))
         (code (cdr (assoc-equal name *proof-number-leaf-returns*)))
         (count (if (equal a 0) 2 4))
         (middle (proof-number-q-normalize-after zero unchanged reduce world))
         (after (proof-number-execute-block code middle)))
    (implies (and (integerp a) (posp b) (or (equal a 0) (equal b 1))
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-q-normalize-pre-p zero unchanged reduce world)
                  (proof-number-cut-free-prefix-p count (list target link) world)
                  (proof-number-checked-block-p code (list link) middle)
                  (not (eq (car (proof-world-machine middle)) :svc))
                  (unsigned-byte-p 64 (+ 4 target)))
             (and (proof-segment-p (+ count (len code)) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 (/ a b) after objects packages)
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-q-normalize-dispatch-by-value (register 0))
                 (:instance proof-number-q-normalize-dispatch-by-value (register 30))
                 (:instance proof-number-leaf-returns-word (register 0)
                            (name (if (equal a 0) "rt:zero" "rt:num-type-return"))
                            (world (proof-number-q-normalize-after zero unchanged reduce world)))
                 (:instance proof-number-compose-segments
                            (before world)
                            (prefix (if (equal a 0) 2 4))
                            (suffix (if (equal a 0) 2 1))
                            (first-cuts (list (if (equal a 0) zero unchanged)))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (reason :cut)
                            (middle (proof-number-q-normalize-after zero unchanged reduce world))
                            (after (proof-number-execute-block
                                    (cdr (assoc-equal
                                          (if (equal a 0) "rt:zero" "rt:num-type-return")
                                          *proof-number-leaf-returns*))
                                    (proof-number-q-normalize-after zero unchanged reduce world))))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value (/ a b)) (before world)
                            (word (if (equal a 0) 1 (proof-world-reg 0 world)))
                            (after (proof-number-execute-block
                                    (cdr (assoc-equal
                                          (if (equal a 0) "rt:zero" "rt:num-type-return")
                                          *proof-number-leaf-returns*))
                                    (proof-number-q-normalize-after zero unchanged reduce world))))
                 (:instance proof-number-immediate-word-view (value 0)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-number-leaf-result-word)
                           (proof-segment-p proof-number-execute-block proof-world-reg
                            proof-heap-base proof-number-cut-free-prefix-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-collapse-return
  (let* ((link (proof-world-reg 30 world))
         (middle (proof-number-box-select-after kind unchanged fields world))
         (code '((:branch-reg 30 nil)))
         (after (proof-number-execute-block code middle))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (integerp a) (equal b 1))
                    (and (equal kind 5) (rationalp a) (equal b 0)))
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-box-select-pre-p kind unchanged fields world)
                  (proof-number-cut-free-prefix-p 2 (list unchanged link) world)
                  (proof-number-checked-block-p code (list link) middle)
                  (not (eq (car (proof-world-machine middle)) :svc))
                  (unsigned-byte-p 64 (+ 4 unchanged)))
             (and (proof-segment-p 3 (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use (proof-number-box-select-by-value proof-number-box-select
                 (:instance proof-number-leaf-returns-word (register 0)
                            (name "rt:num-type-return")
                            (world (proof-number-box-select-after kind unchanged fields world)))
                 (:instance proof-number-compose-segments
                            (before world) (prefix 2) (suffix 1)
                            (first-cuts (list unchanged)) (last-cuts (list (proof-world-reg 30 world)))
                            (reason :cut)
                            (middle (proof-number-box-select-after kind unchanged fields world))
                            (after (proof-number-execute-block
                                    '((:branch-reg 30 nil))
                                    (proof-number-box-select-after kind unchanged fields world))))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value a) (before world) (word (proof-world-reg 0 world))
                            (after (proof-number-execute-block
                                    '((:branch-reg 30 nil))
                                    (proof-number-box-select-after kind unchanged fields world)))))
           :in-theory (e/d (proof-number-box-select-count proof-number-box-select-target
                            proof-number-leaf-result-word)
                           (proof-segment-p proof-number-execute-block proof-world-reg
                            proof-heap-base proof-number-cut-free-prefix-p))
           :do-not-induct t))
  :rule-classes nil)
