(in-package "BOYMOO-PROOFS")

(include-book "conditional-flow")
(include-book "equal-paths")
(include-book "runtime-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-heap-p proof-heap-base proof-reg-value-p proof-machine-value-p proof-value-p
                    proof-segment-p proof-runtime-entry proof-runtime-value proof-runtime-return-p proof-routine-spelling
                    proof-label-address proof-instruction-effect generated-link-to generated-path-after generated-path-p
                    generated-pair-access-path generated-unequal-equality-path generated-heap-world-equiv expt))

(defthm generated-inline-list-and-equality-source-values
  (and (equal (proof-runtime-value 'car (list x) program) (boymoo-model::core-value (car x)))
       (equal (proof-runtime-value 'cdr (list x) program) (boymoo-model::core-value (cdr x)))
       (equal (proof-runtime-value 'consp (list x) program) (boymoo-model::core-value (consp x)))
       (equal (proof-runtime-value 'equal (list x y) program) (boymoo-model::core-value (equal x y))))
  :hints (("Goal" :in-theory (enable proof-runtime-value boymoo-model::core-primitive))))

(local
 (defthm generated-boolean-word-represents-result
   (implies (and (booleanp result) (proof-heap-p before objects packages)
                 (generated-heap-world-equiv after before)
                 (equal (proof-world-reg 0 after) (if result *proof-t* *proof-nil*)))
            (proof-reg-value-p 0 result after objects packages))
   :hints (("Goal" :use (:instance generated-static-booleans-in-published-heap (world before))
                   :in-theory (enable proof-reg-value-p)))
   :rule-classes nil))

(local
 (defthm generated-consp-raw-path-controls
   (let ((after (generated-path-after *generated-consp-path* before)))
     (implies (and (< (+ (proof-world-pc before) 16) (expt 2 64))
                   (generated-ordinary-machine-p before))
              (and (equal (proof-world-pc after) (+ (proof-world-pc before) 16))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before)))))
   :hints (("Goal" :in-theory (enable generated-path-after)))
   :rule-classes nil))

(defthm generated-inline-consp-returns-source-value
  (let* ((continuation (+ (proof-world-pc before) 16))
         (after (generated-path-after *generated-consp-path* before)))
    (implies (and (< continuation (expt 2 64)) (generated-ordinary-machine-p before)
                  (proof-heap-p before objects packages) (not (proof-world-stop before))
                  (proof-reg-value-p 0 input before objects packages)
                  (member-equal continuation cuts) (generated-path-p *generated-consp-path* cuts before))
             (and (proof-segment-p 4 cuts before :cut after)
                  (generated-nontail-value-result-p (consp input) continuation before after objects objects packages))))
  :hints (("Goal"
           :use (generated-consp-raw-path-controls generated-consp-checked-path
                 (:instance generated-boolean-word-represents-result (result (consp input))
                            (after (generated-path-after *generated-consp-path* before)))
                 (:instance generated-placed-path-allows-fewer-cuts (path *generated-consp-path*) (all-cuts cuts)
                            (cuts (list (+ 16 (proof-world-pc before)))))
                 (:instance generated-placed-path-to-cut (instructions *generated-consp-path*))
                 (:instance generated-heap-equivalent-state-provides-value-result (datum (consp input))
                            (after (generated-path-after *generated-consp-path* before))))
           :in-theory (enable proof-reg-value-p proof-machine-value-p)))
  :rule-classes nil)

(local
 (defthm generated-pair-access-raw-path-controls
   (let ((after (generated-path-after (generated-pair-access-path cdr-p before) before)))
     (implies (and (< (+ (proof-world-pc before) 24) (expt 2 64))
                   (generated-ordinary-machine-p before))
              (and (equal (proof-world-pc after) (+ (proof-world-pc before) 24))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before)))))
   :hints (("Goal" :in-theory (enable generated-path-after generated-pair-access-path)))
   :rule-classes nil))

(defthm generated-inline-pair-access-returns-source-value
  (let* ((continuation (+ (proof-world-pc before) 24))
         (path (generated-pair-access-path cdr-p before)) (after (generated-path-after path before)))
    (implies (and (< continuation (expt 2 64)) (generated-ordinary-machine-p before)
                  (proof-heap-p before objects packages) (not (proof-world-stop before))
                  (proof-reg-value-p 0 input before objects packages)
                  (member-equal continuation cuts) (generated-path-p path cuts before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (generated-nontail-value-result-p (if cdr-p (cdr input) (car input)) continuation
                                                    before after objects objects packages))))
  :hints (("Goal"
           :use (generated-pair-access-raw-path-controls generated-pair-access-in-published-heap
                 (:instance generated-placed-path-allows-fewer-cuts (path (generated-pair-access-path cdr-p before))
                            (all-cuts cuts) (cuts (list (+ 24 (proof-world-pc before)))))
                 (:instance generated-placed-path-to-cut (instructions (generated-pair-access-path cdr-p before)))
                 (:instance generated-heap-equivalent-state-provides-value-result
                            (datum (if cdr-p (cdr input) (car input)))
                            (after (generated-path-after (generated-pair-access-path cdr-p before) before))))))
  :rule-classes nil)

(local
 (defthm generated-equal-same-word-raw-path-controls
   (let ((after (generated-path-after *generated-equal-identical-path* before)))
     (implies (and (< (+ (proof-world-pc before) 64) (expt 2 64))
                   (equal (proof-world-reg 0 before) (proof-world-reg 1 before))
                   (generated-ordinary-machine-p before))
              (and (equal (proof-world-pc after) (+ (proof-world-pc before) 64))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before)))))
   :hints (("Goal" :in-theory (enable generated-path-after)))
   :rule-classes nil))

(defthm generated-equal-identical-words-return-source-value
  (let* ((continuation (+ (proof-world-pc before) 64))
         (after (generated-path-after *generated-equal-identical-path* before)))
    (implies (and (< continuation (expt 2 64)) (generated-ordinary-machine-p before)
                  (proof-heap-p before objects packages) (not (proof-world-stop before))
                  (equal (proof-world-reg 0 before) (proof-world-reg 1 before))
                  (proof-reg-value-p 0 x before objects packages) (proof-reg-value-p 1 y before objects packages)
                  (member-equal continuation cuts) (generated-path-p *generated-equal-identical-path* cuts before))
             (and (proof-segment-p 4 cuts before :cut after)
                  (generated-nontail-value-result-p (equal x y) continuation before after objects objects packages))))
  :hints (("Goal"
           :use (generated-equal-same-word-raw-path-controls
                 (:instance generated-identical-word-equality-fast-path (left x) (right y))
                 (:instance generated-boolean-word-represents-result (result t)
                            (after (generated-path-after *generated-equal-identical-path* before)))
                 (:instance generated-placed-path-allows-fewer-cuts (path *generated-equal-identical-path*) (all-cuts cuts)
                            (cuts (list (+ 64 (proof-world-pc before)))))
                 (:instance generated-placed-path-to-cut (instructions *generated-equal-identical-path*))
                 (:instance generated-heap-equivalent-state-provides-value-result (datum t)
                            (after (generated-path-after *generated-equal-identical-path* before))))
           :in-theory (enable proof-reg-value-p proof-machine-value-p)))
  :rule-classes nil)

(defthm generated-equal-distinct-words-select-result-or-slow-call
  (let* ((pc (proof-world-pc before)) (left (proof-world-reg 0 before)) (right (proof-world-reg 1 before))
         (fast (generated-equality-atom-edge-p left right))
         (path (generated-unequal-equality-path left right)) (after (generated-path-after path before))
         (end (+ pc (if fast 64 44))))
    (implies (and (not (equal left right)) (< (+ pc 64) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (proof-heap-p before objects packages) (proof-reg-value-p 0 x before objects packages)
                  (proof-reg-value-p 1 y before objects packages)
                  (member-equal end cuts) (generated-path-p path cuts before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (generated-nontail-value-result-p (if fast (equal x y) x) end before after objects objects packages)
                  (proof-reg-value-p 1 y after objects packages))))
  :hints (("Goal"
           :use (generated-unequal-equality-selects-false-or-runtime generated-unequal-atomic-equality-returns-source-false
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-unequal-equality-path (proof-world-reg 0 before) (proof-world-reg 1 before)))
                            (all-cuts cuts)
                            (cuts (list (+ (proof-world-pc before)
                                           (if (generated-equality-atom-edge-p (proof-world-reg 0 before) (proof-world-reg 1 before))
                                               64 44)))))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-unequal-equality-path (proof-world-reg 0 before) (proof-world-reg 1 before))))
                 (:instance generated-heap-equivalent-state-provides-value-result
                            (datum (if (generated-equality-atom-edge-p (proof-world-reg 0 before) (proof-world-reg 1 before))
                                       (equal x y) x))
                            (after (generated-path-after
                                     (generated-unequal-equality-path (proof-world-reg 0 before) (proof-world-reg 1 before)) before))))
           :in-theory (e/d (proof-reg-value-p) (generated-equality-atom-edge-p))))
  :rule-classes nil)

(local
 (defthm generated-equal-runtime-description
   (equal (proof-runtime-entry 'equal) '("COMMON-LISP::EQUAL" 2 . "prim:COMMON-LISP::EQUAL"))
   :hints (("Goal" :in-theory (enable proof-runtime-entry proof-routine-spelling)))))

(local
 (defthm generated-equal-runtime-and-done-branch-compose
   (let* ((pc (proof-world-pc before)) (link (+ pc 4)) (continuation (+ pc 20))
          (label "prim:COMMON-LISP::EQUAL") (target (proof-label-address label base labels))
          (entered (generated-link-to target before))
          (branch '(:branch 16 nil)) (after (proof-instruction-effect branch returned)))
     (implies (and (proof-program-packages-p program packages) (proof-heap-p before objects packages)
                   (proof-reg-value-p 0 x before objects packages) (proof-reg-value-p 1 y before objects packages)
                   (unsigned-byte-p 64 target) (< continuation (expt 2 64))
                   (generated-ordinary-machine-p before) (not (proof-world-stop before))
                   (not (equal pc target)) (not (member-equal pc cuts)) (member-equal continuation cuts)
                   (generated-linked-item-p (list :bl label) (list :branch (- target pc) t) pc base labels before)
                   (proof-segment-p runtime-steps (cons link cuts) entered :cut returned)
                   (proof-runtime-return-p 'equal (list x y) program entered returned objects new-objects packages)
                   (generated-ordinary-machine-p returned) (generated-path-p (list branch) cuts returned))
              (and (proof-runtime-pre-p 'equal (list x y) program labels base entered objects packages)
                   (proof-segment-p (+ 2 (nfix runtime-steps)) cuts before :cut after)
                   (generated-nontail-value-result-p (equal x y) continuation before after objects new-objects packages))))
   :hints (("Goal"
            :use ((:instance generated-linked-runtime-call-and-return-compose (name 'equal) (args (list x y))
                             (old-objects objects) (routine-steps runtime-steps) (cuts (cons (+ 4 (proof-world-pc before)) cuts))
                             (after returned))
                  (:instance generated-if-true-arm-jump-composes (arm-start before) (arm-exit returned)
                             (arm-end (+ 4 (proof-world-pc before))) (continuation (+ 20 (proof-world-pc before)))
                             (datum (equal x y)) (arm-steps (+ 1 (nfix runtime-steps)))
                             (old-objects objects) (objects new-objects)))
            :in-theory (enable proof-register-arguments-p)))
   :rule-classes nil))

(defthm generated-equal-slow-path-returns-source-value
  (let* ((pc (proof-world-pc before)) (slow (+ pc 44)) (continuation (+ pc 64))
         (left (proof-world-reg 0 before)) (right (proof-world-reg 1 before))
         (path (generated-unequal-equality-path left right)) (ready (generated-path-after path before))
         (label "prim:COMMON-LISP::EQUAL") (target (proof-label-address label base labels))
         (entered (generated-link-to target ready)) (branch '(:branch 16 nil))
         (after (proof-instruction-effect branch returned)))
    (implies (and (not (equal left right)) (not (generated-equality-atom-edge-p left right))
                  (< continuation (expt 2 64)) (unsigned-byte-p 64 target)
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (proof-program-packages-p program packages) (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 x before objects packages) (proof-reg-value-p 1 y before objects packages)
                  (generated-path-p path (cons slow cuts) before)
                  (not (equal slow target)) (not (member-equal slow cuts)) (member-equal continuation cuts)
                  (generated-ordinary-machine-p ready) (not (proof-world-stop ready))
                  (generated-linked-item-p (list :bl label) (list :branch (- target slow) t) slow base labels ready)
                  (proof-segment-p runtime-steps (cons (+ pc 48) cuts) entered :cut returned)
                  (proof-runtime-return-p 'equal (list x y) program entered returned objects new-objects packages)
                  (generated-ordinary-machine-p returned) (generated-path-p (list branch) cuts returned))
             (and (proof-runtime-pre-p 'equal (list x y) program labels base entered objects packages)
                  (proof-segment-p (+ (len path) 2 (nfix runtime-steps)) cuts before :cut after)
                  (generated-nontail-value-result-p (equal x y) continuation before after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-equal-distinct-words-select-result-or-slow-call
                            (cuts (cons (+ 44 (proof-world-pc before)) cuts)))
                 (:instance generated-equal-runtime-and-done-branch-compose
                            (before (generated-path-after (generated-unequal-equality-path (proof-world-reg 0 before)
                                                                                          (proof-world-reg 1 before)) before)))
                 (:instance generated-nontail-segments-compose
                            (prefix-steps (len (generated-unequal-equality-path (proof-world-reg 0 before)
                                                                              (proof-world-reg 1 before))))
                            (suffix-steps (+ 2 (nfix runtime-steps))) (middle-pc (+ 44 (proof-world-pc before)))
                            (middle (generated-path-after (generated-unequal-equality-path (proof-world-reg 0 before)
                                                                                          (proof-world-reg 1 before)) before))
                            (continuation (+ 64 (proof-world-pc before))) (prefix-datum x) (datum (equal x y))
                            (old-objects objects) (middle-objects objects)
                            (after (proof-instruction-effect '(:branch 16 nil) returned))))
           :in-theory (e/d (generated-nontail-value-result-p) (generated-equality-atom-edge-p))))
  :rule-classes nil)
