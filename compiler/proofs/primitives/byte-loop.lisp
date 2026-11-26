(in-package "BOYMOO-PROOFS")

(include-book "compare-bytes")
(include-book "state-invariants")

(logic)
(set-verify-guards-eagerness 0)

(defthm p6-run-continues-after-limit
  (implies (and (natp prefix) (natp suffix)
                (proof-segment-p prefix cuts before :limit middle))
           (equal (proof-run (+ prefix suffix) cuts before)
                  (proof-run suffix cuts middle)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-run prefix cuts before)
                  :in-theory (enable (:induction proof-run))
                  :expand ((:free (fuel) (proof-run fuel cuts before))))))

(local
 (defthm p6-register-frame-transitive
   (implies (and (proof-register-frame-p register clobbers before middle)
                 (proof-register-frame-p register clobbers middle after))
            (proof-register-frame-p register clobbers before after))
   :rule-classes nil
   :hints (("Goal" :induct (proof-register-frame-p register clobbers before middle)))))

(local
 (defthm p6-byte-frame-transitive
   (implies (and (p6-byte-frame-p before middle) (p6-byte-frame-p middle after))
            (p6-byte-frame-p before after))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable p6-byte-frame-p p6-same-mapped-memory-p)
            :use ((:instance p6-register-frame-transitive (register 30) (clobbers '(0 1 2 3 4))))))))

(local
 (defthm p6-byte-frame-keeps-link-and-memory
   (implies (p6-byte-frame-p before after)
            (and (equal (proof-world-reg 30 before) (proof-world-reg 30 after))
                 (p6-memory-equiv (proof-world-machine before) (proof-world-machine after))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable p6-byte-frame-p p6-memory-equiv p6-same-mapped-memory-p)
                   :use ((:instance p6-frame-preserves-unlisted-register
                                    (max 30) (register 30) (clobbers '(0 1 2 3 4))))))))

(local
 (defthm p6-byte-list-length
   (equal (len (proof-byte-list count address machine)) (nfix count))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (enable (:induction proof-byte-list))))))

(local
 (defun p6-paired-prefixes (left right)
   (if (atom left)
       right
     (p6-paired-prefixes (cdr left) (cdr right)))))

(local
 (defthm p6-test-concatenated-bytes
   (implies (and (true-listp left) (true-listp right) (equal (len left) (len right)))
            (equal (equal (append left tail-a) (append right tail-b))
                   (and (equal left right) (equal tail-a tail-b))))
   :hints (("Goal" :induct (p6-paired-prefixes left right)))))

(local
 (defthm p6-byte-list-is-true-list
   (true-listp (proof-byte-list count address machine))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (enable (:induction proof-byte-list))))))

(defund p6-bytes-match-p (count world)
  (equal (proof-byte-list count (proof-world-reg 0 world) (proof-world-machine world))
         (proof-byte-list count (proof-world-reg 1 world) (proof-world-machine world))))

(defthm p6-byte-chunk-match-is-span-match
  (equal (p6-byte-chunk-match-p width world) (p6-bytes-match-p width world))
  :hints (("Goal" :in-theory (enable p6-byte-chunk-match-p p6-bytes-match-p p6-world-load))))

(local
 (defthm p6-span-equality-splits-at-prefix
   (implies (and (natp prefix) (natp count) (<= prefix count)
                 (integerp left) (integerp right))
            (equal (equal (proof-byte-list count left machine) (proof-byte-list count right machine))
                   (and (equal (proof-byte-list prefix left machine) (proof-byte-list prefix right machine))
                        (equal (proof-byte-list (- count prefix) (+ prefix left) machine)
                               (proof-byte-list (- count prefix) (+ prefix right) machine)))))
   :rule-classes nil
   :hints (("Goal"
            :do-not '(fertilize)
            :in-theory (disable p6-test-concatenated-bytes)
            :use ((:instance p6-byte-list-split (suffix (- count prefix)) (address left))
                  (:instance p6-byte-list-split (suffix (- count prefix)) (address right))
                  (:instance p6-test-concatenated-bytes
                             (left (proof-byte-list prefix left machine))
                             (right (proof-byte-list prefix right machine))
                             (tail-a (proof-byte-list (- count prefix) (+ prefix left) machine))
                             (tail-b (proof-byte-list (- count prefix) (+ prefix right) machine))))))))

(defthm p6-byte-span-relates-prefix-to-suffix
  (implies (and (natp prefix) (natp count) (<= prefix count)
                (p6-byte-frame-p before after)
                (equal (proof-world-reg 0 after) (+ prefix (proof-world-reg 0 before)))
                (equal (proof-world-reg 1 after) (+ prefix (proof-world-reg 1 before))))
           (equal (p6-bytes-match-p count before)
                  (and (p6-bytes-match-p prefix before)
                       (p6-bytes-match-p (- count prefix) after))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-bytes-match-p)
           :use ((:instance p6-span-equality-splits-at-prefix
                            (left (proof-world-reg 0 before)) (right (proof-world-reg 1 before))
                            (machine (proof-world-machine before)))))))

(defthm p6-bytes-match-fails-on-mismatching-prefix
  (implies (and (natp prefix) (natp count) (<= prefix count)
                (not (p6-bytes-match-p prefix world)))
           (not (p6-bytes-match-p count world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-bytes-match-p)
           :use ((:instance p6-span-equality-splits-at-prefix
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
                            (machine (proof-world-machine world)))))))

(defun p6-byte-action (width count world)
  (cond ((< (nfix count) width) (if (equal width 8) :tail :empty))
        ((p6-byte-chunk-match-p width world) :advance)
        (t :different)))

(defund p6-byte-loop-join (width count base world continuation)
  (let* ((action (p6-byte-action width count world))
         (sites (p6-byte-block-sites width action))
         (ready (and (equal count (proof-world-reg 2 world))
                     (p6-byte-block-pre-p width action base world))))
    (if (member-eq action '(:tail :advance))
        (list (+ (len sites) (car continuation)) (cadr continuation)
              (and ready (caddr continuation)))
      (list (len sites) (p6-path-end sites world) ready))))

; The count is the number of bytes remaining. At the switch to byte
; loads it stays fixed, and the width drops from eight to one.
(defun p6-byte-loop-recipe (width count base world)
  (declare (xargs :measure (+ (* 2 (nfix count)) (if (equal width 8) 1 0))
                  :ruler-extenders :all))
  (let* ((width (if (equal width 8) 8 1))
         (action (p6-byte-action width count world))
         (next (if (member-eq action '(:tail :advance))
                   (p6-byte-loop-recipe (if (eq action :tail) 1 width)
                                        (if (eq action :tail) count (- count width)) base
                                        (p6-path-end (p6-byte-block-sites width action) world))
                 nil)))
    (p6-byte-loop-join width count base world next)))

(defthm p6-chosen-byte-block-post
  (let ((action (p6-byte-action width (proof-world-reg 2 world) world)))
    (implies (and (member-equal width '(1 8)) (p6-byte-block-pre-p width action base world))
             (p6-byte-block-post-p width action base world)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable p6-byte-chunk-match-is-span-match)
                  :use (p6-byte-comparison-empty-span p6-byte-comparison-switches-to-tail
                        p6-byte-comparison-byte-mismatch p6-byte-comparison-word-mismatch
                        p6-byte-comparison-advances-one-byte p6-byte-comparison-advances-eight-bytes))))

(defthm p6-byte-block-agrees-with-remaining-span
  (let* ((action (p6-byte-action width count world))
         (sites (p6-byte-block-sites width action))
         (after (p6-path-end sites world))
         (continue (member-eq action '(:tail :advance))))
    (implies (and (member-equal width '(1 8)) (equal count (proof-world-reg 2 world))
                  (p6-byte-block-pre-p width action base world))
             (and (p6-byte-frame-p world after)
                  (not (proof-world-stop after))
                  (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world
                                   (if continue :limit :cut) after)
                  (if continue
                      (equal (p6-bytes-match-p count world)
                             (p6-bytes-match-p (if (eq action :tail) count (- count width)) after))
                    (equal (proof-world-reg 0 after) (if (p6-bytes-match-p count world) 1 0))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-byte-block-post-p p6-bytes-match-p)
                           (p6-path-end proof-segment-p p6-byte-block-sites))
           :use (p6-chosen-byte-block-post
                 (:instance p6-byte-comparison-block-runs
                            (before world) (action (p6-byte-action width count world)))
                 (:instance p6-byte-span-relates-prefix-to-suffix
                            (prefix width) (before world)
                            (after (p6-path-end (p6-byte-block-sites width :advance) world)))
                 (:instance p6-bytes-match-fails-on-mismatching-prefix (prefix width))))))

(defthm p6-byte-loop-step-count-natural
  (natp (car (p6-byte-loop-recipe width count base world)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (p6-byte-loop-recipe width count base world)
                  :in-theory (e/d (p6-byte-loop-join)
                                  (p6-path-end p6-byte-block-sites p6-byte-action)))))

(local
 (defthm p6-compose-byte-segments
   (implies (and (natp prefix) (natp suffix)
                 (p6-byte-frame-p world middle) (p6-byte-frame-p middle finish)
                 (proof-segment-p prefix (list (proof-world-reg 30 world)) world :limit middle)
                 (proof-segment-p suffix (list (proof-world-reg 30 middle)) middle :cut finish))
            (and (p6-byte-frame-p world finish)
                 (proof-segment-p (+ prefix suffix) (list (proof-world-reg 30 world)) world :cut finish)))
   :rule-classes nil
   :hints (("Goal" :use ( (:instance p6-run-continues-after-limit
                                     (cuts (list (proof-world-reg 30 world))) (before world))
                           (:instance p6-byte-frame-transitive (before world) (after finish)))))))

(defund p6-byte-loop-summary-p (recipe count world)
  (let ((steps (car recipe)) (finish (cadr recipe)) (ready (caddr recipe)))
    (implies ready
             (and (natp steps)
                  (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut finish)
                  (p6-byte-frame-p world finish)
                  (not (proof-world-stop finish))
                  (equal (proof-world-reg 0 finish) (if (p6-bytes-match-p count world) 1 0))))))

(local
 (defthm p6-byte-loop-summary-after-join
   (let* ((action (p6-byte-action width count world))
          (sites (p6-byte-block-sites width action))
          (middle (p6-path-end sites world)))
     (implies (and (member-equal width '(1 8))
                   (implies (member-eq action '(:tail :advance))
                            (p6-byte-loop-summary-p continuation
                                                    (if (eq action :tail) count (- count width)) middle)))
              (p6-byte-loop-summary-p (p6-byte-loop-join width count base world continuation) count world)))
   :hints (("Goal"
            :in-theory (e/d (p6-byte-loop-summary-p p6-byte-loop-join)
                            (p6-path-end proof-segment-p p6-byte-block-sites p6-byte-action))
            :use (p6-byte-block-agrees-with-remaining-span
                  (:instance p6-compose-byte-segments
                             (prefix (len (p6-byte-block-sites width (p6-byte-action width count world))))
                             (suffix (car continuation)) (finish (cadr continuation))
                             (middle (p6-path-end (p6-byte-block-sites width (p6-byte-action width count world))
                                                  world))))))))

(defthm p6-byte-loop-recipe-correct
  (p6-byte-loop-summary-p (p6-byte-loop-recipe width count base world) count world)
  :rule-classes nil
  :hints (("Goal"
           :induct (p6-byte-loop-recipe width count base world)
           :in-theory (disable (:definition p6-byte-loop-recipe)
                               p6-path-end proof-segment-p p6-byte-block-sites p6-byte-action)
           :expand ((:free (mode) (p6-byte-loop-recipe mode count base world))))))
