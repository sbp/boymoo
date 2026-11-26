(in-package "BOYMOO-PROOFS")

(include-book "view-calls")
(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-char-index-path (world)
  (sequence-index-path (proof-world-reg 0 world) (proof-heap-base world)
                       (proof-world-machine world)))

(defun sequence-char-index-readable-p (world)
  (let* ((machine (proof-world-machine world))
         (word (proof-world-reg 0 world))
         (address (proof-pointer-address word (proof-heap-base world))))
    (implies (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type (proof-load-word address machine)) 3))
             (unsigned-byte-p 64 (+ address 8)))))

(local
 (defthm sequence-char-count-keeps-stack-words
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (and (equal (proof-load-word stack last) (proof-load-word stack first))
                 (equal (proof-load-word (+ stack 8) last) (proof-load-word (+ stack 8) first))))
   :rule-classes nil))

(local
 (defthm sequence-char-count-is-ready
   (let* ((machine (proof-world-machine before))
          (called (sequence-execute *sequence-char-count-call* before))
          (link (+ image-base *sequence-char-offset* 24))
          (ready (sequence-execute (sequence-char-index-path called) called))
          (result-machine (proof-world-machine ready)))
     (implies
      (and (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers machine))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-char-offset* 12))
           (unsigned-byte-p 64 link)
           (not (equal (proof-world-reg 1 before) 0))
           (proof-reg-value-p 5 position before objects packages)
           (sequence-char-index-readable-p called)
           (sequence-instruction-path (sequence-char-index-path called) (list link) called))
      (and (equal (proof-world-pc ready) link)
           (not (proof-world-stop ready))
           (equal (proof-world-reg 0 ready) (sequence-runtime-count position))
           (equal (proof-world-reg 1 ready) (proof-world-reg 1 before))
           (equal (proof-world-reg 2 ready) (proof-world-reg 2 before))
           (equal (proof-heap-base ready) (proof-heap-base before))
           (consp (boymoo-model::a64-registers result-machine))
           (equal (cdr ready) (cdr before))
           (proof-register-frame-p 28 '(0 1 2 3 4 5) before ready)
           (equal (boymoo-model::a64-sp result-machine) (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory result-machine) (boymoo-model::a64-memory machine)))))
   :hints
   (("Goal"
     :in-theory (disable proof-view proof-register-frame-p proof-segment-p
                         proof-world-machine proof-world-reg proof-world-pc
                         proof-pointer-address proof-load-word proof-word-tag proof-header-type
                         sequence-index-path sequence-index-value sequence-runtime-count
                         sequence-runtime-count-exact-for-bounded-size)
     :use
     (sequence-char-index-call-effects
      (:instance sequence-view-of-equal-memory
                 (word (proof-world-reg 5 before)) (base (proof-heap-base before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute *sequence-char-count-call* before))))
      (:instance sequence-index-count-contract
                 (before (sequence-execute *sequence-char-count-call* before)) (datum position))
      (:instance sequence-index-count-effects
                 (before (sequence-execute *sequence-char-count-call* before)))
      (:instance sequence-register-frame-on-prefix
                 (limit 30) (prefix 28) (clobbers '(0 3 4))
                 (before (sequence-execute *sequence-char-count-call* before))
                 (after (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
      (:instance sequence-register-frame-with-more-clobbers
                 (limit 28) (old '(0 3 4)) (new '(0 1 2 3 4 5))
                 (before (sequence-execute *sequence-char-count-call* before))
                 (after (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
      (:instance sequence-register-frame-transitive
                 (limit 28) (clobbers '(0 1 2 3 4 5))
                 (middle (sequence-execute *sequence-char-count-call* before))
                 (after (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 1)
                 (before (sequence-execute *sequence-char-count-call* before))
                 (after (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 2)
                 (before (sequence-execute *sequence-char-count-call* before))
                 (after (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
      (:instance sequence-register-in-frame
                 (limit 30) (clobbers '(0 3 4)) (register 28)
                 (before (sequence-execute *sequence-char-count-call* before))
                 (after (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before)))))))
   :rule-classes nil))

(defun sequence-char-from-view-path (datum before)
  (if (stringp datum)
      (let* ((called (sequence-execute *sequence-char-count-call* before))
             (index-path (sequence-char-index-path called))
             (ready (sequence-execute index-path called)))
        (append *sequence-char-count-call* index-path (sequence-char-result-path datum ready)))
    *sequence-char-nonstring-return*))

(defthm sequence-char-from-view-to-source
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (return-link (proof-load-word (+ stack 8) machine))
         (payload (proof-world-reg 1 before))
         (length (proof-world-reg 2 before))
         (called (sequence-execute *sequence-char-count-call* before))
         (index-path (sequence-char-index-path called))
         (path (sequence-char-from-view-path datum before))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-char-offset* 12))
          (unsigned-byte-p 64 (+ stack 16))
          (<= (len (sequence-elements datum)) *proof-space-size*)
          (if (stringp datum)
              (and (unsigned-byte-p 64 (+ image-base *sequence-char-offset* 24))
                   (not (equal payload 0))
                   (proof-span-p payload length)
                   (equal datum (proof-load-string length payload machine))
                   (proof-reg-value-p 5 position before objects packages)
                   (sequence-char-index-readable-p called)
                   (sequence-instruction-path index-path
                                              (list (+ image-base *sequence-char-offset* 24))
                                              called))
            (equal payload 0))
          (proof-value-p *proof-nil* nil (proof-heap-base before) objects packages machine)
          (sequence-instruction-path path (list return-link) before))
     (and (proof-segment-p (len path) (list return-link) before :cut after)
          (equal (proof-world-pc after) return-link)
          (equal (proof-world-reg 29 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) return-link)
          (not (proof-world-stop after))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (proof-register-frame-p 28 '(0 1 2 3 4 5) before after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                             objects packages (proof-world-machine after))
                 (boymoo-model::core-prelude 'char (list datum position))))))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-span-p proof-segment-p proof-world-machine
                        proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                        proof-register-frame-p proof-load-string proof-load-word proof-reg-value-p
                        sequence-char-index-readable-p sequence-char-return-path sequence-index-path
                        sequence-runtime-count
                        sequence-runtime-count-exact-for-bounded-size
                        boymoo-model::core-prelude boymoo-model::core-prelude-values
                        sequence-core-char acl2::binary-append)
    :cases ((stringp datum))
    :use ((:instance sequence-segment-of-instruction-path
                     (instructions (sequence-char-from-view-path datum before))
                     (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                             (proof-world-machine before))))
                     (after (sequence-execute (sequence-char-from-view-path datum before) before)))))
   ("Subgoal 2"
    :use (sequence-char-nonstring-return-effects (:instance sequence-core-char (index position))
          (:instance sequence-view-of-equal-memory
                     (word *proof-nil*) (base (proof-heap-base before))
                     (first (proof-world-machine before))
                     (last (proof-world-machine
                            (sequence-execute *sequence-char-nonstring-return* before))))))
   ("Subgoal 1"
    :use
    (sequence-char-count-is-ready
     (:instance sequence-view-of-equal-memory
                (word *proof-nil*) (base (proof-heap-base before))
                (first (proof-world-machine before))
                (last (proof-world-machine
                       (sequence-execute (sequence-char-from-view-path datum before) before))))
     (:instance sequence-register-frame-transitive
                (limit 28) (clobbers '(0 1 2 3 4 5))
                (middle (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before)))
                (after (sequence-execute (sequence-char-from-view-path datum before) before)))
     (:instance sequence-core-char (index position))
     (:instance sequence-char-return-effects
                (before (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
     (:instance sequence-char-return-value
                (before (sequence-execute
                         (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                         (sequence-execute *sequence-char-count-call* before))))
     (:instance sequence-char-count-keeps-stack-words
                (stack (boymoo-model::a64-sp (proof-world-machine before)))
                (first (proof-world-machine before))
                (last (proof-world-machine
                       (sequence-execute
                        (sequence-char-index-path
                         (sequence-execute *sequence-char-count-call* before))
                        (sequence-execute *sequence-char-count-call* before)))))
     (:instance sequence-load-string-of-equal-memory
                (count (proof-world-reg 2 before)) (address (proof-world-reg 1 before))
                (first (proof-world-machine before))
                (last (proof-world-machine
                       (sequence-execute
                       (sequence-char-index-path
                          (sequence-execute *sequence-char-count-call* before))
                        (sequence-execute *sequence-char-count-call* before))))))))
  :rule-classes nil)
