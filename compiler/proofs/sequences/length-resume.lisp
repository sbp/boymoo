(in-package "BOYMOO-PROOFS")

(include-book "view-calls")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-length-count-path (datum)
  (if (stringp datum)
      *sequence-length-view-to-tag*
    (append *sequence-length-view-to-list* (sequence-list-length-path datum))))

(local
 (defthm sequence-length-count-is-ready
   (let* ((machine (proof-world-machine before))
          (payload (proof-world-reg 1 before))
          (count (len (sequence-elements datum)))
          (tag (+ image-base *sequence-length-tag-offset*))
          (called (sequence-execute *sequence-length-view-to-list* before))
          (ready (sequence-execute (sequence-length-count-path datum) before)))
     (implies
      (and (not (proof-world-stop before))
           (consp (boymoo-model::a64-registers machine))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-length-offset* 8))
           (unsigned-byte-p 64 tag)
           (unsigned-byte-p 32 count)
           (if (stringp datum)
               (and (not (equal payload 0)) (equal (proof-world-reg 2 before) count))
             (and (equal payload 0)
                  (sequence-cons-spine-p datum (proof-world-reg 0 before)
                                         (proof-heap-base before) machine)
                  (sequence-instruction-path (sequence-list-length-path datum) (list tag) called))))
      (and (equal (proof-world-pc ready) tag)
           (not (proof-world-stop ready))
           (equal (proof-world-reg 2 ready) count)
           (consp (boymoo-model::a64-registers (proof-world-machine ready)))
           (equal (cdr ready) (cdr before))
           (proof-register-frame-p 28 '(0 1 2 3) before ready)
           (equal (boymoo-model::a64-sp (proof-world-machine ready))
                  (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine ready))
                  (boymoo-model::a64-memory machine)))))
   :hints
   (("Goal"
     :in-theory (disable proof-register-frame-p proof-segment-p proof-world-machine
                         proof-world-pc proof-world-reg proof-heap-base sequence-cons-spine-p
                         sequence-list-length-path acl2::binary-append)
     :use
     (sequence-length-after-view-effects
      (:instance sequence-cons-spine-on-equal-memory
                 (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                 (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute *sequence-length-view-to-list* before))))
      (:instance sequence-list-length-contract
                 (before (sequence-execute *sequence-length-view-to-list* before)))
      (:instance sequence-register-frame-on-prefix
                 (limit 30) (prefix 28) (clobbers '(2 3))
                 (before (sequence-execute *sequence-length-view-to-list* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-length-view-to-list* before))))
      (:instance sequence-register-frame-with-more-clobbers
                 (limit 28) (old '(2 3)) (new '(0 1 2 3))
                 (before (sequence-execute *sequence-length-view-to-list* before))
                 (after (sequence-execute (sequence-list-length-path datum)
                                          (sequence-execute *sequence-length-view-to-list* before))))
      (:instance sequence-register-frame-transitive
                 (limit 28) (clobbers '(0 1 2 3))
                 (middle (sequence-execute *sequence-length-view-to-list* before))
                 (after (sequence-execute (sequence-length-count-path datum) before))))))
   :rule-classes nil))

(defun sequence-length-from-view-path (datum)
  (append (sequence-length-count-path datum) *sequence-length-return*))

(defthm sequence-length-from-view-to-source
  (let* ((machine (proof-world-machine before))
         (payload (proof-world-reg 1 before))
         (stack (boymoo-model::a64-sp machine))
         (link (proof-load-word (+ stack 8) machine))
         (tag (+ image-base *sequence-length-tag-offset*))
         (count (len (sequence-elements datum)))
         (called (sequence-execute *sequence-length-view-to-list* before))
         (path (sequence-length-from-view-path datum))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-length-offset* 8))
          (unsigned-byte-p 64 tag)
          (unsigned-byte-p 64 (+ stack 16))
          (unsigned-byte-p 32 count)
          (if (stringp datum)
              (and (not (equal payload 0)) (equal (proof-world-reg 2 before) count))
            (and (equal payload 0)
                 (sequence-cons-spine-p datum (proof-world-reg 0 before)
                                        (proof-heap-base before) machine)
                 (sequence-instruction-path (sequence-list-length-path datum) (list tag) called)))
          (sequence-instruction-path path (list link) before))
     (and (proof-segment-p (len path) (list link) before :cut after)
          (equal (proof-world-pc after) link)
          (equal (proof-world-reg 29 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) link)
          (not (proof-world-stop after))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (proof-register-frame-p 28 '(0 1 2 3) before after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                             objects packages (proof-world-machine after))
                 (boymoo-model::core-prelude 'length (list datum))))))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-segment-p proof-world-machine proof-world-reg
                        proof-world-pc proof-heap-base sequence-core-length proof-register-frame-p
                        sequence-length-count-path sequence-cons-spine-p sequence-elements
                        boymoo-model::core-prelude acl2::binary-append)
    :use
    (sequence-length-count-is-ready
     (:instance sequence-register-frame-transitive
                (limit 28) (clobbers '(0 1 2 3))
                (middle (sequence-execute (sequence-length-count-path datum) before))
                (after (sequence-execute (sequence-length-from-view-path datum) before)))
     (:instance sequence-length-return-effects
                (before (sequence-execute (sequence-length-count-path datum) before)))
     (:instance sequence-length-return-value
                (before (sequence-execute (sequence-length-count-path datum) before)))
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-length-from-view-path datum))
                (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                             (proof-world-machine before))))
                (after (sequence-execute (sequence-length-from-view-path datum) before))))))
  :rule-classes nil)
