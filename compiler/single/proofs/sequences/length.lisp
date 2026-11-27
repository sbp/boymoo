(in-package "BOYMOO-PROOFS")

(include-book "helpers")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-execute-append
  (equal (sequence-execute (append first second) world)
         (sequence-execute second (sequence-execute first world)))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :induct (sequence-execute first world))))

(defthm sequence-register-frame-reflexive
  (proof-register-frame-p limit clobbers world world)
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers world world))))

(defthm sequence-register-frame-transitive
  (implies (and (proof-register-frame-p limit clobbers before middle)
                (proof-register-frame-p limit clobbers middle after))
           (proof-register-frame-p limit clobbers before after))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before middle)))
  :rule-classes nil)

(defthm sequence-unclobbered-frame-allows-clobbers
  (implies (proof-register-frame-p limit nil before after)
           (proof-register-frame-p limit clobbers before after))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)))
  :rule-classes nil)

(defthm sequence-register-frame-on-prefix
  (implies (and (natp limit) (natp prefix) (<= prefix limit)
                (proof-register-frame-p limit clobbers before after))
           (proof-register-frame-p prefix clobbers before after))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)))
  :rule-classes nil)

(defthm sequence-register-frame-with-more-clobbers
  (implies (and (subsetp-equal old new)
                (proof-register-frame-p limit old before after))
           (proof-register-frame-p limit new before after))
  :hints (("Goal" :induct (proof-register-frame-p limit old before after)))
  :rule-classes nil)

(defthm sequence-register-in-frame
  (implies (and (natp limit) (natp register) (<= register limit)
                (not (member-equal register clobbers))
                (proof-register-frame-p limit clobbers before after))
           (equal (proof-world-reg register after) (proof-world-reg register before)))
  :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)))
  :rule-classes nil)

; A cons spine is the finite succession of cdr fields ending in an atom.
; Each cell address in this predicate admits ordinary addition of its offset.
(defun sequence-cons-spine-p (datum word base machine)
  (if (atom datum)
      (not (equal (proof-word-tag word) 0))
    (and (equal (proof-word-tag word) 0)
         (proof-span-p (+ base word) 16)
         (sequence-cons-spine-p (cdr datum)
                                (proof-load-word (+ base word 8) machine)
                                base machine))))

(defun sequence-list-length-loop-path (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      *sequence-list-length-return*
    (append *sequence-list-length-cell*
            (sequence-list-length-loop-path (1- count)))))

(defthm sequence-list-length-loop-step-count
  (equal (len (sequence-list-length-loop-path count)) (+ 3 (* 6 (nfix count)))))

(local
 (defthm sequence-list-length-loop-path-when-positive
   (implies (posp count)
            (equal (sequence-list-length-loop-path count)
                   (append *sequence-list-length-cell*
                           (sequence-list-length-loop-path (1- count)))))
   :hints (("Goal" :expand ((sequence-list-length-loop-path count))))))

(local
 (defun sequence-length-loop-induction (datum world)
   (if (atom datum)
       world
     (sequence-length-loop-induction
      (cdr datum) (sequence-execute *sequence-list-length-cell* world)))))

(local
 (defthm sequence-world-register-is-natural
   (natp (proof-world-reg register world))
   :rule-classes :type-prescription))

(defthm sequence-cons-spine-on-equal-memory
  (implies (and (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
                (sequence-cons-spine-p datum word base first))
           (sequence-cons-spine-p datum word base last))
  :hints (("Goal" :induct (sequence-cons-spine-p datum word base first)))
  :rule-classes nil)

(defthm sequence-list-length-loop-effects
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (count (proof-world-reg 2 before))
         (steps (sequence-list-length-loop-path (len datum)))
         (after (sequence-execute steps before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (sequence-cons-spine-p datum (proof-world-reg 3 before) base machine)
          (unsigned-byte-p 64 (+ 24 (proof-world-pc before)))
          (unsigned-byte-p 64 (+ count (len datum))))
     (and (equal (proof-world-reg 2 after) (+ count (len datum)))
          (equal (proof-world-pc after) (proof-world-reg 30 before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 '(2 3) before after))))
  :hints
  (("Goal" :induct (sequence-length-loop-induction datum before)
           :in-theory (disable proof-register-frame-p sequence-execute
                               proof-world-reg proof-world-machine
                               acl2::binary-append
                               (:definition sequence-list-length-loop-path)))
   ("Subgoal *1/1"
    :use (sequence-list-length-return-effects
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers nil) (register 2)
                     (after (sequence-execute *sequence-list-length-return* before)))
          (:instance sequence-unclobbered-frame-allows-clobbers
                     (limit 30) (clobbers '(2 3))
                     (after (sequence-execute *sequence-list-length-return* before))))
    :expand ((:free (word base machine) (sequence-cons-spine-p datum word base machine))))
   ("Subgoal *1/2"
    :use (sequence-list-length-cell-effects
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers '(2 3)) (register 28)
                     (after (sequence-execute *sequence-list-length-cell* before)))
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers '(2 3)) (register 30)
                     (after (sequence-execute *sequence-list-length-cell* before)))
          (:instance sequence-register-frame-transitive
                     (limit 30) (clobbers '(2 3))
                     (middle (sequence-execute *sequence-list-length-cell* before))
                     (after (sequence-execute (sequence-list-length-loop-path (len datum))
                                              before)))
          (:instance sequence-cons-spine-on-equal-memory
                     (datum (cdr datum)) (base (proof-heap-base before))
                     (word (proof-load-word (+ (proof-heap-base before)
                                              (proof-world-reg 3 before) 8)
                                           (proof-world-machine before)))
                     (first (proof-world-machine before))
                     (last (proof-world-machine
                            (sequence-execute *sequence-list-length-cell* before)))))
    :expand ((:free (word base machine) (sequence-cons-spine-p datum word base machine)))))
  :rule-classes nil)

(defun sequence-list-length-path (datum)
  (append *sequence-list-length-entry*
          (sequence-list-length-loop-path (len datum))))

(defthm sequence-list-length-step-count
  (equal (len (sequence-list-length-path datum)) (+ 5 (* 6 (len datum)))))

(defthm sequence-list-length-contract
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (path (sequence-list-length-path datum))
         (cuts (list (proof-world-reg 30 before)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (sequence-cons-spine-p datum word base machine)
          (unsigned-byte-p 64 (+ 32 (proof-world-pc before)))
          (unsigned-byte-p 64 (len datum))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-frame-return-p '(2 3) t before after)
          (equal (proof-world-reg 2 after) (len datum))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (equal (proof-world-regions after) (proof-world-regions before)))))
  :hints
  (("Goal"
    :in-theory (disable proof-register-frame-p proof-segment-p proof-world-machine
                        proof-world-reg sequence-cons-spine-p acl2::binary-append
                        sequence-list-length-loop-path)
    :use (sequence-list-length-entry-effects
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers '(2 3)) (register 28)
                     (after (sequence-execute *sequence-list-length-entry* before)))
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers '(2 3)) (register 30)
                     (after (sequence-execute *sequence-list-length-entry* before)))
          (:instance sequence-cons-spine-on-equal-memory
                     (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                     (first (proof-world-machine before))
                     (last (proof-world-machine
                            (sequence-execute *sequence-list-length-entry* before))))
          (:instance sequence-list-length-loop-effects
                     (before (sequence-execute *sequence-list-length-entry* before)))
          (:instance sequence-register-frame-transitive
                     (limit 30) (clobbers '(2 3))
                     (middle (sequence-execute *sequence-list-length-entry* before))
                     (after (sequence-execute (sequence-list-length-path datum) before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-list-length-path datum))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute (sequence-list-length-path datum) before))))))
  :rule-classes nil)

(defun sequence-cons-offsets-ordinary-p (objects base)
  (if (atom objects)
      t
    (and (implies (eq (proof-object-kind (car objects)) :cons)
                  (<= base (proof-object-address (car objects))))
         (sequence-cons-offsets-ordinary-p (cdr objects) base))))

(local
 (defthm sequence-cons-record-selected-above-base
   (let ((object (assoc-equal address objects)))
     (implies (and (sequence-cons-offsets-ordinary-p objects base)
                   (eq (proof-object-kind object) :cons))
              (<= base address)))
   :hints (("Goal" :induct (assoc-equal address objects)))
   :rule-classes nil))

(local
 (defthm sequence-cons-address-without-wrap
   (implies (and (unsigned-byte-p 64 base) (unsigned-byte-p 64 word)
                 (equal (proof-word-tag word) 0)
                 (<= base (proof-pointer-address word base)))
            (equal (proof-pointer-address word base) (+ base word)))
   :hints (("Goal" :cases ((< (+ base word) (expt 2 64))))
           ("Subgoal 2"
            :in-theory (disable sequence-truncate-word-plus-modulus)
            :use ((:instance sequence-truncate-word-plus-modulus
                             (value (+ (- (expt 2 64)) base word))))))
   :rule-classes nil))

(defthm sequence-word-cons-tag
  (implies (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view datum))
           (equal (consp datum) (equal (proof-word-tag word) 0)))
  :hints (("Goal"
           :in-theory (disable proof-view-step proof-load-string proof-symbol-value
                               proof-rational-value proof-complex-value
                               sequence-even-tags-mark-even-words)
           :expand ((proof-view-step :word word 0 depth base objects packages machine))
           :use (sequence-cons-view-of-represented-value sequence-even-tags-mark-even-words)))
  :rule-classes nil)

(local
 (defun sequence-spine-view-induction (datum word depth base objects machine)
   (if (atom datum)
       depth
     (sequence-spine-view-induction
      (cdr datum) (proof-load-word (+ base word 8) machine)
      (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))
      base objects machine))))

(defthm sequence-cons-spine-from-value-view
  (implies (and (equal (proof-view-step :word word 0 depth base objects packages machine)
                       (proof-value-view datum))
                (unsigned-byte-p 64 base)
                (sequence-cons-offsets-ordinary-p objects base))
           (sequence-cons-spine-p datum word base machine))
  :hints
  (("Goal" :induct (sequence-spine-view-induction datum word depth base objects machine)
           :in-theory (disable proof-view-step proof-pointer-address proof-word-tag
                               proof-object-kind proof-object-rank proof-load-word
                               sequence-cons-spine-p))
   ("Subgoal *1/1"
    :use sequence-word-cons-tag
    :expand ((sequence-cons-spine-p datum word base machine)))
   ("Subgoal *1/2"
    :use (sequence-word-cons-tag sequence-unsigned-word-of-value
          sequence-even-tags-mark-even-words sequence-cons-fields-of-represented-value
          sequence-cons-address-without-wrap
          (:instance sequence-cons-record-selected-above-base
                     (address (proof-pointer-address word base))))
    :expand ((sequence-cons-spine-p datum word base machine))))
  :rule-classes nil)
