(in-package "BOYMOO-PROOFS")

(include-book "subseq-counts")
(include-book "copy-loops")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-subseq-list-nil-offset* (sequence-offset "rt:subseq-nil"))
(defconst *sequence-subseq-drop-offset* (sequence-offset "rt:subseq-drop"))

(sequence-defpath *sequence-subseq-bounded-string-path*
  ("rt:subseq-checked" 0 4))

(sequence-defpath *sequence-subseq-bounded-empty-list-path*
  ("rt:subseq-checked" 0 4)
  ("rt:subseq-list" 0 1))

(sequence-defpath *sequence-subseq-bounded-list-path*
  ("rt:subseq-checked" 0 4)
  ("rt:subseq-list" 0 3))

(defun sequence-subseq-bounded-path (string-flag size)
  (cond ((not (equal string-flag 0)) *sequence-subseq-bounded-string-path*)
        ((equal size 0) *sequence-subseq-bounded-empty-list-path*)
        (t *sequence-subseq-bounded-list-path*)))

(defun sequence-subseq-bounded-target (string-flag size)
  (cond ((not (equal string-flag 0)) (+ *sequence-subseq-checked-offset* 16))
        ((equal size 0) *sequence-subseq-list-nil-offset*)
        (t *sequence-subseq-drop-offset*)))

(defthm sequence-subseq-bounded-selection-effects
  (let* ((machine (proof-world-machine before))
         (size (proof-world-reg 19 before))
         (flag (proof-world-reg 21 before))
         (path (sequence-subseq-bounded-path flag size))
         (target (+ image-base (sequence-subseq-bounded-target flag size)))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-checked-offset*))
          (unsigned-byte-p 32 size)
          (unsigned-byte-p 64 target))
     (and (equal (proof-world-pc after) target)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 19 after) size)
          (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
          (equal (proof-world-reg 21 after) flag)
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
          (proof-register-frame-p 30 '(1) before after))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-execute) (sequence-signed-word))
    :use ((:instance sequence-floor-unique (value (proof-world-reg 19 before))
                     (divisor (expt 2 60)) (quotient 0)))
    :expand ((:free (limit clobbers first last)
                    (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-subseq-bounded-selection
  (let* ((size (proof-world-reg 19 before))
         (flag (proof-world-reg 21 before))
         (path (sequence-subseq-bounded-path flag size))
         (cuts (list (+ image-base (sequence-subseq-bounded-target flag size))))
         (after (sequence-execute path before))
         (difference (- (sequence-end limit datum) start)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-checked-offset*))
          (unsigned-byte-p 32 size)
          (or (equal size (sequence-count difference)) (equal size (sequence-runtime-count difference)))
          (unsigned-byte-p 64 (car cuts))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 19 after) (sequence-result-size datum start limit)))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-result-size)
                    (proof-world-machine proof-world-pc proof-world-reg proof-world-stop proof-register-frame-p
                     proof-segment-p sequence-execute sequence-instruction-path sequence-subseq-bounded-path
                     sequence-subseq-bounded-target sequence-end sequence-runtime-count sequence-count
                     sequence-runtime-count-exact-for-bounded-size))
    :use (sequence-subseq-bounded-selection-effects
          (:instance sequence-runtime-count-exact-for-bounded-size (value (- (sequence-end limit datum) start)))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-subseq-bounded-path (proof-world-reg 21 before)
                                                               (proof-world-reg 19 before)))
                     (cuts (list (+ image-base (sequence-subseq-bounded-target (proof-world-reg 21 before)
                                                                             (proof-world-reg 19 before)))))
                     (after (sequence-execute (sequence-subseq-bounded-path (proof-world-reg 21 before)
                                                                           (proof-world-reg 19 before)) before))))))
  :rule-classes nil)
