(in-package "BOYMOO-PROOFS")

(include-book "view-calls")
(include-book "subseq-counts")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-subseq-offset* (sequence-offset "jet:COMMON-LISP::SUBSEQ"))
(defconst *sequence-subseq-tag-length-offset* (sequence-offset "rt:subseq-tag-length"))

(sequence-defpath *sequence-subseq-view-call*
  ("jet:COMMON-LISP::SUBSEQ" 0 6))

(defun sequence-subseq-caller-save-memory (before)
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine)))
    (boymoo-model::a64-write-bytes
     8 (- stack 24) (proof-world-reg 30 before)
     (boymoo-model::a64-write-bytes
      8 (- stack 32) (proof-world-reg 21 before)
      (boymoo-model::a64-write-bytes
       8 (- stack 8) (proof-world-reg 20 before)
       (boymoo-model::a64-write-bytes 8 (- stack 16) (proof-world-reg 19 before)
                                     (boymoo-model::a64-memory machine)))))))

(defthm sequence-subseq-view-call-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (after (sequence-execute *sequence-subseq-view-call* before))
         (link (+ image-base *sequence-subseq-offset* 24))
         (last (proof-world-machine after)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-offset*))
          (unsigned-byte-p 64 link) (<= 32 stack))
     (and (equal (proof-world-pc after) (+ image-base *sequence-view-offset*))
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 5 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 6 after) (proof-world-reg 1 before))
          (equal (proof-world-reg 7 after) (proof-world-reg 2 before))
          (equal (boymoo-model::a64-sp last) (- stack 32))
          (equal (boymoo-model::a64-memory last) (sequence-subseq-caller-save-memory before))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (consp (boymoo-model::a64-registers last))
          (proof-register-frame-p 29 '(5 6 7) before after))))
  :hints (("Goal" :in-theory (e/d (sequence-execute) (proof-instruction-effect))
           :expand ((:free (index clobbers first last)
                           (proof-register-frame-p index clobbers first last)))))
  :rule-classes nil)

(sequence-defpath *sequence-subseq-explicit-end*
  ("jet:COMMON-LISP::SUBSEQ" 6 4))

(sequence-defpath *sequence-subseq-string-end*
  ("jet:COMMON-LISP::SUBSEQ" 6 5))

(sequence-defpath *sequence-subseq-list-end-call*
  ("jet:COMMON-LISP::SUBSEQ" 6 6))

(sequence-defpath *sequence-subseq-tag-length*
  ("rt:subseq-tag-length" 0 2))

(defun sequence-subseq-end-branch (word payload)
  (cond ((not (equal word *proof-nil*)) *sequence-subseq-explicit-end*)
        ((not (equal payload 0)) *sequence-subseq-string-end*)
        (t *sequence-subseq-list-end-call*)))

(defthm sequence-subseq-end-branch-effects
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 7 before))
         (payload (proof-world-reg 1 before))
         (path (sequence-subseq-end-branch word payload))
         (tag (+ image-base *sequence-subseq-tag-length-offset*))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-subseq-offset* 24))
          (unsigned-byte-p 64 (+ image-base *sequence-subseq-end-ready-offset*)))
     (and (equal (proof-world-pc after)
                 (cond ((not (equal word *proof-nil*)) (+ image-base *sequence-subseq-end-ready-offset*))
                       ((not (equal payload 0)) tag)
                       (t (+ image-base *sequence-list-length-offset*))))
          (equal (proof-world-reg 21 after) (if (equal payload 0) 0 1))
          (equal (proof-world-reg 30 after)
                 (if (and (equal word *proof-nil*) (equal payload 0))
                     tag
                   (proof-world-reg 30 before)))
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 2 after) (proof-world-reg 2 before))
          (equal (proof-world-reg 5 after) (proof-world-reg 5 before))
          (equal (proof-world-reg 6 after) (proof-world-reg 6 before))
          (equal (proof-world-reg 7 after) word)
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (proof-register-frame-p 29 '(21) before after))))
  :hints (("Goal"
           :in-theory (e/d (sequence-execute) (proof-instruction-effect))
           :use ((:instance sequence-zero-for-equal-words (left (proof-world-reg 7 before)) (right *proof-nil*)))
           :expand ((:free (index clobbers first last)
                           (proof-register-frame-p index clobbers first last)))))
  :rule-classes nil)

(defthm sequence-subseq-default-end-tags-length
  (let* ((machine (proof-world-machine before))
         (count (proof-world-reg 2 before))
         (after (sequence-execute *sequence-subseq-tag-length* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 32 count)
          (unsigned-byte-p 64 (+ 8 (proof-world-pc before))))
     (and (equal (proof-world-reg 7 after) (proof-integer-word count))
          (equal (proof-world-pc after) (+ 8 (proof-world-pc before)))
          (equal (proof-world-stop after) (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
          (proof-register-frame-p 30 '(7) before after))))
  :hints (("Goal" :in-theory (e/d (sequence-execute) (proof-instruction-effect))
           :expand ((:free (index clobbers first last)
                           (proof-register-frame-p index clobbers first last)))))
  :rule-classes nil)
