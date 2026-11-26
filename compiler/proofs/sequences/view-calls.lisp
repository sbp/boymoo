(in-package "BOYMOO-PROOFS")

(include-book "returns")
(include-book "coerce-dispatch")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-length-offset* (sequence-offset "jet:COMMON-LISP::LENGTH"))
(defconst *sequence-char-offset* (sequence-offset "jet:COMMON-LISP::CHAR"))
(defconst *sequence-view-offset* (sequence-offset "rt:string-view"))
(defconst *sequence-list-length-offset* (sequence-offset "rt:list-length"))
(defconst *sequence-length-tag-offset* (sequence-offset "rt:length-tag"))
(defconst *sequence-index-count-offset* (sequence-offset "rt:sequence-count"))

(sequence-defpath *sequence-length-view-call*
  ("jet:COMMON-LISP::LENGTH" 0 2))

(sequence-defpath *sequence-char-view-call*
  ("jet:COMMON-LISP::CHAR" 0 3))

(sequence-defpath *sequence-coerce-list-view-call*
  ("prim:COMMON-LISP::COERCE" 24 2))

(defun sequence-view-call-path (routine)
  (case routine
    (char *sequence-char-view-call*)
    (coerce *sequence-coerce-list-view-call*)
    (otherwise *sequence-length-view-call*)))

(defun sequence-view-caller-offset (routine)
  (case routine
    (char *sequence-char-offset*)
    (coerce *sequence-coerce-list-offset*)
    (otherwise *sequence-length-offset*)))

(defthm sequence-view-call-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (path (sequence-view-call-path routine))
         (link (+ image-base (sequence-view-caller-offset routine) (* 4 (len path))))
         (after (sequence-execute path before)))
    (implies
     (and (member-eq routine '(char length coerce))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base (sequence-view-caller-offset routine)))
          (unsigned-byte-p 64 link)
          (<= 16 stack))
     (and (equal (proof-world-pc after) (+ image-base *sequence-view-offset*))
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (implies (eq routine 'char)
                   (equal (proof-world-reg 5 after) (proof-world-reg 1 before)))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (- stack 16))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (proof-register-frame-p 28 (if (eq routine 'char) '(0 1 2 3 4 5) '(0 1 2 3))
                                  before after)
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-write-bytes
                  8 (- stack 8) (proof-world-reg 30 before)
                  (boymoo-model::a64-write-bytes
                   8 (- stack 16) (proof-world-reg 29 before)
                   (boymoo-model::a64-memory machine)))))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (limit clobbers first last)
                                  (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(sequence-defpath *sequence-length-view-to-tag*
  ("jet:COMMON-LISP::LENGTH" 2 1))

(sequence-defpath *sequence-length-view-to-list*
  ("jet:COMMON-LISP::LENGTH" 2 2))

(defun sequence-length-dispatch-path (payload)
  (if (equal payload 0) *sequence-length-view-to-list* *sequence-length-view-to-tag*))

(defthm sequence-length-after-view-effects
  (let* ((machine (proof-world-machine before))
         (payload (proof-world-reg 1 before))
         (after (sequence-execute (sequence-length-dispatch-path payload) before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-length-offset* 8))
          (unsigned-byte-p 64 (+ image-base *sequence-length-tag-offset*)))
     (and (equal (proof-world-pc after)
                 (+ image-base (if (equal payload 0)
                                   *sequence-list-length-offset* *sequence-length-tag-offset*)))
          (equal (proof-world-reg 30 after)
                 (if (equal payload 0)
                     (+ image-base *sequence-length-tag-offset*)
                   (proof-world-reg 30 before)))
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 2 after) (proof-world-reg 2 before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (proof-register-frame-p 28 '(0 1 2 3) before after)
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (limit clobbers first last)
                                  (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(sequence-defpath *sequence-char-count-call*
  ("jet:COMMON-LISP::CHAR" 3 3))

(defthm sequence-char-index-call-effects
  (let* ((machine (proof-world-machine before))
         (after (sequence-execute *sequence-char-count-call* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-char-offset* 12))
          (unsigned-byte-p 64 (+ image-base *sequence-char-offset* 24))
          (not (equal (proof-world-reg 1 before) 0)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-index-count-offset*))
          (equal (proof-world-reg 30 after) (+ image-base *sequence-char-offset* 24))
          (equal (proof-world-reg 0 after) (proof-world-reg 5 before))
          (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
          (equal (proof-world-reg 2 after) (proof-world-reg 2 before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (proof-register-frame-p 28 '(0 1 2 3 4 5) before after)
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (limit clobbers first last)
                                  (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-view-call-cutpoint
  (let* ((machine (proof-world-machine before))
         (path (sequence-view-call-path routine))
         (entry (+ image-base (sequence-view-caller-offset routine)))
         (link (+ entry (* 4 (len path))))
         (cuts (list (+ image-base *sequence-view-offset*)))
         (after (sequence-execute path before)))
    (implies
     (and (member-eq routine '(char length coerce))
          (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) entry)
          (unsigned-byte-p 64 link)
          (<= 16 (boymoo-model::a64-sp machine))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 30 after) link)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (implies (eq routine 'char)
                   (equal (proof-world-reg 5 after) (proof-world-reg 1 before))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p sequence-view-call-path sequence-view-caller-offset
                        proof-world-machine proof-world-reg proof-world-pc)
    :use
    (sequence-view-call-effects
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-view-call-path routine))
                (cuts (list (+ image-base *sequence-view-offset*)))
                (after (sequence-execute (sequence-view-call-path routine) before))))))
  :rule-classes nil)

(defthm sequence-length-dispatch-cutpoint
  (let* ((machine (proof-world-machine before))
         (payload (proof-world-reg 1 before))
         (path (sequence-length-dispatch-path payload))
         (cuts (list (+ image-base (if (equal payload 0)
                                      *sequence-list-length-offset*
                                    *sequence-length-tag-offset*))))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-length-offset* 8))
          (unsigned-byte-p 64 (+ image-base *sequence-length-tag-offset*))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 2 after) (proof-world-reg 2 before))
          (implies (equal payload 0)
                   (equal (proof-world-reg 30 after)
                          (+ image-base *sequence-length-tag-offset*))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p sequence-length-dispatch-path
                        proof-world-machine proof-world-reg proof-world-pc)
    :use
    (sequence-length-after-view-effects
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-length-dispatch-path (proof-world-reg 1 before)))
                (cuts (list (+ image-base (if (equal (proof-world-reg 1 before) 0)
                                              *sequence-list-length-offset*
                                            *sequence-length-tag-offset*))))
                (after (sequence-execute (sequence-length-dispatch-path (proof-world-reg 1 before))
                                         before))))))
  :rule-classes nil)

(defthm sequence-char-index-cutpoint
  (let* ((machine (proof-world-machine before))
         (path *sequence-char-count-call*)
         (cuts (list (+ image-base *sequence-index-count-offset*)))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-char-offset* 12))
          (unsigned-byte-p 64 (+ image-base *sequence-char-offset* 24))
          (not (equal (proof-world-reg 1 before) 0))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-world-reg 0 after) (proof-world-reg 5 before))
          (equal (proof-world-reg 30 after) (+ image-base *sequence-char-offset* 24)))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-world-machine proof-world-reg proof-world-pc)
    :use
    (sequence-char-index-call-effects
     (:instance sequence-segment-of-instruction-path
                (instructions *sequence-char-count-call*)
                (cuts (list (+ image-base *sequence-index-count-offset*)))
                (after (sequence-execute *sequence-char-count-call* before))))))
  :rule-classes nil)
