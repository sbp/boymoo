(in-package "BOYMOO-PROOFS")

(include-book "counts")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-length-return*
  ("rt:length-tag" 0 4))

(sequence-defpath *sequence-char-read-return*
  ("jet:COMMON-LISP::CHAR" 6 7))

(sequence-defpath *sequence-char-out-of-range-return*
  ("jet:COMMON-LISP::CHAR" 6 2)
  ("rt:char-nil" 0 2)
  ("rt:nil" 0 2))

(sequence-defpath *sequence-char-nonstring-return*
  ("jet:COMMON-LISP::CHAR" 3 1)
  ("rt:char-nil" 0 2)
  ("rt:nil" 0 2))

(defun sequence-char-return-path (index length)
  (if (< index length)
      *sequence-char-read-return*
    *sequence-char-out-of-range-return*))

(defthm sequence-length-return-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (count (proof-world-reg 2 before))
         (after (sequence-execute *sequence-length-return* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 32 count)
          (unsigned-byte-p 64 (+ stack 16)))
     (and (equal (proof-world-reg 0 after) (proof-integer-word count))
          (equal (proof-world-reg 29 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
          (equal (proof-world-pc after) (proof-load-word (+ stack 8) machine))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16))
          (proof-register-frame-p 28 '(0 1 2 3) before after)
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (limit clobbers first last)
                                  (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-char-return-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (index (proof-world-reg 0 before))
         (payload (proof-world-reg 1 before))
         (length (proof-world-reg 2 before))
         (path (sequence-char-return-path index length))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (proof-span-p payload length)
          (unsigned-byte-p 64 (+ stack 16)))
     (and (equal (proof-world-reg 0 after)
                 (if (< index length)
                     (+ 4 (* 8 (boymoo-model::a64-load 1 (+ payload index) machine)))
                   *proof-nil*))
          (equal (proof-world-reg 29 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
          (equal (proof-world-pc after) (proof-load-word (+ stack 8) machine))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16))
          (proof-register-frame-p 28 '(0 1 2 3 4 5) before after)
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (e/d (sequence-execute) (sequence-signed-word))
                  :expand ((:free (limit clobbers first last)
                                  (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-char-nonstring-return-effects
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (after (sequence-execute *sequence-char-nonstring-return* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 1 before) 0)
          (unsigned-byte-p 64 (+ stack 16)))
     (and (equal (proof-world-reg 0 after) *proof-nil*)
          (equal (proof-world-reg 29 after) (proof-load-word stack machine))
          (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
          (equal (proof-world-pc after) (proof-load-word (+ stack 8) machine))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (proof-heap-base after) (proof-heap-base before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ stack 16))
          (proof-register-frame-p 28 '(0 1 2 3 4 5) before after)
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :in-theory (enable sequence-execute)
                  :expand ((:free (limit clobbers first last)
                                  (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(defthm sequence-tagged-character-view
  (implies (unsigned-byte-p 8 byte)
           (proof-value-p (+ 4 (* 8 byte)) (code-char byte) base objects packages machine))
  :hints (("Goal"
           :in-theory (enable sequence-a64-unsigned-as-mod)
           :use ((:instance sequence-mod-add-multiple (value 4) (divisor 8) (multiple byte))
                 (:instance sequence-mod-add-multiple (value 0) (divisor 2) (multiple (+ 2 (* 4 byte))))
                 (:instance sequence-floor-unique
                            (value (+ 4 (* 8 byte))) (divisor 8) (quotient byte))))))

(defthm sequence-tagged-length-view
  (implies (unsigned-byte-p 32 length)
           (proof-value-p (proof-integer-word length) length base objects packages machine))
  :hints (("Goal"
           :in-theory (enable sequence-a64-unsigned-as-mod)
           :use ((:instance sequence-mod-add-multiple (value 1) (divisor 2) (multiple length))
                 (:instance sequence-floor-unique
                            (value (+ 1 (* 2 length))) (divisor 2) (quotient length))))))

(defthm sequence-length-return-value
  (let* ((machine (proof-world-machine before))
         (count (proof-world-reg 2 before))
         (after (sequence-execute *sequence-length-return* before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 32 count)
          (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp machine)))
          (equal count (len (sequence-elements datum))))
     (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                        objects packages (proof-world-machine after))
            (boymoo-model::core-prelude 'length (list datum)))))
  :hints (("Goal"
           :in-theory (disable proof-view proof-world-reg proof-world-machine proof-heap-base
                               sequence-core-length boymoo-model::core-prelude-values)
           :use (sequence-length-return-effects sequence-core-length
                 (:instance sequence-tagged-length-view
                            (length (proof-world-reg 2 before))
                            (base (proof-heap-base before))
                            (machine (proof-world-machine
                                      (sequence-execute *sequence-length-return* before)))))))
  :rule-classes nil)

(defthm sequence-char-return-value
  (let* ((machine (proof-world-machine before))
         (payload (proof-world-reg 1 before))
         (index (proof-world-reg 0 before))
         (length (proof-world-reg 2 before))
         (path (sequence-char-return-path index length))
         (after (sequence-execute path before))
         (result-machine (proof-world-machine after)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (proof-span-p payload length)
          (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp machine)))
          (<= length *proof-space-size*)
          (equal datum (proof-load-string length payload machine))
          (equal index (sequence-runtime-count position))
          (proof-value-p *proof-nil* nil (proof-heap-base after)
                         objects packages result-machine))
     (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                        objects packages result-machine)
            (boymoo-model::core-prelude 'char (list datum position)))))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-load-string sequence-char-return-path
                        sequence-runtime-count sequence-core-char
                        boymoo-model::core-prelude-values)
    :use (sequence-char-return-effects
          (:instance sequence-core-char (index position))
          (:instance sequence-char-of-load-string
                     (count (proof-world-reg 2 before)) (address (proof-world-reg 1 before))
                     (index (proof-world-reg 0 before)) (machine (proof-world-machine before)))
          (:instance sequence-tagged-character-view
                     (byte (boymoo-model::a64-load 1
                              (+ (proof-world-reg 1 before) (proof-world-reg 0 before))
                              (proof-world-machine before)))
                     (base (proof-heap-base before))
                     (machine (proof-world-machine
                               (sequence-execute
                                (sequence-char-return-path (proof-world-reg 0 before)
                                                           (proof-world-reg 2 before))
                                before)))))))
  :rule-classes nil)

(defthm sequence-length-checked-return
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (path *sequence-length-return*)
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (unsigned-byte-p 32 (len (sequence-elements datum)))
          (equal (proof-world-reg 2 before) (len (sequence-elements datum)))
          (unsigned-byte-p 64 (+ stack 16))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                             objects packages (proof-world-machine after))
                 (boymoo-model::core-prelude 'length (list datum))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-view boymoo-model::core-prelude
                        proof-world-machine proof-world-reg proof-world-pc proof-heap-base
                        proof-load-word sequence-elements)
    :use
    (sequence-length-return-effects sequence-length-return-value
     (:instance sequence-segment-of-instruction-path
                (instructions *sequence-length-return*)
                (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                             (proof-world-machine before))))
                (after (sequence-execute *sequence-length-return* before))))))
  :rule-classes nil)

(defun sequence-char-result-path (datum world)
  (if (stringp datum)
      (sequence-char-return-path (proof-world-reg 0 world) (proof-world-reg 2 world))
    *sequence-char-nonstring-return*))

(defthm sequence-char-checked-return
  (let* ((machine (proof-world-machine before))
         (stack (boymoo-model::a64-sp machine))
         (payload (proof-world-reg 1 before))
         (count (proof-world-reg 2 before))
         (cuts (list (proof-load-word (+ stack 8) machine)))
         (path (sequence-char-result-path datum before))
         (after (sequence-execute path before))
         (result-machine (proof-world-machine after)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (<= (len (sequence-elements datum)) *proof-space-size*)
          (unsigned-byte-p 64 (+ stack 16))
          (if (stringp datum)
              (and (proof-span-p payload count)
                   (equal datum (proof-load-string count payload machine))
                   (equal (proof-world-reg 0 before) (sequence-runtime-count position)))
            (equal payload 0))
          (proof-value-p *proof-nil* nil (proof-heap-base after) objects packages result-machine)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                             objects packages result-machine)
                 (boymoo-model::core-prelude 'char (list datum position))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-view proof-span-p boymoo-model::core-prelude
                        proof-world-machine proof-world-reg proof-world-pc proof-heap-base
                        proof-load-word proof-load-string sequence-char-return-path
                        sequence-runtime-count sequence-core-char)
    :use
    (sequence-char-return-effects sequence-char-return-value sequence-char-nonstring-return-effects
     (:instance sequence-core-char (index position))
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-char-result-path datum before))
                (cuts (list (proof-load-word (+ 8 (boymoo-model::a64-sp (proof-world-machine before)))
                                             (proof-world-machine before))))
                (after (sequence-execute (sequence-char-result-path datum before) before))))))
  :rule-classes nil)

