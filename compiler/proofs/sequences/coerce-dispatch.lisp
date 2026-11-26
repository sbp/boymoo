(in-package "BOYMOO-PROOFS")

(include-book "helpers")

(logic)
(set-verify-guards-eagerness 0)

(defconst *sequence-coerce-offset* (sequence-offset "prim:COMMON-LISP::COERCE"))
(defconst *sequence-coerce-string-offset* (sequence-offset "rt:coerce-to-string"))
(defconst *sequence-coerce-list-offset* (+ 96 *sequence-coerce-offset*))

(sequence-defpath *sequence-coerce-check-tag*
  ("prim:COMMON-LISP::COERCE" 0 3))
(sequence-defpath *sequence-coerce-check-header*
  ("prim:COMMON-LISP::COERCE" 0 8))
(sequence-defpath *sequence-coerce-check-package*
  ("prim:COMMON-LISP::COERCE" 0 12))
(sequence-defpath *sequence-coerce-check-name-length*
  ("prim:COMMON-LISP::COERCE" 0 18))
(sequence-defpath *sequence-coerce-check-name*
  ("prim:COMMON-LISP::COERCE" 0 24))

(defun sequence-coerce-name-address (symbol base machine)
  (boymoo-model::a64-unsigned 64
    (+ base (- (proof-load-word (+ symbol 8) machine) 2))))

(defun sequence-coerce-type-test (word base machine)
  (let* ((symbol (proof-pointer-address word base))
         (name (sequence-coerce-name-address symbol base machine)))
    (cond
     ((not (equal (proof-word-tag word) 2)) :tag)
     ((not (equal (proof-header-type (proof-load-word symbol machine)) 2)) :header)
     ((not (equal (proof-load-word (+ symbol 16) machine)
                  (proof-load-word (+ base 48) machine))) :package)
     ((not (equal (proof-load-word name machine) (+ 1 (* 256 4)))) :name-length)
     ((not (equal (boymoo-model::a64-unsigned 32 (proof-load-word (+ name 8) machine))
                  #x5453494c)) :name)
     (t :list))))

(defun sequence-coerce-dispatch-path (before)
  (case (sequence-coerce-type-test (proof-world-reg 1 before)
                                   (proof-heap-base before) (proof-world-machine before))
    (:tag *sequence-coerce-check-tag*)
    (:header *sequence-coerce-check-header*)
    (:package *sequence-coerce-check-package*)
    (:name-length *sequence-coerce-check-name-length*)
    (otherwise *sequence-coerce-check-name*)))

(defun sequence-coerce-test-readable-p (word base machine)
  (let* ((symbol (proof-pointer-address word base))
         (name (sequence-coerce-name-address symbol base machine)))
    (implies (and (equal (proof-word-tag word) 2)
                  (equal (proof-header-type (proof-load-word symbol machine)) 2))
             (and (unsigned-byte-p 64 (+ symbol 16))
                  (unsigned-byte-p 64 (+ base 48))
                  (implies (equal (proof-load-word name machine) (+ 1 (* 256 4)))
                           (unsigned-byte-p 64 (+ name 8)))))))

(defthm sequence-coerce-type-test-effects
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (word (proof-world-reg 1 before))
         (test (sequence-coerce-type-test word base machine))
         (path (sequence-coerce-dispatch-path before))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset*))
          (sequence-coerce-test-readable-p word base machine))
     (and (equal (proof-world-pc after)
                 (+ image-base (if (eq test :list)
                                   *sequence-coerce-list-offset*
                                 *sequence-coerce-string-offset*)))
          (proof-register-frame-p 30 '(1 2 3) before after)
          (consp (boymoo-model::a64-registers (proof-world-machine after)))
          (equal (cdr after) (cdr before))
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (proof-world-replies after) (proof-world-replies before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine)))))
  :hints
  (("Goal" :in-theory (enable sequence-execute
                              boymoo-model::a64-exec-move-wide)
           :use ((:instance sequence-zero-for-equal-words
                            (left (proof-word-tag (proof-world-reg 1 before)))
                            (right 2))
                 (:instance sequence-zero-for-equal-words
                            (left (proof-load-word
                                   (+ 16 (proof-pointer-address (proof-world-reg 1 before)
                                                                 (proof-heap-base before)))
                                   (proof-world-machine before)))
                            (right (proof-load-word (+ 48 (proof-heap-base before))
                                                     (proof-world-machine before))))
                 (:instance sequence-zero-for-equal-words
                            (left (proof-header-type
                                   (proof-load-word
                                    (proof-pointer-address (proof-world-reg 1 before)
                                                           (proof-heap-base before))
                                    (proof-world-machine before))))
                            (right 2))
                 (:instance sequence-zero-for-equal-words
                            (left (proof-load-word
                                   (sequence-coerce-name-address
                                    (proof-pointer-address (proof-world-reg 1 before)
                                                           (proof-heap-base before))
                                    (proof-heap-base before) (proof-world-machine before))
                                   (proof-world-machine before)))
                            (right 1025))
                 (:instance sequence-zero-for-equal-words
                            (left (boymoo-model::a64-unsigned
                                   32 (proof-load-word
                                       (+ 8 (sequence-coerce-name-address
                                             (proof-pointer-address (proof-world-reg 1 before)
                                                                    (proof-heap-base before))
                                             (proof-heap-base before)
                                             (proof-world-machine before)))
                                       (proof-world-machine before))))
                            (right #x5453494c)))
           :expand ((:free (register clobbers first last)
                           (proof-register-frame-p register clobbers first last)))))
  :rule-classes nil)

(defthm sequence-coerce-type-test-cutpoint
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (word (proof-world-reg 1 before))
         (test (sequence-coerce-type-test word base machine))
         (path (sequence-coerce-dispatch-path before))
         (cuts (list (+ image-base (if (eq test :list)
                                      *sequence-coerce-list-offset*
                                    *sequence-coerce-string-offset*))))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset*))
          (sequence-coerce-test-readable-p word base machine)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-register-frame-p 30 '(1 2 3) before after))))
  :hints
  (("Goal" :in-theory (disable proof-segment-p proof-register-frame-p
                               sequence-coerce-type-test sequence-coerce-dispatch-path
                               sequence-coerce-test-readable-p)
           :use (sequence-coerce-type-test-effects
                 (:instance sequence-segment-of-instruction-path
                            (instructions (sequence-coerce-dispatch-path before))
                            (cuts (list (+ image-base
                                           (if (eq (sequence-coerce-type-test
                                                    (proof-world-reg 1 before)
                                                    (proof-heap-base before)
                                                    (proof-world-machine before))
                                                   :list)
                                               *sequence-coerce-list-offset*
                                             *sequence-coerce-string-offset*))))
                            (after (sequence-execute (sequence-coerce-dispatch-path before)
                                                     before))))))
  :rule-classes nil)
