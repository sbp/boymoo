(in-package "BOYMOO-PROOFS")

(include-book "copy-loops")
(include-book "spine-bounds")
(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-subseq-drop-zero*
  ("rt:subseq-drop" 0 1))

(sequence-defpath *sequence-subseq-drop-atom*
  ("rt:subseq-drop" 0 3))

(defun sequence-subseq-drop-end-path (count)
  (if (zp count) *sequence-subseq-drop-zero* *sequence-subseq-drop-atom*))

(defun sequence-subseq-list-drop-path (datum count)
  (if (and (consp datum) (posp count))
      (append *sequence-subseq-list-drop-cell*
              (sequence-subseq-list-drop-path (cdr datum) (1- count)))
    (sequence-subseq-drop-end-path count)))

(local
 (defthm sequence-drop-path-on-cell
   (implies (and (consp datum) (posp count))
            (equal (sequence-subseq-list-drop-path datum count)
                   (append *sequence-subseq-list-drop-cell*
                           (sequence-subseq-list-drop-path (cdr datum) (1- count)))))
   :hints (("Goal" :expand ((sequence-subseq-list-drop-path datum count))))))

(local
 (defthm sequence-drop-path-when-done
   (implies (not (and (consp datum) (posp count)))
            (equal (sequence-subseq-list-drop-path datum count)
                   (sequence-subseq-drop-end-path count)))
   :hints (("Goal" :expand ((sequence-subseq-list-drop-path datum count))))))

(local (in-theory (disable (:definition sequence-subseq-list-drop-path))))

(local
 (defthm sequence-drop-end-effects
   (let* ((machine (proof-world-machine before))
          (count (proof-world-reg 20 before))
          (word (proof-world-reg 0 before))
          (path (sequence-subseq-drop-end-path count))
          (after (sequence-execute path before)))
     (implies
      (and (consp (boymoo-model::a64-registers machine))
           (or (equal count 0) (not (equal (proof-word-tag word) 0)))
           (unsigned-byte-p 64 (+ 28 (proof-world-pc before))))
      (and (equal (proof-world-pc after) (+ 28 (proof-world-pc before)))
           (equal (proof-world-reg 0 after) word)
           (equal (proof-heap-base after) (proof-heap-base before))
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (proof-world-regions after) (proof-world-regions before))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (boymoo-model::a64-memory machine)))))
   :hints (("Goal" :in-theory (e/d (sequence-execute) (sequence-signed-word))))
   :rule-classes nil))

(local
 (defthm sequence-drop-register-natural
   (natp (proof-world-reg register world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-drop-base-fits-word
   (unsigned-byte-p 64 (proof-heap-base world))))

(local
 (defthm sequence-drop-cons-address-is-ordinary
   (let ((word (proof-world-reg 0 world))
         (base (proof-heap-base world)))
     (implies (and (equal (proof-word-tag word) 0)
                   (proof-span-p (+ base word) 16))
              (equal (proof-pointer-address word base) (+ base word))))))

(local
 (defthm sequence-subseq-drop-view-step
   (let* ((machine (proof-world-machine before))
          (word (proof-world-reg 0 before))
          (base (proof-heap-base before))
          (address (proof-pointer-address word base))
          (rank (proof-object-rank (assoc-equal address objects)))
          (count (proof-world-reg 20 before))
          (after (sequence-execute *sequence-subseq-list-drop-cell* before))
          (returned (proof-world-machine after)))
     (implies
      (and (consp datum) (posp count)
           (consp (boymoo-model::a64-registers machine))
           (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view datum))
           (sequence-cons-offsets-ordinary-p objects base)
           (unsigned-byte-p 64 (+ 28 (proof-world-pc before))))
      (and (equal (proof-world-pc after) (proof-world-pc before))
           (equal (proof-world-reg 20 after) (1- count))
           (equal (proof-heap-base after) base)
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (proof-world-regions after) (proof-world-regions before))
           (equal (boymoo-model::a64-memory returned)
                  (boymoo-model::a64-memory machine))
           (consp (boymoo-model::a64-registers returned))
           (equal (proof-view-step :word (proof-world-reg 0 after) 0 rank base objects packages
                                   returned)
                  (proof-value-view (cdr datum))))))
   :hints
   (("Goal"
     :in-theory (disable proof-view-step proof-word-tag proof-pointer-address proof-load-word
                         proof-world-reg proof-world-machine proof-world-pc proof-heap-base
                         proof-object-kind proof-object-rank sequence-cons-offsets-ordinary-p
                         sequence-even-tags-mark-even-words sequence-drop-cons-address-is-ordinary
                         oddp evenp)
     :use
     (sequence-subseq-drop-cell-effects
      (:instance sequence-drop-cons-address-is-ordinary (world before))
      (:instance sequence-cons-spine-from-value-view
                 (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                 (machine (proof-world-machine before)))
      (:instance sequence-even-tags-mark-even-words (word (proof-world-reg 0 before)))
      (:instance sequence-cons-fields-of-represented-value
                 (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                 (machine (proof-world-machine before)))
      (:instance sequence-view-step-of-equal-memory
                 (kind :word) (count 0)
                 (input (proof-load-word (+ 8 (proof-heap-base before) (proof-world-reg 0 before))
                                         (proof-world-machine before)))
                 (depth (proof-object-rank
                         (assoc-equal (proof-pointer-address (proof-world-reg 0 before)
                                                              (proof-heap-base before))
                                      objects)))
                 (base (proof-heap-base before)) (first (proof-world-machine before))
                 (last (proof-world-machine
                        (sequence-execute *sequence-subseq-list-drop-cell* before)))))))
   :rule-classes nil))

(local
 (defun sequence-subseq-drop-induction (datum depth world objects)
   (if (and (consp datum) (posp (proof-world-reg 20 world)))
       (let* ((word (proof-world-reg 0 world))
              (base (proof-heap-base world))
              (address (proof-pointer-address word base))
              (rank (proof-object-rank (assoc-equal address objects))))
         (sequence-subseq-drop-induction
          (cdr datum) rank (sequence-execute *sequence-subseq-list-drop-cell* world) objects))
     depth)))

(defthm sequence-subseq-list-drop-effects
  (let* ((machine (proof-world-machine before))
         (word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (count (proof-world-reg 20 before))
         (path (sequence-subseq-list-drop-path datum count))
         (after (sequence-execute path before))
         (tail (sequence-drop count datum)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-view-step :word word 0 depth base objects packages machine)
                 (proof-value-view datum))
          (sequence-cons-offsets-ordinary-p objects base)
          (unsigned-byte-p 64 (+ 28 (proof-world-pc before))))
     (and (equal (proof-world-pc after) (+ 28 (proof-world-pc before)))
          (equal (proof-heap-base after) base)
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory machine))
          (proof-value-p (proof-world-reg 0 after) tail base objects packages
                         (proof-world-machine after)))))
  :hints
  (("Goal"
    :induct (sequence-subseq-drop-induction datum depth before objects)
    :in-theory (disable proof-view-step proof-value-p proof-view proof-word-tag proof-pointer-address
                        proof-world-pc proof-world-reg proof-world-machine proof-heap-base
                        proof-load-word sequence-cons-offsets-ordinary-p acl2::binary-append
                        sequence-drop-cons-address-is-ordinary sequence-subseq-drop-end-path))
   ("Subgoal *1/2"
    :use
    (sequence-drop-end-effects
     (:instance sequence-word-cons-tag
                (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                (machine (proof-world-machine before)))
     (:instance sequence-value-view-at-its-own-rank
                (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                (machine (proof-world-machine before)))
     (:instance sequence-view-of-equal-memory
                (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                (first (proof-world-machine before))
                (last (proof-world-machine
                       (sequence-execute
                        (sequence-subseq-drop-end-path (proof-world-reg 20 before))
                        before)))))
    :in-theory (disable proof-view-step proof-view proof-word-tag proof-pointer-address
                        proof-world-pc proof-world-reg proof-world-machine proof-heap-base
                        proof-load-word sequence-cons-offsets-ordinary-p
                        proof-integer-view proof-load-string sequence-subseq-drop-end-path))
   ("Subgoal *1/1"
    :use sequence-subseq-drop-view-step))
  :rule-classes nil)

(defthm sequence-subseq-list-drop-segment
  (let* ((count (sequence-runtime-count start))
         (path (sequence-subseq-list-drop-path datum count))
         (cuts (list (+ 28 (proof-world-pc before))))
         (after (sequence-execute path before)))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (not (stringp datum))
          (proof-heap-p before objects packages)
          (proof-reg-value-p 0 datum before objects packages)
          (equal (proof-world-reg 20 before) count)
          (unsigned-byte-p 64 (+ 28 (proof-world-pc before)))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-reg-value-p 0 (sequence-drop count datum) after objects packages)
          (equal (take size (sequence-drop count datum))
                 (take size (boymoo-model::core-nthcdr (sequence-count start) datum))))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-view-step proof-view proof-heap-p
                        proof-world-pc proof-world-reg proof-world-machine proof-heap-base
                        proof-pointer-address sequence-subseq-list-drop-path
                        sequence-drop sequence-runtime-count sequence-take-after-saturated-drop)
    :expand ((proof-view (proof-world-reg 0 before) (proof-heap-base before)
                         objects packages (proof-world-machine before)))
    :use
    ((:instance sequence-subseq-list-drop-effects
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address (proof-world-reg 0 before)
                                                                       (proof-heap-base before))
                                               objects))))))
     (:instance sequence-ordinary-cons-offsets-of-heap (world before))
     (:instance sequence-represented-sequence-length-bounded
                (word (proof-world-reg 0 before)) (world before))
     (:instance sequence-take-after-saturated-drop)
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-subseq-list-drop-path datum (sequence-runtime-count start)))
                (cuts (list (+ 28 (proof-world-pc before))))
                (after (sequence-execute
                        (sequence-subseq-list-drop-path datum (sequence-runtime-count start))
                        before))))))
  :rule-classes nil)
