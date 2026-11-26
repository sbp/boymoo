(in-package "BOYMOO-PROOFS")

(include-book "copy-loops")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

; Each input cell is outside the output span. The head word supplies the
; completed CHAR-CODE of the corresponding source element.
(defun sequence-coerce-input-cells-p (datum word base start end memory)
  (if (atom datum)
      t
    (let ((address (proof-pointer-address word base)))
      (and (equal (proof-word-tag word) 0)
           (proof-span-p address 16)
           (proof-disjoint-p address (+ address 16) start end)
           (equal (sequence-car-byte (boymoo-model::a64-read-bytes 8 address memory))
                  (char-code (car datum)))
           (sequence-coerce-input-cells-p
            (cdr datum) (boymoo-model::a64-read-bytes 8 (+ address 8) memory)
            base start end memory)))))

(defun sequence-cons-spans-disjoint-p (objects start end)
  (if (atom objects)
      t
    (let* ((object (car objects))
           (address (proof-object-address object)))
      (and (implies (eq (proof-object-kind object) :cons)
                    (proof-disjoint-p address (+ 16 address) start end))
           (sequence-cons-spans-disjoint-p (cdr objects) start end)))))

(local
 (defthm sequence-selected-cons-disjoint
   (let ((object (assoc-equal address objects)))
     (implies (and (sequence-cons-spans-disjoint-p objects start end)
                   (eq (proof-object-kind object) :cons))
              (proof-disjoint-p address (+ 16 address) start end)))
   :hints (("Goal" :induct (assoc-equal address objects)))
   :rule-classes nil))

(local
 (defun sequence-coerce-input-induction (datum word depth base objects machine)
   (if (atom datum)
       depth
     (let* ((address (proof-pointer-address word base))
            (rank (proof-object-rank (assoc-equal address objects))))
       (sequence-coerce-input-induction (cdr datum) (proof-load-word (+ address 8) machine)
                                      rank base objects machine)))))

(defthm sequence-coerce-input-cells-from-view
  (let ((memory (boymoo-model::a64-memory machine)))
    (implies (and (equal (proof-view-step :word word 0 depth base objects packages machine)
                         (proof-value-view datum))
                  (sequence-cons-spans-disjoint-p objects start end))
             (sequence-coerce-input-cells-p datum word base start end memory)))
  :hints
  (("Goal"
    :induct (sequence-coerce-input-induction datum word depth base objects machine)
    :in-theory (disable proof-view-step proof-pointer-address proof-word-tag
                        proof-object-rank proof-object-kind proof-span-p proof-disjoint-p
                        sequence-cons-spans-disjoint-p sequence-car-byte))
   ("Subgoal *1/2"
    :use (sequence-word-cons-tag sequence-unsigned-word-of-value
          sequence-cons-fields-of-represented-value sequence-even-tags-mark-even-words
          (:instance sequence-selected-cons-disjoint (address (proof-pointer-address word base)))
          (:instance sequence-encoded-character-byte
                     (word (proof-load-word (proof-pointer-address word base) machine))
                     (depth (proof-object-rank
                             (assoc-equal (proof-pointer-address word base) objects)))
                     (datum (car datum))))
    :expand ((sequence-coerce-input-cells-p
              datum word base start end (boymoo-model::a64-memory machine)))))
  :rule-classes nil)

(local
 (defthm sequence-write-keeps-coerce-input-cells
   (implies
    (and (sequence-coerce-input-cells-p datum word base start end memory)
         (proof-subspan-p write-address 1 start end)
         (<= start next-start))
    (sequence-coerce-input-cells-p
     datum word base next-start end
     (boymoo-model::a64-write-bytes 1 write-address byte memory)))
   :hints
   (("Goal"
     :induct (sequence-coerce-input-cells-p datum word base start end memory)
     :in-theory (disable proof-pointer-address proof-word-tag
                         sequence-car-byte sequence-write-one-byte))
    ("Subgoal *1/2"
     :use ((:instance sequence-read-outside-write
                      (count 8) (address (proof-pointer-address word base))
                      (start write-address) (size 1) (value byte))
           (:instance sequence-read-outside-write
                      (count 8) (address (+ 8 (proof-pointer-address word base)))
                      (start write-address) (size 1) (value byte)))))
   :rule-classes nil))

(defun sequence-coerce-string-copy-path (datum)
  (if (atom datum)
      nil
    (append *sequence-coerce-string-step* (sequence-coerce-string-copy-path (cdr datum)))))

(defun sequence-write-list-bytes (datum address memory)
  (if (atom datum)
      memory
    (sequence-write-list-bytes
     (cdr datum) (1+ address)
     (boymoo-model::a64-write-bytes 1 address (char-code (car datum)) memory))))

(local
 (defun sequence-coerce-copy-induction (datum before)
   (if (atom datum)
       before
     (sequence-coerce-copy-induction
      (cdr datum) (sequence-execute *sequence-coerce-string-step* before)))))

(local
 (defthm sequence-coerce-register-natural
   (natp (proof-world-reg register world))
   :rule-classes :type-prescription))

(defthm sequence-coerce-string-copy-effects
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (address (proof-world-reg 1 before))
         (end (+ address (len datum)))
         (base (proof-heap-base before))
         (word (proof-world-reg 4 before))
         (path (sequence-coerce-string-copy-path datum))
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 2 before) (len datum))
          (unsigned-byte-p 64 end)
          (implies (consp datum) (unsigned-byte-p 64 (+ 40 (proof-world-pc before))))
          (sequence-coerce-input-cells-p datum word base address end memory))
     (and (equal (proof-world-pc after)
                 (if (consp datum) (+ 40 (proof-world-pc before)) (proof-world-pc before)))
          (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
          (equal (proof-world-reg 1 after) end)
          (equal (proof-world-reg 2 after) 0)
          (equal (proof-heap-base after) base)
          (equal (proof-world-stop after) (proof-world-stop before))
          (equal (proof-world-regions after) (proof-world-regions before))
          (equal (boymoo-model::a64-sp (proof-world-machine after))
                 (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (sequence-write-list-bytes datum address memory)))))
  :hints
  (("Goal"
    :induct (sequence-coerce-copy-induction datum before)
    :in-theory (disable acl2::binary-append proof-world-machine proof-world-reg
                        proof-world-pc proof-heap-base proof-pointer-address proof-word-tag
                        sequence-coerce-input-cells-p sequence-car-byte sequence-write-one-byte)
    :do-not '(generalize))
   ("Subgoal *1/1"
    :expand ((sequence-execute nil before)))
   ("Subgoal *1/2"
    :use
    (sequence-coerce-string-step-effects
     (:instance sequence-write-keeps-coerce-input-cells
                (datum (cdr datum))
                (word (proof-load-word
                       (+ 8 (proof-pointer-address (proof-world-reg 4 before)
                                                   (proof-heap-base before)))
                       (proof-world-machine before)))
                (base (proof-heap-base before)) (start (proof-world-reg 1 before))
                (next-start (1+ (proof-world-reg 1 before)))
                (end (+ (proof-world-reg 1 before) (len datum)))
                (write-address (proof-world-reg 1 before)) (byte (char-code (car datum)))
                (memory (boymoo-model::a64-memory (proof-world-machine before)))))
    :expand ((:free (word base start end memory)
                    (sequence-coerce-input-cells-p datum word base start end memory)))))
  :rule-classes nil)

(local
 (defthm sequence-list-byte-writes-keep-outside
   (implies (and (proof-span-p start (len datum))
                 (unsigned-byte-p 64 address)
                 (or (< address start) (<= (+ start (len datum)) address)))
            (equal (boymoo-model::a64-byte address (sequence-write-list-bytes datum start memory))
                   (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :induct (sequence-write-list-bytes datum start memory)
                   :in-theory (disable sequence-write-one-byte)))))

(local
 (defun sequence-bytes-from-memory (count address memory)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       nil
     (cons (boymoo-model::a64-byte address memory)
           (sequence-bytes-from-memory (1- count) (1+ (ifix address)) memory)))))

(local
 (defthm sequence-byte-list-uses-memory
   (equal (proof-byte-list count address machine)
          (sequence-bytes-from-memory count address (boymoo-model::a64-memory machine)))
   :hints (("Goal" :induct (proof-byte-list count address machine)))))

(local
 (defthm sequence-character-code-fits-byte
   (unsigned-byte-p 8 (char-code datum))
   :hints (("Goal" :use ((:instance acl2::completion-of-char-code (acl2::x datum)))))))

(local
 (defthm sequence-written-list-bytes
   (implies (and (proof-span-p address (len datum))
                 (unsigned-byte-p 64 (+ address (len datum))))
            (equal (sequence-bytes-from-memory
                    (len datum) address (sequence-write-list-bytes datum address memory))
                   (sequence-list-bytes datum)))
   :hints (("Goal"
            :induct (sequence-write-list-bytes datum address memory)
            :in-theory (disable sequence-write-one-byte))
           ("Subgoal *1/2"
            :use ((:instance sequence-list-byte-writes-keep-outside
                             (datum (cdr datum)) (start (1+ address))
                             (memory (boymoo-model::a64-write-bytes
                                      1 address (char-code (car datum)) memory)))
                  (:instance sequence-first-byte-of-write
                             (count 1) (start address) (value (char-code (car datum)))))))))

(defthm sequence-coerce-string-copy-source-value
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (path (sequence-coerce-string-copy-path datum))
         (after (sequence-execute path before))
         (address (proof-world-reg 1 before))
         (end (+ address (len datum)))
         (cuts (list (+ 40 (proof-world-pc before)))))
    (implies
     (and (consp datum) (not (eq result-type 'list))
          (not (proof-world-stop before)) (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 2 before) (len datum))
          (unsigned-byte-p 64 end)
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before)))
          (sequence-coerce-input-cells-p datum (proof-world-reg 4 before)
                                        (proof-heap-base before) address end memory)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-value-view (proof-load-string (len datum) address
                                                     (proof-world-machine after)))
                 (boymoo-model::core-primitive 'coerce (list datum result-type) program)))))
  :hints
  (("Goal"
    :in-theory (disable proof-segment-p proof-world-machine proof-world-reg proof-world-pc
                        sequence-coerce-string-copy-path sequence-coerce-input-cells-p
                        sequence-write-list-bytes sequence-core-coerce
                        sequence-byte-characters-of-list-bytes)
    :use
    (sequence-coerce-string-copy-effects sequence-core-coerce
     (:instance sequence-written-list-bytes
                (address (proof-world-reg 1 before))
                (memory (boymoo-model::a64-memory (proof-world-machine before))))
     (:instance sequence-segment-of-instruction-path
                (instructions (sequence-coerce-string-copy-path datum))
                (cuts (list (+ 40 (proof-world-pc before))))
                (after (sequence-execute (sequence-coerce-string-copy-path datum) before))))))
  :rule-classes nil)
