(in-package "BOYMOO-PROOFS")

(include-book "source")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-instruction-path (instructions cuts world)
  (declare (xargs :hints (("Goal" :in-theory (disable proof-instruction-effect)))))
  (if (endp instructions)
      t
    (let ((instruction (car instructions)))
      (and (not (proof-world-stop world))
           (not (member-equal (proof-world-pc world) cuts))
           (proof-instruction-at-p instruction (proof-world-pc world) world)
           (proof-instruction-access-p instruction world)
           (sequence-instruction-path (cdr instructions) cuts
                                      (proof-instruction-effect instruction world))))))

(defun sequence-execute (instructions world)
  (declare (xargs :hints (("Goal" :in-theory (disable proof-instruction-effect)))))
  (if (endp instructions)
      world
    (sequence-execute (cdr instructions)
                      (proof-instruction-effect (car instructions) world))))

(defthm sequence-run-of-instruction-path
  (implies (sequence-instruction-path instructions cuts world)
           (equal (proof-run (+ (len instructions) (nfix fuel)) cuts world)
                  (proof-run fuel cuts (sequence-execute instructions world))))
  :hints (("Goal" :induct (sequence-instruction-path instructions cuts world)
                  :in-theory (disable proof-step proof-instruction-at-p
                                      proof-instruction-access-p
                                      proof-instruction-effect
                                      proof-world-stop proof-world-pc))))

(defthm sequence-segment-of-instruction-path
  (implies (and (sequence-instruction-path instructions cuts before)
                (equal after (sequence-execute instructions before))
                (not (proof-world-stop after))
                (member-equal (proof-world-pc after) cuts))
           (proof-segment-p (len instructions) cuts before :cut after))
  :rule-classes nil
  :hints (("Goal" :use ((:instance sequence-run-of-instruction-path
                                   (world before) (fuel 0)))
                  :in-theory (disable proof-step sequence-execute
                                      sequence-instruction-path
                                      sequence-run-of-instruction-path))))

(defthm sequence-run-append-at-noncut
  (implies (and (natp prefix) (natp suffix)
                (equal (proof-run prefix cuts before) (mv :limit middle)))
           (equal (proof-run (+ prefix suffix) cuts before)
                  (proof-run suffix cuts middle)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-run prefix cuts before)
                  :in-theory (disable proof-step))))

; The fixed Linux system and runtime items supply the offsets and bytes used in
; the instruction paths. The program entry and static data labels close the image.
(defconst *sequence-items*
  (append (boymoo-compiler::linux-system-code)
          (boymoo-compiler::runtime-code)
          '((:label "rt:entry") (:ret) (:label "data:static"))))

(defconst *sequence-labels*
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout *sequence-items* 0 nil nil)
    (declare (ignore end reversed))
    labels))

(defconst *sequence-bytes*
  (mv-let (bytes entry)
    (boymoo-compiler::a64-assemble *sequence-items* "os:main")
    (declare (ignore entry))
    bytes))

(defun sequence-offset (label)
  (boymoo-compiler::a64-offset label *sequence-labels*))

(defun sequence-decoded-instructions (count pc)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (disable proof-decode)))))
  (if (zp count)
      nil
    (let ((word (+ (char-code (char *sequence-bytes* pc))
                   (ash (char-code (char *sequence-bytes* (+ 1 pc))) 8)
                   (ash (char-code (char *sequence-bytes* (+ 2 pc))) 16)
                   (ash (char-code (char *sequence-bytes* (+ 3 pc))) 24))))
      (cons (proof-decode word)
            (sequence-decoded-instructions (1- count) (+ pc 4))))))

(defun sequence-instructions (slices)
  (if (endp slices)
      nil
    (let* ((slice (car slices))
           (pc (+ (sequence-offset (car slice)) (* 4 (cadr slice)))))
      (append (sequence-decoded-instructions (caddr slice) pc)
              (sequence-instructions (cdr slices))))))

(defmacro sequence-defpath (name &rest slices)
  `(defconst ,name (sequence-instructions ',slices)))

(in-theory (disable proof-run proof-step proof-instruction-at-p
                    proof-instruction-access-p proof-instruction-effect
                    sequence-instruction-path sequence-execute
                    sequence-offset sequence-decoded-instructions
                    sequence-instructions))
