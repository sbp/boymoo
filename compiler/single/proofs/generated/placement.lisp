(in-package "BOYMOO-PROOFS")

(include-book "registers")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-instruction-at-p proof-instruction-access-p
                    proof-decode-at proof-decode proof-covered-p proof-fetchable-p
                    proof-world-regions proof-world-machine
                    boymoo-model::a64-execute boymoo-model::a64-read-bytes))

(defthm generated-fetch-of-register-updates
  (and (equal (proof-instruction-at-p instruction address (generated-set-pc pc world))
              (proof-instruction-at-p instruction address world))
       (equal (proof-instruction-at-p instruction address (generated-set-reg register value world))
              (proof-instruction-at-p instruction address world))
       (equal (proof-instruction-at-p instruction address (generated-set-sp sp world))
              (proof-instruction-at-p instruction address world))
       (equal (proof-instruction-at-p instruction address (generated-set-flags flags world))
              (proof-instruction-at-p instruction address world)))
  :hints (("Goal" :in-theory (enable proof-instruction-at-p proof-decode-at proof-fetchable-p))))

(defthm generated-placement-at-first-instruction
  (implies (and (consp instructions) (proof-instructions-at-p instructions address world))
           (proof-instruction-at-p (car instructions) address world)))

(defthm generated-instruction-access-for-control
  (and (proof-instruction-access-p (list :branch delta link) world)
       (proof-instruction-access-p (list :branch-cond delta cond) world)
       (proof-instruction-access-p '(:branch-reg 30 nil) world)
       (proof-instruction-access-p (list :arithmetic-imm op width rd rn value) world)
       (proof-instruction-access-p (list :arithmetic-reg op width rd rn rm 0 0) world)
       (proof-instruction-access-p (list :logical-reg op width rd rn rm 0 0 nil) world)
       (proof-instruction-access-p (list :logical-imm op width rd rn value) world)
       (proof-instruction-access-p (list :move-wide op width rd value shift) world))
  :hints (("Goal" :in-theory (enable proof-instruction-access-p))))

(defthm generated-one-instruction-segment
  (let ((after (proof-instruction-effect instruction before)))
    (implies (and (generated-instruction-p instruction before)
                  (not (proof-world-stop after))
                  (not (member-equal (proof-world-pc before) cuts))
                  (member-equal (proof-world-pc after) cuts))
             (proof-segment-p 1 cuts before :cut after)))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions (list instruction)))
                  :in-theory (disable proof-segment-p proof-instruction-effect))))

; The linked instruction has the decoding of the assembler item at its image offset.
(defun generated-linked-item-p (item instruction address base labels world)
  (and (proof-instruction-at-p instruction address world)
       (equal (proof-decode (boymoo-compiler::a64-word item (- address base) labels))
              instruction)))
