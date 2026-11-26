(in-package "BOYMOO-PROOFS")

(include-book "boxed-scratch")

(logic)
(set-verify-guards-eagerness 0)

; The checked path taken by a numeric projection depends only on whether
; its argument word is an immediate integer.
(defund p6-numeric-projection-sites (name world)
  (if (oddp (proof-world-reg 0 world))
      (p6-immediate-numeric-sites name)
    (p6-boxed-numeric-sites name world)))

; Code placement for the selected path, and for a boxed argument, room
; for the 16-byte save in the machine-stack reservation.
(defund p6-numeric-projection-pre-p (name base world)
  (if (oddp (proof-world-reg 0 world))
      (and (member-equal name *p6-numeric-projections*)
           (p6-path-entry-p (p6-immediate-numeric-sites name) base world))
    (and (p6-boxed-numeric-pre-p name base world)
         (p6-machine-save-room-p world))))

(defthm p6-numeric-projections-runtime-contract
  (let* ((sites (p6-numeric-projection-sites name world))
         (after (p6-path-end sites world))
         (args (list value)))
    (implies (and (p6-numeric-projection-pre-p name runtime-base world)
                  (proof-runtime-pre-p name args program labels code-base world objects packages))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-numeric-projection-sites p6-numeric-projection-pre-p)
                           (proof-segment-p proof-runtime-return-p proof-runtime-pre-p
                            p6-boxed-numeric-pre-p p6-path-entry-p p6-machine-save-room-p))
           :cases ((oddp (proof-world-reg 0 world)))
           :use (p6-immediate-numeric-projections-runtime-contract
                 p6-boxed-numeric-projections-runtime-contract-with-room))))
