(in-package "BOYMOO-PROOFS")

; The comment before rt:z-shift in compiler/runtime.lisp asks for a
; nonzero integer datum in x0.  The first event below shows why on the
; model: for zero and a positive shift, the view of zero has no limbs,
; and the left-shift loop, which tests its limb counter only after the
; first limb, runs on through memory until a load faults.
;
; The only caller of rt:z-shift is rt:n-ash, which is reached only from
; the entry jet:COMMON-LISP::ASH.  That entry returns at once when x0
; is tagged zero, rt:n-ash returns zero itself when x0 is not an
; integer, and the runtime gives every integer of small magnitude the
; immediate form, so no boxed integer it makes is zero.  The second
; event shows that the entry gives zero for (ash 0 1) and other counts.

(include-book "runtime-examples")

(logic)
(set-verify-guards-eagerness 0)

; X0 holds tagged zero and X1 holds the untagged shift count one.
(defun integer-zero-left-shift-fault ()
  (let ((before (integer-example-world "rt:z-shift" (proof-integer-word 0)
                                       1 nil nil)))
    (mv-let (reason after)
      (proof-run 256 (list *integer-example-return*) before)
      (and (equal reason :fault)
           (equal (proof-world-pc after)
                  (integer-runtime-address "rt:z-shift-left" *integer-example-code-base*))
           (equal (proof-world-reg 27 after) (+ *integer-example-free* 24))))))

(assert-event (integer-zero-left-shift-fault))

; The entry for ASH, given tagged zero and tagged one, returns tagged
; zero, as (ash 0 1) is 0 in core-prelude.
(assert-event
 (and (equal (boymoo-model::core-datum (boymoo-model::core-prelude 'ash (list 0 1)))
             0)
      (integer-check-ash 0 1)
      (integer-check-ash 0 62)
      (integer-check-ash 0 (expt 2 62))))
