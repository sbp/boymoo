# Arithmetic cancellation

`b2-meta-cancel-cancellation-equal-shift` returns a Step paired with the
resulting Cancellation. Multiplicative cancellation can add lemmas in
the common-operand proof. Subsequent steps use the Library in the
returned Cancellation.

`grep -nE b2-meta-cancel-cancellation-equal-shift prover/b2/meta-cancel.lisp` shows the proof operations. The command was run on 2026-11-23.
