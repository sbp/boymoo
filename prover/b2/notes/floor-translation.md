# Floor translation

Quotient translation proves that the proposed and original quotients
are the same integer by comparing their bounds against a common ratio.
The rational-type solver carries the Library with any type lemmas added
while establishing those bounds.

`grep -nE 'b2-floor-translation-(unique-integer|rational-type)' prover/b2/floor-translation.lisp` shows the proof operations. The command was run on 2026-11-23.
