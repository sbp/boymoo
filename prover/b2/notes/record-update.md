# Record order

`b2-record-update-smaller` proves `(<< b a)` using evidence of
`(NOT (EQUAL a b))` and `(NOT (<< a b))`. The record code uses the
same case request and reply operations for record law and extensionality
proofs.

`grep -nE 'b2-record-update-(smaller|case-request|case-resume)' prover/b2/record-update.lisp prover/b2/record-extensionality.lisp` shows the proof operations. The command was run on 2026-11-23.
