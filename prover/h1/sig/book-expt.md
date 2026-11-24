# Powers with a shared exponent

`proof` is the H1 Prover described in `tactics.md`, and `normalizer` is
the Algebra from `book-arithmetic.md`. Terms and Steps use the forms in
`prover/sig/proof.md`. A signed test is `(term holds)` with `t` or `nil` in
the second field. This book defines no classes.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-expt-base-factors term)` | The immediate or recursively exposed base factors in depth-first, left-to-right order. Repeated factors remain in the list. | — for prover terms. |
| `(h1-book-expt-open-power proof term normalizer)` | `(cons step normalizer)` with the unfolded power equation and the resulting Algebra. | A failure in place of the pair, including `Unproved` for an unresolved test. |
| `(h1-book-expt-unfold-powers proof term powers normalizer)` | `(cons step normalizer)` with the equation obtained by unfolding the listed powers in `term` in list order and the resulting Algebra. | A failure in place of the pair. |
| `(h1-book-expt-power-equality proof formula)` | `(cons step proof)` with the induction Step and the resulting Prover. The tactic can add the signed countdown lemmas. | A failed tactic puts its failure in the step position so the caller can retain the Prover. |
| `(h1-book-expt-install-powers proof)` | The resulting Prover with the power lemmas and rules installed in order. | A failure in place of the Prover. |

`*h1-book-expt-numeric-equal*` is the prover symbol `COMMON-LISP::=`.
Power terms use the `EXPT` symbol `*h1-arithmetic-expt*`. Distinct powers and distinct
base factors are collected in order of first occurrence. The exponent
set is used only when it has one member.

| Additional call | Result |
|---|---|
| `(h1-book-expt-signed-countdowns proof exponent)` | `(cons (list measure countdowns) proof)` after supplying the arithmetic method replies. A failure occupies the value position. Each countdown is `(bindings step)`, with the down case before the up case. |
| `(h1-book-expt-find normalizer term)` | `(cons step normalizer)` with the Step or `nil` from the Algebra's Context and the resulting Algebra, or a failure in place of the pair. |
| `(h1-book-expt-checked-pair result)` | The failure if `result` is a failure or its first field is a failure, and `result` otherwise. |
