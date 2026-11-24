# Parity and half-integer shifts

`library` is the Library in `prover/sig/library.md`. Terms and Steps have the
forms in `prover/sig/proof.md`. The Signs object has the form specified in
`prover/h3/sig/book-signs.md`. `name` is the theorem's unqualified name string.

Each function returns `(cons value library)`, with the auxiliary lemmas in
the resulting Library in insertion order. A failure from proof construction or
term access is the entire result.

| Call | Arguments and value |
|---|---|
| `(h3-book-parity-two-sign library)` | The four-element list `(integer rational signs inverse)` for the quoted integer two. `integer` and `rational` prove its integrality and rationality, `signs` is its Signs object, and `inverse` is its multiplicative inverse Step. |
| `(h3-book-parity-half-offset library rational double fractional)` | `rational` proves that a term is rational, `double` proves that twice the term is integral, and `fractional` proves that the term is nonintegral. The value is a Step equating the term to one half plus its integer offset. |
| `(h3-book-parity-half-reconstruction library term integer)` | `term` is a product representing half of the integer in the Step `integer`. The value is a Step equating twice `term` with that integer. |
| `(h3-book-parity-parity-theorem library name formula)` | `formula` is a prover term. The value is the Step for the selected parity tactic, or `nil` if the tactic declines. |

Each call has a `-with-library` form with the same arguments and the same
successful result. It returns `(cons failure library)` on failure, preserving
the auxiliary lemmas added before the failure. A dispatcher that retries after
`Unproved` uses `h3-book-parity-parity-theorem-with-library`.
