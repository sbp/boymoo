# Integer bounds

`lib` is the tactic library. Terms and Steps use the forms in `prover/sig/proof.md`. A signed difference is `(term step strictp)`, where `strictp` is `t` when `step` proves positivity and `nil` when it proves nonnegativity. Evidence arguments are lists of Steps in the supplied order.

| Call | Result | Failure |
|---|---|---|
| `(b2-bounds-comparison term)` | `(lower upper strictp)` for a strict comparison or its negation, and `nil` for other terms. | Malformed comparison. |
| `(b2-bounds-coefficients term)` | An insertion-ordered alist of `(term . integer)` entries. The key `nil` represents the constant contribution. Entries with zero coefficients are retained. | A failure from reading a malformed term. |
| `(b2-bounds-add-signs lib first second evidence)` | The signed difference obtained from the two signed differences `first` and `second`. | A failure from proof construction. |
| `(b2-bounds-prove-integer-bound lib target evidence)` | The Step proving the comparison term `target`. | `Unproved` when no candidate works, or a failure from proof construction. |
