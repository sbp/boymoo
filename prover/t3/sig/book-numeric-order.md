# Comparison laws for ACL2 objects

`lib` is a Library. Terms and Steps have the forms in `prover/sig/proof.md`.
`*t3-book-numeric-order-fix*` is the ACL2 symbol `FIX`. A `numeric sums context`
object `sums` is `(:number-sums lib)`. It uses the prefix `T3-NUMBER-`
for its additive and typed order lemmas.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-numeric-order-number-sums-type-of sums term evidence)` | A Step establishing that `term` is a number, using the first matching Step in ordered list `evidence` if present. Pass `nil` for empty evidence. | `Unsupported` if there is no numeric recipe, or a failure from constructing the Step. |
| `(t3-book-numeric-order-number-sums-number-type sums term types)` | A number Step for `term` using the ordered list `types`, with the same lookup as `type-of`. | A failure from `type-of`. |
| `(t3-book-numeric-order-select lib equation evidence)` | A Step chaining equality Step `equation` with normalization of its right side. `evidence` is the ordered list of Steps. | A failure from normalization or proof construction. |
| `(t3-book-numeric-order-fixed-comparison lib sums)` | The Library with numeric fixation, addition, negation, and strict comparison lemmas in that order. | A failure from constructing or adding a lemma. |
| `(t3-book-numeric-order-fixed-comparison-added has-a has-b lib sums a b fx fy)` | A Step comparing the sums of `X` and `Y` and of terms `fx` and `fy` under the signed number tests `a` and `b`. The Boolean arguments choose the signs. | A failure from proof construction. |
| `(t3-book-numeric-order-typed-order lib sums types)` | The Library with the typed strict-to-weak implication and mixed order composition. `types` is the ordered list of number Steps for `X`, `Y`, and `Z`. | A failure from constructing or adding a lemma. |
| `(t3-book-numeric-order-with-fixed lib step reverse)` | A comparison Step with `FIX` applied to both operands, or removed when Boolean `reverse` is true. | A failure from reading or rewriting the comparison. |
| `(t3-book-numeric-order-build lib)` | The Library with the typed and arbitrary-object order laws in proof order. | A failure from constructing or adding a lemma. |
