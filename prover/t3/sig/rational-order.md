# Rational addition and order

Terms, Steps and Libraries have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. `types` and `evidence` are ordered lists of Steps. Pass `nil` for omitted evidence.

A rational sums context object has the form `(:t3-rational-sums library prefix)`.
Use `t3-rational-order-rational-sums-init` to construct it and
`t3-rational-order-rational-sums-lib` to read its Library. The prefix is
`"T3-RAT-"` for rational sums context and `"T3-NUMBER-"` for the numeric sums context specialization.
`t3-rational-order-make-rational-sums` takes the Library and the specialization's
prefix. `t3-rational-order-rational-sums-with-lib` takes a sums object and a
replacement Library. 
The names in `*t3-rational-order-rational-sums-additive-lemmas*` are in
lexicographic order. The `cite` operation uses the supplied evidence Steps in order. Every proof operation in the table can return a failure.
A failure replaces the entire result, including when the listed result is a pair.

| Call | Result |
|---|---|
| `(t3-rational-order-rational term)` | The proposition that `term` is rational. |
| `(t3-rational-order-rational-sums-cite sums name arguments evidence)` | A cited Step, using the sums prefix when `name` denotes an additive lemma. |
| `(t3-rational-order-rational-sums-type-of sums term evidence)` | A Step proving the rational or numeric type of `term`, according to the specialization. |
| `(t3-rational-order-rational-sums-number-type sums term types)` | A Step proving that `term` is an ACL2 number. |
| `(t3-rational-order-rational-sums-inverse-unique sums term inverse cancel types)` | A Step equating `inverse` and the unary minus of `term` when `cancel` proves `term + inverse = 0`. |
| `(t3-rational-order-rational-sums-push-minus n sums term evidence)` | A Step distributing unary minus over sums and removing double negatives, or `nil` if unchanged. Pass `1000000` for the initial fuel `n`. |
| `(t3-rational-order-rational-sums-linear-form sums term evidence)` | A Step equating `term` to its ordered additive normal form. |
| `(t3-rational-order-rational-sums-linear-equal sums left right types)` | A Step proving equality by additive normalization. |
| `(t3-rational-order-rational-sums-comparison sums a b types)` | A Step equating `a < b` with positivity of `b - a`. |
| `(t3-rational-order-additive-identities lib sums types)` | The Library extended by the six additive, multiplicative identity and comparison lemmas. |
| `(t3-rational-order-positive-sum lib sums types)` | The Library extended by the positivity lemma for the sum of a positive and a nonnegative value. |
| `(t3-rational-order-weak-then-strict lib sums types)` | The Library extended by the weak-then-strict transitivity lemma. |
| `(t3-rational-order-scaled-difference lib sums types)` | A Step relating the scaled difference to the difference of the scaled values. |
| `(t3-rational-order-strict-scale lib sums types)` | The Library extended by the strict comparison lemma for positive rational scaling. |
| `(t3-rational-order-opposite-sign lib sums value types)` | A Step equating negativity of `value` with positivity of its additive inverse. |
| `(t3-rational-order-zero-from-bounds lib sums value lower upper types)` | A Step equating `value` to zero, given its lower and upper bounds at zero. |
| `(t3-rational-order-nonnegative-from-positive lib sums proof types)` | A nonnegativity Step from the positive comparison Step `proof`. |
| `(t3-rational-order-nonzero-from-positive lib proof)` | A disequality to zero from the positive comparison Step `proof`. |
| `(t3-rational-order-weak-scale lib)` | The Library with the weak comparison lemma for positive rational scaling available. |
| `(t3-rational-order-reflect-scale lib order low high factor types factor-positive)` | `(cons step lib)` with the Library after `weak-scale` and a Step transferring strict `order` from the scaled terms to `low < high`. |
| `(t3-rational-order-ratio-parts lib term rat)` | Three Steps for integrality of the numerator, integrality of the denominator and positivity of the denominator, in that order. `rat` proves `term` rational. |
| `(t3-rational-order-ratio-identity lib sums types)` | The Library extended by the numerator identity. |
| `(t3-rational-order-build lib)` | The Library after adding the rational order recipes in source order. |

Use `(t3-rational-order-rational-sums-with-lib sums lib)` after an operation
returns a new Library held by `sums`. The proof recipes that take both `lib`
and `sums` accept the Library being extended as their first argument.

The numeric sums context representation `(:number-sums lib)` also supplies the
`"T3-NUMBER-"` specialization to these same functions.
`(t3-rational-order-rational-sums-prefix sums)` returns the selected prefix.
