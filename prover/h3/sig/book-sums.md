# Additive normalization

A Library, a term and a Step have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`. A book sum context has the form
`(:h3-book-sums library types search)`, where `types` is the Search for numeric types
and `search` is the Search for book sum normalization. Use
`h3-book-sums-book-sums-init` to construct it and
`h3-book-sums-book-sums-lib`, `h3-book-sums-book-sums-types` and
`h3-book-sums-book-sums-search` to read its fields. Evidence is a list of
Steps in argument order. A normal-form argument called `source` or `target`
is an equality Step. The four-operand table `numeric` is an alist from
operand terms to their numeric Steps, in order of first occurrence.

| Call | Result |
|---|---|
| `(h3-book-sums-lemmas library)` | Library with the additive lemmas, in the order of their registration. |
| `(h3-book-sums-book-sums-init library)` | A book sum context for the given Library. |
| `(h3-book-sums-book-sums-type-of sums term evidence)` | Step proving the term numeric. |
| `(h3-book-sums-book-sums-constant sums term)` | Primitive evaluation Step, or nil when there is none. |
| `(h3-book-sums-book-sums-push-minus n sums term evidence)` | Step distributing negation, or nil when there is no change. The initial fuel is 1000000. |
| `(h3-book-sums-book-sums-prepare sums term evidence)` | Step equating the term with its sum with numeric fixes inserted. |
| `(h3-book-sums-book-sums-linear-form sums term evidence)` | Step equating the term with its sorted, right-associated sum. |
| `(h3-book-sums-book-sums-linear-equal sums left right evidence)` | Step equating terms with the same linear normal form. |
| `(h3-book-sums-book-sums-sum-form sums term evidence)` | Step equating the term with its normal form after inserting numeric fixes. |
| `(h3-book-sums-add-cancellation library term offset)` | Step cancelling the addend `offset` against its negation in the sum with `term`. |
| `(h3-book-sums-cancel-addend library equality first second offset)` | Step cancelling the common addend `offset` in `equality`, with terms `first` and `second` remaining. |
| `(h3-book-sums-inverse-unique library term other sum-zero)` | Step proving the fixed inverse of `term` from the supplied zero-sum Step. |
| `(h3-book-sums-cancel-comparison library sums p q evidence)` | Step equating comparisons with the same additive difference. |
| `(h3-book-sums-cancel-equalities library sums p q evidence)` | Step equating two equality terms whose differences agree up to sign. |
| `(h3-book-sums-cancel-equalities-transfer step source target library numeric)` | Step transferring an equality proof from its source difference to a target difference. |
| `(h3-book-sums-cancel-equalities-forward step library numeric left right reversep)` | Step transferring the proof of the first equality to the second. |
| `(h3-book-sums-cancel-equalities-backward step library numeric left right reversep)` | Step transferring the proof of the second equality to the first. |
| `(h3-book-sums-conditional-equality library sums p rhs evidence)` | Step equating the equality `p` to a conditional with false alternative. |
| `(h3-book-sums-additive-has-shape formula)` | Boolean recognizing the additive equality and comparison forms. |
| `(h3-book-sums-additive-theorem library formula)` | `(cons step library)` with the additive proof and its Library. The Step is nil when the formula has no additive shape. |
| `(h3-book-sums-additive-theorem-with-library library formula)` | `(cons result library)` with the same Step or nil as the main entry point. If proof construction fails after registering lemmas, `result` contains the failure and the Library retains those lemmas. Use this form when catching the failure and continuing with the Library. |

The field accessors do not produce a failure. Every other entry can return a failure
as its entire result, except for the stated pair from
`h3-book-sums-additive-theorem-with-library`. The constants are
`*h3-book-sums-prefix*`, `*h3-book-sums-add*`, `*h3-book-sums-add-inv*`,
`*h3-book-sums-fixed*`, `*h3-book-sums-double*` and `*h3-book-sums-negate*`.
