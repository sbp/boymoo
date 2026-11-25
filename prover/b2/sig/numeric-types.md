# Numeric result types

A Library, term and Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Evidence is an ordered list of Steps. The constants are
`*b2-numeric-types-floor*`, `*b2-numeric-types-truncate*`,
`*b2-numeric-types-characterp*`, `*b2-numeric-types-stringp*`,
`*b2-numeric-types-coerce*`, `*b2-numeric-types-count*`,
`*b2-numeric-types-logrev*`, `*b2-numeric-types-zp*`,
`*b2-numeric-types-the-check*`, `*b2-numeric-types-size*`,
`*b2-numeric-types-i*`, `*b2-numeric-types-j*`, `*b2-numeric-types-types*`, and
`*b2-numeric-types-sums*`. `types` is a set of predicate symbols used for
membership tests. `sums` maps arithmetic operators to lemma names in the order
addition, multiplication, negation.

A `Types` object has the form `(:b2-numeric-types-types lib search visited fuel)`.
`lib` is the current Library, `search` is the Search initialized from the
constructor's Library, `visited` contains active `(predicate value)` keys with
the most recent first, and `fuel` is the remaining type-search budget. Use
`b2-numeric-types-types-init` with a Library to construct the object, and
`b2-numeric-types-types-lib` to read its Library. To make intervening changes
to the shared Library visible to an existing solver, call
`(b2-numeric-types-types-with-library types lib)`. This preserves the Search
index and the type-search budget. The constructor can return a failure while initializing
Search.

Each function below takes the `Types` object first and returns
`(cons value types)` with the resulting object, or a failure as the entire result.
Pass `nil` for the default evidence and `7` for the default depth.

| Call | Arguments and value |
|---|---|
| `(b2-numeric-types-types-prove types predicate value evidence depth)` | Predicate symbol, term, evidence Steps and depth. Step proving the type of the term. |
| `(b2-numeric-types-types-floor types i j)` | Dividend and divisor terms. Step proving the floor quotient integer. |
| `(b2-numeric-types-types-quotient-integer types operation i j)` | Operation symbol, dividend and divisor terms. Step proving the quotient integer. |

Each function below may return a failure as the entire result. `lib` is a
Library, `value`, `i`, `j`, `base`, `exponent`, `left` and `right` are terms,
and `typed`, `above-zero`, `kind`, `above`, `natural`, `natural-left` and
`natural-right` are Steps for the corresponding hypotheses.

| Call | Result |
|---|---|
| `(b2-numeric-types-natural-quotient lib i j)` | `(cons step lib)` proving a natural result of the nonnegative integer quotient. |
| `(b2-numeric-types-fraction-integer lib field value)` | `(cons step lib)` proving the result of the numerator or denominator symbol `field` integer. |
| `(b2-numeric-types-predecessor-natural lib value typed above-zero)` | Step proving the predecessor of the positive integer natural. |
| `(b2-numeric-types-positive-power lib base exponent kind above natural)` | `(cons (list typed positive) lib)` proving integrality and positivity of the power. |
| `(b2-numeric-types-natural-product lib left right natural-left natural-right)` | `(cons step lib)` proving a natural product. |
| `(b2-numeric-types-type-theorem lib formula)` | `(cons step lib)` proving the result type asserted in the formula. |

`(b2-numeric-types-split lib test prove)` joins the Steps returned by a
callback on the true and false assumptions of `test`, in that order. Pass
the callback replies, each `(cons step lib)`, as the list `prove`. If a
reply is missing, the result is `(cons (list :call lib assumption holds) lib)`.
`assumption` is the Step for the current branch and `holds` is its Boolean
sign. The completed result is `(cons step lib)`. Failures from assumptions,
callbacks and joining the cases are returned as the entire result.
