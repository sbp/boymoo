# Floor and integer quotient proofs

The Library and Step arguments have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`. A term is a frozen prover datum. `call` is a
term whose head is `*h3-book-floor-floor*`, the symbol datum for
`COMMON-LISP::FLOOR`, and whose other fields are the two arguments to
`FLOOR`. An interval is a list of the integer, lower bound and upper
bound Steps, in that order. A prime on `library` below denotes the
Library after any auxiliary proofs have been added. Its facts and entries
retain insertion order. A failure is the entire result.

| Call | Result | Failure |
|---|---|---|
| `(h3-book-floor-conjunction terms)` | Right-nested conjunction of the term list, with its last term as the final branch. | A failure for an empty list. |
| `(h3-book-floor-conjunct-proof library proofs)` | Step for the conjunction of the first literals of the Steps in `proofs`, in their given order. | A failure from reading the Steps or deriving the conjunction. |
| `(h3-book-floor-natural-measure term)` | The term `(IF (NATP term) term '0)`. | None. |
| `(h3-book-floor-measure-ordinal library term)` | Ordinality Step for the natural measure of `term`. | A failure from proof construction. |
| `(h3-book-floor-natural-decrease library new old new-int old-int new-bound old-bound strict)` | Ordinal decrease Step from the integer Steps for `new` and `old`, their nonnegative bounds and the strict bound `new < old`. | A failure from proof construction. |
| `(h3-book-floor-times-successor library d count divisor-number)` | Step distributing `(1 + count) * d`, using the Step that `d` is an ACL2 number. | A failure from proof construction. |
| `(h3-book-floor-floor-ratio i j)` | The term `i * (UNARY-/ j)`. | None. |
| `(h3-book-floor-change-interval-value library interval equality)` | The interval with the compared value rewritten using `equality`. | A failure from proof construction. |
| `(h3-book-floor-floor-default library call not-rational)` | Equality Step of `call` to zero from the Step that its ratio is not rational. | A failure from proof construction. |
| `(h3-book-floor-exact-floor library call ratio-integer)` | Step equating `call` to its ratio, given the ratio's integer Step. | A failure from proof construction. |
| `(h3-book-floor-ratio-by-one library term numeric)` | Step equating the floor ratio with divisor one to `term`, given its numeric Step. | A failure from proof construction. |
| `(h3-book-floor-floor-zero-by-argument library call absent)` | Step equating `call` to zero. `absent` is a nonnumeric-factor Step or `nil` for the default. | A failure from proof construction or missing evidence. Returns an `unproved` failure if the evidence is for neither factor. |
| `(h3-book-floor-noncomplex-type library rational)` | Noncomplex Step for the term of the given rational Step. | A failure from proof construction. |
| `(h3-book-floor-nonnumeric-given-noncomplex library not-complex not-rational)` | Nonnumeric Step for the term proved noncomplex and nonrational by the given Steps. | A failure from proof construction. |
| `(h3-book-floor-floor-through-ratio library call)` | Step equating `call` to `FLOOR` of its ratio with divisor one. | A failure from proof construction. |
| `(h3-book-floor-floor-nonrational-argument library goal not-rational)` | Step for the mixed-argument floor `goal` using the given nonrational Step. | A failure from proof construction. |

To evaluate the Boolean callbacks in order and carry their Library updates,
use the three stages of `equivalent-booleans`. First call
`(h3-book-floor-equivalent-booleans-start library p)` and obtain
`(cons (list yes p-value) library')`. Evaluate the forward callback on
`yes` with that Library. Then call
`(h3-book-floor-equivalent-booleans-positive library p-value forward)`
with the resulting Library and forward Step to get
`(cons positive library')`. With that Library, construct `no` by assuming
`p` false, assume `q` true and evaluate the backward callback on that
assumption. Finally call
`(h3-book-floor-equivalent-booleans-finish library p q positive no backward)`
with the last Library and all five remaining arguments to get the final
Step. Every stage can return a failure from proof construction in place of
its listed result.

The `-with-library` forms of `integer-gap`, `same-floor-interval`,
`strict-from-weak`, `floor-bounds`, `floor-is-integer`,
`equivalent-booleans`, `equivalent-booleans-start`,
`equivalent-booleans-positive` and `floor-theorem` take the same arguments
as the calls above. They return `(cons result library')` on every path.
When `result` is a failure, the Library contains the auxiliary lemmas
registered before the failure. A dispatcher that catches `unproved` uses
`h3-book-floor-floor-theorem-with-library`.
