# Pathname measures

Terms, Steps, Libraries, and Calls have the forms specified in
`prover/sig/proof.md`, `prover/sig/library.md`, and `prover/sig/termination.md`.
The Library supplies B2 tactics. Evidence is a list of Steps in the order
supplied by the caller.

The term constants are `*b2-pathnames-length*`, `*b2-pathnames-stringp*`,
`*b2-pathnames-subseq*`, `*b2-pathnames-take*`, `*b2-pathnames-zp*`,
`*b2-pathnames-string*`, `*b2-pathnames-list*`, `*b2-pathnames-cancel*`,
`*b2-pathnames-parent*`, and `*b2-pathnames-merge*`. The STRING and LIST
constants are quoted symbols.

| ACL2 call | Result | Failure |
|---|---|---|
| `(b2-pathnames-length term)` | A call of LENGTH on the given term. | — |
| `(b2-pathnames-path-plan definitions)` | A map of names to measure terms with `(name . measure)` entries in CANCEL, PARENT, MERGE order. Each definition is `(name formals body)`. | Missing definition or unexpected number of formals. |
| `(b2-pathnames-support-length lib)` | The Library after adding the LENGTH and TAKE support lemmas, if needed. | Failure from proof construction |
| `(b2-pathnames-support-take lib)` | The Library after adding LENGTH-TAKE. | Failure from proof construction |
| `(b2-pathnames-path-ordinal lib measure)` | `(cons step lib)` with a proof of ordinality for the measure term and the Library with its support lemmas. | Failure from proof construction or fuel exhaustion |
| `(b2-pathnames-length-terms term)` | List of LENGTH calls, in the order yielded during traversal of the term. | — |

A PathComparison has the form
`(:b2-pathnames-pathcomparison lib goal facts naturals types)`.
`goal` is the measure comparison term, `facts` is the insertion-ordered
map from evidence literals to Steps, and `naturals` is the map from LENGTH
terms to naturality Steps ordered by the terms' written form. Both maps
use `(term . step)` entries. The integer evidence `types` starts with
the lengths in `naturals` order, then the naturality evidence in `facts`
order, then the integer evidence in `facts` order.

| ACL2 call | Result |
|---|---|
| `(b2-pathnames-pathcomparison-init lib goal evidence)` | A PathComparison with the evidence collected and the length sources sorted. |
| `(b2-pathnames-pathcomparison-require self term)` | The evidence Step for the requested term, or Unproved if it is absent. |
| `(b2-pathnames-pathcomparison-at-least-zero self term)` | A Step proving that the requested term is nonnegative. |
| `(b2-pathnames-pathcomparison-integer self term)` | A Step proving that the requested term is an integer. |
| `(b2-pathnames-pathcomparison-suffix-length self term)` | The length equality Step for a LENGTH term whose operand is a SUBSEQ call. |
| `(b2-pathnames-pathcomparison-additive-bound self call after before)` | A Step proving a positive difference for the Call and the given after and before measures. |
| `(b2-pathnames-pathcomparison-prove self call)` | The Step proving the PathComparison goal for the Call. |

Each PathComparison constructor or operation in the table can return a failure
as its entire result. Its five accessors have the names
`b2-pathnames-pathcomparison-lib`, `b2-pathnames-pathcomparison-goal`,
`b2-pathnames-pathcomparison-facts`, `b2-pathnames-pathcomparison-naturals`,
and `b2-pathnames-pathcomparison-types`. Each takes the PathComparison and
returns the corresponding field.
