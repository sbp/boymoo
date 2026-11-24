# Decimal capacity

`lib` is a Library with the T3 proof rules for its dispatch tag. Terms and Steps
use the forms in `prover/sig/proof.md`. A type pair is a list of two Steps,
for integrality and positivity in that order. `upper` is `t` for the floor
interval proof and `nil` for the decrease-only proof. A failure is
the entire result.

| Call | Result | Failure |
|---|---|---|
| `(t3-digit-capacity-capacity argument)` | Decimal capacity call on term `argument`. | None. |
| `(t3-digit-capacity-capacity-branch lib argument test)` | Step unfolding that capacity call and selecting the branch under evidence Step `test`. | A failure from constructing the proof. |
| `(t3-digit-capacity-capacity-type lib term)` | Type pair for the capacity of `term`. | A failure from citing or splitting the capacity type lemma. |
| `(t3-digit-capacity-capacity-one lib term typed)` | Step bounding the capacity of `term` below by 1, given type pair `typed`. | A failure from constructing the proof. |
| `(t3-digit-capacity-capacity-fold lib)` | Library with the capacity definition and its type lemma. | A failure from constructing or adding a definition or lemma. |
| `(t3-digit-capacity-capacity-append-lemma lib)` | Library with the lemma expressing capacity of append as a product. | A failure from constructing or adding the lemma. |
| `(t3-digit-capacity-multiply-weak lib order factor types factor-positive)` | Pair `(cons step lib)` with the scaled weak comparison and Library, including the weak scaling lemma if added. `order` and `factor-positive` are Steps, `factor` is a term, and `types` is a list of numeric type Steps. | A failure from constructing or adding a proof. |
| `(t3-digit-capacity-append-capacity lib left right right-type)` | Pair `(cons step lib)` with the weak lower bound on the capacity of appending terms `left` and `right`, and the resulting Library. `right-type` is the type pair for the capacity of `right`. | A failure from constructing or adding a proof. |
| `(t3-digit-capacity-known-print-base lib radix)` | Step for the validity of radix term `radix` as a print base. | A failure from constructing the proof. |
| `(t3-digit-capacity-floor-interval lib upper)` | Library with the floor interval or decrease lemma and any supporting lemmas constructed for it. | A failure from constructing or adding a proof. |
| `(t3-digit-capacity-digit-character lib)` | Library with the lemma that the digit conversion returns a character. | A failure from constructing or adding the lemma. |
| `(t3-digit-capacity-expansion-comparison n ans value)` | Weak capacity comparison term for counter `n`, accumulator `ans` and expansion `value`. | None. |
| `(t3-digit-capacity-expansion-claim n ans value)` | Term stating the character-list and capacity properties of that expansion. | None. |
| `(t3-digit-capacity-base-capacity lib value tests ten ix nonnegative char-ans)` | Two Steps for the character list and bound in the base case. `tests` is a list of signed terms and the last four arguments are Steps. | A failure from constructing the proof. |
| `(t3-digit-capacity-grown-capacity lib part suffix next-ans next-value n-type q-type upper ih-bound)` | Pair `(cons step lib)` with the bound transferred through the extra digit and the resulting Library. `part`, `suffix`, `next-ans` and `next-value` are terms, then four Steps follow. | A failure from constructing or adding a proof. |
| `(t3-digit-capacity-explode-bound lib)` | Library with the decimal expansion lemma and the supporting lemmas added in leaf order. | A failure from constructing or adding a proof. |
| `(t3-digit-capacity-decimal-expansion lib counter natural)` | List of two Steps, for the character list and the lower bound of the decimal expansion of term `counter`, given Step `natural`. | A failure from constructing the proof. |
| `(t3-digit-capacity-build lib)` | Library with the floor, capacity, append, digit and decimal expansion lemmas in that order. | A failure from constructing or adding a proof. |

`*t3-digit-capacity-ten*` is the quotation of 10.
`*t3-digit-capacity-capacity*`, `*t3-digit-capacity-explode*`,
`*t3-digit-capacity-digit*` and `*t3-digit-capacity-floor*` are prover
symbols.

`(t3-digit-capacity-explode-bound-leaf value tests lib formula template ix nonnegative ten char-ans substitutions)`
returns `((step substitutions) . lib)` or a failure. `value` is one leaf
term, `tests` is its signed branch tests, `formula` is the expansion
claim, and `template` is that claim with the expansion replaced by the
result slot. The next four arguments are the integer, nonnegativity,
print-base and character-list Steps. The substitutions list is extended
at each recursive leaf in traversal order.
