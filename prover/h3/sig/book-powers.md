# Proofs about powers

`lib` is the Library in `prover/sig/library.md`. Terms and Steps have the
forms in `prover/sig/proof.md`. A numeric, rational, integer, positive,
nonnegative, nonzero or negative Step proves the corresponding property
of its term. Evidence lists are read in their supplied order.
In a result `(cons value lib)`, the returned Library contains auxiliary
entries in the order they were added. A failure takes the place of the
entire result. `power` does not produce a failure. All other calls may fail from
term access, proof construction or proof search.

| Call | Result |
|---|---|
| `(h3-book-powers-power base index)` | The power term with base term `base` and exponent term `index`. |
| `(h3-book-powers-power-equation lib term value evidence)` | Equality Step reducing the power call `term` to term `value` using the list of evidence Steps. Returns an `unproved` failure if there is no reduction. |
| `(h3-book-powers-unit-index-power lib base nonzero)` | Equality Step reducing the first power of the base to its numeric fix, given numeric and nonzero Steps for the base. |
| `(h3-book-powers-predecessor-equation lib base nonzero index-integer index-positive)` | `(cons step lib)` with the recurrence for a positive exponent, given the base's numeric and nonzero Steps and the exponent's integer and positive Steps. |
| `(h3-book-powers-nonnegative-integer lib integer positive)` | Nonnegative Step for the term of the given integer and positive Steps. |
| `(h3-book-powers-decrease-index lib integer nonnegative positive)` | `(cons (list whole lower descent) lib)` with the predecessor's integer and nonnegative Steps and the strict decrease of the natural measure, given the index's integer, nonnegative and positive Steps. |
| `(h3-book-powers-positive-index lib whole nonnegative nonzero)` | `(cons step lib)` with the exponent's positive Step, given its integer, nonnegative and nonzero Steps. The nonzero Step denies equality of the index to zero. |
| `(h3-book-powers-power-guard base indices)` | Conjunction of the base term's numeric and nonzero properties and the integrality of each term in `indices`, in list order. |
| `(h3-book-powers-positive-base lib rational positive)` | `(cons (list numeric nonzero) lib)` with the numeric and nonzero Steps for the term of the given rational and positive Steps. |
| `(h3-book-powers-integral-power-natural lib base index nonnegative)` | `(cons step lib)` proving the power integer, given integer Steps for the base and exponent and the exponent's nonnegative Step. |
| `(h3-book-powers-natural-power lib base positive index nonnegative)` | `(cons (list integral positive) lib)` with both power Steps, given the base's integer and positive Steps and the exponent's integer and nonnegative Steps. |
| `(h3-book-powers-rational-power lib base exponent)` | Rationality Step for the power of the term in rational Step `base` and exponent term `exponent`. Returns a failure if the cited fact gives a different conclusion. |
| `(h3-book-powers-numeric-power lib term)` | Step proving the power call `term` numeric by unfolding its definition. |
| `(h3-book-powers-nonzero-power lib base nonzero exponent)` | Nonzero Step for the power of the term in numeric Step `base` and exponent term `exponent`, given the base's nonzero Step. |
| `(h3-book-powers-power-inverse-law lib base nonzero exponent)` | Inverse-law Step for the power of the term in numeric Step `base` and exponent term `exponent`, given the base's nonzero Step. |
| `(h3-book-powers-inverse-power-equation lib base nonzero index negative)` | `(cons step lib)` equating a negative power and the reciprocal of the power at the opposite exponent, given the base's numeric and nonzero Steps and the exponent's integer and negative Steps. |
| `(h3-book-powers-positive-power lib base positive index)` | `(cons step lib)` proving the power positive, given rational and positive Steps for the base and an integer Step for the exponent. |
| `(h3-book-powers-power-opposite lib base nonzero index)` | `(cons step lib)` equating the opposite power to the reciprocal of the original power, given a numeric and a nonzero Step for the base and an integer Step for the exponent. |
| `(h3-book-powers-add-power-conclusion base first second)` | Equality term for the power of `base` at the sum of the exponent terms `first` and `second`. |
| `(h3-book-powers-power-add-integer lib base nonzero first second)` | `(cons step lib)` proving the addition law, given numeric and nonzero Steps for the base and integer Steps for both exponents. |

`*h3-book-powers-expt*` is the symbol datum for `COMMON-LISP::EXPT`.
The lemma name constants are `*h3-book-powers-natural-integral-power*`,
`*h3-book-powers-natural-positive-power*`, `*h3-book-powers-positive-power*`,
`*h3-book-powers-natural-power-opposite*`, `*h3-book-powers-power-opposite*`,
`*h3-book-powers-power-predecessor*`, `*h3-book-powers-power-add-natural*`
and `*h3-book-powers-power-add-integer*`.

## Exponent induction callbacks

`premises` is a list of the premise Steps in guard order, and `formula`
is an implication term. `whole` and `nonnegative` are the integer and
nonnegative Steps for the exponent. Evaluate the stages in order.

1. `(h3-book-powers-natural-exponent-induction-zero lib whole)` returns
   `(test zero)`. `test` is the equality of the exponent to zero and
   `zero` is the assumption Step for that equality. Run `at-zero` on
   `zero` to produce the base case Step `empty`.
2. `(h3-book-powers-natural-exponent-induction-step lib premises formula whole nonnegative test)`
   takes the Library after `at-zero` and returns
   `(cons (list positive child hypothesis replacement) lib)`. `positive`
   and `child` are the exponent's positive Step and predecessor's integer
   Step. `hypothesis` is the induction hypothesis Step after its decrease
   and premises have been discharged. `replacement` is the list of one
   two-element substitution pair from the exponent to its predecessor.
   Run `advance` on `positive`, `child` and `hypothesis` in the returned
   Library to produce the successor case Step `nonempty`.
3. `(h3-book-powers-natural-exponent-induction lib formula whole test replacement empty nonempty)`
   uses the Library after `advance` to prove the formula by joining the
   two cases and applying induction. It returns `(cons step lib)`.

Each stage may return a failure in place of its result. The abbreviation
`(h3-book-powers-with-natural-exponent-induction lib premises formula whole nonnegative (at-zero arg ...) (advance arg ...))`
executes these stages, passing the current Library first to each callback,
then its Step arguments, then the additional arguments from the call.
Each callback returns `(cons step lib)` or a failure.

## Keeping the Library after a failure

Append `-with-library` to the following names to receive
`(cons result lib)` even when `result` is a failure. The arguments are
the same. The Library contains the auxiliary entries added up to the
failure, in insertion order.

- `predecessor-equation`, `decrease-index`, `positive-index`,
  `natural-exponent-induction-step`, `positive-base`, and `successor-equation`.
- `integral-power-natural`, `positive-power-natural`, `natural-power`,
  `natural-power-opposite`, `inverse-power-equation`, `positive-power`,
  `power-opposite`, `power-predecessor`, `power-add-natural`, and
  `power-add-integer`.
- `prove-natural-power`, `prove-natural-power-opposite`,
  `prove-positive-power`, `prove-power-opposite`, `prove-power-predecessor`,
  `prove-power-add-natural`, and `prove-power-add-integer`. Their successful
  value in the pair is `nil`.
