# List equivalence

A Library and a Step have the forms in their respective signatures. A term is
a prover term. Evidence is a list of Steps. The constant
`*list-equivalence-iff*` is the `IFF` symbol.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `list-equivalence-paired-reduction` | Library, goal term, evidence | Step, `nil`, or a failure |
| `list-equivalence-prove-list-equivalence` | Library, formula term | Pair with a Step, failure, or request |
| `list-equivalence-prove-list-equivalence-resume` | Library, continuation, answer | Same results as `list-equivalence-prove-list-equivalence` |

The pair is `(cons result library)`, with the Library as it stands on
return. A request is `(:call goal evidence continuation)`. The caller
proves `goal` using the evidence Steps and passes the Step or failure as
`answer` together with the resulting Library. Pass the continuation as
returned. Repeat until the result is a Step or a failure.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `list-equivalence-list-equivalence-relation-equation` | ListEquivalence, relation call term | Step for the relation's equation, or a failure |
| `list-equivalence-list-equivalence-align` | ListEquivalence, premise Step, left term, right term, two Booleans for cons shape | Step equating the two spines, or a failure |
| `list-equivalence-list-equivalence-mismatch` | ListEquivalence, equality Step | Step refuting a cons and atom mismatch, or a failure |
| `list-equivalence-list-equivalence-contents` | ListEquivalence, equality Step, left term, right term | List of the head equality and tail relation Steps, or a failure |
| `list-equivalence-list-equivalence-lemmas` | ListEquivalence | `(cons result equivalence)`, with `nil` or a failure and the ListEquivalence containing the Library as it stands |
| `list-equivalence-list-equivalence-new-result` | Library, relation symbol | `(cons result library)`, with the ListEquivalence or failure and the Library as it stands |
