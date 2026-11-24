# List equivalence

A Library and a Step have the forms in their respective signatures. A term is
a prover term. Evidence is a list of Steps. The constant
`*list-equivalence-iff*` is the `IFF` symbol.

A ListEquivalence has the form
`(:list-equivalence library relation equation name cons-equation atom-equation)`.
Its relation is a symbol, its name is a string, and its equations are Steps.
The constructor is `list-equivalence-list-equivalence-new`, taking a Library
and a relation. The accessors have prefix
`list-equivalence-list-equivalence-` and field names `library`,
`relation`, `equation`, `name`, `cons-equation`, and
`atom-equation`. The constructor returns a ListEquivalence or a failure.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `list-equivalence-paired-substitutions` | Library, conclusion term, left variable, right variable | List of substitution binding lists, or a failure |
| `list-equivalence-paired-reduction` | Library, goal term, evidence | Step, `nil`, or a failure |
| `list-equivalence-prove-list-equivalence` | Library, formula term | Pair with a Step, failure, or request |
| `list-equivalence-prove-list-equivalence-resume` | Library, continuation, answer | Same results as `list-equivalence-prove-list-equivalence` |

The recursive arguments used by `list-equivalence-paired-substitutions`
come from the Library definitions.

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
