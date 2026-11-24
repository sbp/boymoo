# Numeric order and additive normalization

A Library, Step and term have the forms in `prover/sig/`. A numeric sum context is
`(:numeric-sums lib types)`. Its fields are the Library and the Search
whose rules derive numeric types. Use the constructor and accessors below.
An evidence argument is a list of Steps in the original argument order.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h3-numeric-order-cite lib name values evidence)` | Library, unprefixed lemma name string, argument terms and evidence. Returns the instantiated numeric-order lemma with evidence discharged in order. | A failure from inspecting evidence or constructing the citation. |
| `(h3-numeric-order-save lib name step hypotheses)` | Library, unprefixed lemma name string, proof Step and hypothesis terms. Returns the Library with the lemma. | A failure from constructing the entry. |
| `(h3-numeric-order-numeric-sums-init lib)` | Library. Returns a numeric sum context. | A failure from constructing the Search or its rules. |
| `(h3-numeric-order-numeric-sums-lib sums)` | A numeric sum context. Returns its Library. | None. |
| `(h3-numeric-order-numeric-sums-types sums)` | A numeric sum context. Returns its Search. | None. |
| `(h3-numeric-order-numeric-sums-cite sums name args evidence)` | A numeric sum context, unprefixed lemma name string, argument terms and evidence. Returns the instantiated lemma Step with evidence discharged in order. | A failure from inspecting evidence or constructing the citation. |
| `(h3-numeric-order-numeric-sums-type-of sums term evidence)` | A numeric sum context, term and evidence. Returns a numeric type Step or `nil`. | A failure from proof search. |
| `(h3-numeric-order-numeric-sums-push-minus sums term evidence)` | A numeric sum context, term and evidence. Returns `nil`. | None. |
| `(h3-numeric-order-numeric-sums-linear-form sums term evidence)` | A numeric sum context, term and evidence. Returns a normalization Step. | A failure from constructing the normalization. |
| `(h3-numeric-order-numeric-sums-linear-equal sums left right evidence)` | A numeric sum context, two terms and evidence. Returns a Step proving the equality of the terms. | A failure from constructing or comparing the normal forms. |
| `(h3-numeric-order-add-zero lib number)` | Library and numeric type Step. Returns the Library with the two numeric zero-addition entries. | A failure from constructing the entries. |
| `(h3-numeric-order-additive-inverse lib sums a b numbers)` | Library, numeric sum context, two terms and numeric evidence. Returns a Step. | A failure from constructing the proof. |
| `(h3-numeric-order-positive-difference lib sums numbers opposite)` | Library, numeric sum context, numeric evidence and opposite-difference equality Step. Returns a Step. | A failure from constructing the proof. |
| `(h3-numeric-order-asymmetric lib numbers comparison opposite)` | Library, numeric evidence and the comparison and opposite-difference equality Steps. Returns a Step. | A failure from constructing the proof. |
| `(h3-numeric-order-antisymmetric lib sums numbers comparison opposite)` | Library, numeric sum context, numeric evidence and the comparison and opposite-difference equality Steps. Returns a Step. | A failure from constructing the proof. |
| `(h3-numeric-order-strict-transitive lib sums numbers)` | Library, numeric sum context and numeric evidence. Returns a Step. | A failure from constructing the proof. |
| `(h3-numeric-order-ordered-composition lib numbers first-strict second-strict)` | Library, numeric evidence and two Boolean strictness flags. Returns a Step. | A failure from constructing the proof. |
| `(h3-numeric-order-numeric-order lib)` | Library. Returns the Library with the numeric-order entries. | A failure from constructing the entries. |

`*h3-numeric-order-prefix*` is the lemma name prefix string. Use
`h3-numeric-order-numeric-sums-lib` to access the Library in a numeric sum
context.
