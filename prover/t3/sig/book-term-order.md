# Term order

`lib` is a Library with the T3 proof rules for its dispatch tag. Terms and Steps
use the forms in `prover/sig/proof.md`. The strings in
`*t3-book-term-order-laws*` occur in the order reflexivity, antisymmetry,
transitivity and totality. `*t3-book-term-order-order*` and
`*t3-book-term-order-lexorder*` are prover symbols.

A LexicographicLayer has the form
`(:t3-lexicographic-layer lib key relation prefix following-prefix)`.
The key and relation are function symbols. The prefixes are lemma name
strings. `(t3-book-term-order-lexicographic-layer-init lib key relation prefix following-prefix)`
constructs this object. Use the following functions
for its methods. A failure is the entire result.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-term-order-call lib law args)` | Step for the named term-order law instantiated with list `args` in X, Y, Z order. | A failure from looking up or instantiating the fact. |
| `(t3-book-term-order-number-chain lib left right)` | Step composing two strict or weak comparison Steps sharing an endpoint. | A failure from reading the Steps or citing the composition lemma. |
| `(t3-book-term-order-lexicographic-layer-leading layer x y)` | Strict comparison term for the key applied to `x` and `y`. | None. |
| `(t3-book-term-order-lexicographic-layer-equation layer x y evidence)` | Equality Step from unfolding and selecting the comparison, with the ordered list of evidence Steps. | A failure from constructing the proof. |
| `(t3-book-term-order-lexicographic-layer-tail layer law args)` | The following layer's law Step instantiated with list `args` in X, Y, Z order. | A failure from looking up or instantiating the fact. |
| `(t3-book-term-order-lexicographic-layer-anti-less layer strict)` | Reversed strict comparison denied by Step `strict`. | A failure from reading the Step or citing the lemma. |
| `(t3-book-term-order-lexicographic-layer-weak-bound layer before x y)` | Weak bound on the first key from the full comparison Step `before`. | A failure from constructing the proof. |
| `(t3-book-term-order-lexicographic-layer-antisymmetry layer)` | Antisymmetry Step for this layer. | A failure from constructing the proof. |
| `(t3-book-term-order-lexicographic-layer-transitivity-strict proof layer)` | Strict comparison case for the transitivity proof, given the strict first-key Step `proof`. | A failure from constructing the proof. |
| `(t3-book-term-order-lexicographic-layer-transitivity layer)` | Transitivity Step for this layer. | A failure from constructing the proof. |
| `(t3-book-term-order-lexicographic-layer-totality layer)` | Totality Step for this layer. | A failure from constructing the proof. |
| `(t3-book-term-order-lexicographic-layer-build layer)` | Layer with its Library extended by all four laws in law order. | A failure from constructing or adding a law. |
| `(t3-book-term-order-projection-keys body)` | List of key terms in their order of comparison in term `body`. | `unproved` for unsupported comparisons, different keys, or a missing tie breaker, or a failure from reading the term. |
| `(t3-book-term-order-build lib)` | Library with the numeric, lexicographic and term-order laws and the intermediate comparison definitions. The comparison layers are built from the last key back to the first. | A failure from constructing or adding a definition or law, or `unproved` if the comparison does not fold as expected. |
