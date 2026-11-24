# Guarded selectors

Libraries, terms, and Steps have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. `*t2-guarded-selectors-selectors*` is the list of `CAR`
and `CDR` symbols in that order. A context is a Hypotheses from
`prover/sig/descent.md` or `(:t2-ruler-facts hypotheses derived)`, with the
underlying Hypotheses and a Boolean indicating whether its ruler premises
have been derived. The latter form is RulerFacts.

| Function | Arguments and result |
|---|---|
| `(t2-guarded-selectors-selector-path term source)` | Two terms. Returns whether `term` is a nonempty selector path ending at `source`. |
| `(t2-guarded-selectors-selector-tree term source)` | Two terms. Returns whether every leaf is a selector path from `source` or quoted `NIL`. |
| `(t2-guarded-selectors-guarded-selector lib term source)` | Library, defined selector application and its input term. Returns its defining equality Step, or `nil`. |
| `(t2-guarded-selectors-nonempty-source lib equality)` | Library and equality Step. Returns a Step for the nonempty input of a selector, or `nil`. |
| `(t2-guarded-selectors-nil-descent lib parent cons)` | Library, parent count term and `CONSP` evidence Step. Returns a decrease Step for the count of quoted `NIL`. |
| `(t2-guarded-selectors-guarded-decrease lib goal hypotheses)` | Library, ordinal decrease goal and hypothesis context. Returns `(cons step hypotheses)` with a Step or `nil` and the resulting context. |
| `(t2-guarded-selectors-guarded-decrease-leaf term tests lib parent hypotheses)` | Leaf term, signed tests in path order, Library, parent count term and hypothesis context. Returns `(cons step hypotheses)` with the resulting outer context. |

Each function can return a failure in place of its result when term access
or proof construction fails. Extra evidence in a context is kept in
insertion order.

The following context operations use the same representation and can return
a failure from proof construction or from a missing required hypothesis.

| Function | Arguments and result |
|---|---|
| `(t2-guarded-selectors-context-init lib tests extra ruler-facts)` | Library, list of signed tests, list of extra Steps and Boolean selecting `RulerFacts`. Returns the initialized context. |
| `(t2-guarded-selectors-context-find context term)` | Context and term. Returns `(cons step context)` with the Step or `nil` and the resulting context. |
| `(t2-guarded-selectors-context-require context term)` | Context and term. Returns `(cons step context)` or a failure. |
| `(t2-guarded-selectors-context-premises context)` | Context. Returns `(cons steps context)` with the extra evidence in insertion order and the resulting context. |
| `(t2-guarded-selectors-context-selector-decrease lib goal context)` | Library, decrease goal and context. Returns `(cons step context)` or a failure. |
| `(t2-guarded-selectors-context-with-library context lib)` | Context and Library. Returns the context with that Library. |
| `(t2-guarded-selectors-context-learn-step context step)` | RulerFacts context and Step. Returns the context after adding the Step and deriving its consequences in order. |
| `(t2-guarded-selectors-context-hypotheses context)` | Context. Returns the underlying Hypotheses. |
| `(t2-guarded-selectors-library-conjunct lib step)` | Library or Proof and conjunction Step. Returns the two conjunct Steps in order using the object's rule. |
| `(t2-guarded-selectors-library-prove lib term evidence definitions)` | Library or Proof, term, evidence Step list and definition name list. Returns the Step for the term using the object's rule. |

The guarded decrease leaf requires a RulerFacts context. A base
Hypotheses context returns a failure when the leaf asks for premises.

The following proof operations are available before the Arithmetic book
loads. They can return a failure from reading a term or constructing a proof.

| Function | Arguments and result |
|---|---|
| `(t2-guarded-selectors-simplify proof term evidence definitions)` | Proof, term, evidence Step list and definition name list. Returns the simplification equality Step or `nil`. |
| `(t2-guarded-selectors-simplify-first proof step evidence definitions)` | Proof, Step, evidence Step list and definition name list. Returns the Step with its first literal simplified. |
| `(t2-guarded-selectors-library-natural lib term)` | Library and term. Returns the naturalness Step. |
| `(t2-guarded-selectors-library-type-of lib term evidence)` | Library, term and integer evidence. Returns the integer Step. |
| `(t2-guarded-selectors-type-arguments lib terms evidence)` | Library, term list and integer evidence. Returns the corresponding integer Steps in term order. |
| `(t2-guarded-selectors-library-compare-chain lib left right)` | Library and two comparison Steps. Returns the comparison Step with the common endpoint removed. |
| `(t2-guarded-selectors-library-ordinal-comparison lib a b)` | Library and two integer terms. Returns the equality Step relating the ordinal and integer comparison. |

`(t2-guarded-selectors-context-from-hypotheses hypotheses derived)` wraps
the given Hypotheses and Boolean as RulerFacts. It cannot fail.
`(t2-guarded-selectors-arithmetic-p lib)` tests whether the Library or
Proof uses the Arithmetic rules and cannot fail.
