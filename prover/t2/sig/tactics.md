# Termination tactics

Terms, Steps, Libraries, and proof entries use the forms in `prover/sig/proof.md`
and `prover/sig/library.md`. A definition and a ruler extender use the forms in
`prover/sig/termination.md`. `tests` is the list of `(term holds)` pairs in call
path order. Dictionaries are insertion-ordered alists. A failure is the entire result. `unsupported` identifies a measure or obligation
that the recipe cannot handle.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-tactics-proof-entries lemmas entry)` | From the list of lemma entries `lemmas` in insertion order, return the entries needed by `entry`, in library order, followed by `entry` itself. | A failure from inspecting an entry or writing its name. |

## Ruler facts

A RulerFacts object has the form `(:t2-tactics-ruler-facts hypotheses derived)`.
`hypotheses` is the underlying Hypotheses object from `prover/sig/descent.md`.
Its `extra` dictionary preserves the insertion order of initial and learned
Steps, and its `found` dictionary records the base hypothesis queries. `derived`
is true once premise derivation has begun. Use the constructor and accessors.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-tactics-ruler-facts-init proof tests extra)` | RulerFacts for the Proof or Arithmetic Library `proof`, signed tests `tests`, and initial Step list `extra`. | A failure from reading a Step. |
| `(t2-tactics-ruler-facts-hypotheses facts)` | Underlying Hypotheses of RulerFacts `facts`. | None. |
| `(t2-tactics-ruler-facts-proof facts)` | The Proof or Library of `facts`. | None. |
| `(t2-tactics-ruler-facts-tests facts)` | The signed tests of `facts`. | None. |
| `(t2-tactics-ruler-facts-extra facts)` | The extra-Step dictionary of `facts`. | None. |
| `(t2-tactics-ruler-facts-derived facts)` | Whether premise derivation has begun. | None. |
| `(t2-tactics-ruler-facts-with-proof facts proof)` | RulerFacts with the supplied Proof or Library. | None. |
| `(t2-tactics-ruler-facts-find facts term)` | `(cons step facts)` with the first Step for `term`, or `nil` in the step position, and the resulting RulerFacts. | A failure from constructing a proof. |
| `(t2-tactics-ruler-facts-require facts term)` | `(cons step facts)` with the Step for `term` and the resulting RulerFacts. | A failure when a required Step is missing or proof construction fails. |
| `(t2-tactics-ruler-facts-premises facts)` | `(cons steps facts)` with the extra Steps in dictionary value order and the resulting RulerFacts. | A failure from constructing a proof. |
| `(t2-tactics-ruler-facts-learn facts step)` | The resulting RulerFacts after learning `step` and its derived Steps in order. | A failure from constructing a proof. |

## Generator

A Generator has the form `(:t2-tactics-generator measures lib shared)`.
`measures` is an insertion-ordered dictionary from function names to
`(measure relation)` pairs. `lib` is the Arithmetic Library. `shared` is the
number of shared call-decrease lemmas named by this Generator. The `measures`
argument of `prove-definition` is instead a dictionary from function names
to measure terms whose insertion order supplies the measure header fields.
`data` is the frozen list of arguments following the entry word `kind`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-tactics-generator-init measures)` | Generator with an Arithmetic Library built for `measures` and a zero shared-lemma count. | A failure from building the Library. |
| `(t2-tactics-generator-make measures lib shared)` | Generator with the given fields. | None. |
| `(t2-tactics-generator-measures generator)` | The stored measure and relation dictionary. | None. |
| `(t2-tactics-generator-lib generator)` | The Arithmetic Library of `generator`. | None. |
| `(t2-tactics-generator-shared generator)` | The shared-lemma counter of `generator`. | None. |
| `(t2-tactics-generator-with-lib generator lib)` | Generator with the supplied Arithmetic Library. | None. |
| `(t2-tactics-generator-with-measures generator measures)` | Generator with the supplied stored measure and relation dictionary. | None. |
| `(t2-tactics-generator-admit-given generator kind data)` | Generator after adding the definitions or facts from the given event. | A failure from inspecting or admitting the event. |
| `(t2-tactics-generator-measures-for generator definitions)` | Dictionary from names to measure terms in definition order. | `missing-binding` for an absent measure, `unsupported` for another relation, or a failure from inspecting the definitions or measures. |
| `(t2-tactics-generator-prove-definition generator rulers definitions measures)` | `(cons entry generator)` with the measure entry and the resulting Generator. | A failure from constructing the obligations or proof. |
| `(t2-tactics-generator-ordinal generator measure)` | `(cons step generator)` with an ordinality Step and the resulting Generator. | A failure from constructing a proof. |
| `(t2-tactics-generator-decrease generator clause tests)` | `(cons step generator)` with the decrease Step and the resulting Generator. | `unsupported` if there is no descent recipe, or a failure from constructing a proof. |

Term constants are `*t2-tactics-atom*`, `*t2-tactics-endp*`,
`*t2-tactics-null*`, `*t2-tactics-eq*`, `*t2-tactics-eql*`,
`*t2-tactics-equal-num*`, `*t2-tactics-zp*`, `*t2-tactics-zip*`,
and `*t2-tactics-posp*`. `*t2-tactics-definition-heads*` is the list of
function symbols opened by `learn`, in test order.

`*t2-tactics-entry-names*` contains the prefix and the allowed continuation
characters of an entry name, each as a character list.

The RulerFacts constructor uses the context tag `:t2-ruler-facts` from
`prover/t2/sig/guarded-selectors.md`. The hypothesis and derived accessors
read the fields specified above for either tag.

With a bare Proof, selector completion returns a failure when it
calls the Library axiom method.

## Recipe queries and caught proof failures

The following Countdown calls use RulerFacts for `facts`. They return
`(step lib facts)` with the resulting Library and RulerFacts, or return a
failure from the recipe or its hypothesis queries.

| Call | Result |
|---|---|
| `(t2-tactics-countdown-fixed-absolute-count lib measure facts)` | Equality Step removing `IFIX` from the fixed absolute measure. |
| `(t2-tactics-countdown-signed-premise lib value facts negative)` | Signed-bound Step for the value term, with `negative` selecting a negative or positive bound. |
| `(t2-tactics-countdown-negative-countdown lib goal facts)` | Integer countdown decrease Step. |

`(t2-tactics-generator-prove-attempt generator kind data)` and
`(t2-tactics-generator-prove-definition-attempt generator rulers definitions measures)`
return `(cons value generator)` for clients that catch a proof failure and
continue with the same Generator. The value is either the entry or a failure.
The Generator carries the library and counter changes through the completed
operations of the attempt.
