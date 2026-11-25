# Proofs of termination obligations

`lib` is a library in the form specified in `prover/sig/library.md`. `rulers`
has the form in `prover/sig/rulers.md`. A `goal` is an ordinal comparison.
A `clause` is a list of literals ending in that comparison. A `step` has
the form specified in `prover/sig/proof.md`. An absent step is `nil`.

Functions that return `(cons value lib)` put the failure in `value` and
preserve the resulting library. A function that returns only a value or
only a library can return a failure in place of that result. The failure
kinds that allow another tactic are described in `prover/notes/failures.md`.

| ACL2 call | Result |
|---|---|
| `(termination-proofs-structural-decrease lib goal rulers)` | `(cons step lib)`. |
| `(termination-proofs-count-or-length-sum term)` | Whether `term` is made of sums, counts, lengths and nonnegative integer literals. |
| `(termination-proofs-minimum-lemma lib)` | The library with the minimum comparison lemma. |
| `(termination-proofs-termination-proofs lib data stored-measures extra-descent extra-ordinality)` | `(cons (list entry methods measures) lib)`. `data` contains the ruler extenders followed by definition triples. `stored-measures` maps names to lists starting with a measure and relation. `entry` is the proof entry, `methods` is a comma-separated string and `measures` maps names to measures. |

`extra-descent` and `extra-ordinality` hold callback replies. Use `nil`
when the tactic has no callback, or `(t reply ...)` when it does. Each
reply is `(cons step lib)` for one invocation, in invocation order, with
`nil` or a failure also allowed in the step position. On reaching an
invocation without a reply the function returns a request in the value
position. The requests are `(:call :descent lib goal rulers)` and
`(:call :ordinality lib measure)`. Evaluate the callback on those
arguments and repeat the original call with its result appended to the
respective reply list. Replies supply the library as it stands after
their invocation.

For a descent callback that queries its Rulers, construct the reply with
`(termination-proofs-descent-reply step lib rulers)`. This carries the
established hypotheses along with the updated library. Both reply forms
are accepted. `termination-proofs-callback-p` recognizes a request.

The constants `*termination-proofs-selector-definitions*`,
`*termination-proofs-minimum-formals*` and `*termination-proofs-minimum-less*`
hold the ordered list of selector definitions, the minimum comparison
formals, and the name of its fact.
