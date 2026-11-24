# B2 simultaneous substitution

Terms, Steps, and the Library use the shared representations in `prover/sig/`.
Steps in an evidence list follow the supplied order. A result of the form
`(cons value lib)` contains the updated Library in its cdr. A failure is
returned in place of the whole result.

| Call | Result | Failure |
|---|---|---|
| `(b2-substitution-original-tail lib value predicate cons-proof not-quote)` | Step proving the cdr of the term `value` a pseudo-term list, using the indicated pseudo-term, cons, and non-quotation Steps. | May return a failure from proof construction. |
| `(b2-substitution-substitution-preserves-term lib name formula)` | `(cons step lib)` for the conjunct of simultaneous substitution preservation that equals `formula`. | Missing matching conjunct or unsuccessful proof construction. |
| `(b2-substitution-second term)` | Term selecting the second value of `term`. | — |
| `(b2-substitution-output fn expression)` | Term selecting the second result of applying the function symbol `fn` to the substitution environment and `expression`. | — |
| `(b2-substitution-result-cases lib call template prove)` | Step for the result template on the given definition call. The leaf proof table `prove` has `((value tests) . step)` entries, with signed tests and failures as in `proof-proof-by-value`. | May return a failure from a leaf or proof construction. |
| `(b2-substitution-pair-projection lib pair)` | `(cons step lib)` for the second projection of the constructed pair term. | May return a failure from proof construction. |
| `(b2-substitution-size-preserved lib)` | `(cons name lib)` for the lemma that substitution preserves length, constructing it when absent. | May return a failure from proof construction. |
| `(b2-substitution-folded-equation lib call)` | Step for unfolding the given call and applying beta reduction to its result until the head is no longer a lambda. | May return a failure from proof construction or fuel exhaustion. |
| `(b2-substitution-computed-term lib)` | `(cons name lib)` for the computed pseudo-term lemma, constructing it when absent. | May return a failure from proof construction. |
| `(b2-substitution-folded-term-property lib call original)` | `(cons step lib)` for the pseudo-term property of the folded call, given the Step `original` for its input term. | May return a failure from proof construction. |
| `(b2-substitution-wrap-construction lib fn args typed)` | `(cons step lib)` for construction with term arguments `fn` and `args`, given their pseudo-term Step `typed`. | May return a failure from proof construction. |
| `(b2-substitution-erase-return-values lib definition)` | The definition Step rewritten after exposing the result of each `RETURN-LAST` call. | May return a failure from proof construction or fuel exhaustion. |
| `(b2-substitution-rebuild-statement lib)` | `(cons name lib)` for rebuilding a pseudo-term, constructing the lemma when absent. | May return a failure from proof construction. |
| `(b2-substitution-preservation lib)` | `(cons name lib)` for the simultaneous substitution preservation lemma, constructing it when absent. | May return a failure from proof construction. |

The symbol constants are `*b2-substitution-pseudo-list*`, `*b2-substitution-salist*`,
`*b2-substitution-term*`, `*b2-substitution-terms*`, `*b2-substitution-construct*`,
`*b2-substitution-fold*`, `*b2-substitution-fold-mv*`, `*b2-substitution-mv*`,
`*b2-substitution-kwote*`, `*b2-substitution-env*`, `*b2-substitution-fn*`,
`*b2-substitution-args*`, and `*b2-substitution-form*`.
