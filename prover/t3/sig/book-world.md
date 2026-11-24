# World lookups and symbol lists

`lib` is the Library used by the T3 proof routines. A term and a Step have
the forms in `prover/sig/proof.md`. An entry is the four-element result of
`proof-proof-entry`. A failure is the entire result.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-world-world-nonsymbol lib)` | Library extended with the lemma for a world lookup with a nonsymbol key. | A failure from inspecting or constructing a proof. |
| `(t3-book-world-macro-symbol lib name formula)` | The theorem entry for `formula` with symbol `name`, paired as `(cons entry lib)` with the Library containing the world lookup lemma. | A failure from inspecting or constructing a proof. |
| `(t3-book-world-signed-list lib goal element-type)` | Induction Step for the list recognizer call `goal`. `element-type` is the symbol naming the element recognizer. | `Unsupported` when there is no single tail-recursive argument, or a failure from proof construction. |
| `(t3-book-world-signed-list-leaf value tests lib variable hypothesis predicate element-type)` | Step for the branch value, including the supplied induction hypothesis when the signed `tests` establish a cons for `variable`. `predicate` and `element-type` are recognizer symbols. | A failure from proof construction or missing evidence. |
| `(t3-book-world-required-symbols lib name formula)` | The theorem entry with symbol `name` for the formula proved by the signed-list induction. | A failure from inspecting or constructing a proof. |

`*t3-book-world-plist-world*`, `*t3-book-world-fgetprop*`,
`*t3-book-world-symbol-list*`, `*t3-book-world-hard-error*`,
`*t3-book-world-w*`, and `*t3-book-world-symbolp*` are term symbols.
`*t3-book-world-default*` is the unprefixed world lookup lemma name string.
