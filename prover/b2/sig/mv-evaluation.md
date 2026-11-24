# Multiple-value evaluation

`lib` is a Library. Indices, terms, environments, and formulas are prover terms. Evidence is a list of Steps in the supplied order. The symbols are `*b2-mv-evaluation-nth*`, `*b2-mv-evaluation-ev*`, `*b2-mv-evaluation-rec*`, `*b2-mv-evaluation-meta*`, `*b2-mv-evaluation-rec-correct*`, `*b2-mv-evaluation-meta-correct*`, and `*b2-mv-evaluation-n*`. `*b2-mv-evaluation-mv-evaluation*` is the theorem-name set, ordered by the text of the serialized symbols.

| Call | Result |
|---|---|
| `(b2-mv-evaluation-index-equivalence lib index values)` | `(cons step lib)` with the equality Step for `MV-NTH` and `NTH`, and the Library containing its auxiliary lemma. |
| `(b2-mv-evaluation-ev-quote lib term env evidence)` | The evaluator equality Step for quoted data. |
| `(b2-mv-evaluation-ev-binary lib term env operation evidence)` | The evaluator equality Step for a cons or multiple-value projection. `operation` is a symbol. |
| `(b2-mv-evaluation-recursive-evaluation lib formula)` | `(cons step lib)` with the recursive-evaluation induction Step and its resulting Library. |
| `(b2-mv-evaluation-mv-meta lib formula)` | The projection metafunction correctness Step. |
| `(b2-mv-evaluation-mv-evaluation-theorem lib name formula)` | `(cons step lib)` with the Step for theorem symbol `name` and its resulting Library. |

Each function can return a failure as its entire result.
