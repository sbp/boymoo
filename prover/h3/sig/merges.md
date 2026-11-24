# Two-list merges

The Library, term and Step arguments have the forms in the shared signatures.
Every call can return a failure.

| Call | Result |
|---|---|
| `(h3-merges-arithmetic lib)` | Library with the shared arithmetic and list-length lemmas installed. |
| `(h3-merges-merge-termination lib call mapping)` | Step proving decrease of the sum of lengths for the recursive call under the ordered substitution association list. |
| `(h3-merges-two-list-merge lib formula rules)` | `(cons step lib)` for the merge formula. Its Library contains the arithmetic lemmas. `rules` lists additional rule names in order and is `nil` when omitted. |
| `(h3-merges-two-list-merge-prove-case evidence lib call rules formula)` | Step for a merge induction case given the evidence Steps, the merge call term and the additional rule names. |
| `(h3-merges-merge-lexorder lib formula)` | `(cons step lib)` for the merge's order formula, with the auxiliary lemmas in the Library. |

Substitution dictionaries use the call argument order. The induction uses
recursive calls in source order.
