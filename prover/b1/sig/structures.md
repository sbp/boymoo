# List and state representation proofs

`lib` is a Library as specified in `prover/sig/library.md`. A proof argument is a Step as specified in `prover/sig/proof.md`. Formulas, selectors and other terms use the term representation in that signature. Each operation on a proof or a formula can return a failure as its entire result.

| ACL2 call | Result |
|---|---|
| `(b1-structures-project-mv lib selector equation)` | Equality Step exposing the fixed `MV-NTH` projection `selector` after applying the equality Step `equation` to its list argument. |
| `(b1-structures-proper-list-is-not-string lib proper)` | Step proving that the true list recognized by Step `proper` is not a string. |
| `(b1-structures-oracle-projection lib formula)` | Step for the oracle or global table projection formula. |
| `(b1-structures-pseudo-tail lib formula)` | Step for the implication that a nonquoted pseudo term has a pseudo-term list as its tail. |
| `(b1-structures-length-of-list lib proof)` | Equality Step reducing `LENGTH` on the true list recognized by Step `proof`. |
| `(b1-structures-symbol-list-implies-list lib)` | `(cons name lib)` for the symbol naming the symbol-list implication lemma and the Library containing it. |
| `(b1-structures-wrappers term)` | List of the `RETURN-LAST` calls in traversal order. A wrapper precedes the wrappers in its last argument. Other applications are visited in argument order, and a quote is opaque. Repeats are retained. |
| `(b1-structures-pseudo-lambda lib formula)` | `(cons step lib)` for the pseudo-term implication for a lambda application and the Library with the symbol-list lemma. |
| `(b1-structures-noncons-selector lib selector noncons)` | Equality Step giving the value of `CAR` or `CDR` on the term that Step `noncons` proves is not a cons. |
| `(b1-structures-open-mv-nth lib formula)` | Step for the implication opening `MV-NTH` on its list argument. |
| `(b1-structures-true-list-tail lib proof cons)` | Step proving that the tail of the true list recognized by Step `proof` is a true list, using Step `cons` for its nonemptiness. |
| `(b1-structures-option-entry-tail lib formula)` | Induction Step proving that an option lookup returns an entry with a proper tail. |

The term constants are `*b1-structures-read-oracle*`, `*b1-structures-update-oracle*`, `*b1-structures-mv-nth*`, `*b1-structures-global-table*`, `*b1-structures-get-global*`, `*b1-structures-nth*`, `*b1-structures-length*`, `*b1-structures-true-listp*`, `*b1-structures-symbol-listp*`, `*b1-structures-pseudo*`, and `*b1-structures-pseudo-list*`. The constant `*b1-structures-projection-unfold*` lists the definitions to unfold in projection proofs.
