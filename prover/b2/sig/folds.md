# Fold reversal proofs

`lib` is the tactic library. Terms and Steps use the forms in `prover/sig/proof.md`. Each call may return a failure in place of the listed result.

| Call | Arguments and result |
|---|---|
| `(b2-folds-multiplication lib)` | Pair of the multiplication lemma name and the library with the lemma added. |
| `(b2-folds-operator-laws lib name)` | Pair of an operator law descriptor and the resulting library for operator symbol `name`. The descriptor is `:abst` for `ABST` and otherwise the multiplication lemma name. |
| `(b2-folds-operator-laws-law lib kind args law)` | Step for the law named by string `kind` on the ordered argument list `args`, using descriptor `law` and the library returned by `operator-laws`. |
| `(b2-folds-noncons-string lib term string)` | Step that `term` is an atom, using the Step `string` that proves it is a string. |
| `(b2-folds-fold-reverse lib formula)` | Pair of the Step proving the fold reversal equality `formula` and the library with its auxiliary lemmas. |

The symbol constants are `*b2-folds-abst*`, `*b2-folds-mult*`, `*b2-folds-reverse*`, `*b2-folds-revappend*`, `*b2-folds-stringp*`, `*b2-folds-item*` and `*b2-folds-root*`.
