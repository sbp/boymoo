# Tree induction

A `TreeInduction` is `(:b1-tree-induction library formula variable measure substitutions)`. Its measure is the `ACL2-COUNT` of the variable. Its substitutions are a list of lists of `(variable term)` pairs, ordered by first occurrence. Each substitution retains the insertion order of its bindings and omits identity bindings.

| Call | Arguments and result | Failure |
|---|---|---|
| `(b1-induction-tree-induction-init lib formula variable)` | Library, claim term, induction variable term. Returns a TreeInduction with an empty substitution list. | None. |
| `(b1-induction-tree-induction-hypothesis induction bindings tests)` | TreeInduction, insertion-ordered alist of `(variable . term)` bindings, and list of signed `(test holds)` pairs. Returns `(cons step induction)` with the hypothesis Step and the resulting TreeInduction. | A failure from substitution, descent or proof construction. |
| `(b1-induction-tree-induction-finish induction proof)` | TreeInduction and case Step. Returns the induction Step. | A failure from proof construction. |
| `(b1-induction-tree-induction-substitutions induction)` | Returns the TreeInduction's ordered substitution list. | None. |
| `(b1-induction-tree-induction-with-lib induction lib)` | Returns the TreeInduction with the supplied Library and its existing formula, measure and substitutions. | None. |
