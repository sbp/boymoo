# Indexed list operations

`proof` is the H2 proof context. Terms and Steps use the forms in
`prover/sig/proof.md`. All results are `(cons value proof)` with the resulting
proof context, except that a failure from proof construction is the entire
result of any call below. Names in the results are strings.

| Function and arguments | Value |
|---|---|
| `(h2-subsequence-take-length proof)` | The name of the lemma for the length of `TAKE`. |
| `(h2-subsequence-list-fix-selectors proof)` | The two list normalization selector lemma names, for `CAR` and `CDR` in that order. |
| `(h2-subsequence-list-fix-operations proof)` | The two list normalization operation lemma names, for `TAKE` and `NTHCDR` in that order. |
| `(h2-subsequence-take-whole proof)` | The name of the lemma for taking the whole list. |
| `(h2-subsequence-nthcdr-nil proof)` | The name of the lemma for `NTHCDR` of `NIL`. |
| `(h2-subsequence-nthcdr-length proof)` | The name of the lemma for the length after `NTHCDR`. |
| `(h2-subsequence-take-with-fixed-count proof)` | The name of the lemma for taking a naturalized count. |
| `(h2-subsequence-subsequence-of-length proof formula)` | The Step proving the whole-subsequence claim term `formula`. |
| `(h2-subsequence-subsequence-theorem proof label formula)` | The Step proving the indexed list theorem with name string `label` and claim term `formula`, or `nil` for an unrecognized label. |

The proof context is the inherited Recipes object described in
`prover/h2/sig/recipes.md`. A proof search can return a Search method request
as its entire result. A successful search leaves the unconsumed replies in
the returned Recipes.
