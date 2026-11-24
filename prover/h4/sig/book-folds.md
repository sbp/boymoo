# List-fold composition

`p` is a Library with H4 proof methods. Terms and Steps use the forms in `prover/sig/proof.md`. These functions leave the Library unchanged.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h4-book-folds-fold-shape p formula)` | Analyze the term `formula`. Return `(function operations left right state condition transition)` in that order, or `nil` for no match. | A failure from reading or substituting a malformed term. |
| `(h4-book-folds-fold-proof p formula)` | Return the Step for a composition formula, or `nil` for an inapplicable formula or one of the fold fallback kinds in `prover/h4/notes/failures.md`. | Other proof failures and failures from shape analysis. |
