# Recursive products and sums

`proof` is the H2 search proof object used by the book prover. Its library contains the facts, definitions and entries described in `prover/sig/library.md`. Terms and Steps are as in `prover/sig/proof.md`. A call that changes the proof returns `(cons value proof)` with the updated object, including the search configuration. Every function can return a failure in place of its result.

`*h2-numeric-recipes-sum*` and `*h2-numeric-recipes-append*` are the ACL2 symbol terms `SUMLIST` and `BINARY-APPEND` respectively.

| ACL2 call | Result |
|---|---|
| `(h2-numeric-recipes-positive-factorial proof formula)` | Step for the positive integer factorial term `formula`. |
| `(h2-numeric-recipes-factorial-theorem proof label formula)` | Pair of the Step for the factorial term `formula` selected by the string `label` and the proof. |
| `(h2-numeric-recipes-factorial-quotient proof formula)` | Pair of the Step for the quotient term `formula` and the proof. |
| `(h2-numeric-recipes-numeric-theorem proof label formula)` | Pair of the Step for the term `formula` selected by the string `label` and the proof. The Step is `nil` for an unrecognized label. |

The proof argument is the inherited Recipes object specified in `prover/h2/sig/recipes.md`. For `SUMLIST-APPEND`, the result contains the Recipes after the auxiliary lemma and configuration. Its value is a request for the operation `:induct-with-folded-calls`. `h2-numeric-recipes-folded-request-p` recognizes the request and `h2-numeric-recipes-folded-request-args` returns `(formula variable definitions)` in method argument order. Apply the operation to the BookProof with the returned Recipes installed and use that operation's Step and updated proof.

An entry point that invokes a search can also return a Search request as its entire result under the replay protocol in `prover/h2/sig/search.md`.
