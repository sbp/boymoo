# Factorization

The `lib` argument is a Library as specified in `prover/sig/library.md`. Terms and Steps have the forms in `prover/sig/proof.md`. The result of each proof recipe can be a failure from reading a term or constructing a proof.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-factorization-factor-right lib expression factor)` | Terms `expression` and `factor`. Returns a Step equating `expression` to a product with right factor `factor`, or `nil` when no factorization is found. |
| `(t2-factorization-align lib actual expected)` | Terms `actual` and `expected`. Returns their equality Step or `nil` when the tactic cannot align them. |
| `(t2-factorization-comparison-equation lib comparison factor parts different facts)` | Comparison operator symbol, factor term, list of factorization Steps in operand order, distinctness Step, and RulerFacts. Returns the Step equating the original and factored comparisons. |
| `(t2-factorization-prove lib formula)` | Formula term. Returns its Step, or `nil` when the formula does not match or no candidate succeeds. |

The candidate search takes premises in the insertion order of the RulerFacts extra evidence and tries each factor before advancing to the next premise.

`factor-right` and `prove` return `(cons step lib)`, with `nil` for a missing Step. The Library includes any `PRODUCT-ZERO` entry added while constructing or trying a factorization. `comparison-equation` returns `(cons step facts)` with the RulerFacts after the rationality query, when the comparison requires one. A failure is the entire result in each case.

`(t2-factorization-factor-candidates facts comparison)` takes RulerFacts and the comparison operator symbol. It returns `(cons candidates facts)`, with `(factor distinctness-step)` pairs in premise order and the resulting RulerFacts, or a failure. `prove` consumes the same sequence incrementally.

For the quoted zero expression, `factor-right` returns the symmetric `PRODUCT-ZERO` Step, with the factor followed by zero on its right side.
