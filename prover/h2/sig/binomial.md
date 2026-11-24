# Factorial ratios and binomial induction

`proof` is the proof-search object described in `prover/h2/sig/search.md`.
Terms and Steps have the forms in `prover/sig/proof.md`. A pair in the
result column is constructed with `cons`. Each call can return a failure
as its entire result. Supply `nil` for omitted `factorization`,
`classify` and `facts` arguments.

| Call | Result |
|---|---|
| `(h2-binomial-factorial-evidence proof term)` | Two Steps, for integrality and positivity of factorial term `term`, in that order. |
| `(h2-binomial-factorial-step proof term typed strict)` | Pair of the opened factorial equality Step and the resulting proof. `typed` and `strict` establish integrality and positivity of the index. |
| `(h2-binomial-natural-predecessor proof position typed strict)` | Pair of the two Steps for integrality and nonnegativity of the predecessor of `position` and the resulting proof. `typed` and `strict` establish integrality and positivity of `position`. |
| `(h2-binomial-choose-view proof call fields)` | The open ratio equality Step for a `CHOOSE` term `call`, using the guard Steps `fields` in order. |
| `(h2-binomial-indexed-difference proof strict facts)` | Step for positivity of the difference in strict comparison Step `strict`, using integer evidence Steps `facts`. |
| `(h2-binomial-positive-product proof value factors)` | Step for positivity of product term `value`. `factors` contains the two pairs of integrality and positivity Steps in factor order. |
| `(h2-binomial-scale-ratio proof denominator ratio rest-type divisor-type positive-divisor factorization)` | Equality Step after scaling the ratio equality Step `ratio` by term `denominator`. `rest-type`, `divisor-type` and `positive-divisor` are Steps establishing integrality of the numerator and integrality and positivity of the divisor. `factorization` is an optional equality Step for the denominator. |
| `(h2-binomial-choose-reduction proof formula)` | Pair of the Step for the factorial ratio reduction `formula` and the resulting proof. |
| `(h2-binomial-choose-edge proof at-zero)` | Pair of the symbol naming the boundary lemma and the resulting proof. Boolean `at-zero` selects index zero when true and the diagonal when false. |
| `(h2-binomial-choose-from-boundary proof k n fields not-interior legal)` | Pair of a Step equating `(CHOOSE k n)` to one and the resulting proof. `k` and `n` are index terms, `fields` are their integer Steps, and `not-interior` and `legal` are Steps for the boundary and bounds tests. |
| `(h2-binomial-choose-iteration proof formula classify)` | Pair of the Step for the Pascal induction `formula` and the resulting proof. Boolean `classify` selects the natural type if true and the equality if false. |
| `(h2-binomial-choose-natural proof formula)` | Pair of the Step for the natural type theorem `formula` and the resulting proof. |
| `(h2-binomial-positive-expt proof)` | Pair of the symbol naming the positive exponent lemma and the resulting proof. |
| `(h2-binomial-unfold-positive-expt proof base power natural-type strict)` | Pair of the opened exponent equality Step and the resulting proof. `base` and `power` are terms, and `natural-type` and `strict` establish integrality and positivity of `power`. |
| `(h2-binomial-natural-countdown proof formula n natural-type strict)` | Pair of `(update step)` and the resulting proof. `update` is a one-element binding list reducing the index term `n` by one. The Step proves the smaller instance of `formula`, using the integer and positivity Steps `natural-type` and `strict`. |
| `(h2-binomial-nonnegative-induction proof formula branch base-definitions facts)` | Pair of the induction Step for `formula` and the resulting proof. `base-definitions` is a space-separated string of definition names. `facts` lists extra fact names. `branch` is `:expt-matches-natural` for the exponent branch or an alist mapping `(goal typed strict smaller)` to a branch Step or a failure. |
| `(h2-binomial-expt-matches-natural proof formula)` | Pair of the Step for the equality between exponent functions in `formula` and the resulting proof. |
| `(h2-binomial-binomial-expansion proof label formula)` | Step for the expansion or commutativity theorem `formula`, selected by the unqualified theorem name string `label`. |
| `(h2-binomial-binomial-theorem proof label formula)` | Pair of the Step or `nil` and the resulting proof. `label` is the unqualified theorem name string. The recognized labels are `CHOOSE-REDUCTION`, `CHOOSE-MK-CHOOSE`, `CHOOSE-IS-NON-NEGATIVE-INTEGER`, `CHOOSE-0-N`, `N-EXPT-EXPT`, `BINOMIAL-THEOREM`, `BINOMIAL-SUM-COMMUTES`, and `BINOMIAL-EXPANSION-ZERO`. |
| `(h2-binomial-choose-reduction-scaled ratio numerator-type factorization proof denominator)` | The scaled equality Step for `ratio`, using integer Step `numerator-type` and the optional denominator equality Step `factorization`. |
| `(h2-binomial-choose-iteration-leaf value conditions proof classify formula k n updates)` | Pair of `(step updates)` and the resulting proof. `value` is the leaf term, `conditions` lists its signed tests, and `updates` lists the binding lists collected so far in traversal order. The remaining arguments are from the induction call. |
| `(h2-binomial-expt-matches-natural-more goal typed strict smaller proof)` | Pair of the positive exponent branch Step and the resulting proof. `goal` is the target equality, `typed` and `strict` are integer and positive power Steps, and `smaller` is the induction hypothesis Step. |

Binding lists, term and Step lists, and the list of updates keep traversal order.

A Search with inherited method hooks may yield a Search request as the
entire result. Replay with the ordered replies as described in
`prover/h2/sig/search.md`. A successful pair preserves the unused replies
in its Search. `BINOMIAL-EXPANSION-ZERO` keeps its shifted expansion call
folded during derivation and restores the input hook configuration.
When the Search supplies `:keep-folded` and `:restore-fixed-calls`, the
recipe sends those requests using the protocol in `prover/h2/sig/characters.md`.
