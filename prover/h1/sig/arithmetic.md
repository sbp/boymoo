# Arithmetic

`lib` is the Library component of an H1 prover, using the Library, Proof, and Step forms in `prover/sig/`. A term is a frozen prover term. `claims` is the list of claim Steps in argument order. The constants are `*h1-arithmetic-abs*`, `*h1-arithmetic-reciprocal*`, `*h1-arithmetic-expt*`, `*h1-arithmetic-fix*`, `*h1-arithmetic-zip*` and `*h1-arithmetic-zp*`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h1-arithmetic-conjunction lib formula claims)` | A Step for the right-associated conjunction `formula`. | Proof construction or a failed assertion. |
| `(h1-arithmetic-discrete lib integral pos)` | The integer discreteness Step from integrality and positivity Steps. | Proof construction. |
| `(h1-arithmetic-comparison-by-difference lib left right difference)` | An equality Step between the two comparisons using the given difference equality Step. | Proof construction. |
| `(h1-arithmetic-decrease-nonnegative lib term integral pos left)` | The Step showing that `term` minus one is nonnegative. `left` is `t` to put minus one first and `nil` by default. | Proof construction. |
| `(h1-arithmetic-index-bound-on-cdr lib bound length-equation)` | The Step bounding the decremented index by the tail length. | Proof construction or a failed assertion. |
| `(h1-arithmetic-positive-trichotomy lib term integral)` | The trichotomy Step given the integrality Step. | Proof construction. |
| `(h1-arithmetic-transport-descent lib step child parent)` | The descent Step transported across the child and parent equality Steps. | Proof construction. |

The following functions can also return a request for a method of the H1 prover. The `replies` argument is an alist keyed by `h1-arithmetic-request-key`, with the reply as the entry's cdr. Start with `nil`. On a request, use the corresponding method on the current prover and replay the original arithmetic call with the reply added to the alist. Retain the updated prover between requests, and supply the original `lib` when replaying. A failure from the method goes in the reply in place of its usual result.

| ACL2 call | Result when all requests have replies | Failure |
|---|---|---|
| `(h1-arithmetic-natural-successor lib replies)` | The resulting Library. | Proof construction or a requested method. |
| `(h1-arithmetic-character-at-index lib formula replies)` | The character-at-index Step. | Proof construction or a requested method. |
| `(h1-arithmetic-nonpositive-absolute-value lib replies)` | `(cons step lib)` for the resulting helper fact and Library. | Proof construction or a requested method. |
| `(h1-arithmetic-signed-countdown-lemmas lib replies)` | The resulting Library. | Proof construction or a requested method. |
| `(h1-arithmetic-signed-countdowns lib i replies)` | `(cons (list measure cases) lib)`. Each case is `(bindings step)`, with the minus-one case before the plus-one case. | Proof construction or a requested method. |
| `(h1-arithmetic-multiplicative-types lib replies)` | The resulting Library. | Proof construction or a requested method. |
| `(h1-arithmetic-multiplication-by-zero lib replies)` | The multiplication-by-zero Step. | Proof construction or a requested method. |
| `(h1-arithmetic-zero-product-rules lib replies)` | The resulting Library. | Proof construction or a requested method. |
| `(h1-arithmetic-exponentiation lib formula nonzero replies)` | `(cons step lib)` for the induction Step and resulting Library. `nonzero` is a Boolean selecting the nonzero case. | Proof construction or a requested method. |

`h1-arithmetic-request-p` recognizes a request. `h1-arithmetic-request-key` gives its alist key, and `h1-arithmetic-request-method`, `h1-arithmetic-request-args`, and `h1-arithmetic-request-library` give the operation, its arguments in order, and the Library component at the call.

| Method | Arguments | Reply |
|---|---|---|
| `:solve` | `formula`, `openings`, `limit` | Step. |
| `:rules-add` | `step`, `general`, `rewrite` | `nil`. Retain the updated Rules of the prover. |
| `:rules-add-formula` | `step`, `general`, `rewrite` | `nil`. Retain the updated Rules of the prover. |
| `:helper` | `name`, `step`, `guards`, `rewrite` | `(cons step lib)` with the returned fact Step and the updated Library. Retain the updated Rules of the prover. |
| `:by-induction` | `formula`, `measure`, `substitutions`, `openings`, `ordinal`, `limit`, `assume-premise`, `preserve`, `split-on` | Step. The absent `ordinal` and `split-on` are `nil`. |

`(h1-arithmetic-query recipe lib args replies)` selects one of the request-bearing calls by keyword, such as `:signed-countdowns`, passing `args` in the order of that call between `lib` and `replies`. It returns the selected call's result. An unknown recipe yields a failure. When calling the `tactics` induction method, translate a `nil` split term to `:none`.

The following operations are shared with the propositional proof methods. `proof` is the Proof component. These operations may return a failure.

| ACL2 call | Result |
|---|---|
| `(h1-arithmetic-proof-assume proof term holds)` | The Step for the signed assumption, with Boolean `holds`. |
| `(h1-arithmetic-proof-if-false proof term)` | The conditional's equation under the negative test. |
| `(h1-arithmetic-proof-if-true proof term)` | The conditional's equation under the positive test. |
| `(h1-arithmetic-term-tail term)` | The elements of a frozen term after its head. An integer argument returns a failure. |
