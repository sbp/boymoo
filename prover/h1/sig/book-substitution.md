# Structural substitution

`proof` is the H1 Prover. Terms and Steps have the forms in
`prover/sig/proof.md`. `tests` is an ordered list of `(term holds)` pairs.
`known` in `typed-value` is an association list from terms to Steps in
insertion order. The prover symbols are `*h1-book-substitution-term*`,
`*h1-book-substitution-terms*`, `*h1-book-substitution-cons-term*`,
`*h1-book-substitution-cons-term1*`, `*h1-book-substitution-cons-term2*`,
`*h1-book-substitution-kwote*`, `*h1-book-substitution-mv-nth*`,
`*h1-book-substitution-strip-cdrs*` and `*h1-book-substitution-eq*`.
`*h1-book-substitution-quote-name*` is the quotation of the `QUOTE` symbol.

| Call | Result |
|---|---|
| `(h1-book-substitution-note proof name step)` | `(cons citation proof)` with the updated Prover and a citation of the lemma named by the unprefixed string `name`. |
| `(h1-book-substitution-tuple-result proof value)` | A Step equating the second projection of a constructed tuple with its second component. |
| `(h1-book-substitution-term-choice proof value typed-yes typed-no)` | A Step proving the type of the conditional term `value` using its branch type Steps. |
| `(h1-book-substitution-typed-value n proof value known)` | A Step proving the type of `value`. Pass `1000000` as the initial fuel `n`. |
| `(h1-book-substitution-constructor-types proof)` | The Prover with the constructor type lemmas. |
| `(h1-book-substitution-list-types proof)` | The Prover with the list constructor and selector type lemmas. |
| `(h1-book-substitution-syntax-body proof term cons not-quote parts)` | A Step opening the nonquote cons case of the term type test. `parts` is an empty list or the two arguments of the constructed cons. |
| `(h1-book-substitution-after-argument-test proof value typed-arguments)` | A Step denying the test extracted from `value`, using the type Step `typed-arguments`. |
| `(h1-book-substitution-logical-header proof equation)` | The equation Step with `RETURN-LAST` calls in its right side unfolded in traversal order. |
| `(h1-book-substitution-replacement-arguments proof)` | The Prover with the argument list type and argument replacement lemmas. |
| `(h1-book-substitution-install-syntax proof)` | The Prover with the term syntax lemmas installed in order. |
| `(h1-book-substitution-install-parallel-lookup proof)` | The Prover with the parallel lookup type lemma. |
| `(h1-book-substitution-nonquote-from-path proof value tests)` | A Step proving the nonquote branch for `value` from the signed tests. |
| `(h1-book-substitution-substitution-proof proof formula)` | `(cons step proof)` with the Step for `formula` and the Prover including any installed substitution lemma. |
| `(h1-book-substitution-substitution-proof-with-proof proof formula)` | `(cons value proof)`, with a Step or a failure in `value` and the Prover as of that result. |

The calls above can return a failure as the entire result, except the
state-preserving `substitution-proof-with-proof`.

## Substitution object

A Substitution is `(:h1-substitution proof family term terms projected
parameters hypothesis assumption term-call list-call term-claim list-claim
length consequent claim)`. `family` is the unqualified string naming the
substitution function. `term` and `terms` are the symbols naming the term
and list substitution functions. `projected` is a Boolean. `parameters`
is the ordered list of formal terms. `hypothesis` and the claim fields are
terms, `assumption` is a Step, and `term-call` and `list-call` are terms.
`h1-book-substitution-substitution-init` constructs this object from
`proof` and `family`. Accessors have the
`h1-book-substitution-substitution-` prefix followed by the field name.

| Call | Result |
|---|---|
| `(h1-book-substitution-substitution-result substitution expression)` | The result term, with its second projection selected for the projected family. |
| `(h1-book-substitution-substitution-projection substitution expression)` | The Step equating the returned value to its tuple projection or to itself. |
| `(h1-book-substitution-substitution-subcase substitution selector)` | Three Steps for the term type, list type and length claims on the argument of the selector. |
| `(h1-book-substitution-substitution-result-cases substitution application known template leaf)` | A Step for `template` applied to `application` under the container Step `known`. `leaf` is an alist of `((value tests) . result)` replies as in `proof-proof-by-value`. |
| `(h1-book-substitution-substitution-atomic-term n substitution value typed-input)` | The type Step for the selected replacement or input. Pass `1000000` as the initial fuel `n`. |
| `(h1-book-substitution-substitution-term-proof substitution cons tail)` | The term implication Step. `cons` is a Step deciding whether the input is a cons. `tail` is the tail subcase or `nil`. |
| `(h1-book-substitution-substitution-list-proof substitution cons head tail)` | The list implication Step. `head` and `tail` are subcases or `nil`. |
| `(h1-book-substitution-substitution-length-proof substitution cons tail)` | The length preservation Step. |
| `(h1-book-substitution-substitution-prove substitution)` | The induction Step for the simultaneous term type, list type and length theorem. |

The constructor and Step construction functions can return a failure in
place of the listed result.

The proof field accessor is `h1-book-substitution-substitution-proof-object`.
