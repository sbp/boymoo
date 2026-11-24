# Bounded list updates

Terms and Steps use the forms in `prover/sig/proof.md`. Library arguments
have the form in `prover/sig/library.md` and supply the proof methods for
these recipes. An update shape is `(update observer getter)`. Its observer
and getter fields are `nil` when the corresponding operation is absent.
A swap plan is `(first second sequence)`. An append suffix shape is
`(call append)`, where append is a function symbol.

| Function | Arguments in order | Result |
|---|---|---|
| `h4-book-updates-index-guard` | Index term, sequence term | Bounds term for the index |
| `h4-book-updates-update-shape` | Formula term | Update shape or `nil` |
| `h4-book-updates-select-result` | Library, call term, condition Step | Equality Step selecting a branch of the unfolded call |
| `h4-book-updates-observe-list` | Library, observer name, sequence term, shape Step or `nil` | Equality Step for observing the sequence |
| `h4-book-updates-prove-bounded-update` | Library, formula term, update shape | Induction Step for the bounded update |
| `h4-book-updates-list-update-proof` | Library, formula term | Bounded update proof Step or `nil` |
| `h4-book-updates-swap-shape` | Formula term | Swap plan or `nil` |
| `h4-book-updates-swap-updates` | Library, formula term, first index, second index, sequence term | Induction Step for the swap |
| `h4-book-updates-swap-proof` | Library, formula term | Swap proof Step or `nil` |
| `h4-book-updates-append-suffix-type` | Library, append function name | Induction Step equating the true-list types of the result and suffix |
| `h4-book-updates-append-suffix-shape` | Library, formula term | Append suffix shape or `nil` |
| `h4-book-updates-append-suffix-proof` | Library, formula term | True-list proof Step or `nil` |

Shape recognizers can return a failure on malformed
terms. Proof functions can return a failure during proof construction. The three
recognizing proof entry points `list-update-proof`, `swap-proof`, and
`append-suffix-proof` return `nil` on an assertion failure in the proof
recipe.

The constants are `*h4-book-updates-true-list*`,
`*h4-book-updates-predecessor-natural*`, `*h4-book-updates-tail-bound*`,
`*h4-book-updates-equal-predecessors*`, and `*h4-book-updates-logic*`.
