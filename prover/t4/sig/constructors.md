# Constructor recipes

The Library and Step representations are specified in `prover/sig/library.md`
and `prover/sig/proof.md`. A formula is a prover term. `recursive` is
the list of recursively defined function names in definition order.

| Call | Result |
|---|---|

Each call returns `(cons result library)`, a failure, or a request
`(:t4-request operation arguments library)`. Pass the starting Library
and an empty `replies` list on the first call. The request gives the
Library at the operation and the ordered operation arguments. Append
`(cons value library)` to `replies` and call the recipe again with its
original arguments. If the operation fails, append its failure as
the reply. The operations execute in request order. A successful result
includes any additions to the Library even when the result is `nil`.

A request for `:use-arithmetic` has no operation arguments and its
successful value is `nil`. Requests for `:known`, `:fact-proof` and
`:equation` have the term and the Evidence object as arguments. A
successful known or fact-proof reply has value `(cons step evidence)`
and a successful equation reply has value `(cons equality evidence)`.
A missing proof or equation uses `nil` in the car of that value.
An Evidence object is the one in `prover/t4/sig/structural.md`.

## Retaining the Library on a caught failure

Each of the four public calls has a `-with-library` form with the same
arguments. This form returns `(cons result library)` even when
`result` is a failure. A request retains the form above.
A reply can also be `(cons failure library)` when the operation changed the Library before it failed. The request recognizer
`t4-constructors-request-p` takes a result and does not return a failure.

## Operations used by record laws

| Call | Result |
|---|---|
| `(t4-constructors-implied formula)` | `(guard claim)`, with `:none` for an absent guard. May return a failure on the wrong number of implication arguments. |
| `(t4-constructors-at term index ...)` | The datum reached by the given term indices. May return a failure on invalid indexing. |
| `(t4-constructors-first step index ...)` | The corresponding datum in the first literal of the Step. May return a failure on invalid indexing or an absent literal. |
| `(t4-constructors-query operation args lib replies)` | A request when the reply list is empty, the received failure, or `(list value library remaining-replies)`. |
| `(t4-constructors-finish result lib keep-library)` | The public result, retaining the Library on a failure when `keep-library` is true. |

`t4-constructors-with` evaluates a list of bindings in order and
propagates a request or failure immediately. A binding target is a
variable, a two-element list for a cons, or a three-element list for
a triple. The optional third macro argument is the expression for
the current Library. It is used to retain the Library on a failure.
`t4-constructors-with-library` uses the variable `lib` for it.
