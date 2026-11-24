# Theorem tactic selection

A tactic is a list whose first element is the ACL2 function name as a symbol
in the book's package. Any additional elements are fixed arguments
in call order. The fixed arguments are the table
term for association tactics and the operator term for substitution tactics.
The absence of a tactic is `nil`. Pass `:none` for an absent guard. A guard
and a goal are prover terms. `has-lambda` is an ACL2 Boolean.

Selection returns a tactic or `nil`, or a failure from reading a malformed
term. The selection checks run in the order of the cases in the formula
classifier.

| Call | Arguments and result |
|---|---|
| `(t3-book-recipes-subject term)` | First argument of the compound term, or `:none` when the term has no argument. |
| `(t3-book-recipes-beta-body term)` | Body with actual arguments substituted for the formals if the term is a lambda application. Otherwise the term itself. |
| `(t3-book-recipes-traversal-tactic guard goal has-lambda)` | Tactic for the traversal property. |
| `(t3-book-recipes-lookup-tactic guard goal)` | Tactic for the association property. |
| `(t3-book-recipes-recognizer-tactic guard goal)` | Tactic for the recognizer property. |
| `(t3-book-recipes-processor-tactic guard goal)` | Tactic for the clause-processor property. |
| `(t3-book-recipes-count-tactic guard left right)` | Tactic for the occurrence-count equation with terms `left` and `right`. |
| `(t3-book-recipes-sorting-tactic guard goal)` | Tactic for sorting or permutation. |
| `(t3-book-recipes-theorem-tactic formula)` | The selected tactic for the complete theorem term `formula`. |
| `(t3-book-recipes-apply tactic lib name formula)` | Pair of the theorem entry and the resulting Library, or a failure from applying the tactic. The tactic is a nonempty result of selection, `name` is the theorem symbol, and `formula` is the complete theorem term. |

In `apply`, the Library is the Library component of a book proof context.
The call uses the book proof context proof dispatch tag from `prover/t3/sig/logic.md` during
the tactic and returns the resulting Library with the input tag.
