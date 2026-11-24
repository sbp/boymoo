# Printing

A Library and a Step use the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Tests are ordered `(term holds)` pairs, with `t`
for a true test and `nil` for a false test. Known premises are a list
of Steps in the order supplied. A term uses the representation in
`prover/sig/proof.md`.

A PrintedList has the form `(:t4-printing-printed-list lib template)`.
The template is the character-list predicate applied to
`*proof-result*`. The constructor and accessors are
`t4-printing-printed-list-init`, `t4-printing-printed-list-lib` and
`t4-printing-printed-list-template`. A method that changes the Library
and returns a value gives `(cons value printer)` with the resulting
PrintedList. A failure is the entire result.

`mutual` is an association list from function symbols to the ordered
lists of their mutually recursive groups. The associations keep
insertion order, and the members of each group keep definition order.
`arithmetic` is true if the Library has already run its arithmetic
build.

| Call | Result | Failure |
|---|---|---|
| `(t4-printing-character-results lib formula mutual arithmetic)` | Pair of a Step for the character-list formula or `nil`, and the resulting Library. The uncached applicable case builds arithmetic if needed. | A failure from inspecting terms or constructing the proof. |
| `(t4-printing-printed-list-init lib)` | A PrintedList for Library `lib`. | None. |
| `(t4-printing-printed-list-pick printer equation condition)` | The equality Step with the conditional on its right side selected using the Step `condition`. | A failure from constructing the proof. |
| `(t4-printing-printed-list-unroll printer proof term)` | The character-list proof Step rewritten using the equality Step `term`. | A failure from constructing the proof. |
| `(t4-printing-printed-list-character printer term tests)` | Pair of the Step showing that `term` is a character and the resulting PrintedList. | A failure for a missing premise, or a failure from constructing the proof. |
| `(t4-printing-printed-list-cons printer head tail)` | Pair of the character-list Step for a cons and the resulting PrintedList. `head` proves the character type and `tail` proves the character-list type. | A failure from constructing the proof. |
| `(t4-printing-printed-list-true-list printer characters)` | Pair of a true-list Step and the resulting PrintedList, given the character-list Step `characters`. | A failure from constructing the proof. |
| `(t4-printing-printed-list-literal printer value)` | Pair of the character-list Step for quoted term `value` and the resulting PrintedList. | A failure for a non-list literal or a failure from constructing the proof. |
| `(t4-printing-printed-list-prove-result printer value leaf tests known)` | Pair of the Step for the character-list result of `value` and the resulting PrintedList. For externally supplied leaf proofs, `leaf` is an association list from `(value tests)` requests to Steps or failures. | A failure from inspecting terms or constructing the proof. |
| `(t4-printing-printed-list-integer-digits printer)` | The PrintedList after adding the theorem for printing an integer. | A failure from constructing the proof. |
| `(t4-printing-printed-list-missing-value value tests)` | The failure for a missing character-list premise on term `value`. | A failure. |
| `(t4-printing-printed-list-atoms printer)` | The PrintedList after adding the printing theorems for integers and atoms. | A failure from constructing the proof. |

`(t4-printing-character-results-arithmetic-needed-p lib formula mutual)`
is true when the formula reaches the arithmetic setup in
`t4-printing-character-results`. A cached lemma makes the result false. The call
can return a failure from inspecting the formula or group.
