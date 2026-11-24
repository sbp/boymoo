# Ordinal construction and lexicographic descent

A library has the form in `prover/sig/library.md`. Terms and proof steps have
the forms in `prover/sig/proof.md`. Rulers have the form in
`prover/sig/rulers.md`. A function with a library argument can return a failure
in place of its result.

| Function | Arguments in order | Result |
|---|---|---|
| `lexicographic-nonnegative-literal` | Term | Boolean |
| `lexicographic-constructed-ordinal` | Library, explicit ordinal term | Ordinality equation step or `nil` |
| `lexicographic-ordinal-constructor-equation` | Library, formula term | Ordinality equation step or `nil` |
| `lexicographic-natural-field` | Library, clipped term, Rulers | Pair of the field equality step and the library |
| `lexicographic-numeric-descent` | Library, child field equality step, parent field equality step, Rulers, extra descent data | Pair of the field comparison step or `nil` and the library |
| `lexicographic-descent-goal` | Library, ordinal comparison term | The equation to look up in the fact index, or `nil` outside the tactic's domain |
| `lexicographic-descent` | Library, ordinal comparison term, Rulers, result of the equation lookup, extra descent data | Pair of the comparison step or `nil` and the library |

The fact index is a later book. The caller obtains the goal from
`lexicographic-descent-goal` and uses the premise lookup with the fact index
to prove that equation. The caller supplies that lookup result, including
a possible `Unproved` failure, to `lexicographic-descent`. The optional
extra descent data follows `prover/sig/termination-proofs.md`.

The value in either descent pair can be a request
`(:call :descent lib goal rulers)` from the optional descent callback.
The caller supplies its reply and repeats the call as specified for
`termination-proofs-prove-decrease`.

The `lexicographic-constructed-ordinal-with-library` and
`lexicographic-ordinal-constructor-equation-with-library` calls take the
same arguments as their other forms and return `(cons step lib)`. Use
these calls when the Library is used again. Typing an ordinal coefficient
can introduce a lemma for a natural subterm.

The `lexicographic-natural-field-with-rulers`,
`lexicographic-numeric-descent-with-rulers`, and
`lexicographic-descent-with-rulers` calls take the same arguments as
their other forms and return `(cons (list value rulers) lib)`. The Rulers
retain established hypotheses for later queries.

`lexicographic-nonnegative-literal` returns a failure for a quote
with no argument.

`lexicographic-lexicographic-descent` has the same arguments and result
as `lexicographic-descent`.
