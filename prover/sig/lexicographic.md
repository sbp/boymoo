# Ordinal construction and lexicographic descent

A library has the form in `prover/sig/library.md`. Terms and proof steps have
the forms in `prover/sig/proof.md`. Rulers have the form in
`prover/sig/rulers.md`. A function with a library argument can return a failure
in place of its result.

| Function | Arguments in order | Result |
|---|---|---|
| `lexicographic-nonnegative-literal` | Term | Boolean |
| `lexicographic-descent-goal` | Library, ordinal comparison term | The equation to look up in the fact index, or `nil` outside the tactic's domain |

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
