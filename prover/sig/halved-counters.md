# Halved counters

A library has the form in `prover/sig/library.md`. Terms and proof steps have
the forms in `prover/sig/proof.md`. Rulers have the form in
`prover/sig/rulers.md`. Each function can return a failure in place of its result.
Each successful result includes the library because these recipes can add lemmas.

| Function | Arguments in order | Result |
|---|---|---|
| `halved-counters-shifted-base` | Library, integer term, integrality step, positivity step, step excluding one | Pair of the weak lower bound by two and the library |
| `halved-counters-natural-clip` | Library, term, proof of naturalness | Pair of an equality from the clipped term to the term and the library |
| `halved-counters-half-positive` | Library, quotient term, naturalness step, integrality step, upper bound step, step giving the lower bound by two | Pair of the strict lower bound on the quotient and the library |
| `halved-counters-half-measure-lemma` | Library, Boolean selecting the remainder | Pair of the lemma label string and the library |
| `halved-counters-halved-counter-descent` | Library, ordinal comparison term, Rulers | Pair of the comparison step or `nil` and the library |
| `halved-counters-halved-counter-comparison` | Library, formula term | Pair of the implication step or `nil` and the library |

`halved-counters-counter-definitions` takes a list of names and the
definitions alist of a Proof. It returns the defined names in input order
and does not return a failure.

`halved-counters-halved-counter-descent-with-rulers` takes the same
arguments as the other descent call and returns
`(cons (list step rulers) lib)`. Its Rulers retain established hypotheses.

`halved-counters-library-ordinal-comparison` takes a Library and two
terms. It returns `(cons step lib)` for the equality of ordinal and
integer order, using the Library's integer rules. It can return a failure.

`halved-counters-rulers-for-library` takes Rulers, the tactic's input
Library, and its resulting Library. When the Rulers use the input
Library, it supplies the resulting Library while retaining the Rulers'
signed tests and established evidence. It does not return a failure.
