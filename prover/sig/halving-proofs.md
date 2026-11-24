# Length descent for a list splitter

A library has the form in `prover/sig/library.md`. Terms and proof steps have
the forms in `prover/sig/proof.md`. Rulers have the form in
`prover/sig/rulers.md`. A function with a library argument can return a failure
in place of its result.

| Function | Arguments in order | Result |
|---|---|---|
| `halving-proofs-length` | Term | Its length term |
| `halving-proofs-length-equation` | Library, list term, branch test step | Length equality step |
| `halving-proofs-cons-length` | Library, head term, tail term | Cons length equality step |
| `halving-proofs-positive-length` | Library, length equality step | A positive length step |
| `halving-proofs-cons-by-length` | Library, list term, positive length step | A cons test step |
| `halving-proofs-split-test` | Fast pointer term | A splitter test term |
| `halving-proofs-lengths` | Split result term | The two projection length terms in order |
| `halving-proofs-properties` | First length term, second length term, middle pointer term, accumulator term | The conjunction of the length properties |
| `halving-proofs-split-hypothesis` | Fast pointer term, middle pointer term | The conjunction of the length hypotheses |
| `halving-proofs-take-step` | Library, fast pointer term, middle pointer term, fast cons step, fast tail cons step, weak length bound step | List of the new hypothesis step and middle length equality step |
| `halving-proofs-halving-rule` | Library, splitter function symbol | The defining equation step or `nil` |
| `halving-proofs-halving-lemma` | Library, defining equation step | Pair of the lemma label string and the library |
| `halving-proofs-halving-descent` | Library, ordinal comparison term, Rulers | Pair of the comparison step or `nil` and the library |

`halving-proofs-halving-descent-with-rulers` takes the same arguments
and returns `(cons (list step rulers) lib)`. Its Rulers retain the
hypotheses established by the tactic.
