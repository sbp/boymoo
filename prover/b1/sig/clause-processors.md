# Clause processors

`lib` is the Library used by the B1 BookProof. `formula` is a prover term
in the form in `prover/sig/proof.md`. A failure is the entire result of any
call below.

| Call | Result |
|---|---|
| `(b1-clause-processors-mv-nth-evaluation-recursion lib formula)` | `(cons step lib)` with the proof that evaluating the recursive transformation preserves the original selected value and the Library with any auxiliary lemma. |
| `(b1-clause-processors-mv-nth-evaluation-meta lib formula)` | A Step proving the evaluator equality for the meta rule. |
| `(b1-clause-processors-flag-processor-correct lib formula)` | A Step proving the evaluator implication for the flag clause processor. |
| `(b1-clause-processors-flag-processor-wellformed lib formula)` | A Step proving the term and logical function recognizer implication for the flag clause processor. |

The induction substitutions in the recursive evaluator proof retain the
order in which the evaluator visits the leaves, with the syntax binding
before the index binding in each substitution.
