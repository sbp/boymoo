# Propositions

`lib` is the H1 prover's Library. A Library holds the Proof and the
ordered entries. Construct it with `library-library-init` and
`proof-proof-init`, and use the accessors in `prover/sig/library.md`.
`proof` is the Proof component. `step`, `equation`, `equality`,
`evidence`, `left`, `right`, `test`, and `consequence` are Steps.
`term` and `formula` are prover terms. Proof construction can return a
failure in place of any result below.

| ACL2 call | Result |
|---|---|
| `(h1-propositions-rewrite-value lib step equality)` | The Step with occurrences at the value positions rewritten by the equality. |
| `(h1-propositions-select-value lib equation test)` | The equation Step chained to the branch equality selected by `test`. |
| `(h1-propositions-beta-value lib equation)` | The equation Step after beta-reducing lambda applications at its right side. May return a fuel failure. |
| `(h1-propositions-computed-test lib equation)` | The Step for a test known to equal quoted `T` or `NIL`. |
| `(h1-propositions-propositional-proof-logic-and-types lib)` | The Library with the logic and type entries if its gap-ordinality fact was absent. |
| `(h1-propositions-propositional-proof-setup-propositions lib)` | The Library with its logic, type, and propositional entries in their publication order. |
| `(h1-propositions-propositional-proof-reflexive lib term)` | The reflexive equality Step. |
| `(h1-propositions-propositional-proof-select lib term evidence)` | The equation Step for the conditional branch selected by `evidence`. |
| `(h1-propositions-propositional-proof-conjoin lib formula left right)` | A Step for the conjunction `formula` from its left and right Steps. |
| `(h1-propositions-propositional-proof-conjunct lib step)` | A two-element list of the left and right conjunct Steps in that order. |
| `(h1-propositions-propositional-proof-modus-ponens lib step evidence)` | The implication's consequent Step using its premise Step. |
| `(h1-propositions-propositional-proof-false-premise lib formula evidence)` | The implication Step under a false premise. Pass `nil` for omitted evidence. |
| `(h1-propositions-propositional-proof-implies-from lib formula consequence)` | The implication Step from a Step of its consequent. |

The following operations use the corresponding inferences from the
arithmetic book.

| ACL2 call | Arithmetic inference |
|---|---|
| `(h1-propositions-proof-symmetric proof equality)` | `h1-arithmetic-proof-symmetric` |
| `(h1-propositions-proof-prove-if proof step test-proof)` | `h1-arithmetic-proof-prove-if` |
| `(h1-propositions-proof-transport proof step equality)` | `h1-arithmetic-proof-transport` |
| `(h1-propositions-library-transport-argument lib step equality index)` | `h1-arithmetic-library-transport-argument` |
| `(h1-propositions-proof-simplify proof term evidence definitions)` | `h1-arithmetic-proof-simplify` |
