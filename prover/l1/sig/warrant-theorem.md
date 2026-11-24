# Warrant theorems

`proof` is the Proof described in `prover/sig/proof.md`, normally a WarrantProof as specified in `prover/l1/sig/warrant.md`. `choices` is the list of ChoiceRule objects in the order they became available. A ChoiceRule is described in `prover/l1/sig/witness.md`. Terms and Steps use the forms in `prover/sig/proof.md`. A missing guard or tame condition is `:none` as in `prover/l1/sig/warrant.md`. A failed recognition returns `nil`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(l1-warrant-theorem-theorem-parts formula)` | `(force badge applied guard)` when the term `formula` has warrant theorem form, or `nil`. | A failure from reading the term. |
| `(l1-warrant-theorem-matching-warrant proof choices parts)` | `(rule badge-test tame designator arguments)` for the first matching warrant, or `nil`. `parts` is the recognized theorem. | A failure from reading facts or terms or substituting into them. |
| `(l1-warrant-theorem-contract proof rule arguments warrant-holds)` | A Step for the warrant's contract at term `arguments`, from ChoiceRule `rule` and Step `warrant-holds`. | A failure from reading or constructing the Step. |
| `(l1-warrant-theorem-prove-warrant-theorem proof name formula choices)` | `(count source)` for the theorem named by symbol datum `name`, or `nil` when the tactic does not apply. Source is an ASCII byte string with its newlines. | A failure from reading, constructing or writing the certificate. |
| `(l1-warrant-theorem-prove-fragments proof name formula choices)` | As above, with a list of strings in entry order in place of the joined source string. | A failure from reading, constructing or writing the certificate. |
